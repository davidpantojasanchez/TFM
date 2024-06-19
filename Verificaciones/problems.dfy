// 2 - Problemas

include "auxiliar.dfy"

// Problema de decisión del conjunto de cobertura
ghost predicate {:opaque} SetCover<T>(U:set<T>, S: set<set<T>>, k:int)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
{
  exists C:set<set<T>> | C <= S :: isCover(U, C) && |C| <= k
}

ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall e | e in universe :: (exists s | s in sets :: e in s)
}

// Hitting Set
ghost predicate HittingSet<T>(universe:set<T>, sets:set<set<T>>, cardinality:int)
  requires forall s | s in sets :: s <= universe
  requires forall s1 | s1 in sets :: !(exists s2 | s2 in sets - {s1} :: s1 == s2)
{
  exists s:set<T> :: hitsSets(sets, s) && |s| <= cardinality && s <= universe
}

ghost predicate hitsSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}

// D-ATDP : Problema determinista de decisión de tests adaptativos
/*
Problema de determinar si es posible construir unos tests adaptativo (árbol de tests) de hasta k tests que pueda determinar
si una IUT (implementation under test) en C es correcta (está en las especificaciones E) o incorrecta
*/
ghost predicate {:opaque} DATDP(C:set<map<Question, Answer>>, E:set<map<Question, Answer>>, k:int, I:set<Question>)
  requires E <= C
  requires 0 <= k <= |I|
  requires forall vehicle:map<Question, Answer> | vehicle in C :: vehicle.Keys == I
{
  if k == 0 then
    separatedSet(C, E)
  else
    exists i:Question | i in I ::
      forall o:Answer | o in (set m:map<Question, Answer> | m in C :: m[i]) ::
        DATDP(
          restrictSet(C, i, o),
          restrictSet(E, i, o),
          k - 1,
          I
        )
}

/*
Variante de D-ATDP diseñada para ser más similar al problema PCD-Límite. En lugar del conjunto de especificaciones
correctas E, tiene un mapa f de IUTs (mapas de tests a comportamientos) a bool (si la IUT es correcta o no)
*/
ghost predicate {:opaque} DATDPintermediate(C: set<map<Question, Answer>>, f: map<map<Question, Answer>, bool>, k: int, I: set<Question>)
  requires f.Keys == C
  requires 0 <= k <= |I|
  requires forall vehicle: map<Question, Answer> | vehicle in C :: vehicle.Keys == I
{
  if k == 0 then
    separatedMixed(C, f)
  else
    exists i: Question | i in I ::
      forall o: Answer | o in (set m:map<Question, Answer> | m in C :: m[i]) ::
        DATDPintermediate(
          restrictSet(C, i, o),
          restrictMap(f, i, o),
          k - 1,
          I
        )
}

// PCD-Límite : Problema de clasificación de datos con características privadas no exhaustivo, interactivo, con límite de preguntas y total
/*
No exhaustivo: Las funciones f y g son parciales
Interactivo: Las preguntas pueden cambiar en función de las respuestas (la entrevista es adaptativa)
Con límite de preguntas: Las ramas de la entrevista adaptativa no puede tener más de k preguntas
Total: Requiere poder discernir la aptitud de la población completamente
       Independientemente de quién es el candidato entrevistado, la entrevista debe ser capaz de determinar con certeza absoluta si es apto o no
*/
ghost predicate {:opaque} PCDLim(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires 0 <= k <= |Q|
{
  okPrivate(f, g, P, a, b, Q) &&
  if k == 0 then
    okFitness(f)
  else
    okFitness(f) ||
    exists i:Question | i in Q ::
      forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
        PCDLim(
          restrictMap(f, i, o),
          restrictMap(g, i, o),
          P, k - 1, a, b, Q
        )
}

// PCD-Exhaustivo : Problema de clasificación de datos con características privadas exhaustivo, no interactivo, sin límite de preguntas y total
/*
Exhaustivo: Las funciones f y g son totales
No interactivo: Las preguntas no pueden cambiar en función de las respuestas (la entrevista es un conjunto de preguntas)
Sin límite de preguntas: Las ramas de la entrevista adaptativa pueden tener todas las preguntas posibles
Total: Requiere poder discernir la aptitud de la población completamente
       Independientemente de quién es el candidato entrevistado, la entrevista debe ser capaz de determinar con certeza absoluta si es apto o no
*/
ghost predicate PCDExhaustivo(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, Q:set<Question>)
  requires forall m | m in f.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires forall answers:map<Question, Answer> | answers.Keys == Q :: answers in g.Keys
{
  exists qs:set<Question> | qs <= Q ::
    forall answers:map<Question, Maybe<Answer>> |
    answers.Keys == Q &&
    answered(qs, answers, Q) ::
      okFitness(
        map m:map<Question, Answer> | m in f.Keys && (forall q:Question | q in Q :: Just(m[q]) == answers[q] || answers[q] == Nothing) :: f[m]
      ) &&
      okPrivate(
        map m:map<Question, Answer> | m in f.Keys && (forall q:Question | q in Q :: Just(m[q]) == answers[q] || answers[q] == Nothing) :: f[m],
        map m:map<Question, Answer> | m in g.Keys && (forall q:Question | q in Q :: Just(m[q]) == answers[q] || answers[q] == Nothing) :: g[m],
        P, a, b, Q
      )
}

// PCD-Estático : Problema de clasificación de datos con características privadas no exhaustivo, no interactivo, con límite de preguntas y total
/*
No exhaustivo: Las funciones f y g son parciales
No interactivo: Las preguntas no pueden cambiar en función de las respuestas (la entrevista es un conjunto de preguntas)
Con límite de preguntas: Las ramas de la entrevista adaptativa no puede tener más de k preguntas
Total: Requiere poder discernir la aptitud de la población completamente
       Independientemente de quién es el candidato entrevistado, la entrevista debe ser capaz de determinar con certeza absoluta si es apto o no
*/
ghost predicate {:opaque} PCDEstatico(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, k:int, a:real, b:real, Q:set<Question>)
  requires forall m | m in f.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires forall answers:map<Question, Answer> | answers.Keys == Q :: answers in g.Keys
  requires 0 <= k <= |Q|
{
  exists qs:set<Question> | qs <= Q && |qs| <= k ::
    forall answers:map<Question, Maybe<Answer>> |
    answers.Keys == Q &&
    answered(qs, answers, Q) ::
      okFitness(
        map m:map<Question, Answer> | m in f.Keys && (forall q:Question | q in Q :: Just(m[q]) == answers[q] || answers[q] == Nothing) :: f[m]
      ) &&
      okPrivate(
        map m:map<Question, Answer> | m in f.Keys && (forall q:Question | q in Q :: Just(m[q]) == answers[q] || answers[q] == Nothing) :: f[m],
        map m:map<Question, Answer> | m in g.Keys && (forall q:Question | q in Q :: Just(m[q]) == answers[q] || answers[q] == Nothing) :: g[m],
        P, a, b, Q
      )
}

// PCD-Parcial : Problema de clasificación de datos con características privadas no exhaustivo, interactivo, sin límite de preguntas y parcial
/*
No exhaustivo: Las funciones f y g son parciales
Interactivo: Las preguntas pueden cambiar en función de las respuestas (la entrevista es adaptativa)
Sin límite de preguntas: Las ramas de la entrevista adaptativa pueden tener todas las preguntas posibles
Parcial: No es necesario poder discernir con certeza absoluta la aptitud de la población; es suficiente con asegurar que está en un determinado rango
*/
ghost predicate PCDParcial(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, x:real, y:real, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
{
  PCDParcialRec(f, g, P, a, b, x, y, |Q|, Q)
}

ghost predicate PCDParcialRec(f:map<map<Question, Answer>, bool>, g:map<map<Question, Answer>, int>, P:set<Question>, a:real, b:real, x:real, y:real, k:int, Q:set<Question>)
  requires forall m | m in g.Keys :: m.Keys == Q
  requires f.Keys == g.Keys
  requires P <= Q
  requires 0.0 <= a <= b <= 1.0
  requires 0.0 <= x <= y <= 1.0
  requires 0 <= k <= |Q|
{
  okPrivate(f, g, P, a, b, Q) &&
  if k == 0 then
    okFitnessPartial(f, g, Q, x, y)
  else
    okFitnessPartial(f, g, Q, x, y) ||
    exists i:Question | i in Q ::
      forall o:Answer | o in (set m:map<Question, Answer> | m in f.Keys :: m[i]) ::
        PCDParcialRec(
          (map m:map<Question, Answer> | m in f.Keys && m[i] == o :: f[m]),
          (map m:map<Question, Answer> | m in g.Keys && m[i] == o :: g[m]),
          P, a, b, x, y, k - 1, Q
        )
}
