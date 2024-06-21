Code of the Master's thesis "Analysis of complexity and practical resolution of the data classification problem with private characteristics".

ABSTRACT

This Master Thesis is a study of the data classification problem with private characteristics. This problem has numerous applications that are very relevant nowadays. We are going to focus on its application in the design of non-discriminatory personnel selection processes.

We will start by explaining some problems that will be useful in the study, such as the deterministic adaptive test decision problem, and defining the variants of the data classification problem that we will analyze.

A large part of the report will be devoted to the analysis of the complexity of the different variants of the problem we have defined. For this purpose, we will define several polynomial reductions, devoting special attention to the reduction of the most complex variant.

One of the objectives of this study is to showcase the usefulness of the language Dafny for proving the validity of polynomial reductions. To this end, we will verify using Dafny one of the reductions that we have previously defined and verified manually.

Having proven the intractability of most variants of the problem, it is of great interest to use heuristic methods to solve in a non-optimal way the data classification problem with private characteristics. We have implemented a greedy algorithm and two genetic algorithms to solve this problem.

We will conclude the Master's thesis with a case study, in which we will compare the performance of the three implemented algorithms using a non-parametric test.

KEYWORDS

NP-completeness, computational complexity, data classification, personnel selection, human resources, assisted verification, Dafny, non-parametric tests, Friedman test.
