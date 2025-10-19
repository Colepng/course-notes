#import "@preview/thmbox:0.3.0": *
#show: thmbox-init()

#let recall = thmbox.with(
    variant: "Recall", 
    color: gray,
    numbering: none,
  )

#let notation = thmbox.with(
  variant: "Notation",
  color: maroon,
  numbering: none,
)

#align(center)[*September 3rd*]

#align(center)[*Goal*]
Calculus is the study of functions $f : [a, b] -> R$ and how they change.

To study calculus we must develop the language of real analysis.
#align(center)[ = ]
#align(center)[ == Completeness Axiom]

#definition()[
  Let $A$ be every nonempty subset of $RR$ or $(emptyset != A subset.eq RR)$.

  If $A$ has a largest element we denote it with $max(A)$ and the min is $min(A)$.
]

This leads to a problem.

#example()[
  $A = [0, 1)$

  $min(A)=0$
  
  $max(A)=$ DNE

  $A$ has a least upper bound.
]

#definition()[
  $emptyset != A subset.eq RR$
  
  We say $A$ is bounded above iff there exists $m in RR$ such that $a <= m$ for all $a in A$ we call such an $m$ an upper bound for $A$.

  Similarly we define bounded below as lower bound.

  $A$ is bounded if it's both bounded below and above.
]

#axiom("Completeness")[
  if $emptyset != A subset.eq RR$ is bounded above it has a least upper bound, called the supremum of $A$, $sup(A)$
]

#example()[
  $A = [0, 1)$ then $sup(A) = 1$.
]

#proposition()[
  if $emptyset != A subset.eq RR$ is bounded below then $A$ has a greatest lower bound, called the infimum of $A$, $inf(A)$
]

#proof()[
  Assume $m in RR$ such that $a >= m$ for all $a in A$. 
  Then, $-a <= m, forall a in A$.

  Hence, $-A = { -a : a in A }$ is bounded above.

  By the completeness axiom $L = sup(-A)$ exists.

  #claim()[
    $inf(A) = -L$
  ]

  For all $a in A, -a <= L => a >= -L => -L$ is a lower bound for $A$.

  If $N in RR$ is a lower bound for $A$ then for all $a in A, N <= a$ 
  $ &=> -a <= -N\ &=> L <= -N ("def of sup")\ &=>-L <= N\ &=> -L <= inf(A)$
]

#remark()[
  - $sup(A) = L = -inf(A)$
]

#example()[
  $emptyset != A, B subset.eq RR$ is bounded above.

  Consider, $A + B = {a + b : a in A, b in B}$. Prove that $sup(A + B) = sup(A) + sup(B)$
]

#proof()[
  if $a in A$ and $b in B$ then $ a <= sup(A)$ and $b <= sup(B)$. 

  This implies 
  $ a + b <= sup(A) + sup(B)$.

  Hence $sup(A+B) <= sup(A) + sup(B)$

  Let $epsilon < 0$ be given.

  Observe that there exists an $a in A, b in B$ such that  $ &sup(A) - epsilon/2 < a\ &sup(B) - epsilon/2 < b $

  This implies $sup(A) + sup(B)  - epsilon <= a + b <= sup(A+B)$.

  Since $epsilon > 0$ was arbitrary, $sup(A) + sup(B) <= sup(A +B)$
]

#align(center)[*September 5th*]

#example()[
  $emptyset != A subset.eq R$ is bounded above, let $alpha > 0$ be given. $alpha A = {alpha a : a in A}$

  Prove that $sup(alpha A) = alpha sup(A)$
]

#proof()[
  for $a in A, a <= sup(A)$\ $ &=> alpha a <= alpha sup(A)\ &=>sup(alpha A) <= alpha sup(A) "(by the def of sup)" $

  for $a in A$ $ alpha a &<= sup(alpha A)\ => a &<= 1/alpha sup(alpha a)\ => sup(A) &<=1/alpha sup(alpha a) \ => alpha sup(A) &<= sup(alpha A) $ 
]

#exercise()[][
  What if $alpha < 0$?

  $ sup(alpha A) &= sup( - ( -alpha) A)\
    &= - inf(- alpha A) "(did last lecture)"\
    &= - (- alpha) inf(A) "(for homework)"\
    &= alpha inf(A)
  $
]

#remark[][
  $emptyset != A subset.eq RR$

  If $A$ is not bounded above, we write $sup(A) = infinity$.

  If $A$ is not bounded below, we write $inf(A) = -infinity$.
]

#note[][
  As a convention in this class we say

  $sup(emptyset) = - infinity "(the smallest of everything)"$\
  $inf(emptyset) = infinity "(the largest of everything)"$
]

#proposition[Density of $QQ$][
  For all real numbers $a < b, exists q in Q$ such that $a < q < b$.
]

#proof[
  Choose $n in NN$ large enough such that $n ( b - a) > 1$.

  Take $k in NN$ such that $-k< a n < b n < k$.

  Consider $K = [-k, k] inter ZZ$ and such that $m = min{j in K: a n < j}$. Thus $- K < a n < m$ and so $m - 1 in K$.

  By minimality $a n >= m-1$. Hence $m <= a n + 1 < b n$ and $a n < m < b n$, this implies that $a < m/n < b$.
]

#pagebreak()
#align(center)[ = Sequences]
#align(center)[ == Limit of Sequences]

#align(center)[*September 8th*]
#definition()[
  A sequence is an infinite list of real numbers: 
  $ (a_n)_(n=1)^infinity = (a_n) = (a_1, a_2, dots) $

  We can view a sequence as a function $f: NN -> RR$ via the correspond $(a_1, a_2, dots) <-> f: n mapsto a_n$
]

#notation()[
  Let $(a_n)$ be a sequence such that $a_n in A$ for all $n in NN$ we write $(a_n) subset.eq A$.
]

#note("Big Idea")[
  $(a_n) subset.eq RR, a in RR$

  We say "$(a_n)$ converges to $a$" iff no matter how close you wish, eventually in $(a_n)$ the terms are that close to $a$.
]

#definition()[
  $(a_n) subset.eq RR, a in RR$

  We say $(a_n)$ converges to $a, a -> a$ iff for all $epsilon > 0$ there exists $N in RR$ such that $abs(a_n - a) < epsilon$ for all $n >= N$.

  We call a limit of $(a_n)$ and write  $display(lim_(n -> infinity)) a_n = a$ or $lim a_n = a$.
]

#definition()[
  if $(a_n)$ does not converge to any $a in RR$ we say it diverges.
]

#remark()[
  By taking the next highest natural number, we may assume $N in NN$. Symbolically:

  $ a_n -> a <==> forall epsilon>0, exists N in RR, (n >= N ==> abs(a_n -a) < epsilon) $
]

#example()[
  - $a_n = 1/n$

  *Claim: * $a_n -> 0$

  #proof()[
    Let $epsilon > 0$ be given and take $N = 1/epsilon + 1$.

    We see that $abs(a_n - 0) < epsilon <==> 1/n < epsilon <==> 1/epsilon < n$.

    For $n >= N, n > 1/epsilon$ and so $|a_n - 0| < epsilon$.
  ]
]

#example()[
  - $a_n = 1/(n^2 + 1)$
  *Claim: * $a_n -> 0$

  #proof()[
  Let $epsilon > 0$ be given and choose $N = sqrt((1 - epsilon)/epsilon) + 1$.

  We see that $abs(a_n - 0) < epsilon <==> 1/(n^2+1) < epsilon <==> 1 < epsilon n^2 + epsilon <==> (1-epsilon)/epsilon <==> n > sqrt((1-3)/epsilon)$.

  For $n >= N, n > sqrt((1-epsilon)/epsilon)$ and so $abs(a_n - 0) < epsilon$
]
]

#example()[
  - $a_n = (5n + 2)/(3n -1) = (5+2/n)/(3-1/n)$
  *Claim: * $a_n -> 5/3$

  #proof()[
  Let $epsilon > 0$ be given and take $N = (11 + 3epsilon)/(9epsilon) + 1$. We see that 

  $ abs(a_n - 5/3) < epsilon &<==> abs((5n+2)/(3n-1) - 5/3) < epsilon &&<==> abs((15n + 6 - 15n + 5)/(9n-3)) < epsilon <==>\ 11/(9n-3) &<==> 11 < 9n epsilon - 3 epsilon &&<==> (11 + 3 epsilon)/(9 epsilon) < n $

  For $n >= N, n > (11 + 3 epsilon)/(9 epsilon)$ and so $abs(a_n - 5/3) < epsilon$.
]
]

#align(center)[ == ]
#align(center)[ == ]

#align(center)[*September 22th*]

#theorem[Balzard-Weierstaw][
  Every bounded sequence, $(a_n) subset.eq RR$ has a convergent subsequence.
]

#align(center)[== Completeness of $RR$]

#definition()[
  We say $(a_n) subset.eq RR$ is cauchy iff $forall epsilon > 0, exists N in NN, n, m >= N => abs(a_n - a_m) < epsilon$.
]

#proposition()[
  If $(a_n)$ is convergent then $(a_n)$ is cauchy.
]

#proof()[
  Suppose $a_n arrow a$. 

  Let $epsilon > 0$ be given and take $N in NN$ such that $n >= N => abs(a_n - a) < epsilon/2$.

  For $n, m >= N$, $  &abs(a_n-a_m)\
                      &= abs(a_n -a +a - a_m)
                      &<= abs(a_n - a) + abs(a - a_m)\
                      &< epsilon/2 + epsilon/2 = Epsilon.
                      $
]

#proposition[$(a_n) subset.eq RR$ cauchy][
  Suppose $(a_n_k)$ is a subsequence such that $a_n_k arrow a$ then, $a_n arrow a$.
];

#proof[
  Let $epsilon$ > 0 be given.

  We know, $exists N_1 in NN$ such that $abs(a_n - a_m) < epsilon/2$ for $n, m >= N_1$.

  There exists $N_2 >= N_1$ such that $abs(a_n_k - a) < epsilon/2$ for $k >= N_2$

  For $n>=N_1$ $ abs(a_n-a) &= abs(a_n - a_n_N_2 + a_n_N_2 - a)\
    &<= abs(a_n -a_n_N_2) + abs(a_n_N_2 -a) 
    <= epsilon/2 + epsilon/2 = epsilon.
  $
]

#align(center)[*September 24th*]

#definition[
  We say $A subset.eq RR$ is complete iff whenever $(a_n) subset.eq A$ is cauchy  then $a_n arrow a$ for some $a in A$.
]

#theorem()[
  $RR$ is complete.
]

#proof()[
  Let $(a_n) subset.eq RR$ be cauchy. Then $(a_n)$ is bounded.

  By the B-W thm, $exists (a_n_k) "such that" a_n_k arrow a in RR$.\

  From before, $a_n arrow a$
]

#example[
  $A = (0, 1]$

  $a_n = 1/n, "then" a_n arrow 0 => (a_n) subset.eq A$ is cauchy since $0 in.not A$, then $A$ is not complete.
]

#definition[
  We say $C subset.eq RR$ is closed iff $(x_n) subset.eq C$ such that $x_n arrow x in R$ then $x in C$.
]

#example[
  - $(0, 1]$ is not closed
  - $RR$ is not closed
  - Assignment 2 implies $[a, b]$ is closed.
  - $ZZ$ is closed.
]

#proposition()[
  For $A subset.eq RR, A$ is closed iff $A$ is complete.
]

#proof[
  Assume $A$ is closed. Let $(a_n) subset.eq A$ be cauchy. 

  Since $RR$ is complete, $a_n arrow a in RR$ for some $a$.
  
  However $A$ is closed and so $a in A$.

  Hence, $A$ is complete.

  Assume $A$ is complete.

  Let $(a_n) subset.eq A$ such that $a_n arrow a in RR$.

  Since $(a_n)$ is cauchy and $A$ is complete, we know $a_n arrow a in A$.

  Hence, $A$ is closed.
]

#align(center)[ == $limsup, liminf$]

#align(center)[== Typology]
#align(center)[*September 29th*]

#definition()[
We say that $U subset RR$ is open if and only if $forall x in U, exists epsilon > 0, (x-epsilon, x+ epsilon) subset.eq U$
]



#example[
- $(a, b)$ is open
- $(0, 1]$ is neither open or closed
- $forall epsilon > 0, exists q in QQ, q in (pi - epsilon, pi + epsilon) subset.eq RR\\QQ$
]


#proposition()[
  A set $C subset.eq RR$ is closed iff $RR\\C$ is open
]

#proof()[
Assume $C$ is closed.

Let $x in RR\\C$.

For a contradiction, suppose $forall epsilon > 0, exists c in C$ such that $c in (x -epsilon, x+epsilon)$.

Thus $forall n in NN, exists c_n in C "such that" c_n in (x-1/n, x + 1/n)$. Then $abs(c_n-x) < 1/n arrow 0$ and so
$c_n arrow x$.

Since $C$ is closed, $x in C$, Contradiction!.


Assume $RR\\C$ is open.

Let $(c_n) subset.eq C$ such that $c_n arrow x in RR$.

For a contradiction assume $x in.not C$.

Since $RR\\C$ is open, $exists epsilon > 0$ such that $(x-epsilon, x + epsilon) subset.eq RR\\C$.

Using $c_n arrow x, exists N$ such that $c_N in (x-epsilon, x+ epsilon) subset.eq RR\\C$, Contradiction!.
]

#remark()[
$U in RR$ is open $arrow.l.r.double$ $RR\\(RR\\U)$ is open $arrow.l.r.double$ $RR\\U$ is closed.
]

#proposition()[
Let I be the index set

+ If $u_i subset.eq RR, i in I$ are open, then $union_(i in I) u_i$ is open.
+ If $c_i subset.eq RR, i in I$ are closed, then $inter_(i in I) c_i$ is closed.
+ If $u, v in RR$ are open, then $u inter v$ is open.
+ If $C, D in RR$ are closed, then $C union D$ is closed.
]
#proof[
+ Let $x in union u_i => exists i in I, x in u_i => exists epsilon > 0, (x - epsilon, x + epsilon) subset.eq u_i subset.eq U u_i$
+ $RR\\inter c_i = union (RR\\c_i)$ is open $=> inter c_i$ is closed.
+ Let $x in U inter V$, such that $ &exists epsilon_1 > 0, (x - epsilon_1, x + epsilon_1) subset.eq U\ 
&exists epsilon_2 > 0 (x - epsilon_2, x + epsilon_2) subset.eq V\ &epsilon = min{epsilon_1, epsilon_2} $
  This implies $(x - epsilon, x + epsilon) subset.eq U inter V$.
+ $RR\\(C inter D) = (RR\\C)inter(RR\\D) "open" => C union D "closed"$.
]

#example()[
- $underbrace(inter.big_(n=1)^infinity (- 1/n, 1/n), "open") = underbrace({0}, "not open")$
- $underbrace(union.big_(n=1)^infinity [0, 1 - 1/n], "closed") = underbrace([0, 1), "not closed")$
]

#definition()[
  $A subset.eq RR$
  + The closure of $A$ is $ overline(A) = inter.big_(A subset.eq C) C, "where" C "is closed." $
  + The interior of $A$ is $ "int"(A) = union.big_(U subset.eq A) U, "where" U "is open". $
]

#remark()[
+ $overline(A)$ is the smallest closed set containing A
+ $"int"(A)$ is the largest open set contained in A
]

#example()[
$A&=[0, 1)\
"int"(A)&=(0, 1)\
overline(A)&=[0, 1]$
]

#definition()[
$A subset.eq RR$
+ We say $x in RR$ is a limit point of A iff $exists (a_n) subset.eq A "such that" a_n arrow x$.
+ We say $x in RR$ is an interior point of A iff $exists epsilon > 0, (x-epsilon, x+epsilon) subset.eq A$.
]

#proposition()[
+ $overline(A) = { "limit pts of A" }$
+ $"int"(A) = { "interior pts of A" }$
]

#align(center)[*October 1st*]

#proof()[
  + Let $L = {x : x "limit point of" A}$

  Let $x in overline(A)$. If $x in.not L$ then, $exists epsilon > 0, (x - epsilon, x + epsilon)
  subset.eq RR\\A$. This implies $underbrace(RR\\(x - epsilon, x + epsilon), "closed") supset.eq A$

  Since $x in overline(A), => x in RR\\(x-epsilon,x+epsilon)$, Contradiction!.

  $(<==)$

  Let $x in L$ 
]

#proposition()[
  + $overline(RR\\A) = RR\\"int"(A)$
  + $"int"(RR\\A) = RR\\overline(A)$
]

#proof()[]

#example()[
  - $overline(QQ) = RR$\
    $"int"(QQ) = emptyset$
  -
]

#align(center)[= Continuity]
#counter(heading).step(level: 2)

#align(center)[*October 6th*]

#recall[recall][
  if $f: A -> RR$ is cst at $a in A$ iff $f(a_n) arrow f(a)$ whenever $(a_n) subset.eq A, a_n -> a$
]

#proposition[][
  $f: A -> RR$

  Then, $f$ is cts at $a in A$ iff $forall epsilon >0, exists delta > 0, x in A, abs(x-a)<delta => abs(f(x)-f(a))<epsilon$.
]

#proof[
  $(=>$) Suppose f is cts at $a in A$. Let $epsilon > 0$ be given.\
  Suppose no such $delta > 0$ exists. Thus for all $n in NN$, $exists a_n in A$ such that $|a_n -a| < 1/n$ but $|f(a_n) - f(a) >= epsilon$. 

  $N a_n$, $a_n arrow a$ and so $f(a_n) -> f(a)$ by cty at $a$.

  For a large $N, |f(a_N) - f(a)| < epsilon$. Contradiction!.

  $(<==)$ Suppose $f$ satisfies the $epsilon, delta$ Condition at $a$.

  Assume $(a_n) subset.eq A$ such that $a_n arrow a$.
]

#claim()[
  $f(a_n) arrow f(a)$

  #proof[
    Let $epsilon>0$ be given.

    There exists $delta>0$ such that $x in A, |x - a| < delta => |f(x)-f(a)| < epsilon$.

    Also, $exists N in NN$ such that $n >= |a_n - a| < delta$.

    For $n>=N, |f(a_n) - f(a)| < epsilon$.
  ]
]

#proposition()[
  $f: A arrow RR$

  Then, $f$ is cts iff $f^-1(u)$ is relatively open in $A$, whenever $U subset.eq RR$ is open.
]

#notation()[
  $f: X arrow Y, B subset.eq Y$.

  The pre-image of $B$ under $f$ is $f^-1(B) = { x in X: f(x) in B}$.
]

#proof[
  Assume $f$ is cts.

  Assume there exists an open $U subset.eq RR$ such that $f^-1(u)$ is not relatively open in $A$.

  Thus $exists x in f^(-1)(u)$ such that $forall n in N, exists a_n in A$ with, $|a_n -x| < 1/n$ and $a_n in.not f^(-1)(u)$.

  $therefore a_n -> x "and so", f(a_n) arrow f(x)$ by cty.

  Since $U$ is open, $exists epsilon > 0, (f(x)-epsilon, f(x) + epsilon) subset.eq U$

  However, $f(a_n) arrow f(x)$ and so for large $N, f(a_n) in (f(x)-epsilon, f(x) + epsilon) subset.eq u$. This implies
  $a_N in f^(-1)(u)$, Contradiction!.

  $<==$ Assume the pre-image Condition.

  Let $(a_n) subset.eq A$ such that $a_n arrow a in A$.

  #claim[$f(a_n) arrow f(a)$]

  Let $epsilon > 0$ be given.

  Consider $u = (f(a) - epsilon, f(a) + epsilon)$.

  By assumption, $f^(-1)(u)$ is relatively open in A.

  Since $a in f^(-1)(u), exists delta>0$ such that.
  $(a - delta, a + delta) inter A subset.eq f^(-1)(u)$.

  There exists $N in NN$ such that $n >= N => |a_n-a| < delta$. 

  Hence, $a >= N => a_n in (a - delta, a + delta) inter A, subset f^(-1)(u)$.

  $therefore n >= f(a_n) in U => |f(a_n)-f(a)| < epsilon$.
]

#corollary()[
  $f: A arrow RR$

  Then, $f$ is cts iff $f^(-1)(c)$ is rel closed in $A$ whenever $C subset.eq RR$ is closed.
]

#proof[
  $=>$ Let f be cts, and let $C subset.eq RR$ be closed.

  Then $RR\\C$ is open and so $f^(-1)(RR\\C$ is rel open in $A$.

  For homework check, $f^(-1)(RR\\C) = f^(-1)(RR)\\f-1(C) = A\\f^(-1)(c) => f^-1(C)$ rel closed in A.

  $<==$ Identical, do for homework if time.
]

#align(center)[*October 8th*]

#proposition()[
  $f, g : A -> RR, a in A$ is cts at $a in A$
]

#proof()[
  Then, $f + g, alpha f, f g, "where " f/g g(0) != 0$ are all cts at $a$.

  $(a_n) subset.eq A, a_n -> a, (f+g)(a_n) = f(a_n) + g(a_n) -> f(a) + g(a), "etc"$.
]

#proposition()[
  If $g$ is cts at $a$, and $f$ is cts at $(a)$, then $f circle.small g$ is cts at $a$.
  
  #note("why")[
    $(a_n) subset.eq "dom"(g)< a_n -> a, g "cts" => g(a_n) -> g(a)$
    $f "cts" => f(g(a_n)) -> f(g(a)) => (f circle.small g)(a_n) -> (f circle.small g)(a)$.
  ]
]

#example()[
  - $f, g: A -> RR$ are cts

    $X={x in A: f(x) < g(x)}$

    Prove that $X$ is relatively open in $A$.

    $X = (g - f)^(-1)(0, infinity)$

    - $f, g : A -> RR$ is cts

      Prove that $max {f, g}$ is cts.

      $max{f, g}=((f+g) + abs(f-g))/2$
]

#proposition()[
  $K subset.eq RR$ is compact

  $f : K -> RR$ is cts

  Then, $f(k)$ is compact.
]

#note[Notation][
  $f: X -> Y, A subset.eq X$ the image of $A$ is $f(A) = {f(a) : a in A$.
]

#proof()[
  Let $(y_n) subset.eq f(k)$ and say $y_n = f(x_n), x_n in K$.

  Since $(x_n) subset.eq K$ and $K$ is compact, $exists a "subsequence" X_n_k -> x in K$.

  Using continuity of $f$, we have $f(x_n_k) -> f(x)$, and so $y_n_k -> f(x) in f(K)$
]

#example()[
  $f: RR -> RR$, $f(x) = arctan(x) = tan^(-1)(x)$,

  $ underbrace(f(RR), "closed") = underbrace((- pi/2, pi/2), "not closed") $
]

#align(center)[* END OF MIDTERM MATERIAL *]

Midterm Exam
Wed, Oct, 22, 7:00 - 8:30 PM. (not 8:50). DWE 1501

Every question has a theme
+ Suprema
  + [5] From class (either a example problem or proof)
  + [5] New, (new homework type problem)
+ Sequence  Conv
  + [3] New (a is separate)
  + [3] From Class (b, c, d) are all part of the same idea
  + [2] Stat a thm
  + [2] From Class
+ Cty + topology
  + [5] From class
  + [5] New
+ Assignment Probs (read the assignment solutions)
  + [5] 
  + [5]
+ Short Answer/Computation
  5 x [2] = [10]

Out of 50 points

The density of $QQ$ proof is not on the midterm.

#align(center)[== EVT + IVT]

#recall()[
  $emptyset != A subset.eq RR "bd"$

  $exists (a_n), (b_n) subset.eq A$ such that $
    &a_n_> sup(A) in overline(A)\
    &b_n _> inf(A) in overline(A)
  $
]

#theorem("Exterme Value Thm")[
  If $K subset.eq RR$ is compact and $f : K -> RR$ is cts, then $exists a, b in K$ such that $f(a) = max f(k)$ and $f(b) = min f(k)$
]

#proof()[
  Since $f(k)$ is compact

  $sup f(k) in overline(f(k)) = f(k)$ and $inf f(k) in overline(f(k)) = f(k)$.
]

#align(center)[*October 10th*]

#theorem("Intermediate Value Theorem")[
  If $f: [a, b] -> RR$ is cts, then $f([a, b])$ is a compact interval.
]

#proof()[
  Let $y_1, y_2 in f([a, b])$ and let $z in RR$ such that $y_1 < z < y_2$

  Say $y_i = f(x_i), x_i in [a, b]$

  *Case 1:*  $x_1 < x_2$
  Let $ x_0 = sup {x in [x_1, x_2] : f(x) < z}. $

  For every $n in NN, exists a_n in [x_1, x_2] "s.t." x_0  - 1/n < a_n <= x_0$ and $f(a_n) < z$.

  Then, we have $a_n -> x_0$ and so $f(a_n) -> f(x_0) < z$.

  Hence by limits preserve order, $f(x_0) <= z$.

  Let $t_n = min { x_0 + 1/n, x_2}$

  $ therefore x_0 <= t_n < x_0 + 1/n => t_n -> x_0 => f(t_n) -> f(x_0) $ 

  However,  $f(t_n) >= z$ and so $f(x_0) >= z$

  $therefore z = f(x_0)$.

  *Case 2:* $x_2 < x_1$

  Similar, so we are done.
]

#example()[
  - $K subset.eq RR$ compact

    $f: K -> K$ is cts. $forall x != y, abs(f(x) - f(y)) < abs(x - y)$

    Prove that $exists x in K$ such that $f(x) = x$.
]

#proof()[
  Consider $g : K -> RR$, $g(x) = abs(f(x) - x)$. This is a comp of cts functions which implies $g$ is cts.

  Using EVT, Let $g(x_0) = min g(K)$.

  #claim()[$f(x_0) = x_0$]

  Suppose for a contradiction $f(x_0) != x_0$.

  $therefore abs(f(f(x_0)) - f(x_0)) < abs(f(x_0)- x_0) => g(f(x_0)) < g(x_0)$.

  By minimally $g(x_0)$ must the smallest value, Condition!
]

#example()[
  $f: [0,1 ] -> [0, 1]$ cts

  Prove that $x in [0, 1]$ such that $f(x) = x$.

  #note("why")[
    $g(x) = f(x) - 1$\
    $g(0) = f(0) >= 0$\
    $g(1) = f(1) 0 1<= 1$
  ]

  By the IVT, $g([0, 1]$ is an interval. $g(1) <= 0 <= g(0)$

  $therefore exists x in [0, 1]$ such that $g(x) = 0$.
]

#example()[
  Prove $exists x in RR$ such that $cos x = 1/x$.

  $f(x) = cos(x) - 1/x$ is cts.


  $f(phi/2) = 0 - 2/pi < 0$

  $f(2pi) = 1 - 1/2pi > 0$

  Since $f  : [pi/2, 2 pi] -> RR$ is cts, by the IVT, $f(pi/2, 2 p)$.

  Hence we have, $f(pi/2) < 0 < f(2pi)$.

  Thus $exists x in [pi/2, 2 pi] "such that" f(x) = 0$.
]
