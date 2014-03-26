# `quadratic-irrational`

[![Build Status](https://travis-ci.org/ion1/quadratic-irrational.svg)](https://travis-ci.org/ion1/quadratic-irrational)

An implementation of [quadratic irrationals][qi] with support for conversion
from and to [periodic continued fractions][pcf].

[qi]:  http://en.wikipedia.org/wiki/Quadratic_irrational
[pcf]: http://en.wikipedia.org/wiki/Periodic_continued_fraction

A quadratic irrational is a number that can be expressed in the form

```
(a + b √c) / d
```

where `a`, `b` and `d` are integers and `c` is a square-free natural number.

Some examples of such numbers are

* `7/2`,

* `√2`,

* `(1 + √5)/2` ([the golden ratio][gr]),

* solutions to some quadratic equations – the [quadratic formula][qf] has a
  familiar shape.

[gr]: http://en.wikipedia.org/wiki/Golden_ratio
[qf]: http://en.wikipedia.org/wiki/Quadratic_formula

A continued fraction is a number that can be expressed in the form

```
a + 1/(b + 1/(c + 1/(d + 1/(e + …))))
```

or alternatively expressed using the notation

```
[a; b, c, d, e, …]
```

where `a` is an integer and `b`, `c`, `d`, `e`, … are positive integers.

Every finite continued fraction represents a rational number and every
infinite, periodic continued fraction represents a quadratic irrational.

```
3.5      = [3; 2]
(1+√5)/2 = [1; 1, 1, 1, …]
√2       = [1; 2, 2, 2, …]
```
