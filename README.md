# fruit-problem
A search pipeline and database for elliptic curves isomorphic to the fruit problem equation

## What this project computes
This project computes the generators of the family of elliptic curves

$$
y^2=x^3+(4n^2+12n-3)x^2+32(n+3)x
$$

thus providing non-trivial solutions to the fruit problem

$$
\frac{a}{b+c}+\frac{b}{a+c}+\frac{c}{a+b}=n
$$

## How is data computed
- PARI/GP `ellrank` ([cubic.gp](cubic.gp)) is applied to those curves first.
- For those curves where `ellrank` cannot determine the rank, Magma's higher descents ([cubic_descent.m](cubic_descent.m)) are used.
- When the conductor is small, and analytic calculation is cheap, PARI/GP `ellheegner` is used to compute the generators.

## Completeness
- Range of the database: 1 - 10,000
- Completed data: 9,982 / 10,000 (99.82%)
- Saturated: yes
- Verification against 2-Selmer group bounds: **no** (missing generators are possible)

## File Structure
- [cubic.gp](cubic.gp): PARI/GP engine for rank bounds, isogeny mappings, and solution transformations.
- [cubic_descent.m](cubic_descent.m): Magma script for higher-degree descents.
- [cubic_db.txt](cubic_db.txt): The compiled dataset for $N \in [1,10^4]$.

## License
- **Code:** GPL-3.0
- **Dataset:** CC-BY-4.0
