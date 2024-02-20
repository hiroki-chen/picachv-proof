# A TODO List

So far we still have a number of works to be done, among which are the following important tasks:

- [x] Slightly modify the syntax of the expressions; there seems no need to introduce the "lambda calculus" thing. For example, there would be no variables at all... The syntax can thus be simplified.
- [ ] Implement the noise generator. I am not sure whether if this is directly integrated into the aggregation expressions. It seems to be more natural and easier for us to implement if we just let the type constructor take it as an argument:

  - The privacy budget is defined globally for the whole dataset.
  - We only need to calculate the sensitivity of aggregate queries because they will consume privacy budget.
  - Then it "consumes" the privacy budget. The amount of noise is proportional to the sensitivity of the query and inversely proportional to the privacy budget.

  - [ ] A new type of expression is added as a constructor of `expression`.
- [ ] Implement the evaluation rule for binary expressions $e_1 \oplus e_2$.
  - What would be the policy checking logic ??
