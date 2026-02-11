import BET.LinReg
--import Mathlib.Algebra.Order.Floor

/-Criteria:
  1. Minimum 10 points, up to n points (n = list length)
  2. R^2 >= 0.995 (variable, user selected)
  3. V(1-P/P0) Monotonic Increase with P/P0
  4. C (1 + slope/int) obtained by LinReg must be > 0, i.e. slope > (-int)
  5. Monolayer loading (Nm Read) must correspond to point in linear region
  6. Nm BET must be equal to Nm Read, 20% tolerance -/
