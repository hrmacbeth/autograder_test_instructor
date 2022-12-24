import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Ring

/- 4 points -/
theorem problem1 {x : ℚ} (hx : x = 2/3) : 3 * x ≠ 1 := by
  apply ne_of_gt
  calc 3 * x = 3 * (2 / 3) := by rw [hx]
  _ > 1 := by rfl

/- 5 points -/
theorem problem2 {x y : ℚ} (h : x = 1 ∨ y = -1) :
    x * y + x = y + 1 := by
  cases' h with hx hy
  . calc x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  . calc x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

/- 1 point -/
theorem problem3 {x : ℚ} (hx : 2 * x + 1 = 5) :
    2 * x = 2 ∨ 2 * x = 4 := by
  right
  calc 2 * x = (2 * x + 1) - 1 := by ring
  _ = 5 - 1 := by rw [hx]
  _ = 4 := by norm_num