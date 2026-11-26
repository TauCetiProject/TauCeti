/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Powers of ideal sheaves

Powers of an ideal sheaf on a scheme decrease, as for ideals
(`AlgebraicGeometry.Scheme.IdealSheafData.pow_le_self`,
`AlgebraicGeometry.Scheme.IdealSheafData.pow_le_pow_right`), so the ideal sheaf of the closed
immersion `V(I ^ n) ⟶ X` lies in `I` for `n ≠ 0`
(`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_pow_le`). A nonzero power of an ideal
sheaf has the same radical (`AlgebraicGeometry.Scheme.IdealSheafData.radical_pow`).
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme} (I : X.IdealSheafData)

/-- A nonzero power of an ideal sheaf is contained in it, as for ideals (`Ideal.pow_le_self`). -/
theorem pow_le_self {n : ℕ} (hn : n ≠ 0) : I ^ n ≤ I :=
  pow_le_of_le_one bot_le ((le_top : I ≤ ⊤).trans_eq one_eq_top.symm) hn

/-- Powers of an ideal sheaf decrease, as for ideals (`Ideal.pow_le_pow_right`). -/
theorem pow_le_pow_right {m n : ℕ} (h : m ≤ n) : I ^ n ≤ I ^ m :=
  pow_le_pow_of_le_one bot_le ((le_top : I ≤ ⊤).trans_eq one_eq_top.symm) h

/-- The ideal sheaf of the closed immersion `V(I ^ n) ⟶ X`, for `n ≠ 0`, is contained in `I`, so
closed immersions with ideal sheaf `I` lift along it. -/
theorem ker_subschemeι_pow_le {n : ℕ} (hn : n ≠ 0) : (I ^ n).subschemeι.ker ≤ I :=
  (ker_subschemeι _).trans_le (I.pow_le_self hn)

/-- The radical of a nonzero power of an ideal sheaf is its radical, as for ideals
(Mathlib's `Ideal.radical_pow`): both are the vanishing ideal of the common support. -/
@[simp]
theorem radical_pow {n : ℕ} (hn : n ≠ 0) : (I ^ n).radical = I.radical := by
  rw [← vanishingIdeal_support, ← vanishingIdeal_support, support_pow I n hn]

end AlgebraicGeometry.Scheme.IdealSheafData
