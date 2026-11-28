/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Adjunction

/-!
# Derivation rules for the multiplication adjoint in the Hall algebra

Let `k` be a finite field. In `TauCeti.HallAlgebra.Adjunction`, it is shown that for a cuspidal
element `c : HallAlgebra k` and `d ≠ 0`, the multiplication adjoint `∂_{d, c} = mulAdjoint d c`
is a derivation of the Hall algebra (`TauCeti.HallAlgebra.mulAdjoint_mul`).

This file records the immediate algebraic consequences used when computing inner products of
products of Green's cuspidal functions (`Ξ_c = ∏_{P ∣ c} τ_P`) and pairing them with `𝟙`:

* `TauCeti.HallAlgebra.mulAdjoint_one`: `∂_{d, f} 1 = 0` for any `f` and `d ≠ 0`.
* `TauCeti.HallAlgebra.mulAdjoint_pow_succ`:
  `∂_{d, c} (F ^ (n + 1)) = (n + 1) • (F ^ n * ∂_{d, c} F)` for cuspidal `c` and `d ≠ 0`.
* `TauCeti.HallAlgebra.mulAdjoint_prod`: Leibniz rule for finite products
  `∂_{d, c} (∏ i ∈ s, F i) = ∑ i ∈ s, ∂_{d, c} (F i) * ∏ j ∈ s.erase i, F j`.
* `TauCeti.HallAlgebra.mulAdjoint_constOne`: `∂_{d, f} 𝟙 = ⟨f, 𝟙⟩_d • 𝟙` for any `f`.
* `TauCeti.HallAlgebra.mulAdjoint_constOne_eq_zero_iff`: `∂_{d, f} 𝟙 = 0 ↔ ⟨f, 𝟙⟩_d = 0`.

## References

* Adapted from `src/Lib/LocalGL/Green/TauFunctions.lean` and
  `src/Lib/LocalGL/Green/LabelCharacters.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC).
-/

public section

open scoped BigOperators

namespace TauCeti.HallAlgebra

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

/-- For `d ≠ 0` and any `f`, the multiplication adjoint `∂_{d, f}` annihilates the unit `1`. -/
@[simp]
theorem mulAdjoint_one {d : ℕ} (hd : d ≠ 0) (f : HallAlgebra k) :
    mulAdjoint d f 1 = 0 := by
  ext a
  rw [mulAdjoint_apply, zero_apply]
  refine rankInner_eq_zero_of_right f fun b hb ↦ ?_
  let _ := Fintype.ofEquiv (Matrix (Fin a.dim) (Fin b.dim) k) Matrix.toLin'.toEquiv
  rw [← SimilarityClass.ofEnd_rep a, ← SimilarityClass.ofEnd_rep b, blockAverage_ofEnd]
  simp [one_apply, SimilarityClass.dim_ofEnd, Module.finrank_prod, hb, hd]

/-- For cuspidal `c` and `d ≠ 0`, the derivation `∂_{d, c}` satisfies the power rule
`∂_{d, c} (F ^ (n + 1)) = (n + 1) • (F ^ n * ∂_{d, c} F)`. -/
theorem mulAdjoint_pow_succ {c : HallAlgebra k} (hc : c.IsCuspidal) {d : ℕ} (hd : d ≠ 0)
    (F : HallAlgebra k) :
    ∀ n : ℕ, mulAdjoint d c (F ^ (n + 1)) = (n + 1) • (F ^ n * mulAdjoint d c F)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, mulAdjoint_mul hc hd, mulAdjoint_pow_succ hc hd F n]
    simp only [add_smul, one_smul, pow_succ]
    ring

/-- **Finite-product Leibniz rule.** For cuspidal `c` and `d ≠ 0`,
`∂_{d, c} (∏ i ∈ s, F i) = ∑ i ∈ s, ∂_{d, c} (F i) * ∏ j ∈ s.erase i, F j`. -/
theorem mulAdjoint_prod {ι : Type*} [DecidableEq ι] {c : HallAlgebra k} (hc : c.IsCuspidal)
    {d : ℕ} (hd : d ≠ 0) (s : Finset ι) (F : ι → HallAlgebra k) :
    mulAdjoint d c (∏ i ∈ s, F i) =
      ∑ i ∈ s, mulAdjoint d c (F i) * ∏ j ∈ s.erase i, F j := by
  induction s using Finset.induction_on with
  | empty => simp [mulAdjoint_one hd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mulAdjoint_mul hc hd, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hne : a ≠ i := fun h ↦ ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (by simp [ha]), mul_left_comm]

/-- The multiplication adjoint `∂_{d, f}` scales the constant function `𝟙` by `⟨f, 𝟙⟩_d`. -/
theorem mulAdjoint_constOne (d : ℕ) (f : HallAlgebra k) :
    mulAdjoint d f constOne = rankInner d f constOne • constOne := by
  ext a
  have hba : blockAverage (constOne : HallAlgebra k) a = constOne := by
    ext b
    let _ := Fintype.ofEquiv (Matrix (Fin a.dim) (Fin b.dim) k) Matrix.toLin'.toEquiv
    rw [← SimilarityClass.ofEnd_rep a, ← SimilarityClass.ofEnd_rep b, blockAverage_ofEnd]
    simp [constOne_apply]
  rw [mulAdjoint_apply, hba, smul_apply, constOne_apply, mul_one]

/-- `∂_{d, f} 𝟙 = 0` iff `⟨f, 𝟙⟩_d = 0`. -/
theorem mulAdjoint_constOne_eq_zero_iff (d : ℕ) (f : HallAlgebra k) :
    mulAdjoint d f constOne = 0 ↔ rankInner d f constOne = 0 := by
  rw [mulAdjoint_constOne]
  constructor
  · intro h
    have h0 := congrArg (fun F : HallAlgebra k ↦ F (SimilarityClass.ofEnd
      (0 : Module.End k (Fin 0 → k)))) h
    simpa [smul_apply, constOne_apply] using h0
  · intro h
    simp [h]

end TauCeti.HallAlgebra
