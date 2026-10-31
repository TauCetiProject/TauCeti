/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products with the dual standard module of `gl n`

Let `V = K^n` be the standard module of `gl n K` and `V*` its dual. This file gives coordinates
on `V* ⊗ M` for a `gl n K`-module `M` and computes how matrices act on them.

Every element of `V* ⊗ M` is uniquely `∑ₛ e*ₛ ⊗ mₛ`, with `e*ₛ` the dual of the standard basis;
`TauCeti.dualStandardCoeff M s` reads off `mₛ`, via Mathlib's
`TensorProduct.equivFinsuppOfBasisLeft`. The matrix unit `Eᵢⱼ` sends `e*ᵢ` to `-e*ⱼ` and kills the
other `e*ₛ`, so the coefficients of `⁅Eᵢⱼ, x⁆` are those of `x` acted on by `Eᵢⱼ`, minus the
coefficient at `i` moved to `j`. The identity matrix acts on `V*` by `-1`, so a scalar action of
the identity on `M` shifts by `-1` on `V* ⊗ M`.

## Main results

* `TauCeti.dualStandardCoeff`: the coefficient of `x ∈ V* ⊗ M` at the dual basis functional `e*ₛ`.
* `TauCeti.ext_dualStandardCoeff`: elements of `V* ⊗ M` are determined by their coefficients.
* `TauCeti.dualStandardCoeff_lie_single`: the coefficients of `⁅Eᵢⱼ, x⁆`.
* `TauCeti.one_lie_dual_tensorProduct`: the identity matrix acts on `V* ⊗ M` by `c - 1` when it
  acts on `M` by `c`.
-/

public section

namespace TauCeti

open Matrix TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module K M]

variable (M) in
/-- The coefficient of `x ∈ V* ⊗ M` at the dual basis functional `e*ₛ`, read off Mathlib's
expansion `TensorProduct.equivFinsuppOfBasisLeft` along the dual of the standard basis. -/
noncomputable def dualStandardCoeff (s : Fin n) : Module.Dual K (Fin n → K) ⊗[K] M →ₗ[K] M :=
  (Finsupp.lapply s).comp
    (equivFinsuppOfBasisLeft (Pi.basisFun K (Fin n)).dualBasis).toLinearMap

/-- The coefficient of `f ⊗ m` at `e*ₛ` is `f (Pi.single s 1) • m`. -/
@[simp]
theorem dualStandardCoeff_tmul (s : Fin n) (f : Module.Dual K (Fin n → K)) (m : M) :
    dualStandardCoeff M s (f ⊗ₜ m) = f (Pi.single s 1) • m := by
  simp [dualStandardCoeff]

/-- Two elements of `V* ⊗ M` with the same coefficients are equal. -/
theorem ext_dualStandardCoeff {x y : Module.Dual K (Fin n → K) ⊗[K] M}
    (h : ∀ s, dualStandardCoeff M s x = dualStandardCoeff M s y) : x = y :=
  (equivFinsuppOfBasisLeft (Pi.basisFun K (Fin n)).dualBasis).injective (Finsupp.ext h)

/-- A nonzero element of `V* ⊗ M` has a least index with a nonzero coefficient. -/
theorem exists_dualStandardCoeff_ne_zero_of_ne_zero {x : Module.Dual K (Fin n → K) ⊗[K] M}
    (hx : x ≠ 0) : ∃ s, dualStandardCoeff M s x ≠ 0 ∧ ∀ r < s, dualStandardCoeff M r x = 0 := by
  have hS : {s | dualStandardCoeff M s x ≠ 0}.Nonempty := by
    by_contra h
    refine hx (ext_dualStandardCoeff fun s => ?_)
    by_contra hs
    exact h ⟨s, by simpa using hs⟩
  obtain ⟨s, hs, hmin⟩ := wellFounded_lt.has_min _ hS
  exact ⟨s, hs, fun r hr => by_contra fun h => hmin r h hr⟩

/-- The coefficients of `∑ᵣ e*ᵣ ⊗ mᵣ` are the `mᵣ`. -/
theorem dualStandardCoeff_sum_dualBasis_tmul (m : Fin n → M) (s : Fin n) :
    dualStandardCoeff M s (∑ r, (Pi.basisFun K (Fin n)).dualBasis r ⊗ₜ m r) = m s := by
  simp

variable [LieRingModule (Matrix (Fin n) (Fin n) K) M] [LieModule K (Matrix (Fin n) (Fin n) K) M]

/-- **The coefficients of `⁅Eᵢⱼ, x⁆`.** The matrix unit acts on each coefficient, and also moves
the coefficient at `i` to `j` with a sign, since `Eᵢⱼ` sends `e*ᵢ` to `-e*ⱼ`. -/
theorem dualStandardCoeff_lie_single (i j s : Fin n) (x : Module.Dual K (Fin n → K) ⊗[K] M) :
    dualStandardCoeff M s ⁅(single i j 1 : Matrix (Fin n) (Fin n) K), x⁆ =
      ⁅(single i j 1 : Matrix (Fin n) (Fin n) K), dualStandardCoeff M s x⁆ -
        if j = s then dualStandardCoeff M i x else 0 := by
  have h : (dualStandardCoeff M s).comp (LieModule.toEnd K (Matrix (Fin n) (Fin n) K)
      (Module.Dual K (Fin n → K) ⊗[K] M) (single i j 1)) =
      (LieModule.toEnd K (Matrix (Fin n) (Fin n) K) M (single i j 1)).comp (dualStandardCoeff M s) -
        if j = s then dualStandardCoeff M i else 0 := by
    -- `Eᵢⱼ` sends the standard basis vector at `s` to the one at `i` when `j = s`, else to `0`.
    have hvec : (single i j (1 : K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single s 1 =
        if j = s then Pi.single i 1 else 0 := by
      ext r
      rw [mulVec_single_one]
      by_cases hjs : j = s
      · subst hjs
        by_cases hri : r = i
        · subst hri; simp
        · simp [hri, Ne.symm hri]
      · simp [hjs]
    refine TensorProduct.ext' fun f m => ?_
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply, LieModule.lie_tmul_right,
      map_add, dualStandardCoeff_tmul, dualStandardCoeff_tmul, dualStandardCoeff_tmul,
      Module.Dual.lie_apply, Matrix.lie_apply, hvec, lie_smul]
    split_ifs <;> simp [dualStandardCoeff_tmul, sub_eq_add_neg, add_comm]
  have hx := LinearMap.congr_fun h x
  rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply] at hx
  rw [hx]
  split_ifs <;> rfl

/-- The diagonal matrix units on the coefficients of a vector of weight `ν`: the coefficient at `s`
has weight `ν + εₛ`. -/
theorem lie_single_self_dualStandardCoeff {nu : Fin n → K} {x : Module.Dual K (Fin n → K) ⊗[K] M}
    (hx : ∀ k, ⁅(single k k 1 : Matrix (Fin n) (Fin n) K), x⁆ = nu k • x) (k s : Fin n) :
    ⁅(single k k 1 : Matrix (Fin n) (Fin n) K), dualStandardCoeff M s x⁆ =
      (nu + Pi.single s (1 : K) : Fin n → K) k • dualStandardCoeff M s x := by
  have h := dualStandardCoeff_lie_single k k s x
  rw [hx, map_smul, eq_sub_iff_add_eq] at h
  rw [← h]
  by_cases hks : k = s
  · subst hks; simp [add_smul]
  · simp [hks]

/-- If the identity matrix acts on `M` by a scalar `c`, it acts on `V* ⊗ M` by `c - 1`, since it
acts on `V*` by `-1`. -/
theorem one_lie_dual_tensorProduct {c : K} (hc : ∀ m : M,
    ⁅(1 : Matrix (Fin n) (Fin n) K), m⁆ = c • m) (x : Module.Dual K (Fin n → K) ⊗[K] M) :
    ⁅(1 : Matrix (Fin n) (Fin n) K), x⁆ = (c - 1) • x := by
  have h : LieModule.toEnd K (Matrix (Fin n) (Fin n) K) (Module.Dual K (Fin n → K) ⊗[K] M) 1 =
      (c - 1) • LinearMap.id := by
    refine TensorProduct.ext' fun f m => ?_
    have hf : ⁅(1 : Matrix (Fin n) (Fin n) K), f⁆ = -f := LinearMap.ext fun w => by
      rw [Module.Dual.lie_apply, Matrix.lie_apply, Matrix.one_mulVec, LinearMap.neg_apply]
    rw [LieModule.toEnd_apply_apply, LieModule.lie_tmul_right, hf, hc, LinearMap.smul_apply,
      LinearMap.id_apply, neg_tmul, tmul_smul, sub_smul, one_smul]
    abel
  simpa using LinearMap.congr_fun h x

end TauCeti
