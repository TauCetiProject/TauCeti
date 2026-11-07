/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Basic

import Mathlib.Algebra.Polynomial.Laurent.Roots

/-!
# Pointwise evaluation and linear independence across weights

For a subgroup `Γ ≤ GL₂(ℝ)`, evaluating each component on the upper half-plane assembles into an
additive homomorphism `SlashInvariantForm.evalDirectSum` from
`⨁ k : ℤ, SlashInvariantForm Γ k` to `ℍ → ℂ`, a ring homomorphism
`ModularForm.evalDirectSum` from `⨁ k : ℤ, ModularForm Γ k` to `ℍ → ℂ` when
`[Γ.HasDetPlusMinusOne]`, and a `ℂ`-algebra homomorphism `ModularForm.evalDirectSumAlgHom`
when `[Γ.HasDetOne]`.

When `Γ` has finite-index intersection with `SL₂(ℤ)` (`[Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]`), this
evaluation is injective: slash-invariant forms of distinct weights are linearly independent as
functions on `ℍ`. Indeed, `Γ ⊓ 𝒮ℒ` contains a positive power `γ₀ = (S T S⁻¹)ⁿ` (`n > 0`), whose
powers `γ₀ᵐ` have automorphy factors `denom (γ₀ᵐ) z = -n m z + 1`. Evaluating a relation among
slash-invariant forms at the orbit `γ₀ᵐ • z` turns it into a Laurent polynomial in `ℂ[T; T⁻¹]`
vanishing at the infinitely many units `-n m z + 1` (`m : ℕ`), which vanishes identically by
`LaurentPolynomial.eq_zero_of_infinite_smeval_eq_zero`.

## Main definitions

* `SlashInvariantForm.evalDirectSum`: pointwise evaluation
  `(⨁ k : ℤ, SlashInvariantForm Γ k) →+ (ℍ → ℂ)`.
* `ModularForm.evalDirectSum`: pointwise evaluation as a ring homomorphism
  `(⨁ k : ℤ, ModularForm Γ k) →+* (ℍ → ℂ)`.
* `ModularForm.evalDirectSumAlgHom`: pointwise evaluation as a `ℂ`-algebra homomorphism
  `(⨁ k : ℤ, ModularForm Γ k) →ₐ[ℂ] (ℍ → ℂ)`.

## Main results

* `SlashInvariantForm.evalDirectSum_injective`: slash-invariant forms of distinct weights
  are linearly independent under `[Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]`.
* `ModularForm.evalDirectSum_injective`,
  `ModularForm.evalDirectSumAlgHom_injective`: the corresponding injectivity statements for
  modular forms.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII.
* T. Miyake, *Modular Forms*, Theorem 2.1.2.
-/

public noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup ModularGroup
open scoped DirectSum MatrixGroups LaurentPolynomial

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

namespace SlashInvariantForm

/-- Pointwise evaluation of a graded sum of slash-invariant forms as a function `ℍ → ℂ`. -/
def evalDirectSum : (⨁ k : ℤ, SlashInvariantForm Γ k) →+ (ℍ → ℂ) :=
  DirectSum.toAddMonoid fun k ↦ FunLike.coeAddMonoidHom (SlashInvariantForm Γ k) ℍ ℂ

@[simp]
theorem evalDirectSum_of (k : ℤ) (f : SlashInvariantForm Γ k) :
    evalDirectSum (DirectSum.of _ k f) = ⇑f :=
  DirectSum.toAddMonoid_of _ _ _

/-- Evaluating `evalDirectSum x` at `z : ℍ` sums the values `x k z` across all weights `k`. -/
theorem evalDirectSum_apply (x : ⨁ k : ℤ, SlashInvariantForm Γ k) (z : ℍ) :
    evalDirectSum x z = ∑ᶠ k : ℤ, x k z := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of x]
  rw [map_sum, Finset.sum_apply, finsum_eq_sum_of_support_subset _ (s := x.support)]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [evalDirectSum_of]
  · intro k hk
    by_contra hmem
    have hxk : x k = 0 := DFinsupp.notMem_support_iff.mp hmem
    exact hk (by simp [hxk])

/-- The bottom row of `(S * T * S⁻¹) ^ r` in `SL₂(ℤ)` has entries `-r` and `1`, so its automorphy
factor at `z` is `-r z + 1`. -/
private theorem denom_mapGL_STS_inv_pow (r : ℕ) (z : ℍ) :
    denom (mapGL ℝ ((S * T * S⁻¹ : SL(2, ℤ)) ^ r)) z = -(r : ℂ) * z + 1 := by
  let g : SL(2, ℤ) := (S * T * S⁻¹ : SL(2, ℤ)) ^ r
  have hg : (S * T * S⁻¹ : SL(2, ℤ)) ^ r = g := rfl
  have hp : g = S * T ^ r * S⁻¹ := by simp [g, conj_pow]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(r : ℤ) := by
    rw [hp, ← zpow_natCast]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S_inv,
      Matrix.SpecialLinearGroup.coe_neg, coe_S, coe_T_zpow]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    rw [hp, ← zpow_natCast]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S_inv,
      Matrix.SpecialLinearGroup.coe_neg, coe_S, coe_T_zpow]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hg, denom, mapGL_coe_matrix, map_apply_coe]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, h10, h11]
  simp [algebraMap_int_eq]

/-- The denominators of `(S T S⁻¹) ^ (n * m)` at a point `z` are pairwise distinct as `m` varies,
for `n > 0`. -/
private theorem denom_mapGL_STS_inv_pow_injective {n : ℕ} (hn : 0 < n) (z : ℍ) :
    Function.Injective fun m : ℕ ↦ denom (mapGL ℝ ((S * T * S⁻¹ : SL(2, ℤ)) ^ (n * m))) z :=
  fun m₁ m₂ hm ↦ by
    have him := congrArg Complex.im hm
    simp only [denom_mapGL_STS_inv_pow, Complex.add_im, Complex.one_im, add_zero,
      Complex.neg_im, Complex.mul_im, Complex.natCast_im] at him
    have hmul : ((n * m₁ : ℕ) : ℝ) = ((n * m₂ : ℕ) : ℝ) :=
      mul_right_cancel₀ z.im_ne_zero (by simpa using him)
    exact Nat.eq_of_mul_eq_mul_left hn (Nat.cast_injective hmul)

/-- **Linear independence of slash-invariant forms across weights.** When `Γ` has finite-index
intersection with `SL₂(ℤ)`, the evaluation `evalDirectSum` into `ℍ → ℂ` is injective. -/
theorem evalDirectSum_injective [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ] :
    Function.Injective (evalDirectSum (Γ := Γ)) := by
  classical
  refine (injective_iff_map_eq_zero evalDirectSum).mpr fun x hx ↦ ?_
  -- Choose `n > 0` so `γ₀ = (S T S⁻¹)ⁿ` maps into `Γ ⊓ 𝒮ℒ`.
  let u : SL(2, ℤ) := S * T * S⁻¹
  have hu : mapGL ℝ u ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := ⟨u, rfl⟩
  obtain ⟨n, hn, _, hmem⟩ := Γ.exists_pow_mem_of_relIndex_ne_zero Γ.relIndex_ne_zero hu
  ext k z
  simp only [DirectSum.zero_apply, FunLike.coe_zero, Pi.zero_apply]
  -- Assemble the values `x j z` into a Laurent polynomial `p ∈ ℂ[T; T⁻¹]`.
  let p : ℂ[T;T⁻¹] := ∑ j ∈ x.support, AddMonoidAlgebra.single j (x j z)
  let γ (m : ℕ) : GL (Fin 2) ℝ := mapGL ℝ (u ^ (n * m))
  have hγ_mem (m : ℕ) : γ m ∈ Γ ⊓ 𝒮ℒ := by
    have hpow : γ m = (mapGL ℝ u ^ n) ^ m := by simp [γ, pow_mul]
    exact hpow ▸ (Γ ⊓ 𝒮ℒ).pow_mem hmem m
  let d (m : ℕ) : ℂˣ := Units.mk0 (denom (γ m) z) (denom_ne_zero (γ m) z)
  have hd_val (m : ℕ) : (d m : ℂ) = -((n * m : ℕ) : ℂ) * z + 1 :=
    denom_mapGL_STS_inv_pow (n * m) z
  have hd_inj : Function.Injective d := fun m₁ m₂ hm ↦
    denom_mapGL_STS_inv_pow_injective hn z (congrArg Units.val hm)
  have hd_root (m : ℕ) : p.smeval (d m) = 0 := by
    rw [← LaurentPolynomial.leval_apply (R := ℂ), map_sum]
    simp only [LaurentPolynomial.leval_apply, LaurentPolynomial.smeval_single, smul_eq_mul,
      Units.val_zpow_eq_zpow_val]
    have hslash (j : ℤ) : x j (γ m • z) = x j z * (d m : ℂ) ^ j := by
      have hact := slash_action_eqn (x j) (γ m) (hγ_mem m).1
      simpa [d, ModularForm.slash_def, UpperHalfPlane.σ,
        mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero _ _)),
        Subgroup.HasDetOne.det_eq (hγ_mem m).2] using congr($hact z)
    calc
      ∑ j ∈ x.support, x j z * (d m : ℂ) ^ j
        = ∑ j ∈ x.support, x j (γ m • z) := Finset.sum_congr rfl fun j _ ↦ (hslash j).symm
      _ = ∑ᶠ j : ℤ, x j (γ m • z) := by
          symm
          refine finsum_eq_sum_of_support_subset _ (s := x.support) fun j hj ↦ ?_
          by_contra hjm
          exact hj (by simp [DFinsupp.notMem_support_iff.mp hjm])
      _ = evalDirectSum x (γ m • z) := (evalDirectSum_apply x (γ m • z)).symm
      _ = 0 := by simp [hx]
  have hp0 : p = 0 := LaurentPolynomial.eq_zero_of_infinite_smeval_eq_zero p <|
    (Set.infinite_range_of_injective hd_inj).mono <| by
      rintro _ ⟨m, rfl⟩
      exact hd_root m
  have hp_coeff : p.coeff k = if k ∈ x.support then x k z else 0 := by
    simp only [p, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single,
      Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  have hk0 : p.coeff k = 0 := by simp [hp0]
  by_cases hkx : k ∈ x.support
  · simpa [hp_coeff, hkx] using hk0
  · simp [DFinsupp.notMem_support_iff.mp hkx]

@[simp]
theorem evalDirectSum_inj [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {x y : ⨁ k : ℤ, SlashInvariantForm Γ k} :
    evalDirectSum x = evalDirectSum y ↔ x = y :=
  evalDirectSum_injective.eq_iff

end SlashInvariantForm

namespace ModularForm

/-- Coercion of a modular form of weight `k` to a function `ℍ → ℂ`, as a `ℂ`-linear map when
`[Γ.HasDetOne]`. -/
def coeLinearMap (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] (k : ℤ) :
    ModularForm Γ k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coeLinearMap_apply [Γ.HasDetOne] (k : ℤ) (f : ModularForm Γ k) :
    coeLinearMap Γ k f = ⇑f :=
  (rfl)

/-- Pointwise evaluation of the graded ring `⨁ k : ℤ, ModularForm Γ k` as a ring homomorphism into
`ℍ → ℂ`. -/
def evalDirectSum [Γ.HasDetPlusMinusOne] :
    (⨁ k : ℤ, ModularForm Γ k) →+* (ℍ → ℂ) :=
  DirectSum.toSemiring (fun k ↦ FunLike.coeAddMonoidHom (ModularForm Γ k) ℍ ℂ)
    rfl (fun _ _ ↦ rfl)

@[simp]
theorem evalDirectSum_of [Γ.HasDetPlusMinusOne] (k : ℤ) (f : ModularForm Γ k) :
    evalDirectSum (DirectSum.of _ k f) = ⇑f :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- Pointwise evaluation of the graded `ℂ`-algebra `⨁ k : ℤ, ModularForm Γ k` as a `ℂ`-algebra
homomorphism into `ℍ → ℂ`. -/
def evalDirectSumAlgHom [Γ.HasDetOne] :
    (⨁ k : ℤ, ModularForm Γ k) →ₐ[ℂ] (ℍ → ℂ) :=
  DirectSum.toAlgebra ℂ _ (coeLinearMap Γ) rfl (fun _ _ ↦ rfl)

@[simp]
theorem evalDirectSumAlgHom_of [Γ.HasDetOne] (k : ℤ) (f : ModularForm Γ k) :
    evalDirectSumAlgHom (DirectSum.of _ k f) = ⇑f :=
  DirectSum.toSemiring_of (fun k ↦ (coeLinearMap Γ k).toAddMonoidHom) rfl (fun _ _ ↦ rfl) k f

@[simp]
theorem evalDirectSumAlgHom_toRingHom [Γ.HasDetOne] :
    (evalDirectSumAlgHom (Γ := Γ) : (⨁ k : ℤ, ModularForm Γ k) →+* (ℍ → ℂ)) =
      evalDirectSum :=
  (rfl)

private def toSlashInvariantFormAddMonoidHom (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    ModularForm Γ k →+ SlashInvariantForm Γ k where
  toFun := toSlashInvariantForm
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem evalDirectSum_eq_slashInvariantForm_evalDirectSum [Γ.HasDetPlusMinusOne]
    (x : ⨁ k : ℤ, ModularForm Γ k) :
    evalDirectSum x =
      SlashInvariantForm.evalDirectSum (DirectSum.map (toSlashInvariantFormAddMonoidHom Γ) x) := by
  have hcomp : (evalDirectSum (Γ := Γ)).toAddMonoidHom =
      SlashInvariantForm.evalDirectSum.comp
        (DirectSum.map (toSlashInvariantFormAddMonoidHom Γ)) := by
    ext k f : 2
    simp [toSlashInvariantFormAddMonoidHom]
  exact DFunLike.congr_fun hcomp x

/-- Evaluating `ModularForm.evalDirectSum x` at `z : ℍ` sums `x k z` across all weights `k`. -/
theorem evalDirectSum_apply [Γ.HasDetPlusMinusOne]
    (x : ⨁ k : ℤ, ModularForm Γ k) (z : ℍ) :
    evalDirectSum x z = ∑ᶠ k : ℤ, x k z := by
  simp [evalDirectSum_eq_slashInvariantForm_evalDirectSum, SlashInvariantForm.evalDirectSum_apply,
    toSlashInvariantFormAddMonoidHom]

theorem evalDirectSumAlgHom_apply [Γ.HasDetOne]
    (x : ⨁ k : ℤ, ModularForm Γ k) (z : ℍ) :
    evalDirectSumAlgHom x z = ∑ᶠ k : ℤ, x k z :=
  evalDirectSum_apply x z

/-- **Linear independence of modular forms across weights.** When `Γ` has finite-index intersection
with `SL₂(ℤ)`, `ModularForm.evalDirectSum` is injective. -/
theorem evalDirectSum_injective [Γ.HasDetPlusMinusOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ] :
    Function.Injective (evalDirectSum (Γ := Γ)) := by
  have hι : Function.Injective (DirectSum.map (toSlashInvariantFormAddMonoidHom Γ)) :=
    (DirectSum.map_injective (f := toSlashInvariantFormAddMonoidHom Γ)).mpr fun _ _ _ h ↦
      DFunLike.coe_injective (congrArg (DFunLike.coe (F := SlashInvariantForm Γ _)) h)
  intro x y hxy
  apply hι
  apply SlashInvariantForm.evalDirectSum_injective
  simpa only [evalDirectSum_eq_slashInvariantForm_evalDirectSum] using hxy

@[simp]
theorem evalDirectSum_inj [Γ.HasDetPlusMinusOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {x y : ⨁ k : ℤ, ModularForm Γ k} :
    evalDirectSum x = evalDirectSum y ↔ x = y :=
  evalDirectSum_injective.eq_iff

/-- **Linear independence of modular forms across weights, as a `ℂ`-algebra map.** -/
theorem evalDirectSumAlgHom_injective [Γ.HasDetOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ] :
    Function.Injective (evalDirectSumAlgHom (Γ := Γ)) :=
  evalDirectSum_injective

@[simp]
theorem evalDirectSumAlgHom_inj [Γ.HasDetOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {x y : ⨁ k : ℤ, ModularForm Γ k} :
    evalDirectSumAlgHom x = evalDirectSumAlgHom y ↔ x = y :=
  evalDirectSumAlgHom_injective.eq_iff

end ModularForm

end
