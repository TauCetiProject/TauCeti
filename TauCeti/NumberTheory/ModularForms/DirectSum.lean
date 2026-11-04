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
additive homomorphism `TauCeti.SlashInvariantForm.evalDirectSum` from
`⨁ k : ℤ, SlashInvariantForm Γ k` to `ℍ → ℂ`, a ring homomorphism
`TauCeti.ModularForm.evalDirectSum` from `⨁ k : ℤ, ModularForm Γ k` to `ℍ → ℂ` when
`[Γ.HasDetPlusMinusOne]`, and a `ℂ`-algebra homomorphism `TauCeti.ModularForm.evalDirectSumAlgHom`
when `[Γ.HasDetOne]`.

When `Γ` has finite-index intersection with `SL₂(ℤ)` (`[Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]`), this
evaluation is injective: slash-invariant forms of distinct weights are linearly independent as
functions on `ℍ`. Indeed, `Γ ⊓ 𝒮ℒ` contains a positive power `γ₀ = (S T S⁻¹)ⁿ` (`n > 0`), whose
powers `γ₀ᵐ` have automorphy factors `denom (γ₀ᵐ) z = -n m z + 1`. Evaluating a relation among
slash-invariant forms at the orbit `γ₀ᵐ • z` turns it into a Laurent polynomial in `ℂ[T; T⁻¹]`
vanishing at the infinitely many units `-n m z + 1` (`m : ℕ`), which vanishes identically by
`LaurentPolynomial.eq_zero_of_infinite_smeval_eq_zero`.

## Main definitions

* `TauCeti.SlashInvariantForm.evalDirectSum`: pointwise evaluation
  `(⨁ k : ℤ, SlashInvariantForm Γ k) →+ (ℍ → ℂ)`.
* `TauCeti.ModularForm.evalDirectSum`: pointwise evaluation as a ring homomorphism
  `(⨁ k : ℤ, ModularForm Γ k) →+* (ℍ → ℂ)`.
* `TauCeti.ModularForm.evalDirectSumAlgHom`: pointwise evaluation as a `ℂ`-algebra homomorphism
  `(⨁ k : ℤ, ModularForm Γ k) →ₐ[ℂ] (ℍ → ℂ)`.

## Main results

* `TauCeti.SlashInvariantForm.evalDirectSum_injective`: slash-invariant forms of distinct weights
  are linearly independent under `[Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]`.
* `TauCeti.ModularForm.evalDirectSum_injective`,
  `TauCeti.ModularForm.evalDirectSumAlgHom_injective`: the corresponding injectivity statements for
  modular forms.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII.
* T. Miyake, *Modular Forms*, Theorem 2.1.2.
-/

public noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup ModularGroup
open scoped DirectSum MatrixGroups LaurentPolynomial

namespace TauCeti

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

namespace SlashInvariantForm

/-- Coercion of a slash-invariant form of weight `k` to a function `ℍ → ℂ`, as an additive monoid
homomorphism. -/
def coeAddMonoidHom (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) :
    _root_.SlashInvariantForm Γ k →+ (ℍ → ℂ) where
  toFun f := ⇑f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coeAddMonoidHom_apply (k : ℤ) (f : _root_.SlashInvariantForm Γ k) :
    coeAddMonoidHom Γ k f = ⇑f :=
  (rfl)

/-- Pointwise evaluation of a graded sum of slash-invariant forms as a function `ℍ → ℂ`. -/
def evalDirectSum : (⨁ k : ℤ, _root_.SlashInvariantForm Γ k) →+ (ℍ → ℂ) :=
  DirectSum.toAddMonoid (coeAddMonoidHom Γ)

@[simp]
theorem evalDirectSum_of (k : ℤ) (f : _root_.SlashInvariantForm Γ k) :
    evalDirectSum (DirectSum.of _ k f) = ⇑f :=
  DirectSum.toAddMonoid_of _ _ _

/-- Evaluating `evalDirectSum x` at `z : ℍ` sums the values `x k z` across all weights `k`. -/
theorem evalDirectSum_apply (x : ⨁ k : ℤ, _root_.SlashInvariantForm Γ k) (z : ℍ) :
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
    simp only [coe_mul, ModularGroup.S_inv, coe_neg, coe_S, coe_T_zpow]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    rw [hp, ← zpow_natCast]
    simp only [coe_mul, ModularGroup.S_inv, coe_neg, coe_S, coe_T_zpow]
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hg, denom, mapGL_coe_matrix, map_apply_coe]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, h10, h11]
  simp [algebraMap_int_eq]

private theorem smeval_sum_single (s : Finset ℤ) (c : ℤ → ℂ) (w : ℂˣ) :
    (∑ j ∈ s, AddMonoidAlgebra.single j (c j) : ℂ[T;T⁻¹]).smeval w =
      ∑ j ∈ s, c j * (w : ℂ) ^ j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, LaurentPolynomial.smeval_add,
      LaurentPolynomial.smeval_single, ih, smul_eq_mul, Units.val_zpow_eq_zpow_val]

private theorem coeff_sum_single_of_mem {s : Finset ℤ} {k : ℤ} (hk : k ∈ s) (c : ℤ → ℂ) :
    (∑ j ∈ s, AddMonoidAlgebra.single j (c j) : ℂ[T;T⁻¹]).coeff k = c k := by
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
  rw [← Finsupp.lapply_apply (R := ℕ), map_sum]
  simp [Finsupp.single_apply, hk]

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
  have hd_inj : Function.Injective d := fun m₁ m₂ hm ↦ by
    have him := congrArg (Complex.im ∘ Units.val) hm
    simp only [Function.comp_apply, hd_val, Complex.add_im, Complex.one_im, add_zero,
      Complex.neg_im, Complex.mul_im, Complex.natCast_im] at him
    have hmul : ((n * m₁ : ℕ) : ℝ) = ((n * m₂ : ℕ) : ℝ) :=
      mul_right_cancel₀ z.im_ne_zero (by simpa using him)
    exact Nat.eq_of_mul_eq_mul_left hn (Nat.cast_injective hmul)
  have hd_root (m : ℕ) : p.smeval (d m) = 0 := by
    rw [smeval_sum_single]
    have hslash (j : ℤ) : x j (γ m • z) = x j z * (d m : ℂ) ^ j := by
      have hact := _root_.SlashInvariantForm.slash_action_eqn (x j) (γ m) (hγ_mem m).1
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
  by_cases hkx : k ∈ x.support
  · rw [← coeff_sum_single_of_mem hkx (x · z)]
    exact (congrArg (fun q : ℂ[T;T⁻¹] ↦ q.coeff k) hp0).trans rfl
  · simp [DFinsupp.notMem_support_iff.mp hkx]

@[simp]
theorem evalDirectSum_inj [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {x y : ⨁ k : ℤ, _root_.SlashInvariantForm Γ k} :
    evalDirectSum x = evalDirectSum y ↔ x = y :=
  evalDirectSum_injective.eq_iff

end SlashInvariantForm

namespace ModularForm

/-- Coercion of a modular form of weight `k` to a function `ℍ → ℂ`, as a `ℂ`-linear map when
`[Γ.HasDetOne]`. -/
def coeLinearMap (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] (k : ℤ) :
    _root_.ModularForm Γ k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coeLinearMap_apply [Γ.HasDetOne] (k : ℤ) (f : _root_.ModularForm Γ k) :
    coeLinearMap Γ k f = ⇑f :=
  (rfl)

/-- Pointwise evaluation of the graded ring `⨁ k : ℤ, ModularForm Γ k` as a ring homomorphism into
`ℍ → ℂ`. -/
def evalDirectSum [Γ.HasDetPlusMinusOne] :
    (⨁ k : ℤ, _root_.ModularForm Γ k) →+* (ℍ → ℂ) :=
  DirectSum.toSemiring
    (fun k ↦ (SlashInvariantForm.coeAddMonoidHom Γ k).comp
      { toFun := _root_.ModularForm.toSlashInvariantForm
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
    rfl (fun _ _ ↦ rfl)

@[simp]
theorem evalDirectSum_of [Γ.HasDetPlusMinusOne] (k : ℤ) (f : _root_.ModularForm Γ k) :
    evalDirectSum (DirectSum.of _ k f) = ⇑f :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- Pointwise evaluation of the graded `ℂ`-algebra `⨁ k : ℤ, ModularForm Γ k` as a `ℂ`-algebra
homomorphism into `ℍ → ℂ`. -/
def evalDirectSumAlgHom [Γ.HasDetOne] :
    (⨁ k : ℤ, _root_.ModularForm Γ k) →ₐ[ℂ] (ℍ → ℂ) :=
  DirectSum.toAlgebra ℂ _ (coeLinearMap Γ) rfl (fun _ _ ↦ rfl)

@[simp]
theorem evalDirectSumAlgHom_of [Γ.HasDetOne] (k : ℤ) (f : _root_.ModularForm Γ k) :
    evalDirectSumAlgHom (DirectSum.of _ k f) = ⇑f :=
  DirectSum.toSemiring_of (fun k ↦ (coeLinearMap Γ k).toAddMonoidHom) rfl (fun _ _ ↦ rfl) k f

@[simp]
theorem evalDirectSumAlgHom_toRingHom [Γ.HasDetOne] :
    (evalDirectSumAlgHom (Γ := Γ) : (⨁ k : ℤ, _root_.ModularForm Γ k) →+* (ℍ → ℂ)) =
      evalDirectSum :=
  (rfl)

/-- Evaluating `ModularForm.evalDirectSum x` at `z : ℍ` sums `x k z` across all weights `k`. -/
theorem evalDirectSum_apply [Γ.HasDetPlusMinusOne]
    (x : ⨁ k : ℤ, _root_.ModularForm Γ k) (z : ℍ) :
    evalDirectSum x z = ∑ᶠ k : ℤ, x k z := by
  let ι : ∀ k : ℤ, _root_.ModularForm Γ k →+ _root_.SlashInvariantForm Γ k := fun _ ↦
    { toFun := _root_.ModularForm.toSlashInvariantForm
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hcomp : evalDirectSum.toAddMonoidHom =
      SlashInvariantForm.evalDirectSum.comp (DirectSum.map ι) := by
    ext k f : 2
    simp [ι]
  have hx := congrFun (DFunLike.congr_fun hcomp x) z
  simpa [SlashInvariantForm.evalDirectSum_apply, ι] using hx

theorem evalDirectSumAlgHom_apply [Γ.HasDetOne]
    (x : ⨁ k : ℤ, _root_.ModularForm Γ k) (z : ℍ) :
    evalDirectSumAlgHom x z = ∑ᶠ k : ℤ, x k z :=
  evalDirectSum_apply x z

/-- **Linear independence of modular forms across weights.** When `Γ` has finite-index intersection
with `SL₂(ℤ)`, `ModularForm.evalDirectSum` is injective. -/
theorem evalDirectSum_injective [Γ.HasDetPlusMinusOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ] :
    Function.Injective (evalDirectSum (Γ := Γ)) := by
  let ι : ∀ k : ℤ, _root_.ModularForm Γ k →+ _root_.SlashInvariantForm Γ k := fun _ ↦
    { toFun := _root_.ModularForm.toSlashInvariantForm
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hcomp : evalDirectSum.toAddMonoidHom =
      SlashInvariantForm.evalDirectSum.comp (DirectSum.map ι) := by
    ext k f : 2
    simp [ι]
  have hι : Function.Injective (DirectSum.map ι) :=
    (DirectSum.map_injective (f := ι)).mpr fun _ _ _ h ↦
      DFunLike.coe_injective (congrArg (DFunLike.coe (F := _root_.SlashInvariantForm Γ _)) h)
  intro x y hxy
  apply hι
  apply SlashInvariantForm.evalDirectSum_injective
  simpa [← AddMonoidHom.comp_apply, ← hcomp] using hxy

@[simp]
theorem evalDirectSum_inj [Γ.HasDetPlusMinusOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {x y : ⨁ k : ℤ, _root_.ModularForm Γ k} :
    evalDirectSum x = evalDirectSum y ↔ x = y :=
  evalDirectSum_injective.eq_iff

/-- **Linear independence of modular forms across weights, as a `ℂ`-algebra map.** -/
theorem evalDirectSumAlgHom_injective [Γ.HasDetOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ] :
    Function.Injective (evalDirectSumAlgHom (Γ := Γ)) :=
  evalDirectSum_injective

@[simp]
theorem evalDirectSumAlgHom_inj [Γ.HasDetOne] [Subgroup.IsFiniteRelIndex Γ 𝒮ℒ]
    {x y : ⨁ k : ℤ, _root_.ModularForm Γ k} :
    evalDirectSumAlgHom x = evalDirectSumAlgHom y ↔ x = y :=
  evalDirectSumAlgHom_injective.eq_iff

end ModularForm

end TauCeti

end
