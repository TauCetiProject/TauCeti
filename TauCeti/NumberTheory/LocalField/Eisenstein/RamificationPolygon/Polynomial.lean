/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import TauCeti.NumberTheory.LocalField.Different.Eisenstein
public import TauCeti.NumberTheory.LocalField.Discriminant.Height
public import TauCeti.NumberTheory.LocalField.RealAddValuation
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.Algebra.Order.Monoid.Unbundled.WithTop
import TauCeti.Data.ENat.Monoid
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.RingTheory.Polynomial.Eisenstein.ValuativeRel
import TauCeti.RingTheory.Valuation.Orthogonality

/-!
# The ramification polynomial of an Eisenstein extension

For `φ ∈ K[X]` of degree `n` and `α : L` in a field extension `L/K`, the *ramification polynomial*
is `ρ(X) = α⁻ⁿ φ(α X + α) ∈ L[X]`. When `φ` is the image in `K[X]` of an Eisenstein polynomial in
`𝒪[K][X]` over a nonarchimedean local field `K` and `L = K(α)` for a root `α` of `φ`, `ρ` has
degree `n`, `ρ(0) = 0`, roots `(σ α - α) / α` over the `K`-embeddings `σ : L →ₐ[K] M`, and integral
coefficients whose valuations come from expanding `φ(α X + α)` without cancellation on `1 ≤ i ≤ n`
(whereas at `i = 0` the terms cancel identically because `φ(α) = 0`).

## Main definitions

* `TauCeti.ramificationPolynomial`:
  `C (α⁻¹ ^ φ.natDegree) * (φ.map (algebraMap K L)).comp (C α * X + C α)` in `L[X]`.

## Main results

* `TauCeti.coeff_ramificationPolynomial`, `TauCeti.natDegree_ramificationPolynomial` and
  `Polynomial.Monic.ramificationPolynomial`: binomial coefficients, degree and monicity.
* `TauCeti.roots_map_ramificationPolynomial`,
  `TauCeti.roots_map_ramificationPolynomial_eq_map_algHom`,
  `TauCeti.roots_map_ramificationPolynomial_filter_ne_zero_eq_map_algHom`,
  `TauCeti.splits_map_ramificationPolynomial`, `Polynomial.Separable.ramificationPolynomial` and
  `TauCeti.natTrailingDegree_ramificationPolynomial`: roots, conjugate differences `(σ α - α) / α`,
  splitting, separability and trailing degree `1`.
* `TauCeti.realAddValuation_coeff_ramificationPolynomial_add_natDegree`,
  `TauCeti.addVal_coeff_ramificationPolynomial`,
  `TauCeti.realAddValuation_coeff_ramificationPolynomial`,
  `TauCeti.realAddValuation_coeff_one_ramificationPolynomial`,
  `TauCeti.realAddValuation_coeff_one_ramificationPolynomial_eq_height`,
  `TauCeti.addVal_coeff_one_ramificationPolynomial`, and
  `TauCeti.ord_intValuation_coeff_one_ramificationPolynomial`: coefficient valuations and
  `v_L(ρ₁) = H`.

## References

* O. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. 25 (1926), 1–8.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory 8 (2012), 1401–1424, §§2–3.
* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017), 2007–2038.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, and Chapter IV, §1.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField Polynomial
open scoped IntermediateField

namespace TauCeti

section Algebraic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The ramification polynomial `ρ(X) = α⁻ⁿ φ(α X + α)` attached to `φ : K[X]` and `α : L`. -/
def ramificationPolynomial (φ : K[X]) (α : L) : L[X] :=
  C (α⁻¹ ^ φ.natDegree) * (φ.map (algebraMap K L)).comp (C α * X + C α)

/-- Unfolding `ramificationPolynomial` to its defining composition. -/
theorem ramificationPolynomial_def (φ : K[X]) (α : L) :
    ramificationPolynomial φ α =
      C (α⁻¹ ^ φ.natDegree) * (φ.map (algebraMap K L)).comp (C α * X + C α) := (rfl)

/-- Evaluating `ramificationPolynomial φ α` at `x : L` gives `α⁻ⁿ φ(α x + α)`. -/
theorem eval_ramificationPolynomial (φ : K[X]) (α x : L) :
    (ramificationPolynomial φ α).eval x =
      α⁻¹ ^ φ.natDegree * (φ.map (algebraMap K L)).eval (α * x + α) := by
  simp [ramificationPolynomial, eval_comp]

/-- Base-changing `ramificationPolynomial φ α` along a tower `M/L/K`. -/
theorem map_ramificationPolynomial {M : Type*} [CommRing M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (φ : K[X]) (α : L) :
    (ramificationPolynomial φ α).map (algebraMap L M) =
      C (algebraMap L M α⁻¹ ^ φ.natDegree) *
        (φ.map (algebraMap K M)).comp (C (algebraMap L M α) * X + C (algebraMap L M α)) := by
  rw [ramificationPolynomial, Polynomial.map_mul, map_C, map_pow, Polynomial.map_comp,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L M, Polynomial.map_add,
    Polynomial.map_mul, map_C, map_X]

/-- The constant coefficient of `ramificationPolynomial φ α` is `α⁻ⁿ φ(α)`. -/
theorem coeff_zero_ramificationPolynomial (φ : K[X]) (α : L) :
    (ramificationPolynomial φ α).coeff 0 =
      α⁻¹ ^ φ.natDegree * (φ.map (algebraMap K L)).eval α := by
  rw [coeff_zero_eq_eval_zero, eval_ramificationPolynomial, mul_zero, zero_add]

/-- When `α` is a root of `φ`, the constant coefficient of `ramificationPolynomial φ α` vanishes. -/
theorem coeff_zero_ramificationPolynomial_of_isRoot {φ : K[X]} {α : L}
    (hroot : (φ.map (algebraMap K L)).IsRoot α) :
    (ramificationPolynomial φ α).coeff 0 = 0 := by
  rw [coeff_zero_ramificationPolynomial, hroot.eq_zero, mul_zero]

/-- When `α` is a root of `φ`, `0` is a root of `ramificationPolynomial φ α`. -/
theorem isRoot_zero_ramificationPolynomial {φ : K[X]} {α : L}
    (hroot : (φ.map (algebraMap K L)).IsRoot α) :
    (ramificationPolynomial φ α).IsRoot 0 := by
  rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_ramificationPolynomial_of_isRoot hroot]

/-- Binomial formula `ρ_i = α⁻ⁿ ∑_{h ∈ [i, n]} C(h, i) φ_h α^h` for `ramificationPolynomial`. -/
theorem coeff_ramificationPolynomial (φ : K[X]) (α : L) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i =
      α⁻¹ ^ φ.natDegree *
        ∑ h ∈ Finset.Icc i φ.natDegree,
          (h.choose i : L) * algebraMap K L (φ.coeff h) * α ^ h := by
  have hlin : C α * X + C α = C α * (X + 1) := by simp [mul_add]
  rw [ramificationPolynomial, coeff_C_mul, hlin, comp_eq_sum_left, coeff_sum,
    sum_over_range' _ (by simp) (φ.natDegree + 1) (Nat.lt_succ_of_le natDegree_map_le)]
  congr 1
  trans ∑ h ∈ Finset.range (φ.natDegree + 1),
      (h.choose i : L) * algebraMap K L (φ.coeff h) * α ^ h
  · refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [mul_pow, ← mul_assoc, ← C_pow, ← C_mul, coeff_C_mul, coeff_X_add_one_pow, coeff_map]
    ring
  · exact (Finset.sum_subset
      (fun h hh ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hh).2))
      fun h hh hnot ↦ by simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge fun hi ↦
        hnot (Finset.mem_Icc.mpr ⟨hi, Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)⟩))]).symm

/-- Multiplying `(ramificationPolynomial φ α).coeff i` by `α ^ φ.natDegree` when `α ≠ 0`. -/
theorem coeff_ramificationPolynomial_mul_pow (φ : K[X]) {α : L} (hα : α ≠ 0) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i * α ^ φ.natDegree =
      ∑ h ∈ Finset.Icc i φ.natDegree,
        (h.choose i : L) * algebraMap K L (φ.coeff h) * α ^ h := by
  rw [coeff_ramificationPolynomial, mul_right_comm, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hα),
    one_mul]

/-- Above `φ.natDegree`, all coefficients of `ramificationPolynomial φ α` vanish. -/
theorem coeff_ramificationPolynomial_eq_zero_of_lt {φ : K[X]} {α : L} {i : ℕ}
    (hi : φ.natDegree < i) : (ramificationPolynomial φ α).coeff i = 0 := by
  rw [coeff_ramificationPolynomial, Finset.Icc_eq_empty (not_le.mpr hi), Finset.sum_empty, mul_zero]

/-- The degree of `ramificationPolynomial φ α` is at most `φ.natDegree`. -/
theorem natDegree_ramificationPolynomial_le (φ : K[X]) (α : L) :
    (ramificationPolynomial φ α).natDegree ≤ φ.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hi ↦ coeff_ramificationPolynomial_eq_zero_of_lt hi

/-- For `α ≠ 0`, the `φ.natDegree`-th coefficient of `ramificationPolynomial φ α` is `φ_n`. -/
theorem coeff_natDegree_ramificationPolynomial (φ : K[X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).coeff φ.natDegree = algebraMap K L φ.leadingCoeff := by
  rw [coeff_ramificationPolynomial, Finset.Icc_self, Finset.sum_singleton, Nat.choose_self,
    Nat.cast_one, one_mul, coeff_natDegree, ← mul_assoc, mul_right_comm, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hα), one_mul]

/-- For `α ≠ 0`, `ramificationPolynomial φ α` has degree `φ.natDegree`. -/
theorem natDegree_ramificationPolynomial (φ : K[X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).natDegree = φ.natDegree := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · simp [ramificationPolynomial]
  · exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_ramificationPolynomial_le φ α) <|
      (coeff_natDegree_ramificationPolynomial φ hα).symm ▸
        (map_ne_zero (algebraMap K L)).mpr (leadingCoeff_ne_zero.mpr hφ)

/-- For `α ≠ 0`, `ramificationPolynomial φ α = 0` iff `φ = 0`. -/
theorem ramificationPolynomial_eq_zero_iff {φ : K[X]} {α : L} (hα : α ≠ 0) :
    ramificationPolynomial φ α = 0 ↔ φ = 0 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simp [ramificationPolynomial]⟩
  have hcoeff := congrArg (·.coeff φ.natDegree) h
  rw [coeff_natDegree_ramificationPolynomial φ hα, coeff_zero] at hcoeff
  exact leadingCoeff_eq_zero.mp ((map_eq_zero (algebraMap K L)).mp hcoeff)

/-- The linear coefficient of `ramificationPolynomial φ α` is `α⁻¹ ^ φ.natDegree * (φ'(α) * α)`. -/
theorem coeff_one_ramificationPolynomial (φ : K[X]) (α : L) :
    (ramificationPolynomial φ α).coeff 1 =
      α⁻¹ ^ φ.natDegree * ((φ.derivative.map (algebraMap K L)).eval α * α) := by
  have hc1 : (ramificationPolynomial φ α).coeff 1 =
      (ramificationPolynomial φ α).derivative.eval 0 := by
    simp [← coeff_zero_eq_eval_zero, coeff_derivative]
  rw [hc1, ramificationPolynomial, derivative_C_mul, derivative_comp, derivative_add, derivative_C,
    add_zero, derivative_C_mul, derivative_X, mul_one, derivative_map]
  simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_zero, zero_add]; ring

/-- When `α` is a root of `φ` and `ramificationPolynomial φ α` is separable, its linear
coefficient is nonzero. -/
theorem coeff_one_ramificationPolynomial_ne_zero {φ : K[X]} {α : L}
    (hroot : (φ.map (algebraMap K L)).IsRoot α)
    (hsep : (ramificationPolynomial φ α).Separable) :
    (ramificationPolynomial φ α).coeff 1 ≠ 0 := by
  simpa [eval₂_id, ← coeff_zero_eq_eval_zero, coeff_derivative] using
    hsep.eval₂_derivative_ne_zero (RingHom.id L) (isRoot_zero_ramificationPolynomial hroot)

/-- When `α` is a root of `φ` and `ramificationPolynomial φ α` is separable, its trailing
degree is `1`. -/
theorem natTrailingDegree_ramificationPolynomial {φ : K[X]} {α : L}
    (hroot : (φ.map (algebraMap K L)).IsRoot α)
    (hsep : (ramificationPolynomial φ α).Separable) :
    (ramificationPolynomial φ α).natTrailingDegree = 1 := by
  have hc1 := coeff_one_ramificationPolynomial_ne_zero hroot hsep
  refine le_antisymm (natTrailingDegree_le_of_ne_zero hc1)
    (le_natTrailingDegree (fun h0 ↦ hc1 (by simp [h0])) fun m hm ↦ ?_)
  obtain rfl : m = 0 := by omega
  exact coeff_zero_ramificationPolynomial_of_isRoot hroot

section OverField

variable {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- For `α ≠ 0`, the roots in `M` of `ramificationPolynomial φ α` are `(r - α) / α` (`φ(r) = 0`). -/
theorem roots_map_ramificationPolynomial (φ : K[X]) {α : L} (hα : α ≠ 0) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).roots =
      (φ.map (algebraMap K M)).roots.map
        fun r ↦ (r - algebraMap L M α) / algebraMap L M α := by
  have haM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα
  have hainv : algebraMap L M α⁻¹ ^ φ.natDegree ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero (algebraMap L M)).mpr (inv_ne_zero hα))
  rw [map_ramificationPolynomial (M := M), roots_C_mul _ hainv,
    roots_comp_C_mul_X_add_C _ _ _ (IsUnit.mk0 _ haM)]
  exact Multiset.map_congr rfl fun r _ ↦ by rw [Ring.inverse_eq_inv', div_eq_inv_mul, mul_comm]

/-- If `φ` splits over `M`, then `ramificationPolynomial φ α` splits over `M`. -/
theorem splits_map_ramificationPolynomial {φ : K[X]} (α : L)
    (hsplit : (φ.map (algebraMap K M)).Splits) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).Splits := by
  rw [map_ramificationPolynomial (M := M)]
  exact Splits.mul (Splits.C _) (hsplit.comp_of_natDegree_le_one (by compute_degree!))

end OverField

end Algebraic

end TauCeti

namespace Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `φ` is monic and `α ≠ 0`, then `ramificationPolynomial φ α` is monic. -/
theorem Monic.ramificationPolynomial {φ : K[X]} (hφ : φ.Monic) {α : L} (hα : α ≠ 0) :
    (TauCeti.ramificationPolynomial φ α).Monic := by
  rw [Monic, Polynomial.leadingCoeff, TauCeti.natDegree_ramificationPolynomial φ hα,
    TauCeti.coeff_natDegree_ramificationPolynomial φ hα, hφ.leadingCoeff,
    map_one (algebraMap K L)]

/-- If `φ` is separable and `α ≠ 0`, then `ramificationPolynomial φ α` is separable. -/
theorem Separable.ramificationPolynomial {φ : K[X]} (hsep : φ.Separable) {α : L} (hα : α ≠ 0) :
    (TauCeti.ramificationPolynomial φ α).Separable := by
  obtain ⟨u, v, huv⟩ := hsep.map (f := algebraMap K L)
  set P := φ.map (algebraMap K L)
  set g : L[X] := C α * X + C α; set c : L := α⁻¹ ^ φ.natDegree
  have hc : c ≠ 0 := pow_ne_zero _ (inv_ne_zero hα)
  have hcomp := congrArg (·.comp g) huv
  simp only [add_comp, mul_comp, one_comp] at hcomp
  refine ⟨C c⁻¹ * u.comp g, C (c * α)⁻¹ * v.comp g, ?_⟩
  rw [TauCeti.ramificationPolynomial_def, derivative_C_mul, derivative_comp, derivative_add,
    derivative_C, add_zero, derivative_C_mul, derivative_X, mul_one]
  trans C (c⁻¹ * c) * (u.comp g * P.comp g) +
      C ((c * α)⁻¹ * (c * α)) * (v.comp g * P.derivative.comp g)
  · simp only [P, g, c, C_mul]; ring
  · rw [inv_mul_cancel₀ hc, inv_mul_cancel₀ (mul_ne_zero hc hα), C_1, one_mul, one_mul, hcomp]

end Polynomial

namespace TauCeti

section EisensteinSeparable

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]

/-- If `α : L` is a separable root of an Eisenstein polynomial `φ : 𝒪[K][X]`, then
`ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α` is separable. -/
theorem separable_ramificationPolynomial_of_eisenstein {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α)
    (hsep : IsSeparable K α) :
    (ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).Separable := by
  have hsepφ : (φ.map (algebraMap 𝒪[K] K)).Separable := by
    rw [hφ.map_eq_C_leadingCoeff_mul_minpoly hroot]
    exact Polynomial.Separable.unit_mul
      ((hφ.isUnit_leadingCoeff.map (algebraMap 𝒪[K] K)).map C) hsep
  exact hsepφ.ramificationPolynomial (hφ.ne_zero_of_isRoot hroot)

/-- **Conjugate-difference description of the roots of `ramificationPolynomial`**: in any extension
field `M` of a separable extension `L = K⟮α⟯` generated by a root `α : L` of an Eisenstein
polynomial `φ : 𝒪[K][X]`, the roots of `ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α` in
`M` are `(σ α - α) / α` as `σ` ranges over all `K`-embeddings `L →ₐ[K] M` (each occurring once). -/
theorem roots_map_ramificationPolynomial_eq_map_algHom {M : Type*} [Algebra.IsSeparable K L]
    [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Fintype (L →ₐ[K] M)]
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).map (algebraMap L M)).roots =
      (Finset.univ : Finset (L →ₐ[K] M)).val.map
        fun σ ↦ (σ α - algebraMap L M α) / algebraMap L M α := by
  rw [roots_map_ramificationPolynomial _ (hφ.ne_zero_of_isRoot hroot),
    hφ.roots_map_eq_map_algHom hroot hgen, Multiset.map_map, Function.comp_def]

/-- **Nonzero roots of `ramificationPolynomial`**: filtering out the root `0` (contributed by the
canonical inclusion `IsScalarTower.toAlgHom K L M`) leaves `(σ α - α) / α` over all nontrivial
`K`-embeddings `σ ≠ IsScalarTower.toAlgHom K L M`. -/
theorem roots_map_ramificationPolynomial_filter_ne_zero_eq_map_algHom {M : Type*}
    [Algebra.IsSeparable K L] [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Fintype (L →ₐ[K] M)] [DecidableEq M] [DecidableEq (L →ₐ[K] M)]
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    (((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).map (algebraMap L M)).roots.filter
        (· ≠ 0)) =
      ((Finset.univ : Finset (L →ₐ[K] M)).erase (IsScalarTower.toAlgHom K L M)).val.map
        fun σ ↦ (σ α - algebraMap L M α) / algebraMap L M α := by
  have hαM : algebraMap L M α ≠ 0 :=
    (_root_.map_ne_zero (algebraMap L M)).mpr (hφ.ne_zero_of_isRoot hroot)
  let pb : PowerBasis K L :=
    PowerBasis.ofAdjoinSimpleEqTop (hφ.isIntegral_of_isRoot hroot) hgen
  have hpb_gen : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  have hsigma_eq (σ : L →ₐ[K] M) :
      (σ α - algebraMap L M α) / algebraMap L M α = 0 ↔ σ = IsScalarTower.toAlgHom K L M := by
    rw [div_eq_zero_iff, or_iff_left hαM, sub_eq_zero]
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, IsScalarTower.toAlgHom_apply]⟩
    apply pb.algHom_ext
    rw [hpb_gen, h, IsScalarTower.toAlgHom_apply]
  rw [roots_map_ramificationPolynomial_eq_map_algHom hφ hroot hgen, Multiset.filter_map]
  congr 1
  rw [← Finset.filter_val]
  congr 1
  ext σ
  simp [Finset.mem_erase, hsigma_eq, and_comm]

end EisensteinSeparable

section LeadingValuation

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- When `φ.leadingCoeff` is a unit of `𝒪[K]` and `α ≠ 0`,
`(ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff φ.natDegree` has `realAddValuation`
equal to `0`. -/
theorem realAddValuation_coeff_natDegree_ramificationPolynomial {φ : 𝒪[K][X]}
    (hu : IsUnit φ.leadingCoeff) {α : L} (hα : α ≠ 0) :
    realAddValuation L
      ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff φ.natDegree) = 0 := by
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := FaithfulSMul.algebraMap_injective 𝒪[K] K
  rw [← natDegree_map_eq_of_injective hinj, coeff_natDegree_ramificationPolynomial _ hα,
    leadingCoeff_map_of_injective hinj, Algebra.algebraMap_ofSubsemiring_apply,
    ← Valuation.HasExtension.val_algebraMap (vA := valuation L),
    isUnit_iff_realAddValuation_eq_zero.mp (hu.map (algebraMap 𝒪[K] 𝒪[L]))]

end LeadingValuation

section LocalField

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- If `α : L` is a root of an Eisenstein `φ : 𝒪[K][X]` with `K⟮α⟯ = ⊤`, then `α ∈ 𝒪[L]` is a
root of `φ.map (algebraMap 𝒪[K] 𝒪[L])` and a uniformizer of `𝒪[L]`, with `α ≠ 0`,
`realAddValuation L α = 1`, and `e(L/K) = φ.natDegree`. -/
theorem irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    ∃ hα : α ∈ 𝒪[L], (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ⟨α, hα⟩ ∧
      Irreducible (⟨α, hα⟩ : 𝒪[L]) ∧ α ≠ 0 ∧ realAddValuation L α = 1 ∧
      ramificationIndex K L = φ.natDegree := by
  have hα : α ∈ 𝒪[L] := hφ.mem_integer_of_isRoot hroot
  have hroot' : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ⟨α, hα⟩ :=
    isRoot_map_integerRing_iff.mpr hroot
  have hξ := irreducible_of_eisenstein_adjoin_eq_top φ hφ ⟨α, hα⟩ hroot' hgen
  exact ⟨hα, hroot', hξ, fun h ↦ hξ.ne_zero (Subtype.ext h), realAddValuation_irreducible hξ,
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ⟨α, hα⟩ hroot' hgen⟩

/-- Exact valuation formula for `1 ≤ i`:
`v_L(ρ_i) + n = min_{i ≤ h ≤ n} (n · v_K(C(h, i) φ_h) + h)`, where `n = φ.natDegree`. -/
theorem realAddValuation_coeff_ramificationPolynomial_add_natDegree {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {i : ℕ} (hi : 1 ≤ i) :
    realAddValuation L ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i) +
        (φ.natDegree : WithTop ℝ) =
      (Finset.Icc i φ.natDegree).inf fun h ↦
        (realAddValuation K (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K)).map
          ((φ.natDegree : ℝ) * ·) + (h : WithTop ℝ) := by
  obtain ⟨-, -, -, hα0, hvα, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hφ hroot hgen
  have hdeg : (φ.map (algebraMap 𝒪[K] K)).natDegree = φ.natDegree :=
    natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) φ
  set n := φ.natDegree; let c (h : ℕ) : 𝒪[K] := (h.choose i : 𝒪[K]) * φ.coeff h
  let t (h : ℕ) : L := algebraMap K L (c h : K) * α ^ h
  have hterm (h : ℕ) : realAddValuation L (t h) =
      (realAddValuation K (c h : K)).map ((n : ℝ) * ·) + (h : WithTop ℝ) := by
    rw [(realAddValuation L).map_mul, realAddValuation_algebraMap, he,
      (realAddValuation L).map_pow, hvα, nsmul_one]
  have hval_mul :
      realAddValuation L ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i) +
          (n : WithTop ℝ) =
        realAddValuation L ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i *
          α ^ (φ.map (algebraMap 𝒪[K] K)).natDegree) := by
    rw [(realAddValuation L).map_mul, (realAddValuation L).map_pow, hvα, nsmul_one, hdeg]
  have hsum_t (h : ℕ) :
      (h.choose i : L) * algebraMap K L ((φ.map (algebraMap 𝒪[K] K)).coeff h) * α ^ h = t h := by
    simp [t, c, Algebra.algebraMap_ofSubsemiring_apply]
  rw [hval_mul, coeff_ramificationPolynomial_mul_pow _ hα0 i, hdeg,
    Finset.sum_congr rfl fun h _ ↦ hsum_t h, (realAddValuation L).map_sum_eq_inf_of_ne]
  · exact Finset.inf_congr rfl fun h _ ↦ hterm h
  · intro h₁ hh₁ h₂ hh₂ hne ht₁ ht₂ heq
    rw [hterm, realAddValuation_coe_integer] at ht₁ ht₂
    rw [hterm, hterm, realAddValuation_coe_integer, realAddValuation_coe_integer] at heq
    cases ha₁ : IsDiscreteValuationRing.addVal 𝒪[K] (c h₁) using ENat.recTopCoe with
    | top => exact ht₁ (by simp [ha₁])
    | coe m₁ =>
      cases ha₂ : IsDiscreteValuationRing.addVal 𝒪[K] (c h₂) using ENat.recTopCoe with
      | top => exact ht₂ (by simp [ha₂])
      | coe m₂ =>
        rw [ha₁, ha₂] at heq
        simp only [ENat.map_natCast, WithTop.map_coe, ← WithTop.coe_natCast,
          ← WithTop.coe_add, WithTop.coe_eq_coe] at heq
        have hnat : n * m₁ + h₁ = n * m₂ + h₂ := by exact_mod_cast heq
        obtain ⟨_, h₁n⟩ := Finset.mem_Icc.mp hh₁; obtain ⟨_, h₂n⟩ := Finset.mem_Icc.mp hh₂
        rcases lt_trichotomy m₁ m₂ with hm | rfl | hm
        · have := Nat.mul_succ n m₁ ▸ Nat.mul_le_mul_left n hm; omega
        · omega
        · have := Nat.mul_succ n m₂ ▸ Nat.mul_le_mul_left n hm; omega

/-- Every coefficient of `ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α` for an Eisenstein
root has `0 ≤ v_L`. -/
theorem realAddValuation_coeff_ramificationPolynomial_nonneg {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (i : ℕ) :
    0 ≤ realAddValuation L ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i) := by
  rcases eq_or_ne i 0 with rfl | hi0
  · simp [coeff_zero_ramificationPolynomial_of_isRoot hroot]
  have hdeg : (φ.map (algebraMap 𝒪[K] K)).natDegree = φ.natDegree :=
    natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) φ
  rcases lt_or_ge φ.natDegree i with hgt | _
  · simp [coeff_ramificationPolynomial_eq_zero_of_lt (hdeg.symm ▸ hgt)]
  have hmono : Monotone (WithTop.map ((φ.natDegree : ℝ) * ·)) :=
    WithTop.monotone_map_iff.mpr fun _ _ hab ↦ mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)
  refine (WithTop.add_le_add_iff_right (WithTop.natCast_ne_top φ.natDegree)).mp ?_
  rw [zero_add, realAddValuation_coeff_ramificationPolynomial_add_natDegree hφ hroot hgen
    (Nat.one_le_iff_ne_zero.mpr hi0), Finset.le_inf_iff]
  intro h hh
  rcases eq_or_lt_of_le (Finset.mem_Icc.mp hh).2 with h_eq | hlt
  · simpa [h_eq] using add_le_add (hmono (mem_integer_iff_realAddValuation_nonneg.mp
      ((h.choose i : 𝒪[K]) * φ.coeff h).property)) (le_rfl : (h : WithTop ℝ) ≤ h)
  · refine le_trans (by simp [← WithTop.coe_natCast, ← WithTop.coe_add])
      (add_le_add (hmono (mem_maximalIdeal_iff_one_le_realAddValuation.mp
        (Ideal.mul_mem_left _ _ (hφ.mem hlt)))) le_rfl)

/-- Every coefficient of `ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α` for an Eisenstein
root lies in `𝒪[L]`. -/
theorem coeff_ramificationPolynomial_mem_integer {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (i : ℕ) : (ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i ∈ 𝒪[L] :=
  mem_integer_iff_realAddValuation_nonneg.mpr
    (realAddValuation_coeff_ramificationPolynomial_nonneg hφ hroot hgen i)

private theorem addVal_coeff_ramificationPolynomial_add_natDegree_eq {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        ⟨(ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i,
          coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩ +
      (φ.natDegree : ℕ∞) =
      ⨅ h ∈ Finset.Icc i φ.natDegree,
        (φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
          ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞)) := by
  obtain ⟨hi1, hin⟩ := Finset.mem_Icc.mp hi
  have hn0 : φ.natDegree ≠ 0 := by omega
  have Hne : (Finset.Icc i φ.natDegree).Nonempty := ⟨φ.natDegree, Finset.right_mem_Icc.mpr hin⟩
  rw [← Finset.inf_eq_iInf, ← Finset.inf'_eq_inf Hne]
  refine ENat.map_natCast_injective (α := ℝ) ?_
  rw [ENat.map_natCast_add, ← realAddValuation_coe_integer, ENat.map_natCast, WithTop.coe_natCast,
    realAddValuation_coeff_ramificationPolynomial_add_natDegree hφ hroot hgen hi1,
    ← Finset.inf'_eq_inf Hne,
    Finset.apply_inf'_eq_inf'_comp Hne (ENat.map ((↑) : ℕ → ℝ)) fun _ _ ↦
      (ENat.map_natCast_strictMono (α := ℝ)).monotone.map_min]
  exact Finset.inf'_congr Hne rfl fun h _ ↦ by
    rw [Function.comp_apply, ENat.map_natCast_add, ENat.map_natCast_nsmul,
      ← realAddValuation_coe_integer, WithTop.nsmul_eq_map hn0]
    simp [nsmul_eq_mul]

/-- **Exact DVR valuation formula for the coefficients of `ramificationPolynomial`**: for
`1 ≤ i ≤ φ.natDegree`,
`v_L(ρ_i) = (⨅_{i ≤ h ≤ n} (n • v_K(C(h, i) φ_h) + h)) - n` in `ℕ∞`. -/
theorem addVal_coeff_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        ⟨(ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i,
          coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩ =
      (⨅ h ∈ Finset.Icc i φ.natDegree,
        (φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
          ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞))) - φ.natDegree := by
  rw [← addVal_coeff_ramificationPolynomial_add_natDegree_eq hφ hroot hgen hi,
    (ENat.addLECancellable_natCast φ.natDegree).add_tsub_cancel_right]

/-- **Exact subtractive `WithTop ℝ` valuation formula** for the coefficients of
`ramificationPolynomial`: for `1 ≤ i ≤ φ.natDegree`,
`v_L(ρ_i) = min_{i ≤ h ≤ n} (n · v_K(C(h, i) φ_h) + h) - n`. -/
theorem realAddValuation_coeff_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    realAddValuation L ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff i) =
      ((Finset.Icc i φ.natDegree).inf fun h ↦
        (realAddValuation K (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K)).map
          ((φ.natDegree : ℝ) * ·) + (h : WithTop ℝ)) -
        ((φ.natDegree : ℝ) : WithTop ℝ) := by
  rw [← realAddValuation_coeff_ramificationPolynomial_add_natDegree hφ hroot hgen
      (Finset.mem_Icc.mp hi).1, ← WithTop.coe_natCast,
    (LinearOrderedAddCommGroupWithTop.isAddUnit_iff.mpr WithTop.coe_ne_top).add_sub_cancel_right]

section Separable

variable [Algebra.IsSeparable K L]

/-- In separable `L = K(α)`, `(ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff 1` has
height `d(L/K) + 1 - n`. -/
theorem realAddValuation_coeff_one_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    realAddValuation L ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff 1) =
      (((differentExponent K L : ℝ) + 1 - φ.natDegree : ℝ) : WithTop ℝ) := by
  obtain ⟨hα, hroot', -, hα0, hvα, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hφ hroot hgen
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hdeg : (φ.map (algebraMap 𝒪[K] K)).natDegree = φ.natDegree :=
    natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K) φ
  have hdiff :=
    Polynomial.natCast_differentExponent_eq_addVal_aeval_derivative_of_eisenstein_adjoin_eq_top
      φ hφ ξ hroot' hgen
  have hcoe : ((aeval ξ φ.derivative : 𝒪[L]) : L) =
      ((φ.derivative.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).eval α := by
    rw [← Algebra.algebraMap_ofSubsemiring_apply, aeval_def, hom_eval₂,
      algebraMap_comp_algebraMap_integerRing, Algebra.algebraMap_ofSubsemiring_apply,
      Polynomial.map_map, eval_map]
  have hmul :
      (ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff 1 * α ^ φ.natDegree =
        ((aeval ξ φ.derivative : 𝒪[L]) : L) * α := by
    rw [coeff_one_ramificationPolynomial, hdeg, derivative_map, hcoe, mul_right_comm, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hα0), one_mul]
  have hval := congrArg (realAddValuation L) hmul
  rw [(realAddValuation L).map_mul, (realAddValuation L).map_pow, hvα, nsmul_one,
    (realAddValuation L).map_mul, realAddValuation_coe_integer, ← hdiff, ENat.map_natCast,
    hvα] at hval
  refine (WithTop.add_right_inj (WithTop.natCast_ne_top φ.natDegree)).mp ?_
  rw [hval, ← WithTop.coe_natCast, ← WithTop.coe_one, ← WithTop.coe_add, ← WithTop.coe_add]
  congr 1; ring

/-- **The linear-term valuation of `ramificationPolynomial` in `WithTop ℝ` is `height K L`.** -/
theorem realAddValuation_coeff_one_ramificationPolynomial_eq_height {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    realAddValuation L ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff 1) =
      (height K L : WithTop ℝ) := by
  obtain ⟨-, -, -, -, -, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hφ hroot hgen
  have hh : (height K L : ℝ) + φ.natDegree = (differentExponent K L : ℝ) + 1 := by
    have := height_add_ramificationIndex K L; rw [he] at this; exact_mod_cast this
  rw [realAddValuation_coeff_one_ramificationPolynomial hφ hroot hgen, ← WithTop.coe_natCast]
  congr 1; linarith

/-- **The linear-term DVR valuation of `ramificationPolynomial` is `height K L`.** -/
theorem addVal_coeff_one_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        ⟨(ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff 1,
          coeff_ramificationPolynomial_mem_integer hφ hroot hgen 1⟩ =
      (height K L : ℕ∞) :=
  ENat.map_natCast_injective (α := ℝ) <|
    (realAddValuation_coe_integer _).symm.trans <| by
      rw [realAddValuation_coeff_one_ramificationPolynomial_eq_height hφ hroot hgen,
        ENat.map_natCast, WithTop.coe_natCast]

/-- **The linear-term integer valuation of `ramificationPolynomial` is `height K L`.** -/
theorem ord_intValuation_coeff_one_ramificationPolynomial {φ : 𝒪[K][X]}
    (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K L)).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    Valuation.ord (intValuation L)
      ((ramificationPolynomial (φ.map (algebraMap 𝒪[K] K)) α).coeff 1) = height K L :=
  ord_intValuation_of_addVal_eq_natCast (addVal_coeff_one_ramificationPolynomial hφ hroot hgen)

end Separable

end LocalField

end TauCeti
