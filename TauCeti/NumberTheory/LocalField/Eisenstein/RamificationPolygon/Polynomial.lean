/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import TauCeti.NumberTheory.LocalField.Different.Eisenstein
public import TauCeti.NumberTheory.LocalField.RealAddValuation
import Mathlib.FieldTheory.Separable
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.RingTheory.Valuation.Orthogonality
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# The ramification polynomial of an Eisenstein extension

For `φ ∈ 𝒪[K][X]` of degree `n` and `α : L` in an extension `L/K`, the *ramification polynomial* is
`ρ(X) = α⁻ⁿ φ(α X + α) ∈ L[X]`. When `φ` is monic Eisenstein over a nonarchimedean local field `K`
and `L = K(α)` for a root `α` of `φ`, `ρ` is monic of degree `n` with `ρ(0) = 0`, roots
`(α' - α) / α`, and integral coefficients whose valuations come from expanding `φ(α X + α)`.

## Main definitions

* `TauCeti.ramificationPolynomial`: `C (α⁻¹ ^ φ.natDegree) * (φ.map _).comp (C α * X + C α)` in
  `L[X]`.

## Main results

* `TauCeti.coeff_ramificationPolynomial`, `Polynomial.Monic.natDegree_ramificationPolynomial` and
  `Polynomial.Monic.ramificationPolynomial`: binomial coefficients, degree and monicity.
* `TauCeti.roots_map_ramificationPolynomial`, `TauCeti.splits_map_ramificationPolynomial` and
  `Polynomial.Separable.ramificationPolynomial`: roots, splitting and separability.
* `TauCeti.realAddValuation_coeff_ramificationPolynomial_add_natDegree`,
  `TauCeti.realAddValuation_coeff_one_ramificationPolynomial` and
  `TauCeti.natTrailingDegree_ramificationPolynomial`: coefficient valuations, `v_L(ρ₁)` and
  trailing degree `1`.

## References

* O. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. 25 (1926), 1–8.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory 8 (2012), 1401–1424, §§2–3.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, and Chapter IV, §1.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField Polynomial
open scoped IntermediateField

namespace TauCeti

section Algebraic

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]

/-- The ramification polynomial `ρ(X) = α⁻ⁿ φ(α X + α)` attached to `φ : 𝒪[K][X]` and `α : L`. -/
def ramificationPolynomial (φ : 𝒪[K][X]) (α : L) : L[X] :=
  C (α⁻¹ ^ φ.natDegree) *
    (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α)

/-- Unfolding `ramificationPolynomial` to its defining composition. -/
theorem ramificationPolynomial_def (φ : 𝒪[K][X]) (α : L) :
    ramificationPolynomial φ α =
      C (α⁻¹ ^ φ.natDegree) *
        (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α) := (rfl)

/-- Evaluating `ramificationPolynomial φ α` at `x : L` gives `α⁻ⁿ φ(α x + α)`. -/
theorem eval_ramificationPolynomial (φ : 𝒪[K][X]) (α x : L) :
    (ramificationPolynomial φ α).eval x =
      α⁻¹ ^ φ.natDegree * (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).eval (α * x + α) := by
  simp [ramificationPolynomial, eval_comp]

/-- Base-changing `ramificationPolynomial φ α` along a tower `M/L/K`. -/
theorem map_ramificationPolynomial {M : Type*} [CommRing M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).map (algebraMap L M) =
      C (algebraMap L M α⁻¹ ^ φ.natDegree) *
        (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).comp
          (C (algebraMap L M α) * X + C (algebraMap L M α)) := by
  have hmap : (algebraMap L M).comp ((algebraMap K L).comp (algebraMap 𝒪[K] K)) =
      (algebraMap K M).comp (algebraMap 𝒪[K] K) :=
    RingHom.ext fun a ↦ (IsScalarTower.algebraMap_apply K L M (algebraMap 𝒪[K] K a)).symm
  rw [ramificationPolynomial, Polynomial.map_mul, map_C, map_pow, Polynomial.map_comp,
    Polynomial.map_map, hmap, Polynomial.map_add, Polynomial.map_mul, map_C, map_X]

/-- The constant coefficient of `ramificationPolynomial φ α` is `α⁻ⁿ φ(α)`. -/
theorem coeff_zero_ramificationPolynomial (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).coeff 0 =
      α⁻¹ ^ φ.natDegree * (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).eval α := by
  rw [coeff_zero_eq_eval_zero, eval_ramificationPolynomial, mul_zero, zero_add]

/-- When `α` is a root of `φ`, the constant coefficient of `ramificationPolynomial φ α` vanishes. -/
theorem coeff_zero_ramificationPolynomial_of_isRoot {φ : 𝒪[K][X]} {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).coeff 0 = 0 := by
  rw [coeff_zero_ramificationPolynomial, hroot.eq_zero, mul_zero]

/-- When `α` is a root of `φ`, `0` is a root of `ramificationPolynomial φ α`. -/
theorem isRoot_zero_ramificationPolynomial {φ : 𝒪[K][X]} {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).IsRoot 0 := by
  rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_ramificationPolynomial_of_isRoot hroot]

/-- Binomial formula `ρ_i = α⁻ⁿ ∑_{h ∈ [i, n]} C(h, i) φ_h α^h` for `ramificationPolynomial`. -/
theorem coeff_ramificationPolynomial (φ : 𝒪[K][X]) (α : L) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i =
      α⁻¹ ^ φ.natDegree *
        ∑ h ∈ Finset.Icc i φ.natDegree,
          (h.choose i : L) * algebraMap K L (φ.coeff h : K) * α ^ h := by
  rw [ramificationPolynomial, coeff_C_mul, show C α * X + C α = C α * (X + 1) by simp [mul_add],
    comp_eq_sum_left, coeff_sum,
    sum_over_range' _ (by simp) (φ.natDegree + 1) (Nat.lt_succ_of_le natDegree_map_le)]
  congr 1
  trans ∑ h ∈ Finset.range (φ.natDegree + 1),
      (h.choose i : L) * algebraMap K L (φ.coeff h : K) * α ^ h
  · refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [mul_pow, ← mul_assoc, ← C_pow, ← C_mul, coeff_C_mul, coeff_X_add_one_pow]
    simp only [coeff_map, RingHom.comp_apply, Algebra.algebraMap_ofSubsemiring_apply]; ring
  · exact (Finset.sum_subset
      (fun h hh ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hh).2))
      fun h hh hnot ↦ by simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge fun hi ↦
        hnot (Finset.mem_Icc.mpr ⟨hi, Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)⟩))]).symm

/-- Multiplying `(ramificationPolynomial φ α).coeff i` by `α ^ φ.natDegree` when `α ≠ 0`. -/
theorem coeff_ramificationPolynomial_mul_pow (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i * α ^ φ.natDegree =
      ∑ h ∈ Finset.Icc i φ.natDegree,
        (h.choose i : L) * algebraMap K L (φ.coeff h : K) * α ^ h := by
  rw [coeff_ramificationPolynomial, mul_right_comm, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hα),
    one_mul]

/-- Above `φ.natDegree`, all coefficients of `ramificationPolynomial φ α` vanish. -/
theorem coeff_ramificationPolynomial_eq_zero_of_lt {φ : 𝒪[K][X]} {α : L} {i : ℕ}
    (hi : φ.natDegree < i) : (ramificationPolynomial φ α).coeff i = 0 := by
  rw [coeff_ramificationPolynomial, Finset.Icc_eq_empty (not_le.mpr hi), Finset.sum_empty, mul_zero]

/-- The degree of `ramificationPolynomial φ α` is at most `φ.natDegree`. -/
theorem natDegree_ramificationPolynomial_le (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).natDegree ≤ φ.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hi ↦ coeff_ramificationPolynomial_eq_zero_of_lt hi

/-- For `α ≠ 0`, the `φ.natDegree`-th coefficient of `ramificationPolynomial φ α` is `φ_n`. -/
theorem coeff_natDegree_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).coeff φ.natDegree = algebraMap K L (φ.leadingCoeff : K) := by
  rw [coeff_ramificationPolynomial, Finset.Icc_self, Finset.sum_singleton, Nat.choose_self,
    Nat.cast_one, one_mul, coeff_natDegree, ← mul_assoc, mul_right_comm, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hα), one_mul]

/-- If `(φ.leadingCoeff : K) ≠ 0` and `α ≠ 0`, `ramificationPolynomial` has degree `φ.natDegree`. -/
theorem natDegree_ramificationPolynomial {φ : 𝒪[K][X]} (hφ : (φ.leadingCoeff : K) ≠ 0) {α : L}
    (hα : α ≠ 0) : (ramificationPolynomial φ α).natDegree = φ.natDegree :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_ramificationPolynomial_le φ α) <|
    (coeff_natDegree_ramificationPolynomial φ hα).symm ▸ (map_ne_zero (algebraMap K L)).mpr hφ

/-- The linear coefficient of `ramificationPolynomial φ α` is `α⁻¹ ^ φ.natDegree * (φ'(α) * α)`. -/
theorem coeff_one_ramificationPolynomial (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).coeff 1 =
      α⁻¹ ^ φ.natDegree *
        ((φ.derivative.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).eval α * α) := by
  rw [show (ramificationPolynomial φ α).coeff 1 = (ramificationPolynomial φ α).derivative.eval 0 by
    simp [← coeff_zero_eq_eval_zero, coeff_derivative],
    ramificationPolynomial, derivative_C_mul, derivative_comp, derivative_add, derivative_C,
    add_zero, derivative_C_mul, derivative_X, mul_one, derivative_map]
  simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X, mul_zero, zero_add]; ring

section OverField

variable {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- For `α ≠ 0`, the roots in `M` of `ramificationPolynomial φ α` are `(r - α) / α` (`φ(r) = 0`). -/
theorem roots_map_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).roots =
      (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).roots.map
        fun r ↦ (r - algebraMap L M α) / algebraMap L M α := by
  have haM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα
  have hainv : algebraMap L M α⁻¹ ^ φ.natDegree ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero (algebraMap L M)).mpr (inv_ne_zero hα))
  rw [map_ramificationPolynomial (M := M), roots_C_mul _ hainv,
    roots_comp_C_mul_X_add_C _ _ _ (IsUnit.mk0 _ haM)]
  exact Multiset.map_congr rfl fun r _ ↦ by rw [Ring.inverse_eq_inv', div_eq_inv_mul, mul_comm]

/-- If `φ` splits over `M`, then `ramificationPolynomial φ α` splits over `M`. -/
theorem splits_map_ramificationPolynomial {φ : 𝒪[K][X]} (α : L)
    (hsplit : (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).Splits) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).Splits := by
  rw [map_ramificationPolynomial (M := M)]
  exact Splits.mul (Splits.C _) (hsplit.comp_of_natDegree_le_one (by compute_degree!))

end OverField

end Algebraic

end TauCeti

namespace Polynomial

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]

/-- If `φ` is monic and `α ≠ 0`, then `ramificationPolynomial φ α` has degree `φ.natDegree`. -/
theorem Monic.natDegree_ramificationPolynomial {φ : 𝒪[K][X]} (hφ : φ.Monic) {α : L} (hα : α ≠ 0) :
    (TauCeti.ramificationPolynomial φ α).natDegree = φ.natDegree :=
  TauCeti.natDegree_ramificationPolynomial (by simp [hφ.leadingCoeff]) hα

/-- If `φ` is monic and `α ≠ 0`, then `ramificationPolynomial φ α` is monic. -/
theorem Monic.ramificationPolynomial {φ : 𝒪[K][X]} (hφ : φ.Monic) {α : L} (hα : α ≠ 0) :
    (TauCeti.ramificationPolynomial φ α).Monic := by
  rw [Monic, Polynomial.leadingCoeff, hφ.natDegree_ramificationPolynomial hα,
    TauCeti.coeff_natDegree_ramificationPolynomial φ hα, hφ.leadingCoeff, Subring.coe_one,
    map_one (algebraMap K L)]

/-- If `φ`'s image in `L[X]` is separable and `α ≠ 0`, `ramificationPolynomial φ α` is separable. -/
theorem Separable.ramificationPolynomial {φ : 𝒪[K][X]}
    (hsep : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).Separable) {α : L} (hα : α ≠ 0) :
    (TauCeti.ramificationPolynomial φ α).Separable := by
  obtain ⟨u, v, huv⟩ := hsep
  set P := φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))
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

section ValuativeExtension

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- A root in `L` of a monic polynomial over `𝒪[K]` lies in `𝒪[L]`. -/
theorem mem_integer_of_isRoot_monic {φ : 𝒪[K][X]} (hmonic : φ.Monic) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) : α ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff]
  refine (valuation L).le_one_of_root_monic (hmonic.map _) (fun i _ ↦ ?_) hroot
  rw [coeff_map, RingHom.comp_apply, Algebra.algebraMap_ofSubsemiring_apply,
    ValuativeExtension.valuation_algebraMap_le_one_iff]
  exact (Valuation.mem_integer_iff _ _).mp (φ.coeff i).2

private theorem coe_aeval_integerRing (P : 𝒪[K][X]) (ξ : 𝒪[L]) :
    ((aeval ξ P : 𝒪[L]) : L) =
      (P.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).eval (ξ : L) := by
  have hcomp : (algebraMap 𝒪[L] L).comp (algebraMap 𝒪[K] 𝒪[L]) =
      (algebraMap K L).comp (algebraMap 𝒪[K] K) := by ext; rfl
  change algebraMap 𝒪[L] L (P.eval₂ (algebraMap 𝒪[K] 𝒪[L]) ξ) = _
  rw [hom_eval₂, hcomp, ← eval_map]; rfl

/-- Lifting a root `α ∈ 𝒪[L]` of `φ : 𝒪[K][X]` makes it a root of `φ.map (algebraMap 𝒪[K] 𝒪[L])`. -/
theorem isRoot_map_integerRing_of_isRoot {φ : 𝒪[K][X]} {α : L} (hα : α ∈ 𝒪[L])
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ⟨α, hα⟩ :=
  Subtype.ext <| by rw [eval_map, ← aeval_def, coe_aeval_integerRing]; exact hroot

end ValuativeExtension

section LeadingValuation

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]

/-- At `i = φ.natDegree`, `(ramificationPolynomial φ α).coeff φ.natDegree` has valuation `0`. -/
theorem realAddValuation_coeff_natDegree_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) {α : L} (hα : α ≠ 0) :
    realAddValuation L ((ramificationPolynomial φ α).coeff φ.natDegree) = 0 := by
  rw [coeff_natDegree_ramificationPolynomial φ hα, hmonic.leadingCoeff, Subring.coe_one,
    map_one, (realAddValuation L).map_one]

end LeadingValuation

section LocalField

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- If `α : L` is a root of a monic Eisenstein `φ : 𝒪[K][X]` with `K⟮α⟯ = ⊤`, then `α` is a
uniformizer of `𝒪[L]`, `α ≠ 0`, `realAddValuation L α = 1`, and `e(L/K) = φ.natDegree`. -/
theorem irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    ∃ hα : α ∈ 𝒪[L], Irreducible (⟨α, hα⟩ : 𝒪[L]) ∧ α ≠ 0 ∧ realAddValuation L α = 1 ∧
      ramificationIndex K L = φ.natDegree := by
  have hα := mem_integer_of_isRoot_monic hmonic hroot
  have hroot' := isRoot_map_integerRing_of_isRoot hα hroot
  have hξ := irreducible_of_eisenstein_adjoin_eq_top φ hφ ⟨α, hα⟩ hroot' hgen
  exact ⟨hα, hξ, fun h ↦ hξ.ne_zero (Subtype.ext h), realAddValuation_irreducible hξ,
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ⟨α, hα⟩ hroot' hgen⟩

/-- Exact valuation formula for `1 ≤ i`:
`v_L(ρ_i) + n = min_{i ≤ h ≤ n} (n · v_K(C(h, i) φ_h) + h)`, where `n = φ.natDegree`. -/
theorem realAddValuation_coeff_ramificationPolynomial_add_natDegree {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    {i : ℕ} (hi : 1 ≤ i) :
    realAddValuation L ((ramificationPolynomial φ α).coeff i) + (φ.natDegree : WithTop ℝ) =
      (Finset.Icc i φ.natDegree).inf fun h ↦
        (realAddValuation K (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K)).map
          ((φ.natDegree : ℝ) * ·) + (h : WithTop ℝ) := by
  obtain ⟨-, -, hα0, hvα, he⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set n := φ.natDegree; let c (h : ℕ) : 𝒪[K] := (h.choose i : 𝒪[K]) * φ.coeff h
  let t (h : ℕ) : L := algebraMap K L (c h : K) * α ^ h
  have hterm (h : ℕ) : realAddValuation L (t h) =
      (realAddValuation K (c h : K)).map ((n : ℝ) * ·) + (h : WithTop ℝ) := by
    rw [(realAddValuation L).map_mul, realAddValuation_algebraMap, he,
      (realAddValuation L).map_pow, hvα, nsmul_one]
  have hsum : (ramificationPolynomial φ α).coeff i * α ^ n = ∑ h ∈ Finset.Icc i n, t h := by
    rw [coeff_ramificationPolynomial_mul_pow φ hα0 i]
    exact Finset.sum_congr rfl fun h _ ↦ by simp [t, c]
  rw [show realAddValuation L ((ramificationPolynomial φ α).coeff i) + (n : WithTop ℝ) =
      realAddValuation L ((ramificationPolynomial φ α).coeff i * α ^ n) by
    rw [(realAddValuation L).map_mul, (realAddValuation L).map_pow, hvα, nsmul_one],
    hsum, (realAddValuation L).map_sum_eq_inf_of_ne]
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
        simp only [ENat.recTopCoe_natCast, WithTop.map_coe, ← WithTop.coe_natCast,
          ← WithTop.coe_add, WithTop.coe_eq_coe] at heq
        have hnat : n * m₁ + h₁ = n * m₂ + h₂ := by exact_mod_cast heq
        obtain ⟨_, h₁n⟩ := Finset.mem_Icc.mp hh₁; obtain ⟨_, h₂n⟩ := Finset.mem_Icc.mp hh₂
        rcases lt_trichotomy m₁ m₂ with hm | rfl | hm
        · have := Nat.mul_succ n m₁ ▸ Nat.mul_le_mul_left n hm; omega
        · omega
        · have := Nat.mul_succ n m₂ ▸ Nat.mul_le_mul_left n hm; omega

/-- Every coefficient of `ramificationPolynomial φ α` for a monic Eisenstein root has `0 ≤ v_L`. -/
theorem realAddValuation_coeff_ramificationPolynomial_nonneg {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (i : ℕ) : 0 ≤ realAddValuation L ((ramificationPolynomial φ α).coeff i) := by
  rcases eq_or_ne i 0 with rfl | hi0
  · simp [coeff_zero_ramificationPolynomial_of_isRoot hroot]
  rcases lt_or_ge φ.natDegree i with hgt | _
  · simp [coeff_ramificationPolynomial_eq_zero_of_lt hgt]
  have hmono : Monotone (WithTop.map ((φ.natDegree : ℝ) * ·)) :=
    WithTop.monotone_map_iff.mpr fun _ _ hab ↦ mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)
  have hge : (φ.natDegree : WithTop ℝ) ≤
      realAddValuation L ((ramificationPolynomial φ α).coeff i) + (φ.natDegree : WithTop ℝ) := by
    rw [realAddValuation_coeff_ramificationPolynomial_add_natDegree hmonic hφ hroot hgen
      (Nat.one_le_iff_ne_zero.mpr hi0), Finset.le_inf_iff]
    intro h hh
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hh).2 with h_eq | hlt
    · simpa [h_eq] using add_le_add (hmono (mem_integer_iff_realAddValuation_nonneg.mp
        ((h.choose i : 𝒪[K]) * φ.coeff h).2)) (le_rfl : (h : WithTop ℝ) ≤ h)
    · refine (show (φ.natDegree : WithTop ℝ) ≤
          (1 : WithTop ℝ).map ((φ.natDegree : ℝ) * ·) + (h : WithTop ℝ) by
        simp [← WithTop.coe_natCast, ← WithTop.coe_add]).trans
        (add_le_add (hmono (mem_maximalIdeal_iff_one_le_realAddValuation.mp
          (Ideal.mul_mem_left _ _ (hφ.mem hlt)))) le_rfl)
  cases hv : realAddValuation L ((ramificationPolynomial φ α).coeff i) with
  | top => simp
  | coe r =>
    rw [hv, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_le_coe] at hge
    rw [← WithTop.coe_zero, WithTop.coe_le_coe]; linarith

/-- Every coefficient of `ramificationPolynomial φ α` for a monic Eisenstein root lies in `𝒪[L]`. -/
theorem coeff_ramificationPolynomial_mem_integer {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤)
    (i : ℕ) : (ramificationPolynomial φ α).coeff i ∈ 𝒪[L] :=
  mem_integer_iff_realAddValuation_nonneg.mpr
    (realAddValuation_coeff_ramificationPolynomial_nonneg hmonic hφ hroot hgen i)

section Separable

variable [Algebra.IsSeparable K L]

/-- In separable `L = K(α)`, `(ramificationPolynomial φ α).coeff 1` has height `d(L/K) + 1 - n`. -/
theorem realAddValuation_coeff_one_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    realAddValuation L ((ramificationPolynomial φ α).coeff 1) =
      (((differentExponent K L : ℝ) + 1 - φ.natDegree : ℝ) : WithTop ℝ) := by
  obtain ⟨hα, -, hα0, hvα, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hdiff :=
    Polynomial.natCast_differentExponent_eq_addVal_aeval_derivative_of_eisenstein_adjoin_eq_top
      φ hφ ξ (isRoot_map_integerRing_of_isRoot hα hroot) hgen
  have hval := congrArg (realAddValuation L) (show
      (ramificationPolynomial φ α).coeff 1 * α ^ φ.natDegree =
        ((aeval ξ φ.derivative : 𝒪[L]) : L) * α by
    rw [coeff_one_ramificationPolynomial, coe_aeval_integerRing, mul_right_comm, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hα0), one_mul])
  rw [(realAddValuation L).map_mul, (realAddValuation L).map_pow, hvα, nsmul_one,
    (realAddValuation L).map_mul, realAddValuation_coe_integer, ← hdiff, ENat.recTopCoe_natCast,
    hvα] at hval
  cases hc1 : realAddValuation L ((ramificationPolynomial φ α).coeff 1) with
  | top =>
    rw [hc1, top_add, ← WithTop.coe_one, ← WithTop.coe_add] at hval
    exact absurd hval WithTop.top_ne_coe
  | coe r =>
    rw [hc1, ← WithTop.coe_natCast, ← WithTop.coe_one, ← WithTop.coe_add, ← WithTop.coe_add,
      WithTop.coe_eq_coe] at hval
    rw [WithTop.coe_eq_coe]; linarith

/-- In a separable Eisenstein extension `L = K(α)`, `(ramificationPolynomial φ α).coeff 1 ≠ 0`. -/
theorem coeff_one_ramificationPolynomial_ne_zero {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).coeff 1 ≠ 0 := fun h0 ↦ by
  have h := realAddValuation_coeff_one_ramificationPolynomial hmonic hφ hroot hgen
  rw [h0, (realAddValuation L).map_zero] at h
  exact WithTop.top_ne_coe h

/-- In separable `L = K(α)`, `ramificationPolynomial φ α` has trailing degree `1`. -/
theorem natTrailingDegree_ramificationPolynomial {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).natTrailingDegree = 1 := by
  have hc1 := coeff_one_ramificationPolynomial_ne_zero hmonic hφ hroot hgen
  refine le_antisymm (natTrailingDegree_le_of_ne_zero hc1)
    (le_natTrailingDegree (fun h0 ↦ hc1 (by simp [h0])) fun m hm ↦ ?_)
  obtain rfl : m = 0 := by omega
  exact coeff_zero_ramificationPolynomial_of_isRoot hroot

/-- In a separable Eisenstein extension `L = K(α)`, `ramificationPolynomial φ α` is separable. -/
theorem separable_ramificationPolynomial_of_eisenstein_adjoin_eq_top {φ : 𝒪[K][X]}
    (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).Separable := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  obtain ⟨hα, -, hα0, -, -⟩ :=
    irreducible_and_realAddValuation_of_eisenstein_adjoin_eq_top hmonic hφ hroot hgen
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have heq : minpoly 𝒪[K] ξ = φ := eq_of_monic_of_associated (minpoly.monic hint) hmonic
    (hφ.associated_minpoly hφ.isUnit_leadingCoeff (isRoot_map_integerRing_of_isRoot hα hroot))
  have hminK : minpoly K α = φ.map (algebraMap 𝒪[K] K) := by
    simpa [ξ, heq, Algebra.algebraMap_ofSubsemiring_apply] using
      minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hsepL : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).Separable := by
    rw [← Polynomial.map_map, ← hminK]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K α)
  exact hsepL.ramificationPolynomial hα0

end Separable

end LocalField

end TauCeti
