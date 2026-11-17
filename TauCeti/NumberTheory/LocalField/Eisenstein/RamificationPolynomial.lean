/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.PowerBasis
public import TauCeti.NumberTheory.LocalField.AddValuation
public import TauCeti.NumberTheory.LocalField.Different.Eisenstein
public import TauCeti.NumberTheory.LocalField.Discriminant.Height
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Data.ENat.Map
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.RingTheory.Polynomial.Eisenstein.ValuativeRel
import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.RingTheory.PowerBasis

/-!
# The ramification polynomial of an Eisenstein extension

Let `K` be a valued field, `φ ∈ 𝒪[K][X]` a polynomial of degree `n`, and `α : L` an element of a
`K`-algebra field `L`. Following Ore, Pauli–Sinclair, and the LMFDB (`lf.ramification_polygon`),
the **ramification polynomial** of `(φ, α)` is

`ramificationPolynomial φ α := C (α⁻¹ ^ n) * (φ.map (algebraMap 𝒪[K] L)).comp (C α * X + C α)`

in `L[X]`, that is, `ρ(X) = α⁻ⁿ φ(α X + α)`. (Some authors, such as Greve–Pauli, divide `ρ` by
`X` to remove the trivial root at `0`.)

When `φ` is monic and `α ≠ 0`, `ρ` is monic of degree `n`, and when `α` is a root of `φ` it
satisfies `ρ(0) = 0`. Expanding `φ(α X + α)` via Taylor shifts and Hasse derivatives gives the
binomial coefficient formula `ρ_i = α⁻ⁿ ∑_{i ≤ h ≤ n} C(h, i) φ_h α^h`.

When `K` and `L` are nonarchimedean local fields, `φ` is Eisenstein, and `L = K(α)`, `α` is a
uniformizer of `L` with `e(L/K) = n`. For `1 ≤ i ≤ n`, the powers `α^i, …, α^{n - 1}` have
distinct nonzero valuation residues modulo `n` while the `h = n` summand has valuation divisible
by `n`, so no cancellation can occur between the `h < n` block and the `h = n` term (at `i = 0`,
by contrast, the `h = 0` term also has residue `0` modulo `n`, and the sum cancels identically
since `φ(α) = 0`). Every coefficient `ρ_i` lies in `𝒪[L]`, and for `1 ≤ i ≤ n` its normalized
valuation is

`v_L(ρ_i) = min_{i ≤ h ≤ n} (n · v_K(C(h, i) φ_h) + h) - n`.

At the right endpoint `i = n` this gives `v_L(ρ_n) = 0`. When `L/K` is separable, the Eisenstein
different formula identifies the linear-term valuation `v_L(ρ_1)` with `d(L/K) - n + 1 = height K L`
(and algebraically `ρ_1 ≠ 0` and `ρ.natTrailingDegree = 1`), and in any extension field `M` of `L`
the roots of `ρ` are the simple elements `(σ α - α) / α` as `σ` ranges over `L →ₐ[K] M`.

## Main definitions

* `Polynomial.ramificationPolynomial φ α`: the ramification polynomial
  `α⁻ⁿ φ(α X + α) ∈ L[X]`.

## Main results

* `Polynomial.coeff_ramificationPolynomial` and
  `Polynomial.coeff_ramificationPolynomial_eq_eval_hasseDeriv`: the binomial and Hasse-derivative
  formulas for the coefficients of `ramificationPolynomial φ α`.
* `Polynomial.natDegree_ramificationPolynomial`, `Polynomial.monic_ramificationPolynomial`,
  `Polynomial.eval_zero_ramificationPolynomial_of_isRoot`,
  `Polynomial.roots_ramificationPolynomial`, `Polynomial.splits_ramificationPolynomial_iff`, and
  `Polynomial.map_ramificationPolynomial`: degree `n`, monicity, vanishing at `0`, roots,
  splitting, and compatibility with field extensions.
* `Polynomial.separable_ramificationPolynomial_iff`,
  `Polynomial.separable_ramificationPolynomial`,
  `Polynomial.coeff_ramificationPolynomial_one_ne_zero`, and
  `Polynomial.natTrailingDegree_ramificationPolynomial`: separability, nonvanishing linear term,
  and `natTrailingDegree ρ = 1` when `L/K` is separable.
* `Polynomial.coeff_ramificationPolynomial_mem_integer`: integrality `ρ_i ∈ 𝒪[L]` for all `i`.
* `Polynomial.addVal_coeff_ramificationPolynomial` and
  `Polynomial.normalizedAddValuation_coeff_ramificationPolynomial`: exact valuation of `ρ_i` for
  `1 ≤ i ≤ n`.
* `Polynomial.addVal_coeff_ramificationPolynomial_one`,
  `Polynomial.addValInt_coeff_ramificationPolynomial_one`, and
  `Polynomial.normalizedAddValuation_coeff_ramificationPolynomial_one`: `v_L(ρ_1) = height K L`
  when `L/K` is separable.
* `Polynomial.addValInt_coeff_ramificationPolynomial_natDegree` and
  `Polynomial.normalizedAddValuation_coeff_ramificationPolynomial_natDegree`: `v_L(ρ_n) = 0`.
* `Polynomial.roots_map_ramificationPolynomial_eq_map_algHom` and
  `Polynomial.roots_map_ramificationPolynomial_filter_ne_zero_eq_map_algHom`: the
  conjugate-difference description of the roots `(σ α - α) / α`.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8.
* Ø. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928),
  84–117.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, and Chapter IV, §§1–2.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory **8** (2012), 1401–1424.
* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory **13** (2017), 2007–2038.
* The LMFDB Collaboration, *The L-functions and modular forms database*, knowl
  `lf.ramification_polygon` (<https://www.lmfdb.org/knowledge/show/lf.ramification_polygon>).
-/

public section
noncomputable section

open TauCeti ValuativeRel IsLocalRing IsNonarchimedeanLocalField
open scoped IntermediateField

namespace Polynomial

section Algebraic

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]

/-- The **ramification polynomial** `ρ(X) = α⁻ⁿ φ(α X + α)` in `L[X]` attached to a polynomial
`φ : 𝒪[K][X]` of degree `n = φ.natDegree` and an element `α : L`. -/
def ramificationPolynomial (φ : 𝒪[K][X]) (α : L) : L[X] :=
  C (α⁻¹ ^ φ.natDegree) *
    (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α)

/-- The defining formula of `ramificationPolynomial`. -/
theorem ramificationPolynomial_def (φ : 𝒪[K][X]) (α : L) :
    ramificationPolynomial φ α =
      C (α⁻¹ ^ φ.natDegree) *
        (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α) := (rfl)

/-- The ramification polynomial of `0` is `0`. -/
@[simp]
theorem ramificationPolynomial_zero (α : L) :
    ramificationPolynomial (0 : 𝒪[K][X]) α = 0 := by
  simp [ramificationPolynomial_def]

/-- `ramificationPolynomial φ α` written via `Polynomial.taylor`. -/
theorem ramificationPolynomial_eq_C_mul_taylor_comp (φ : 𝒪[K][X]) (α : L) :
    ramificationPolynomial φ α =
      C (α⁻¹ ^ φ.natDegree) *
        (taylor α (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K)))).comp (C α * X) := by
  rw [ramificationPolynomial_def, comp_C_mul_X_add_C_eq_taylor_comp]

/-- Hasse-derivative formula for the `i`-th coefficient of `ramificationPolynomial φ α`. -/
theorem coeff_ramificationPolynomial_eq_eval_hasseDeriv (φ : 𝒪[K][X]) (α : L) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i =
      α⁻¹ ^ φ.natDegree *
        ((hasseDeriv i (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K)))).eval α * α ^ i) := by
  rw [ramificationPolynomial_def, coeff_C_mul, coeff_comp_C_mul_X_add_C_eq_eval_hasseDeriv]

/-- **Binomial coefficient formula for `ramificationPolynomial`**:
`ρ_i = α⁻ⁿ ∑_{i ≤ h ≤ n} C(h, i) φ_h α^h` for every `i : ℕ` (vanishing when `i > n`). -/
theorem coeff_ramificationPolynomial (φ : 𝒪[K][X]) (α : L) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i =
      α⁻¹ ^ φ.natDegree *
        ∑ h ∈ Finset.Icc i φ.natDegree,
          (h.choose i : L) * algebraMap K L (φ.coeff h : K) * α ^ h := by
  rw [ramificationPolynomial_def, coeff_C_mul,
    coeff_comp_C_mul_X_add_C_eq_sum_Icc _ α α natDegree_map_le]
  congr 1
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  rw [coeff_map, RingHom.comp_apply, Algebra.algebraMap_ofSubsemiring_apply, mul_assoc (_ * _),
    ← pow_add, Nat.sub_add_cancel (Finset.mem_Icc.mp hh).1]

/-- Coefficients of `ramificationPolynomial φ α` vanish above `φ.natDegree`. -/
theorem coeff_ramificationPolynomial_of_natDegree_lt (φ : 𝒪[K][X]) (α : L) {i : ℕ}
    (hi : φ.natDegree < i) :
    (ramificationPolynomial φ α).coeff i = 0 := by
  rw [coeff_ramificationPolynomial, Finset.Icc_eq_empty (by omega), Finset.sum_empty, mul_zero]

/-- Evaluating `ramificationPolynomial φ α` at `x : L` computes `α⁻ⁿ φ(α x + α)`. -/
theorem eval_ramificationPolynomial (φ : 𝒪[K][X]) (α x : L) :
    (ramificationPolynomial φ α).eval x =
      α⁻¹ ^ φ.natDegree *
        (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).eval (α * x + α) := by
  simp [ramificationPolynomial_def, eval_comp]

/-- Evaluating `ramificationPolynomial φ α` in any `L`-algebra `A`. -/
theorem aeval_ramificationPolynomial {A : Type*} [CommSemiring A] [Algebra L A]
    (φ : 𝒪[K][X]) (α : L) (x : A) :
    aeval x (ramificationPolynomial φ α) =
      algebraMap L A (α⁻¹ ^ φ.natDegree) *
        aeval (algebraMap L A α * x + algebraMap L A α)
          (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))) := by
  simp [ramificationPolynomial_def, aeval_comp]

/-- The constant coefficient of `ramificationPolynomial φ α` is `α⁻ⁿ φ(α)`. -/
@[simp]
theorem coeff_ramificationPolynomial_zero (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).coeff 0 =
      α⁻¹ ^ φ.natDegree * (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).eval α := by
  rw [coeff_zero_eq_eval_zero, eval_ramificationPolynomial, mul_zero, zero_add]

/-- When `α` is a root of `φ`, the constant coefficient of `ramificationPolynomial φ α` is `0`. -/
theorem coeff_ramificationPolynomial_zero_of_isRoot {φ : 𝒪[K][X]} {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).coeff 0 = 0 := by
  rw [coeff_ramificationPolynomial_zero, hroot.eq_zero, mul_zero]

/-- When `α` is a root of `φ`, `ramificationPolynomial φ α` vanishes at `0`. -/
theorem eval_zero_ramificationPolynomial_of_isRoot {φ : 𝒪[K][X]} {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_ramificationPolynomial_zero_of_isRoot hroot]

/-- The linear coefficient of `ramificationPolynomial φ α` is `α⁻ⁿ (φ'(α) · α)`. -/
@[simp]
theorem coeff_ramificationPolynomial_one (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).coeff 1 =
      α⁻¹ ^ φ.natDegree *
        ((φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).derivative.eval α * α) := by
  rw [coeff_ramificationPolynomial_eq_eval_hasseDeriv, hasseDeriv_one, pow_one]

/-- When `α ≠ 0`, the degree-`φ.natDegree` coefficient of `ramificationPolynomial φ α` equals the
image of `φ.leadingCoeff` in `L`. -/
@[simp]
theorem coeff_ramificationPolynomial_natDegree (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).coeff φ.natDegree = algebraMap K L (φ.leadingCoeff : K) := by
  simp only [coeff_ramificationPolynomial, Finset.Icc_self, Finset.sum_singleton,
    Nat.choose_self, Nat.cast_one, one_mul, coeff_natDegree]
  rw [mul_comm _ (α ^ φ.natDegree), ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hα, one_pow, one_mul]

/-- When `α ≠ 0`, `ramificationPolynomial φ α` is zero if and only if `φ = 0`. -/
@[simp]
theorem ramificationPolynomial_eq_zero_iff {φ : 𝒪[K][X]} {α : L} (hα : α ≠ 0) :
    ramificationPolynomial φ α = 0 ↔ φ = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ramificationPolynomial_zero α⟩
  have hlc : algebraMap K L (φ.leadingCoeff : K) = 0 := by
    rw [← coeff_ramificationPolynomial_natDegree φ hα, h, coeff_zero]
  exact leadingCoeff_eq_zero.mp
    (Subtype.ext ((FaithfulSMul.algebraMap_eq_zero_iff K L).mp hlc))

/-- When `φ ≠ 0` and `α ≠ 0`, `ramificationPolynomial φ α` is nonzero. -/
theorem ramificationPolynomial_ne_zero {φ : 𝒪[K][X]} (hφ : φ ≠ 0) {α : L} (hα : α ≠ 0) :
    ramificationPolynomial φ α ≠ 0 :=
  (ramificationPolynomial_eq_zero_iff hα).not.mpr hφ

/-- When `α ≠ 0`, the degree of `ramificationPolynomial φ α` is `φ.natDegree`. -/
@[simp]
theorem natDegree_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).natDegree = φ.natDegree := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · simp
  refine le_antisymm
    (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦
      coeff_ramificationPolynomial_of_natDegree_lt φ α hi)
    (le_natDegree_of_ne_zero ?_)
  rw [coeff_ramificationPolynomial_natDegree φ hα]
  exact (_root_.map_ne_zero (algebraMap K L)).mpr fun h ↦
    leadingCoeff_ne_zero.mpr hφ (Subtype.ext h)

/-- When `α ≠ 0`, the leading coefficient of `ramificationPolynomial φ α` is the image of
`φ.leadingCoeff` in `L`. -/
@[simp]
theorem leadingCoeff_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).leadingCoeff = algebraMap K L (φ.leadingCoeff : K) := by
  rw [leadingCoeff, natDegree_ramificationPolynomial φ hα,
    coeff_ramificationPolynomial_natDegree φ hα]

/-- When `φ` is monic and `α ≠ 0`, `ramificationPolynomial φ α` is monic. -/
theorem monic_ramificationPolynomial {φ : 𝒪[K][X]} (hmonic : φ.Monic) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).Monic := by
  rw [Monic, leadingCoeff_ramificationPolynomial φ hα, hmonic.leadingCoeff, Subring.coe_one,
    map_one]

/-- When `α ≠ 0`, `x : L` is a root of `ramificationPolynomial φ α` if and only if `α x + α` is a
root of `φ`. -/
theorem isRoot_ramificationPolynomial_iff (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) (x : L) :
    (ramificationPolynomial φ α).IsRoot x ↔
      (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot (α * x + α) := by
  rw [IsRoot.def, IsRoot.def, eval_ramificationPolynomial]
  simp [hα]

/-- When `α ≠ 0`, the root multiplicity of `x : L` in `ramificationPolynomial φ α` equals the root
multiplicity of `α x + α` in `φ`. -/
theorem rootMultiplicity_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) (x : L) :
    (ramificationPolynomial φ α).rootMultiplicity x =
      (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).rootMultiplicity (α * x + α) := by
  have hc : (α⁻¹ ^ φ.natDegree : L) ≠ 0 := pow_ne_zero _ (inv_ne_zero hα)
  rw [ramificationPolynomial_def, rootMultiplicity_C_mul hc,
    rootMultiplicity_comp_C_mul_X_add_C _ _ _ x hα.isUnit]

/-- **Roots of `ramificationPolynomial` from roots of `φ`**: for `α ≠ 0`, the multiset of roots of
`ramificationPolynomial φ α` in `L` is `(r - α) / α` as `r` ranges over the roots of `φ` in `L`. -/
theorem roots_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).roots =
      ((φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).roots).map fun r ↦ (r - α) / α := by
  have hc : (α⁻¹ ^ φ.natDegree : L) ≠ 0 := pow_ne_zero _ (inv_ne_zero hα)
  rw [ramificationPolynomial_def, roots_C_mul _ hc, roots_comp_C_mul_X_add_C _ _ _ hα.isUnit]
  refine Multiset.map_congr rfl fun r _ ↦ ?_
  simp [div_eq_inv_mul, mul_comm]

/-- When `α ≠ 0`, `ramificationPolynomial φ α` splits over `L` if and only if `φ` splits over `L`.
-/
theorem splits_ramificationPolynomial_iff (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).Splits ↔
      (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).Splits := by
  have hc : (C (α⁻¹ ^ φ.natDegree) : L[X]) ≠ 0 :=
    C_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hα))
  rw [ramificationPolynomial_def, splits_mul_iff_right hc (Splits.C _),
    ← splits_iff_comp_splits_of_natDegree_eq_one (by compute_degree!)]

/-- When `α ≠ 0`, `ramificationPolynomial φ α` is separable if and only if `φ` mapped to `L[X]` is
separable. -/
@[simp]
theorem separable_ramificationPolynomial_iff {φ : 𝒪[K][X]} {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).Separable ↔
      (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).Separable := by
  have hu : IsUnit (C (α⁻¹ ^ φ.natDegree) : L[X]) :=
    isUnit_C.mpr (pow_ne_zero _ (inv_ne_zero hα)).isUnit
  have hassoc : Associated
      ((φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α))
      (ramificationPolynomial φ α) := by
    rw [ramificationPolynomial_def]
    exact associated_unit_mul_right _ _ hu
  rw [← hassoc.separable_iff, separable_comp_C_mul_X_add_C_iff hα.isUnit]

/-- For an Eisenstein polynomial `φ` and any root `α : L`, `ramificationPolynomial φ α` has degree
`φ.natDegree`. -/
theorem natDegree_ramificationPolynomial_of_isEisensteinAt
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).natDegree = φ.natDegree :=
  natDegree_ramificationPolynomial φ (hφ.ne_zero_of_isRoot hroot)

/-- For a monic Eisenstein polynomial `φ` and any root `α : L`, `ramificationPolynomial φ α` is
monic. -/
theorem monic_ramificationPolynomial_of_isEisensteinAt
    {φ : 𝒪[K][X]} (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).Monic :=
  monic_ramificationPolynomial hmonic (hφ.ne_zero_of_isRoot hroot)

section SeparableAlgebraic

variable [Algebra.IsSeparable K L]

/-- **Separability of `ramificationPolynomial`**: when `L/K` is separable, `φ` is Eisenstein, and
`α : L` is a root of `φ`, `ramificationPolynomial φ α` is separable. -/
theorem separable_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).Separable := by
  have hα0 : α ≠ 0 := hφ.ne_zero_of_isRoot hroot
  have hlc : (φ.leadingCoeff : K) ≠ 0 := fun h ↦
    hφ.isUnit_leadingCoeff.ne_zero (Subtype.ext h)
  rw [separable_ramificationPolynomial_iff hα0, ← Polynomial.map_map,
    hφ.map_eq_C_leadingCoeff_mul_minpoly hroot]
  exact (Separable.unit_mul (isUnit_C.mpr hlc.isUnit) (Algebra.IsSeparable.isSeparable K α)).map

/-- When `L/K` is separable, every root of `ramificationPolynomial φ α` in `L` is simple
(`Nodup`). -/
theorem nodup_roots_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).roots.Nodup :=
  nodup_roots (separable_ramificationPolynomial hφ hroot)

/-- When `L/K` is separable, the linear coefficient of `ramificationPolynomial φ α` is nonzero. -/
theorem coeff_ramificationPolynomial_one_ne_zero
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).coeff 1 ≠ 0 := by
  have hderiv : (derivative (ramificationPolynomial φ α)).eval 0 ≠ 0 :=
    (separable_ramificationPolynomial hφ hroot).eval₂_derivative_ne_zero (RingHom.id L)
      (eval_zero_ramificationPolynomial_of_isRoot hroot)
  rwa [← coeff_zero_eq_eval_zero, coeff_derivative, zero_add, Nat.cast_zero, zero_add,
    mul_one] at hderiv

/-- When `L/K` is separable, `ramificationPolynomial φ α` has trailing degree `1` (it vanishes to
order `1` at `0`), so its Newton polygon begins at abscissa `1`. -/
theorem natTrailingDegree_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (ramificationPolynomial φ α).natTrailingDegree = 1 := by
  have hc1 := coeff_ramificationPolynomial_one_ne_zero hφ hroot
  have hp0 : ramificationPolynomial φ α ≠ 0 := fun h ↦ hc1 (by simp [h])
  refine le_antisymm (natTrailingDegree_le_of_ne_zero hc1) (le_natTrailingDegree hp0 fun m hm ↦ ?_)
  obtain rfl : m = 0 := by omega
  exact coeff_ramificationPolynomial_zero_of_isRoot hroot

end SeparableAlgebraic

end Algebraic

section EisensteinValuations

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- **Integral shifted polynomial** `φ(ξ X + ξ) ∈ 𝒪[L][X]`, whose `i`-th coefficient is
`ξ ^ φ.natDegree` times the `i`-th coefficient of `ramificationPolynomial φ α`. -/
private def intShiftedPoly (φ : 𝒪[K][X]) {α : L} (hα : α ∈ 𝒪[L]) : 𝒪[L][X] :=
  (φ.map (algebraMap 𝒪[K] 𝒪[L])).comp (C ⟨α, hα⟩ * X + C ⟨α, hα⟩)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] in
private theorem coeff_intShiftedPoly (φ : 𝒪[K][X]) {α : L} (hα : α ∈ 𝒪[L]) (i : ℕ) :
    (intShiftedPoly φ hα).coeff i =
      ∑ h ∈ Finset.Icc i φ.natDegree,
        algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) * (⟨α, hα⟩ : 𝒪[L]) ^ h := by
  rw [intShiftedPoly, coeff_comp_C_mul_X_add_C_eq_sum_Icc _ _ _ natDegree_map_le]
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  rw [coeff_map, map_mul, map_natCast, mul_assoc (_ * _), ← pow_add,
    Nat.sub_add_cancel (Finset.mem_Icc.mp hh).1]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] in
private theorem coe_coeff_intShiftedPoly (φ : 𝒪[K][X]) {α : L} (hα : α ∈ 𝒪[L]) (i : ℕ) :
    ((intShiftedPoly φ hα).coeff i : L) =
      ((φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α)).coeff i := by
  have hmap : (intShiftedPoly φ hα).map (algebraMap 𝒪[L] L) =
      (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α) := by
    rw [intShiftedPoly, Polynomial.map_comp, Polynomial.map_map,
      algebraMap_comp_algebraMap_integerRing]
    simp [Algebra.algebraMap_ofSubsemiring_apply]
  rw [← hmap, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]

private theorem addVal_summand_ge_natDegree {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K])
    {α : L} (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) {i h : ℕ} (hh : h ∈ Finset.Icc i φ.natDegree) :
    (φ.natDegree : ℕ∞) ≤
      IsDiscreteValuationRing.addVal 𝒪[L]
        (algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) *
          (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) ^ h) := by
  set ξ : 𝒪[L] := ⟨α, hφ.mem_integer_of_isRoot hroot⟩
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have he : ramificationIndex K L = φ.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ
      (isRoot_map_integerRing_iff.mpr hroot) hgen
  rw [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap (K := K) (L := L), he, hξ.addVal_pow]
  rw [Finset.mem_Icc] at hh
  rcases eq_or_lt_of_le hh.2 with rfl | hlt
  · exact le_add_of_nonneg_left zero_le
  · have hv1 : (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal 𝒪[K] (φ.coeff h) := by
      simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
        (n := 1)).mp (by simpa using hφ.mem hlt)
    have hv2 : (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) :=
      hv1.trans
        (by rw [IsDiscreteValuationRing.addVal_mul]; exact le_add_of_nonneg_left zero_le)
    calc (φ.natDegree : ℕ∞) = φ.natDegree • (1 : ℕ∞) := by simp
      _ ≤ φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) :=
        nsmul_le_nsmul_right hv2 φ.natDegree
      _ ≤ _ := le_self_add

private theorem addVal_coeff_intShiftedPoly_ge {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K])
    {α : L} (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) (i : ℕ) :
    (φ.natDegree : ℕ∞) ≤
      IsDiscreteValuationRing.addVal 𝒪[L]
        ((intShiftedPoly φ (hφ.mem_integer_of_isRoot hroot)).coeff i) := by
  rw [coeff_intShiftedPoly]
  exact (IsDiscreteValuationRing.addVal 𝒪[L]).map_le_sum fun _ hh ↦
    addVal_summand_ge_natDegree hφ hroot hgen hh

/-- **Integrality of the coefficients of `ramificationPolynomial`**: for an Eisenstein polynomial
`φ : 𝒪[K][X]` and a root `α` generating `L/K`, every coefficient of `ramificationPolynomial φ α`
lies in `𝒪[L]`. -/
theorem coeff_ramificationPolynomial_mem_integer
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i ∈ 𝒪[L] := by
  have hα : α ∈ 𝒪[L] := hφ.mem_integer_of_isRoot hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hα0 : α ≠ 0 := hφ.ne_zero_of_isRoot hroot
  -- Every summand of `intShiftedPoly` has valuation at least `deg φ`, so `ξ ^ deg φ` divides it.
  have hdvd : ξ ^ φ.natDegree ∣ (intShiftedPoly φ hα).coeff i := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hξ.addVal_pow]
    exact addVal_coeff_intShiftedPoly_ge hφ hroot hgen i
  obtain ⟨q, hq⟩ := hdvd
  have hcoeff : (ramificationPolynomial φ α).coeff i = (q : L) := by
    rw [ramificationPolynomial_def, coeff_C_mul, ← coe_coeff_intShiftedPoly φ hα i, hq,
      Subring.coe_mul, Subring.coe_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hα0, one_pow,
      one_mul]
  rw [hcoeff]
  exact q.2

private theorem coeff_intShiftedPoly_eq_pow_mul
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) (i : ℕ) :
    (intShiftedPoly φ (hφ.mem_integer_of_isRoot hroot)).coeff i =
      (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) ^ φ.natDegree *
        ⟨(ramificationPolynomial φ α).coeff i,
          coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩ := by
  have hα0 : α ≠ 0 := hφ.ne_zero_of_isRoot hroot
  apply Subtype.ext
  rw [Subring.coe_mul, Subring.coe_pow, coe_coeff_intShiftedPoly]
  dsimp only
  rw [ramificationPolynomial_def, coeff_C_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hα0,
    one_pow, one_mul]

/-- Valuation of the `h < φ.natDegree` sub-sum of `intShiftedPoly.coeff i`, computed via the
Eisenstein power-basis orthogonality `addVal_sum_eisenstein_powerBasis`. -/
private theorem addVal_sum_Ico_intShiftedPoly
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) (i : ℕ) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ h ∈ Finset.Ico i φ.natDegree,
          algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) *
            (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) ^ h) =
      ⨅ h ∈ Finset.Ico i φ.natDegree,
        (φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
          ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞)) := by
  have hα : α ∈ 𝒪[L] := hφ.mem_integer_of_isRoot hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  set n := φ.natDegree
  have hroot_int : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ :=
    isRoot_map_integerRing_iff.mpr hroot
  have he : ramificationIndex K L = n :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ hroot_int hgen
  have hn0 : (n : ℕ∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (he ▸ ramificationIndex_pos (K := K) (L := L)).ne'
  -- Extend the sum from `Ico i n` to `Fin n` using `C(h, i) = 0` for `h < i`.
  let c : Fin n → 𝒪[K] := fun j ↦ ((j : ℕ).choose i : 𝒪[K]) * φ.coeff j
  have hB_eq :
      (∑ h ∈ Finset.Ico i n,
        algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) * ξ ^ h) =
      ∑ j : Fin n, algebraMap 𝒪[K] 𝒪[L] (c j) * ξ ^ (j : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun h ↦ algebraMap 𝒪[K] 𝒪[L]
      ((h.choose i : 𝒪[K]) * φ.coeff h) * ξ ^ h)]
    refine Finset.sum_subset (fun h hh ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hh).2) ?_
    intro h hh hnot
    rw [Finset.mem_range] at hh
    rw [Finset.mem_Ico, not_and] at hnot
    simp [Nat.choose_eq_zero_of_lt (by omega : h < i)]
  rw [hB_eq, addVal_sum_eisenstein_powerBasis φ hφ ξ hroot_int hgen c, he]
  refine le_antisymm (le_iInf₂ fun h hh ↦ ?_) (le_iInf fun j ↦ ?_)
  · exact iInf_le (fun j : Fin n ↦ n • IsDiscreteValuationRing.addVal 𝒪[K] (c j) + (j : ℕ))
      ⟨h, (Finset.mem_Ico.mp hh).2⟩
  · by_cases hji : i ≤ (j : ℕ)
    · exact iInf₂_le (j : ℕ) (Finset.mem_Ico.mpr ⟨hji, j.2⟩)
    · have hcz : c j = 0 := by simp [c, Nat.choose_eq_zero_of_lt (lt_of_not_ge hji)]
      simp [hcz, ENat.mul_top hn0]

/-- When `1 ≤ i ≤ φ.natDegree`, a nonzero `h = n` term and a nonzero `h < n` sub-sum have distinct
valuations in `𝒪[L]` because their residues modulo `n = φ.natDegree` are `0` and `j ∈ [i, n)`. -/
private theorem addVal_top_ne_addVal_sum_Ico
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) {i : ℕ} (hi1 : 1 ≤ i)
    (hA_fin : IsDiscreteValuationRing.addVal 𝒪[L]
      (algebraMap 𝒪[K] 𝒪[L] ((φ.natDegree.choose i : 𝒪[K]) * φ.coeff φ.natDegree) *
        (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) ^ φ.natDegree) ≠ ⊤)
    (hB_fin : IsDiscreteValuationRing.addVal 𝒪[L]
      (∑ h ∈ Finset.Ico i φ.natDegree,
        algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) *
          (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) ^ h) ≠ ⊤) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        (algebraMap 𝒪[K] 𝒪[L] ((φ.natDegree.choose i : 𝒪[K]) * φ.coeff φ.natDegree) *
          (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) ^ φ.natDegree) ≠
      IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ h ∈ Finset.Ico i φ.natDegree,
          algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) *
            (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) ^ h) := by
  have hα : α ∈ 𝒪[L] := hφ.mem_integer_of_isRoot hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  set n := φ.natDegree
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have he : ramificationIndex K L = n :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ
      (isRoot_map_integerRing_iff.mpr hroot) hgen
  have hn0 : (n : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (he ▸ ramificationIndex_pos (K := K) (L := L)).ne'
  -- The `h = n` summand has valuation congruent to `0` modulo `n`, whereas the minimum over
  -- `h ∈ Ico i n` is attained at some `j ∈ [i, n)` and has residue `j ≠ 0` modulo `n`.
  rw [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap (K := K) (L := L), he,
    hξ.addVal_pow] at hA_fin ⊢
  have hvA : IsDiscreteValuationRing.addVal 𝒪[K] ((n.choose i : 𝒪[K]) * φ.coeff n) ≠ ⊤ :=
    fun h ↦ hA_fin (by rw [h, nsmul_eq_mul, ENat.mul_top hn0, top_add])
  obtain ⟨kA, hkA⟩ := ENat.ne_top_iff_exists.mp hvA
  have hne : (Finset.Ico i n).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun hempty ↦ hB_fin (by simp [hempty])
  rw [addVal_sum_Ico_intShiftedPoly hφ hroot hgen i, ← Finset.inf_eq_iInf] at hB_fin ⊢
  obtain ⟨j, hj_mem, hj_eq⟩ := Finset.exists_mem_eq_inf (Finset.Ico i n) hne fun h ↦
    n • IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞)
  rw [hj_eq] at hB_fin ⊢
  have hvB : IsDiscreteValuationRing.addVal 𝒪[K] ((j.choose i : 𝒪[K]) * φ.coeff j) ≠ ⊤ :=
    fun h ↦ hB_fin (by rw [h, nsmul_eq_mul, ENat.mul_top hn0, top_add])
  obtain ⟨kB, hkB⟩ := ENat.ne_top_iff_exists.mp hvB
  rw [Finset.mem_Ico] at hj_mem
  rw [← hkA, ← hkB]
  simp only [nsmul_eq_mul, ← ENat.natCast_mul, ← ENat.natCast_add, ne_eq, ENat.natCast_inj]
  intro heq
  have hmod := congrArg (· % n) heq
  have h1 : (n * kA + n) % n = 0 := by rw [← Nat.mul_succ, Nat.mul_mod_right]
  have h2 : (n * kB + j) % n = j := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj_mem.2]
  omega

/-- **Exact valuation of `intShiftedPoly.coeff i`** for `1 ≤ i ≤ φ.natDegree`: the `h < n` block
and the `h = n` term have distinct valuations modulo `n = φ.natDegree`, so the valuation of the sum
is the infimum of the valuations of the summands. -/
private theorem addVal_coeff_intShiftedPoly
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        ((intShiftedPoly φ (hφ.mem_integer_of_isRoot hroot)).coeff i) =
      ⨅ h ∈ Finset.Icc i φ.natDegree,
        (φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
          ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞)) := by
  have hα : α ∈ 𝒪[L] := hφ.mem_integer_of_isRoot hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  let n := φ.natDegree
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have he : ramificationIndex K L = n :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ
      (isRoot_map_integerRing_iff.mpr hroot) hgen
  rw [Finset.mem_Icc] at hi
  let s : ℕ → 𝒪[L] := fun h ↦
    algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) * ξ ^ h
  -- Split `Icc i n` into the `h = n` endpoint and the `Ico i n` block, whose valuations cannot
  -- coincide when finite.
  have hdecomp : (intShiftedPoly φ hα).coeff i = s n + ∑ h ∈ Finset.Ico i n, s h := by
    rw [coeff_intShiftedPoly, ← Finset.insert_right_Ico hi.2,
      Finset.sum_insert Finset.right_notMem_Ico]
  have hmin : IsDiscreteValuationRing.addVal 𝒪[L] (s n + ∑ h ∈ Finset.Ico i n, s h) =
      min (IsDiscreteValuationRing.addVal 𝒪[L] (s n))
        (IsDiscreteValuationRing.addVal 𝒪[L] (∑ h ∈ Finset.Ico i n, s h)) := by
    rcases eq_or_ne (s n) 0 with hA0 | hA0
    · simp [hA0]
    rcases eq_or_ne (∑ h ∈ Finset.Ico i n, s h) 0 with hB0 | hB0
    · simp [hB0]
    exact (IsDiscreteValuationRing.addVal 𝒪[L]).map_add_of_distinct_val
      (addVal_top_ne_addVal_sum_Ico hφ hroot hgen hi.1
        (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hA0)
        (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hB0))
  have hs_n : IsDiscreteValuationRing.addVal 𝒪[L] (s n) =
      φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
        ((φ.natDegree.choose i : 𝒪[K]) * φ.coeff φ.natDegree) + (φ.natDegree : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap (K := K) (L := L), he, hξ.addVal_pow]
  rw [hdecomp, hmin, hs_n, addVal_sum_Ico_intShiftedPoly hφ hroot hgen i,
    ← Finset.inf_eq_iInf, ← Finset.insert_right_Ico hi.2, ← Finset.inf_eq_iInf,
    Finset.inf_insert]

/-- **Exact DVR valuation formula for the coefficients of `ramificationPolynomial`**: for
`1 ≤ i ≤ φ.natDegree`,
`v_L(ρ_i) = (⨅_{i ≤ h ≤ n} (n • v_K(C(h, i) φ_h) + h)) - n` in `ℕ∞`. -/
theorem addVal_coeff_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        ⟨(ramificationPolynomial φ α).coeff i,
          coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩ =
      (⨅ h ∈ Finset.Icc i φ.natDegree,
        (φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
          ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞))) - φ.natDegree := by
  have hξ : Irreducible (⟨α, hφ.mem_integer_of_isRoot hroot⟩ : 𝒪[L]) :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hmul := congrArg (IsDiscreteValuationRing.addVal 𝒪[L])
    (coeff_intShiftedPoly_eq_pow_mul hφ hroot hgen i)
  rw [addVal_coeff_intShiftedPoly hφ hroot hgen hi, IsDiscreteValuationRing.addVal_mul,
    hξ.addVal_pow] at hmul
  rw [hmul]
  generalize IsDiscreteValuationRing.addVal 𝒪[L]
    ⟨(ramificationPolynomial φ α).coeff i,
      coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩ = v
  induction v using ENat.recTopCoe with
  | top => simp
  | coe k =>
    norm_cast
    omega

/-- **Exact `WithTop ℝ` valuation formula for the coefficients of `ramificationPolynomial`** with
respect to `normalizedAddValuation`: for `1 ≤ i ≤ φ.natDegree`,
`v_L(ρ_i) = min_{i ≤ h ≤ n} (n · v_K(C(h, i) φ_h) + h) - n`. -/
theorem normalizedAddValuation_coeff_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    normalizedAddValuation L ((ramificationPolynomial φ α).coeff i) =
      ((Finset.Icc i φ.natDegree).inf'
        ⟨φ.natDegree, Finset.right_mem_Icc.mpr (Finset.mem_Icc.mp hi).2⟩
        fun h ↦ (normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K))).map
          ((φ.natDegree : ℝ) * ·) + ((h : ℝ) : WithTop ℝ)) -
        ((φ.natDegree : ℝ) : WithTop ℝ) := by
  have hval := normalizedAddValuation_coe_integer
    (⟨(ramificationPolynomial φ α).coeff i,
      coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩ : 𝒪[L])
  dsimp only at hval
  have hn0 : (φ.natDegree : ℕ∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := Finset.mem_Icc.mp hi; omega)
  let Hne : (Finset.Icc i φ.natDegree).Nonempty :=
    ⟨φ.natDegree, Finset.right_mem_Icc.mpr (Finset.mem_Icc.mp hi).2⟩
  let term : ℕ → ℕ∞ := fun h ↦
    φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) +
      (h : ℕ∞)
  have hiInf_eq : (⨅ h ∈ Finset.Icc i φ.natDegree, term h) =
      (Finset.Icc i φ.natDegree).inf' Hne term :=
    ((Finset.inf_eq_iInf _ _).symm.trans (Finset.inf'_eq_inf Hne _).symm)
  have hge : (φ.natDegree : ℕ∞) ≤ (Finset.Icc i φ.natDegree).inf' Hne term := by
    rw [← hiInf_eq, ← addVal_coeff_intShiftedPoly hφ hroot hgen hi]
    exact addVal_coeff_intShiftedPoly_ge hφ hroot hgen i
  have hterm (h : ℕ) : ENat.map ((↑) : ℕ → ℝ) (term h) =
      (normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K))).map
        ((φ.natDegree : ℝ) * ·) + ((h : ℝ) : WithTop ℝ) := by
    have hKcoe : ((h.choose i : K) * (φ.coeff h : K)) =
        (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K) := by simp
    rw [hKcoe, normalizedAddValuation_coe_integer]
    dsimp only [term]
    generalize IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) = vK
    induction vK using ENat.recTopCoe with
    | top => simp [ENat.mul_top hn0]
    | coe k =>
      rw [nsmul_eq_mul, ← ENat.natCast_mul, ← ENat.natCast_add, ENat.map_natCast, ENat.map_natCast,
        WithTop.map_coe, ← WithTop.coe_add, Nat.cast_add, Nat.cast_mul]
  rw [hval, addVal_coeff_ramificationPolynomial hφ hroot hgen hi, hiInf_eq,
    ENat.map_sub_natCast_of_le Nat.cast_add hge,
    Finset.apply_inf'_eq_inf'_comp Hne (ENat.map ((↑) : ℕ → ℝ)) fun _ _ ↦
      (ENat.monotone_map_iff.mpr Nat.mono_cast).map_min]
  simp_rw [Function.comp_def, hterm]

/-- At the right endpoint `i = φ.natDegree`, the coefficient of `ramificationPolynomial φ α` has
normalized valuation `0` in `ℤ`. -/
theorem addValInt_coeff_ramificationPolynomial_natDegree
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    addValInt L ((ramificationPolynomial φ α).coeff φ.natDegree) = 0 := by
  have hα0 : α ≠ 0 := hφ.ne_zero_of_isRoot hroot
  rw [coeff_ramificationPolynomial_natDegree φ hα0, addValInt_algebraMap,
    addValInt_eq_zero_of_isUnit_integer hφ.isUnit_leadingCoeff, mul_zero]

/-- At the right endpoint `i = φ.natDegree`, the coefficient of `ramificationPolynomial φ α` has
`normalizedAddValuation` equal to `0`. -/
theorem normalizedAddValuation_coeff_ramificationPolynomial_natDegree
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    normalizedAddValuation L ((ramificationPolynomial φ α).coeff φ.natDegree) = 0 := by
  have hα0 : α ≠ 0 := hφ.ne_zero_of_isRoot hroot
  have hne : (ramificationPolynomial φ α).coeff φ.natDegree ≠ 0 := by
    rw [coeff_ramificationPolynomial_natDegree φ hα0]
    exact (_root_.map_ne_zero (algebraMap K L)).mpr fun h ↦
      hφ.isUnit_leadingCoeff.ne_zero (Subtype.ext h)
  rw [normalizedAddValuation_of_ne_zero hne,
    addValInt_coeff_ramificationPolynomial_natDegree hφ hroot, Int.cast_zero, WithTop.coe_zero]

section Separable

variable [Algebra.IsSeparable K L]

/-- **The linear-term valuation of `ramificationPolynomial` is the height `H(L/K)`** (in `ℕ∞`):
when `L/K` is separable, `v_L(ρ_1) = d(L/K) - n + 1 = height K L`. -/
theorem addVal_coeff_ramificationPolynomial_one
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        ⟨(ramificationPolynomial φ α).coeff 1,
          coeff_ramificationPolynomial_mem_integer hφ hroot hgen 1⟩ =
      (height K L : ℕ∞) := by
  have hα : α ∈ 𝒪[L] := hφ.mem_integer_of_isRoot hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hroot_int : (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ξ :=
    isRoot_map_integerRing_iff.mpr hroot
  have he : ramificationIndex K L = φ.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ hroot_int hgen
  -- On `𝒪[L]`, `(intShiftedPoly φ hα).coeff 1 = aeval ξ φ.derivative * ξ`.
  have hc1 : (intShiftedPoly φ hα).coeff 1 = aeval ξ φ.derivative * ξ := by
    rw [intShiftedPoly, coeff_comp_C_mul_X_add_C_eq_eval_hasseDeriv, hasseDeriv_one, pow_one,
      derivative_map, eval_map, aeval_def]
  have hval_int : IsDiscreteValuationRing.addVal 𝒪[L] ((intShiftedPoly φ hα).coeff 1) =
      ((φ.natDegree + height K L : ℕ) : ℕ∞) := by
    rw [hc1, IsDiscreteValuationRing.addVal_mul,
      ← Polynomial.natCast_differentExponent_eq_addVal_aeval_derivative_of_eisenstein_adjoin_eq_top
        φ hφ ξ hroot_int hgen,
      IsDiscreteValuationRing.addVal_uniformizer hξ, ← ENat.natCast_one, ← ENat.natCast_add,
      ← height_add_ramificationIndex K L, add_comm, he]
  have hmul := congrArg (IsDiscreteValuationRing.addVal 𝒪[L])
    (coeff_intShiftedPoly_eq_pow_mul hφ hroot hgen 1)
  rw [hval_int, IsDiscreteValuationRing.addVal_mul, hξ.addVal_pow] at hmul
  rw [ENat.natCast_add] at hmul
  exact WithTop.add_left_cancel (ENat.natCast_ne_top φ.natDegree) hmul.symm

/-- **The linear-term valuation of `ramificationPolynomial` in `ℤ` is `height K L`.** -/
theorem addValInt_coeff_ramificationPolynomial_one
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    addValInt L ((ramificationPolynomial φ α).coeff 1) = height K L :=
  addValInt_of_addVal_eq_natCast (addVal_coeff_ramificationPolynomial_one hφ hroot hgen)

/-- **The linear-term valuation of `ramificationPolynomial` in `WithTop ℝ` is `height K L`.** -/
theorem normalizedAddValuation_coeff_ramificationPolynomial_one
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    normalizedAddValuation L ((ramificationPolynomial φ α).coeff 1) = (height K L : WithTop ℝ) := by
  rw [normalizedAddValuation_of_ne_zero (coeff_ramificationPolynomial_one_ne_zero hφ hroot),
    addValInt_coeff_ramificationPolynomial_one hφ hroot hgen, Int.cast_natCast,
    WithTop.coe_natCast]

end Separable

end EisensteinValuations

section Roots

variable {K L M : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
  [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- Base-changing `ramificationPolynomial φ α` along a field extension `L → M` in a scalar tower
`K / L / M` produces `ramificationPolynomial φ (algebraMap L M α)`. -/
@[simp]
theorem map_ramificationPolynomial (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).map (algebraMap L M) =
      ramificationPolynomial φ (algebraMap L M α) := by
  have hcomp : (algebraMap L M).comp ((algebraMap K L).comp (algebraMap 𝒪[K] K)) =
      (algebraMap K M).comp (algebraMap 𝒪[K] K) := by
    ext x
    simp [IsScalarTower.algebraMap_apply K L M]
  simp [ramificationPolynomial_def, Polynomial.map_comp, Polynomial.map_map, hcomp]

section EisensteinRoots

variable [Algebra.IsSeparable K L]

omit [Algebra K M] [IsScalarTower K L M] in
/-- Over any extension field `M` of `L`, `(ramificationPolynomial φ α).map (algebraMap L M)` is
separable when `L/K` is separable. -/
theorem separable_map_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).Separable :=
  (separable_ramificationPolynomial hφ hroot).map

omit [Algebra K M] [IsScalarTower K L M] in
/-- Over any extension field `M` of `L`, every root of `ramificationPolynomial φ α` in `M` is
simple (`Nodup`). -/
theorem nodup_roots_map_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).roots.Nodup :=
  nodup_roots (separable_map_ramificationPolynomial hφ hroot)

/-- **Conjugate-difference description of the roots of `ramificationPolynomial`**: in any extension
field `M` of `L`, the roots of `ramificationPolynomial φ α` in `M` are `(σ α - α) / α` as `σ`
ranges over all `K`-embeddings `L →ₐ[K] M` (each occurring once). -/
theorem roots_map_ramificationPolynomial_eq_map_algHom
    [Fintype (L →ₐ[K] M)]
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).roots =
      (Finset.univ : Finset (L →ₐ[K] M)).val.map
        fun σ ↦ (σ α - algebraMap L M α) / algebraMap L M α := by
  have hαM : algebraMap L M α ≠ 0 :=
    (_root_.map_ne_zero (algebraMap L M)).mpr (hφ.ne_zero_of_isRoot hroot)
  have hlcM : algebraMap K M (φ.leadingCoeff : K) ≠ 0 :=
    (_root_.map_ne_zero (algebraMap K M)).mpr fun h ↦ hφ.isUnit_leadingCoeff.ne_zero (Subtype.ext h)
  have hroots_φ : (φ.map ((algebraMap K M).comp (algebraMap 𝒪[K] K))).roots =
      (minpoly K α).aroots M := by
    rw [← Polynomial.map_map, hφ.map_eq_C_leadingCoeff_mul_minpoly hroot,
      Polynomial.map_mul, map_C, roots_C_mul _ hlcM, aroots_def]
  let pb : PowerBasis K L :=
    PowerBasis.ofAdjoinSimpleEqTop (hφ.isIntegral_of_isRoot hroot) hgen
  have hpb_gen : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  have hnodup : ((minpoly K pb.gen).aroots M).Nodup := by
    rw [aroots_def]
    exact nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
  rw [map_ramificationPolynomial, roots_ramificationPolynomial φ hαM, hroots_φ, ← hpb_gen,
    pb.aroots_minpoly_eq_map_algHom hnodup, Multiset.map_map]
  simp only [Function.comp_def]

/-- **Nonzero roots of `ramificationPolynomial`**: filtering out the root `0` (contributed by the
canonical inclusion `IsScalarTower.toAlgHom K L M`) leaves `(σ α - α) / α` over all nontrivial
`K`-embeddings `σ ≠ IsScalarTower.toAlgHom K L M`. -/
theorem roots_map_ramificationPolynomial_filter_ne_zero_eq_map_algHom
    [Fintype (L →ₐ[K] M)] [DecidableEq M] [DecidableEq (L →ₐ[K] M)]
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    (((ramificationPolynomial φ α).map (algebraMap L M)).roots.filter (· ≠ 0)) =
      ((Finset.univ : Finset (L →ₐ[K] M)).erase (IsScalarTower.toAlgHom K L M)).val.map
        fun σ ↦ (σ α - algebraMap L M α) / algebraMap L M α := by
  have hα0 : α ≠ 0 := hφ.ne_zero_of_isRoot hroot
  have hαM : algebraMap L M α ≠ 0 := (_root_.map_ne_zero (algebraMap L M)).mpr hα0
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

end EisensteinRoots

end Roots

end Polynomial

end
