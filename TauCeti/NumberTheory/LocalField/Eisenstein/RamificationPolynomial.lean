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
import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
import TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.RingTheory.PowerBasis
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# The ramification polynomial of an Eisenstein extension

Let `K` be a nonarchimedean local field, `φ ∈ 𝒪[K][X]` an Eisenstein polynomial of degree `n`, and
`α : L` a root of `φ` generating a finite extension `L = K(α)`. Following Ore and Greve–Pauli, the
**ramification polynomial** of `(φ, α)` is

`ramificationPolynomial φ α := C (α⁻¹ ^ n) * (φ.map (algebraMap 𝒪[K] L)).comp (C α * X + C α)`

in `L[X]`, that is, `ρ(X) = α⁻ⁿ φ(α X + α)`.

When `φ` is monic, `ρ` is monic of degree `n` with `ρ(0) = 0`. Expanding `φ(α X + α)` via Taylor
shifts and Hasse derivatives gives the binomial coefficient formula
`ρ_i = α⁻ⁿ ∑_{i ≤ h ≤ n} C(h, i) φ_h α^h`. Because `α` is a uniformizer of `L` with
`e(L/K) = n` and the powers `1, α, …, α^{n - 1}` have distinct valuation residues modulo `n` while
the `h = n` summand has valuation divisible by `n`, no cancellation can occur between the `h < n`
block and the `h = n` term. Every coefficient `ρ_i` lies in `𝒪[L]`, and for `1 ≤ i ≤ n` its
normalized valuation is

`v_L(ρ_i) = min_{i ≤ h ≤ n} (n · v_K(C(h, i) φ_h) + h) - n`.

At the right endpoint `i = n` this gives `v_L(ρ_n) = 0`. When `L/K` is separable, the Eisenstein
different formula identifies the linear-term valuation `v_L(ρ_1)` with `d(L/K) - n + 1 = height K L`
(in particular `ρ_1 ≠ 0` and `ρ.natTrailingDegree = 1`), and in any extension field `M` of `L` the
roots of `ρ` are the simple elements `(σ α - α) / α` as `σ` ranges over `L →ₐ[K] M`.

## Main definitions

* `TauCeti.ramificationPolynomial φ α`: the ramification polynomial `α⁻ⁿ φ(α X + α) ∈ L[X]`.

## Main results

* `TauCeti.coeff_ramificationPolynomial` and
  `TauCeti.coeff_ramificationPolynomial_eq_eval_hasseDeriv`: the binomial and Hasse-derivative
  formulas for the coefficients of `ramificationPolynomial φ α`.
* `TauCeti.natDegree_ramificationPolynomial`, `TauCeti.monic_ramificationPolynomial`,
  `TauCeti.eval_zero_ramificationPolynomial_of_isRoot`, and `TauCeti.map_ramificationPolynomial`:
  degree `n`, monicity, vanishing at `0`, and compatibility with field extensions.
* `TauCeti.coeff_ramificationPolynomial_mem_integer`: integrality `ρ_i ∈ 𝒪[L]` for all `i`.
* `TauCeti.addVal_coeff_ramificationPolynomial`,
  `TauCeti.normalizedAddValuation_coeff_ramificationPolynomial`, and
  `TauCeti.addValuation_coeff_ramificationPolynomial`: exact valuation of `ρ_i` for `1 ≤ i ≤ n`.
* `TauCeti.addVal_coeff_ramificationPolynomial_one`,
  `TauCeti.addValInt_coeff_ramificationPolynomial_one`,
  `TauCeti.normalizedAddValuation_coeff_ramificationPolynomial_one`, and
  `TauCeti.natTrailingDegree_ramificationPolynomial`: `v_L(ρ_1) = height K L` and
  `natTrailingDegree ρ = 1` when `L/K` is separable.
* `TauCeti.addValInt_coeff_ramificationPolynomial_natDegree` and
  `TauCeti.normalizedAddValuation_coeff_ramificationPolynomial_natDegree`: `v_L(ρ_n) = 0`.
* `TauCeti.separable_ramificationPolynomial_iff`, `TauCeti.separable_ramificationPolynomial`,
  `TauCeti.roots_map_ramificationPolynomial`,
  `TauCeti.roots_map_ramificationPolynomial_eq_map_algHom`, and
  `TauCeti.roots_map_ramificationPolynomial_filter_ne_zero_eq_map_algHom`: separability and the
  conjugate-difference description of the roots `(σ α - α) / α`.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, and Chapter IV, §§1–2.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory **8** (2012), 1401–1424.
-/

public section
noncomputable section

open Polynomial ValuativeRel IsLocalRing IsNonarchimedeanLocalField
open scoped IntermediateField

namespace TauCeti

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
theorem coeff_ramificationPolynomial_one (φ : 𝒪[K][X]) (α : L) :
    (ramificationPolynomial φ α).coeff 1 =
      α⁻¹ ^ φ.natDegree *
        ((φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).derivative.eval α * α) := by
  rw [coeff_ramificationPolynomial_eq_eval_hasseDeriv, hasseDeriv_one, pow_one]

/-- When `α ≠ 0`, the degree-`φ.natDegree` coefficient of `ramificationPolynomial φ α` equals the
image of `φ.leadingCoeff` in `L`. -/
theorem coeff_ramificationPolynomial_natDegree (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).coeff φ.natDegree = algebraMap K L (φ.leadingCoeff : K) := by
  rw [coeff_ramificationPolynomial, Finset.Icc_self, Finset.sum_singleton, Nat.choose_self,
    Nat.cast_one, one_mul, coeff_natDegree, mul_comm _ (α ^ φ.natDegree), ← mul_assoc,
    ← mul_pow, inv_mul_cancel₀ hα, one_pow, one_mul]

/-- The degree of `ramificationPolynomial φ α` is `φ.natDegree` whenever `φ ≠ 0` and `α ≠ 0`. -/
theorem natDegree_ramificationPolynomial {φ : 𝒪[K][X]} (hφ : φ ≠ 0) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).natDegree = φ.natDegree := by
  refine le_antisymm
    (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦
      coeff_ramificationPolynomial_of_natDegree_lt φ α hi)
    (le_natDegree_of_ne_zero ?_)
  rw [coeff_ramificationPolynomial_natDegree φ hα]
  have hlc : (φ.leadingCoeff : K) ≠ 0 := fun h ↦
    leadingCoeff_ne_zero.mpr hφ (Subtype.ext h)
  exact (map_ne_zero (algebraMap K L)).mpr hlc

/-- When `α ≠ 0`, the leading coefficient of `ramificationPolynomial φ α` is the image of
`φ.leadingCoeff` in `L`. -/
theorem leadingCoeff_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).leadingCoeff = algebraMap K L (φ.leadingCoeff : K) := by
  rcases eq_or_ne φ 0 with rfl | hφ
  · simp [ramificationPolynomial_def]
  · rw [leadingCoeff, natDegree_ramificationPolynomial hφ hα,
      coeff_ramificationPolynomial_natDegree φ hα]

/-- When `φ` is monic and `α ≠ 0`, `ramificationPolynomial φ α` is monic of degree `φ.natDegree`. -/
theorem monic_ramificationPolynomial {φ : 𝒪[K][X]} (hmonic : φ.Monic) {α : L} (hα : α ≠ 0) :
    (ramificationPolynomial φ α).Monic := by
  rw [Monic, leadingCoeff_ramificationPolynomial φ hα, hmonic.leadingCoeff, Subring.coe_one,
    map_one]

/-- When `α ≠ 0`, `ramificationPolynomial φ α` is separable if and only if `φ` mapped to `L[X]` is
separable. -/
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

end Algebraic

section EisensteinValuations

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] in
/-- Any root `α : L` of a polynomial `φ : 𝒪[K][X]` with unit leading coefficient lies in `𝒪[L]`. -/
theorem mem_integer_of_isUnit_leadingCoeff_of_isRoot {φ : 𝒪[K][X]} (hlc : IsUnit φ.leadingCoeff)
    {α : L} (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    α ∈ 𝒪[L] := by
  let u : 𝒪[K]ˣ := hlc.unit
  let g : 𝒪[K][X] := C (↑u⁻¹ : 𝒪[K]) * φ
  have hgu : (↑u⁻¹ : 𝒪[K]) * φ.leadingCoeff = 1 := by
    rw [← hlc.unit_spec, Units.inv_mul]
  have hg_monic : g.Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, hgu]
  let ψ : 𝒪[K] →+* L := (algebraMap K L).comp (algebraMap 𝒪[K] K)
  have hmap_monic : (g.map ψ).Monic := hg_monic.map ψ
  have hcoeff : ∀ i < (g.map ψ).natDegree, valuation L ((g.map ψ).coeff i) ≤ 1 := by
    intro i _
    rw [coeff_map]
    have hmem : ψ (g.coeff i) ∈ 𝒪[L] := by
      -- Map through `𝒪[K] →+* 𝒪[L] →+* L` so that valuation-ring membership is immediate.
      have hψ : ψ (g.coeff i) = (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) : L) := by
        simp [ψ, Algebra.algebraMap_ofSubsemiring_apply]
      rw [hψ]
      exact (algebraMap 𝒪[K] 𝒪[L] (g.coeff i)).2
    exact hmem
  have heval : (g.map ψ).eval α = 0 := by
    rw [Polynomial.map_mul, eval_mul, hroot.eq_zero, mul_zero]
  exact (valuation L).le_one_of_root_monic hmap_monic hcoeff heval

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- Any root `α : L` of an Eisenstein polynomial `φ : 𝒪[K][X]` lies in `𝒪[L]`. -/
theorem mem_integer_of_isEisensteinAt_of_isRoot {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K])
    {α : L} (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    α ∈ 𝒪[L] :=
  mem_integer_of_isUnit_leadingCoeff_of_isRoot hφ.isUnit_leadingCoeff hroot

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] in
private theorem isRoot_integer_of_isRoot {φ : 𝒪[K][X]} {α : L} (hα : α ∈ 𝒪[L])
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    (φ.map (algebraMap 𝒪[K] 𝒪[L])).IsRoot ⟨α, hα⟩ := by
  rw [IsRoot] at hroot ⊢
  apply Subtype.ext
  have hcomp : (algebraMap K L).comp (algebraMap 𝒪[K] K) =
      (algebraMap 𝒪[L] L).comp (algebraMap 𝒪[K] 𝒪[L]) := by
    ext x
    simp [Algebra.algebraMap_ofSubsemiring_apply]
  have hα_eq : α = algebraMap 𝒪[L] L ⟨α, hα⟩ := rfl
  rw [hcomp, ← Polynomial.map_map, hα_eq, eval_map_apply] at hroot
  simpa [Algebra.algebraMap_ofSubsemiring_apply] using hroot

/-- When `α : L` is a root of an Eisenstein polynomial `φ : 𝒪[K][X]` with `K⟮α⟯ = ⊤`, the integral
element `⟨α, …⟩ : 𝒪[L]` is irreducible (a uniformizer of `𝒪[L]`). -/
theorem irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    Irreducible (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) :=
  irreducible_of_eisenstein_adjoin_eq_top φ hφ
    ⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩
    (isRoot_integer_of_isRoot (mem_integer_of_isEisensteinAt_of_isRoot hφ hroot) hroot)
    hgen

/-- A root `α : L` of an Eisenstein polynomial `φ : 𝒪[K][X]` with `K⟮α⟯ = ⊤` is nonzero. -/
theorem ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    α ≠ 0 := by
  have hirr := irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  exact fun h ↦ hirr.ne_zero (Subtype.ext h)

/-- A root `α : L` of an Eisenstein polynomial `φ : 𝒪[K][X]` with `K⟮α⟯ = ⊤` has normalized
valuation `1`. -/
theorem addValInt_eq_one_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    addValInt L α = 1 :=
  addValInt_irreducible
    (irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen)

/-- For an Eisenstein polynomial `φ` and a root `α` generating `L/K`, `ramificationPolynomial φ α`
has degree `φ.natDegree`. -/
theorem natDegree_ramificationPolynomial_of_isEisensteinAt
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).natDegree = φ.natDegree := by
  have hne : φ ≠ 0 := by
    rintro rfl
    exact hφ.isUnit_leadingCoeff.ne_zero leadingCoeff_zero
  exact natDegree_ramificationPolynomial hne
    (ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen)

/-- For a monic Eisenstein polynomial `φ` and a root `α` generating `L/K`,
`ramificationPolynomial φ α` is monic. -/
theorem monic_ramificationPolynomial_of_isEisensteinAt
    {φ : 𝒪[K][X]} (hmonic : φ.Monic) (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).Monic :=
  monic_ramificationPolynomial hmonic
    (ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen)

/-- **Integral shifted polynomial** `φ(ξ X + ξ) ∈ 𝒪[L][X]`, whose `i`-th coefficient is
`ξ ^ φ.natDegree` times the `i`-th coefficient of `ramificationPolynomial φ α`. -/
private def intShiftedPoly (φ : 𝒪[K][X]) {α : L} (hα : α ∈ 𝒪[L]) : 𝒪[L][X] :=
  (φ.map (algebraMap 𝒪[K] 𝒪[L])).comp (C ⟨α, hα⟩ * X + C ⟨α, hα⟩)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] in
private theorem coe_coeff_intShiftedPoly (φ : 𝒪[K][X]) {α : L} (hα : α ∈ 𝒪[L]) (i : ℕ) :
    ((intShiftedPoly φ hα).coeff i : L) =
      ((φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α)).coeff i := by
  have hmap : (intShiftedPoly φ hα).map (algebraMap 𝒪[L] L) =
      (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).comp (C α * X + C α) := by
    have hcomp : (algebraMap K L).comp (algebraMap 𝒪[K] K) =
        (algebraMap 𝒪[L] L).comp (algebraMap 𝒪[K] 𝒪[L]) := by
      ext x
      simp [Algebra.algebraMap_ofSubsemiring_apply]
    simp [intShiftedPoly, Polynomial.map_comp, Polynomial.map_map, hcomp,
      Algebra.algebraMap_ofSubsemiring_apply]
  rw [← hmap, coeff_map, Algebra.algebraMap_ofSubsemiring_apply]

private theorem addVal_summand_ge_natDegree {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K])
    {α : L} (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) {i h : ℕ} (hh : h ∈ Finset.Icc i φ.natDegree) :
    (φ.natDegree : ℕ∞) ≤
      IsDiscreteValuationRing.addVal 𝒪[L]
        (algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) *
          (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) ^ h) := by
  set ξ : 𝒪[L] := ⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have he : ramificationIndex K L = φ.natDegree :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ
      (isRoot_integer_of_isRoot _ hroot) hgen
  rw [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap (K := K) (L := L), he, hξ.addVal_pow]
  rw [Finset.mem_Icc] at hh
  rcases eq_or_lt_of_le hh.2 with rfl | hlt
  · exact le_add_of_nonneg_left zero_le
  · have hmem : φ.coeff h ∈ 𝓂[K] := hφ.mem hlt
    have hv1 : (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal 𝒪[K] (φ.coeff h) := by
      simpa using (TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal
        (n := 1)).mp (by simpa using hmem)
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
        ((intShiftedPoly φ (mem_integer_of_isEisensteinAt_of_isRoot hφ hroot)).coeff i) := by
  have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
  rw [intShiftedPoly, coeff_comp_C_mul_X_add_C_eq_sum_Icc _ _ _ natDegree_map_le]
  refine (IsDiscreteValuationRing.addVal 𝒪[L]).map_le_sum fun h hh ↦ ?_
  have hrew : (h.choose i : 𝒪[L]) * (φ.map (algebraMap 𝒪[K] 𝒪[L])).coeff h *
        (⟨α, hα⟩ : 𝒪[L]) ^ (h - i) * (⟨α, hα⟩ : 𝒪[L]) ^ i =
      algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) * (⟨α, hα⟩ : 𝒪[L]) ^ h := by
    rw [coeff_map, map_mul, map_natCast, mul_assoc (_ * _), ← pow_add,
      Nat.sub_add_cancel (Finset.mem_Icc.mp hh).1]
  rw [hrew]
  exact addVal_summand_ge_natDegree hφ hroot hgen hh

/-- **Integrality of the coefficients of `ramificationPolynomial`**: for an Eisenstein polynomial
`φ : 𝒪[K][X]` and a root `α` generating `L/K`, every coefficient of `ramificationPolynomial φ α`
lies in `𝒪[L]`. -/
theorem coeff_ramificationPolynomial_mem_integer
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) (i : ℕ) :
    (ramificationPolynomial φ α).coeff i ∈ 𝒪[L] := by
  have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hα0 : α ≠ 0 := ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
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
    (intShiftedPoly φ (mem_integer_of_isEisensteinAt_of_isRoot hφ hroot)).coeff i =
      (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) ^ φ.natDegree *
        ⟨(ramificationPolynomial φ α).coeff i,
          coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩ := by
  have hα0 : α ≠ 0 := ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
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
            (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) ^ h) =
      ⨅ h ∈ Finset.Ico i φ.natDegree,
        (φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
          ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞)) := by
  have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  set n := φ.natDegree
  have hroot_int := isRoot_integer_of_isRoot hα hroot
  have he : ramificationIndex K L = n :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ hroot_int hgen
  have hn0 : (n : ℕ∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (he ▸ ramificationIndex_pos (K := K) (L := L)).ne'
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
        (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) ^ φ.natDegree) ≠ ⊤)
    (hB_fin : IsDiscreteValuationRing.addVal 𝒪[L]
      (∑ h ∈ Finset.Ico i φ.natDegree,
        algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) *
          (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) ^ h) ≠ ⊤) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        (algebraMap 𝒪[K] 𝒪[L] ((φ.natDegree.choose i : 𝒪[K]) * φ.coeff φ.natDegree) *
          (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) ^ φ.natDegree) ≠
      IsDiscreteValuationRing.addVal 𝒪[L]
        (∑ h ∈ Finset.Ico i φ.natDegree,
          algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) *
            (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) ^ h) := by
  have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  set n := φ.natDegree
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have he : ramificationIndex K L = n :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ
      (isRoot_integer_of_isRoot hα hroot) hgen
  have hn : 0 < n := he ▸ ramificationIndex_pos (K := K) (L := L)
  have hn0 : (n : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hAc : ∃ kA : ℕ, IsDiscreteValuationRing.addVal 𝒪[L]
      (algebraMap 𝒪[K] 𝒪[L] ((n.choose i : 𝒪[K]) * φ.coeff n) * ξ ^ n) =
      ((n * kA + n : ℕ) : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap (K := K) (L := L), he,
      hξ.addVal_pow] at hA_fin ⊢
    generalize IsDiscreteValuationRing.addVal 𝒪[K] ((n.choose i : 𝒪[K]) * φ.coeff n) = vA
      at hA_fin ⊢
    induction vA using ENat.recTopCoe with
    | top => exact absurd (by simp [ENat.mul_top hn0]) hA_fin
    | coe kA => exact ⟨kA, by simp [nsmul_eq_mul]⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let f : Fin n → ℕ∞ := fun j ↦
    n • IsDiscreteValuationRing.addVal 𝒪[K] (((j : ℕ).choose i : 𝒪[K]) * φ.coeff j) + (j : ℕ)
  obtain ⟨j, hj⟩ := ENat.exists_eq_iInf f
  have hj_val : IsDiscreteValuationRing.addVal 𝒪[L]
      (∑ h ∈ Finset.Ico i n,
        algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) * ξ ^ h) = f j := by
    rw [addVal_sum_Ico_intShiftedPoly hφ hroot hgen i, hj]
    refine le_antisymm (le_iInf fun k ↦ ?_)
      (le_iInf₂ fun h hh ↦ iInf_le f ⟨h, (Finset.mem_Ico.mp hh).2⟩)
    by_cases hik : i ≤ (k : ℕ)
    · exact iInf₂_le (k : ℕ) (Finset.mem_Ico.mpr ⟨hik, k.2⟩)
    · simp [f, Nat.choose_eq_zero_of_lt (lt_of_not_ge hik), ENat.mul_top hn0]
  have hji : i ≤ (j : ℕ) := by
    by_contra hlt
    rw [hj_val] at hB_fin
    exact hB_fin (by simp [f, Nat.choose_eq_zero_of_lt (lt_of_not_ge hlt), ENat.mul_top hn0])
  have hBc : ∃ kB : ℕ, f j = ((n * kB + (j : ℕ) : ℕ) : ℕ∞) := by
    rw [hj_val] at hB_fin
    dsimp only [f] at hB_fin ⊢
    generalize IsDiscreteValuationRing.addVal 𝒪[K] (((j : ℕ).choose i : 𝒪[K]) * φ.coeff j) = vB
      at hB_fin ⊢
    induction vB using ENat.recTopCoe with
    | top => exact absurd (by simp [ENat.mul_top hn0]) hB_fin
    | coe kB => exact ⟨kB, by simp [nsmul_eq_mul]⟩
  obtain ⟨kA, hkA⟩ := hAc
  obtain ⟨kB, hkB⟩ := hBc
  rw [hkA, hj_val, hkB, ne_eq, ENat.natCast_inj]
  intro heq
  have hmod := congrArg (· % n) heq
  have h1 : (n * kA + n) % n = 0 := by rw [← Nat.mul_succ, Nat.mul_mod_right]
  have h2 : (n * kB + (j : ℕ)) % n = (j : ℕ) := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
  omega

/-- **Exact valuation of `intShiftedPoly.coeff i`** for `1 ≤ i ≤ φ.natDegree`: the `h < n` block
and the `h = n` term have distinct valuations modulo `n = φ.natDegree`, so the valuation of the sum
is the infimum of the valuations of the summands. -/
private theorem addVal_coeff_intShiftedPoly
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    IsDiscreteValuationRing.addVal 𝒪[L]
        ((intShiftedPoly φ (mem_integer_of_isEisensteinAt_of_isRoot hφ hroot)).coeff i) =
      ⨅ h ∈ Finset.Icc i φ.natDegree,
        (φ.natDegree • IsDiscreteValuationRing.addVal 𝒪[K]
          ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞)) := by
  have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  set n := φ.natDegree
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have he : ramificationIndex K L = n :=
    ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ξ
      (isRoot_integer_of_isRoot hα hroot) hgen
  rw [Finset.mem_Icc] at hi
  let s : ℕ → 𝒪[L] := fun h ↦
    algebraMap 𝒪[K] 𝒪[L] ((h.choose i : 𝒪[K]) * φ.coeff h) * ξ ^ h
  have hdecomp : (intShiftedPoly φ hα).coeff i = s n + ∑ h ∈ Finset.Ico i n, s h := by
    rw [intShiftedPoly, coeff_comp_C_mul_X_add_C_eq_sum_Icc _ _ _ natDegree_map_le,
      ← Finset.insert_right_Ico hi.2, Finset.sum_insert Finset.right_notMem_Ico]
    congr 1
    · dsimp only [s, ξ]
      rw [coeff_map, map_mul, map_natCast, mul_assoc (_ * _), ← pow_add,
        Nat.sub_add_cancel hi.2]
    · refine Finset.sum_congr rfl fun h hh ↦ ?_
      dsimp only [s, ξ]
      rw [coeff_map, map_mul, map_natCast, mul_assoc (_ * _), ← pow_add,
        Nat.sub_add_cancel (Finset.mem_Ico.mp hh).1]
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
      n • IsDiscreteValuationRing.addVal 𝒪[K] ((n.choose i : 𝒪[K]) * φ.coeff n) + (n : ℕ∞) := by
    rw [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap (K := K) (L := L), he, hξ.addVal_pow]
  rw [hdecomp, hmin, hs_n, addVal_sum_Ico_intShiftedPoly hφ hroot hgen i,
    ← Finset.insert_right_Ico hi.2]
  refine le_antisymm (le_iInf₂ fun h hh ↦ ?_) (le_min ?_ (le_iInf₂ fun h hh ↦ ?_))
  · rcases Finset.mem_insert.mp hh with rfl | hh'
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (iInf₂_le h hh')
  · exact iInf₂_le n (Finset.mem_insert_self _ _)
  · exact iInf₂_le h (Finset.mem_insert_of_mem hh)

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
  have hξ : Irreducible (⟨α, mem_integer_of_isEisensteinAt_of_isRoot hφ hroot⟩ : 𝒪[L]) :=
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

private def enatToWithTopReal : ℕ∞ → WithTop ℝ :=
  ENat.recTopCoe ⊤ fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ)

private theorem enatToWithTopReal_monotone : Monotone enatToWithTopReal := by
  intro x y hxy
  induction x using ENat.recTopCoe with
  | top =>
    rw [top_le_iff] at hxy
    subst hxy
    exact le_rfl
  | coe a =>
    induction y using ENat.recTopCoe with
    | top => exact le_top
    | coe b =>
      have hab : a ≤ b := Nat.cast_le.mp hxy
      rw [enatToWithTopReal, ENat.recTopCoe_natCast, enatToWithTopReal, ENat.recTopCoe_natCast]
      exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hab)

private theorem enatToWithTopReal_sub_natCast {n : ℕ} {x : ℕ∞} (hx : (n : ℕ∞) ≤ x) :
    enatToWithTopReal (x - (n : ℕ∞)) = enatToWithTopReal x - ((n : ℝ) : WithTop ℝ) := by
  induction x using ENat.recTopCoe with
  | top => rfl
  | coe m =>
    have hnm : n ≤ m := Nat.cast_le.mp hx
    rw [← ENat.natCast_sub, enatToWithTopReal, ENat.recTopCoe_natCast, enatToWithTopReal,
      ENat.recTopCoe_natCast, ← WithTop.LinearOrderedAddCommGroup.coe_sub, Nat.cast_sub hnm]

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
  set n := φ.natDegree
  set q : 𝒪[L] := ⟨(ramificationPolynomial φ α).coeff i,
    coeff_ramificationPolynomial_mem_integer hφ hroot hgen i⟩
  have hcoe : ((ramificationPolynomial φ α).coeff i) = (q : L) := rfl
  rw [hcoe, normalizedAddValuation_coe_integer]
  have hterm (h : ℕ) :
      enatToWithTopReal
          (n • IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞)) =
        (normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K))).map ((n : ℝ) * ·) +
          ((h : ℝ) : WithTop ℝ) := by
    have hKcoe : ((h.choose i : K) * (φ.coeff h : K)) =
        (((h.choose i : 𝒪[K]) * φ.coeff h : 𝒪[K]) : K) := by simp
    rw [hKcoe, normalizedAddValuation_coe_integer]
    have hn0 : n ≠ 0 := by have := Finset.mem_Icc.mp hi; omega
    have hn0' : (n : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    generalize IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) = vK
    induction vK using ENat.recTopCoe with
    | top => simp [enatToWithTopReal, ENat.mul_top hn0']
    | coe k =>
      simp only [enatToWithTopReal, nsmul_eq_mul, ← ENat.natCast_mul, ← ENat.natCast_add,
        ENat.recTopCoe_natCast, WithTop.map_coe, ← WithTop.coe_add]
      push_cast
      rfl
  set Hne : (Finset.Icc i n).Nonempty := ⟨n, Finset.right_mem_Icc.mpr (Finset.mem_Icc.mp hi).2⟩
  have hiInf_eq : (⨅ h ∈ Finset.Icc i n,
      (n • IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) + (h : ℕ∞))) =
      (Finset.Icc i n).inf' Hne
        (fun h ↦ n • IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) +
          (h : ℕ∞)) :=
    le_antisymm (Finset.le_inf' Hne _ fun h hh ↦ iInf₂_le h hh)
      (le_iInf₂ fun h hh ↦ Finset.inf'_le _ hh)
  have hge : (n : ℕ∞) ≤ (Finset.Icc i n).inf' Hne
      (fun h ↦ n • IsDiscreteValuationRing.addVal 𝒪[K] ((h.choose i : 𝒪[K]) * φ.coeff h) +
        (h : ℕ∞)) := by
    rw [Finset.le_inf'_iff]
    intro h hh
    have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
    have h1 := addVal_summand_ge_natDegree hφ hroot hgen hh
    have hξ : Irreducible (⟨α, hα⟩ : 𝒪[L]) :=
      irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
    have he : ramificationIndex K L = n :=
      ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top φ hφ ⟨α, hα⟩
        (isRoot_integer_of_isRoot hα hroot) hgen
    rwa [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap (K := K) (L := L), he,
      hξ.addVal_pow] at h1
  have hlhs : ENat.recTopCoe ⊤ (fun k : ℕ ↦ ((k : ℝ) : WithTop ℝ))
        (IsDiscreteValuationRing.addVal 𝒪[L] q) =
      enatToWithTopReal (IsDiscreteValuationRing.addVal 𝒪[L] q) := rfl
  rw [hlhs, addVal_coeff_ramificationPolynomial hφ hroot hgen hi, hiInf_eq,
    enatToWithTopReal_sub_natCast hge,
    Finset.apply_inf'_eq_inf'_comp Hne enatToWithTopReal fun _ _ ↦
      enatToWithTopReal_monotone.map_min]
  simp_rw [Function.comp_def, hterm]
  rfl

/-- **Exact `WithTop ℝ` valuation formula** for any `v : AddValuation L (WithTop ℝ)` agreeing with
`addValInt L` away from zero. -/
theorem addValuation_coeff_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) (v : AddValuation L (WithTop ℝ))
    (hv : ∀ x : L, x ≠ 0 → v x = ((addValInt L x : ℝ) : WithTop ℝ))
    {i : ℕ} (hi : i ∈ Finset.Icc 1 φ.natDegree) :
    v ((ramificationPolynomial φ α).coeff i) =
      ((Finset.Icc i φ.natDegree).inf'
        ⟨φ.natDegree, Finset.right_mem_Icc.mpr (Finset.mem_Icc.mp hi).2⟩
        fun h ↦ (normalizedAddValuation K ((h.choose i : K) * (φ.coeff h : K))).map
          ((φ.natDegree : ℝ) * ·) + ((h : ℝ) : WithTop ℝ)) -
        ((φ.natDegree : ℝ) : WithTop ℝ) := by
  rw [eq_normalizedAddValuation hv,
    normalizedAddValuation_coeff_ramificationPolynomial hφ hroot hgen hi]

/-- At the right endpoint `i = φ.natDegree`, the coefficient of `ramificationPolynomial φ α` has
normalized valuation `0` in `ℤ`. -/
theorem addValInt_coeff_ramificationPolynomial_natDegree
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    addValInt L ((ramificationPolynomial φ α).coeff φ.natDegree) = 0 := by
  have hα0 : α ≠ 0 := ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  rw [coeff_ramificationPolynomial_natDegree φ hα0, addValInt_algebraMap,
    addValInt_eq_zero_of_isUnit_integer hφ.isUnit_leadingCoeff, mul_zero]

/-- At the right endpoint `i = φ.natDegree`, the coefficient of `ramificationPolynomial φ α` has
`normalizedAddValuation` equal to `0`. -/
theorem normalizedAddValuation_coeff_ramificationPolynomial_natDegree
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    normalizedAddValuation L ((ramificationPolynomial φ α).coeff φ.natDegree) = 0 := by
  have hα0 : α ≠ 0 := ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hne : (ramificationPolynomial φ α).coeff φ.natDegree ≠ 0 := by
    rw [coeff_ramificationPolynomial_natDegree φ hα0]
    exact (map_ne_zero (algebraMap K L)).mpr fun h ↦
      hφ.isUnit_leadingCoeff.ne_zero (Subtype.ext h)
  rw [normalizedAddValuation_of_ne_zero hne,
    addValInt_coeff_ramificationPolynomial_natDegree hφ hroot hgen, Int.cast_zero,
    WithTop.coe_zero]

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
  have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hξ : Irreducible ξ :=
    irreducible_integer_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hroot_int := isRoot_integer_of_isRoot hα hroot
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

/-- When `L/K` is separable, the linear coefficient of `ramificationPolynomial φ α` is nonzero. -/
theorem coeff_ramificationPolynomial_one_ne_zero
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).coeff 1 ≠ 0 := by
  intro h0
  have hv := addVal_coeff_ramificationPolynomial_one hφ hroot hgen
  have hsub0 : (⟨(ramificationPolynomial φ α).coeff 1,
      coeff_ramificationPolynomial_mem_integer hφ hroot hgen 1⟩ : 𝒪[L]) = 0 := Subtype.ext h0
  rw [hsub0, AddValuation.map_zero] at hv
  exact ENat.natCast_ne_top (height K L) hv.symm

/-- When `L/K` is separable, `ramificationPolynomial φ α` has trailing degree `1` (it vanishes to
order `1` at `0`), so its Newton polygon begins at abscissa `1`. -/
theorem natTrailingDegree_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).natTrailingDegree = 1 := by
  have hc1 := coeff_ramificationPolynomial_one_ne_zero hφ hroot hgen
  have hp0 : ramificationPolynomial φ α ≠ 0 := fun h ↦ hc1 (by simp [h])
  refine le_antisymm (natTrailingDegree_le_of_ne_zero hc1) (le_natTrailingDegree hp0 fun m hm ↦ ?_)
  obtain rfl : m = 0 := by omega
  exact coeff_ramificationPolynomial_zero_of_isRoot hroot

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
  rw [normalizedAddValuation_of_ne_zero (coeff_ramificationPolynomial_one_ne_zero hφ hroot hgen),
    addValInt_coeff_ramificationPolynomial_one hφ hroot hgen, Int.cast_natCast]
  rfl

/-- **The linear-term valuation** for any `v : AddValuation L (WithTop ℝ)` agreeing with
`addValInt L` away from zero equals `height K L`. -/
theorem addValuation_coeff_ramificationPolynomial_one
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) (v : AddValuation L (WithTop ℝ))
    (hv : ∀ x : L, x ≠ 0 → v x = ((addValInt L x : ℝ) : WithTop ℝ)) :
    v ((ramificationPolynomial φ α).coeff 1) = (height K L : WithTop ℝ) := by
  rw [eq_normalizedAddValuation hv,
    normalizedAddValuation_coeff_ramificationPolynomial_one hφ hroot hgen]

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

/-- When `α ≠ 0`, `x : M` is a root of `ramificationPolynomial φ α` if and only if `α x + α` is a
root of `φ`. -/
theorem isRoot_map_ramificationPolynomial_iff (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) (x : M) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).IsRoot x ↔
      ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K M)).IsRoot
        (algebraMap L M α * x + algebraMap L M α) := by
  have hαM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα
  have hc : ((algebraMap L M α)⁻¹ ^ φ.natDegree : M) ≠ 0 := pow_ne_zero _ (inv_ne_zero hαM)
  rw [map_ramificationPolynomial, ramificationPolynomial_def, ← Polynomial.map_map, IsRoot.def,
    IsRoot.def, eval_mul, eval_C, eval_comp, eval_add, eval_mul, eval_C, eval_X, mul_eq_zero,
    or_iff_right hc]

/-- When `α ≠ 0`, the root multiplicity of `x : M` in `ramificationPolynomial φ α` equals the root
multiplicity of `α x + α` in `φ`. -/
theorem rootMultiplicity_map_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) (x : M) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).rootMultiplicity x =
      ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K M)).rootMultiplicity
        (algebraMap L M α * x + algebraMap L M α) := by
  have hαM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα
  have hc : ((algebraMap L M α)⁻¹ ^ φ.natDegree : M) ≠ 0 := pow_ne_zero _ (inv_ne_zero hαM)
  rw [map_ramificationPolynomial, ramificationPolynomial_def, ← Polynomial.map_map,
    rootMultiplicity_C_mul hc, rootMultiplicity_comp_C_mul_X_add_C _ _ _ x hαM.isUnit]

/-- **Roots of `ramificationPolynomial` from roots of `φ`**: for `α ≠ 0` and any extension field
`M` of `L`, the multiset of roots of `ramificationPolynomial φ α` in `M` is `(r - α) / α` as `r`
ranges over the roots of `φ` in `M`. -/
theorem roots_map_ramificationPolynomial (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).roots =
      (((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K M)).roots).map
        fun r ↦ (r - algebraMap L M α) / algebraMap L M α := by
  have hαM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα
  have hc : ((algebraMap L M α)⁻¹ ^ φ.natDegree : M) ≠ 0 := pow_ne_zero _ (inv_ne_zero hαM)
  rw [map_ramificationPolynomial, ramificationPolynomial_def, ← Polynomial.map_map,
    roots_C_mul _ hc, roots_comp_C_mul_X_add_C _ _ _ hαM.isUnit]
  refine Multiset.map_congr rfl fun r _ ↦ ?_
  simp [div_eq_inv_mul, mul_comm]

/-- When `α ≠ 0`, `ramificationPolynomial φ α` splits over `M` if and only if `φ` splits over
`M`. -/
theorem splits_map_ramificationPolynomial_iff (φ : 𝒪[K][X]) {α : L} (hα : α ≠ 0) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).Splits ↔
      ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K M)).Splits := by
  have hαM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα
  set P : M[X] := (φ.map (algebraMap 𝒪[K] K)).map (algebraMap K M)
  constructor
  · intro hsp
    have hcomp_sp : (P.comp (C (algebraMap L M α) * X + C (algebraMap L M α))).Splits := by
      have h1 : P.comp (C (algebraMap L M α) * X + C (algebraMap L M α)) =
          C (algebraMap L M α ^ φ.natDegree) *
            ((ramificationPolynomial φ α).map (algebraMap L M)) := by
        rw [map_ramificationPolynomial, ramificationPolynomial_def, ← Polynomial.map_map,
          ← mul_assoc, ← C_mul, ← mul_pow, mul_inv_cancel₀ hαM, one_pow, C_1, one_mul]
      rw [h1]
      exact hsp.C_mul _
    have hinv : P = (P.comp (C (algebraMap L M α) * X + C (algebraMap L M α))).comp
        (C (algebraMap L M α)⁻¹ * X + C (-1 : M)) := by
      rw [comp_assoc]
      suffices (C (algebraMap L M α) * X + C (algebraMap L M α)).comp
          (C (algebraMap L M α)⁻¹ * X + C (-1 : M)) = X by
        rw [this, comp_X]
      rw [add_comp, mul_comp, C_comp, X_comp, mul_add, ← mul_assoc, ← C_mul,
        mul_inv_cancel₀ hαM, C_1, one_mul, ← C_mul, mul_neg, mul_one, C_neg,
        add_assoc, neg_add_cancel, add_zero]
    rw [hinv]
    exact hcomp_sp.comp_of_natDegree_le_one (by compute_degree!)
  · intro hsp
    rw [map_ramificationPolynomial, ramificationPolynomial_def, ← Polynomial.map_map]
    exact (hsp.comp_of_natDegree_le_one (by compute_degree!)).C_mul _

section EisensteinRoots

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [Algebra.IsSeparable K L]

private theorem map_eisenstein_eq_C_mul_minpoly
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α) :
    φ.map (algebraMap 𝒪[K] K) = C (φ.leadingCoeff : K) * minpoly K α := by
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hα : α ∈ 𝒪[L] := mem_integer_of_isEisensteinAt_of_isRoot hφ hroot
  set ξ : 𝒪[L] := ⟨α, hα⟩
  have hint : IsIntegral 𝒪[K] ξ := IsIntegral.of_finite 𝒪[K] ξ
  have hassoc : Associated (minpoly 𝒪[K] ξ) φ :=
    hφ.associated_minpoly hφ.isUnit_leadingCoeff (isRoot_integer_of_isRoot hα hroot)
  have hscale : φ = C φ.leadingCoeff * minpoly 𝒪[K] ξ :=
    eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hint) hassoc.dvd
      (natDegree_le_natDegree (degree_eq_degree_of_associated hassoc).symm.le)
  have hminpoly : minpoly K α = (minpoly 𝒪[K] ξ).map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hmap := congrArg (Polynomial.map (algebraMap 𝒪[K] K)) hscale
  rwa [Polynomial.map_mul, map_C, ← hminpoly] at hmap

/-- **Separability of `ramificationPolynomial`**: when `L/K` is separable, `φ` is Eisenstein, and
`α` is a root of `φ` with `K⟮α⟯ = ⊤`, `ramificationPolynomial φ α` is separable. -/
theorem separable_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    (ramificationPolynomial φ α).Separable := by
  have hα0 : α ≠ 0 := ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hlc : (φ.leadingCoeff : K) ≠ 0 := fun h ↦
    hφ.isUnit_leadingCoeff.ne_zero (Subtype.ext h)
  rw [separable_ramificationPolynomial_iff hα0, ← Polynomial.map_map,
    map_eisenstein_eq_C_mul_minpoly hφ hroot]
  exact (Separable.unit_mul (isUnit_C.mpr hlc.isUnit) (Algebra.IsSeparable.isSeparable K α)).map

omit [Algebra K M] [IsScalarTower K L M] in
/-- Over any extension field `M` of `L`, `(ramificationPolynomial φ α).map (algebraMap L M)` is
separable when `L/K` is separable. -/
theorem separable_map_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).Separable :=
  (separable_ramificationPolynomial hφ hroot hgen).map

omit [Algebra K M] [IsScalarTower K L M] in
/-- Over any extension field `M` of `L`, every root of `ramificationPolynomial φ α` in `M` is
simple (`Nodup`). -/
theorem nodup_roots_map_ramificationPolynomial
    {φ : 𝒪[K][X]} (hφ : φ.IsEisensteinAt 𝓂[K]) {α : L}
    (hroot : (φ.map ((algebraMap K L).comp (algebraMap 𝒪[K] K))).IsRoot α)
    (hgen : K⟮α⟯ = ⊤) :
    ((ramificationPolynomial φ α).map (algebraMap L M)).roots.Nodup :=
  nodup_roots (separable_map_ramificationPolynomial hφ hroot hgen)

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
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hα0 : α ≠ 0 := ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hlcM : algebraMap K M (φ.leadingCoeff : K) ≠ 0 :=
    (map_ne_zero (algebraMap K M)).mpr fun h ↦ hφ.isUnit_leadingCoeff.ne_zero (Subtype.ext h)
  have hroots_φ : ((φ.map (algebraMap 𝒪[K] K)).map (algebraMap K M)).roots =
      (minpoly K α).aroots M := by
    rw [map_eisenstein_eq_C_mul_minpoly hφ hroot, Polynomial.map_mul, map_C,
      roots_C_mul _ hlcM, aroots_def]
  let pb : PowerBasis K L := PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite K α) hgen
  have hpb_gen : pb.gen = α := PowerBasis.ofAdjoinSimpleEqTop_gen _ hgen
  rw [roots_map_ramificationPolynomial φ hα0, hroots_φ, ← hpb_gen,
    pb.aroots_minpoly_gen_eq_map_algHom (Algebra.IsSeparable.isSeparable K pb.gen),
    Multiset.map_map]
  rfl

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
  have : Module.Finite K L := finite_of_valuativeExtension K L
  have hα0 : α ≠ 0 := ne_zero_of_isEisensteinAt_of_isRoot_of_adjoin_eq_top hφ hroot hgen
  have hαM : algebraMap L M α ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hα0
  let pb : PowerBasis K L := PowerBasis.ofAdjoinSimpleEqTop (IsIntegral.of_finite K α) hgen
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

end TauCeti
