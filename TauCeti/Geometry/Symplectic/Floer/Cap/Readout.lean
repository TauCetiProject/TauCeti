/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Sewing
public import TauCeti.Geometry.Symplectic.Floer.Cap.Unit
public import TauCeti.Geometry.Symplectic.Floer.Cap.Comparison
public import TauCeti.Geometry.Symplectic.Floer.Cap.Aspherical
import TauCeti.Geometry.Symplectic.Floer.Grading
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Operator readout and coevaluation sewing of class-indexed Floer count functionals

Counts of rigid moduli spaces in Hamiltonian Floer theory with input ends in `X` and an output orbit
in `CF₀` define functionals on `X ⊗ CF₀^∨`, indexed class by class in `G` over `Γ = PeriodGroup ω c`
via an area-preserving homomorphism `q`. Recapping an orbit `k` by `γ ∈ Γ` shifts `μ₀` by the even
integer `2 c₁(γ)`, so the graded bidual sign `(-1)^(n - μ₀(k, D₀))` depends only on `k` and agrees
with `(-1)^(n - μ₀(k, r₀ k))` at any reference cap `r₀ k`
(`TauCeti.Floer.negOnePowCast_cochain_eq_ref`).
Operator readout therefore acts directly on `G`-indexed series (`TauCeti.Floer.seriesReadout`) and
agrees on all capped generators with `NovikovModule.combinationReadout` and
`NovikovModule.kernelReadout`:

* **Reference-cap invariance and unit caps:** `seriesReadout` is invariant under translating
  reference caps (`seriesReadout_vadd`, `novikovProductOfMatrix_seriesReadout_vadd`) and fixes any
  PSS unit cap functional satisfying `μ₁(r₁ i) - 2 c₁(q A) = n`
  (`seriesReadout_eq_self_of_unit_index`).
* **Class-indexed sewing and boundaries:** `seriesSew` and `seriesSewPair` intertwine
  `seriesReadout` with matrix composition (`seriesSew_seriesReadout`, `seriesReadout_seriesSew`,
  `seriesReadout_seriesSewPair_of_index`), with `seriesEval` as identity readout; `seriesBoundary`
  intertwines `seriesReadout` with the Hom differential under the Floer Fredholm index condition
  (`seriesBoundary_seriesReadout_of_index`), even when `c₁ ≠ 0`.
* **Capped Floer identities and classical sign check:** Combining readout with `Cap.Product`,
  `Cap.Unit`, and `Cap.Comparison` yields the capped Leibniz rule, left/right unit homotopies,
  associativity homotopy, and multiplicative PSS comparisons directly from count-functional
  boundaries, together with the odd-degree skew-commutativity check
  `novikovProductOfMatrix_seriesReadout_skew_of_subsingleton`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 11 and 12.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [CommRing R] [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ}

section SeriesReadout

variable {ι₁ ι₂ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}

/-- **Operator readout of class-indexed count functionals**, multiplying at output orbit `k` by
`(-1)^(n - μ₀(k, r₀ k))`. -/
def seriesReadout (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ : ι₀ → NovikovSeries R G ωG) (k : ι₀) : NovikovSeries R G ωG :=
  negOnePowCast R (n - μ₀ ⟨k, r₀ k⟩) • Ψ k

/-- A value of `TauCeti.Floer.seriesReadout` at an output orbit. -/
theorem seriesReadout_apply (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ : ι₀ → NovikovSeries R G ωG) (k : ι₀) :
    seriesReadout r₀ μ₀ n Ψ k = negOnePowCast R (n - μ₀ ⟨k, r₀ k⟩) • Ψ k := (rfl)

/-- Class-indexed operator readout is an involution. -/
@[simp]
theorem seriesReadout_seriesReadout (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ : ι₀ → NovikovSeries R G ωG) :
    seriesReadout r₀ μ₀ n (seriesReadout r₀ μ₀ n Ψ) = Ψ := by funext k; simp [seriesReadout_apply]

@[simp]
theorem seriesReadout_zero (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ) :
    seriesReadout r₀ μ₀ n (0 : ι₀ → NovikovSeries R G ωG) = 0 := by
  funext k; simp [seriesReadout_apply]

@[simp]
theorem seriesReadout_add (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ Ψ' : ι₀ → NovikovSeries R G ωG) :
    seriesReadout r₀ μ₀ n (Ψ + Ψ') = seriesReadout r₀ μ₀ n Ψ + seriesReadout r₀ μ₀ n Ψ' := by
  funext k; simp [seriesReadout_apply, smul_add]

@[simp]
theorem seriesReadout_neg (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ : ι₀ → NovikovSeries R G ωG) :
    seriesReadout r₀ μ₀ n (-Ψ) = -seriesReadout r₀ μ₀ n Ψ := by funext k; simp [seriesReadout_apply]

@[simp]
theorem seriesReadout_sub (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ Ψ' : ι₀ → NovikovSeries R G ωG) :
    seriesReadout r₀ μ₀ n (Ψ - Ψ') = seriesReadout r₀ μ₀ n Ψ - seriesReadout r₀ μ₀ n Ψ' := by
  funext k; simp [seriesReadout_apply, smul_sub]

@[simp]
theorem seriesReadout_sub_apply (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ Ψ' : ι₀ → NovikovSeries R G ωG) (k : ι₀) :
    seriesReadout r₀ μ₀ n (Ψ - Ψ') k =
      seriesReadout r₀ μ₀ n Ψ k - seriesReadout r₀ μ₀ n Ψ' k := by
  simp [seriesReadout_apply, smul_sub]

/-- Operator readout preserves class supports. -/
theorem support_seriesReadout_subset (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ : ι₀ → NovikovSeries R G ωG) (k : ι₀) :
    (seriesReadout r₀ μ₀ n Ψ k).support ⊆ (Ψ k).support :=
  support_smul_subset _ (Ψ k)

/-- At an output orbit of odd cochain degree, `seriesReadout` negates the count functional. -/
theorem seriesReadout_eq_neg_of_odd (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (Ψ : ι₀ → NovikovSeries R G ωG) {k : ι₀} (hk : Odd (n - μ₀ ⟨k, r₀ k⟩)) :
    seriesReadout r₀ μ₀ n Ψ k = -Ψ k := by
  rw [seriesReadout_apply, negOnePowCast_odd hk, neg_one_smul]

/-- **Change of reference caps preserves `seriesReadout`.** -/
theorem seriesReadout_vadd [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)] (r₀ : ∀ k, P₀ k)
    {μ₀ : (Σ k, P₀ k) → ℤ}
    (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    (γ : ι₀ → PeriodGroup ω c) (n : ℤ) (Ψ : ι₀ → NovikovSeries R G ωG) :
    seriesReadout (fun k => γ k +ᵥ r₀ k) μ₀ n Ψ = seriesReadout r₀ μ₀ n Ψ := by
  funext k
  rw [seriesReadout_apply, seriesReadout_apply,
    negOnePowCast_cochain_eq_ref hμ₀ r₀ n k (γ k +ᵥ r₀ k)]

/-- **Unit cap functionals equal their own combination readout** when
`μ₁(r₁ i) - 2 c₁(q A) = n`. -/
theorem seriesReadout_eq_self_of_unit_index (q : G →+ PeriodGroup ω c) (r₁ : ∀ i, P₁ i)
    (μ₁ : (Σ i, P₁ i) → ℤ) (n : ℤ) {Ε : ι₁ → NovikovSeries R G ωG}
    (hΕ : ∀ i, ∀ A ∈ (Ε i).support, μ₁ ⟨i, r₁ i⟩ - degree ω c (q A) = n) :
    seriesReadout r₁ μ₁ n Ε = Ε := by
  funext i
  by_cases hi : Ε i = 0
  · simp [seriesReadout_apply, hi]
  · obtain ⟨A, hA⟩ := NovikovSeries.support_nonempty_iff.mpr hi
    have hd : n - μ₁ ⟨i, r₁ i⟩ = -degree ω c (q A) := by linarith [hΕ i A hA]
    rw [seriesReadout_apply, hd, negOnePowCast_even (even_degree ω c (q A)).neg, one_smul]

variable [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]

section KernelAgreement

variable (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  (q : G →+ PeriodGroup ω c) (hq : ∀ A, area ω c (q A) = ωG A)
  {μ₀ : (Σ k, P₀ k) → ℤ}
  (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)

include hμ₀

/-- **Agreement of `seriesReadout` with `combinationReadout` on capped generators.** -/
theorem combinationReadout_coordinates_symm_coefficientComparison [Finite ι₀]
    {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ) (n : ℤ)
    (Ε : ι₀ → NovikovSeries R G ωG) :
    combinationReadout (fun p => n - μ₀ p)
        (((coordinates hF₀ r₀).symm fun k => coefficientComparison q hq (Ε k)).val) =
      ((coordinates hF₀ r₀).symm fun k =>
        coefficientComparison q hq (seriesReadout r₀ μ₀ n Ε k)).val := by
  funext ⟨k, D₀⟩
  rw [combinationReadout_apply, coordinates_symm_apply, coordinates_symm_apply,
    negOnePowCast_cochain_eq_ref hμ₀ r₀ n k D₀, seriesReadout_apply, map_negOnePowCast_smul,
    coeff_smul, smul_eq_mul]

/-- **Agreement of `seriesReadout` with `kernelReadout` on `mapKernelOfMatrix`.** -/
theorem kernelReadout_mapKernelOfMatrix_coefficientComparison (n : ℤ)
    (Φ : ι₁ → ι₀ → NovikovSeries R G ωG) :
    kernelReadout (fun p => n - μ₀ p)
        (mapKernelOfMatrix r₁ r₀ fun i k => coefficientComparison q hq (Φ i k)) =
      mapKernelOfMatrix r₁ r₀ fun i k =>
        coefficientComparison q hq (seriesReadout r₀ μ₀ n (Φ i) k) := by
  funext ⟨i, D₁⟩ ⟨k, D₀⟩
  rw [kernelReadout_apply,
    mapKernelOfMatrix_apply r₁ r₀ (fun i k => coefficientComparison q hq (Φ i k)) D₁ D₀,
    mapKernelOfMatrix_apply r₁ r₀
      (fun i k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Φ i) k)) D₁ D₀,
    negOnePowCast_cochain_eq_ref hμ₀ r₀ n k D₀, seriesReadout_apply, map_negOnePowCast_smul,
    coeff_smul, smul_eq_mul]

/-- **Agreement of `seriesReadout` with `kernelReadout` on `kernelOfMatrix`.** -/
theorem kernelReadout_kernelOfMatrix_coefficientComparison (n : ℤ)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) :
    kernelReadout (fun p => n - μ₀ p)
        (fun x : (Σ i, P₁ i) × (Σ j, P₂ j) =>
          kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Ψ i j k)) x.1 x.2) =
      fun x => kernelOfMatrix r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k)) x.1 x.2 := by
  funext ⟨⟨i, D₁⟩, ⟨j, D₂⟩⟩ ⟨k, D₀⟩
  rw [kernelReadout_apply, kernelOfMatrix_apply, kernelOfMatrix_apply,
    negOnePowCast_cochain_eq_ref hμ₀ r₀ n k D₀, seriesReadout_apply, map_negOnePowCast_smul,
    coeff_smul, smul_eq_mul]

end KernelAgreement

/-- **Change of reference caps for the readout product.** Shifting reference caps to `q(gₗ) +ᵥ rₗ`
and multiplying functional series by `q^(g₀ - g₁ - g₂)` preserves the readout product. -/
theorem novikovProductOfMatrix_seriesReadout_vadd {G : Type*} [AddGroup G] {ωG : G →+ ℝ}
    [Finite ι₁] [Finite ι₂] [Finite ι₀]
    (q : G →+ PeriodGroup ω c) (hq : ∀ A, area ω c (q A) = ωG A)
    (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
    {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
    {μ₀ : (Σ k, P₀ k) → ℤ}
    (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩) (n : ℤ)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (g₁ : ι₁ → G) (g₂ : ι₂ → G) (g₀ : ι₀ → G) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ (fun i => q (g₁ i) +ᵥ r₁ i) (fun j => q (g₂ j) +ᵥ r₂ j)
        (fun k => q (g₀ k) +ᵥ r₀ k)
        (fun i j k => coefficientComparison q hq
          (seriesReadout (fun k => q (g₀ k) +ᵥ r₀ k) μ₀ n
            (fun k => NovikovSeries.single (g₀ k - g₁ i - g₂ j) 1 * Ψ i j k) k)) =
      novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k)) := by
  have hsmul : ∀ i j k,
      seriesReadout (fun k => q (g₀ k) +ᵥ r₀ k) μ₀ n
          (fun k => NovikovSeries.single (g₀ k - g₁ i - g₂ j) 1 * Ψ i j k) k =
        NovikovSeries.single (g₀ k - g₁ i - g₂ j) 1 *
          seriesReadout r₀ μ₀ n (Ψ i j) k := fun i j k => by
    rw [seriesReadout_vadd r₀ hμ₀, seriesReadout_apply, seriesReadout_apply, mul_smul_comm]
  simp only [hsmul]
  exact novikovProductOfMatrix_coefficientComparison_vadd r₁ r₂ r₀ q hq hF₁ hF₂ hF₀
    (fun i j k => seriesReadout r₀ μ₀ n (Ψ i j) k) g₁ g₂ g₀

end SeriesReadout

section SeriesSew

variable {ι₁ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*}

/-- **Class-indexed coevaluation sewing** along intermediate orbits `t ∈ ι₁` with weight
`(-1)^(n - μ₁(t, r₁ t))`. -/
def seriesSew [Fintype ι₁] (r₁ : ∀ t, P₁ t) (μ₁ : (Σ t, P₁ t) → ℤ) (n : ℤ)
    (Φ : ι₁ → NovikovSeries R G ωG) (Ψ : ι₁ → ι₀ → NovikovSeries R G ωG) (l : ι₀) :
    NovikovSeries R G ωG :=
  ∑ t, negOnePowCast R (n - μ₁ ⟨t, r₁ t⟩) • (Φ t * Ψ t l)

/-- A value of `TauCeti.Floer.seriesSew` at an output orbit. -/
theorem seriesSew_apply [Fintype ι₁] (r₁ : ∀ t, P₁ t) (μ₁ : (Σ t, P₁ t) → ℤ) (n : ℤ)
    (Φ : ι₁ → NovikovSeries R G ωG) (Ψ : ι₁ → ι₀ → NovikovSeries R G ωG) (l : ι₀) :
    seriesSew r₁ μ₁ n Φ Ψ l = ∑ t, negOnePowCast R (n - μ₁ ⟨t, r₁ t⟩) • (Φ t * Ψ t l) := (rfl)

/-- **Class-indexed right-evaluation functional** `γ_min`, reading out to `[k = k']`. -/
def seriesEval [DecidableEq ι₀] (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (k k' : ι₀) : NovikovSeries R G ωG :=
  if k = k' then negOnePowCast R (n - μ₀ ⟨k, r₀ k⟩) • 1 else 0

/-- A value of `TauCeti.Floer.seriesEval` at a pair of orbits. -/
theorem seriesEval_apply [DecidableEq ι₀] (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ) (n : ℤ)
    (k k' : ι₀) :
    (seriesEval r₀ μ₀ n k k' : NovikovSeries R G ωG) =
      if k = k' then negOnePowCast R (n - μ₀ ⟨k, r₀ k⟩) • 1 else 0 := (rfl)

@[simp]
theorem seriesReadout_seriesEval [DecidableEq ι₀] (r₀ : ∀ k, P₀ k) (μ₀ : (Σ k, P₀ k) → ℤ)
    (n : ℤ) (k k' : ι₀) :
    seriesReadout r₀ μ₀ n (seriesEval r₀ μ₀ n k : ι₀ → NovikovSeries R G ωG) k' =
      if k = k' then 1 else 0 := by
  obtain rfl | h := eq_or_ne k k' <;> simp [seriesReadout_apply, seriesEval_apply, *]

/-- **Sewing two readout functionals gives the readout of the matrix product.** -/
theorem seriesSew_seriesReadout [Fintype ι₁] (r₁ : ∀ t, P₁ t) (r₀ : ∀ l, P₀ l)
    (μ₁ : (Σ t, P₁ t) → ℤ) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ)
    (T : ι₁ → NovikovSeries R G ωG) (S : ι₁ → ι₀ → NovikovSeries R G ωG) :
    seriesSew r₁ μ₁ n (seriesReadout r₁ μ₁ n T) (fun t => seriesReadout r₀ μ₀ n (S t)) =
      seriesReadout r₀ μ₀ n fun l => ∑ t, T t * S t l := by
  funext l
  rw [seriesSew_apply, seriesReadout_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => by
    rw [seriesReadout_apply, seriesReadout_apply, smul_mul_assoc, mul_smul_comm, smul_smul,
      negOnePowCast_mul_self, one_smul]

/-- **Operator readout turns `seriesSew` into matrix composition of readouts.** -/
@[simp]
theorem seriesReadout_seriesSew [Fintype ι₁] (r₁ : ∀ t, P₁ t) (r₀ : ∀ l, P₀ l)
    (μ₁ : (Σ t, P₁ t) → ℤ) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ)
    (Φ : ι₁ → NovikovSeries R G ωG) (Ψ : ι₁ → ι₀ → NovikovSeries R G ωG) (l : ι₀) :
    seriesReadout r₀ μ₀ n (seriesSew r₁ μ₁ n Φ Ψ) l =
      ∑ t, seriesReadout r₁ μ₁ n Φ t * seriesReadout r₀ μ₀ n (Ψ t) l := by
  conv_lhs =>
    rw [← seriesReadout_seriesReadout r₁ μ₁ n Φ,
      ← funext fun t => seriesReadout_seriesReadout r₀ μ₀ n (Ψ t)]
  rw [seriesSew_seriesReadout, seriesReadout_seriesReadout]

/-- **Class-indexed Koszul functional boundary** for an input piece of cochain degree `d_in`. -/
def seriesBoundary [Fintype ι₀] (d_in : ℤ) (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ)
    (B_in : ι₀ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (Ψ : ι₀ → NovikovSeries R G ωG) (l : ι₀) : NovikovSeries R G ωG :=
  B_in l - negOnePowCast R (d_in + (n - μ₀ ⟨l, r₀ l⟩)) • ∑ m, Ψ m * D₀ m l

/-- A value of `TauCeti.Floer.seriesBoundary` at an output orbit. -/
theorem seriesBoundary_apply [Fintype ι₀] (d_in : ℤ) (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ)
    (n : ℤ) (B_in : ι₀ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (Ψ : ι₀ → NovikovSeries R G ωG) (l : ι₀) :
    seriesBoundary d_in r₀ μ₀ n B_in D₀ Ψ l =
      B_in l - negOnePowCast R (d_in + (n - μ₀ ⟨l, r₀ l⟩)) • ∑ m, Ψ m * D₀ m l := (rfl)

/-- **Intertwining of `seriesBoundary` and `seriesReadout` under degree parity.** -/
theorem seriesBoundary_seriesReadout [Fintype ι₀] (d_in j : ℤ)
    (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ)
    (B_in : ι₀ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    {T : ι₀ → NovikovSeries R G ωG}
    (hT : ∀ m, T m ≠ 0 → Even (n - μ₀ ⟨m, r₀ m⟩ - (d_in + j))) (l : ι₀) :
    seriesBoundary d_in r₀ μ₀ n (seriesReadout r₀ μ₀ n B_in) D₀ (seriesReadout r₀ μ₀ n T) l =
      negOnePowCast R (j + 1) •
        seriesReadout r₀ μ₀ n (fun l => ∑ m, T m * D₀ m l - negOnePowCast R j • B_in l) l := by
  have hsum : ∑ m, seriesReadout r₀ μ₀ n T m * D₀ m l =
      negOnePowCast R (d_in + j) • ∑ m, T m * D₀ m l := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : T m = 0
    · simp [seriesReadout_apply, hm]
    · have hd : n - μ₀ ⟨m, r₀ m⟩ = (n - μ₀ ⟨m, r₀ m⟩ - (d_in + j)) + (d_in + j) := by ring
      rw [seriesReadout_apply, hd, negOnePowCast_add, negOnePowCast_even (hT m hm), one_mul,
        smul_mul_assoc]
  rw [seriesBoundary_apply, hsum, seriesReadout_apply, seriesReadout_apply]
  ext A
  simp only [coeff_sub', Pi.sub_apply, coeff_smul, smul_eq_mul, negOnePowCast_add,
    negOnePowCast_one]
  linear_combination
    (-(negOnePowCast R (n - μ₀ ⟨l, r₀ l⟩) * negOnePowCast R j *
        (∑ m, T m * D₀ m l).coeff A)) * negOnePowCast_mul_self (R := R) d_in +
    (-(negOnePowCast R (n - μ₀ ⟨l, r₀ l⟩) * (B_in l).coeff A)) *
      negOnePowCast_mul_self (R := R) j

/-- **Floer Fredholm index implies degree parity.** -/
theorem even_cochain_sub_of_index (q : G →+ PeriodGroup ω c) (d_in j : ℤ)
    (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ) {T : ι₀ → NovikovSeries R G ωG}
    (hT : ∀ m, ∀ A ∈ (T m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = n - (d_in + j))
    (m : ι₀) (hm : T m ≠ 0) :
    Even (n - μ₀ ⟨m, r₀ m⟩ - (d_in + j)) := by
  obtain ⟨A, hA⟩ := NovikovSeries.support_nonempty_iff.mpr hm
  have hd : n - μ₀ ⟨m, r₀ m⟩ - (d_in + j) = -degree ω c (q A) := by linarith [hT m A hA]
  exact hd ▸ (even_degree ω c (q A)).neg

/-- **Intertwining of `seriesBoundary` and `seriesReadout` from the Fredholm index.** -/
theorem seriesBoundary_seriesReadout_of_index [Fintype ι₀] (q : G →+ PeriodGroup ω c)
    (d_in j : ℤ) (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ)
    (B_in : ι₀ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    {T : ι₀ → NovikovSeries R G ωG}
    (hT : ∀ m, ∀ A ∈ (T m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = n - (d_in + j))
    (l : ι₀) :
    seriesBoundary d_in r₀ μ₀ n (seriesReadout r₀ μ₀ n B_in) D₀ (seriesReadout r₀ μ₀ n T) l =
      negOnePowCast R (j + 1) •
        seriesReadout r₀ μ₀ n (fun l => ∑ m, T m * D₀ m l - negOnePowCast R j • B_in l) l :=
  seriesBoundary_seriesReadout d_in j r₀ μ₀ n B_in D₀
    (even_cochain_sub_of_index q d_in j r₀ μ₀ n hT) l

/-- **Pair coevaluation sewing of two input functionals into a binary count functional**, matching
`TauCeti.NovikovModule.functionalSewPair` for a second input of cochain degree `d_in₂`. -/
def seriesSewPair {ι₂ : Type*} {P₂ : ι₂ → Type*} [Fintype ι₁] [Fintype ι₂]
    (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (μ₁ : (Σ i, P₁ i) → ℤ) (μ₂ : (Σ j, P₂ j) → ℤ)
    (d_in₂ n : ℤ) (Φ₁ : ι₁ → NovikovSeries R G ωG) (Φ₂ : ι₂ → NovikovSeries R G ωG)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (k : ι₀) : NovikovSeries R G ωG :=
  ∑ i, ∑ j, negOnePowCast R
      ((n - μ₁ ⟨i, r₁ i⟩) * (d_in₂ - (n - μ₂ ⟨j, r₂ j⟩)) +
        (n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) • (Φ₁ i * Φ₂ j * Ψ i j k)

/-- A value of `TauCeti.Floer.seriesSewPair` at an output orbit. -/
theorem seriesSewPair_apply {ι₂ : Type*} {P₂ : ι₂ → Type*} [Fintype ι₁] [Fintype ι₂]
    (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (μ₁ : (Σ i, P₁ i) → ℤ) (μ₂ : (Σ j, P₂ j) → ℤ)
    (d_in₂ n : ℤ) (Φ₁ : ι₁ → NovikovSeries R G ωG) (Φ₂ : ι₂ → NovikovSeries R G ωG)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (k : ι₀) :
    seriesSewPair r₁ r₂ μ₁ μ₂ d_in₂ n Φ₁ Φ₂ Ψ k =
      ∑ i, ∑ j, negOnePowCast R
        ((n - μ₁ ⟨i, r₁ i⟩) * (d_in₂ - (n - μ₂ ⟨j, r₂ j⟩)) +
          (n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) • (Φ₁ i * Φ₂ j * Ψ i j k) := (rfl)

/-- **Operator readout of `seriesSewPair`** when `Φ₂` has Fredholm index `0` relative to `d_in₂`. -/
theorem seriesReadout_seriesSewPair_of_index {ι₂ : Type*} {P₂ : ι₂ → Type*}
    [Fintype ι₁] [Fintype ι₂]
    (q : G →+ PeriodGroup ω c) (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
    (μ₁ : (Σ i, P₁ i) → ℤ) (μ₂ : (Σ j, P₂ j) → ℤ) (μ₀ : (Σ k, P₀ k) → ℤ) (d_in₂ n : ℤ)
    (Φ₁ : ι₁ → NovikovSeries R G ωG) {Φ₂ : ι₂ → NovikovSeries R G ωG}
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG)
    (hΦ₂ : ∀ j, ∀ A ∈ (Φ₂ j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = n - d_in₂) (k : ι₀) :
    seriesReadout r₀ μ₀ n (seriesSewPair r₁ r₂ μ₁ μ₂ d_in₂ n Φ₁ Φ₂ Ψ) k =
      ∑ i, ∑ j, seriesReadout r₁ μ₁ n Φ₁ i * seriesReadout r₂ μ₂ n Φ₂ j *
        seriesReadout r₀ μ₀ n (Ψ i j) k := by
  rw [seriesReadout_apply, seriesSewPair_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : Φ₂ j = 0
  · simp [seriesReadout_apply, hj]
  · have hev : Even (d_in₂ - (n - μ₂ ⟨j, r₂ j⟩)) := by
      convert (even_cochain_sub_of_index q d_in₂ 0 r₂ μ₂ n
        (fun m A hA => by rw [add_zero]; exact hΦ₂ m A hA) j hj).neg using 1; ring
    rw [add_assoc, negOnePowCast_add, negOnePowCast_even (hev.mul_left _), one_mul,
      seriesReadout_apply, seriesReadout_apply, seriesReadout_apply]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul, negOnePowCast_add]
    congr 1; ring

/-- **Three-end PSS sewing readout:** sewing `Φ₁`, `Φ₂` via `seriesSewPair` and the output into `Ψ₀`
via `seriesSew` reads out to `∑ᵢ ∑ⱼ Φ₁ᵢ Φ₂ⱼ ∑ₖ Qᵢⱼₖ Ψ₀ₖₗ`. -/
theorem seriesReadout_seriesSew_seriesSewPair {ι₂ κ₀ : Type*} {P₂ : ι₂ → Type*} {T₀ : κ₀ → Type*}
    [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]
    (q : G →+ PeriodGroup ω c) (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
    (s₀ : ∀ l, T₀ l) (μ₁ : (Σ i, P₁ i) → ℤ) (μ₂ : (Σ j, P₂ j) → ℤ)
    (μ₀ : (Σ k, P₀ k) → ℤ) (ν₀ : (Σ l, T₀ l) → ℤ) (d_in₂ n : ℤ)
    (Φ₁ : ι₁ → NovikovSeries R G ωG) {Φ₂ : ι₂ → NovikovSeries R G ωG}
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Ψ₀ : ι₀ → κ₀ → NovikovSeries R G ωG)
    (hΦ₂ : ∀ j, ∀ A ∈ (Φ₂ j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = n - d_in₂) (l : κ₀) :
    seriesReadout s₀ ν₀ n
        (seriesSew r₀ μ₀ n (seriesSewPair r₁ r₂ μ₁ μ₂ d_in₂ n Φ₁ Φ₂ Ψ) Ψ₀) l =
      ∑ i, ∑ j, seriesReadout r₁ μ₁ n Φ₁ i * seriesReadout r₂ μ₂ n Φ₂ j *
        ∑ k, seriesReadout r₀ μ₀ n (Ψ i j) k * seriesReadout s₀ ν₀ n (Ψ₀ k) l := by
  rw [seriesReadout_seriesSew]
  simp_rw [seriesReadout_seriesSewPair_of_index q r₁ r₂ r₀ μ₁ μ₂ μ₀ d_in₂ n Φ₁ Ψ hΦ₂,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by simp only [mul_assoc, ← Finset.mul_sum]

/-- **Chain-map equation from a closed degree-`0` count functional.** -/
theorem sum_mul_eq_of_seriesBoundary_eq_zero [Fintype ι₀]
    (q : G →+ PeriodGroup ω c) (d_in : ℤ) (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ)
    (B_in : ι₀ → NovikovSeries R G ωG)
    {Φ : ι₀ → NovikovSeries R G ωG} {D₀ : ι₀ → ι₀ → NovikovSeries R G ωG}
    (hΦ : ∀ m, ∀ A ∈ (Φ m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = n - d_in) (l : ι₀)
    (hB : seriesBoundary d_in r₀ μ₀ n (seriesReadout r₀ μ₀ n B_in) D₀ Φ l = 0) :
    ∑ m, seriesReadout r₀ μ₀ n Φ m * D₀ m l = B_in l := by
  have hb := seriesBoundary_seriesReadout_of_index q d_in 0 r₀ μ₀ n B_in D₀
    (fun m A hA => by rw [add_zero]; exact hΦ m A (support_seriesReadout_subset r₀ μ₀ n Φ m hA)) l
  simp only [seriesReadout_seriesReadout, hB, zero_add, negOnePowCast_one, negOnePowCast_zero,
    one_smul, neg_one_smul] at hb
  have hinj := congrArg (negOnePowCast R (n - μ₀ ⟨l, r₀ l⟩) • ·) (neg_eq_zero.mp hb.symm)
  rw [seriesReadout_apply, negOnePowCast_smul_negOnePowCast_smul, smul_zero] at hinj
  exact sub_eq_zero.mp hinj

/-- **Homotopy equation from a degree-`-1` functional boundary.** -/
theorem sum_mul_add_eq_of_seriesBoundary_eq_seriesReadout [Fintype ι₀]
    (q : G →+ PeriodGroup ω c) (d_in : ℤ) (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ) (n : ℤ)
    (B_in S : ι₀ → NovikovSeries R G ωG)
    {Κ : ι₀ → NovikovSeries R G ωG} {D₀ : ι₀ → ι₀ → NovikovSeries R G ωG}
    (hΚ : ∀ m, ∀ A ∈ (Κ m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = n - (d_in - 1)) (l : ι₀)
    (hB : seriesBoundary d_in r₀ μ₀ n (seriesReadout r₀ μ₀ n B_in) D₀ Κ l =
      seriesReadout r₀ μ₀ n S l) :
    ∑ m, seriesReadout r₀ μ₀ n Κ m * D₀ m l + B_in l = S l := by
  have hb := seriesBoundary_seriesReadout_of_index q d_in (-1) r₀ μ₀ n B_in D₀
    (fun m A hA => by
      rw [← sub_eq_add_neg]; exact hΚ m A (support_seriesReadout_subset r₀ μ₀ n Κ m hA)) l
  rw [seriesReadout_seriesReadout, neg_add_cancel, negOnePowCast_zero, one_smul, hB] at hb
  simpa [seriesReadout_apply, sub_neg_eq_add] using
    congrArg (negOnePowCast R (n - μ₀ ⟨l, r₀ l⟩) • ·) hb.symm

private theorem seriesReadout_sum_mul [Fintype ι₁] (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ)
    (n : ℤ) (D : ι₁ → NovikovSeries R G ωG) (Φ : ι₁ → ι₀ → NovikovSeries R G ωG) (l : ι₀) :
    seriesReadout r₀ μ₀ n (fun l => ∑ m, D m * Φ m l) l =
      ∑ m, D m * seriesReadout r₀ μ₀ n (Φ m) l := by
  simp only [seriesReadout_apply, Finset.smul_sum, mul_smul_comm]

private theorem seriesReadout_negOnePowCast_smul_apply (r₀ : ∀ l, P₀ l) (μ₀ : (Σ l, P₀ l) → ℤ)
    (n e : ℤ) (Φ : ι₀ → NovikovSeries R G ωG) (l : ι₀) :
    seriesReadout r₀ μ₀ n (fun l => negOnePowCast R e • Φ l) l =
      negOnePowCast R e • seriesReadout r₀ μ₀ n Φ l := by
  rw [seriesReadout_apply, seriesReadout_apply, smul_comm]

end SeriesSew

section CappedIdentities

variable {ι₁ ι₂ ι₃ ι₀ ι₁₂ ι₂₃ : Type*}
  [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₀] [Fintype ι₁₂] [Fintype ι₂₃]
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₃ : ι₃ → Type*}
  {P₀ : ι₀ → Type*} {P₁₂ : ι₁₂ → Type*} {P₂₃ : ι₂₃ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₃ k)] [∀ l, AddTorsor (PeriodGroup ω c) (P₀ l)]
  [∀ t, AddTorsor (PeriodGroup ω c) (P₁₂ t)] [∀ u, AddTorsor (PeriodGroup ω c) (P₂₃ u)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₃ : ∀ k, P₃ k)
  (r₀ : ∀ l, P₀ l) (r₁₂ : ∀ t, P₁₂ t) (r₂₃ : ∀ u, P₂₃ u)
  (q : G →+ PeriodGroup ω c) (hq : ∀ A, area ω c (q A) = ωG A)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₃ : (Σ k, P₃ k) → ℝ}
  {F₀ : (Σ l, P₀ l) → ℝ} {F₁₂ : (Σ t, P₁₂ t) → ℝ} {F₂₃ : (Σ u, P₂₃ u) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₃ : ∀ k γ (D : P₃ k), F₃ ⟨k, γ +ᵥ D⟩ = F₃ ⟨k, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ l γ (D : P₀ l), F₀ ⟨l, γ +ᵥ D⟩ = F₀ ⟨l, D⟩ - (-area ω c) γ)
  (hF₁₂ : ∀ t γ (D : P₁₂ t), F₁₂ ⟨t, γ +ᵥ D⟩ = F₁₂ ⟨t, D⟩ - (-area ω c) γ)
  (hF₂₃ : ∀ u γ (D : P₂₃ u), F₂₃ ⟨u, γ +ᵥ D⟩ = F₂₃ ⟨u, D⟩ - (-area ω c) γ)

/-- **The capped Leibniz rule** `d₀ (a ⋆ b) = d₁ a ⋆ b + (-1)^e a ⋆ d₂ b` from a closed
pair-of-pants count functional `Ψ`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_seriesReadout_eq_add
    {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
    {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ l, P₀ l) → ℤ} (n : ℤ)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG)
    (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hΨ : ∀ i j k, ∀ A ∈ (Ψ i j k).support,
      μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n)
    (hclosed : ∀ i j l,
      seriesBoundary ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) r₀ μ₀ n
        (fun l => ∑ m, D₁ i m * Ψ m j l +
          negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * Ψ i m l)
        D₀ (Ψ i j) l = 0)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂) :
    novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
        (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k)) a b) =
      novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k))
            b) := by
  refine novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_eq_add r₁ r₂ r₀ q hq
    hF₁ hF₂ hF₀ hμ₁ (fun i j k => seriesReadout r₀ μ₀ n (Ψ i j) k) D₁ D₂ D₀ n (fun i j l => ?_) ha b
  have h := sum_mul_eq_of_seriesBoundary_eq_zero q ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) r₀
    μ₀ n (seriesReadout r₀ μ₀ n ((fun l => ∑ m, D₁ i m * Ψ m j l) +
      fun l => negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * Ψ i m l))
    (fun m A hA => by linarith [hΨ i j m A hA]) l
    (by rw [seriesReadout_seriesReadout]; exact hclosed i j l)
  simpa only [seriesReadout_add, Pi.add_apply, seriesReadout_negOnePowCast_smul_apply,
    seriesReadout_sum_mul] using h

/-- **Left unit homotopy** `e ⋆ b - Φ b = d₀ K(b) + K(d₂ b)` from a cap-gluing count functional. -/
theorem novikovProductOfMatrix_seriesReadout_sub_novikovMapOfMatrix_right
    {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ l, P₀ l) → ℤ} (n : ℤ)
    (Ε : ι₁ → NovikovSeries R G ωG) (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG)
    (Φ_func Κ : ι₂ → ι₀ → NovikovSeries R G ωG)
    (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hΚ : ∀ j m, ∀ A ∈ (Κ j m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = μ₂ ⟨j, r₂ j⟩ + 1)
    (hB : ∀ j l,
      seriesBoundary (n - μ₂ ⟨j, r₂ j⟩) r₀ μ₀ n (fun l => ∑ m, D₂ j m * Κ m l) D₀ (Κ j) l =
        seriesSew r₁ μ₁ n Ε (fun i => Ψ i j) l - Φ_func j l)
    (b : NovikovModule R F₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k))
          ((coordinates hF₁ r₁).symm fun i =>
            coefficientComparison q hq (seriesReadout r₁ μ₁ n Ε i)) b -
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀
          (fun j l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Φ_func j) l)) b =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l))
          (novikovMapOfMatrix hF₂ hF₀ r₂ r₀
            (fun j m => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ j) m)) b) +
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀
          (fun j m => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ j) m))
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m))
            b) := by
  refine novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right r₁ r₂ r₀ q hq
    hF₁ hF₂ hF₀ (fun i j k => seriesReadout r₀ μ₀ n (Ψ i j) k) D₀ (seriesReadout r₁ μ₁ n Ε)
    (fun j l => seriesReadout r₀ μ₀ n (Φ_func j) l) (fun j m => seriesReadout r₀ μ₀ n (Κ j) m)
    D₂ (fun j l => ?_) b
  have h := (sum_mul_add_eq_of_seriesBoundary_eq_seriesReadout q (n - μ₂ ⟨j, r₂ j⟩) r₀ μ₀ n
    (seriesReadout r₀ μ₀ n fun l => ∑ m, D₂ j m * Κ m l)
    (seriesReadout r₀ μ₀ n (seriesSew r₁ μ₁ n Ε fun i => Ψ i j) -
      seriesReadout r₀ μ₀ n (Φ_func j))
    (fun m A hA => by linarith [hΚ j m A hA]) l
    (by rw [seriesReadout_seriesReadout, hB j l, seriesReadout_sub_apply,
      seriesReadout_seriesReadout, seriesReadout_seriesReadout])).symm
  simpa only [Pi.sub_apply, seriesReadout_seriesSew, seriesReadout_sum_mul] using h

/-- **Right unit homotopy** `a ⋆ e - Φ a = d₀ K(a) + K(d₁ a)` from a Koszul-braided cap-gluing
count functional. -/
theorem novikovProductOfMatrix_seriesReadout_sub_novikovMapOfMatrix_left
    {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ l, P₀ l) → ℤ} (n : ℤ)
    (Ε : ι₂ → NovikovSeries R G ωG) (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG)
    (Φ_func Κ : ι₁ → ι₀ → NovikovSeries R G ωG)
    (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hΕ : ∀ t, ∀ A ∈ (Ε t).support, μ₂ ⟨t, r₂ t⟩ - degree ω c (q A) = n)
    (hΚ : ∀ i m, ∀ A ∈ (Κ i m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + 1)
    (hB : ∀ i l,
      seriesBoundary (n - μ₁ ⟨i, r₁ i⟩) r₀ μ₀ n (fun l => ∑ m, D₁ i m * Κ m l) D₀ (Κ i) l =
        (∑ t, negOnePowCast R ((n - μ₁ ⟨i, r₁ i⟩) * (n - μ₂ ⟨t, r₂ t⟩) + (n - μ₂ ⟨t, r₂ t⟩)) •
            (Ε t * Ψ i t l)) - Φ_func i l)
    (a : NovikovModule R F₁) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k)) a
          ((coordinates hF₂ r₂).symm fun j =>
            coefficientComparison q hq (seriesReadout r₂ μ₂ n Ε j)) -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀
          (fun i l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Φ_func i) l)) a =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l))
          (novikovMapOfMatrix hF₁ hF₀ r₁ r₀
            (fun i m => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ i) m)) a) +
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀
          (fun i m => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ i) m))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m))
            a) := by
  rw [seriesReadout_eq_self_of_unit_index q r₂ μ₂ n hΕ]
  refine novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left r₁ r₂ r₀ q hq
    hF₁ hF₂ hF₀ (fun i j k => seriesReadout r₀ μ₀ n (Ψ i j) k) D₀ Ε
    (fun i l => seriesReadout r₀ μ₀ n (Φ_func i) l) (fun i m => seriesReadout r₀ μ₀ n (Κ i) m)
    D₁ (fun i l => ?_) a
  have hsew : (∑ t, negOnePowCast R
        ((n - μ₁ ⟨i, r₁ i⟩) * (n - μ₂ ⟨t, r₂ t⟩) + (n - μ₂ ⟨t, r₂ t⟩)) • (Ε t * Ψ i t l)) =
      seriesReadout r₀ μ₀ n (fun l => ∑ t, Ε t * seriesReadout r₀ μ₀ n (Ψ i t) l) l := by
    rw [seriesReadout_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : Ε t = 0
    · simp [ht]
    · have hev : Even (n - μ₂ ⟨t, r₂ t⟩) := by
        simpa using even_cochain_sub_of_index q 0 0 r₂ μ₂ n (by simpa using hΕ) t ht
      rw [negOnePowCast_even ((hev.mul_left _).add hev), one_smul, seriesReadout_apply,
        mul_smul_comm, negOnePowCast_smul_negOnePowCast_smul]
  simpa only [Pi.sub_apply, seriesReadout_sum_mul] using
    (sum_mul_add_eq_of_seriesBoundary_eq_seriesReadout q (n - μ₁ ⟨i, r₁ i⟩) r₀ μ₀ n
      (seriesReadout r₀ μ₀ n fun l => ∑ m, D₁ i m * Κ m l)
      ((fun l => ∑ t, Ε t * seriesReadout r₀ μ₀ n (Ψ i t) l) - seriesReadout r₀ μ₀ n (Φ_func i))
      (fun m A hA => by linarith [hΚ i m A hA]) l
      (by rw [seriesReadout_seriesReadout, hB i l, hsew, seriesReadout_sub_apply,
        seriesReadout_seriesReadout])).symm

/-- **Associativity homotopy** from a four-punctured-sphere count-functional boundary. -/
theorem novikovProductOfMatrix_seriesReadout_assoc_sub_eq_add
    {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
    {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    {μ₃ : (Σ k, P₃ k) → ℤ} {μ₀ : (Σ l, P₀ l) → ℤ}
    {μ₁₂ : (Σ t, P₁₂ t) → ℤ} {μ₂₃ : (Σ u, P₂₃ u) → ℤ} (n : ℤ)
    (Ψ : ι₁ → ι₂ → ι₁₂ → NovikovSeries R G ωG) (Ψ' : ι₁₂ → ι₃ → ι₀ → NovikovSeries R G ωG)
    (Θ : ι₂ → ι₃ → ι₂₃ → NovikovSeries R G ωG) (Θ' : ι₁ → ι₂₃ → ι₀ → NovikovSeries R G ωG)
    (Κ : ι₁ → ι₂ → ι₃ → ι₀ → NovikovSeries R G ωG)
    (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
    (D₃ : ι₃ → ι₃ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hΘ : ∀ j k u, ∀ A ∈ (Θ j k u).support,
      μ₂₃ ⟨u, r₂₃ u⟩ - degree ω c (q A) = μ₂ ⟨j, r₂ j⟩ + μ₃ ⟨k, r₃ k⟩ - n)
    (hΚ : ∀ i j k m, ∀ A ∈ (Κ i j k m).support,
      μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ + μ₃ ⟨k, r₃ k⟩ - 2 * n + 1)
    (hB : ∀ i j k l,
      seriesBoundary ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩) + (n - μ₃ ⟨k, r₃ k⟩)) r₀ μ₀ n
        (fun l => ∑ m, D₁ i m * Κ m j k l +
          negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * Κ i m k l +
          negOnePowCast R ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) • ∑ m, D₃ k m * Κ i j m l)
        D₀ (Κ i j k) l =
      seriesSew r₁₂ μ₁₂ n (Ψ i j) (fun t => Ψ' t k) l -
        ∑ u, negOnePowCast R
            ((n - μ₁ ⟨i, r₁ i⟩) * ((n - μ₂ ⟨j, r₂ j⟩) + (n - μ₃ ⟨k, r₃ k⟩) - (n - μ₂₃ ⟨u, r₂₃ u⟩)) +
              (n - μ₂₃ ⟨u, r₂₃ u⟩)) • (Θ j k u * Θ' i u l))
    {e₁ e₂ : ℤ} {x₁ : NovikovModule R F₁} (ha : x₁ ∈ gradeBy R F₁ (fun p => n - μ₁ p) e₁)
    {x₂ : NovikovModule R F₂} (hb : x₂ ∈ gradeBy R F₂ (fun p => n - μ₂ p) e₂)
    (x₃ : NovikovModule R F₃) :
    novikovProductOfMatrix hF₁₂ hF₃ hF₀ r₁₂ r₃ r₀
          (fun t k l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ' t k) l))
          (novikovProductOfMatrix hF₁ hF₂ hF₁₂ r₁ r₂ r₁₂
            (fun i j t => coefficientComparison q hq (seriesReadout r₁₂ μ₁₂ n (Ψ i j) t)) x₁ x₂)
          x₃ -
        novikovProductOfMatrix hF₁ hF₂₃ hF₀ r₁ r₂₃ r₀
          (fun i u l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Θ' i u) l)) x₁
          (novikovProductOfMatrix hF₂ hF₃ hF₂₃ r₂ r₃ r₂₃
            (fun j k u => coefficientComparison q hq (seriesReadout r₂₃ μ₂₃ n (Θ j k) u)) x₂ x₃) =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l))
          (novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
            (fun i j k l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ i j k) l))
            x₁ x₂ x₃) +
        novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
          (fun i j k l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ i j k) l))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m)) x₁)
          x₂ x₃ +
        negOnePowCast R e₁ • novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
          (fun i j k l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ i j k) l)) x₁
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m)) x₂)
          x₃ +
        negOnePowCast R (e₁ + e₂) • novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
          (fun i j k l => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Κ i j k) l)) x₁ x₂
          (novikovMapOfMatrix hF₃ hF₃ r₃ r₃ (fun k m => coefficientComparison q hq (D₃ k m))
            x₃) := by
  refine novikovProductOfMatrix_coefficientComparison_assoc_sub_eq_add r₁ r₂ r₀ q hq r₃ r₁₂ r₂₃
    hF₁ hF₂ hF₃ hF₀ hμ₁ hμ₂ hF₁₂ hF₂₃ (fun i j t => seriesReadout r₁₂ μ₁₂ n (Ψ i j) t)
    (fun t k l => seriesReadout r₀ μ₀ n (Ψ' t k) l)
    (fun j k u => seriesReadout r₂₃ μ₂₃ n (Θ j k) u)
    (fun i u l => seriesReadout r₀ μ₀ n (Θ' i u) l)
    (fun i j k l => seriesReadout r₀ μ₀ n (Κ i j k) l) D₁ D₂ D₃ D₀ n (fun i j k l => ?_) ha hb x₃
  have hL : seriesSew r₁₂ μ₁₂ n (Ψ i j) (fun t => Ψ' t k) l =
      seriesReadout r₀ μ₀ n (fun l =>
        ∑ t, seriesReadout r₁₂ μ₁₂ n (Ψ i j) t * seriesReadout r₀ μ₀ n (Ψ' t k) l) l := by
    rw [← seriesSew_seriesReadout, seriesReadout_seriesReadout]
    congr 1; funext t; exact (seriesReadout_seriesReadout r₀ μ₀ n (Ψ' t k)).symm
  have hR : (∑ u, negOnePowCast R
        ((n - μ₁ ⟨i, r₁ i⟩) * ((n - μ₂ ⟨j, r₂ j⟩) + (n - μ₃ ⟨k, r₃ k⟩) - (n - μ₂₃ ⟨u, r₂₃ u⟩)) +
          (n - μ₂₃ ⟨u, r₂₃ u⟩)) • (Θ j k u * Θ' i u l)) =
      seriesReadout r₀ μ₀ n (fun l =>
        ∑ u, seriesReadout r₂₃ μ₂₃ n (Θ j k) u * seriesReadout r₀ μ₀ n (Θ' i u) l) l := by
    rw [seriesReadout_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : Θ j k u = 0
    · simp [seriesReadout_apply, hu]
    · have hev : Even ((n - μ₂ ⟨j, r₂ j⟩) + (n - μ₃ ⟨k, r₃ k⟩) - (n - μ₂₃ ⟨u, r₂₃ u⟩)) := by
        convert (even_cochain_sub_of_index q ((n - μ₂ ⟨j, r₂ j⟩) + (n - μ₃ ⟨k, r₃ k⟩)) 0 r₂₃ μ₂₃ n
          (fun m A hA => by linarith [hΘ j k m A hA]) u hu).neg using 1; ring
      rw [negOnePowCast_add, negOnePowCast_even (hev.mul_left _), one_mul, seriesReadout_apply,
        seriesReadout_apply, smul_mul_assoc, mul_smul_comm,
        smul_comm (negOnePowCast R (n - μ₀ ⟨l, r₀ l⟩)) (negOnePowCast R (n - μ₂₃ ⟨u, r₂₃ u⟩)),
        negOnePowCast_smul_negOnePowCast_smul]
  have h := (sum_mul_add_eq_of_seriesBoundary_eq_seriesReadout q
    ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩) + (n - μ₃ ⟨k, r₃ k⟩)) r₀ μ₀ n
    (seriesReadout r₀ μ₀ n fun l => ∑ m, D₁ i m * Κ m j k l +
      negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * Κ i m k l +
      negOnePowCast R ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) • ∑ m, D₃ k m * Κ i j m l)
    ((fun l => ∑ t, seriesReadout r₁₂ μ₁₂ n (Ψ i j) t * seriesReadout r₀ μ₀ n (Ψ' t k) l) -
      fun l => ∑ u, seriesReadout r₂₃ μ₂₃ n (Θ j k) u * seriesReadout r₀ μ₀ n (Θ' i u) l)
    (fun m A hA => by linarith [hΚ i j k m A hA]) l
    (by rw [seriesReadout_seriesReadout, hB i j k l, hL, hR, seriesReadout_sub_apply])).symm
  -- Rewrite the pointwise sum inside the lambda as function addition so `seriesReadout_add`
  -- distributes across the three input-breaking summands.
  have hadd : (fun l => ∑ m, D₁ i m * Κ m j k l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * Κ i m k l +
        negOnePowCast R ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) • ∑ m, D₃ k m * Κ i j m l) =
      ((fun l => ∑ m, D₁ i m * Κ m j k l) +
        fun l => negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * Κ i m k l) +
        fun l => negOnePowCast R ((n - μ₁ ⟨i, r₁ i⟩) + (n - μ₂ ⟨j, r₂ j⟩)) •
          ∑ m, D₃ k m * Κ i j m l := rfl
  rw [hadd] at h
  simp only [Pi.sub_apply, seriesReadout_add, Pi.add_apply,
    seriesReadout_negOnePowCast_smul_apply, seriesReadout_sum_mul] at h
  exact h.trans (by abel)

end CappedIdentities

section Comparison

variable {ι₁ ι₂ ι₀ κ₁ κ₂ κ₀ : Type*}
  [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] [Fintype κ₁] [Fintype κ₂] [Fintype κ₀]
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  {T₁ : κ₁ → Type*} {T₂ : κ₂ → Type*} {T₀ : κ₀ → Type*}

private theorem comparison_readout_eq
    (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
    (s₂ : ∀ t, T₂ t) (s₀ : ∀ l, T₀ l) (q : G →+ PeriodGroup ω c)
    {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
    {ν₁ : (Σ s, T₁ s) → ℤ} (s₁ : ∀ s, T₁ s)
    {ν₂ : (Σ t, T₂ t) → ℤ} {ν₀ : (Σ l, T₀ l) → ℤ} (n : ℤ)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Μ : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (Φ₁ : κ₁ → ι₁ → NovikovSeries R G ωG) (Φ₂ : κ₂ → ι₂ → NovikovSeries R G ωG)
    (Ψ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (Κ : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (E₁ : κ₁ → κ₁ → NovikovSeries R G ωG) (E₂ : κ₂ → κ₂ → NovikovSeries R G ωG)
    (E₀ : κ₀ → κ₀ → NovikovSeries R G ωG)
    (hΦ₂ : ∀ t j, ∀ A ∈ (Φ₂ t j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = ν₂ ⟨t, s₂ t⟩)
    (hΚ : ∀ s t m, ∀ A ∈ (Κ s t m).support,
      ν₀ ⟨m, s₀ m⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩ + ν₂ ⟨t, s₂ t⟩ - n + 1)
    (hB : ∀ s t l,
      seriesBoundary ((n - ν₁ ⟨s, s₁ s⟩) + (n - ν₂ ⟨t, s₂ t⟩)) s₀ ν₀ n
        (fun l => ∑ m, E₁ s m * Κ m t l +
          negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * Κ s m l)
        E₀ (Κ s t) l =
      seriesSew r₀ μ₀ n
        (seriesSewPair r₁ r₂ μ₁ μ₂ (n - ν₂ ⟨t, s₂ t⟩) n (Φ₁ s) (Φ₂ t) Ψ) Ψ₀ l - Μ s t l)
    (s : κ₁) (t : κ₂) (l : κ₀) :
    ∑ i, ∑ j, seriesReadout r₁ μ₁ n (Φ₁ s) i * seriesReadout r₂ μ₂ n (Φ₂ t) j *
          ∑ k, seriesReadout r₀ μ₀ n (Ψ i j) k * seriesReadout s₀ ν₀ n (Ψ₀ k) l -
        seriesReadout s₀ ν₀ n (Μ s t) l =
      ∑ m, seriesReadout s₀ ν₀ n (Κ s t) m * E₀ m l +
        ∑ m, E₁ s m * seriesReadout s₀ ν₀ n (Κ m t) l +
        negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * seriesReadout s₀ ν₀ n (Κ s m) l := by
  set sew := seriesSew r₀ μ₀ n (seriesSewPair r₁ r₂ μ₁ μ₂ (n - ν₂ ⟨t, s₂ t⟩) n (Φ₁ s) (Φ₂ t) Ψ) Ψ₀
  have h := (sum_mul_add_eq_of_seriesBoundary_eq_seriesReadout q
    ((n - ν₁ ⟨s, s₁ s⟩) + (n - ν₂ ⟨t, s₂ t⟩)) s₀ ν₀ n
    (seriesReadout s₀ ν₀ n fun l => ∑ m, E₁ s m * Κ m t l +
      negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * Κ s m l)
    (seriesReadout s₀ ν₀ n sew - seriesReadout s₀ ν₀ n (Μ s t))
    (fun m A hA => by linarith [hΚ s t m A hA]) l
    (by rw [seriesReadout_seriesReadout, hB s t l, seriesReadout_sub_apply,
      seriesReadout_seriesReadout, seriesReadout_seriesReadout])).symm
  -- Rewrite the pointwise sum inside the lambda as function addition so `seriesReadout_add`
  -- distributes across the two input-breaking summands.
  have hadd : (fun l => ∑ m, E₁ s m * Κ m t l +
        negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * Κ s m l) =
      (fun l => ∑ m, E₁ s m * Κ m t l) +
        fun l => negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * Κ s m l := rfl
  rw [hadd, Pi.sub_apply, seriesReadout_seriesSew_seriesSewPair q r₁ r₂ r₀ s₀ μ₁ μ₂ μ₀ ν₀
    (n - ν₂ ⟨t, s₂ t⟩) n (Φ₁ s) Ψ Ψ₀ (fun j A hA => by linarith [hΦ₂ t j A hA]) l] at h
  simp only [seriesReadout_add, Pi.add_apply, seriesReadout_negOnePowCast_smul_apply,
    seriesReadout_sum_mul] at h
  exact h.trans (by abel)

variable [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)] [∀ s, AddTorsor (PeriodGroup ω c) (T₁ s)]
  [∀ t, AddTorsor (PeriodGroup ω c) (T₂ t)] [∀ l, AddTorsor (PeriodGroup ω c) (T₀ l)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  (s₁ : ∀ s, T₁ s) (s₂ : ∀ t, T₂ t) (s₀ : ∀ l, T₀ l)
  (q : G →+ PeriodGroup ω c) (hq : ∀ A, area ω c (q A) = ωG A)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {G₁ : (Σ s, T₁ s) → ℝ} {G₂ : (Σ t, T₂ t) → ℝ} {G₀ : (Σ l, T₀ l) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hG₁ : ∀ s γ (D : T₁ s), G₁ ⟨s, γ +ᵥ D⟩ = G₁ ⟨s, D⟩ - (-area ω c) γ)
  (hG₂ : ∀ t γ (D : T₂ t), G₂ ⟨t, γ +ᵥ D⟩ = G₂ ⟨t, D⟩ - (-area ω c) γ)
  (hG₀ : ∀ l γ (D : T₀ l), G₀ ⟨l, γ +ᵥ D⟩ = G₀ ⟨l, D⟩ - (-area ω c) γ)

/-- **Comparison of readout products through the inverse PSS functional**
`Ψ₀ (Φ₁ a ⋆ Φ₂ b) - a ⋆_M b = E₀ K(a, b) + K(E₁ a, b) + (-1)^e K(a, E₂ b)`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_seriesReadout_sub_novikovProductOfMatrix
    {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
    {ν₁ : (Σ s, T₁ s) → ℤ} (hν₁ : ∀ s γ (D : T₁ s), ν₁ ⟨s, γ +ᵥ D⟩ = degree ω c γ + ν₁ ⟨s, D⟩)
    {ν₂ : (Σ t, T₂ t) → ℤ} {ν₀ : (Σ l, T₀ l) → ℤ} (n : ℤ)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Μ : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (Φ₁ : κ₁ → ι₁ → NovikovSeries R G ωG) (Φ₂ : κ₂ → ι₂ → NovikovSeries R G ωG)
    (Ψ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (Κ : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (E₁ : κ₁ → κ₁ → NovikovSeries R G ωG) (E₂ : κ₂ → κ₂ → NovikovSeries R G ωG)
    (E₀ : κ₀ → κ₀ → NovikovSeries R G ωG)
    (hΦ₂ : ∀ t j, ∀ A ∈ (Φ₂ t j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = ν₂ ⟨t, s₂ t⟩)
    (hΚ : ∀ s t m, ∀ A ∈ (Κ s t m).support,
      ν₀ ⟨m, s₀ m⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩ + ν₂ ⟨t, s₂ t⟩ - n + 1)
    (hB : ∀ s t l,
      seriesBoundary ((n - ν₁ ⟨s, s₁ s⟩) + (n - ν₂ ⟨t, s₂ t⟩)) s₀ ν₀ n
        (fun l => ∑ m, E₁ s m * Κ m t l +
          negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * Κ s m l)
        E₀ (Κ s t) l =
      seriesSew r₀ μ₀ n
        (seriesSewPair r₁ r₂ μ₁ μ₂ (n - ν₂ ⟨t, s₂ t⟩) n (Φ₁ s) (Φ₂ t) Ψ) Ψ₀ l - Μ s t l)
    {e : ℤ} {a : NovikovModule R G₁} (ha : a ∈ gradeBy R G₁ (fun p => n - ν₁ p) e)
    (b : NovikovModule R G₂) :
    novikovMapOfMatrix hF₀ hG₀ r₀ s₀
          (fun k l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Ψ₀ k) l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k))
            (novikovMapOfMatrix hG₁ hF₁ s₁ r₁
              (fun s i => coefficientComparison q hq (seriesReadout r₁ μ₁ n (Φ₁ s) i)) a)
            (novikovMapOfMatrix hG₂ hF₂ s₂ r₂
              (fun t j => coefficientComparison q hq (seriesReadout r₂ μ₂ n (Φ₂ t) j)) b)) -
        novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
          (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Μ s t) l)) a b =
      novikovMapOfMatrix hG₀ hG₀ s₀ s₀ (fun l m => coefficientComparison q hq (E₀ l m))
          (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
            (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Κ s t) l)) a b) +
        novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
          (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Κ s t) l))
          (novikovMapOfMatrix hG₁ hG₁ s₁ s₁ (fun s m => coefficientComparison q hq (E₁ s m)) a)
          b +
        negOnePowCast R e • novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
          (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Κ s t) l)) a
          (novikovMapOfMatrix hG₂ hG₂ s₂ s₂ (fun t m => coefficientComparison q hq (E₂ t m))
            b) :=
  novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_novikovProductOfMatrix
    r₁ r₂ r₀ s₁ s₂ s₀ q hq hF₁ hF₂ hF₀ hG₁ hG₂ hG₀ hν₁
    (fun i j k => seriesReadout r₀ μ₀ n (Ψ i j) k) (fun s t l => seriesReadout s₀ ν₀ n (Μ s t) l)
    (fun s i => seriesReadout r₁ μ₁ n (Φ₁ s) i) (fun t j => seriesReadout r₂ μ₂ n (Φ₂ t) j)
    (fun k l => seriesReadout s₀ ν₀ n (Ψ₀ k) l) (fun s t l => seriesReadout s₀ ν₀ n (Κ s t) l)
    E₁ E₂ E₀ n (comparison_readout_eq r₁ r₂ r₀ s₂ s₀ q s₁ n Ψ Μ Φ₁ Φ₂ Ψ₀ Κ E₁ E₂ E₀ hΦ₂ hΚ hB)
    ha b

/-- **Multiplicative PSS comparison from sewn count functionals** between `Φ₁ a ⋆ Φ₂ b` and
`Φ₀ (a ⋆_M b)`. -/
theorem novikovProductOfMatrix_seriesReadout_sub_novikovMapOfMatrix_novikovProductOfMatrix
    [DecidableEq ι₀]
    {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
    {ν₁ : (Σ s, T₁ s) → ℤ} (hν₁ : ∀ s γ (D : T₁ s), ν₁ ⟨s, γ +ᵥ D⟩ = degree ω c γ + ν₁ ⟨s, D⟩)
    {ν₂ : (Σ t, T₂ t) → ℤ} {ν₀ : (Σ l, T₀ l) → ℤ} (n : ℤ)
    (Ψ : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Μ : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (Φ₁ : κ₁ → ι₁ → NovikovSeries R G ωG) (Φ₂ : κ₂ → ι₂ → NovikovSeries R G ωG)
    (Ψ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (Φ₀ : κ₀ → ι₀ → NovikovSeries R G ωG)
    (Κ : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (E₁ : κ₁ → κ₁ → NovikovSeries R G ωG) (E₂ : κ₂ → κ₂ → NovikovSeries R G ωG)
    (E₀ : κ₀ → κ₀ → NovikovSeries R G ωG) (D₀ Υ₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hΦ₂ : ∀ t j, ∀ A ∈ (Φ₂ t j).support, μ₂ ⟨j, r₂ j⟩ - degree ω c (q A) = ν₂ ⟨t, s₂ t⟩)
    (hΦ₀_idx : ∀ l m, ∀ A ∈ (Φ₀ l m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = ν₀ ⟨l, s₀ l⟩)
    (hΚ : ∀ s t m, ∀ A ∈ (Κ s t m).support,
      ν₀ ⟨m, s₀ m⟩ - degree ω c (q A) = ν₁ ⟨s, s₁ s⟩ + ν₂ ⟨t, s₂ t⟩ - n + 1)
    (hΥ₀_idx : ∀ k m, ∀ A ∈ (Υ₀ k m).support, μ₀ ⟨m, r₀ m⟩ - degree ω c (q A) = μ₀ ⟨k, r₀ k⟩ + 1)
    (hB : ∀ s t l,
      seriesBoundary ((n - ν₁ ⟨s, s₁ s⟩) + (n - ν₂ ⟨t, s₂ t⟩)) s₀ ν₀ n
        (fun l => ∑ m, E₁ s m * Κ m t l +
          negOnePowCast R (n - ν₁ ⟨s, s₁ s⟩) • ∑ m, E₂ t m * Κ s m l)
        E₀ (Κ s t) l =
      seriesSew r₀ μ₀ n
        (seriesSewPair r₁ r₂ μ₁ μ₂ (n - ν₂ ⟨t, s₂ t⟩) n (Φ₁ s) (Φ₂ t) Ψ) Ψ₀ l - Μ s t l)
    (hΦ₀_closed : ∀ l k,
      seriesBoundary (n - ν₀ ⟨l, s₀ l⟩) r₀ μ₀ n (fun k => ∑ m, E₀ l m * Φ₀ m k) D₀ (Φ₀ l) k = 0)
    (hΥ₀_B : ∀ k k',
      seriesBoundary (n - μ₀ ⟨k, r₀ k⟩) r₀ μ₀ n
        (fun k' => ∑ m, D₀ k m * Υ₀ m k') D₀ (Υ₀ k) k' =
      seriesSew s₀ ν₀ n (Ψ₀ k) Φ₀ k' - seriesEval r₀ μ₀ n k k')
    {e : ℤ} {a : NovikovModule R G₁} (ha : a ∈ gradeBy R G₁ (fun p => n - ν₁ p) e)
    (b : NovikovModule R G₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k))
          (novikovMapOfMatrix hG₁ hF₁ s₁ r₁
            (fun s i => coefficientComparison q hq (seriesReadout r₁ μ₁ n (Φ₁ s) i)) a)
          (novikovMapOfMatrix hG₂ hF₂ s₂ r₂
            (fun t j => coefficientComparison q hq (seriesReadout r₂ μ₂ n (Φ₂ t) j)) b) -
        novikovMapOfMatrix hG₀ hF₀ s₀ r₀
          (fun l k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Φ₀ l) k))
          (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
            (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Μ s t) l)) a b) =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k'))
          (novikovMapOfMatrix hG₀ hF₀ s₀ r₀
              (fun l k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Φ₀ l) k))
              (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
                (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Κ s t) l)) a b) -
            novikovMapOfMatrix hF₀ hF₀ r₀ r₀
              (fun k k' => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Υ₀ k) k'))
              (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
                (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k))
                (novikovMapOfMatrix hG₁ hF₁ s₁ r₁
                  (fun s i => coefficientComparison q hq (seriesReadout r₁ μ₁ n (Φ₁ s) i)) a)
                (novikovMapOfMatrix hG₂ hF₂ s₂ r₂
                  (fun t j => coefficientComparison q hq (seriesReadout r₂ μ₂ n (Φ₂ t) j)) b))) +
        (novikovMapOfMatrix hG₀ hF₀ s₀ r₀
            (fun l k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Φ₀ l) k))
            (novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
                (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Κ s t) l))
                (novikovMapOfMatrix hG₁ hG₁ s₁ s₁
                  (fun s m => coefficientComparison q hq (E₁ s m)) a) b +
              negOnePowCast R e • novikovProductOfMatrix hG₁ hG₂ hG₀ s₁ s₂ s₀
                (fun s t l => coefficientComparison q hq (seriesReadout s₀ ν₀ n (Κ s t) l)) a
                (novikovMapOfMatrix hG₂ hG₂ s₂ s₂
                  (fun t m => coefficientComparison q hq (E₂ t m)) b)) -
          novikovMapOfMatrix hF₀ hF₀ r₀ r₀
            (fun k k' => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Υ₀ k) k'))
            (novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k k' => coefficientComparison q hq (D₀ k k'))
              (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
                (fun i j k => coefficientComparison q hq (seriesReadout r₀ μ₀ n (Ψ i j) k))
                (novikovMapOfMatrix hG₁ hF₁ s₁ r₁
                  (fun s i => coefficientComparison q hq (seriesReadout r₁ μ₁ n (Φ₁ s) i)) a)
                (novikovMapOfMatrix hG₂ hF₂ s₂ r₂
                  (fun t j => coefficientComparison q hq (seriesReadout r₂ μ₂ n (Φ₂ t) j))
                  b)))) := by
  refine novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_novikovProductOfMatrix
    r₁ r₂ r₀ s₁ s₂ s₀ q hq hF₁ hF₂ hF₀ hG₁ hG₂ hG₀ hν₁
    (fun i j k => seriesReadout r₀ μ₀ n (Ψ i j) k) (fun s t l => seriesReadout s₀ ν₀ n (Μ s t) l)
    (fun s i => seriesReadout r₁ μ₁ n (Φ₁ s) i) (fun t j => seriesReadout r₂ μ₂ n (Φ₂ t) j)
    (fun k l => seriesReadout s₀ ν₀ n (Ψ₀ k) l) (fun s t l => seriesReadout s₀ ν₀ n (Κ s t) l)
    E₁ E₂ E₀ n (fun l k => seriesReadout r₀ μ₀ n (Φ₀ l) k) D₀
    (fun k k' => seriesReadout r₀ μ₀ n (Υ₀ k) k')
    (comparison_readout_eq r₁ r₂ r₀ s₂ s₀ q s₁ n Ψ Μ Φ₁ Φ₂ Ψ₀ Κ E₁ E₂ E₀ hΦ₂ hΚ hB)
    (fun l k => ?_) (fun k k' => ?_) ha b
  · simpa only [seriesReadout_sum_mul] using
      (sum_mul_eq_of_seriesBoundary_eq_zero q (n - ν₀ ⟨l, s₀ l⟩) r₀ μ₀ n
        (seriesReadout r₀ μ₀ n fun k => ∑ m, E₀ l m * Φ₀ m k)
        (fun m A hA => by linarith [hΦ₀_idx l m A hA]) k
        (by rw [seriesReadout_seriesReadout, hΦ₀_closed l k])).symm
  · have h := (sum_mul_add_eq_of_seriesBoundary_eq_seriesReadout q (n - μ₀ ⟨k, r₀ k⟩) r₀ μ₀ n
      (seriesReadout r₀ μ₀ n fun k' => ∑ m, D₀ k m * Υ₀ m k')
      (seriesReadout r₀ μ₀ n (seriesSew s₀ ν₀ n (Ψ₀ k) Φ₀) -
        seriesReadout r₀ μ₀ n (seriesEval r₀ μ₀ n k))
      (fun m A hA => by linarith [hΥ₀_idx k m A hA]) k'
      (by rw [seriesReadout_seriesReadout, hΥ₀_B k k', seriesReadout_sub_apply,
        seriesReadout_seriesReadout, seriesReadout_seriesReadout])).symm
    simpa only [Pi.sub_apply, seriesReadout_seriesSew, seriesReadout_seriesEval,
      seriesReadout_sum_mul] using h

end Comparison

section ClassicalSignCheck

/-- **Non-vacuous classical odd-degree sign check on a trivial period group.** For two degree-`1`
input generators (`n = 2`, `μ = 1`) and a degree-`2` output generator (`n = 2`, `μ = 0`), any count
functional `Ψ` with `Ψ 1 0 () = -Ψ 0 1 ()` reads out to `e₀ ⋆ e₁ = -(e₁ ⋆ e₀)` with
`(e₀ ⋆ e₁)(r₀ ()) = ∑_A (Ψ 0 1 ()).coeff A`. -/
theorem novikovProductOfMatrix_seriesReadout_skew_of_subsingleton
    [Subsingleton (PeriodGroup ω c)] (q : G →+ PeriodGroup ω c)
    (hq : ∀ A, area ω c (q A) = ωG A) {P₁ : Fin 2 → Type*} {P₀ : Unit → Type*}
    [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
    (r₁ : ∀ i, P₁ i) (r₀ : ∀ k, P₀ k) {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
    (Ψ : Fin 2 → Fin 2 → Unit → NovikovSeries R G ωG) (hskew : Ψ 1 0 () = -Ψ 0 1 ())
    (e₀ e₁ : NovikovModule R F₁)
    (he₀ : e₀.val ⟨0, r₁ 0⟩ = 1 ∧ e₀.val ⟨1, r₁ 1⟩ = 0)
    (he₁ : e₁.val ⟨0, r₁ 0⟩ = 0 ∧ e₁.val ⟨1, r₁ 1⟩ = 1) :
    let prod := novikovProductOfMatrix hF₁ hF₁ hF₀ r₁ r₁ r₀
      (fun i j k => coefficientComparison q hq (seriesReadout r₀ (fun _ => 0) 2 (Ψ i j) k))
    (prod e₀ e₁).val ⟨(), r₀ ()⟩ = ∑ᶠ A, (Ψ 0 1 ()).coeff A ∧ prod e₀ e₁ = -prod e₁ e₀ := by
  intro prod
  have hread : ∀ i j, seriesReadout r₀ (fun _ => 0) 2 (Ψ i j) () = Ψ i j () := fun i j => by
    rw [seriesReadout_apply, sub_zero, negOnePowCast_even (⟨1, rfl⟩ : Even (2 : ℤ)), one_smul]
  have h01 : ∀ D₀ : P₀ (), (prod e₀ e₁).val ⟨(), D₀⟩ = ∑ᶠ A, (Ψ 0 1 ()).coeff A := fun D₀ => by
    rw [novikovProductOfMatrix_coefficientComparison_apply_val_of_subsingleton q hq r₁ r₁ r₀
      hF₁ hF₁ hF₀ _ e₀ e₁ D₀]
    simp [Fin.sum_univ_two, hread, he₀.left, he₀.right, he₁.left, he₁.right]
  refine ⟨h01 (r₀ ()), Subtype.ext (funext fun ⟨k, D₀⟩ => ?_)⟩
  cases k
  rw [Submodule.coe_neg, Pi.neg_apply, h01 D₀,
    novikovProductOfMatrix_coefficientComparison_apply_val_of_subsingleton q hq r₁ r₁ r₀
      hF₁ hF₁ hF₀ _ e₁ e₀ D₀]
  simp [Fin.sum_univ_two, hread, hskew, he₀.left, he₀.right, he₁.left, he₁.right,
    finsum_neg_distrib]

end ClassicalSignCheck

end TauCeti.Floer
