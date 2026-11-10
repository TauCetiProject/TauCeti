/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Product
public import TauCeti.RingTheory.NovikovModule.Continuation

/-!
# Continuation maps and the capped product of class-indexed counts

Let `⋆` and `⋆'` be the capped pair-of-pants products of class-indexed counts
(`TauCeti.Geometry.Symplectic.Floer.Cap.Product`) for two choices of end Hamiltonians: the first
on capped generators of finitely many orbits `i`, `j`, `k` with reference caps `r₁`, `r₂`, `r₀`,
the second on capped generators of finitely many orbits with reference caps `s₁`, `s₂`, `s₀`. All
capped generators are torsors under the same period group `Γ = PeriodGroup ω c`, and all counts
are indexed by a common class group `G` mapping to `Γ` by an area-preserving homomorphism `q`.
The continuation maps between the two choices on each end are counted in the same way, by the
generating series `Φ₁`, `Φ₂`, `Φ₀` of rigid continuation cylinders between reference capped
orbits; their comparisons `q^A ↦ e^(-q A)` are the matrices of the continuation maps on the
completed capped modules (`TauCeti.NovikovModule.novikovMapOfMatrix`).

Gluing continuation cylinders to the ends of a pair of pants gives a one-parameter family of
pairs of pants whose perturbation data interpolate between the two choices of end Hamiltonians
(`TauCeti.Floer.pairOfPantsContinuationPerturbation`). Let `K` be the generating series of its
rigid members and `D₁`, `D₂`, `E₀` those of rigid Floer cylinders of the inputs of `⋆` and of the
output of `⋆'`. The ends of the one-dimensional moduli spaces of the family are the two broken
configurations, a pair of pants followed by a continuation cylinder at the output or preceded by
continuation cylinders at both inputs, together with breakings of Floer cylinders at the three
ends. Counting them class by class gives the identity

`∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ₖ ∑ₘ Φ₁ᵢₖ Φ₂ⱼₘ Q'ₖₘₗ =`
`  ∑ₖ Kᵢⱼₖ E₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series. This file shows:

* **The continuation homotopy.** The identity gives the chain homotopy
  `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = E₀ K(a, b) + K(D₁ a, b) + (-1)^e K(a, D₂ b)` on the completed capped
  modules, for `a` of cochain degree `e`
  (`novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_coefficientComparison`).
* **Continuation maps are multiplicative up to coboundaries.** If the classes counted by `K`
  satisfy the index condition of rigid members of the family, whose Fredholm index at a fixed
  parameter is `-1`, then `K` lowers the cochain degree by one, and for cocycles `a` and `b` the
  difference `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b` is the coboundary of `K(a, b)`
  (`novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_mem_coboundaries`).

The count identity, the energy bounds and the index conditions are the input that the geometric
moduli spaces are to supply; no moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  compatibility of the pair-of-pants product with continuation maps.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [CommRing R] [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {ι₁ ι₂ ι₀ κ₁ κ₂ κ₀ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] [Fintype κ₁] [Fintype κ₂]
  [Fintype κ₀] {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*} {T₁ : κ₁ → Type*}
  {T₂ : κ₂ → Type*} {T₀ : κ₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)] [∀ i, AddTorsor (PeriodGroup ω c) (T₁ i)]
  [∀ j, AddTorsor (PeriodGroup ω c) (T₂ j)] [∀ k, AddTorsor (PeriodGroup ω c) (T₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  (s₁ : ∀ i, T₁ i) (s₂ : ∀ j, T₂ j) (s₀ : ∀ k, T₀ k)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {F₁' : (Σ i, T₁ i) → ℝ} {F₂' : (Σ j, T₂ j) → ℝ} {F₀' : (Σ k, T₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hF₁' : ∀ i γ (D : T₁ i), F₁' ⟨i, γ +ᵥ D⟩ = F₁' ⟨i, D⟩ - (-area ω c) γ)
  (hF₂' : ∀ j γ (D : T₂ j), F₂' ⟨j, γ +ᵥ D⟩ = F₂' ⟨j, D⟩ - (-area ω c) γ)
  (hF₀' : ∀ k γ (D : T₀ k), F₀' ⟨k, γ +ᵥ D⟩ = F₀' ⟨k, D⟩ - (-area ω c) γ)
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Q' : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (Φ₁ : ι₁ → κ₁ → NovikovSeries R G ωG) (Φ₂ : ι₂ → κ₂ → NovikovSeries R G ωG)
  (Φ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (K : ι₁ → ι₂ → κ₀ → NovikovSeries R G ωG)
  (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
  (E₀ : κ₀ → κ₀ → NovikovSeries R G ωG) (n : ℤ)

include hμ₁ in
/-- **The continuation homotopy for class-indexed counts.** Let `Q` and `Q'` be the generating
series of rigid pairs of pants for two choices of end Hamiltonians, `Φ₁`, `Φ₂`, `Φ₀` those of
rigid continuation cylinders from the first choice to the second on the two inputs and the
output, `K` those of the rigid members of the family of pairs of pants with continuation necks,
and `D₁`, `D₂`, `E₀` those of rigid Floer cylinders of the inputs of the first product and of the
output of the second, all between reference capped orbits and indexed by a common class group
`G`. Suppose the series obey the identity

`∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ₖ ∑ₘ Φ₁ᵢₖ Φ₂ⱼₘ Q'ₖₘₗ =`
`  ∑ₖ Kᵢⱼₖ E₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family. Then on the completed capped modules, with the first input graded by
the cochain degree `n - μ₁`, the continuation maps, the two products and the operation `K` of the
family obey `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = E₀ K(a, b) + K(D₁ a, b) + (-1)^e K(a, D₂ b)` for every
`a` of degree `e`. The sign is constant on the capped generators of each orbit, because recapping
changes the degree by the even number `2 c₁(γ)`. -/
theorem
    novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_coefficientComparison
    (hcont : ∀ i j l, ∑ k, Q i j k * Φ₀ k l - ∑ k, ∑ m, Φ₁ i k * Φ₂ j m * Q' k m l =
      ∑ k, K i j k * E₀ k l + ∑ k, D₁ i k * K k j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * K i k l)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂) :
    novikovMapOfMatrix hF₀ hF₀' r₀ s₀ (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k)) a b) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
          (fun i j k => coefficientComparison q hq (Q' i j k))
          (novikovMapOfMatrix hF₁ hF₁' r₁ s₁ (fun i k => coefficientComparison q hq (Φ₁ i k)) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ s₂ (fun j m => coefficientComparison q hq (Φ₂ j m)) b) =
      novikovMapOfMatrix hF₀' hF₀' s₀ s₀ (fun k l => coefficientComparison q hq (E₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ s₀
            (fun i j k => coefficientComparison q hq (K i j k)) a b) +
        novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ s₀
          (fun i j k => coefficientComparison q hq (K i j k))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ s₀
          (fun i j k => coefficientComparison q hq (K i j k)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k))
            b) := by
  refine novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_novikovMapOfMatrix
    hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' r₁ r₂ r₀ s₁ s₂ s₀ _ _ _ _ _ _ _ _ _ (fun i γ D => ?_)
    (fun i j l => ?_) ha b
  -- Recapping changes the cochain degree by the even number `-2 c₁(γ)`.
  · rw [hμ₁, show n - (degree ω c γ + μ₁ ⟨i, D⟩) - (n - μ₁ ⟨i, D⟩) = -degree ω c γ by ring]
    exact (even_degree ω c γ).neg
  · have h := congrArg (coefficientComparison q hq) (hcont i j l)
    simp only [map_sum, map_add, map_sub, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
      Units.smul_def, map_zsmul] at h ⊢
    exact h

include hμ₁ in
/-- **Continuation maps are multiplicative up to coboundaries.** Under the identity of
`novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_coefficientComparison`,
suppose that every class counted by `K` satisfies the index condition
`μ₀'(s₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n + 1` of rigid members of the family of pairs of pants with
continuation necks, whose Fredholm index at a fixed parameter is `-1`, so that `K` lowers the
cochain degree by one. Then for cocycles `a` and `b` of the cylinder differentials, of cochain
degrees `e` and `f`, the difference `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b` is the coboundary of `K(a, b)` in
cochain degree `e + f`. The differentials are the ground-ring linear maps of the cylinder counts,
for any potential bounds of their kernels. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_mem_coboundaries
    {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    {μ₀' : (Σ k, T₀ k) → ℤ}
    (hμ₀' : ∀ k γ (D : T₀ k), μ₀' ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀' ⟨k, D⟩)
    (hK : ∀ i j k, ∀ A ∈ (K i j k).support,
      μ₀' ⟨k, s₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    (hcont : ∀ i j l, ∑ k, Q i j k * Φ₀ k l - ∑ k, ∑ m, Φ₁ i k * Φ₂ j m * Q' k m l =
      ∑ k, K i j k * E₀ k l + ∑ k, D₁ i k * K k j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * K i k l)
    {C₁ C₂ C₀ : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    (hδ₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C₂)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix s₀ s₀ (fun k l => coefficientComparison q hq (E₀ k l)) p p' ≠ 0 →
        F₀' p' ≤ F₀' p + C₀)
    {e f : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e)
    (hb : b ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    novikovMapOfMatrix hF₀ hF₀' r₀ s₀ (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k)) a b) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' s₁ s₂ s₀
          (fun i j k => coefficientComparison q hq (Q' i j k))
          (novikovMapOfMatrix hF₁ hF₁' r₁ s₁ (fun i k => coefficientComparison q hq (Φ₁ i k)) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ s₂ (fun j m => coefficientComparison q hq (Φ₂ j m)) b) ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀' s₀ s₀ _)).coboundaries
        (gradeBy R F₀' fun p => n - μ₀' p) (e + f) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  have hDa : novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a =
      0 := by
    rw [novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁]
    exact ha.1
  have hDb : novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) b =
      0 := by
    rw [novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂ _ hδ₂]
    exact hb.1
  -- `K` is the product of rigid counts for the output grading `μ₀' - 1`, so `K(a, b)` has cochain
  -- degree `e + f - 1`.
  have hKab := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ s₀ q hq hF₁
    hF₂ hF₀' hμ₁ hμ₂ (μ₀ := fun p => μ₀' p - 1) (fun k γ D => by rw [hμ₀']; ring) K
    (fun i j k A hA => by linarith [hK i j k A hA]) ha.2 hb.2
  have hdeg : ((fun x : ℤ => x - 1) ∘ fun p => n - (μ₀' p - 1)) = fun p => n - μ₀' p := by
    funext p
    simp only [Function.comp_apply]
    ring
  have hKab' := gradeBy_le_gradeBy_comp (R := R) (fun x : ℤ => x - 1) (e + f) hKab
  rw [hdeg] at hKab'
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, hKab', ?_⟩
  -- The Novikov module structures, for the vanishing of the products with `d₁ a = 0`, `d₂ b = 0`.
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₀'
  rw [novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_coefficientComparison
      r₁ r₂ r₀ s₁ s₂ s₀ q hq hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' hμ₁ Q Q' Φ₁ Φ₂ Φ₀ K D₁ D₂ E₀ n hcont ha.2,
    hDa, hDb, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀' hF₀' s₀ s₀ _ hδ₀]

end TauCeti.Floer
