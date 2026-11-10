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

Fix two choices of Floer data for the pair-of-pants product, for instance two triples of end
Hamiltonians `(H₁, H₂, H₀)` and `(H₁', H₂', H₀')`. For each choice fix finitely many orbits at
each end and reference caps `rₗ`, `rₗ'` of the orbits, as in
`TauCeti.Geometry.Symplectic.Floer.Cap.Product`. Counting, class by class in a common class
group `G`, the rigid pairs of pants of the two choices gives generating series `Q` and `Q'`, and
counting the rigid continuation cylinders from the orbits of `Hₗ` to those of `Hₗ'` gives
generating series `Φ₁`, `Φ₂`, `Φ₀`. Their comparisons `q^A ↦ e^(-q A)`
(`TauCeti.Floer.coefficientComparison`) are the matrices of the two products and of the three
continuation maps on the completed capped modules.

Gluing the continuation cylinders to the ends of a pair of pants gives a one-parameter family of
pairs of pants with input ends `H₁`, `H₂` and output end `H₀'`, whose two broken ends are the
two composites `Φ₀ ∘ ⋆` and `⋆' ∘ (Φ₁ ⊗ Φ₂)`. Its rigid members are counted by series `K`, and
the other ends of its one-dimensional moduli spaces are breakings of Floer cylinders at the three
ends, counted by series `D₁`, `D₂` and `D₀'`. Counting all ends gives, class by class, the
identity

`∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ᵢ' ∑ⱼ' Φ₁ᵢᵢ' Φ₂ⱼⱼ' Q'ᵢ'ⱼ'ₗ =`
`  ∑ₖ Kᵢⱼₖ D₀'ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series. This file proves:

* **The continuation homotopy.** The identity gives the chain homotopy
  `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = d₀' K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` on the completed capped
  modules, for `a` of cochain degree `e`
  (`TauCeti.Floer.novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`).
* **On cocycles.** If every class counted by `K` satisfies the index condition of rigid members of
  the family, whose Fredholm index at a fixed parameter is `-1`, then for cocycles `a` and `b` the
  difference `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b` is a coboundary, so the continuation maps intertwine the
  two products on cohomology (see
  `novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries`).
* **Independence of the perturbation data.** For two choices of perturbation data on the pair of
  pants with the same ends, the continuation maps are the identity, and the identity
  `Qᵢⱼₗ - Q'ᵢⱼₗ = ∑ₖ Kᵢⱼₖ D₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Kᵢₖₗ` makes
  `a ⋆ b - a ⋆' b` a coboundary for cocycles `a` and `b`: the two products agree on cohomology
  (see `novikovProductOfMatrix_coefficientComparison_sub_novikovProductOfMatrix_mem_coboundaries`).

The count identity and the index condition are the input the geometric moduli spaces are to
supply; no moduli space, orientation or count is constructed here.

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

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {ι₁ ι₂ ι₀ κ₁ κ₂ κ₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  {P₁' : κ₁ → Type*} {P₂' : κ₂ → Type*} {P₀' : κ₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)] [∀ i, AddTorsor (PeriodGroup ω c) (P₁' i)]
  [∀ j, AddTorsor (PeriodGroup ω c) (P₂' j)] [∀ k, AddTorsor (PeriodGroup ω c) (P₀' k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  (r₁' : ∀ i, P₁' i) (r₂' : ∀ j, P₂' j) (r₀' : ∀ k, P₀' k)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {F₁' : (Σ i, P₁' i) → ℝ} {F₂' : (Σ j, P₂' j) → ℝ} {F₀' : (Σ k, P₀' k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hF₁' : ∀ i γ (D : P₁' i), F₁' ⟨i, γ +ᵥ D⟩ = F₁' ⟨i, D⟩ - (-area ω c) γ)
  (hF₂' : ∀ j γ (D : P₂' j), F₂' ⟨j, γ +ᵥ D⟩ = F₂' ⟨j, D⟩ - (-area ω c) γ)
  (hF₀' : ∀ k γ (D : P₀' k), F₀' ⟨k, γ +ᵥ D⟩ = F₀' ⟨k, D⟩ - (-area ω c) γ)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)
  [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  (n : ℤ)

section Homotopy

variable [Fintype κ₁] [Fintype κ₂] [Fintype κ₀]
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Q' : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
  (Φ₁ : ι₁ → κ₁ → NovikovSeries R G ωG) (Φ₂ : ι₂ → κ₂ → NovikovSeries R G ωG)
  (Φ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (K : ι₁ → ι₂ → κ₀ → NovikovSeries R G ωG)
  (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
  (D₀' : κ₀ → κ₀ → NovikovSeries R G ωG)

include hμ₁ in
/-- **The continuation homotopy for class-indexed counts.** Let `Q` and `Q'` be the generating
series of rigid pairs of pants for two choices of Floer data, `Φ₁`, `Φ₂`, `Φ₀` those of rigid
continuation cylinders from the orbits of each end of the first choice to those of the second,
`K` those of the rigid members of the continuation family of pairs of pants, and `D₁`, `D₂`,
`D₀'` those of rigid Floer cylinders of the two inputs of the first choice and of the output of
the second, all indexed by a common class group `G`. Suppose the series obey the identity

`∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ᵢ' ∑ⱼ' Φ₁ᵢᵢ' Φ₂ⱼⱼ' Q'ᵢ'ⱼ'ₗ =`
`  ∑ₖ Kᵢⱼₖ D₀'ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family between reference capped orbits. Then on the completed capped
modules, with the first input graded by the cochain degree `n - μ₁`, the products, the
continuation maps and the operation `K` of the family obey
`Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = d₀' K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` for every `a` of degree
`e` and every `b`. The sign is constant on the capped generators of each orbit, because recapping
changes the degree by the even number `2 c₁(γ)`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add
    (hcont : ∀ i j l,
      ∑ k, Q i j k * Φ₀ k l - ∑ i', ∑ j', Φ₁ i i' * Φ₂ j j' * Q' i' j' l =
        ∑ k, K i j k * D₀' k l + ∑ k, D₁ i k * K k j l +
          negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * K i k l)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂) :
    novikovMapOfMatrix hF₀ hF₀' r₀ r₀' (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k)) a b) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' r₁' r₂' r₀'
          (fun i j k => coefficientComparison q hq (Q' i j k))
          (novikovMapOfMatrix hF₁ hF₁' r₁ r₁' (fun i i' => coefficientComparison q hq (Φ₁ i i')) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ r₂' (fun j j' => coefficientComparison q hq (Φ₂ j j'))
            b) =
      novikovMapOfMatrix hF₀' hF₀' r₀' r₀' (fun k l => coefficientComparison q hq (D₀' k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
            (fun i j k => coefficientComparison q hq (K i j k)) a b) +
        novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
          (fun i j k => coefficientComparison q hq (K i j k))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
          (fun i j k => coefficientComparison q hq (K i j k)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k))
            b) := by
  refine novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_novikovMapOfMatrix
    hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' r₁ r₂ r₀ r₁' r₂' r₀' _ _ _ _ _ _ _ _ _ (fun i γ D => ?_)
    (fun i j l => ?_) ha b
  · -- Recapping changes the cochain degree by the even number `-2 c₁(γ)`.
    rw [hμ₁, show n - (degree ω c γ + μ₁ ⟨i, D⟩) - (n - μ₁ ⟨i, D⟩) = -degree ω c γ by ring]
    exact (even_degree ω c γ).neg
  · have h := congrArg (coefficientComparison q hq) (hcont i j l)
    simp only [map_sum, map_sub, map_add, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
      Units.smul_def, map_zsmul] at h ⊢
    exact h

include hμ₁ hμ₂ in
/-- **Continuation maps intertwine the products of class-indexed counts on cohomology.** Under the
identity of `novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`, suppose
that every class counted by `K` satisfies the index condition
`μ₀'(r₀') - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n + 1` of rigid members of the continuation family, whose
Fredholm index at a fixed parameter is `-1`, so that `K` lowers the cochain degree by one. Then for
cocycles `a` and `b` of the cylinder differentials of the first choice, of cochain degrees `e` and
`f`, the difference `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b` is the coboundary of `K(a, b)` in cochain degree
`e + f` for the output differential of the second choice. The differentials are the ground-ring
linear maps of the cylinder counts, for any potential bounds of their kernels. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries
    {μ₀' : (Σ k, P₀' k) → ℤ}
    (hμ₀' : ∀ k γ (D : P₀' k), μ₀' ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀' ⟨k, D⟩)
    (hK : ∀ i j k, ∀ A ∈ (K i j k).support,
      μ₀' ⟨k, r₀' k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    (hcont : ∀ i j l,
      ∑ k, Q i j k * Φ₀ k l - ∑ i', ∑ j', Φ₁ i i' * Φ₂ j j' * Q' i' j' l =
        ∑ k, K i j k * D₀' k l + ∑ k, D₁ i k * K k j l +
          negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * K i k l)
    {C₁ C₂ C₀ : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    (hδ₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C₂)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix r₀' r₀' (fun k l => coefficientComparison q hq (D₀' k l)) p p' ≠ 0 →
        F₀' p' ≤ F₀' p + C₀)
    {e f : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e)
    (hb : b ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    novikovMapOfMatrix hF₀ hF₀' r₀ r₀' (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k)) a b) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' r₁' r₂' r₀'
          (fun i j k => coefficientComparison q hq (Q' i j k))
          (novikovMapOfMatrix hF₁ hF₁' r₁ r₁' (fun i i' => coefficientComparison q hq (Φ₁ i i')) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ r₂' (fun j j' => coefficientComparison q hq (Φ₂ j j'))
            b) ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀' r₀' r₀' _)).coboundaries
        (gradeBy R F₀' fun p => n - μ₀' p) (e + f) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  have hDa : novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a =
      0 := (novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁ a).trans ha.1
  have hDb : novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) b =
      0 := (novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂ _ hδ₂ b).trans hb.1
  -- `K` is the product of rigid counts for the output grading `μ₀' - 1`, so `K(a, b)` has cochain
  -- degree `e + f - 1`.
  have hKab := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ r₀' q hq hF₁
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
  rw [novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add r₁ r₂ r₀ r₁' r₂'
      r₀' hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' q hq hμ₁ n Q Q' Φ₁ Φ₂ Φ₀ K D₁ D₂ D₀' hcont ha.2 b,
    hDa, hDb, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀' hF₀' r₀' r₀' _ hδ₀]

end Homotopy

section Data

omit [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] in
/-- On a common complex the comparison of the identity matrix of series gives the identity map. -/
private theorem novikovMapOfMatrix_coefficientComparison_one_apply [Finite ι₀] [DecidableEq ι₀]
    (b : NovikovModule R F₀) :
    novikovMapOfMatrix hF₀ hF₀ r₀ r₀
        (fun k l => coefficientComparison q hq ((1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) k l)) b =
      b := by
  have h1 :
      (fun k l => coefficientComparison q hq ((1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) k l)) =
      (1 : Matrix ι₀ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c))) := by
    funext k l
    rw [Matrix.one_apply, Matrix.one_apply, apply_ite (coefficientComparison q hq),
      _root_.map_one, map_zero]
  let := module (R := R) hF₀
  rw [h1, novikovMapOfMatrix_one, LinearMap.id_apply]

include hμ₁ hμ₂ in
/-- **The product of class-indexed counts on cohomology does not depend on the perturbation
data.** Let `Q` and `Q'` be the generating series of rigid pairs of pants for two choices of
perturbation data with the same ends, so that the continuation maps are the identity, and let `K`
be those of the rigid members of a family of perturbation data joining them, with
`μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n + 1` for every counted class. If the series obey the
identity

`Qᵢⱼₗ - Q'ᵢⱼₗ = ∑ₖ Kᵢⱼₖ D₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series, then for cocycles `a` and `b` of cochain degrees `e` and `f`, the
difference `a ⋆ b - a ⋆' b` is a coboundary in cochain degree `e + f`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovProductOfMatrix_mem_coboundaries
    {μ₀ : (Σ k, P₀ k) → ℤ}
    (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    (Q Q' K : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hK : ∀ i j k, ∀ A ∈ (K i j k).support,
      μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    (hcont : ∀ i j l, Q i j l - Q' i j l =
      ∑ k, K i j k * D₀ k l + ∑ k, D₁ i k * K k j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * K i k l)
    {C₁ C₂ C₀ : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    (hδ₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C₂)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {e f : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e)
    (hb : b ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a b -
        novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q' i j k)) a b ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) (e + f) := by
  classical
  -- The continuation maps are the identity matrices.
  have h := novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries
    r₁ r₂ r₀ r₁ r₂ r₀ hF₁ hF₂ hF₀ hF₁ hF₂ hF₀ q hq hμ₁ hμ₂ n Q Q'
    (1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) (1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG))
    (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) K D₁ D₂ D₀ hμ₀ hK (fun i j l => by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact hcont i j l) hδ₁ hδ₂ hδ₀ ha hb
  rwa [novikovMapOfMatrix_coefficientComparison_one_apply r₁ hF₁ q hq,
    novikovMapOfMatrix_coefficientComparison_one_apply r₂ hF₂ q hq,
    novikovMapOfMatrix_coefficientComparison_one_apply r₀ hF₀ q hq] at h

end Data

end TauCeti.Floer
