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

Fix two choices of end Hamiltonians for the pair of pants, finitely many orbits for each end of
each choice, and reference caps `rₗ` and `rₗ'` of the orbits, as in
`TauCeti.Geometry.Symplectic.Floer.Cap.Product`. The rigid pairs of pants of the two choices are
counted by generating series `Q` and `Q'`, and the rigid continuation cylinders from the orbits of
each end of the first choice to those of the second by generating series `Φ₁`, `Φ₂` and `Φ₀`, all
indexed by classes of a common class group `G` relative to the reference caps. The rigid Floer
cylinders of the two inputs of the first choice and of the output of the second are counted by
`D₁`, `D₂` and `D₀'`.

Gluing continuation cylinders to the three ends of a pair of pants gives a one-parameter family of
pairs of pants whose perturbation data interpolate between the two choices. Its rigid elements
are counted by series `K`. The ends of its one-dimensional moduli spaces are the two broken
configurations, a pair of pants of the first choice followed by a continuation cylinder at the
output, or continuation cylinders at the inputs followed by a pair of pants of the second choice,
together with the breaking of Floer cylinders at the three ends. Counting them, class by class,
gives the identity

`∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ₜ ∑ᵤ Φ₁ᵢₜ Φ₂ⱼᵤ Q'ₜᵤₗ =
  ∑ₘ Kᵢⱼₘ D₀'ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₗ`

in `G`-indexed series. This file proves:

* **The continuation homotopy.** The identity gives the chain homotopy
  `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = d₀' K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` on the completed
  capped modules, for `a` of cochain degree `e`
  (`TauCeti.Floer.novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`).
* **The degree of the homotopy.** If every class counted by `K` satisfies the index condition
  `μ₀'(r₀') - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n + 1` of the rigid members of a one-parameter family,
  the product of the counts lowers the cochain degree `n - μ` by one
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy_sub_one`).
* **On cocycles.** Under this index condition, for cocycles `a` and `b` of cochain degrees `i` and
  `j` the difference `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b` is a coboundary of cochain degree `i + j` (see
  `novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries`). So
  continuation maps intertwine the two products on cohomology.

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
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)] [∀ t, AddTorsor (PeriodGroup ω c) (P₁' t)]
  [∀ u, AddTorsor (PeriodGroup ω c) (P₂' u)] [∀ l, AddTorsor (PeriodGroup ω c) (P₀' l)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  (r₁' : ∀ t, P₁' t) (r₂' : ∀ u, P₂' u) (r₀' : ∀ l, P₀' l)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {F₁' : (Σ t, P₁' t) → ℝ} {F₂' : (Σ u, P₂' u) → ℝ} {F₀' : (Σ l, P₀' l) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hF₁' : ∀ t γ (D : P₁' t), F₁' ⟨t, γ +ᵥ D⟩ = F₁' ⟨t, D⟩ - (-area ω c) γ)
  (hF₂' : ∀ u γ (D : P₂' u), F₂' ⟨u, γ +ᵥ D⟩ = F₂' ⟨u, D⟩ - (-area ω c) γ)
  (hF₀' : ∀ l γ (D : P₀' l), F₀' ⟨l, γ +ᵥ D⟩ = F₀' ⟨l, D⟩ - (-area ω c) γ)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  {μ₀' : (Σ l, P₀' l) → ℤ}
  (hμ₀' : ∀ l γ (D : P₀' l), μ₀' ⟨l, γ +ᵥ D⟩ = degree ω c γ + μ₀' ⟨l, D⟩)

section Degree

variable [CommSemiring R] [Finite ι₁] [Finite ι₂] [Finite κ₀]

include hμ₁ hμ₂ hμ₀' in
/-- **The homotopy of rigid counts in a one-parameter family has cochain degree `-1`.** If every
class `A` counted by the series `K i j l` satisfies the index condition
`μ₀'(r₀' l) - 2 c₁(A) = μ₁(r₁ i) + μ₂(r₂ j) - n + 1` of the rigid members of a one-parameter
family relative to the reference caps, and the gradings obey the recapping law, then the product of
the counts on capped generators lowers the cochain degree `n - μ` by one. -/
theorem novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy_sub_one {n : ℤ}
    (K : ι₁ → ι₂ → κ₀ → NovikovSeries R G ωG)
    (hK : ∀ i j l, ∀ A ∈ (K i j l).support,
      μ₀' ⟨l, r₀' l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    {i' j' : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i') (hb : b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j') :
    novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
        (fun i j l => coefficientComparison q hq (K i j l)) a b ∈
      gradeBy R F₀' (fun p => n - μ₀' p) (i' + j' - 1) := by
  -- This is the degree-zero statement for the cochain degree `(n - 1) - μ`.
  rw [gradeBy_sub] at ha hb ⊢
  have h := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ r₀' q hq hF₁ hF₂
    hF₀' hμ₁ hμ₂ hμ₀' (n := n - 1) K (fun i j l A hA => by linarith [hK i j l A hA])
    (i' := i' - 1) (j' := j' - 1) (by rwa [gradeBy_sub, sub_sub_sub_cancel_right])
    (by rwa [gradeBy_sub, sub_sub_sub_cancel_right])
  rwa [gradeBy_sub, show n - 1 - (i' - 1 + (j' - 1)) = n - (i' + j' - 1) by ring] at h

end Degree

section Homotopy

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] [Fintype κ₁] [Fintype κ₂]
  [Fintype κ₀]

include hμ₁ in
/-- **The continuation homotopy for class-indexed counts.** Let `Q` and `Q'` be the generating
series of rigid pairs of pants for two choices of end Hamiltonians, `Φ₁`, `Φ₂`, `Φ₀` those of rigid
continuation cylinders from the orbits of each end of the first choice to those of the second,
`K` those of the rigid elements of the continuation family of pairs of pants, and `D₁`, `D₂`,
`D₀'` those of rigid Floer cylinders of the two inputs of the first choice and of the output of the
second, all indexed by a common class group `G`. Suppose the series obey the identity

`∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ₜ ∑ᵤ Φ₁ᵢₜ Φ₂ⱼᵤ Q'ₜᵤₗ =
  ∑ₘ Kᵢⱼₘ D₀'ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family between reference capped orbits. Then on the completed capped
modules, with the first input graded by the cochain degree `n - μ₁`, the products and the maps of
the counts obey `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = d₀' K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` for
every `a` of degree `e`. The sign is constant on the capped generators of each orbit, because
recapping changes the degree by the even number `2 c₁(γ)`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Q' : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (Φ₁ : ι₁ → κ₁ → NovikovSeries R G ωG) (Φ₂ : ι₂ → κ₂ → NovikovSeries R G ωG)
    (Φ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (K : ι₁ → ι₂ → κ₀ → NovikovSeries R G ωG)
    (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
    (D₀' : κ₀ → κ₀ → NovikovSeries R G ωG) (n : ℤ)
    (hcont : ∀ i j l, ∑ k, Q i j k * Φ₀ k l - ∑ t, ∑ u, Φ₁ i t * Φ₂ j u * Q' t u l =
      ∑ m, K i j m * D₀' m l + ∑ m, D₁ i m * K m j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m l)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂) :
    novikovMapOfMatrix hF₀ hF₀' r₀ r₀' (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k)) a b) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' r₁' r₂' r₀'
          (fun t u l => coefficientComparison q hq (Q' t u l))
          (novikovMapOfMatrix hF₁ hF₁' r₁ r₁' (fun i t => coefficientComparison q hq (Φ₁ i t)) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ r₂' (fun j u => coefficientComparison q hq (Φ₂ j u))
            b) =
      novikovMapOfMatrix hF₀' hF₀' r₀' r₀' (fun m l => coefficientComparison q hq (D₀' m l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
            (fun i j l => coefficientComparison q hq (K i j l)) a b) +
        novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
          (fun i j l => coefficientComparison q hq (K i j l))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
          (fun i j l => coefficientComparison q hq (K i j l)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m))
            b) := by
  refine novikovMapOfMatrix_novikovProductOfMatrix_sub_eq_add hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' r₁ r₂ r₀
    r₁' r₂' r₀' _ _ _ _ _ _ _ _ _ (fun i γ D => ?_) (fun i j l => ?_) ha b
  · rw [hμ₁, show n - (degree ω c γ + μ₁ ⟨i, D⟩) - (n - μ₁ ⟨i, D⟩) = -degree ω c γ by ring]
    exact (even_degree ω c γ).neg
  · have h := congrArg (coefficientComparison q hq) (hcont i j l)
    simp only [map_sum, map_sub, map_add, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
      Units.smul_def, map_zsmul] at h ⊢
    exact h

include hμ₁ hμ₂ hμ₀' in
/-- **Continuation maps and the capped product on cocycles.** Under the identity of
`TauCeti.Floer.novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`, if
every class counted by the homotopy series `K i j l` satisfies the index condition
`μ₀'(r₀' l) - 2 c₁(A) = μ₁(r₁ i) + μ₂(r₂ j) - n + 1`, then for cocycles `a` and `b` of the two
inputs of the first product, of cochain degrees `i` and `j`, the difference
`Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b` is a coboundary of cochain degree `i + j` for the output of the second
product. The differentials are the maps of the cylinder counts, as kernel maps for any potential
bounds of their kernels. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Q' : κ₁ → κ₂ → κ₀ → NovikovSeries R G ωG)
    (Φ₁ : ι₁ → κ₁ → NovikovSeries R G ωG) (Φ₂ : ι₂ → κ₂ → NovikovSeries R G ωG)
    (Φ₀ : ι₀ → κ₀ → NovikovSeries R G ωG) (K : ι₁ → ι₂ → κ₀ → NovikovSeries R G ωG)
    (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
    (D₀' : κ₀ → κ₀ → NovikovSeries R G ωG) (n : ℤ)
    (hcont : ∀ i j l, ∑ k, Q i j k * Φ₀ k l - ∑ t, ∑ u, Φ₁ i t * Φ₂ j u * Q' t u l =
      ∑ m, K i j m * D₀' m l + ∑ m, D₁ i m * K m j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m l)
    (hK : ∀ i j l, ∀ A ∈ (K i j l).support,
      μ₀' ⟨l, r₀' l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    {C₁ C₂ C₀ : ℝ}
    (hm₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    (hm₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C₂)
    (hm₀ : ∀ p p',
      mapKernelOfMatrix r₀' r₀' (fun m l => coefficientComparison q hq (D₀' m l)) p p' ≠ 0 →
        F₀' p' ≤ F₀' p + C₀)
    {i j : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hm₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) i)
    {b : NovikovModule R F₂}
    (hb : b ∈ (kernelMap hm₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) j) :
    novikovMapOfMatrix hF₀ hF₀' r₀ r₀' (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k)) a b) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' r₁' r₂' r₀'
          (fun t u l => coefficientComparison q hq (Q' t u l))
          (novikovMapOfMatrix hF₁ hF₁' r₁ r₁' (fun i t => coefficientComparison q hq (Φ₁ i t)) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ r₂' (fun j u => coefficientComparison q hq (Φ₂ j u))
            b) ∈
      (kernelMap hm₀ (mapKernelOfMatrix_mem hF₀' r₀' r₀' _)).coboundaries
        (gradeBy R F₀' fun p => n - μ₀' p) (i + j) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₀'
  rw [LinearMap.mem_cocycles_iff] at ha hb
  have h₁ := (novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁
    (fun i m => coefficientComparison q hq (D₁ i m)) hm₁ a).trans ha.1
  have h₂ := (novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂
    (fun j m => coefficientComparison q hq (D₂ j m)) hm₂ b).trans hb.1
  rw [novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add r₁ r₂ r₀ r₁' r₂'
      r₀' hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' q hq hμ₁ Q Q' Φ₁ Φ₂ Φ₀ K D₁ D₂ D₀' n hcont ha.2 b, h₁, h₂,
    map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀' hF₀' r₀' r₀' _ hm₀]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  exact novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy_sub_one r₁ r₂ r₀' hF₁ hF₂
    hF₀' q hq hμ₁ hμ₂ hμ₀' K hK ha.2 hb.2

end Homotopy

end TauCeti.Floer
