/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Product
public import TauCeti.RingTheory.NovikovModule.Unit

/-!
# The unit of the capped product of class-indexed counts

Let `⋆` be the capped pair-of-pants product of class-indexed counts
(`TauCeti.Geometry.Symplectic.Floer.Cap.Product`), on capped generators of finitely many orbits
with reference caps `r₁`, `r₂`, `r₀`, torsors under the period group `Γ = PeriodGroup ω c`, with
counts indexed by a common class group `G` mapping to `Γ` by an area-preserving homomorphism `q`.

The unit cycle is the count of rigid PSS planes: planes with one negative end, asymptotic to an
orbit `i`, whose centre is constrained to lie on the Morse fundamental cycle of the target. They
are counted class by class, by the generating series `U i = ∑_A N_A q^A`, where a plane of class
`A` relative to the reference cap `r i` is itself the capped generator `(-q A) # r i`. The
completed combination with coordinates `q^A ↦ e^(-q A)` of these series,
`(coordinates hF r).symm fun i => coefficientComparison q hq (U i)`, is the unit cycle `e` on the
completed capped module. This file shows:

* **Degree.** If every class counted by `U` satisfies the index condition `μ(r i) - 2 c₁(A) = n`,
  so that each rigid plane has raw degree `n`, then `e` has cochain degree `n - μ = 0`
  (`coordinates_symm_coefficientComparison_mem_cochain_gradeBy`).
* **Closedness.** The ends of the one-dimensional moduli spaces of PSS planes are the breaking of
  a Floer cylinder at the orbit, and breakings at the constraint, which cancel because the
  fundamental cycle is closed. The count identity `∑ᵢ Uᵢ Dᵢₖ = 0` for the generating series `D`
  of rigid Floer cylinders says that `e` is a cocycle
  (`novikovMapOfMatrix_coordinates_symm_coefficientComparison_eq_zero`).
* **The unit homotopies.** Gluing a PSS plane into the first input of a pair of pants gives a
  one-parameter family of cylinders, whose other end is a Floer cylinder: a continuation
  cylinder between the end Hamiltonians, counted by `Φ`, or the stationary cylinder, with the
  identity matrix, when they coincide. With `K` the generating series of its rigid members, the
  ends of its one-dimensional moduli spaces give the identity
  `∑ᵢ Uᵢ Qᵢⱼₗ - Φⱼₗ = ∑ₖ Kⱼₖ D₀ₖₗ + ∑ₖ D₂ⱼₖ Kₖₗ` of `G`-indexed series, and hence the chain
  homotopy `e ⋆ b - Φ b = D₀ (K b) + K (D₂ b)` on the completed capped modules
  (`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right`). The same holds
  for a plane glued into the second input
  (`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left`).
* **The unit on cocycles.** If moreover the classes counted by `K` satisfy the index condition of
  rigid members of the family, whose Fredholm index at a fixed parameter is `-1`, then for every
  cocycle `b` the difference `e ⋆ b - Φ b` is a coboundary
  (`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right`).
  On a common complex, with `Φ` the identity, `e ⋆ b - b` is a coboundary
  (`novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries_right`): this is the left
  unit law on cohomology classes. Likewise on the right.

The count identities, the energy bounds and the index conditions are the input that the
geometric moduli spaces are to supply; no moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

section UnitCycle

variable {ι : Type*} [Finite ι] {P : ι → Type*} [∀ i, AddTorsor (PeriodGroup ω c) (P i)]
  (r : ∀ i, P i) {F : (Σ i, P i) → ℝ}
  (hF : ∀ i γ (D : P i), F ⟨i, γ +ᵥ D⟩ = F ⟨i, D⟩ - (-area ω c) γ)

/-- **The unit cycle has cochain degree zero.** Let `U` be the generating series of rigid PSS
planes between reference capped orbits. If every class with nonzero count satisfies the index
condition `μ(r i) - 2 c₁(A) = n`, and the grading obeys the recapping law, then the completed
combination with coordinates `q^A ↦ e^(-q A)` of `U` has cochain degree `n - μ` equal to zero. -/
theorem coordinates_symm_coefficientComparison_mem_cochain_gradeBy [Semiring R]
    {μ : (Σ i, P i) → ℤ}
    (hμ : ∀ i γ (D : P i), μ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ ⟨i, D⟩) {n : ℤ}
    (U : ι → NovikovSeries R G ωG)
    (hU : ∀ i, ∀ A ∈ (U i).support, μ ⟨i, r i⟩ - degree ω c (q A) = n) :
    (coordinates hF r).symm (fun i => coefficientComparison q hq (U i)) ∈
      gradeBy R F (fun p => n - μ p) 0 := by
  rw [NovikovModule.mem_gradeBy_iff]
  rintro ⟨i, D⟩ hD
  rw [coordinates_symm_apply] at hD
  obtain ⟨A, hA, hAD⟩ := support_coefficientComparison_subset q hq _ (mem_support.2 hD)
  have e := hμ i (D -ᵥ r i) (r i)
  rw [vsub_vadd, ← hAD, AddMonoidHom.neg_apply, map_neg] at e
  linarith [hU i A hA]

/-- **The unit cycle is a cocycle.** Let `U` be the generating series of rigid PSS planes and `D`
that of rigid Floer cylinders between reference capped orbits. If the series obey the identity
`∑ᵢ Uᵢ Dᵢₖ = 0` in `G`-indexed series, which is the count, class by class, of the ends of the
one-dimensional moduli spaces of PSS planes, then the differential of the cylinder counts vanishes
on the completed combination with coordinates `q^A ↦ e^(-q A)` of `U`. -/
theorem novikovMapOfMatrix_coordinates_symm_coefficientComparison_eq_zero [CommSemiring R]
    [Fintype ι] (U : ι → NovikovSeries R G ωG) (D : ι → ι → NovikovSeries R G ωG)
    (hU : ∀ k, ∑ i, U i * D i k = 0) :
    novikovMapOfMatrix hF hF r r (fun i k => coefficientComparison q hq (D i k))
      ((coordinates hF r).symm fun i => coefficientComparison q hq (U i)) = 0 := by
  refine (coordinates hF r).injective (funext fun k => ?_)
  rw [coordinates_novikovMapOfMatrix hF hF r r (fun i k => coefficientComparison q hq (D i k)),
    LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply]
  simpa only [map_sum, _root_.map_mul, map_zero] using congrArg (coefficientComparison q hq) (hU k)

end UnitCycle

variable [CommRing R] {ι₁ ι₂ ι₀ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]
  {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)

section Right

variable (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (U : ι₁ → NovikovSeries R G ωG)
  (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)

/-- **The unit homotopy in the first input for class-indexed counts.** Let `Q` be the generating
series of rigid pairs of pants, `U` those of rigid PSS planes at the first input, `Φ` those of
rigid Floer cylinders from the second input to the output, `K` those of the rigid members of the
family of pairs of pants with a PSS plane glued into the first input, and `D₂`, `D₀` those of
rigid Floer cylinders of the second input and the output, all between reference capped orbits and
indexed by a common class group `G`. Suppose the series obey the identity

`∑ᵢ Uᵢ Qᵢⱼₗ - Φⱼₗ = ∑ₖ Kⱼₖ D₀ₖₗ + ∑ₖ D₂ⱼₖ Kₖₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family. Then on the completed capped modules, with `e` the unit cycle of
`U`, the maps of the counts obey `e ⋆ b - Φ b = D₀ (K b) + K (D₂ b)` for every `b`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right
    (Φ K : ι₂ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ j l, ∑ i, U i * Q i j l - Φ j l = ∑ k, K j k * D₀ k l + ∑ k, D₂ j k * K k l)
    (b : NovikovModule R F₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
          ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (U i)) b -
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (Φ j l)) b =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
          (novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j k => coefficientComparison q hq (K j k)) b) +
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j k => coefficientComparison q hq (K j k))
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k))
            b) := by
  refine novikovProductOfMatrix_sub_novikovMapOfMatrix_right hF₁ hF₂ hF₀ r₁ r₂ r₀ _ _ _ _ _ _
    (fun j l => ?_) b
  have h := congrArg (coefficientComparison q hq) (hunit j l)
  simp only [map_sum, map_sub, map_add, _root_.map_mul, LinearEquiv.apply_symm_apply] at h ⊢
  exact h

variable {μ₂ : (Σ j, P₂ j) → ℤ}
  (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  (n : ℤ) {C₂ C₀ : ℝ}
  (hδ₂ : ∀ p p',
    mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
      F₂ p' ≤ F₂ p + C₂)
  (hδ₀ : ∀ p p',
    mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
      F₀ p' ≤ F₀ p + C₀)

include hμ₂ hμ₀ in
/-- **The unit in the first input, on cocycles.** Under the identity of
`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right`, suppose that every
class counted by `K` satisfies the index condition `μ₀(r₀) - 2 c₁(A) = μ₂(r₂) + 1` of rigid
members of the family, whose Fredholm index at a fixed parameter is `-1`, so that `K` lowers the
cochain degree `n - μ` by one. Then for every cocycle `b` of the cylinder differential of cochain
degree `f`, the difference `e ⋆ b - Φ b` is the coboundary of `K b` in cochain degree `f`. The
differentials are the ground-ring linear maps of the cylinder counts, for any potential bounds of
their kernels. -/
theorem
    novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right
    (Φ K : ι₂ → ι₀ → NovikovSeries R G ωG)
    (hK : ∀ j l, ∀ A ∈ (K j l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₂ ⟨j, r₂ j⟩ + 1)
    (hunit : ∀ j l, ∑ i, U i * Q i j l - Φ j l = ∑ k, K j k * D₀ k l + ∑ k, D₂ j k * K k l)
    {f : ℤ} {b : NovikovModule R F₂}
    (hb : b ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
          ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (U i)) b -
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (Φ j l)) b ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) f := by
  rw [LinearMap.mem_cocycles_iff, ← novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂ _ hδ₂] at hb
  rw [novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right q hq r₁ r₂ r₀ hF₁
      hF₂ hF₀ Q U D₂ D₀ Φ K hunit, hb.1, map_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  -- `K` lowers the cochain degree by one: its entries have the degree `2 c₁(A)` of the index
  -- condition.
  simpa only [sub_eq_add_neg] using novikovMapOfMatrix_mem_gradeBy hF₂ hF₀ r₂ r₀ (-degree ω c)
    (fun j γ D => by rw [hμ₂, AddMonoidHom.neg_apply]; ring)
    (fun k γ D => by rw [hμ₀, AddMonoidHom.neg_apply]; ring) (ε := -1)
    (fun j l => NovikovSeries.mem_gradeBy_iff.2 fun γ hγ => by
      obtain ⟨A, hA, rfl⟩ := support_coefficientComparison_subset q hq _ hγ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, AddMonoidHom.neg_apply, map_neg,
        neg_neg]
      linarith [hK j l A hA]) hb.2

include hμ₂ in
/-- **The unit in the first input on a common complex.** Suppose the second input and the output
are the same capped complex, and the identity of
`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right` holds with `Φ` the
identity matrix, the count of the stationary cylinders. If every class counted by `K` satisfies
the index condition `μ(r l) - 2 c₁(A) = μ(r j) + 1`, then for every cocycle `b` of the cylinder
differential of cochain degree `f`, the difference `e ⋆ b - b` is a coboundary in cochain degree
`f`, which is the left unit law on cohomology classes. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries_right [DecidableEq ι₂]
    (Q : ι₁ → ι₂ → ι₂ → NovikovSeries R G ωG) (K : ι₂ → ι₂ → NovikovSeries R G ωG)
    (hK : ∀ j l, ∀ A ∈ (K j l).support, μ₂ ⟨l, r₂ l⟩ - degree ω c (q A) = μ₂ ⟨j, r₂ j⟩ + 1)
    (hunit : ∀ j l, ∑ i, U i * Q i j l - (1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG)) j l =
      ∑ k, K j k * D₂ k l + ∑ k, D₂ j k * K k l)
    {f : ℤ} {b : NovikovModule R F₂}
    (hb : b ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₂ r₁ r₂ r₂ (fun i j k => coefficientComparison q hq (Q i j k))
          ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (U i)) b - b ∈
      (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).coboundaries
        (gradeBy R F₂ fun p => n - μ₂ p) f := by
  have h :=
    novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right
      q hq r₁ r₂ r₂ hF₁ hF₂ hF₂ Q U D₂ D₂ hμ₂ hμ₂ n hδ₂ hδ₂
      (1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG)) K hK hunit hb
  -- The comparison of the identity matrix is the identity matrix, whose map is the identity.
  have hid : novikovMapOfMatrix hF₂ hF₂ r₂ r₂
      (fun j l => coefficientComparison q hq ((1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG)) j l)) b =
        b := by
    refine (coordinates hF₂ r₂).injective (funext fun l => ?_)
    rw [coordinates_novikovMapOfMatrix hF₂ hF₂ r₂ r₂
      (fun j l => coefficientComparison q hq ((1 : Matrix ι₂ ι₂ (NovikovSeries R G ωG)) j l))]
    simp [Matrix.one_apply, apply_ite]
  rwa [hid] at h

end Right

section Left

variable (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (U : ι₂ → NovikovSeries R G ωG)
  (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)

/-- **The unit homotopy in the second input for class-indexed counts.** Let `Q` be the generating
series of rigid pairs of pants, `U` those of rigid PSS planes at the second input, `Φ` those of
rigid Floer cylinders from the first input to the output, `K` those of the rigid members of the
family of pairs of pants with a PSS plane glued into the second input, and `D₁`, `D₀` those of
rigid Floer cylinders of the first input and the output, all between reference capped orbits and
indexed by a common class group `G`. Suppose the series obey the identity

`∑ⱼ Uⱼ Qᵢⱼₗ - Φᵢₗ = ∑ₖ Kᵢₖ D₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family. Then on the completed capped modules, with `e` the unit cycle of
`U`, the maps of the counts obey `a ⋆ e - Φ a = D₀ (K a) + K (D₁ a)` for every `a`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left
    (Φ K : ι₁ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ i l, ∑ j, U j * Q i j l - Φ i l = ∑ k, K i k * D₀ k l + ∑ k, D₁ i k * K k l)
    (a : NovikovModule R F₁) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
          a ((coordinates hF₂ r₂).symm fun j => coefficientComparison q hq (U j)) -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (Φ i l)) a =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
          (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (K i k)) a) +
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (K i k))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k))
            a) := by
  refine novikovProductOfMatrix_sub_novikovMapOfMatrix_left hF₁ hF₂ hF₀ r₁ r₂ r₀ _ _ _ _ _ _
    (fun i l => ?_) a
  have h := congrArg (coefficientComparison q hq) (hunit i l)
  simp only [map_sum, map_sub, map_add, _root_.map_mul, LinearEquiv.apply_symm_apply] at h ⊢
  exact h

variable {μ₁ : (Σ i, P₁ i) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  (n : ℤ) {C₁ C₀ : ℝ}
  (hδ₁ : ∀ p p',
    mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
      F₁ p' ≤ F₁ p + C₁)
  (hδ₀ : ∀ p p',
    mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
      F₀ p' ≤ F₀ p + C₀)

include hμ₁ hμ₀ in
/-- **The unit in the second input, on cocycles.** Under the identity of
`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left`, suppose that every
class counted by `K` satisfies the index condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + 1` of rigid
members of the family, whose Fredholm index at a fixed parameter is `-1`, so that `K` lowers the
cochain degree `n - μ` by one. Then for every cocycle `a` of the cylinder differential of cochain
degree `f`, the difference `a ⋆ e - Φ a` is the coboundary of `K a` in cochain degree `f`. The
differentials are the ground-ring linear maps of the cylinder counts, for any potential bounds of
their kernels. -/
theorem
    novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_left
    (Φ K : ι₁ → ι₀ → NovikovSeries R G ωG)
    (hK : ∀ i l, ∀ A ∈ (K i l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + 1)
    (hunit : ∀ i l, ∑ j, U j * Q i j l - Φ i l = ∑ k, K i k * D₀ k l + ∑ k, D₁ i k * K k l)
    {f : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
          a ((coordinates hF₂ r₂).symm fun j => coefficientComparison q hq (U j)) -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (Φ i l)) a ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) f := by
  rw [LinearMap.mem_cocycles_iff, ← novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁] at ha
  rw [novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left q hq r₁ r₂ r₀ hF₁
      hF₂ hF₀ Q U D₁ D₀ Φ K hunit, ha.1, map_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  -- `K` lowers the cochain degree by one: its entries have the degree `2 c₁(A)` of the index
  -- condition.
  simpa only [sub_eq_add_neg] using novikovMapOfMatrix_mem_gradeBy hF₁ hF₀ r₁ r₀ (-degree ω c)
    (fun i γ D => by rw [hμ₁, AddMonoidHom.neg_apply]; ring)
    (fun k γ D => by rw [hμ₀, AddMonoidHom.neg_apply]; ring) (ε := -1)
    (fun i l => NovikovSeries.mem_gradeBy_iff.2 fun γ hγ => by
      obtain ⟨A, hA, rfl⟩ := support_coefficientComparison_subset q hq _ hγ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, AddMonoidHom.neg_apply, map_neg,
        neg_neg]
      linarith [hK i l A hA]) ha.2

include hμ₁ in
/-- **The unit in the second input on a common complex.** Suppose the first input and the output
are the same capped complex, and the identity of
`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left` holds with `Φ` the
identity matrix, the count of the stationary cylinders. If every class counted by `K` satisfies
the index condition `μ(r l) - 2 c₁(A) = μ(r i) + 1`, then for every cocycle `a` of the cylinder
differential of cochain degree `f`, the difference `a ⋆ e - a` is a coboundary in cochain degree
`f`, which is the right unit law on cohomology classes. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries_left [DecidableEq ι₁]
    (Q : ι₁ → ι₂ → ι₁ → NovikovSeries R G ωG) (K : ι₁ → ι₁ → NovikovSeries R G ωG)
    (hK : ∀ i l, ∀ A ∈ (K i l).support, μ₁ ⟨l, r₁ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + 1)
    (hunit : ∀ i l, ∑ j, U j * Q i j l - (1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) i l =
      ∑ k, K i k * D₁ k l + ∑ k, D₁ i k * K k l)
    {f : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₁ r₁ r₂ r₁ (fun i j k => coefficientComparison q hq (Q i j k))
          a ((coordinates hF₂ r₂).symm fun j => coefficientComparison q hq (U j)) - a ∈
      (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).coboundaries
        (gradeBy R F₁ fun p => n - μ₁ p) f := by
  have h :=
    novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_left
      q hq r₁ r₂ r₁ hF₁ hF₂ hF₁ Q U D₁ D₁ hμ₁ hμ₁ n hδ₁ hδ₁
      (1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) K hK hunit ha
  -- The comparison of the identity matrix is the identity matrix, whose map is the identity.
  have hid : novikovMapOfMatrix hF₁ hF₁ r₁ r₁
      (fun i l => coefficientComparison q hq ((1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) i l)) a =
        a := by
    refine (coordinates hF₁ r₁).injective (funext fun l => ?_)
    rw [coordinates_novikovMapOfMatrix hF₁ hF₁ r₁ r₁
      (fun i l => coefficientComparison q hq ((1 : Matrix ι₁ ι₁ (NovikovSeries R G ωG)) i l))]
    simp [Matrix.one_apply, apply_ite]
  rwa [hid] at h

end Left

end TauCeti.Floer
