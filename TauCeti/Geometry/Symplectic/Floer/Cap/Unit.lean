/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Product
public import TauCeti.RingTheory.NovikovModule.Unit

/-!
# The unit of the pair-of-pants product of class-indexed counts

The unit of the pair-of-pants product is the image of the fundamental cycle under the PSS map: the
count of the negative PSS planes whose constraint is the fundamental cycle, each plane `u`
asymptotic at its output to an orbit `i`. Fix a reference cap `rᵢ` of each orbit. A plane is
itself a cap of its orbit, so the planes are counted in each class `A = rᵢ - u`, by generating
series `Eᵢ = ∑_A N_A q^A` indexed by a common class group `G` mapping to the period group `Γ` by an
area-preserving homomorphism `q`. The completed capped combination of these counts is
`(coordinates hF r).symm fun i => coefficientComparison q hq (E i)`; its coefficient at a capped
generator `D` of the orbit `i` is the finite sum of the counts over the classes `A` with
`q A = rᵢ - D`, that is, the count of the planes whose cap class is `D`
(`TauCeti.Floer.coordinates_symm_coefficientComparison_apply`). This file proves:

* **Degree from the index.** If every counted class satisfies the rigidity condition
  `μ(rᵢ) - 2 c₁(A) = n - k`, the combination has cochain degree `k`
  (`TauCeti.Floer.coordinates_symm_coefficientComparison_mem_cochain_gradeBy`). For the
  fundamental cycle, of raw degree `n`, this is cochain degree `0`.
* **The cocycle condition from the count identity.** The image of a combination of counts under
  the map of cylinder counts `D` is the combination of the counts `∑ᵢ Eᵢ Dᵢₖ`
  (`TauCeti.Floer.novikovMapOfMatrix_coordinates_symm_coefficientComparison`). The ends of the
  one-dimensional moduli spaces of PSS planes are the planes broken at their output, since the
  fundamental cycle is closed, so `∑ᵢ Eᵢ Dᵢₖ = 0` and the combination is a cocycle
  (`TauCeti.Floer.coordinates_symm_coefficientComparison_mem_cocycles`).
* **The unit homotopy from the count identity.** Gluing a PSS plane into the first input of a
  pair of pants gives a one-parameter family whose other end is a Floer cylinder: a continuation
  cylinder between the Hamiltonians of the second input and of the output, or the stationary
  cylinder when they coincide. If the series obey the identity
  `∑ᵢ Eᵢ Qᵢⱼₗ - Φⱼₗ = ∑ₘ Kⱼₘ D₀ₘₗ + ∑ₘ D₂ⱼₘ Kₘₗ` given by the ends of the one-dimensional moduli
  spaces of the family, with `K` counting its rigid members and `Φ` the continuation cylinders,
  then `e ⋆ b - Φ b = d₀ K(b) + K(d₂ b)` for the combination `e` of the plane counts
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right`), and
  likewise for a plane glued into the second input
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left`). If
  the classes counted by `K` satisfy the index condition of rigid members of the family, then on
  cocycles the difference is a coboundary
  (`novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right`
  and its `_left` form).
* **The unit on cohomology.** When the second input and the output are the same complex and `Φ`
  is the identity, the class of the combination of plane counts is a left identity for the product
  on the cohomology of the cylinder differentials
  (`TauCeti.Floer.cohomologyProduct_kernelProduct_coefficientComparison_unit_mk`), and likewise a
  right identity (`TauCeti.Floer.cohomologyProduct_kernelProduct_coefficientComparison_mk_unit`).

The energy, compactness, index and boundary-count hypotheses are the ones the geometric moduli
spaces are to supply; no moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  PSS map and the unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich, 1995.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on
  Floer homology and the pair-of-pants product.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  {ι₁ ι₂ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)

section Combination

variable [Semiring R] [Finite ι₁]

/-- **The combination of class-indexed counts on capped generators.** Its coefficient at a capped
generator `D` of the orbit `i` is the finite sum of the counts over all classes `A` with
`q A = rᵢ - D`: the planes whose cap class is `D`. -/
theorem coordinates_symm_coefficientComparison_apply (E : ι₁ → NovikovSeries R G ωG) {i : ι₁}
    (D : P₁ i) :
    ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (E i)).val ⟨i, D⟩ =
      ∑ᶠ A ∈ q ⁻¹' {r₁ i -ᵥ D}, (E i).coeff A := by
  rw [coordinates_symm_apply, coefficientComparison_apply, coeff_map]
  refine finsum_mem_congr ?_ fun _ _ => rfl
  ext A
  simp only [Set.mem_preimage, Set.mem_singleton_iff, AddMonoidHom.neg_apply,
    neg_eq_iff_eq_neg, neg_vsub_eq_vsub_rev]

variable {μ₁ : (Σ i, P₁ i) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)

include hμ₁ in
/-- **Degree of the combination of counts from the index.** If the gradings obey the recapping law
and every class with nonzero count satisfies `μ(rᵢ) - 2 c₁(A) = n - k` relative to the reference
caps, then the combination of the counts has cochain degree `k` for the cochain grading `n - μ`.
For the PSS planes of the fundamental cycle, of raw degree `n`, this is the degree `k = 0`. -/
theorem coordinates_symm_coefficientComparison_mem_cochain_gradeBy {n k : ℤ}
    {E : ι₁ → NovikovSeries R G ωG}
    (hE : ∀ i, ∀ A ∈ (E i).support, μ₁ ⟨i, r₁ i⟩ - degree ω c (q A) = n - k) :
    ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (E i)) ∈
      gradeBy R F₁ (fun p => n - μ₁ p) k := by
  rw [NovikovModule.mem_gradeBy_iff]
  rintro ⟨i, D⟩ hD
  rw [coordinates_symm_apply] at hD
  obtain ⟨A, hA, hAD⟩ := support_coefficientComparison_subset q hq (E i) (mem_support.2 hD)
  have hd := hE i A hA
  have e₁ := hμ₁ i (D -ᵥ r₁ i) (r₁ i)
  rw [vsub_vadd, ← hAD, AddMonoidHom.neg_apply, map_neg] at e₁
  linarith

end Combination

section Map

variable [CommSemiring R] [Fintype ι₁] [Finite ι₀]

/-- **The map of cylinder counts on a combination of counts.** The image of the combination of
counts `E` under the map of the class-indexed counts `M` is the combination of the counts
`∑ᵢ Eᵢ Mᵢₖ`: in Floer theory, the planes glued at their output to the cylinders. -/
theorem novikovMapOfMatrix_coordinates_symm_coefficientComparison
    (E : ι₁ → NovikovSeries R G ωG) (M : ι₁ → ι₀ → NovikovSeries R G ωG) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (M i k))
        ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (E i)) =
      (coordinates hF₀ r₀).symm fun k => coefficientComparison q hq (∑ i, E i * M i k) := by
  refine (coordinates hF₀ r₀).injective (funext fun k => ?_)
  refine (coordinates_novikovMapOfMatrix hF₁ hF₀ r₁ r₀ _ _ k).trans ?_
  simp only [LinearEquiv.apply_symm_apply, map_sum, _root_.map_mul]

end Map

section Cocycle

variable [CommRing R] [Fintype ι₁] {μ₁ : (Σ i, P₁ i) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)

include hμ₁ in
/-- **The combination of counts is a cocycle from the count identity.** Let `E` be the generating
series of rigid PSS planes and `D₁` those of rigid Floer cylinders, all indexed by a common class
group `G`. If the series obey the identity `∑ᵢ Eᵢ D₁ᵢₖ = 0` given by the ends of the
one-dimensional moduli spaces of PSS planes, and the classes counted by `E` satisfy the index
condition `μ(rᵢ) - 2 c₁(A) = n - k`, then the combination of the counts is a cocycle of cochain
degree `k` of the cylinder differential, for any potential bound of its kernel. -/
theorem coordinates_symm_coefficientComparison_mem_cocycles {n k : ℤ}
    {E : ι₁ → NovikovSeries R G ωG} {D₁ : ι₁ → ι₁ → NovikovSeries R G ωG}
    (hE : ∀ i, ∀ A ∈ (E i).support, μ₁ ⟨i, r₁ i⟩ - degree ω c (q A) = n - k)
    (hED : ∀ l, ∑ i, E i * D₁ i l = 0) {C : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C) :
    ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (E i)) ∈
      (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
        (gradeBy R F₁ fun p => n - μ₁ p) k := by
  refine LinearMap.mem_cocycles_iff.2
    ⟨?_, coordinates_symm_coefficientComparison_mem_cochain_gradeBy r₁ q hq hF₁ hμ₁ hE⟩
  rw [← novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁,
    novikovMapOfMatrix_coordinates_symm_coefficientComparison,
    show (fun l => coefficientComparison q hq (∑ i, E i * D₁ i l)) = 0 from
      funext fun l => by rw [hED, map_zero, Pi.zero_apply]]
  exact map_zero _

end Cocycle

section Homotopy

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)

section Right

variable (E : ι₁ → NovikovSeries R G ωG) (Φ K : ι₂ → ι₀ → NovikovSeries R G ωG)
  (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
  (hunit : ∀ j l, ∑ i, E i * Q i j l - Φ j l = ∑ m, K j m * D₀ m l + ∑ m, D₂ j m * K m l)

include hunit

/-- **The unit homotopy for class-indexed counts, in the first input.** Let `E` be the generating
series of rigid PSS planes with output in the orbits of the first input, `Q` those of rigid pairs
of pants, `Φ` those of rigid continuation cylinders from the orbits of the second input to those
of the output, `D₂`, `D₀` those of rigid Floer cylinders of the second input and of the output,
and `K` those of the rigid members of the family obtained by gluing a PSS plane into the first
input of a pair of pants, all indexed by a common class group `G`. Suppose the series obey the
identity

`∑ᵢ Eᵢ Qᵢⱼₗ - Φⱼₗ = ∑ₘ Kⱼₘ D₀ₘₗ + ∑ₘ D₂ⱼₘ Kₘₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family between reference capped orbits. Then on the completed capped
modules, for the combination `e` of the plane counts, the map of `K` is a homotopy between
multiplication by `e` and the continuation map: `e ⋆ b - Φ b = d₀ K(b) + K(d₂ b)` for every `b`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right
    (b : NovikovModule R F₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k))
          ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (E i)) b -
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (Φ j l)) b =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l))
          (novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j m => coefficientComparison q hq (K j m)) b) +
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j m => coefficientComparison q hq (K j m))
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m))
            b) := by
  refine novikovProductOfMatrix_sub_novikovMapOfMatrix_right hF₁ hF₂ hF₀ r₁ r₂ r₀ _ _ _ _ _ _
    (fun j l => ?_) b
  have h := congrArg (coefficientComparison q hq) (hunit j l)
  simp only [map_sum, map_add, map_sub, _root_.map_mul] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- **The unit homotopy for class-indexed counts on cocycles, in the first input.** Under the
identity of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right`, suppose
that every class counted by `K` satisfies the index condition
`μ₀(r₀) - 2 c₁(A) = μ₂(r₂) + 1` of rigid members of the family, whose Fredholm index at a fixed
parameter is `-1`, so that `K` lowers the cochain degree by one. Then for every cocycle `b` of
the cylinder differential of cochain degree `f`, the difference `e ⋆ b - Φ b` is the coboundary of
`K(b)` in cochain degree `f`. The differentials are the ground-ring linear maps of the cylinder
counts, for any potential bounds of their kernels. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right
    {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    {n : ℤ} (hK : ∀ j l, ∀ A ∈ (K j l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₂ ⟨j, r₂ j⟩ + 1)
    {C₂ C₀ : ℝ}
    (hδ₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C₂)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {f : ℤ} {b : NovikovModule R F₂}
    (hb : b ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k))
          ((coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (E i)) b -
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (Φ j l)) b ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) f := by
  rw [LinearMap.mem_cocycles_iff, ← novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂ _ hδ₂] at hb
  refine LinearMap.mem_coboundaries_iff.2 ⟨_,
    novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy r₂ r₀ q hq hμ₂ hμ₀ hF₂ hF₀ hK
      hb.2, ?_⟩
  rw [novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right r₁ r₂ r₀ q hq hF₁
      hF₂ hF₀ Q D₀ E Φ K D₂ hunit b,
    hb.1, map_zero, add_zero, novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀]

end Right

section Left

variable (E : ι₂ → NovikovSeries R G ωG) (Φ K : ι₁ → ι₀ → NovikovSeries R G ωG)
  (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
  (hunit : ∀ i l, ∑ j, E j * Q i j l - Φ i l = ∑ m, K i m * D₀ m l + ∑ m, D₁ i m * K m l)

include hunit

/-- **The unit homotopy for class-indexed counts, in the second input.** Let `E` be the generating
series of rigid PSS planes with output in the orbits of the second input, `Q` those of rigid pairs
of pants, `Φ` those of rigid continuation cylinders from the orbits of the first input to those of
the output, `D₁`, `D₀` those of rigid Floer cylinders of the first input and of the output, and
`K` those of the rigid members of the family obtained by gluing a PSS plane into the second input
of a pair of pants, all indexed by a common class group `G`. Suppose the series obey the identity

`∑ⱼ Eⱼ Qᵢⱼₗ - Φᵢₗ = ∑ₘ Kᵢₘ D₀ₘₗ + ∑ₘ D₁ᵢₘ Kₘₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family between reference capped orbits. Then on the completed capped
modules, for the combination `e` of the plane counts, the map of `K` is a homotopy between
multiplication by `e` on the right and the continuation map:
`a ⋆ e - Φ a = d₀ K(a) + K(d₁ a)` for every `a`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left
    (a : NovikovModule R F₁) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a
          ((coordinates hF₂ r₂).symm fun j => coefficientComparison q hq (E j)) -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (Φ i l)) a =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l))
          (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i m => coefficientComparison q hq (K i m)) a) +
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i m => coefficientComparison q hq (K i m))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m))
            a) := by
  refine novikovProductOfMatrix_sub_novikovMapOfMatrix_left hF₁ hF₂ hF₀ r₁ r₂ r₀ _ _ _ _ _ _
    (fun i l => ?_) a
  have h := congrArg (coefficientComparison q hq) (hunit i l)
  simp only [map_sum, map_add, map_sub, _root_.map_mul] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- **The unit homotopy for class-indexed counts on cocycles, in the second input.** Under the
identity of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left`, suppose
that every class counted by `K` satisfies the index condition
`μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + 1` of rigid members of the family, so that `K` lowers the cochain
degree by one. Then for every cocycle `a` of the cylinder differential of cochain degree `f`, the
difference `a ⋆ e - Φ a` is the coboundary of `K(a)` in cochain degree `f`. The differentials are
the ground-ring linear maps of the cylinder counts, for any potential bounds of their kernels. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_left
    {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
    {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    {n : ℤ} (hK : ∀ i l, ∀ A ∈ (K i l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + 1)
    {C₁ C₀ : ℝ}
    (hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁)
    (hδ₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {f : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a
          ((coordinates hF₂ r₂).symm fun j => coefficientComparison q hq (E j)) -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (Φ i l)) a ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) f := by
  rw [LinearMap.mem_cocycles_iff, ← novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁] at ha
  refine LinearMap.mem_coboundaries_iff.2 ⟨_,
    novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₀ q hq hμ₁ hμ₀ hF₁ hF₀ hK
      ha.2, ?_⟩
  rw [novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left r₁ r₂ r₀ q hq hF₁
      hF₂ hF₀ Q D₀ E Φ K D₁ hunit a,
    ha.1, map_zero, add_zero, novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀]

end Left

end Homotopy

section Cohomology

variable [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Type*}
  [∀ j, AddTorsor (PeriodGroup ω c) (P j)] (r : ∀ j, P j) {F : (Σ j, P j) → ℝ}
  (hF : ∀ j γ (D : P j), F ⟨j, γ +ᵥ D⟩ = F ⟨j, D⟩ - (-area ω c) γ)
  {μ : (Σ j, P j) → ℤ} (hμ : ∀ j γ (D : P j), μ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ ⟨j, D⟩)
  (D : ι → ι → NovikovSeries R G ωG) {C : ℝ}
  (hδ : ∀ p p', mapKernelOfMatrix r r (fun j k => coefficientComparison q hq (D j k)) p p' ≠ 0 →
    F p' ≤ F p + C)
  (K : ι → ι → NovikovSeries R G ωG)
  (hK : ∀ j l, ∀ A ∈ (K j l).support, μ ⟨l, r l⟩ - degree ω c (q A) = μ ⟨j, r j⟩ + 1)
  {n ε : ℤ} {CQ : ℝ}

omit [Fintype ι] in
/-- The comparison of the identity matrix of class-indexed series is the identity matrix. -/
private theorem coefficientComparison_one_apply :
    (fun j l => coefficientComparison q hq ((1 : Matrix ι ι (NovikovSeries R G ωG)) j l)) =
      (1 : Matrix ι ι _) :=
  Matrix.map_one (coefficientComparison q hq) (map_zero _) (map_one _)

include hμ hK

/-- **The unit of class-indexed counts on cohomology, on the left.** Let the product of
class-indexed counts `Q`, with the first input graded by `n - μ₁` and a common complex as its
second input and its output, as a ground-ring bilinear map for any potential bound of its kernel,
induce a product on the cohomology of the cylinder differentials, with degree shift `ε`. Let `e`
be a cocycle of the first input of degree `d₁` which is the combination of the counts `E` of PSS
planes. Suppose the series obey the unit identity
`∑ᵢ Eᵢ Qᵢⱼₗ - [j = l] = ∑ₘ Kⱼₘ Dₘₗ + ∑ₘ Dⱼₘ Kₘₗ` of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right` with
the stationary cylinders as the continuation cylinders, and that `K` satisfies the index
condition of rigid members of the family. Then the class of `e` is a left identity for the
product on cohomology: `[e] ⋆ y = y` for every class `y` of degree `d`, where `d₁ + d + ε = d`. -/
theorem cohomologyProduct_kernelProduct_coefficientComparison_unit_mk [Fintype ι₁]
    {μ₁ : (Σ i, P₁ i) → ℤ}
    (Q : ι₁ → ι → ι → NovikovSeries R G ωG) (E : ι₁ → NovikovSeries R G ωG)
    (hunit : ∀ j l, ∑ i, E i * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) j l =
      ∑ m, K j m * D m l + ∑ m, D j m * K m l)
    {D₁ : ι₁ → ι₁ → NovikovSeries R G ωG} {C₁ : ℝ}
    {hδ₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C₁}
    {hnQ : ∀ p₁ p₂ p₀,
      kernelOfMatrix r₁ r r (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
        F p₀ ≤ F₁ p₁ + F p₂ + CQ}
    {hQdeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F},
      a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → b ∈ gradeBy R F (fun p => n - μ p) j →
        kernelProduct hnQ (kernelOfMatrix_mem hF r₁ r r _) a b ∈
          gradeBy R F (fun p => n - μ p) (i + j + ε)}
    {hQL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → ∀ b,
      kernelMap hδ (mapKernelOfMatrix_mem hF r r _)
          (kernelProduct hnQ (kernelOfMatrix_mem hF r₁ r r _) a b) =
        kernelProduct hnQ (kernelOfMatrix_mem hF r₁ r r _)
            (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _) a) b +
          negOnePowCast R i • kernelProduct hnQ (kernelOfMatrix_mem hF r₁ r r _) a
            (kernelMap hδ (mapKernelOfMatrix_mem hF r r _) b)}
    {d₁ d : ℤ} (hij : d₁ + d + ε = d)
    (e : (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) d₁)
    (he : (e : NovikovModule R F₁) =
      (coordinates hF₁ r₁).symm fun i => coefficientComparison q hq (E i))
    (y : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
      (gradeBy R F fun p => n - μ p) d) :
    LinearMap.cohomologyProduct (kernelProduct hnQ (kernelOfMatrix_mem hF r₁ r r _)) hQdeg hQL hij
      (Submodule.Quotient.mk e) y = y := by
  induction y using Submodule.Quotient.induction_on with
  | H b =>
    rw [LinearMap.cohomologyProduct_mk, LinearMap.cohomology_mk_eq_mk_iff]
    have h :=
      novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right
        r₁ r r q hq hF₁ hF hF Q D E
        (1 : Matrix ι ι (NovikovSeries R G ωG)) K D hunit hμ hμ hK hδ hδ b.2
    -- The Novikov module structure, for the identity map of the identity matrix.
    let := module (R := R) hF
    rw [coefficientComparison_one_apply, novikovMapOfMatrix_one, LinearMap.id_apply,
      novikovProductOfMatrix_eq_kernelProduct hF₁ hF hF r₁ r r _ hnQ, ← he] at h
    exact h

/-- **The unit of class-indexed counts on cohomology, on the right.** Let the product of
class-indexed counts `Q`, with a common complex as its first input and its output and the second
input graded by `n - μ₂`, as a ground-ring bilinear map for any potential bound of its kernel,
induce a product on the cohomology of the cylinder differentials, with degree shift `ε`. Let `e`
be a cocycle of the second input of degree `d₂` which is the combination of the counts `E` of PSS
planes. Suppose the series obey the unit identity
`∑ⱼ Eⱼ Qᵢⱼₗ - [i = l] = ∑ₘ Kᵢₘ Dₘₗ + ∑ₘ Dᵢₘ Kₘₗ` of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left` with
the stationary cylinders as the continuation cylinders, and that `K` satisfies the index
condition of rigid members of the family. Then the class of `e` is a right identity for the
product on cohomology: `x ⋆ [e] = x` for every class `x` of degree `d`, where `d + d₂ + ε = d`. -/
theorem cohomologyProduct_kernelProduct_coefficientComparison_mk_unit [Fintype ι₂]
    {μ₂ : (Σ j, P₂ j) → ℤ}
    (Q : ι → ι₂ → ι → NovikovSeries R G ωG) (E : ι₂ → NovikovSeries R G ωG)
    (hunit : ∀ i l, ∑ j, E j * Q i j l - (1 : Matrix ι ι (NovikovSeries R G ωG)) i l =
      ∑ m, K i m * D m l + ∑ m, D i m * K m l)
    {D₂ : ι₂ → ι₂ → NovikovSeries R G ωG} {C₂ : ℝ}
    {hδ₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C₂}
    {hnQ : ∀ p₁ p₂ p₀,
      kernelOfMatrix r r₂ r (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0 →
        F p₀ ≤ F p₁ + F₂ p₂ + CQ}
    {hQdeg : ∀ {i j : ℤ} {a : NovikovModule R F} {b : NovikovModule R F₂},
      a ∈ gradeBy R F (fun p => n - μ p) i → b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j →
        kernelProduct hnQ (kernelOfMatrix_mem hF r r₂ r _) a b ∈
          gradeBy R F (fun p => n - μ p) (i + j + ε)}
    {hQL : ∀ {i : ℤ} {a : NovikovModule R F}, a ∈ gradeBy R F (fun p => n - μ p) i → ∀ b,
      kernelMap hδ (mapKernelOfMatrix_mem hF r r _)
          (kernelProduct hnQ (kernelOfMatrix_mem hF r r₂ r _) a b) =
        kernelProduct hnQ (kernelOfMatrix_mem hF r r₂ r _)
            (kernelMap hδ (mapKernelOfMatrix_mem hF r r _) a) b +
          negOnePowCast R i • kernelProduct hnQ (kernelOfMatrix_mem hF r r₂ r _) a
            (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _) b)}
    {d d₂ : ℤ} (hij : d + d₂ + ε = d)
    (x : (kernelMap hδ (mapKernelOfMatrix_mem hF r r _)).cohomology
      (gradeBy R F fun p => n - μ p) d)
    (e : (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) d₂)
    (he : (e : NovikovModule R F₂) =
      (coordinates hF₂ r₂).symm fun j => coefficientComparison q hq (E j)) :
    LinearMap.cohomologyProduct (kernelProduct hnQ (kernelOfMatrix_mem hF r r₂ r _)) hQdeg hQL hij
      x (Submodule.Quotient.mk e) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [LinearMap.cohomologyProduct_mk, LinearMap.cohomology_mk_eq_mk_iff]
    have h :=
      novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_left
        r r₂ r q hq hF hF₂ hF Q D E
        (1 : Matrix ι ι (NovikovSeries R G ωG)) K D hunit hμ hμ hK hδ hδ a.2
    -- The Novikov module structure, for the identity map of the identity matrix.
    let := module (R := R) hF
    rw [coefficientComparison_one_apply, novikovMapOfMatrix_one, LinearMap.id_apply,
      novikovProductOfMatrix_eq_kernelProduct hF hF₂ hF r r₂ r _ hnQ, ← he] at h
    exact h

end Cohomology

end TauCeti.Floer
