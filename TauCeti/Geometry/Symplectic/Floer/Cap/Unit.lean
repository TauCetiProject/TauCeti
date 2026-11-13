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

Fix finitely many orbits for each end of the pair of pants, and reference caps `rₗ` of the
orbits, as in `TauCeti.Geometry.Symplectic.Floer.Cap.Product`. The unit of the pair-of-pants
product is the count of PSS planes constrained by the fundamental cycle of the target. Counting
these planes asymptotic to the orbit `i` in each class `A`, relative to the reference cap
`r₁ i`, gives a generating series `E i = ∑_A N_A q^A` in a common class group `G`. The unit
cycle `e` on the capped generators is the completed combination whose coordinates relative to the
reference caps are the comparisons `q^A ↦ e^(-q A)` of these series
(`TauCeti.Floer.coefficientComparison`).

Gluing such a plane into the first input of a pair of pants gives a one-parameter family whose
other end is a Floer cylinder: a continuation cylinder between the end Hamiltonians or, on a
common complex, the stationary cylinder. Its rigid elements are counted by series `K`, and the
ends of its one-dimensional moduli spaces give, class by class, the identity

`∑ᵢ Eᵢ Qᵢⱼₗ - Φⱼₗ = ∑ₖ Kⱼₖ D₀ₖₗ + ∑ₖ D₂ⱼₖ Kₖₗ`

in `G`-indexed series, where `Q` counts rigid pairs of pants, `Φ` counts the cylinders of the
other end, and `D₂`, `D₀` count rigid Floer cylinders of the second input and of the output. This
file proves:

* **The unit homotopy.** The identity gives the chain homotopy `e ⋆ b - Φ b = d₀ (K b) + K (d₂ b)`
  on the completed capped modules
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right`), and
  likewise for the unit in the second input
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left`).
* **Degrees.** If every plane counted by `E i` has index zero, `μ₁(r₁ i) - 2 c₁(A) = n`, the unit
  cycle has cochain degree `0`
  (`TauCeti.Floer.mem_cochain_gradeBy_zero_of_coordinates_eq_coefficientComparison`). If every
  cylinder counted by a series `K` raises the raw degree by `ε` relative to the reference caps,
  the map of `K` shifts the raw degree by `ε`
  (`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_mem_gradeBy`).
* **On cocycles.** If the homotopy counts raise the raw degree by one, the difference
  `e ⋆ b - Φ b` of a cocycle `b` of cochain degree `j` is a coboundary of cochain degree `j`
  (see
`Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right`
and
`Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_left`).
  On a common complex, with `Φ` the identity matrix, whose comparison gives the identity map
  (`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_one`), this says that `e ⋆ b - b` is a
  coboundary
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries_right`,
  `TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries_left`).

The count identity and the index conditions are the input the geometric moduli spaces are to
supply; no moduli space, orientation or count is constructed here.

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
  {ι₁ ι₂ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

section Grading

variable {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)

include hμ₁ in
/-- **The unit cycle has cochain degree zero.** If every plane counted by the series `E i` has
index zero relative to the reference cap, `μ₁(r₁ i) - 2 c₁(A) = n`, then the completed
combination whose reference coordinates are the comparisons of the `E i` is homogeneous of
cochain degree `0` for the cochain degree `n - μ₁`, that is, of raw degree `n`. -/
theorem mem_cochain_gradeBy_zero_of_coordinates_eq_coefficientComparison [Semiring R] [Finite ι₁]
    {n : ℤ}
    (E : ι₁ → NovikovSeries R G ωG)
    (hE : ∀ i, ∀ A ∈ (E i).support, μ₁ ⟨i, r₁ i⟩ - degree ω c (q A) = n)
    {e : NovikovModule R F₁} (he : ∀ i, coordinates hF₁ r₁ e i = coefficientComparison q hq (E i)) :
    e ∈ gradeBy R F₁ (fun p => n - μ₁ p) 0 := by
  rw [gradeBy_sub, sub_zero, mem_gradeBy_iff_coordinates hF₁ (degree ω c) hμ₁ r₁]
  intro i
  rw [he i]
  simpa only [neg_sub] using coefficientComparison_mem_gradeBy q hq ((degree ω c).comp q)
    (degree ω c) (fun _ => rfl) (k := μ₁ ⟨i, r₁ i⟩ - n)
    fun A hA => by rw [AddMonoidHom.comp_apply]; linarith [hE i A hA]

include hμ₂ hμ₀ in
/-- **The degree of the map of class-indexed counts.** If every class counted by the series
`K j l` raises the raw degree by `ε` relative to the reference caps,
`μ₀(r₀ l) - 2 c₁(A) = μ₂(r₂ j) + ε`, then the map of the counts on capped generators shifts the
raw degree by `ε`. -/
theorem novikovMapOfMatrix_coefficientComparison_mem_gradeBy [CommSemiring R] [Finite ι₂]
    [Finite ι₀] {ε : ℤ} (K : ι₂ → ι₀ → NovikovSeries R G ωG)
    (hK : ∀ j l, ∀ A ∈ (K j l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₂ ⟨j, r₂ j⟩ + ε)
    {k : ℤ} {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ μ₂ k) :
    novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (K j l)) b ∈
      gradeBy R F₀ μ₀ (k + ε) := by
  have := Fintype.ofFinite ι₂
  rw [mem_gradeBy_iff_coordinates hF₂ (degree ω c) hμ₂ r₂] at hb
  rw [mem_gradeBy_iff_coordinates hF₀ (degree ω c) hμ₀ r₀]
  intro l
  rw [coordinates_novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (K j l))]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hc := coefficientComparison_mem_gradeBy q hq ((degree ω c).comp q) (degree ω c)
    (fun _ => rfl) (k := μ₀ ⟨l, r₀ l⟩ - μ₂ ⟨j, r₂ j⟩ - ε)
    fun A hA => by rw [AddMonoidHom.comp_apply]; linarith [hK j l A hA]
  convert SetLike.mul_mem_graded (hb j) hc using 2
  ring

end Grading

section Homotopy

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]

/-- **The unit homotopy for class-indexed counts, in the first input.** Let `Q` be the
generating series of rigid pairs of pants, `E` those of the unit planes at the orbits of the first
input, `Φ` and `K` those of the cylinders and of the rigid elements of the unit family, and `D₂`,
`D₀` those of rigid Floer cylinders of the second input and of the output, all indexed by a
common class group `G`. If they obey the identity

`∑ᵢ Eᵢ Qᵢⱼₗ - Φⱼₗ = ∑ₖ Kⱼₖ D₀ₖₗ + ∑ₖ D₂ⱼₖ Kₖₗ`

in `G`-indexed series, then for the completed combination `e` whose reference coordinates are the
comparisons of the `Eᵢ`, the product and the maps of the counts on capped generators obey
`e ⋆ b - Φ b = d₀ (K b) + K (d₂ b)` for every completed combination `b`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (E : ι₁ → NovikovSeries R G ωG)
    (Φ K : ι₂ → ι₀ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ j l, ∑ i, E i * Q i j l - Φ j l = ∑ k, K j k * D₀ k l + ∑ k, D₂ j k * K k l)
    {e : NovikovModule R F₁} (he : ∀ i, coordinates hF₁ r₁ e i = coefficientComparison q hq (E i))
    (b : NovikovModule R F₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) e b -
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (Φ j l)) b =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
          (novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (K j l)) b) +
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (K j l))
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k))
            b) := by
  refine novikovProductOfMatrix_sub_novikovMapOfMatrix_right hF₁ hF₂ hF₀ r₁ r₂ r₀ _ e _ _ _ _
    (fun j l => ?_) b
  have h := congrArg (coefficientComparison q hq) (hunit j l)
  simp only [map_sub, map_add, map_sum, _root_.map_mul] at h
  simpa only [he] using h

/-- **The unit homotopy for class-indexed counts, in the second input.** If the generating series
obey the identity

`∑ⱼ Eⱼ Qᵢⱼₗ - Φᵢₗ = ∑ₖ Kᵢₖ D₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖₗ`

in `G`-indexed series, then for the completed combination `e` whose reference coordinates are the
comparisons of the `Eⱼ`, the product and the maps of the counts on capped generators obey
`a ⋆ e - Φ a = d₀ (K a) + K (d₁ a)` for every completed combination `a`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (E : ι₂ → NovikovSeries R G ωG)
    (Φ K : ι₁ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ i l, ∑ j, E j * Q i j l - Φ i l = ∑ k, K i k * D₀ k l + ∑ k, D₁ i k * K k l)
    {e : NovikovModule R F₂} (he : ∀ j, coordinates hF₂ r₂ e j = coefficientComparison q hq (E j))
    (a : NovikovModule R F₁) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a e -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (Φ i l)) a =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
          (novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (K i l)) a) +
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (K i l))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k))
            a) := by
  refine novikovProductOfMatrix_sub_novikovMapOfMatrix_left hF₁ hF₂ hF₀ r₁ r₂ r₀ _ e _ _ _ _
    (fun i l => ?_) a
  have h := congrArg (coefficientComparison q hq) (hunit i l)
  simp only [map_sub, map_add, map_sum, _root_.map_mul] at h
  simpa only [he] using h

end Homotopy

section Identity

variable [CommSemiring R] [Finite ι₀] [DecidableEq ι₀]

/-- The comparison of the identity matrix of class-indexed counts gives the identity map. -/
@[simp]
theorem novikovMapOfMatrix_coefficientComparison_one :
    letI := module (R := R) hF₀
    novikovMapOfMatrix hF₀ hF₀ r₀ r₀
        (fun k l => coefficientComparison q hq ((1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) k l)) =
      LinearMap.id := by
  have h1 :
      (fun k l => coefficientComparison q hq ((1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) k l)) =
        (1 : Matrix ι₀ ι₀ (NovikovSeries R (PeriodGroup ω c) (-area ω c))) :=
    Matrix.map_one _ (map_zero (coefficientComparison q hq))
      (map_one (coefficientComparison q hq))
  rw [h1]
  exact novikovMapOfMatrix_one hF₀ r₀

end Identity

section Cocycles

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀]
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  {n : ℤ} {C₀ C' : ℝ}

include hμ₂ hμ₀ in
/-- **The unit in the first input, on cocycles.** Under the identity of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right`, if
every class counted by the homotopy series `K j l` raises the raw degree by one relative to the
reference caps, `μ₀(r₀ l) - 2 c₁(A) = μ₂(r₂ j) + 1`, then for every cocycle `b` of the second
input of cochain degree `j` the difference `e ⋆ b - Φ b` is a coboundary of cochain degree `j`.
The differentials are the maps of the cylinder counts, as kernel maps for any potential bounds
of their kernels. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (E : ι₁ → NovikovSeries R G ωG)
    (Φ K : ι₂ → ι₀ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ j l, ∑ i, E i * Q i j l - Φ j l = ∑ k, K j k * D₀ k l + ∑ k, D₂ j k * K k l)
    {e : NovikovModule R F₁} (he : ∀ i, coordinates hF₁ r₁ e i = coefficientComparison q hq (E i))
    (hK : ∀ j l, ∀ A ∈ (K j l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₂ ⟨j, r₂ j⟩ + 1)
    (hm₂ : ∀ p p',
      mapKernelOfMatrix r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) p p' ≠ 0 →
        F₂ p' ≤ F₂ p + C')
    (hm₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {j : ℤ} {b : NovikovModule R F₂}
    (hb : b ∈ (kernelMap hm₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) j) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) e b -
        novikovMapOfMatrix hF₂ hF₀ r₂ r₀ (fun j l => coefficientComparison q hq (Φ j l)) b ∈
      (kernelMap hm₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) j := by
  rw [LinearMap.mem_cocycles_iff, gradeBy_sub] at hb
  have h₀ := (novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂
    (fun j k => coefficientComparison q hq (D₂ j k)) hm₂ b).trans hb.1
  rw [novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_right r₁ r₂ r₀ hF₁ hF₂ hF₀
    q hq Q E Φ K D₂ D₀ hunit he b, h₀, map_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hm₀]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  have h := novikovMapOfMatrix_coefficientComparison_mem_gradeBy r₂ r₀ hF₂ hF₀ q hq hμ₂ hμ₀ K hK
    hb.2
  rwa [gradeBy_sub, ← sub_add]

include hμ₁ hμ₀ in
/-- **The unit in the second input, on cocycles.** Under the identity of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left`, if
every class counted by the homotopy series `K i l` raises the raw degree by one relative to the
reference caps, `μ₀(r₀ l) - 2 c₁(A) = μ₁(r₁ i) + 1`, then for every cocycle `a` of the first
input of cochain degree `i` the difference `a ⋆ e - Φ a` is a coboundary of cochain degree `i`.
The differentials are the maps of the cylinder counts, as kernel maps for any potential bounds
of their kernels. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_left
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (E : ι₂ → NovikovSeries R G ωG)
    (Φ K : ι₁ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ i l, ∑ j, E j * Q i j l - Φ i l = ∑ k, K i k * D₀ k l + ∑ k, D₁ i k * K k l)
    {e : NovikovModule R F₂} (he : ∀ j, coordinates hF₂ r₂ e j = coefficientComparison q hq (E j))
    (hK : ∀ i l, ∀ A ∈ (K i l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + 1)
    (hm₁ : ∀ p p',
      mapKernelOfMatrix r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) p p' ≠ 0 →
        F₁ p' ≤ F₁ p + C')
    (hm₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {i : ℤ} {a : NovikovModule R F₁}
    (ha : a ∈ (kernelMap hm₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) i) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a e -
        novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i l => coefficientComparison q hq (Φ i l)) a ∈
      (kernelMap hm₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) i := by
  rw [LinearMap.mem_cocycles_iff, gradeBy_sub] at ha
  have h₀ := (novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁
    (fun i k => coefficientComparison q hq (D₁ i k)) hm₁ a).trans ha.1
  rw [novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_left r₁ r₂ r₀ hF₁ hF₂ hF₀
    q hq Q E Φ K D₁ D₀ hunit he a, h₀, map_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hm₀]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, ?_, rfl⟩
  have h := novikovMapOfMatrix_coefficientComparison_mem_gradeBy r₁ r₀ hF₁ hF₀ q hq hμ₁ hμ₀ K hK
    ha.2
  rwa [gradeBy_sub, ← sub_add]

include hμ₀ in
/-- **The unit on a common complex, in the first input.** If the second input and the output of
the product are the same capped complex, and the generating series obey

`∑ᵢ Eᵢ Qᵢⱼₗ - [j = l] = ∑ₖ Kⱼₖ D₀ₖₗ + ∑ₖ D₀ⱼₖ Kₖₗ`,

with the homotopy series `K` raising the raw degree by one, then for every cocycle `b` of cochain
degree `j` the difference `e ⋆ b - b` is a coboundary of cochain degree `j`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries_right [DecidableEq ι₀]
    (Q : ι₁ → ι₀ → ι₀ → NovikovSeries R G ωG) (E : ι₁ → NovikovSeries R G ωG)
    (K D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ j l, ∑ i, E i * Q i j l - (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) j l =
      ∑ k, K j k * D₀ k l + ∑ k, D₀ j k * K k l)
    {e : NovikovModule R F₁} (he : ∀ i, coordinates hF₁ r₁ e i = coefficientComparison q hq (E i))
    (hK : ∀ j l, ∀ A ∈ (K j l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₀ ⟨j, r₀ j⟩ + 1)
    (hm₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {j : ℤ} {b : NovikovModule R F₀}
    (hb : b ∈ (kernelMap hm₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).cocycles
      (gradeBy R F₀ fun p => n - μ₀ p) j) :
    novikovProductOfMatrix hF₁ hF₀ hF₀ r₁ r₀ r₀
        (fun i j k => coefficientComparison q hq (Q i j k)) e b - b ∈
      (kernelMap hm₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) j := by
  have h :=
    novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_right
      r₁ r₀ r₀ hF₁ hF₀ hF₀ q hq hμ₀ hμ₀ Q E (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) K D₀ D₀
      hunit he hK hm₀ hm₀ hb
  let := module (R := R) hF₀
  rwa [novikovMapOfMatrix_coefficientComparison_one, LinearMap.id_apply] at h

include hμ₀ in
/-- **The unit on a common complex, in the second input.** If the first input and the output of
the product are the same capped complex, and the generating series obey

`∑ⱼ Eⱼ Qᵢⱼₗ - [i = l] = ∑ₖ Kᵢₖ D₀ₖₗ + ∑ₖ D₀ᵢₖ Kₖₗ`,

with the homotopy series `K` raising the raw degree by one, then for every cocycle `a` of cochain
degree `i` the difference `a ⋆ e - a` is a coboundary of cochain degree `i`. -/
theorem novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries_left [DecidableEq ι₀]
    (Q : ι₀ → ι₂ → ι₀ → NovikovSeries R G ωG) (E : ι₂ → NovikovSeries R G ωG)
    (K D₀ : ι₀ → ι₀ → NovikovSeries R G ωG)
    (hunit : ∀ i l, ∑ j, E j * Q i j l - (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) i l =
      ∑ k, K i k * D₀ k l + ∑ k, D₀ i k * K k l)
    {e : NovikovModule R F₂} (he : ∀ j, coordinates hF₂ r₂ e j = coefficientComparison q hq (E j))
    (hK : ∀ i l, ∀ A ∈ (K i l).support, μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₀ ⟨i, r₀ i⟩ + 1)
    (hm₀ : ∀ p p',
      mapKernelOfMatrix r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l)) p p' ≠ 0 →
        F₀ p' ≤ F₀ p + C₀)
    {i : ℤ} {a : NovikovModule R F₀}
    (ha : a ∈ (kernelMap hm₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).cocycles
      (gradeBy R F₀ fun p => n - μ₀ p) i) :
    novikovProductOfMatrix hF₀ hF₂ hF₀ r₀ r₂ r₀
        (fun i j k => coefficientComparison q hq (Q i j k)) a e - a ∈
      (kernelMap hm₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) i := by
  have h :=
    novikovProductOfMatrix_coefficientComparison_sub_novikovMapOfMatrix_mem_coboundaries_left
      r₀ r₂ r₀ hF₀ hF₂ hF₀ q hq hμ₀ hμ₀ Q E (1 : Matrix ι₀ ι₀ (NovikovSeries R G ωG)) K D₀ D₀
      hunit he hK hm₀ hm₀ ha
  let := module (R := R) hF₀
  rwa [novikovMapOfMatrix_coefficientComparison_one, LinearMap.id_apply] at h

end Cocycles

end TauCeti.Floer
