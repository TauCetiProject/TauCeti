/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CoefficientComparison
public import TauCeti.Geometry.Symplectic.Floer.Grading
public import TauCeti.RingTheory.NovikovModule.Bilinear
public import TauCeti.RingTheory.NovikovModule.Commutativity
public import TauCeti.RingTheory.NovikovModule.Continuation
public import TauCeti.RingTheory.NovikovModule.Associativity
public import TauCeti.RingTheory.NovikovModule.Leibniz
public import TauCeti.RingTheory.NovikovModule.Topology

/-!
# The pair-of-pants product of class-indexed counts on capped generators

Fix finitely many orbits for each end of the pair of pants, and a reference cap `rₗ` of each
orbit. Capped generators of an orbit form a torsor under the period group `Γ = PeriodGroup ω c`,
and their actions `F` obey the recapping law `F(γ # D) = F(D) + ω(γ)`. For each ordered triple
`(i, j, k)` of orbits, the rigid pairs of pants `u` with input orbits `γ₁ = i`, `γ₂ = j` and
output orbit `γ₀ = k` are counted in each class `A = D₀ + u - D₁ - D₂`, where `D₁`, `D₂`, `D₀` are
the reference caps: the caps cancel the boundary `γ₁ + γ₂ - γ₀` of `u`, so `A` is a closed class.
The class may be taken in any common class group `G` mapping to `Γ` by an area-preserving
homomorphism `q`; the counts are recorded by their generating series `Q i j k = ∑_A N_A q^A`, a
Novikov series in the area of `G`. That it is a Novikov series, that is, that only finitely many
classes below any area carry a nonzero count, is Gromov–Floer compactness below an energy level.

The *count matrix* `fun i j k => coefficientComparison q hq (Q i j k)` sends each generating
series to the Floer Novikov ring by the coefficient comparison `q^A ↦ e^(-q A)` of
`TauCeti.Floer.coefficientComparison`; by
`TauCeti.NovikovModule.coordinates_novikovProductOfMatrix_basis` it is the matrix of the product
in the reference basis. A pair of pants of class `A` with inputs the reference caps has glued
output cap `(-q A) # r₀`, so its contribution to the output in the reference basis is
`e^(-q A)`. The kernel of this matrix on capped generators
(`TauCeti.NovikovModule.kernelOfMatrix`) has as coefficient at `(D₁, D₂, D₀)` the finite sum of
the counts over the classes `A` with `q A = (D₁ - r₁) + (D₂ - r₂) - (D₀ - r₀)`
(`TauCeti.Floer.kernelOfMatrix_coefficientComparison_apply`), and its product
(`TauCeti.NovikovModule.novikovProductOfMatrix`) is a bilinear map over the Floer Novikov ring
on the completed capped modules. This file proves:

* **Support from the energy bound.** The energy of a pair of pants of class `A` is
  `E = F₁(r₁) + F₂(r₂) - F₀(r₀) + ω(A) - ∫ R_K`, so `E ≥ 0` and `∫ |R_K| ≤ C` give
  `ω(A) ≥ F₀(r₀) - F₁(r₁) - F₂(r₂) - C` whenever `N_A ≠ 0`, that is, `Q i j k` lies in the period
  filtration at this level. Under this hypothesis the matrix entries have a uniform lower
  valuation bound (`TauCeti.Floer.coefficientComparison_mem_periodFiltration`), so the kernel obeys
  the potential bound `F₀ ≤ F₁ + F₂ + C` on all capped generators and the product shifts action
  cutoffs by `C`
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_mem_potentialFiltration`).
* **Degree from the index.** If every counted class satisfies the rigidity condition
  `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n`, and the gradings obey the recapping law
  `μ(γ # D) = 2 c₁(γ) + μ(D)`, then the kernel has raw degree `-n` on all capped generators
  (`TauCeti.Floer.grading_eq_of_kernelOfMatrix_coefficientComparison_ne_zero`), and the product
  preserves the cochain degree `n - μ` and its residues
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_mem_map_cochain_gradeBy`).
* **Degree of cylinder counts from the index.** If every class counted by a matrix of cylinder
  counts `M` satisfies `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + ε`, its map sends cochain degree `e` to
  `e - ε` (`TauCeti.Floer.novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy`): `ε = -1`
  for the differential, `0` for continuation maps and `1` for homotopies.
* **Change of reference caps.** Moving the reference caps by lifts `g₁, g₂, g₀ ∈ G` multiplies
  the generating series by `q^(g₀ - g₁ - g₂)` and leaves the kernel, hence the product, unchanged
  (`TauCeti.Floer.kernelOfMatrix_coefficientComparison_vadd`).
* **The Leibniz rule from the count identity.** The rigid Floer cylinders between reference
  capped orbits of each end are counted in the same way, by generating series `Dₗ` whose
  comparisons are the matrices of the differentials on the completed capped modules
  (`TauCeti.NovikovModule.novikovMapOfMatrix`). If the series obey the identity
  `∑ₖ Qᵢⱼₖ D₀ₖₗ = ∑ₖ D₁ᵢₖ Qₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Qᵢₖₗ` given by the ends of the
  one-dimensional moduli spaces, then the product obeys `d (a ⋆ b) = d a ⋆ b + (-1)^e a ⋆ d b`
  for `a` of cochain degree `e`
  (`TauCeti.Floer.novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_eq_add`).
* **Graded commutativity from the count identity.** Let `Q'` be the generating series of the
  rigid pairs of pants with the two inputs exchanged, and `K` those of the rigid members of the
  input-exchange family. If the series obey the identity
  `Qᵢⱼₗ - (-1)^(e₁ e₂) Q'ⱼᵢₗ = ∑ₖ Kᵢⱼₖ D₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^e₁ ∑ₖ D₂ⱼₖ Kᵢₖₗ` given by the
  ends of the one-dimensional moduli spaces of the family, with `e₁ = n - μ₁(r₁ i)` and
  `e₂ = n - μ₂(r₂ j)`, then
  `a ⋆ b - (-1)^(e f) b ⋆' a = d₀ K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)`
  for `a` and `b` of cochain degrees `e` and `f`
  (`novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_coefficientComparison`).
  If moreover the classes counted by `K` satisfy the index condition of rigid members of the
  family, whose Fredholm index at a fixed parameter is `-1`, then `K` lowers the cochain degree by
  one, and for cocycles `a` and `b` the graded commutator is the coboundary of `K(a, b)`, so the
  two products agree on cohomology up to the sign `(-1)^(e f)`
  (`novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_mem_coboundaries`).
* **The associativity homotopy from the count identity.** The rigid elements of the
  one-parameter family of four-punctured spheres between the two broken triple products are
  counted by generating series `K` indexed by three input orbits and an output orbit; their
  comparisons define a trilinear map on the completed capped modules
  (`TauCeti.NovikovModule.novikovTrilinearOfMatrix`). Under the rigidity condition
  `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) + μ₃(r₃) - 2n + 1` it lowers the cochain degree by one
  (`TauCeti.Floer.novikovTrilinearOfMatrix_coefficientComparison_mem_map_cochain_gradeBy`). If
  the series obey the identity given by the ends of the one-dimensional moduli spaces of the
  family, the two broken products and the cylinder breakings at the four ends, then
  `(a ⋆ b) ⋆' c - a ⋆''' (b ⋆'' c) = d K(a, b, c) + K(d a, b, c) + (-1)^e₁ K(a, d b, c) +
  (-1)^(e₁ + e₂) K(a, b, d c)` for `a`, `b` of cochain degrees `e₁`, `e₂`
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_assoc_sub_eq_add`).
* **Associativity on cohomology.** If moreover the classes counted by `K` satisfy the index
  condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) + μ₃(r₃) - 2n + 1`, then for cocycles of the
  cylinder differentials the difference of the two bracketings is the coboundary of
  `K(x₁, x₂, x₃)`
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_assoc_sub_mem_coboundaries`), so
  the products induced on the cohomology of the cylinder differentials are associative,
  `([x] ⋆ [y]) ⋆' [z] = [x] ⋆''' ([y] ⋆'' [z])`
  (`TauCeti.Floer.cohomologyProduct_kernelProduct_coefficientComparison_assoc`).
* **Compatibility with continuation maps from the count identity.** Let `Q'` be the generating
  series of the rigid pairs of pants for a second choice of end Hamiltonians, `Φ₁`, `Φ₂`, `Φ₀`
  those of the rigid continuation cylinders from the orbits of each end of the first choice to
  those of the second, and `K` those of the rigid members of the continuation family of pairs of
  pants. If the series obey the identity
  `∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ₛ ∑ₜ Φ₁ᵢₛ Φ₂ⱼₜ Q'ₛₜₗ = ∑ₘ Kᵢⱼₘ D₀'ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₗ + (-1)^e₁ ∑ₘ D₂ⱼₘ Kᵢₘₗ`
  given by the ends of the one-dimensional moduli spaces of the family, with `e₁ = n - μ₁(r₁ i)`
  and `D₀'` the cylinder counts of the output of the second choice, then
  `Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = d₀' K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` for `a` of cochain
  degree `e` (`novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`). If
  moreover the classes counted by `K` satisfy the index condition of rigid members of the family,
  then for cocycles `a` and `b` the difference is the coboundary of `K(a, b)`, so the two
  composites agree on cohomology
  (`novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries`).

The energy, compactness, index and boundary-count hypotheses are the ones the geometric moduli
spaces are to supply; no moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich, 1995, for the associativity of the pair-of-pants product.
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

section Recapping

variable {ι : Type*} {P : ι → Type*} [∀ i, AddTorsor (PeriodGroup ω c) (P i)]
  {μ : (Σ i, P i) → ℤ} (hμ : ∀ i γ (D : P i), μ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ ⟨i, D⟩) (n : ℤ)

include hμ

/-- Recapping by `γ` changes the cochain degree `n - μ` by the even number `-2 c₁(γ)`. -/
private theorem even_cochain_vadd_sub (i : ι) (γ : PeriodGroup ω c) (D : P i) :
    Even (n - μ ⟨i, γ +ᵥ D⟩ - (n - μ ⟨i, D⟩)) := by
  rw [hμ, show n - (degree ω c γ + μ ⟨i, D⟩) - (n - μ ⟨i, D⟩) = -degree ω c γ by ring]
  exact (even_degree ω c γ).neg

/-- Recapping by `γ` adds `f (-2 c₁(γ))` to any additive image `f` of the cochain degree. -/
private theorem map_cochain_vadd {D : Type*} [AddCommMonoid D] (f : ℤ →+ D) (i : ι)
    (γ : PeriodGroup ω c) (E : P i) :
    f (n - μ ⟨i, γ +ᵥ E⟩) = (f.comp (-degree ω c)) γ + f (n - μ ⟨i, E⟩) := by
  rw [hμ, AddMonoidHom.comp_apply, AddMonoidHom.neg_apply, ← map_add]
  congr 1
  ring

end Recapping

section Monoid

variable {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

section Semiring

variable [Semiring R]

/-- **The kernel of class-indexed counts on capped generators.** Its coefficient at capped
generators `D₁`, `D₂`, `D₀` of the orbits `i`, `j`, `k` is the finite sum of the counts over all
classes `A` with `q A = (D₁ - r₁) + (D₂ - r₂) - (D₀ - r₀)`: the pairs of pants whose glued output
cap is `D₀`. -/
theorem kernelOfMatrix_coefficientComparison_apply (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG)
    {i : ι₁} {j : ι₂} {k : ι₀} (D₁ : P₁ i) (D₂ : P₂ j) (D₀ : P₀ k) :
    kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
        ⟨i, D₁⟩ ⟨j, D₂⟩ ⟨k, D₀⟩ =
      ∑ᶠ A ∈ q ⁻¹' {(D₁ -ᵥ r₁ i) + (D₂ -ᵥ r₂ j) - (D₀ -ᵥ r₀ k)}, (Q i j k).coeff A := by
  rw [kernelOfMatrix_apply, coefficientComparison_apply, coeff_map]
  refine finsum_mem_congr ?_ fun _ _ => rfl
  ext A
  simp only [Set.mem_preimage, Set.mem_singleton_iff, AddMonoidHom.neg_apply,
    neg_eq_iff_eq_neg, neg_sub]
  exact iff_of_eq (congrArg _ (by abel))

/-- If `q` is injective, for instance for counts indexed by the period group itself, the kernel
of class-indexed counts is the count in the single class
`q A = (D₁ - r₁) + (D₂ - r₂) - (D₀ - r₀)`. -/
theorem kernelOfMatrix_coefficientComparison_apply_of_injective
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (hqi : Function.Injective q) {i : ι₁} {j : ι₂}
    {k : ι₀} (D₁ : P₁ i) (D₂ : P₂ j) (D₀ : P₀ k)
    {A : G} (hA : q A = (D₁ -ᵥ r₁ i) + (D₂ -ᵥ r₂ j) - (D₀ -ᵥ r₀ k)) :
    kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
        ⟨i, D₁⟩ ⟨j, D₂⟩ ⟨k, D₀⟩ = (Q i j k).coeff A := by
  rw [kernelOfMatrix_coefficientComparison_apply, ← hA, ← Set.image_singleton,
    hqi.preimage_image, finsum_mem_singleton]

end Semiring

section Grading

variable [Semiring R] {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  {n : ℤ} {Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG}
  (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
    μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n)

include hμ₁ hμ₂ hμ₀ hQ

/-- **Degree of the kernel from the index.** If the gradings obey the recapping law and every
class with nonzero count satisfies the rigidity condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n`
relative to the reference caps, then the kernel has raw degree `-n` at all capped generators. -/
theorem grading_eq_of_kernelOfMatrix_coefficientComparison_ne_zero (p₁ : Σ i, P₁ i)
    (p₂ : Σ j, P₂ j) (p₀ : Σ k, P₀ k)
    (h : kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k)) p₁ p₂ p₀ ≠ 0) :
    μ₀ p₀ = μ₁ p₁ + μ₂ p₂ - n := by
  obtain ⟨i, D₁⟩ := p₁
  obtain ⟨j, D₂⟩ := p₂
  obtain ⟨k, D₀⟩ := p₀
  rw [kernelOfMatrix_coefficientComparison_apply] at h
  obtain ⟨A, hA, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero h
  have hd := hQ i j k A (mem_support.2 hne)
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hA
  rw [hA, map_sub, map_add] at hd
  have e₁ := hμ₁ i (D₁ -ᵥ r₁ i) (r₁ i)
  have e₂ := hμ₂ j (D₂ -ᵥ r₂ j) (r₂ j)
  have e₀ := hμ₀ k (D₀ -ᵥ r₀ k) (r₀ k)
  rw [vsub_vadd] at e₁ e₂ e₀
  linarith

end Grading

section Map

variable {μ₁ : (Σ i, P₁ i) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩) {ε : ℤ}

section Semiring

variable [Semiring R]

/-- **The kernel of class-indexed counts of cylinders on capped generators.** Its coefficient at
capped generators `D₁` and `D₀` of the orbits `i` and `k` is the finite sum of the counts over all
classes `A` with `q A = (D₁ - r₁) - (D₀ - r₀)`: the cylinders from `D₁` whose glued output cap is
`D₀`. -/
theorem mapKernelOfMatrix_coefficientComparison_apply (M : ι₁ → ι₀ → NovikovSeries R G ωG)
    {i : ι₁} {k : ι₀} (D₁ : P₁ i) (D₀ : P₀ k) :
    mapKernelOfMatrix r₁ r₀ (fun i k => coefficientComparison q hq (M i k)) ⟨i, D₁⟩ ⟨k, D₀⟩ =
      ∑ᶠ A ∈ q ⁻¹' {(D₁ -ᵥ r₁ i) - (D₀ -ᵥ r₀ k)}, (M i k).coeff A := by
  refine (mapKernelOfMatrix_apply r₁ r₀ _ D₁ D₀).trans ?_
  rw [coefficientComparison_apply, coeff_map]
  refine finsum_mem_congr ?_ fun _ _ => rfl
  ext A
  simp only [Set.mem_preimage, Set.mem_singleton_iff, AddMonoidHom.neg_apply,
    neg_eq_iff_eq_neg, neg_sub]

include hμ₁ hμ₀ in
/-- **Degree of the kernel of cylinder counts from the index.** If the gradings obey the recapping
law and every class with nonzero count satisfies `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + ε` relative to the
reference caps, then the kernel has raw degree `ε` at all capped generators. For rigid
continuation cylinders `ε = 0`, for rigid Floer cylinders `ε = -1`, and for the rigid members of a
one-parameter family of cylinders `ε = 1`. -/
theorem grading_eq_of_mapKernelOfMatrix_coefficientComparison_ne_zero
    {M : ι₁ → ι₀ → NovikovSeries R G ωG}
    (hM : ∀ i k, ∀ A ∈ (M i k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + ε)
    (p₁ : Σ i, P₁ i) (p₀ : Σ k, P₀ k)
    (h : mapKernelOfMatrix r₁ r₀ (fun i k => coefficientComparison q hq (M i k)) p₁ p₀ ≠ 0) :
    μ₀ p₀ = μ₁ p₁ + ε := by
  obtain ⟨i, D₁⟩ := p₁
  obtain ⟨k, D₀⟩ := p₀
  rw [mapKernelOfMatrix_coefficientComparison_apply] at h
  obtain ⟨A, hA, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero h
  have hd := hM i k A (mem_support.2 hne)
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hA
  rw [hA, map_sub] at hd
  have e₁ := hμ₁ i (D₁ -ᵥ r₁ i) (r₁ i)
  have e₀ := hμ₀ k (D₀ -ᵥ r₀ k) (r₀ k)
  rw [vsub_vadd] at e₁ e₀
  linarith

end Semiring

include hμ₁ hμ₀ in
/-- **The map of cylinder counts shifts cochain degree.** Under the index condition of
`TauCeti.Floer.grading_eq_of_mapKernelOfMatrix_coefficientComparison_ne_zero`, the map of
class-indexed counts sends combinations of cochain degree `e = n - μ₁` to combinations of cochain
degree `e - ε`. -/
theorem novikovMapOfMatrix_coefficientComparison_mem_cochain_gradeBy [CommSemiring R]
    [Finite ι₁] [Finite ι₀] {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
    (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
    (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
    {M : ι₁ → ι₀ → NovikovSeries R G ωG}
    (hM : ∀ i k, ∀ A ∈ (M i k).support, μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + ε)
    {n e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e) :
    novikovMapOfMatrix hF₁ hF₀ r₁ r₀ (fun i k => coefficientComparison q hq (M i k)) a ∈
      gradeBy R F₀ (fun p => n - μ₀ p) (e - ε) := by
  obtain ⟨C, hm⟩ := exists_potential_le_of_mapKernelOfMatrix_ne_zero hF₁ hF₀ r₁ r₀
    (fun i k => coefficientComparison q hq (M i k))
  rw [novikovMapOfMatrix_eq_kernelMap hF₁ hF₀ r₁ r₀ _ hm, sub_eq_add_neg]
  refine kernelMap_mem_gradeBy _ _ (fun p₁ p₀ h => ?_) ha
  rw [grading_eq_of_mapKernelOfMatrix_coefficientComparison_ne_zero r₁ r₀ q hq hμ₁ hμ₀ hM p₁ p₀ h]
  ring

end Map

section Product

variable [Finite ι₁] [Finite ι₂] [Finite ι₀] {F₁ : (Σ i, P₁ i) → ℝ}
  {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)

/-- **The product of class-indexed counts.** If the counts satisfy the energy bound with
curvature constant `C`, their product on capped generators is the kernel product of their kernel
with that constant, so it shifts action cutoffs by `C`: if `a` and `b` vanish above the actions
`D₁` and `D₂`, then their product vanishes above `D₁ + D₂ + C`. -/
theorem novikovProductOfMatrix_coefficientComparison_mem_potentialFiltration [CommRing R]
    {Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG} {C : ℝ}
    (hE : ∀ i j k,
      Q i j k ∈ periodFiltration R ωG (F₀ ⟨k, r₀ k⟩ - F₁ ⟨i, r₁ i⟩ - F₂ ⟨j, r₂ j⟩ - C))
    {D₁ D₂ : ℝ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ potentialFiltration R F₁ D₁) (hb : b ∈ potentialFiltration R F₂ D₂) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (Q i j k)) a b ∈
      potentialFiltration R F₀ (D₁ + D₂ + C) := by
  have hn := potential_le_of_kernelOfMatrix_ne_zero hF₁ hF₂ hF₀ r₁ r₂ r₀
    (fun i j k => coefficientComparison_mem_periodFiltration q hq (hE i j k))
  rw [novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ hF₀ r₁ r₂ r₀ _ hn]
  exact kernelProduct_mem_potentialFiltration hn _ ha hb

variable [CommSemiring R] {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ} {μ₀ : (Σ k, P₀ k) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
  {n : ℤ} (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG)
  (hQ : ∀ i j k, ∀ A ∈ (Q i j k).support,
    μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n)

include hμ₁ hμ₂ hμ₀ hQ

/-- **The product of rigid counts preserves cochain degree.** Under the rigidity condition of
`TauCeti.Floer.grading_eq_of_kernelOfMatrix_coefficientComparison_ne_zero`, the product of
class-indexed counts is additive in every additive image `f` of the cochain degree `n - μ`; for
`f` the quotient map modulo the degrees of the period group this is the residue grading. -/
theorem novikovProductOfMatrix_coefficientComparison_mem_map_cochain_gradeBy {D : Type*}
    [AddMonoid D] (f : ℤ →+ D) {i' j' : D} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ (fun p => f (n - μ₁ p)) i')
    (hb : b ∈ gradeBy R F₂ (fun p => f (n - μ₂ p)) j') :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (Q i j k)) a b ∈
      gradeBy R F₀ (fun p => f (n - μ₀ p)) (i' + j') := by
  obtain ⟨C, hn⟩ := exists_potential_le_of_kernelOfMatrix_ne_zero hF₁ hF₂ hF₀ r₁ r₂ r₀
    (fun i j k => coefficientComparison q hq (Q i j k))
  rw [novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ hF₀ r₁ r₂ r₀ _ hn]
  exact kernelProduct_mem_map_cochain_gradeBy hn _
    (grading_eq_of_kernelOfMatrix_coefficientComparison_ne_zero r₁ r₂ r₀ q hq hμ₁ hμ₂ hμ₀ hQ) f
    ha hb

/-- The product of rigid class-indexed counts has degree zero on capped generators regraded by
the cochain degree `n - μ`. -/
theorem novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy {i' j' : ℤ}
    {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i') (hb : b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j') :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (Q i j k)) a b ∈
      gradeBy R F₀ (fun p => n - μ₀ p) (i' + j') :=
  novikovProductOfMatrix_coefficientComparison_mem_map_cochain_gradeBy r₁ r₂ r₀ q hq hF₁ hF₂ hF₀
    hμ₁ hμ₂ hμ₀ Q hQ (AddMonoidHom.id ℤ) ha hb

end Product

section Leibniz

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] {F₁ : (Σ i, P₁ i) → ℝ}
  {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)

include hμ₁ in
/-- **The Leibniz rule for class-indexed counts.** Let `Q` be the generating series of rigid
pairs of pants between reference capped orbits, and `D₁`, `D₂`, `D₀` those of rigid Floer
cylinders of the two inputs and the output, all indexed by a common class group `G`. Suppose the
series obey the identity

`∑ₖ Qᵢⱼₖ D₀ₖₗ = ∑ₖ D₁ᵢₖ Qₖⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₖ D₂ⱼₖ Qᵢₖₗ`

in `G`-indexed series, which is the count, class by class, of the ends of one-dimensional
pair-of-pants moduli spaces between reference capped orbits. Then on the completed capped
modules, with the first input graded by the cochain degree `n - μ₁`, the product and the maps of
the cylinder counts obey `d₀ (a ⋆ b) = d₁ a ⋆ b + (-1)^e a ⋆ d₂ b` for every `a` of degree `e`.
The sign is constant on the capped generators of each orbit, because recapping changes the degree
by the even number `2 c₁(γ)`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_eq_add
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG) (n : ℤ)
    (hL : ∀ i j l, ∑ k, Q i j k * D₀ k l =
      ∑ k, D₁ i k * Q k j l + negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * Q i k l)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂) :
    novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
        (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a b) =
      novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k))
            b) := by
  refine novikovMapOfMatrix_novikovProductOfMatrix_eq_add hF₁ hF₂ hF₀ r₁ r₂ r₀ _ _ _ _
    (even_cochain_vadd_sub hμ₁ n) (fun i j l => ?_) ha b
  have h := congrArg (coefficientComparison q hq) (hL i j l)
  simp only [map_sum, map_add, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
    Units.smul_def, map_zsmul] at h ⊢
  exact h

end Leibniz

section Commutativity

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] {F₁ : (Σ i, P₁ i) → ℝ}
  {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Q' : ι₂ → ι₁ → ι₀ → NovikovSeries R G ωG)
  (K : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
  (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG) (n : ℤ)

include hμ₁ hμ₂ in
/-- **Graded commutativity of class-indexed counts up to homotopy.** Let `Q` be the generating
series of rigid pairs of pants between reference capped orbits, `Q'` those of the rigid pairs of
pants with the two inputs exchanged, `K` those of the rigid members of the input-exchange family,
and `D₁`, `D₂`, `D₀` those of rigid Floer cylinders of the two inputs and the output, all indexed by
a common class group `G`. Suppose the series obey the identity

`Qᵢⱼₗ - (-1)^(e₁ e₂) Q'ⱼᵢₗ = ∑ₖ Kᵢⱼₖ D₀ₖₗ + ∑ₖ D₁ᵢₖ Kₖⱼₗ + (-1)^e₁ ∑ₖ D₂ⱼₖ Kᵢₖₗ`

in `G`-indexed series, where `e₁ = n - μ₁(r₁ i)` and `e₂ = n - μ₂(r₂ j)` are the cochain degrees
of the reference caps. This is the count, class by class, of the ends of the one-dimensional moduli
spaces of the input-exchange family between reference capped orbits. Then on the completed capped
modules, graded by the cochain degrees `n - μ₁` and `n - μ₂`, the product, the product with
exchanged inputs and the operation `K` of the family obey
`a ⋆ b - (-1)^(e f) b ⋆' a = d₀ K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` for `a` of degree `e` and
`b` of degree `f`. The signs are constant on the capped generators of each orbit, because recapping
changes the degree by the even number `2 c₁(γ)`. -/
theorem
    novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_coefficientComparison
    (hC : ∀ i j l, Q i j l -
        negOnePowCast R ((n - μ₁ ⟨i, r₁ i⟩) * (n - μ₂ ⟨j, r₂ j⟩)) • Q' j i l =
      ∑ k, K i j k * D₀ k l + ∑ k, D₁ i k * K k j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ k, D₂ j k * K i k l)
    {e f : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e) (hb : b ∈ gradeBy R F₂ (fun p => n - μ₂ p) f) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (Q i j k)) a b -
        negOnePowCast R (e * f) • novikovProductOfMatrix hF₂ hF₁ hF₀ r₂ r₁ r₀
          (fun j i k => coefficientComparison q hq (Q' j i k)) b a =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun k l => coefficientComparison q hq (D₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (K i j k)) a b) +
        novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (K i j k))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
          (fun i j k => coefficientComparison q hq (K i j k)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k))
            b) := by
  -- Recapping changes the cochain degree by the even number `-2 c₁(γ)`.
  refine novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix hF₁ hF₂ hF₀
    r₁ r₂ r₀ _ _ _ _ _ _ (fun i γ D => ?_) (fun j γ D => ?_) (fun i j l => ?_) ha hb
  · rw [hμ₁, show n - (degree ω c γ + μ₁ ⟨i, D⟩) - (n - μ₁ ⟨i, D⟩) = -degree ω c γ by ring]
    exact (even_degree ω c γ).neg
  · rw [hμ₂, show n - (degree ω c γ + μ₂ ⟨j, D⟩) - (n - μ₂ ⟨j, D⟩) = -degree ω c γ by ring]
    exact (even_degree ω c γ).neg
  · have h := congrArg (coefficientComparison q hq) (hC i j l)
    simp only [map_sum, map_add, map_sub, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
      Units.smul_def, map_zsmul] at h ⊢
    exact h

include hμ₁ hμ₂ in
/-- **Graded commutativity of class-indexed counts on cohomology.** Under the identity of
`novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_coefficientComparison`,
suppose that every class counted by `K` satisfies the index condition
`μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n + 1` of rigid members of the input-exchange family, whose
Fredholm index at a fixed parameter is `-1`, so that `K` lowers the cochain degree by one. Then
for cocycles `a` and `b` of the cylinder differentials, of cochain degrees `e` and `f`, the graded
commutator `a ⋆ b - (-1)^(e f) b ⋆' a` is the coboundary of `K(a, b)` in cochain degree `e + f`.
The differentials are the ground-ring linear maps of the cylinder counts, for any potential bounds
of their kernels. -/
theorem novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_mem_coboundaries
    {μ₀ : (Σ k, P₀ k) → ℤ} (hμ₀ : ∀ k γ (D : P₀ k), μ₀ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨k, D⟩)
    (hK : ∀ i j k, ∀ A ∈ (K i j k).support,
      μ₀ ⟨k, r₀ k⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    (hC : ∀ i j l, Q i j l -
        negOnePowCast R ((n - μ₁ ⟨i, r₁ i⟩) * (n - μ₂ ⟨j, r₂ j⟩)) • Q' j i l =
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
        negOnePowCast R (e * f) • novikovProductOfMatrix hF₂ hF₁ hF₀ r₂ r₁ r₀
          (fun j i k => coefficientComparison q hq (Q' j i k)) b a ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) (e + f) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  have hDa : novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i k => coefficientComparison q hq (D₁ i k)) a =
      0 := by
    rw [novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁]
    exact ha.1
  have hDb : novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j k => coefficientComparison q hq (D₂ j k)) b =
      0 := by
    rw [novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂ _ hδ₂]
    exact hb.1
  -- `K` is the product of rigid counts for the gradings `μ₀ - 1`, so `K(a, b)` has cochain
  -- degree `e + f - 1`.
  have hKab := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ r₀ q hq hF₁
    hF₂ hF₀ hμ₁ hμ₂ (μ₀ := fun p => μ₀ p - 1) (fun k γ D => by rw [hμ₀]; ring) K
    (fun i j k A hA => by linarith [hK i j k A hA]) ha.2 hb.2
  have hdeg : ((fun x : ℤ => x - 1) ∘ fun p => n - (μ₀ p - 1)) = fun p => n - μ₀ p := by
    funext p
    simp only [Function.comp_apply]
    ring
  have hKab' := gradeBy_le_gradeBy_comp (R := R) (fun x : ℤ => x - 1) (e + f) hKab
  rw [hdeg] at hKab'
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, hKab', ?_⟩
  -- The Novikov module structures, for the vanishing of the products with `d₁ a = 0`, `d₂ b = 0`.
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₀
  rw [novikovProductOfMatrix_sub_negOnePowCast_smul_novikovProductOfMatrix_coefficientComparison
      r₁ r₂ r₀ q hq hF₁ hF₂ hF₀ hμ₁ hμ₂ Q Q' K D₁ D₂ D₀ n hC ha.2 hb.2,
    hDa, hDb, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀]

end Commutativity

section Associativity

variable {ι₃ ι₁₂ ι₂₃ : Type*} {P₃ : ι₃ → Type*} {P₁₂ : ι₁₂ → Type*} {P₂₃ : ι₂₃ → Type*}
  [∀ k, AddTorsor (PeriodGroup ω c) (P₃ k)] [∀ t, AddTorsor (PeriodGroup ω c) (P₁₂ t)]
  [∀ u, AddTorsor (PeriodGroup ω c) (P₂₃ u)]
  (r₃ : ∀ k, P₃ k) (r₁₂ : ∀ t, P₁₂ t) (r₂₃ : ∀ u, P₂₃ u)
  [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₀] {F₁ : (Σ i, P₁ i) → ℝ}
  {F₂ : (Σ j, P₂ j) → ℝ} {F₃ : (Σ k, P₃ k) → ℝ} {F₀ : (Σ l, P₀ l) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₃ : ∀ k γ (D : P₃ k), F₃ ⟨k, γ +ᵥ D⟩ = F₃ ⟨k, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ l γ (D : P₀ l), F₀ ⟨l, γ +ᵥ D⟩ = F₀ ⟨l, D⟩ - (-area ω c) γ)
  {μ₁ : (Σ i, P₁ i) → ℤ} {μ₂ : (Σ j, P₂ j) → ℤ}
  (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)

section Degree

variable [CommSemiring R] {μ₃ : (Σ k, P₃ k) → ℤ} {μ₀ : (Σ l, P₀ l) → ℤ}
  (hμ₃ : ∀ k γ (D : P₃ k), μ₃ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₃ ⟨k, D⟩)
  (hμ₀ : ∀ l γ (D : P₀ l), μ₀ ⟨l, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨l, D⟩)
  {n : ℤ} (K : ι₁ → ι₂ → ι₃ → ι₀ → NovikovSeries R G ωG)
  (hK : ∀ i j k l, ∀ A ∈ (K i j k l).support,
    μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ + μ₃ ⟨k, r₃ k⟩ - 2 * n + 1)

include hμ₁ hμ₂ hμ₃ hμ₀ hK

/-- **The homotopy of rigid counts lowers cochain degree by one.** Let `K` be the generating
series of the rigid elements of a one-parameter family of four-punctured spheres with three
inputs, between reference capped orbits. If every class with nonzero count satisfies the rigidity
condition `μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) + μ₃(r₃) - 2n + 1`, and the gradings obey the
recapping law, then the trilinear map of the counts on capped generators shifts every additive
image `f` of the cochain degree `n - μ` by `f (-1)`. -/
theorem novikovTrilinearOfMatrix_coefficientComparison_mem_map_cochain_gradeBy {D : Type*}
    [AddCommGroup D] (f : ℤ →+ D) {e₁ e₂ e₃ : D} {x₁ : NovikovModule R F₁}
    {x₂ : NovikovModule R F₂} {x₃ : NovikovModule R F₃}
    (ha : x₁ ∈ gradeBy R F₁ (fun p => f (n - μ₁ p)) e₁)
    (hb : x₂ ∈ gradeBy R F₂ (fun p => f (n - μ₂ p)) e₂)
    (hc : x₃ ∈ gradeBy R F₃ (fun p => f (n - μ₃ p)) e₃) :
    novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
        (fun i j k l => coefficientComparison q hq (K i j k l)) x₁ x₂ x₃ ∈
      gradeBy R F₀ (fun p => f (n - μ₀ p)) (e₁ + e₂ + e₃ + f (-1)) := by
  refine novikovTrilinearOfMatrix_mem_gradeBy hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀ _ (f.comp (-degree ω c))
    (map_cochain_vadd hμ₁ n f) (map_cochain_vadd hμ₂ n f) (map_cochain_vadd hμ₃ n f)
    (map_cochain_vadd hμ₀ n f) (fun i j k l => NovikovSeries.mem_gradeBy_iff.2 fun γ hγ => ?_)
    ha hb hc
  obtain ⟨A, hA, rfl⟩ := support_coefficientComparison_subset q hq _ hγ
  have hd : degree ω c (q A) = n - μ₁ ⟨i, r₁ i⟩ + (n - μ₂ ⟨j, r₂ j⟩) + (n - μ₃ ⟨k, r₃ k⟩) + -1 -
      (n - μ₀ ⟨l, r₀ l⟩) := by
    linarith [hK i j k l A hA]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, AddMonoidHom.comp_apply,
    AddMonoidHom.neg_apply, map_neg, neg_neg, hd, map_sub, map_add]

/-- The trilinear map of rigid homotopy counts has degree `-1` on capped generators regraded by
the cochain degree `n - μ`. -/
theorem novikovTrilinearOfMatrix_coefficientComparison_mem_cochain_gradeBy {e₁ e₂ e₃ : ℤ}
    {x₁ : NovikovModule R F₁} {x₂ : NovikovModule R F₂} {x₃ : NovikovModule R F₃}
    (ha : x₁ ∈ gradeBy R F₁ (fun p => n - μ₁ p) e₁) (hb : x₂ ∈ gradeBy R F₂ (fun p => n - μ₂ p) e₂)
    (hc : x₃ ∈ gradeBy R F₃ (fun p => n - μ₃ p) e₃) :
    novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
        (fun i j k l => coefficientComparison q hq (K i j k l)) x₁ x₂ x₃ ∈
      gradeBy R F₀ (fun p => n - μ₀ p) (e₁ + e₂ + e₃ - 1) :=
  novikovTrilinearOfMatrix_coefficientComparison_mem_map_cochain_gradeBy r₁ r₂ r₀ q hq r₃ hF₁ hF₂
    hF₃ hF₀ hμ₁ hμ₂ hμ₃ hμ₀ K hK (AddMonoidHom.id ℤ) ha hb hc

end Degree

variable [CommRing R] [Fintype ι₁₂] [Fintype ι₂₃] {F₁₂ : (Σ t, P₁₂ t) → ℝ}
  {F₂₃ : (Σ u, P₂₃ u) → ℝ}
  (hF₁₂ : ∀ t γ (D : P₁₂ t), F₁₂ ⟨t, γ +ᵥ D⟩ = F₁₂ ⟨t, D⟩ - (-area ω c) γ)
  (hF₂₃ : ∀ u γ (D : P₂₃ u), F₂₃ ⟨u, γ +ᵥ D⟩ = F₂₃ ⟨u, D⟩ - (-area ω c) γ)

include hμ₁ hμ₂ in
/-- **The associativity homotopy for class-indexed counts.** Let `Q`, `Q'` be the generating
series of rigid pairs of pants for the products in `(x₁ ⋆ x₂) ⋆' x₃`, and `T`, `T'` those for the
products in `x₁ ⋆''' (x₂ ⋆'' x₃)`. Let `D₁`, `D₂`, `D₃`, `D₀` be those of rigid Floer cylinders of
the three inputs and the output, and `K` that of the rigid elements of the one-parameter family of
four-punctured spheres between the two broken configurations, all between reference capped orbits
and indexed by a common class group `G`. Suppose the series obey the identity

`∑ₜ Qᵢⱼₜ Q'ₜₖₗ - ∑ᵤ Tⱼₖᵤ T'ᵢᵤₗ = ∑ₘ Kᵢⱼₖₘ D₀ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₖₗ +
  (-1)^(n - μ₁(r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₖₗ + (-1)^((n - μ₁(r₁ i)) + (n - μ₂(r₂ j))) ∑ₘ D₃ₖₘ Kᵢⱼₘₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional
moduli spaces of the family: the two broken products and the breaking of a Floer cylinder at one
of the four ends. Then on the completed capped modules, with the first two inputs graded by the
cochain degrees `n - μ₁` and `n - μ₂`, the trilinear map of `K` is a homotopy between the two
products: `(x₁ ⋆ x₂) ⋆' x₃ - x₁ ⋆''' (x₂ ⋆'' x₃) = d₀ K(x₁, x₂, x₃) + K(d₁ x₁, x₂, x₃) +
(-1)^e₁ K(x₁, d₂ x₂, x₃) + (-1)^(e₁ + e₂) K(x₁, x₂, d₃ x₃)` for `x₁` of degree `e₁` and `x₂` of
degree `e₂`. The signs are constant on the capped generators of each orbit, because recapping
changes the degree by the even number `2 c₁(γ)`. -/
theorem novikovProductOfMatrix_coefficientComparison_assoc_sub_eq_add
    (Q : ι₁ → ι₂ → ι₁₂ → NovikovSeries R G ωG) (Q' : ι₁₂ → ι₃ → ι₀ → NovikovSeries R G ωG)
    (T : ι₂ → ι₃ → ι₂₃ → NovikovSeries R G ωG) (T' : ι₁ → ι₂₃ → ι₀ → NovikovSeries R G ωG)
    (K : ι₁ → ι₂ → ι₃ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
    (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₃ : ι₃ → ι₃ → NovikovSeries R G ωG)
    (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG) (n : ℤ)
    (hA : ∀ i j k l, ∑ t, Q i j t * Q' t k l - ∑ u, T j k u * T' i u l =
      ∑ m, K i j k m * D₀ m l + ∑ m, D₁ i m * K m j k l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m k l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩ + (n - μ₂ ⟨j, r₂ j⟩)) • ∑ m, D₃ k m * K i j m l)
    {e₁ e₂ : ℤ} {x₁ : NovikovModule R F₁} (ha : x₁ ∈ gradeBy R F₁ (fun p => n - μ₁ p) e₁)
    {x₂ : NovikovModule R F₂} (hb : x₂ ∈ gradeBy R F₂ (fun p => n - μ₂ p) e₂)
    (x₃ : NovikovModule R F₃) :
    novikovProductOfMatrix hF₁₂ hF₃ hF₀ r₁₂ r₃ r₀
          (fun t k l => coefficientComparison q hq (Q' t k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₁₂ r₁ r₂ r₁₂
            (fun i j t => coefficientComparison q hq (Q i j t)) x₁ x₂) x₃ -
        novikovProductOfMatrix hF₁ hF₂₃ hF₀ r₁ r₂₃ r₀
          (fun i u l => coefficientComparison q hq (T' i u l)) x₁
          (novikovProductOfMatrix hF₂ hF₃ hF₂₃ r₂ r₃ r₂₃
            (fun j k u => coefficientComparison q hq (T j k u)) x₂ x₃) =
      novikovMapOfMatrix hF₀ hF₀ r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l))
          (novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
            (fun i j k l => coefficientComparison q hq (K i j k l)) x₁ x₂ x₃) +
        novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
          (fun i j k l => coefficientComparison q hq (K i j k l))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m)) x₁)
          x₂ x₃ +
        negOnePowCast R e₁ • novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
          (fun i j k l => coefficientComparison q hq (K i j k l)) x₁
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m)) x₂)
          x₃ +
        negOnePowCast R (e₁ + e₂) • novikovTrilinearOfMatrix hF₁ hF₂ hF₃ hF₀ r₁ r₂ r₃ r₀
          (fun i j k l => coefficientComparison q hq (K i j k l)) x₁ x₂
          (novikovMapOfMatrix hF₃ hF₃ r₃ r₃ (fun k m => coefficientComparison q hq (D₃ k m))
            x₃) := by
  refine novikovProductOfMatrix_assoc_sub_eq_add hF₁ hF₂ hF₃ hF₀ hF₁₂ hF₂₃ r₁ r₂ r₃ r₀ r₁₂ r₂₃
    _ _ _ _ _ _ _ _ _ (even_cochain_vadd_sub hμ₁ n) (even_cochain_vadd_sub hμ₂ n)
    (fun i j k l => ?_) ha hb x₃
  have h := congrArg (coefficientComparison q hq) (hA i j k l)
  simp only [map_sum, map_add, map_sub, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
    Units.smul_def, map_zsmul] at h ⊢
  exact h

section Cohomology

variable {μ₃ : (Σ k, P₃ k) → ℤ} {μ₀ : (Σ l, P₀ l) → ℤ}
  (hμ₃ : ∀ k γ (D : P₃ k), μ₃ ⟨k, γ +ᵥ D⟩ = degree ω c γ + μ₃ ⟨k, D⟩)
  (hμ₀ : ∀ l γ (D : P₀ l), μ₀ ⟨l, γ +ᵥ D⟩ = degree ω c γ + μ₀ ⟨l, D⟩)
  (Q : ι₁ → ι₂ → ι₁₂ → NovikovSeries R G ωG) (Q' : ι₁₂ → ι₃ → ι₀ → NovikovSeries R G ωG)
  (T : ι₂ → ι₃ → ι₂₃ → NovikovSeries R G ωG) (T' : ι₁ → ι₂₃ → ι₀ → NovikovSeries R G ωG)
  (K : ι₁ → ι₂ → ι₃ → ι₀ → NovikovSeries R G ωG) (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG)
  (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG) (D₃ : ι₃ → ι₃ → NovikovSeries R G ωG)
  (D₀ : ι₀ → ι₀ → NovikovSeries R G ωG) (n : ℤ) {C₁ C₂ C₃ C₀ : ℝ}
  (hδ₁ : ∀ p p',
    mapKernelOfMatrix r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m)) p p' ≠ 0 →
      F₁ p' ≤ F₁ p + C₁)
  (hδ₂ : ∀ p p',
    mapKernelOfMatrix r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m)) p p' ≠ 0 →
      F₂ p' ≤ F₂ p + C₂)
  (hδ₃ : ∀ p p',
    mapKernelOfMatrix r₃ r₃ (fun k m => coefficientComparison q hq (D₃ k m)) p p' ≠ 0 →
      F₃ p' ≤ F₃ p + C₃)
  (hδ₀ : ∀ p p',
    mapKernelOfMatrix r₀ r₀ (fun m l => coefficientComparison q hq (D₀ m l)) p p' ≠ 0 →
      F₀ p' ≤ F₀ p + C₀)

include hμ₁ hμ₂ hμ₃ hμ₀ in
/-- **Associativity of class-indexed counts on cocycles.** Under the identity of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_assoc_sub_eq_add`, suppose that every
class counted by `K` satisfies the index condition
`μ₀(r₀) - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) + μ₃(r₃) - 2n + 1` of rigid elements of the one-parameter
family of four-punctured spheres, so that `K` lowers the cochain degree by one. Then for cocycles
`x₁`, `x₂`, `x₃` of the cylinder differentials, of cochain degrees `e₁`, `e₂`, `e₃`, the difference
`(x₁ ⋆ x₂) ⋆' x₃ - x₁ ⋆''' (x₂ ⋆'' x₃)` is the coboundary of `K(x₁, x₂, x₃)` in cochain degree
`e₁ + e₂ + e₃`. The differentials are the ground-ring linear maps of the cylinder counts, for any
potential bounds of their kernels. -/
theorem novikovProductOfMatrix_coefficientComparison_assoc_sub_mem_coboundaries
    (hK : ∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ + μ₃ ⟨k, r₃ k⟩ - 2 * n + 1)
    (hA : ∀ i j k l, ∑ t, Q i j t * Q' t k l - ∑ u, T j k u * T' i u l =
      ∑ m, K i j k m * D₀ m l + ∑ m, D₁ i m * K m j k l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m k l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩ + (n - μ₂ ⟨j, r₂ j⟩)) • ∑ m, D₃ k m * K i j m l)
    {e₁ e₂ e₃ : ℤ} {x₁ : NovikovModule R F₁}
    (hx₁ : x₁ ∈ (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cocycles
      (gradeBy R F₁ fun p => n - μ₁ p) e₁)
    {x₂ : NovikovModule R F₂}
    (hx₂ : x₂ ∈ (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cocycles
      (gradeBy R F₂ fun p => n - μ₂ p) e₂)
    {x₃ : NovikovModule R F₃}
    (hx₃ : x₃ ∈ (kernelMap hδ₃ (mapKernelOfMatrix_mem hF₃ r₃ r₃ _)).cocycles
      (gradeBy R F₃ fun p => n - μ₃ p) e₃) :
    novikovProductOfMatrix hF₁₂ hF₃ hF₀ r₁₂ r₃ r₀
          (fun t k l => coefficientComparison q hq (Q' t k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₁₂ r₁ r₂ r₁₂
            (fun i j t => coefficientComparison q hq (Q i j t)) x₁ x₂) x₃ -
        novikovProductOfMatrix hF₁ hF₂₃ hF₀ r₁ r₂₃ r₀
          (fun i u l => coefficientComparison q hq (T' i u l)) x₁
          (novikovProductOfMatrix hF₂ hF₃ hF₂₃ r₂ r₃ r₂₃
            (fun j k u => coefficientComparison q hq (T j k u)) x₂ x₃) ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)).coboundaries
        (gradeBy R F₀ fun p => n - μ₀ p) (e₁ + e₂ + e₃) := by
  rw [LinearMap.mem_cocycles_iff] at hx₁ hx₂ hx₃
  rw [← novikovMapOfMatrix_eq_kernelMap hF₁ hF₁ r₁ r₁ _ hδ₁] at hx₁
  rw [← novikovMapOfMatrix_eq_kernelMap hF₂ hF₂ r₂ r₂ _ hδ₂] at hx₂
  rw [← novikovMapOfMatrix_eq_kernelMap hF₃ hF₃ r₃ r₃ _ hδ₃] at hx₃
  refine LinearMap.mem_coboundaries_iff.2 ⟨_,
    novikovTrilinearOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ r₀ q hq r₃ hF₁ hF₂
      hF₃ hF₀ hμ₁ hμ₂ hμ₃ hμ₀ K hK hx₁.2 hx₂.2 hx₃.2, ?_⟩
  -- The Novikov module structures, for the vanishing of the homotopy terms with `dᵢ xᵢ = 0`.
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₃
  let := module (R := R) hF₀
  rw [novikovProductOfMatrix_coefficientComparison_assoc_sub_eq_add r₁ r₂ r₀ q hq r₃ r₁₂ r₂₃ hF₁
      hF₂ hF₃ hF₀ hμ₁ hμ₂ hF₁₂ hF₂₃ Q Q' T T' K D₁ D₂ D₃ D₀ n hA hx₁.2 hx₂.2 x₃,
    hx₁.1, hx₂.1, hx₃.1, novikovMapOfMatrix_eq_kernelMap hF₀ hF₀ r₀ r₀ _ hδ₀]
  simp

variable {G₁₂ : ℤ → Submodule R (NovikovModule R F₁₂)}
  {G₂₃ : ℤ → Submodule R (NovikovModule R F₂₃)}
  {δ₁₂ : NovikovModule R F₁₂ →ₗ[R] NovikovModule R F₁₂}
  {δ₂₃ : NovikovModule R F₂₃ →ₗ[R] NovikovModule R F₂₃} {CQ CQ' CT CT' : ℝ}
  (hnQ : ∀ p₁ p₂ p₀,
    kernelOfMatrix r₁ r₂ r₁₂ (fun i j t => coefficientComparison q hq (Q i j t)) p₁ p₂ p₀ ≠ 0 →
      F₁₂ p₀ ≤ F₁ p₁ + F₂ p₂ + CQ)
  (hnQ' : ∀ p₁ p₂ p₀,
    kernelOfMatrix r₁₂ r₃ r₀ (fun t k l => coefficientComparison q hq (Q' t k l)) p₁ p₂ p₀ ≠ 0 →
      F₀ p₀ ≤ F₁₂ p₁ + F₃ p₂ + CQ')
  (hnT : ∀ p₁ p₂ p₀,
    kernelOfMatrix r₂ r₃ r₂₃ (fun j k u => coefficientComparison q hq (T j k u)) p₁ p₂ p₀ ≠ 0 →
      F₂₃ p₀ ≤ F₂ p₁ + F₃ p₂ + CT)
  (hnT' : ∀ p₁ p₂ p₀,
    kernelOfMatrix r₁ r₂₃ r₀ (fun i u l => coefficientComparison q hq (T' i u l)) p₁ p₂ p₀ ≠ 0 →
      F₀ p₀ ≤ F₁ p₁ + F₂₃ p₂ + CT')
  {ε₁ ε₂ ε₃ ε₄ : ℤ}
  {hQdeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → b ∈ gradeBy R F₂ (fun p => n - μ₂ p) j →
      kernelProduct hnQ (kernelOfMatrix_mem hF₁₂ r₁ r₂ r₁₂ _) a b ∈ G₁₂ (i + j + ε₁)}
  {hQL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → ∀ b,
    δ₁₂ (kernelProduct hnQ (kernelOfMatrix_mem hF₁₂ r₁ r₂ r₁₂ _) a b) =
      kernelProduct hnQ (kernelOfMatrix_mem hF₁₂ r₁ r₂ r₁₂ _)
          (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _) a) b +
        negOnePowCast R i • kernelProduct hnQ (kernelOfMatrix_mem hF₁₂ r₁ r₂ r₁₂ _) a
          (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _) b)}
  {hQ'deg : ∀ {i j : ℤ} {a : NovikovModule R F₁₂} {b : NovikovModule R F₃},
    a ∈ G₁₂ i → b ∈ gradeBy R F₃ (fun p => n - μ₃ p) j →
      kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁₂ r₃ r₀ _) a b ∈
        gradeBy R F₀ (fun p => n - μ₀ p) (i + j + ε₂)}
  {hQ'L : ∀ {i : ℤ} {a : NovikovModule R F₁₂}, a ∈ G₁₂ i → ∀ b,
    kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)
        (kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁₂ r₃ r₀ _) a b) =
      kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁₂ r₃ r₀ _) (δ₁₂ a) b +
        negOnePowCast R i • kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁₂ r₃ r₀ _) a
          (kernelMap hδ₃ (mapKernelOfMatrix_mem hF₃ r₃ r₃ _) b)}
  {hTdeg : ∀ {i j : ℤ} {a : NovikovModule R F₂} {b : NovikovModule R F₃},
    a ∈ gradeBy R F₂ (fun p => n - μ₂ p) i → b ∈ gradeBy R F₃ (fun p => n - μ₃ p) j →
      kernelProduct hnT (kernelOfMatrix_mem hF₂₃ r₂ r₃ r₂₃ _) a b ∈ G₂₃ (i + j + ε₃)}
  {hTL : ∀ {i : ℤ} {a : NovikovModule R F₂}, a ∈ gradeBy R F₂ (fun p => n - μ₂ p) i → ∀ b,
    δ₂₃ (kernelProduct hnT (kernelOfMatrix_mem hF₂₃ r₂ r₃ r₂₃ _) a b) =
      kernelProduct hnT (kernelOfMatrix_mem hF₂₃ r₂ r₃ r₂₃ _)
          (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _) a) b +
        negOnePowCast R i • kernelProduct hnT (kernelOfMatrix_mem hF₂₃ r₂ r₃ r₂₃ _) a
          (kernelMap hδ₃ (mapKernelOfMatrix_mem hF₃ r₃ r₃ _) b)}
  {hT'deg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂₃},
    a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → b ∈ G₂₃ j →
      kernelProduct hnT' (kernelOfMatrix_mem hF₀ r₁ r₂₃ r₀ _) a b ∈
        gradeBy R F₀ (fun p => n - μ₀ p) (i + j + ε₄)}
  {hT'L : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i → ∀ b,
    kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀ r₀ r₀ _)
        (kernelProduct hnT' (kernelOfMatrix_mem hF₀ r₁ r₂₃ r₀ _) a b) =
      kernelProduct hnT' (kernelOfMatrix_mem hF₀ r₁ r₂₃ r₀ _)
          (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _) a) b +
        negOnePowCast R i • kernelProduct hnT' (kernelOfMatrix_mem hF₀ r₁ r₂₃ r₀ _) a (δ₂₃ b)}

include hμ₁ hμ₂ hμ₃ hμ₀ in
/-- **Associativity of class-indexed counts on cohomology.** Let the four products of
class-indexed counts in `(x ⋆ y) ⋆' z` and `x ⋆''' (y ⋆'' z)`, as ground-ring bilinear maps for any
potential bounds of their kernels, induce products on the cohomology of the cylinder
differentials, graded by the cochain degrees `n - μ`. The intermediate complexes of `x ⋆ y` and
`y ⋆'' z` may carry any differentials and gradings for which the products obey the Leibniz rule,
and the degree shifts `ε₁` and `ε₂` of the first bracketing must add up to zero, as the shifts of
products of rigid counts do. Under the identity and the index condition of
`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_assoc_sub_mem_coboundaries`, the
induced products are associative: `([x] ⋆ [y]) ⋆' [z] = [x] ⋆''' ([y] ⋆'' [z])`. -/
theorem cohomologyProduct_kernelProduct_coefficientComparison_assoc
    (hK : ∀ i j k l, ∀ A ∈ (K i j k l).support,
      μ₀ ⟨l, r₀ l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ + μ₃ ⟨k, r₃ k⟩ - 2 * n + 1)
    (hA : ∀ i j k l, ∑ t, Q i j t * Q' t k l - ∑ u, T j k u * T' i u l =
      ∑ m, K i j k m * D₀ m l + ∑ m, D₁ i m * K m j k l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m k l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩ + (n - μ₂ ⟨j, r₂ j⟩)) • ∑ m, D₃ k m * K i j m l)
    (hε : ε₁ + ε₂ = 0) {e₁ e₂ e₃ e₁₂ e₂₃ e₀ : ℤ} (h₁₂ : e₁ + e₂ + ε₁ = e₁₂)
    (h₀ : e₁₂ + e₃ + ε₂ = e₀) (h₂₃ : e₂ + e₃ + ε₃ = e₂₃) (h₀' : e₁ + e₂₃ + ε₄ = e₀)
    (x : (kernelMap hδ₁ (mapKernelOfMatrix_mem hF₁ r₁ r₁ _)).cohomology
      (gradeBy R F₁ fun p => n - μ₁ p) e₁)
    (y : (kernelMap hδ₂ (mapKernelOfMatrix_mem hF₂ r₂ r₂ _)).cohomology
      (gradeBy R F₂ fun p => n - μ₂ p) e₂)
    (z : (kernelMap hδ₃ (mapKernelOfMatrix_mem hF₃ r₃ r₃ _)).cohomology
      (gradeBy R F₃ fun p => n - μ₃ p) e₃) :
    LinearMap.cohomologyProduct (kernelProduct hnQ' (kernelOfMatrix_mem hF₀ r₁₂ r₃ r₀ _)) hQ'deg
        hQ'L h₀
        (LinearMap.cohomologyProduct (kernelProduct hnQ (kernelOfMatrix_mem hF₁₂ r₁ r₂ r₁₂ _))
          hQdeg hQL h₁₂ x y) z =
      LinearMap.cohomologyProduct (kernelProduct hnT' (kernelOfMatrix_mem hF₀ r₁ r₂₃ r₀ _)) hT'deg
        hT'L h₀' x
        (LinearMap.cohomologyProduct (kernelProduct hnT (kernelOfMatrix_mem hF₂₃ r₂ r₃ r₂₃ _))
          hTdeg hTL h₂₃ y z) := by
  refine LinearMap.cohomologyProduct_assoc h₁₂ h₀ h₂₃ h₀' (fun ha hb hc => ?_) x y z
  have h := novikovProductOfMatrix_coefficientComparison_assoc_sub_mem_coboundaries r₁ r₂ r₀ q hq
    r₃ r₁₂ r₂₃ hF₁ hF₂ hF₃ hF₀ hμ₁ hμ₂ hF₁₂ hF₂₃ hμ₃ hμ₀ Q Q' T T' K D₁ D₂ D₃ D₀ n hδ₁ hδ₂ hδ₃
    hδ₀ hK hA ha hb hc
  rw [novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂ hF₁₂ r₁ r₂ r₁₂ _ hnQ,
    novikovProductOfMatrix_eq_kernelProduct hF₁₂ hF₃ hF₀ r₁₂ r₃ r₀ _ hnQ',
    novikovProductOfMatrix_eq_kernelProduct hF₂ hF₃ hF₂₃ r₂ r₃ r₂₃ _ hnT,
    novikovProductOfMatrix_eq_kernelProduct hF₁ hF₂₃ hF₀ r₁ r₂₃ r₀ _ hnT'] at h
  rwa [show e₀ = e₁ + e₂ + e₃ by omega]

end Cohomology

end Associativity

section Continuation

variable {ι₁' ι₂' ι₀' : Type*} {P₁' : ι₁' → Type*} {P₂' : ι₂' → Type*} {P₀' : ι₀' → Type*}
  [∀ s, AddTorsor (PeriodGroup ω c) (P₁' s)] [∀ t, AddTorsor (PeriodGroup ω c) (P₂' t)]
  [∀ l, AddTorsor (PeriodGroup ω c) (P₀' l)]
  (r₁' : ∀ s, P₁' s) (r₂' : ∀ t, P₂' t) (r₀' : ∀ l, P₀' l)
  [CommRing R] [Fintype ι₁] [Fintype ι₂] [Fintype ι₀] [Fintype ι₁'] [Fintype ι₂'] [Fintype ι₀']
  {F₁ : (Σ i, P₁ i) → ℝ} {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  {F₁' : (Σ s, P₁' s) → ℝ} {F₂' : (Σ t, P₂' t) → ℝ} {F₀' : (Σ l, P₀' l) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)
  (hF₁' : ∀ s γ (D : P₁' s), F₁' ⟨s, γ +ᵥ D⟩ = F₁' ⟨s, D⟩ - (-area ω c) γ)
  (hF₂' : ∀ t γ (D : P₂' t), F₂' ⟨t, γ +ᵥ D⟩ = F₂' ⟨t, D⟩ - (-area ω c) γ)
  (hF₀' : ∀ l γ (D : P₀' l), F₀' ⟨l, γ +ᵥ D⟩ = F₀' ⟨l, D⟩ - (-area ω c) γ)
  {μ₁ : (Σ i, P₁ i) → ℤ} (hμ₁ : ∀ i γ (D : P₁ i), μ₁ ⟨i, γ +ᵥ D⟩ = degree ω c γ + μ₁ ⟨i, D⟩)
  (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (Q' : ι₁' → ι₂' → ι₀' → NovikovSeries R G ωG)
  (Φ₁ : ι₁ → ι₁' → NovikovSeries R G ωG) (Φ₂ : ι₂ → ι₂' → NovikovSeries R G ωG)
  (Φ₀ : ι₀ → ι₀' → NovikovSeries R G ωG) (K : ι₁ → ι₂ → ι₀' → NovikovSeries R G ωG)
  (D₁ : ι₁ → ι₁ → NovikovSeries R G ωG) (D₂ : ι₂ → ι₂ → NovikovSeries R G ωG)
  (D₀' : ι₀' → ι₀' → NovikovSeries R G ωG) (n : ℤ)

include hμ₁ in
/-- **Compatibility of class-indexed counts with continuation maps up to homotopy.** Let `Q` be the
generating series of rigid pairs of pants between reference capped orbits for one choice of end
Hamiltonians and `Q'` those for another, let `Φ₁`, `Φ₂`, `Φ₀` be those of rigid continuation
cylinders from the orbits of each end of the first choice to those of the second, `D₁`, `D₂` those
of rigid Floer cylinders of the two inputs of the first choice and `D₀'` those of the output of the
second, and `K` those of the rigid members of the continuation family of pairs of pants, all indexed
by a common class group `G`. Suppose the series obey the identity

`∑ₖ Qᵢⱼₖ Φ₀ₖₗ - ∑ₛ ∑ₜ Φ₁ᵢₛ Φ₂ⱼₜ Q'ₛₜₗ =
  ∑ₘ Kᵢⱼₘ D₀'ₘₗ + ∑ₘ D₁ᵢₘ Kₘⱼₗ + (-1)^(n - μ₁(r₁ i)) ∑ₘ D₂ⱼₘ Kᵢₘₗ`

in `G`-indexed series, which is the count, class by class, of the ends of the one-dimensional moduli
spaces of the continuation family between reference capped orbits: the pair of pants broken at its
output from a continuation cylinder, the continuation cylinders broken at the two inputs from a
pair of pants, and the breaking of a Floer cylinder at one of the three ends. Then on the completed
capped modules, with the first input graded by the cochain degree `n - μ₁`, the operation of `K` is
a homotopy between the two composites:
`Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b = d₀' K(a, b) + K(d₁ a, b) + (-1)^e K(a, d₂ b)` for `a` of degree `e`.
The sign is constant on the capped generators of each orbit, because recapping changes the degree
by the even number `2 c₁(γ)`. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add
    (hcont : ∀ i j l, ∑ k, Q i j k * Φ₀ k l - ∑ s, ∑ t, Φ₁ i s * Φ₂ j t * Q' s t l =
      ∑ m, K i j m * D₀' m l + ∑ m, D₁ i m * K m j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m l)
    {e : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) e)
    (b : NovikovModule R F₂) :
    novikovMapOfMatrix hF₀ hF₀' r₀ r₀' (fun k l => coefficientComparison q hq (Φ₀ k l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
            (fun i j k => coefficientComparison q hq (Q i j k)) a b) -
        novikovProductOfMatrix hF₁' hF₂' hF₀' r₁' r₂' r₀'
          (fun s t l => coefficientComparison q hq (Q' s t l))
          (novikovMapOfMatrix hF₁ hF₁' r₁ r₁' (fun i s => coefficientComparison q hq (Φ₁ i s)) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ r₂' (fun j t => coefficientComparison q hq (Φ₂ j t)) b) =
      novikovMapOfMatrix hF₀' hF₀' r₀' r₀' (fun m l => coefficientComparison q hq (D₀' m l))
          (novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
            (fun i j m => coefficientComparison q hq (K i j m)) a b) +
        novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
          (fun i j m => coefficientComparison q hq (K i j m))
          (novikovMapOfMatrix hF₁ hF₁ r₁ r₁ (fun i m => coefficientComparison q hq (D₁ i m)) a) b +
        negOnePowCast R e • novikovProductOfMatrix hF₁ hF₂ hF₀' r₁ r₂ r₀'
          (fun i j m => coefficientComparison q hq (K i j m)) a
          (novikovMapOfMatrix hF₂ hF₂ r₂ r₂ (fun j m => coefficientComparison q hq (D₂ j m))
            b) := by
  refine novikovMapOfMatrix_novikovProductOfMatrix_sub_novikovProductOfMatrix_novikovMapOfMatrix
    hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' r₁ r₂ r₀ r₁' r₂' r₀' _ _ _ _ _ _ _ _ _
    (even_cochain_vadd_sub hμ₁ n) (fun i j l => ?_) ha b
  have h := congrArg (coefficientComparison q hq) (hcont i j l)
  simp only [map_sum, map_add, map_sub, _root_.map_mul, ← negOnePow_smul_eq_negOnePowCast_smul,
    Units.smul_def, map_zsmul] at h ⊢
  exact h

include hμ₁ in
/-- **Compatibility of class-indexed counts with continuation maps on cohomology.** Under the
identity of `novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add`, suppose
that every class counted by `K` satisfies the index condition
`μ₀'(r₀') - 2 c₁(A) = μ₁(r₁) + μ₂(r₂) - n + 1` of rigid members of the continuation family, whose
Fredholm index at a fixed parameter is `-1`, so that `K` lowers the cochain degree by one. Then for
cocycles `a` and `b` of the cylinder differentials, of cochain degrees `e` and `f`, the difference
`Φ₀ (a ⋆ b) - Φ₁ a ⋆' Φ₂ b` is the coboundary of `K(a, b)` in cochain degree `e + f`. The
differentials are the ground-ring linear maps of the cylinder counts, for any potential bounds of
their kernels. -/
theorem novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_mem_coboundaries
    {μ₂ : (Σ j, P₂ j) → ℤ} (hμ₂ : ∀ j γ (D : P₂ j), μ₂ ⟨j, γ +ᵥ D⟩ = degree ω c γ + μ₂ ⟨j, D⟩)
    {μ₀' : (Σ l, P₀' l) → ℤ}
    (hμ₀' : ∀ l γ (D : P₀' l), μ₀' ⟨l, γ +ᵥ D⟩ = degree ω c γ + μ₀' ⟨l, D⟩)
    (hK : ∀ i j l, ∀ A ∈ (K i j l).support,
      μ₀' ⟨l, r₀' l⟩ - degree ω c (q A) = μ₁ ⟨i, r₁ i⟩ + μ₂ ⟨j, r₂ j⟩ - n + 1)
    (hcont : ∀ i j l, ∑ k, Q i j k * Φ₀ k l - ∑ s, ∑ t, Φ₁ i s * Φ₂ j t * Q' s t l =
      ∑ m, K i j m * D₀' m l + ∑ m, D₁ i m * K m j l +
        negOnePowCast R (n - μ₁ ⟨i, r₁ i⟩) • ∑ m, D₂ j m * K i m l)
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
          (fun s t l => coefficientComparison q hq (Q' s t l))
          (novikovMapOfMatrix hF₁ hF₁' r₁ r₁' (fun i s => coefficientComparison q hq (Φ₁ i s)) a)
          (novikovMapOfMatrix hF₂ hF₂' r₂ r₂' (fun j t => coefficientComparison q hq (Φ₂ j t)) b) ∈
      (kernelMap hδ₀ (mapKernelOfMatrix_mem hF₀' r₀' r₀' _)).coboundaries
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
  -- `K` is the product of rigid counts for the gradings `μ₀' - 1`, so `K(a, b)` has cochain
  -- degree `e + f - 1`.
  have hKab := novikovProductOfMatrix_coefficientComparison_mem_cochain_gradeBy r₁ r₂ r₀' q hq hF₁
    hF₂ hF₀' hμ₁ hμ₂ (μ₀ := fun p => μ₀' p - 1) (fun l γ D => by rw [hμ₀']; ring) K
    (fun i j l A hA => by linarith [hK i j l A hA]) ha.2 hb.2
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
  rw [novikovMapOfMatrix_novikovProductOfMatrix_coefficientComparison_sub_eq_add
      r₁ r₂ r₀ q hq r₁' r₂' r₀' hF₁ hF₂ hF₀ hF₁' hF₂' hF₀' hμ₁ Q Q' Φ₁ Φ₂ Φ₀ K D₁ D₂ D₀' n hcont
      ha.2 b,
    hDa, hDb, map_zero, LinearMap.zero_apply, map_zero, smul_zero, add_zero, add_zero,
    novikovMapOfMatrix_eq_kernelMap hF₀' hF₀' r₀' r₀' _ hδ₀]

end Continuation

end Monoid

section Reference

variable {G : Type*} [AddCommGroup G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

/-- **Change of reference caps.** Moving the reference caps to `q gₗ # rₗ` changes the class of a
pair of pants relative to the reference caps by `g₀ - g₁ - g₂`, so the generating series become
`q^(g₀ - g₁ - g₂) Q`. The kernel on capped generators is unchanged. -/
theorem kernelOfMatrix_coefficientComparison_vadd [Semiring R]
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (g₁ : ι₁ → G) (g₂ : ι₂ → G) (g₀ : ι₀ → G) :
    kernelOfMatrix (fun i => q (g₁ i) +ᵥ r₁ i) (fun j => q (g₂ j) +ᵥ r₂ j)
        (fun k => q (g₀ k) +ᵥ r₀ k) (fun i j k => coefficientComparison q hq
          (NovikovSeries.single (g₀ k - g₁ i - g₂ j) 1 * Q i j k)) =
      kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k)) := by
  funext ⟨i, D₁⟩ ⟨j, D₂⟩ ⟨k, D₀⟩
  rw [kernelOfMatrix_apply, kernelOfMatrix_apply, _root_.map_mul, coefficientComparison_single,
    coeff_single_mul, one_mul, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub,
    vsub_vadd_eq_vsub_sub, map_sub, map_sub]
  congr 1
  abel

variable [CommSemiring R] [Finite ι₁] [Finite ι₂] [Finite ι₀] {F₁ : (Σ i, P₁ i) → ℝ}
  {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)

/-- **The product of class-indexed counts does not depend on the reference caps.** Moving the
reference caps to `q gₗ # rₗ` and the generating series to `q^(g₀ - g₁ - g₂) Q` gives the same
product on capped generators. -/
theorem novikovProductOfMatrix_coefficientComparison_vadd
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (g₁ : ι₁ → G) (g₂ : ι₂ → G) (g₀ : ι₀ → G) :
    novikovProductOfMatrix hF₁ hF₂ hF₀ (fun i => q (g₁ i) +ᵥ r₁ i) (fun j => q (g₂ j) +ᵥ r₂ j)
        (fun k => q (g₀ k) +ᵥ r₀ k) (fun i j k => coefficientComparison q hq
          (NovikovSeries.single (g₀ k - g₁ i - g₂ j) 1 * Q i j k)) =
      novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (Q i j k)) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  let := module (R := R) hF₀
  refine LinearMap.ext fun a => LinearMap.ext fun b => Subtype.ext (funext fun p₀ => ?_)
  rw [novikovProductOfMatrix_apply_val, novikovProductOfMatrix_apply_val,
    kernelOfMatrix_coefficientComparison_vadd]

end Reference

end TauCeti.Floer
