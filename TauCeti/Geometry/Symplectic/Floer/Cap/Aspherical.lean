/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Product

/-!
# The capped product on targets with trivial period group

On a symplectically aspherical target whose first Chern class vanishes on spheres, for instance
on any aspherical manifold such as a torus
(`TauCeti.Floer.SphericalPeriodGroup.subsingleton_of_isAspherical`), the period group
`Γ = PeriodGroup ω c` of capped Hamiltonian Floer theory is trivial. This file computes what the
capped constructions of `TauCeti.Geometry.Symplectic.Floer.Cap.Product` become in that case; it is
the classical setting of the pair-of-pants product before Novikov coefficients were introduced.

* The Floer Novikov ring `NovikovSeries R Γ (-area ω c)` is the coefficient ring `R` itself,
  through the coefficient at `0` (`TauCeti.NovikovSeries.coeffZeroRingEquiv`).
* Every orbit has exactly one capped generator: each fibre of the capped generators is a torsor
  under the trivial group. For actual caps of contractible loops this is the uniqueness of their
  cap classes (`TauCeti.Floer.SphericalCapClass` is a subsingleton when `Γ` is).
* A class `A` of any common class group `G` mapping to `Γ` by an area-preserving homomorphism has
  zero area, so a generating series `Q = ∑_A N_A q^A` of counts has only finitely many nonzero
  counts (`TauCeti.NovikovSeries.finite_support_of_bddAbove_image`), and the coefficient comparison
  `q^A ↦ e^(-q A)` sends it to the total count `∑_A N_A`
  (`TauCeti.Floer.coeff_zero_coefficientComparison_of_subsingleton`).
* With finitely many orbits every coefficient function on capped generators is a completed
  combination (`TauCeti.NovikovModule.eq_top_of_subsingleton`): the capped complex is the
  free `R`-module on the orbits, with no completion.
* The kernel of the counts on capped generators is the total count, whatever the caps
  (`TauCeti.Floer.kernelOfMatrix_coefficientComparison_apply_of_subsingleton`), and the product
  of completed combinations `a` and `b` is the finite matrix product
  `(a ⋆ b)(x₀) = ∑ᵢ ∑ⱼ a(xᵢ) b(xⱼ) ∑_A N_A(i, j, k)` over the orbits, with the coefficients of the
  unique capped generators
  (`TauCeti.Floer.novikovProductOfMatrix_coefficientComparison_apply_val_of_subsingleton`).

So on such targets no completion is needed, and the capped product is the `R`-bilinear product of
the matrix of total counts of rigid pairs of pants. Its identification with the ordinary cup
product needs the actual counts and the multiplicative PSS comparison.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product on symplectically aspherical manifolds.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

namespace TauCeti.Floer

open NovikovModule NovikovSeries PeriodGroup

variable {R S : Type*} [AddCommGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}
  [Subsingleton (PeriodGroup ω c)]
  {G : Type*} [AddMonoid G] {ωG : G →+ ℝ} (q : G →+ PeriodGroup ω c)
  (hq : ∀ A, area ω c (q A) = ωG A)

variable {ι₁ ι₂ ι₀ : Type*} {P₁ : ι₁ → Type*} {P₂ : ι₂ → Type*} {P₀ : ι₀ → Type*}
  [∀ i, AddTorsor (PeriodGroup ω c) (P₁ i)] [∀ j, AddTorsor (PeriodGroup ω c) (P₂ j)]
  [∀ k, AddTorsor (PeriodGroup ω c) (P₀ k)]
  (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j) (r₀ : ∀ k, P₀ k)

/-- **On a trivial period group the product kernel is the total count.** At any capped generators
of the orbits `i`, `j` and `k`, the kernel of class-indexed counts is the total count
`∑_A N_A(i, j, k)` of all classes. -/
theorem kernelOfMatrix_coefficientComparison_apply_of_subsingleton [Semiring R]
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) {i : ι₁} {j : ι₂} {k : ι₀} (D₁ : P₁ i)
    (D₂ : P₂ j) (D₀ : P₀ k) :
    kernelOfMatrix r₁ r₂ r₀ (fun i j k => coefficientComparison q hq (Q i j k))
        ⟨i, D₁⟩ ⟨j, D₂⟩ ⟨k, D₀⟩ =
      ∑ᶠ A, (Q i j k).coeff A := by
  have h : q ⁻¹' {(D₁ -ᵥ r₁ i) + (D₂ -ᵥ r₂ j) - (D₀ -ᵥ r₀ k)} = Set.univ :=
    Set.eq_univ_of_forall fun A => Subsingleton.elim _ _
  rw [kernelOfMatrix_coefficientComparison_apply, h, finsum_mem_univ]

variable [CommSemiring R] [Fintype ι₁] [Fintype ι₂] [Finite ι₀] {F₁ : (Σ i, P₁ i) → ℝ}
  {F₂ : (Σ j, P₂ j) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i γ (D : P₁ i), F₁ ⟨i, γ +ᵥ D⟩ = F₁ ⟨i, D⟩ - (-area ω c) γ)
  (hF₂ : ∀ j γ (D : P₂ j), F₂ ⟨j, γ +ᵥ D⟩ = F₂ ⟨j, D⟩ - (-area ω c) γ)
  (hF₀ : ∀ k γ (D : P₀ k), F₀ ⟨k, γ +ᵥ D⟩ = F₀ ⟨k, D⟩ - (-area ω c) γ)

/-- **On a trivial period group the capped product is the matrix product of total counts.** Each
orbit has a single capped generator, the reference one, and the coefficient of the product of `a`
and `b` at a capped generator of the orbit `k` is `∑ᵢ ∑ⱼ a(rᵢ) b(rⱼ) ∑_A N_A(i, j, k)`. -/
theorem novikovProductOfMatrix_coefficientComparison_apply_val_of_subsingleton
    (Q : ι₁ → ι₂ → ι₀ → NovikovSeries R G ωG) (a : NovikovModule R F₁) (b : NovikovModule R F₂)
    {k : ι₀} (D₀ : P₀ k) :
    (novikovProductOfMatrix hF₁ hF₂ hF₀ r₁ r₂ r₀
        (fun i j k => coefficientComparison q hq (Q i j k)) a b).val ⟨k, D₀⟩ =
      ∑ i, ∑ j, a.val ⟨i, r₁ i⟩ * b.val ⟨j, r₂ j⟩ * ∑ᶠ A, (Q i j k).coeff A := by
  obtain rfl : D₀ = (0 : PeriodGroup ω c) +ᵥ r₀ k :=
    ((AddTorsor.subsingleton_iff (PeriodGroup ω c) (P₀ k)).1 inferInstance).elim _ _
  rw [← coordinates_coeff hF₀ r₀, coordinates_novikovProductOfMatrix, ← coeffZeroRingEquiv_apply]
  simp only [map_sum, _root_.map_mul, coeffZeroRingEquiv_apply, coordinates_coeff, zero_vadd,
    coeff_zero_coefficientComparison_of_subsingleton]

end TauCeti.Floer
