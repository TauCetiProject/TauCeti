/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CoefficientComparison
public import TauCeti.Geometry.Symplectic.Floer.Grading
public import TauCeti.RingTheory.NovikovModule.Bilinear
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
* **Change of reference caps.** Moving the reference caps by lifts `g₁, g₂, g₀ ∈ G` multiplies
  the generating series by `q^(g₀ - g₁ - g₂)` and leaves the kernel, hence the product, unchanged
  (`TauCeti.Floer.kernelOfMatrix_coefficientComparison_vadd`).

The energy, compactness and index hypotheses are the ones the geometric moduli spaces are to
supply; no moduli space, orientation or count is constructed here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
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
