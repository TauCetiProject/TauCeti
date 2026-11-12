/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker

/-!
# The Kronecker pairing of singular cap and cup products

For a space `X`, a coefficient morphism `u : T ⟶ R ⊗ S`, a singular cohomology class
`α ∈ Hᵖ(X; R, 𝟙)` with values in the tensor unit and a class `β ∈ H^q(X; S, N)`, the cap product
`x ⌢ α ∈ H_q(X; S)` of a class `x ∈ Hₙ(X; T)`, `n = p + q`, taken along the left unitor
`𝟙 ⊗ S ⟶ S`, satisfies

`⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`,

where the cup product is taken along `u` and the left unitor `𝟙 ⊗ N ⟶ N`
(`TopCat.singularCap_comp_singularKronecker`).  There is no sign: with the front-face convention
of the Alexander–Whitney diagonal both sides evaluate `α` on the front `p`-face and `β` on the back
`q`-face of each singular simplex.  For modules over a commutative ring `k`, with all coefficients
the module `k` and `u` the inverse left unitor, this is the identity
`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩` of Hatcher, Section 3.3, which makes the cap product the adjoint of
the cup product under the Kronecker pairing.

For a class `μ ∈ Hₙ(X; k)`, evaluating cup products on `μ` is the bilinear cup pairing
`TopCat.singularCupPairing`, `(α, β) ↦ ⟨α ⌣ β, μ⟩`, and the identity above says that it is
`⟨β, μ ⌢ α⟩` (`TopCat.singularCupPairing_eq_singularKronecker_singularCapLinearMap`). When `2`
is invertible in `k`, graded commutativity makes the cup pairing in an odd middle degree
alternating (`TopCat.isAlt_singularCupPairing`).

The key chain-level input is `SSet.chainComplexPairing_leftUnitor_hom_f`, from
`TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing`: the action of the tensor unit on
singular chains is the left unitor.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T N : C}

/-- **The Kronecker pairing of a singular cap product**, `⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for a class
`α` of degree `p` with values in the tensor unit and a class `β` of degree `q` with values in `N`,
capping a class of degree `n = p + q` with `α` along `u` and the left unitor, and then evaluating
`β`, is evaluating the cup product of `α` and `β` along `u` and the left unitor of `N`. -/
theorem singularCap_comp_singularKronecker (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (p q n : ℕ) (h : p + q = n)
    (α : X.singularCohomology R k (𝟙_ C) p) (β : X.singularCohomology S k N q) :
    X.singularCap k u (λ_ S).hom p q n h α ≫ X.singularKronecker k q β =
      X.singularKronecker k n (X.singularCup k u (λ_ N).hom p q n h α β) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  refine TauCeti.ChainComplex.cap_comp_kronecker _ _ _ p q n h φ ψ ψ ?_
  rw [SSet.chainComplexPairing_leftUnitor_hom_f]
  exact (leftUnitor_naturality _).symm

section ModuleCat

variable {k : Type w} [CommRing k] (X : TopCat.{w})

/-- **The cup pairing on a homology class**: for `μ ∈ Hₙ(X; k)` and `p + q = n`, the bilinear form
`(α, β) ↦ ⟨α ⌣ β, μ⟩` on `Hᵖ(X; k) × H^q(X; k)`, with the cup product taken along the unitors of
`𝟙_ (ModuleCat k)`. -/
def singularCupPairing {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p →ₗ[k]
      X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q →ₗ[k] k :=
  LinearMap.mk₂ k
    (fun α β ↦ (X.singularKronecker k n (X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h α β)).hom μ)
    (fun α α' β ↦ by simp) (fun c α β ↦ by simp) (fun α β β' ↦ by simp) (fun c α β ↦ by simp)

/-- The cup pairing of `α` and `β` on `μ` is the Kronecker pairing `⟨α ⌣ β, μ⟩`. -/
@[simp]
theorem singularCupPairing_apply {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCupPairing h μ α β =
      (X.singularKronecker k n (X.singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h α β)).hom μ :=
  (rfl)

/-- The cup pairing of `α` and `β` on `μ` is the Kronecker pairing `⟨β, μ ⌢ α⟩` of `β` with the
cap product of `μ` and `α`. -/
theorem singularCupPairing_eq_singularKronecker_singularCapLinearMap {p q n : ℕ}
    (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (β : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCupPairing h μ α β =
      (X.singularKronecker k q β).hom (X.singularCapLinearMap h μ α) := by
  rw [singularCupPairing_apply, singularCapLinearMap_apply,
    ← singularCap_comp_singularKronecker]
  rfl

/-- In odd degree `p` with `p + p = n`, the cup pairing on `μ` is alternating when `2` is
invertible in `k`. -/
theorem isAlt_singularCupPairing [Invertible (2 : k)] {p n : ℕ} (hp : Odd p) (h : p + p = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCupPairing h μ).IsAlt := fun α ↦ by
  rw [singularCupPairing_apply,
    X.singularCup_self_eq_zero_of_odd k (by simp [unitors_inv_equal]) hp h α, map_zero]
  rfl

end ModuleCat

end TopCat
