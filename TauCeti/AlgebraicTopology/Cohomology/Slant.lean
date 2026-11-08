/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Slant
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-!
# The slant product in singular cohomology

For spaces `X` and `Y`, modules `R`, `S`, `T` and `M` over a commutative ring `k` and a
coefficient map `u : R ⊗ S ⟶ T`, the **slant product**

`Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)`,  `p + q = n`,

sends a homology class `x` of `X` and a cohomology class `φ` of the product to the class `φ / x`
on `Y` represented by the cochain `σ ↦ φ (u_*(z × σ))`, where `z` is a cycle representing `x` and
`z × σ` is the shuffle product of singular chains. It is the slant product of chains and cochains
`TauCeti.ChainComplex.slant` along the shuffle map followed by `u`, with `X` as the first factor.

The slant product satisfies the evaluation law
`⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩` (`TopCat.singularKronecker_singularSlant`), where `x × y` is the
homology cross product `TopCat.singularHomologyCross`; on the classes of a cycle and a cocycle it
is the class of the slant product of representatives (`TopCat.singularSlant_homologyπ`), and it is
natural, `(f × g)^* φ / x = g^* (φ / f_* x)` (`TopCat.singularSlant_naturality`).

Slant products by homology classes turn a cohomology class on a product into classes on the second
factor. For a line bundle `U` on `X × Y` with first Chern class `c₁(U) ∈ H²(X × Y; ℤ)`, the slant
by the class of a point of `X` is a class of degree two on `Y`, and the slant by a loop in `X` is a
class of degree one on `Y`; these are the point and loop classes of universal line bundles over
moduli spaces.

## Main definitions and results

* `TopCat.singularSlant`: the slant product `Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)`.
* `TopCat.singularSlant_homologyπ`: its value on classes of cycles and cocycles.
* `TopCat.singularKronecker_singularSlant`: the evaluation law `⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩`.
* `TopCat.singularSlant_naturality`: naturality in both spaces.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product of
  singular homology and cohomology).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII (products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w

namespace TopCat

variable {k : Type w} [CommRing k] {R S T : ModuleCat.{w} k} (M : ModuleCat.{w} k)

variable (k) in
/-- **The slant product** `Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)` for `p + q = n`, along the
coefficient map `u : R ⊗ S ⟶ T`: the slant product of chains and cochains along the shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` followed by the map induced by `u`. -/
def singularSlant (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n) :
    ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X →ₗ[k]
      (X ⊗ Y).singularCohomology T k M n →ₗ[k] Y.singularCohomology S k M q :=
  TauCeti.ChainComplex.slant k
    (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y))) p q n h

/-- The slant product of singular cohomology is the slant product of chains and cochains along
the shuffle map followed by the coefficient map. -/
lemma singularSlant_def (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n) :
    singularSlant k M X Y u p q n h =
      TauCeti.ChainComplex.slant k
        (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y)))
        p q n h :=
  (rfl)

/-- **The slant product on classes**: the slant product of the classes of a singular cycle `z` and
a singular cocycle `φ` is the class of the cochain `σ ↦ φ (u_*(z × σ))`. -/
@[simp]
lemma singularSlant_homologyπ (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    (z : ((toSSet.obj X).chainComplex R).cycles p)
    (φ : ((X ⊗ Y).singularCochainComplex T k M).cycles n) :
    singularSlant k M X Y u p q n h (((toSSet.obj X).chainComplex R).homologyπ p z)
        (((X ⊗ Y).singularCochainComplex T k M).homologyπ n φ) =
      (Y.singularCochainComplex S k M).homologyπ q
        (TauCeti.ChainComplex.slantCycles k
          (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y)))
          p q n h z φ) :=
  TauCeti.ChainComplex.slant_homologyπ _ p q n h z φ

/-- **The evaluation law of the slant product**, `⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩`: the Kronecker
pairing of the slant product `φ / x ∈ H^q(Y; S, M)` with a class `y ∈ H_q(Y; S)` is the
Kronecker pairing of `φ` with the image under `u` of the homology cross product
`x × y ∈ Hₙ(X × Y; R ⊗ S)`. -/
theorem singularKronecker_singularSlant (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T) (p q n : ℕ)
    (h : p + q = n) (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (φ : (X ⊗ Y).singularCohomology T k M n)
    (y : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).obj Y) :
    Y.singularKronecker k q (singularSlant k M X Y u p q n h x φ) y =
      (X ⊗ Y).singularKronecker k n φ
        (((singularHomologyFunctor (ModuleCat.{w} k) n).map u).app (X ⊗ Y)
          (singularHomologyCross X Y R S p q n h (x ⊗ₜ y))) := by
  -- the cross product is the algebraic one followed by the shuffle map, so both sides evaluate
  -- `φ` on the image of the algebraic cross product under the shuffle map followed by `u`
  have hev := TauCeti.ChainComplex.kronecker_slant
    (shuffle X Y R S ≫ ((SSet.chainComplexFunctor _).map u).app (toSSet.obj (X ⊗ Y))) p q n h x
    φ y
  rw [homologyMap_comp, ConcreteCategory.comp_apply] at hev
  rw [singularKronecker_def, singularKronecker_def, singularHomologyCross_def]
  exact hev

/-- **Naturality of the slant product** in both spaces: for continuous maps `f : X ⟶ X'` and
`g : Y ⟶ Y'`, `(f × g)^* φ / x = g^* (φ / f_* x)`. -/
lemma singularSlant_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (u : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (φ : (X' ⊗ Y').singularCohomology T k M n) :
    singularSlant k M X Y u p q n h x (TopCat.singularCohomologyMap (f ⊗ₘ g) n φ) =
      TopCat.singularCohomologyMap g q
        (singularSlant k M X' Y' u p q n h
          (((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).map f x) φ) :=
  TauCeti.ChainComplex.slant_naturality _ _ (SSet.chainComplexMap (toSSet.map f) R)
    (SSet.chainComplexMap (toSSet.map g) S) (SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) T)
    (by
      rw [Category.assoc, ← ((SSet.chainComplexFunctor _).map u).naturality]
      exact shuffle_naturality_assoc f g R S _)
    p q n h x φ

end TopCat
