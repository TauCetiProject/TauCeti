/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Slant
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Singular.CrossProduct
import TauCeti.AlgebraicTopology.Cohomology.Point

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

On classes pulled back from one factor the slant product is computed by the cohomology of a point:

* a class `pr₁^* a` pulled back from `X` has `pr₁^* a / x = 0` whenever `q ≠ 0`
  (`TopCat.singularSlant_singularCohomologyMap_fst_eq_zero`), because by naturality it is pulled
  back from the slant product on `X × pt`, which lies in `H^q(pt) = 0`;
* a class `pr₂^* b` pulled back from `Y` has `pr₂^* b / x = 0` whenever `p ≠ 0`
  (`TopCat.singularSlant_singularCohomologyMap_snd_eq_zero`), because by naturality it is the slant
  product by the image of `x` in `Hₚ(pt) = 0`;
* for the class `x` of a point of `X` with coefficient `r`, `pr₂^* b / x` is `b` with its
  coefficients changed along `s ↦ u (r ⊗ s)`
  (`TopCat.singularSlant_homologyπ_singularCohomologyMap_snd`), and it is `b` itself when
  `u (r ⊗ s) = s` (`TopCat.singularSlant_homologyπ_singularCohomologyMap_snd_eq_self`). This uses
  the shuffle product of a vertex with a simplex
  (`TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_snd`).

So if a class on `X × Y` is `pr₁^* e + φ`, for instance the first Chern class
`c₁(pr₁^* E ⊗ U) = pr₁^* c₁(E) + c₁(U)` of a line bundle twisted by a line bundle `E` on `X`, then
its slant products by the point class (`p = 0`, `q = 2`) and by loops (`p = 1`, `q = 1`) are those
of `φ`: the class `pr₁^* e` contributes to neither. Classes pulled back from `Y` survive the slant
by a point and are killed by the slant by a loop.

## Main definitions and results

* `TopCat.singularSlant`: the slant product `Hₚ(X; R) × Hⁿ(X × Y; T, M) ⟶ H^q(Y; S, M)`.
* `TopCat.singularSlant_homologyπ`: its value on classes of cycles and cocycles.
* `TopCat.singularKronecker_singularSlant`: the evaluation law `⟨φ / x, y⟩ = ⟨φ, u_*(x × y)⟩`.
* `TopCat.singularSlant_naturality`: naturality in both spaces.
* `TopCat.singularSlant_singularCohomologyMap_fst_eq_zero` and
  `TopCat.singularSlant_singularCohomologyMap_snd_eq_zero`: the vanishing of the slant product of a
  class pulled back from one factor in the degrees where the cohomology or homology of a point
  vanishes.
* `TopCat.singularSlant_homologyπ_singularCohomologyMap_snd` and
  `TopCat.singularSlant_homologyπ_singularCohomologyMap_snd_eq_self`: the slant product of a class
  pulled back from `Y` by the class of a point of `X`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product of
  singular homology and cohomology).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII (products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Simplicial

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

/-- **A class pulled back from the first factor has no slant products in positive codegree**: for
`a ∈ Hⁿ(X; T, M)` and `x ∈ Hₚ(X; R)` with `p + q = n` and `q ≠ 0`, `pr₁^* a / x = 0`. In particular
`pr₁^* a` contributes nothing to the slant products by the class of a point (`p = 0`) or by a loop
(`p = 1`) of a class of degree two. -/
theorem singularSlant_singularCohomologyMap_fst_eq_zero (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T)
    (p q n : ℕ) (h : p + q = n) (hq : q ≠ 0)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (a : X.singularCohomology T k M n) :
    singularSlant k M X Y u p q n h x
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.fst X Y) n a) = 0 := by
  -- `pr₁ = pr₁ ∘ (𝟙 × g)` for the map `g` from `Y` to a point, and slant products of classes on
  -- `X × pt` lie in `H^q(pt) = 0`
  let g : Y ⟶ TopCat.of PUnit.{w + 1} := ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩
  rw [← CartesianMonoidalCategory.whiskerLeft_fst X g, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, ← id_tensorHom, singularSlant_naturality]
  have := ModuleCat.subsingleton_of_isZero
    (TauCeti.isZero_singularCohomology_point S k M (TopCat.of PUnit.{w + 1}) hq)
  rw [Subsingleton.elim (singularSlant k M X _ u p q n h _ _) 0, map_zero]

/-- **A class pulled back from the second factor has no slant products by classes of positive
degree**: for `b ∈ Hⁿ(Y; T, M)` and `x ∈ Hₚ(X; R)` with `p + q = n` and `p ≠ 0`,
`pr₂^* b / x = 0`. In particular `pr₂^* b` has no slant products by loops. -/
theorem singularSlant_singularCohomologyMap_snd_eq_zero (X Y : TopCat.{w}) (u : R ⊗ S ⟶ T)
    (p q n : ℕ) (h : p + q = n) (hp : p ≠ 0)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).obj X)
    (b : Y.singularCohomology T k M n) :
    singularSlant k M X Y u p q n h x
      (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) n b) = 0 := by
  -- `pr₂ = pr₂ ∘ (f × 𝟙)` for the map `f` from `X` to a point, and `f_* x ∈ Hₚ(pt) = 0`
  let f : X ⟶ TopCat.of PUnit.{w + 1} := ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩
  rw [← CartesianMonoidalCategory.whiskerRight_snd f Y, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply, ← tensorHom_id, singularSlant_naturality]
  have := ModuleCat.subsingleton_of_isZero
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat.{w} k) p R
      (TopCat.of PUnit.{w + 1}) hp)
  rw [Subsingleton.elim (((singularHomologyFunctor (ModuleCat.{w} k) p).obj R).map f x) 0,
    map_zero, LinearMap.zero_apply, map_zero]

/-- **The slant product of a class pulled back from the second factor by the class of a point**:
let `z` be the singular `0`-cycle of `X` given by a singular vertex `x` with coefficient `r ∈ R`,
and let `c : S ⟶ T` be the coefficient map `s ↦ u (r ⊗ s)`. Then for `b ∈ H^q(Y; T, M)`,
`pr₂^* b / [z] = c^* b ∈ H^q(Y; S, M)`, the class `b` with its coefficients changed along `c`. -/
theorem singularSlant_homologyπ_singularCohomologyMap_snd (X Y : TopCat.{w})
    (u : R ⊗ S ⟶ T) (q : ℕ) (z : ((toSSet.obj X).chainComplex R).cycles 0)
    (x : (toSSet.obj X) _⦋0⦌) (r : R)
    (hz : ((toSSet.obj X).chainComplex R).iCycles 0 z = (toSSet.obj X).ιChainComplex (R := R) x r)
    (c : S ⟶ T) (hc : ∀ s, u (r ⊗ₜ s) = c s) (b : Y.singularCohomology T k M q) :
    singularSlant k M X Y u 0 q q (zero_add q) (((toSSet.obj X).chainComplex R).homologyπ 0 z)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b) =
      homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k M).map
        (((SSet.chainComplexFunctor _).map c).app (toSSet.obj Y)).op) q b := by
  refine TauCeti.ChainComplex.slant_homologyπ_zero_homologyMap _
    (SSet.chainComplexMap (toSSet.map (CartesianMonoidalCategory.snd X Y)) T) _ z q ?_ b
  -- on the summand of a singular simplex `y` of `Y`, the shuffle product with `x` followed by the
  -- projection is `y`, and the coefficient `s` becomes `u (r ⊗ s) = c s`
  rw [hz]
  refine SSet.chainComplex_hom_ext (X := toSSet.obj Y) (R := S) fun y ↦ ?_
  have hy : (toSSet.obj Y).ιChainComplex (R := S) y ≫
        TauCeti.ModuleCat.tensorMk ((toSSet.obj X).ιChainComplex (R := R) x r) =
      TauCeti.ModuleCat.tensorMk r ≫
        ((toSSet.obj X).ιChainComplex x ⊗ₘ (toSSet.obj Y).ιChainComplex y) :=
    ModuleCat.hom_ext (LinearMap.ext fun s ↦ by simp [TauCeti.ModuleCat.tensorMk_apply])
  have hu : TauCeti.ModuleCat.tensorMk r ≫ u = c :=
    ModuleCat.hom_ext (LinearMap.ext fun s ↦ by simpa [TauCeti.ModuleCat.tensorMk_apply] using hc s)
  rw [SSet.ιChainComplex_chainComplexFunctor_map_app_f, reassoc_of% hy, HomologicalComplex.comp_f,
    Category.assoc, ← SSet.chainComplexMap_f_chainComplexFunctor_map_app_f,
    ιChainComplex_tensorHom_ιChainComplex_shuffle_f_snd_assoc,
    SSet.ιChainComplex_chainComplexFunctor_map_app_f, reassoc_of% hu]

/-- **Slanting a class pulled back from the second factor by a point returns the class**: for the
singular `0`-cycle `z` of `X` given by a singular vertex with coefficient `r`, and a coefficient map
`u : R ⊗ S ⟶ S` with `u (r ⊗ s) = s`, such as the unit `1` of a ring `R = S = k` and the
multiplication `k ⊗ k ⟶ k`, `pr₂^* b / [z] = b` for every `b ∈ H^q(Y; S, M)`. -/
theorem singularSlant_homologyπ_singularCohomologyMap_snd_eq_self (X Y : TopCat.{w})
    (u : R ⊗ S ⟶ S) (q : ℕ) (z : ((toSSet.obj X).chainComplex R).cycles 0)
    (x : (toSSet.obj X) _⦋0⦌) (r : R)
    (hz : ((toSSet.obj X).chainComplex R).iCycles 0 z = (toSSet.obj X).ιChainComplex (R := R) x r)
    (hu : ∀ s, u (r ⊗ₜ s) = s) (b : Y.singularCohomology S k M q) :
    singularSlant k M X Y u 0 q q (zero_add q) (((toSSet.obj X).chainComplex R).homologyπ 0 z)
        (TopCat.singularCohomologyMap (CartesianMonoidalCategory.snd X Y) q b) = b := by
  rw [singularSlant_homologyπ_singularCohomologyMap_snd M X Y u q z x r hz (𝟙 S) hu]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, op_id]
  rw [HomologicalComplex.homologyMap_id]
  rfl

end TopCat
