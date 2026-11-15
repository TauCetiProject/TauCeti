/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.ConvexRetract

/-!
# Straightening singular simplices in a retract of a convex set

A singular simplex in a convex subset `K` of a real vector space can be replaced by the affine
simplex with the same vertices, and the straight-line homotopy joins the two. The same works in a
space `X` which is a retract of `K`: map the vertices into `K`, take the affine simplex there, and
push it back to `X` along the retraction. This is the *straightening* of singular simplices which
Gromov and Thurston use for hyperbolic manifolds, where `X` is hyperbolic space in its hyperboloid
model, `K` is the open future light cone, and the retraction is the radial projection
(`TauCeti.hyperboloidConvexRetract`).

A `TauCeti.ConvexRetract X V` records such a presentation: a convex set `K ⊆ V`, a continuous map
`embed : X → V` into `K`, and a continuous retraction `K → X` of it. For vertices `v : ι → X`, the
**straight simplex** `R.straightSimplex v` is the map from the standard simplex `Δ^ι` to `X`
sending `t` to the retraction of `∑ i, tᵢ • embed (v i)`. Its vertices are the points `v i`
(`TauCeti.ConvexRetract.straightSimplex_single`), and precomposing with the affine map induced by
`f : κ → ι` gives the straight simplex with vertices `v ∘ f`
(`TauCeti.ConvexRetract.straightSimplex_map`). The latter is what makes straightening a
morphism of simplicial sets.

* `TauCeti.ConvexRetract.straighten` is the endomorphism of the singular simplicial set of `X`
  replacing every singular simplex by the straight simplex with the same vertices. It is
  idempotent (`TauCeti.ConvexRetract.straighten_comp_straighten`).
* `TauCeti.ConvexRetract.straightenHomotopy` is a simplicial homotopy from the identity to
  `straighten`, given by the straight-line homotopy in `K` pushed back to `X`. Through
  `SSet.Homotopy.chainComplexMap` it gives a chain homotopy on singular chains, with any
  coefficients.
* Both are natural for maps `g : X → Y` covered by an affine map `L : V → W` which carries
  `embed` to `embed`, the convex set into the convex set, and commutes with the retractions
  (`TauCeti.ConvexRetract.straighten_comp_toSSet_map`,
  `TauCeti.ConvexRetract.cylinderMap_comp_toSSet_map`). For hyperbolic space these are the
  isometries, acting linearly on Minkowski space. So straightening and its homotopy commute with
  any group of isometries; this is what is needed for them to descend to the singular chains of
  a quotient of hyperbolic space by a discrete group, that is, of a hyperbolic manifold. That
  descent is not carried out here.

## References

* W. P. Thurston, *The Geometry and Topology of Three-Manifolds*, Princeton lecture notes
  (1978–1980), Section 6.1 (straightening singular simplices in hyperbolic space).
* R. Benedetti, C. Petronio, *Lectures on Hyperbolic Geometry*, Springer Universitext (1992),
  Chapter C (straight simplices and the proof of the proportionality theorem).
* M. Gromov, *Volume and bounded cohomology*, Publ. Math. IHÉS 56 (1982), 5–99, Section 2.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite Convexity

open scoped Simplicial

universe u v w

namespace TauCeti

namespace ConvexRetract

variable {X : Type u} [TopologicalSpace X] {V : Type v} [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] (R : ConvexRetract X V)

/-! ### Straightening the singular simplicial set -/

open _root_.TopCat (toSSet)

/-- **Straightening**: the endomorphism of the singular simplicial set of `X` replacing every
singular simplex by the straight simplex with the same vertices. -/
def straighten : toSSet.obj (.of X) ⟶ toSSet.obj (.of X) where
  app n := ↾fun σ ↦ ((TopCat.of X).toSSetObjEquiv n).symm
    (R.straightSimplex fun i ↦ (TopCat.of X).toSSetObjEquiv n σ (.single i))
  naturality n m θ := by
    ext σ
    apply ((TopCat.of X).toSSetObjEquiv m).injective
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply,
      Equiv.apply_symm_apply]
    have hmap (τ : (toSSet.obj (.of X)).obj n) :
        (TopCat.of X).toSSetObjEquiv m ((toSSet.obj (.of X)).map θ τ) =
          ((TopCat.of X).toSSetObjEquiv n τ).comp
            ⟨StdSimplex.map θ.unop, StdSimplex.continuous_map ℝ _⟩ := by
      ext t
      exact TopCat.toSSetObjEquiv_naturality_apply θ.unop τ t
    rw [hmap, hmap, Equiv.apply_symm_apply]
    ext t
    simp [R.straightSimplex_map, Function.comp_def]

/-- The straightening of a singular simplex is the straight simplex with the same vertices. -/
lemma toSSetObjEquiv_straighten_app (n : SimplexCategoryᵒᵖ) (σ : (toSSet.obj (.of X)).obj n) :
    (TopCat.of X).toSSetObjEquiv n (R.straighten.app n σ) =
      R.straightSimplex fun i ↦ (TopCat.of X).toSSetObjEquiv n σ (.single i) :=
  Equiv.apply_symm_apply _ _

/-- Straightening is idempotent: a straight simplex is its own straightening. -/
@[simp]
theorem straighten_comp_straighten : R.straighten ≫ R.straighten = R.straighten := by
  ext n σ
  apply ((TopCat.of X).toSSetObjEquiv n).injective
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, types_comp_apply]
  rw [toSSetObjEquiv_straighten_app, toSSetObjEquiv_straighten_app]
  simp

/-- The straight-line homotopy from singular simplices to their straightenings, as a morphism
out of the cylinder `Sing X ⊗ Δ[1]`. -/
def cylinderMap : toSSet.obj (.of X) ⊗ Δ[1] ⟶ toSSet.obj (.of X) where
  app n := ↾fun p ↦ ((TopCat.of X).toSSetObjEquiv n).symm
    (R.cylinderSimplex ((TopCat.of X).toSSetObjEquiv n p.1)
      (fun i ↦ (TopCat.of X).toSSetObjEquiv n p.1 (.single i))
      (SSet.stdSimplex.objEquiv p.2).toOrderHom)
  naturality n m θ := by
    ext p
    apply ((TopCat.of X).toSSetObjEquiv m).injective
    -- The components of a reindexed simplex of the cylinder `Sing X ⊗ Δ[1]` are the reindexed
    -- components, by definition of the cartesian product of simplicial sets.
    have hσ : (TopCat.of X).toSSetObjEquiv m (((toSSet.obj (.of X) ⊗ Δ[1]).map θ p).1) =
        ((TopCat.of X).toSSetObjEquiv n p.1).comp
          ⟨StdSimplex.map θ.unop, StdSimplex.continuous_map ℝ _⟩ :=
      rfl
    have hα : ⇑(SSet.stdSimplex.objEquiv ((toSSet.obj (.of X) ⊗ Δ[1]).map θ p).2).toOrderHom =
        ⇑(SSet.stdSimplex.objEquiv p.2).toOrderHom ∘ ⇑(ConcreteCategory.hom θ.unop) :=
      rfl
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply,
      Equiv.apply_symm_apply]
    have hmap (τ : (toSSet.obj (.of X)).obj n) :
        (TopCat.of X).toSSetObjEquiv m ((toSSet.obj (.of X)).map θ τ) =
          ((TopCat.of X).toSSetObjEquiv n τ).comp
            ⟨StdSimplex.map θ.unop, StdSimplex.continuous_map ℝ _⟩ := by
      ext t
      exact TopCat.toSSetObjEquiv_naturality_apply θ.unop τ t
    rw [hmap, Equiv.apply_symm_apply, hσ, hα, R.cylinderSimplex_comp_map]
    congr 1
    funext i
    simp

lemma toSSetObjEquiv_cylinderMap_app (n : SimplexCategoryᵒᵖ)
    (p : (toSSet.obj (.of X) ⊗ Δ[1]).obj n) :
    (TopCat.of X).toSSetObjEquiv n (R.cylinderMap.app n p) =
      R.cylinderSimplex ((TopCat.of X).toSSetObjEquiv n p.1)
        (fun i ↦ (TopCat.of X).toSSetObjEquiv n p.1 (.single i))
        (SSet.stdSimplex.objEquiv p.2).toOrderHom :=
  Equiv.apply_symm_apply _ _

/-- The straight-line homotopy is a simplicial homotopy from the identity of the singular
simplicial set to straightening. -/
def straightenHomotopy : SSet.Homotopy (𝟙 (toSSet.obj (.of X))) R.straighten :=
  SSet.Homotopy.mk' R.cylinderMap
    (by
      ext n σ
      apply ((TopCat.of X).toSSetObjEquiv n).injective
      -- On the bottom of the cylinder the `Δ[1]`-component is the constant map to `0`.
      have hα : ⇑(SSet.stdSimplex.objEquiv (SSet.ι₀.app n σ).2).toOrderHom = fun _ ↦ 0 := rfl
      simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, types_comp_apply,
        NatTrans.id_app, types_id_apply]
      -- The first component of `ι₀.app n σ` is `σ` by definition (`SSet.ι₀_app_fst`).
      rw [toSSetObjEquiv_cylinderMap_app, hα, R.cylinderSimplex_zero]
      rfl)
    (by
      ext n σ
      apply ((TopCat.of X).toSSetObjEquiv n).injective
      -- On the top of the cylinder the `Δ[1]`-component is the constant map to `1`.
      have hα : ⇑(SSet.stdSimplex.objEquiv (SSet.ι₁.app n σ).2).toOrderHom = fun _ ↦ 1 := rfl
      simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, types_comp_apply]
      -- The first component of `ι₁.app n σ` is `σ` by definition (`SSet.ι₁_app_fst`).
      rw [toSSetObjEquiv_cylinderMap_app, hα, R.cylinderSimplex_one,
        toSSetObjEquiv_straighten_app]
      rfl)

@[simp]
lemma straightenHomotopy_h : R.straightenHomotopy.h = R.cylinderMap :=
  (rfl)

/-! ### Naturality -/

section Naturality

variable {Y : Type u} [TopologicalSpace Y] {W : Type w} [AddCommGroup W] [Module ℝ W]
  [TopologicalSpace W] {R' : ConvexRetract Y W} {g : C(X, Y)} {L : V →ᵃ[ℝ] W}

variable [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  (hembed : ∀ x, L (R.embed x) = R'.embed (g x)) (hmaps : Set.MapsTo L R.carrier R'.carrier)
  (hret : ∀ v (hv : v ∈ R.carrier), R'.retraction ⟨L v, hmaps hv⟩ = g (R.retraction ⟨v, hv⟩))
include hembed hret

/-- **Naturality of straightening.** A continuous map `g : X → Y` covered by an affine map
`L : V → W` which carries `embed` to `embed` and the convex set into the convex set, and which
commutes with the retractions, commutes with straightening. -/
theorem straighten_comp_toSSet_map :
    R.straighten ≫ toSSet.map (TopCat.ofHom g) = toSSet.map (TopCat.ofHom g) ≫ R'.straighten := by
  ext n σ
  apply ((TopCat.of Y).toSSetObjEquiv n).injective
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, types_comp_apply]
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, toSSetObjEquiv_straighten_app,
    toSSetObjEquiv_straighten_app, TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  -- The continuous map underlying `TopCat.ofHom g` is `g` by definition.
  exact R.comp_straightSimplex hembed hmaps hret _

/-- **Naturality of the straightening homotopy.** A continuous map covered by a compatible affine
map commutes with the straight-line homotopy from the identity to straightening. -/
theorem cylinderMap_comp_toSSet_map :
    R.cylinderMap ≫ toSSet.map (TopCat.ofHom g) =
      toSSet.map (TopCat.ofHom g) ▷ Δ[1] ≫ R'.cylinderMap := by
  ext n p
  apply ((TopCat.of Y).toSSetObjEquiv n).injective
  simp only [TypeCat.Fun.toFun_apply, NatTrans.comp_app, types_comp_apply]
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, toSSetObjEquiv_cylinderMap_app,
    toSSetObjEquiv_cylinderMap_app]
  -- The components of `(Sing g ▷ Δ[1]).app n p` are `(Sing g).app n p.1` and `p.2`
  -- (`SSet.whiskerRight_app_apply`), and `Sing g` acts on singular simplices by postcomposition
  -- (`TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app`); both hold by definition.
  exact R.comp_cylinderSimplex hembed hmaps hret _ _ _

end Naturality

end ConvexRetract

end TauCeti
