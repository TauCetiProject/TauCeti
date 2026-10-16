/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# The fundamental group is a homeomorphism invariant

Mathlib records the homomorphism `FundamentalGroup.map` induced by a continuous map and the
variant `FundamentalGroup.mapOfEq` that adjusts the target basepoint along an equality, but it
stops short of packaging a homeomorphism as an *isomorphism* of fundamental groups. This file
supplies that: a homeomorphism `e : X ≃ₜ Y` induces a group isomorphism
`π₁(X, x) ≃* π₁(Y, e x)`, and more generally `π₁(X, x) ≃* π₁(Y, y)` whenever `e x = y`.

The forward map is `FundamentalGroup.mapOfEq` of `e`; the inverse is `FundamentalGroup.mapOfEq`
of `e.symm`. The two round trips are the composition law `mapOfEq_comp` (the induced maps of two
continuous maps compose to the induced map of their composite) applied to `e.symm ∘ e = id` and
`e ∘ e.symm = id`, together with `mapOfEq_id` (the induced map of the identity is the identity).
Both auxiliary lemmas are proved once here from Mathlib's `FundamentalGroup.mapOfEq_apply` and the
`Path.Homotopic.Quotient` transport lemmas (`map_comp`, `map_cast`, `cast_cast`), and are useful
on their own.

For nested subspaces, the induced isomorphisms commute with inclusions. The two subspace
naturality squares are public so that other fundamental-group diagrams can reuse this transport.

Transporting a fundamental-group computation across a homeomorphism is the group-level input the
universal-covers roadmap needs for its Stage 4 applications: for example the fundamental group of
the unit circle `Circle ⊆ ℂ`, obtained from the additive-circle computation through Mathlib's
`AddCircle.homeomorphCircle`, and later `π₁(ℝPⁿ)`. This mirrors the way
`TauCeti.FundamentalGroup.prodMulEquiv` supplied the product formula the torus computation needs.

## Main declarations

* `TauCeti.FundamentalGroup.mapOfEq_comp`: `mapOfEq g hg (mapOfEq f hf p) = mapOfEq (g.comp f) _ p`.
* `TauCeti.FundamentalGroup.mapOfEq_id`: `mapOfEq (ContinuousMap.id X) h = id`.
* `TauCeti.FundamentalGroup.mapOfEq_rfl`: along the reflexivity proof, `mapOfEq` is `map`.
* `TauCeti.FundamentalGroup.homeomorphMulEquivOfEq`: `π₁(X, x) ≃* π₁(Y, y)` from `e : X ≃ₜ Y`
  with `e x = y`.
* `TauCeti.FundamentalGroup.homeomorphMulEquiv`: `π₁(X, x) ≃* π₁(Y, e x)`.
* `TauCeti.FundamentalGroup.subspace_inclusion_square`: naturality for nested inclusions.
* `TauCeti.FundamentalGroup.subspace_subtypeVal_square`: naturality for subtype inclusion.
-/

public section

namespace TauCeti

namespace FundamentalGroup

open Path.Homotopic

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- The maps induced on fundamental groups by two continuous maps compose to the map induced by
their composite: `mapOfEq g hg (mapOfEq f hf p) = mapOfEq (g.comp f) _ p`. -/
theorem mapOfEq_comp (g : C(Y, Z)) (f : C(X, Y)) (hf : f x = y) (hg : g y = z)
    (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq g hg (_root_.FundamentalGroup.mapOfEq f hf p) =
      _root_.FundamentalGroup.mapOfEq (g.comp f)
        (show (g.comp f) x = z by rw [ContinuousMap.comp_apply, hf, hg]) p := by
  simp only [_root_.FundamentalGroup.mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast,
    ← Path.Homotopic.Quotient.map_comp]

/-- The map induced on fundamental groups by the identity continuous map is the identity. -/
@[simp]
theorem mapOfEq_id (h : (ContinuousMap.id X) x = x) (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq (ContinuousMap.id X) h p = p := by
  have key : ∀ q : Path.Homotopic.Quotient x x,
      Path.Homotopic.Quotient.map q (ContinuousMap.id X) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h γ => exact congrArg _ (Path.map_id γ)
  rw [_root_.FundamentalGroup.mapOfEq_apply, key]
  exact CategoryTheory.End.ext (Path.Homotopic.Quotient.cast_rfl_rfl p.asHom)

/-- Transporting the target basepoint along the reflexivity proof does nothing: `mapOfEq f rfl`
is Mathlib's `FundamentalGroup.map f x`.

This is the comparison needed whenever a statement phrased with a general basepoint equation
`f x = y` is applied to a lifting criterion phrased at the basepoint `f x` itself. -/
@[simp]
theorem mapOfEq_rfl (f : C(X, Y)) :
    _root_.FundamentalGroup.mapOfEq f (rfl : f x = f x) = _root_.FundamentalGroup.map f x := by
  ext γ
  rw [_root_.FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- The induced map `mapOfEq` depends only on the underlying continuous map, not on the chosen
proof of the basepoint equation: two equal continuous maps induce the same map. -/
theorem mapOfEq_congr {f₁ f₂ : C(X, Y)} (hfe : f₁ = f₂) (h₁ : f₁ x = y) (h₂ : f₂ x = y)
    (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq f₁ h₁ p = _root_.FundamentalGroup.mapOfEq f₂ h₂ p := by
  subst hfe
  rfl

/-- If `g ∘ f` is the identity, then the induced map of `g` undoes the induced map of `f`. -/
theorem mapOfEq_mapOfEq_of_comp_eq_id (g : C(Y, X)) (f : C(X, Y)) (hf : f x = y) (hg : g y = x)
    (hgf : g.comp f = ContinuousMap.id X) (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq g hg (_root_.FundamentalGroup.mapOfEq f hf p) = p := by
  rw [mapOfEq_comp g f hf hg]
  exact (mapOfEq_congr hgf _ rfl p).trans (mapOfEq_id rfl p)

/-- A homeomorphism `e : X ≃ₜ Y` carrying `x` to `y` induces an isomorphism of fundamental groups
`π₁(X, x) ≃* π₁(Y, y)`. The forward map is `FundamentalGroup.mapOfEq` of `e`; the inverse is
`FundamentalGroup.mapOfEq` of `e.symm`. -/
@[expose] noncomputable def homeomorphMulEquivOfEq (e : X ≃ₜ Y) (h : e x = y) :
    _root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y y where
  toFun := _root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
  invFun := _root_.FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (show e.symm y = x by rw [← h, e.symm_apply_apply])
  left_inv p :=
    mapOfEq_mapOfEq_of_comp_eq_id ⟨e.symm, e.symm.continuous⟩ ⟨e, e.continuous⟩ h
      (show e.symm y = x by rw [← h, e.symm_apply_apply])
      (ContinuousMap.ext fun t => e.symm_apply_apply t) p
  right_inv q :=
    mapOfEq_mapOfEq_of_comp_eq_id ⟨e, e.continuous⟩ ⟨e.symm, e.symm.continuous⟩
      (show e.symm y = x by rw [← h, e.symm_apply_apply]) h
      (ContinuousMap.ext fun t => e.apply_symm_apply t) q
  map_mul' := (_root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h).map_mul

@[simp]
theorem homeomorphMulEquivOfEq_apply (e : X ≃ₜ Y) (h : e x = y) (p : _root_.FundamentalGroup X x) :
    homeomorphMulEquivOfEq e h p = _root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h p :=
  rfl

@[simp]
theorem homeomorphMulEquivOfEq_symm_apply (e : X ≃ₜ Y) (h : e x = y)
    (q : _root_.FundamentalGroup Y y) : (homeomorphMulEquivOfEq e h).symm q =
      _root_.FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
        (show e.symm y = x by rw [← h, e.symm_apply_apply]) q :=
  rfl

/-- A homeomorphism `e : X ≃ₜ Y` induces an isomorphism of fundamental groups
`π₁(X, x) ≃* π₁(Y, e x)`. -/
@[expose] noncomputable def homeomorphMulEquiv (e : X ≃ₜ Y) (x : X) :
    _root_.FundamentalGroup X x ≃* _root_.FundamentalGroup Y (e x) :=
  homeomorphMulEquivOfEq e rfl

@[simp]
theorem homeomorphMulEquiv_apply (e : X ≃ₜ Y) (x : X) (p : _root_.FundamentalGroup X x) :
    homeomorphMulEquiv e x p =
      _root_.FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ rfl p :=
  rfl

@[simp]
theorem homeomorphMulEquiv_symm_apply (e : X ≃ₜ Y) (x : X) (q : _root_.FundamentalGroup Y (e x)) :
    (homeomorphMulEquiv e x).symm q =
      _root_.FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x) q :=
  rfl

section Subspace

open CategoryTheory Set

/-- Inclusions between nested subspaces commute on fundamental groups after the canonical
homeomorphisms that forget the containing subspace. -/
theorem subspace_inclusion_square {C S T : Set X}
    (hSC : S ⊆ C) (hTC : T ⊆ C) (hST : S ⊆ T) (x : X) (hxS : x ∈ S) :
    let S' : Set C := Subtype.val ⁻¹' S
    let T' : Set C := Subtype.val ⁻¹' T
    let eS : S' ≃ₜ S := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun s hs => ⟨⟨s, hSC hs⟩, rfl⟩)
    let eT : T' ≃ₜ T := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun t ht => ⟨⟨t, hTC ht⟩, rfl⟩)
    let x' : C := ⟨x, hSC hxS⟩
    GrpCat.ofHom (_root_.FundamentalGroup.map
        (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T')) ⟨x', hxS⟩) ≫
        (homeomorphMulEquivOfEq eT rfl).toGrpIso.hom =
      (homeomorphMulEquivOfEq eS rfl).toGrpIso.hom ≫
        GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion hST) ⟨x, hxS⟩) := by
  intro S' T' eS eT x'
  apply GrpCat.ext
  intro p
  -- Pin the group carriers before unfolding the categorical wrappers: composition simp
  -- cannot infer them through the homeomorphism-induced isomorphisms at nested subtypes.
  change homeomorphMulEquivOfEq eT rfl
      (_root_.FundamentalGroup.map (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T'))
        (⟨x', hxS⟩ : S') p) =
    _root_.FundamentalGroup.map (ContinuousMap.inclusion hST) ⟨x, hxS⟩
      (homeomorphMulEquivOfEq eS rfl p)
  rw [homeomorphMulEquivOfEq_apply,
    homeomorphMulEquivOfEq_apply,
    ← mapOfEq_rfl (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T')),
    ← mapOfEq_rfl (ContinuousMap.inclusion hST)]
  exact (mapOfEq_comp ⟨eT, eT.continuous⟩
    (ContinuousMap.inclusion (preimage_mono hST : S' ⊆ T')) rfl rfl p).trans
    ((mapOfEq_congr
      (f₂ := (ContinuousMap.inclusion hST).comp ⟨eS, eS.continuous⟩)
      (by ext z; rfl) _ _ p).trans
      (mapOfEq_comp (ContinuousMap.inclusion hST)
        ⟨eS, eS.continuous⟩ rfl rfl p).symm)

/-- Inclusion of a nested subspace into its ambient subspace factors through the canonical
homeomorphism that forgets one subtype layer. -/
theorem subspace_subtypeVal_square {C S : Set X}
    (hSC : S ⊆ C) (x : X) (hxS : x ∈ S) :
    let S' : Set C := Subtype.val ⁻¹' S
    let eS : S' ≃ₜ S := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun s hs => ⟨⟨s, hSC hs⟩, rfl⟩)
    let x' : C := ⟨x, hSC hxS⟩
    GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.subtypeVal S') ⟨x', hxS⟩) =
      (homeomorphMulEquivOfEq eS rfl).toGrpIso.hom ≫
        GrpCat.ofHom (_root_.FundamentalGroup.map (ContinuousMap.inclusion hSC) ⟨x, hxS⟩) := by
  intro S' eS x'
  apply GrpCat.ext
  intro p
  -- As in the overlap square, expose the induced maps after fixing their group carriers.
  change _root_.FundamentalGroup.map (ContinuousMap.subtypeVal S') ⟨x', hxS⟩ p =
    _root_.FundamentalGroup.map (ContinuousMap.inclusion hSC) ⟨x, hxS⟩
      (homeomorphMulEquivOfEq eS rfl p)
  rw [homeomorphMulEquivOfEq_apply,
    ← mapOfEq_rfl (ContinuousMap.inclusion hSC),
    ← mapOfEq_rfl (ContinuousMap.subtypeVal S')]
  -- The canonical homeomorphism forgets the outer subtype, so composing it with
  -- inclusion is definitionally the subtype-value map.
  exact (mapOfEq_comp (ContinuousMap.inclusion hSC)
    ⟨eS, eS.continuous⟩ rfl rfl p).symm

end Subspace

end FundamentalGroup

end TauCeti
