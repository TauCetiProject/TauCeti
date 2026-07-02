/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.AmbientIsotopicNaturality

/-!
# Ambient-isotopy classes of continuous maps

The geometric-topology roadmap asks for isotopy and ambient isotopy to be defined once, in full
generality, before specialising to locally flat embeddings, diffeotopies, knots, and concordance.
`TauCeti.AmbientIsotopic` is the general continuous ambient-isotopy relation on maps
`C(X, Y)`. This file packages its quotient and records the coordinate-change maps induced by
precomposition on the source and by homeomorphisms of the ambient space.

This is deliberately a point-set topological layer. Smooth and PL embedding presentations can
specialise it by mapping their bundled embeddings to the underlying continuous maps, while keeping
their own stronger smooth or PL data elsewhere.

## Main definitions

* `TauCeti.AmbientIsotopyClass X Y`: continuous maps `X → Y` modulo ambient isotopy of `Y`.
* `TauCeti.AmbientIsotopyClass.lift`: descend ambient-isotopy-invariant functions.
* `TauCeti.AmbientIsotopyClass.map`: descend ambient-isotopy-preserving operations.
* `TauCeti.AmbientIsotopyClass.map₂`: descend binary ambient-isotopy-preserving operations.
* `TauCeti.AmbientIsotopyClass.precomp`: precompose classes by a continuous source map.
* `TauCeti.AmbientIsotopyClass.precompHomeomorphEquiv`: the quotient equivalence induced by a
  homeomorphism of source spaces.
* `TauCeti.AmbientIsotopyClass.postcompHomeomorph`: postcompose classes by a homeomorphism of
  ambient spaces.
* `TauCeti.AmbientIsotopyClass.postcompHomeomorphEquiv`: the quotient equivalence induced by a
  homeomorphism of ambient spaces.

The relation follows Burde--Zieschang, *Knots*, Chapter 1, Definitions 1.1 and 1.2, via
`TauCeti.Topology.Homotopy.AmbientIsotopic`.

The quotient, lift, and map API is adapted from
`TauCeti.Geometry.Manifold.SmoothEmbedding.AmbientIsotopyClass`.
-/

public section

namespace TauCeti

open ContinuousMap

variable {U W X Y Z X' Y' : Type*} [TopologicalSpace U] [TopologicalSpace W]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace X']
  [TopologicalSpace Y']

/-- Continuous maps `X → Y` modulo ambient isotopy of the ambient space `Y`. -/
abbrev AmbientIsotopyClass (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] : Type _ :=
  Quotient (AmbientIsotopic.setoid X Y)

namespace AmbientIsotopyClass

variable {f g : C(X, Y)}

/-- The ambient-isotopy class of a continuous map. -/
abbrev mk (f : C(X, Y)) : AmbientIsotopyClass X Y :=
  Quotient.mk (AmbientIsotopic.setoid X Y) f

/-- Equality of two quotient representatives is equivalent to ambient isotopy. -/
@[simp]
theorem mk_eq_mk_iff : mk f = mk g ↔ AmbientIsotopic f g := by
  rw [mk, mk, Quotient.eq]
  exact AmbientIsotopic.setoid_r_iff

/-- Ambient-isotopic maps determine the same ambient-isotopy class. -/
theorem mk_eq_mk (hfg : AmbientIsotopic f g) : mk f = mk g :=
  mk_eq_mk_iff.2 hfg

/-- Equality of ambient-isotopy classes of representatives recovers ambient isotopy. -/
theorem ambientIsotopic_of_mk_eq (hfg : mk f = mk g) : AmbientIsotopic f g :=
  mk_eq_mk_iff.1 hfg

/-- Prove a proposition about ambient-isotopy classes by checking representatives. -/
@[elab_as_elim]
theorem induction_on {motive : AmbientIsotopyClass X Y → Prop} (x : AmbientIsotopyClass X Y)
    (h : ∀ f : C(X, Y), motive (mk f)) : motive x :=
  Quotient.inductionOn x h

/-- Two functions out of ambient-isotopy classes are equal if they agree on representatives. -/
theorem funext {β : Sort*} {F G : AmbientIsotopyClass X Y → β}
    (h : ∀ f : C(X, Y), F (mk f) = G (mk f)) : F = G :=
  _root_.funext fun x => induction_on x h

/-- Descend a function on continuous maps to ambient-isotopy classes.

The hypothesis says exactly that the function is invariant under ambient isotopy. -/
def lift {β : Sort*} (F : C(X, Y) → β)
    (hF : ∀ ⦃f g : C(X, Y)⦄, AmbientIsotopic f g → F f = F g) :
    AmbientIsotopyClass X Y → β :=
  Quotient.lift F fun f g hfg => hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg)

/-- Computation rule for `AmbientIsotopyClass.lift` on representatives. -/
@[simp]
theorem lift_mk {β : Sort*} (F : C(X, Y) → β)
    (hF : ∀ ⦃f g : C(X, Y)⦄, AmbientIsotopic f g → F f = F g) (f : C(X, Y)) :
    lift F hF (mk f) = F f :=
  Quotient.lift_mk F
    (fun f g hfg => hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg)) f

/-- A function on ambient-isotopy classes agreeing with a descended function on representatives is
equal to that descended function. -/
theorem lift_unique {β : Sort*} (F : C(X, Y) → β)
    (hF : ∀ ⦃f g : C(X, Y)⦄, AmbientIsotopic f g → F f = F g)
    (G : AmbientIsotopyClass X Y → β) (hG : ∀ f : C(X, Y), G (mk f) = F f) :
    G = lift F hF :=
  funext fun f => by simp [hG f]

/-- Descend an ambient-isotopy-preserving map between continuous-map types to their quotients. -/
def map (F : C(X, Y) → C(W, Z))
    (hF : ∀ ⦃f g : C(X, Y)⦄, AmbientIsotopic f g → AmbientIsotopic (F f) (F g)) :
    AmbientIsotopyClass X Y → AmbientIsotopyClass W Z :=
  Quotient.map F fun {f g} hfg =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg))

/-- Computation rule for `AmbientIsotopyClass.map` on representatives. -/
@[simp]
theorem map_mk (F : C(X, Y) → C(W, Z))
    (hF : ∀ ⦃f g : C(X, Y)⦄, AmbientIsotopic f g → AmbientIsotopic (F f) (F g))
    (f : C(X, Y)) : map F hF (mk f) = mk (F f) :=
  Quotient.map_mk F
    (fun {f g} hfg =>
      AmbientIsotopic.setoid_r_iff.2
        (hF (f := f) (g := g) (AmbientIsotopic.setoid_r_iff.1 hfg)))
    f

/-- Descend a binary ambient-isotopy-preserving operation between continuous-map types to their
ambient-isotopy quotients. -/
def map₂ (F : C(X, Y) → C(X', Y') → C(W, Z))
    (hF : ∀ ⦃f f' : C(X, Y)⦄, AmbientIsotopic f f' →
      ∀ ⦃g g' : C(X', Y')⦄, AmbientIsotopic g g' → AmbientIsotopic (F f g) (F f' g')) :
    AmbientIsotopyClass X Y → AmbientIsotopyClass X' Y' → AmbientIsotopyClass W Z :=
  Quotient.map₂ F fun {_ _} hff' {_ _} hgg' =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (AmbientIsotopic.setoid_r_iff.1 hff') (AmbientIsotopic.setoid_r_iff.1 hgg'))

/-- Computation rule for `AmbientIsotopyClass.map₂` on representatives. -/
@[simp]
theorem map₂_mk_mk (F : C(X, Y) → C(X', Y') → C(W, Z))
    (hF : ∀ ⦃f f' : C(X, Y)⦄, AmbientIsotopic f f' →
      ∀ ⦃g g' : C(X', Y')⦄, AmbientIsotopic g g' → AmbientIsotopic (F f g) (F f' g'))
    (f : C(X, Y)) (g : C(X', Y')) :
    map₂ F hF (mk f) (mk g) = mk (F f g) :=
  (Quotient.map₂_mk F (fun {_ _} hff' {_ _} hgg' =>
    AmbientIsotopic.setoid_r_iff.2
      (hF (AmbientIsotopic.setoid_r_iff.1 hff')
        (AmbientIsotopic.setoid_r_iff.1 hgg'))) f g)

/-- Precompose an ambient-isotopy class by a continuous map of source spaces.

An ambient isotopy acts only on the codomain, so precomposition by any continuous map is
well-defined on classes. -/
def precomp (e : C(W, X)) : AmbientIsotopyClass X Y → AmbientIsotopyClass W Y :=
  map (fun f => f.comp e) fun {f g} (hfg : AmbientIsotopic f g) =>
    AmbientIsotopic.precomp hfg e

/-- Computation rule for precomposition on representatives. -/
@[simp]
theorem precomp_mk (e : C(W, X)) (f : C(X, Y)) : precomp e (mk f) = mk (f.comp e) :=
  map_mk (fun f => f.comp e)
    (fun {f g} (hfg : AmbientIsotopic f g) => AmbientIsotopic.precomp hfg e) f

/-- Precomposition by the identity source map is the identity on ambient-isotopy classes. -/
@[simp]
theorem precomp_id (x : AmbientIsotopyClass X Y) : precomp (ContinuousMap.id X) x = x := by
  refine induction_on x ?_
  intro f
  simp

/-- Source precomposition is functorial on ambient-isotopy classes. -/
@[simp]
theorem precomp_comp (e : C(W, X)) (d : C(U, W)) (x : AmbientIsotopyClass X Y) :
    precomp d (precomp e x) = precomp (e.comp d) x := by
  refine induction_on x ?_
  intro f
  simp

/-- The equivalence of ambient-isotopy class quotients induced by a homeomorphism of source
spaces.

The map sends the class of `f : C(X, Y)` to the class of `f ∘ h`, where `h : W ≃ₜ X`. -/
def precompHomeomorphEquiv (h : W ≃ₜ X) :
    AmbientIsotopyClass X Y ≃ AmbientIsotopyClass W Y where
  toFun := precomp (h : C(W, X))
  invFun := precomp (h.symm : C(X, W))
  left_inv x := by
    refine induction_on x ?_
    intro f
    rw [precomp_mk, precomp_mk]
    apply mk_eq_mk
    convert AmbientIsotopic.refl f using 1
    ext x
    simp
  right_inv x := by
    refine induction_on x ?_
    intro f
    rw [precomp_mk, precomp_mk]
    apply mk_eq_mk
    convert AmbientIsotopic.refl f using 1
    ext x
    simp

/-- Computation rule for source-homeomorphism reparametrisation on representatives. -/
@[simp]
theorem precompHomeomorphEquiv_mk (h : W ≃ₜ X) (f : C(X, Y)) :
    precompHomeomorphEquiv h (mk f) = mk (f.comp (h : C(W, X))) :=
  precomp_mk (h : C(W, X)) f

/-- The inverse of source reparametrisation is reparametrisation by the inverse source
homeomorphism. -/
@[simp]
theorem precompHomeomorphEquiv_symm_apply (h : W ≃ₜ X) (x : AmbientIsotopyClass W Y) :
    (precompHomeomorphEquiv h).symm x = precompHomeomorphEquiv h.symm x := by
  refine induction_on x ?_
  intro f
  simp [precompHomeomorphEquiv]

/-- Reparametrisation by the identity homeomorphism is the identity on ambient-isotopy classes. -/
@[simp]
theorem precompHomeomorphEquiv_refl_apply (x : AmbientIsotopyClass X Y) :
    precompHomeomorphEquiv (Homeomorph.refl X) x = x := by
  exact precomp_id x

/-- Source-homeomorphism reparametrisation is functorial on ambient-isotopy classes. -/
@[simp]
theorem precompHomeomorphEquiv_trans_apply (h : W ≃ₜ X) (k : U ≃ₜ W)
    (x : AmbientIsotopyClass X Y) :
    precompHomeomorphEquiv k (precompHomeomorphEquiv h x) =
      precompHomeomorphEquiv (k.trans h) x := by
  exact precomp_comp (h : C(W, X)) (k : C(U, W)) x

/-- Postcompose an ambient-isotopy class by a homeomorphism of ambient spaces. -/
def postcompHomeomorph (h : Y ≃ₜ Z) : AmbientIsotopyClass X Y → AmbientIsotopyClass X Z :=
  map (fun f => (h : C(Y, Z)).comp f) fun {f g} (hfg : AmbientIsotopic f g) =>
    AmbientIsotopic.postcomp_homeomorph hfg h

/-- Computation rule for postcomposition by a homeomorphism on representatives. -/
@[simp]
theorem postcompHomeomorph_mk (h : Y ≃ₜ Z) (f : C(X, Y)) :
    postcompHomeomorph h (mk f) = mk ((h : C(Y, Z)).comp f) :=
  map_mk (fun f => (h : C(Y, Z)).comp f)
    (fun {f g} (hfg : AmbientIsotopic f g) => AmbientIsotopic.postcomp_homeomorph hfg h) f

/-- Postcomposition by the identity ambient homeomorphism is the identity on ambient-isotopy
classes. -/
@[simp]
theorem postcompHomeomorph_refl (x : AmbientIsotopyClass X Y) :
    postcompHomeomorph (Homeomorph.refl Y) x = x := by
  refine induction_on x ?_
  intro f
  simp

/-- Ambient-homeomorphism postcomposition is functorial on ambient-isotopy classes. -/
@[simp]
theorem postcompHomeomorph_trans (h : Y ≃ₜ Z) (k : Z ≃ₜ U)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorph k (postcompHomeomorph h x) = postcompHomeomorph (h.trans k) x := by
  refine induction_on x ?_
  intro f
  simp

/-- The equivalence of ambient-isotopy class quotients induced by a homeomorphism of ambient
spaces. -/
def postcompHomeomorphEquiv (h : Y ≃ₜ Z) : AmbientIsotopyClass X Y ≃ AmbientIsotopyClass X Z where
  toFun := postcompHomeomorph h
  invFun := postcompHomeomorph h.symm
  left_inv x := by
    refine induction_on x ?_
    intro f
    rw [postcompHomeomorph_mk, postcompHomeomorph_mk]
    apply mk_eq_mk
    convert AmbientIsotopic.refl f using 1
    ext x
    simp
  right_inv x := by
    refine induction_on x ?_
    intro f
    rw [postcompHomeomorph_mk, postcompHomeomorph_mk]
    apply mk_eq_mk
    convert AmbientIsotopic.refl f using 1
    ext x
    simp

/-- Computation rule for the homeomorphism-induced quotient equivalence on representatives. -/
@[simp]
theorem postcompHomeomorphEquiv_mk (h : Y ≃ₜ Z) (f : C(X, Y)) :
    postcompHomeomorphEquiv h (mk f) = mk ((h : C(Y, Z)).comp f) :=
  postcompHomeomorph_mk h f

/-- The two-sided coordinate-change map on ambient-isotopy classes: precompose the source by a
continuous map and postcompose the ambient space by a homeomorphism. -/
def postcompHomeomorphPrecomp (h : Y ≃ₜ Z) (e : C(W, X)) :
    AmbientIsotopyClass X Y → AmbientIsotopyClass W Z :=
  map (fun f => (h : C(Y, Z)).comp (f.comp e)) fun {f g} (hfg : AmbientIsotopic f g) =>
    AmbientIsotopic.postcomp_homeomorph_precomp hfg h e

/-- Computation rule for the two-sided coordinate-change map on representatives. -/
theorem postcompHomeomorphPrecomp_mk (h : Y ≃ₜ Z) (e : C(W, X)) (f : C(X, Y)) :
    postcompHomeomorphPrecomp h e (mk f) = mk ((h : C(Y, Z)).comp (f.comp e)) :=
  map_mk (fun f => (h : C(Y, Z)).comp (f.comp e))
    (fun {f g} (hfg : AmbientIsotopic f g) =>
      AmbientIsotopic.postcomp_homeomorph_precomp hfg h e) f

/-- The two-sided coordinate-change map is postcomposition after source precomposition. -/
@[simp]
theorem postcompHomeomorphPrecomp_apply (h : Y ≃ₜ Z) (e : C(W, X))
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecomp h e x = postcompHomeomorph h (precomp e x) := by
  refine induction_on x ?_
  intro f
  simp [postcompHomeomorphPrecomp_mk]

/-- The two-sided coordinate-change map equals the composite of the primitive coordinate-change
maps. -/
theorem postcompHomeomorphPrecomp_eq_postcompHomeomorph_comp_precomp (h : Y ≃ₜ Z)
    (e : C(W, X)) :
    postcompHomeomorphPrecomp h e = postcompHomeomorph h ∘ precomp e := by
  funext x
  simp

/-- The two-sided coordinate-change equivalence on ambient-isotopy classes: precompose the source
by a homeomorphism and postcompose the ambient space by a homeomorphism. -/
def postcompHomeomorphPrecompEquiv (h : Y ≃ₜ Z) (e : W ≃ₜ X) :
    AmbientIsotopyClass X Y ≃ AmbientIsotopyClass W Z :=
  (precompHomeomorphEquiv e).trans (postcompHomeomorphEquiv h)

/-- Computation rule for two-sided coordinate change on representatives. -/
theorem postcompHomeomorphPrecompEquiv_mk (h : Y ≃ₜ Z) (e : W ≃ₜ X) (f : C(X, Y)) :
    postcompHomeomorphPrecompEquiv h e (mk f) =
      mk ((h : C(Y, Z)).comp (f.comp (e : C(W, X)))) :=
  postcompHomeomorphPrecomp_mk h (e : C(W, X)) f

/-- The inverse of two-sided coordinate change is the two-sided coordinate change by the inverse
homeomorphisms. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_symm_apply (h : Y ≃ₜ Z) (e : W ≃ₜ X)
    (x : AmbientIsotopyClass W Z) :
    (postcompHomeomorphPrecompEquiv h e).symm x =
      postcompHomeomorphPrecompEquiv h.symm e.symm x := by
  refine induction_on x ?_
  intro f
  apply mk_eq_mk
  convert AmbientIsotopic.refl ((h.symm : C(Z, Y)).comp (f.comp (e.symm : C(X, W)))) using 1
  ext x
  simp

/-- The two-sided coordinate-change equivalence factors as ambient postcomposition after source
reparametrisation. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_apply_eq (h : Y ≃ₜ Z) (e : W ≃ₜ X)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv h e x =
      postcompHomeomorph h (precompHomeomorphEquiv e x) := by
  rfl

/-- Two-sided coordinate change is functorial for iterated coordinate changes. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_trans_apply (h : Y ≃ₜ Z) (k : Z ≃ₜ Y')
    (e : W ≃ₜ X) (d : X' ≃ₜ W) (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv k d (postcompHomeomorphPrecompEquiv h e x) =
      postcompHomeomorphPrecompEquiv (h.trans k) (d.trans e) x := by
  refine induction_on x ?_
  intro f
  simp

/-- With the identity source reparametrisation, the two-sided coordinate-change equivalence is
ambient postcomposition. -/
theorem postcompHomeomorphPrecompEquiv_refl_source_apply (h : Y ≃ₜ Z)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv h (Homeomorph.refl X) x = postcompHomeomorph h x := by
  rw [postcompHomeomorphPrecompEquiv_apply_eq, precompHomeomorphEquiv_refl_apply]

/-- With the identity ambient homeomorphism, the two-sided coordinate-change equivalence is source
reparametrisation. -/
theorem postcompHomeomorphPrecompEquiv_refl_ambient_apply (e : W ≃ₜ X)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv (Homeomorph.refl Y) e x =
      precompHomeomorphEquiv e x := by
  rw [postcompHomeomorphPrecompEquiv_apply_eq, postcompHomeomorph_refl]

/-- The two-sided coordinate-change equivalence is the identity when both coordinate changes are
identities. -/
theorem postcompHomeomorphPrecompEquiv_refl_refl_apply (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv (Homeomorph.refl Y) (Homeomorph.refl X) x = x := by
  rw [postcompHomeomorphPrecompEquiv_refl_source_apply, postcompHomeomorph_refl]

end AmbientIsotopyClass

end TauCeti
