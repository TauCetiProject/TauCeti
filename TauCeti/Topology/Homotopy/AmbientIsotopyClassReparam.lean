/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.AmbientIsotopyClass

/-!
# Source reparametrisation of ambient-isotopy classes

The geometric-topology roadmap asks for isotopy and ambient isotopy to be defined once, for
arbitrary maps, before being specialised to knot presentations such as smooth embeddings
`S¹ ↪ M`. The quotient `TauCeti.AmbientIsotopyClass X Y` already supports precomposition by any
continuous source map. This file records the invertible special case: changing source
coordinates by a homeomorphism gives an equivalence of ambient-isotopy class quotients.

This is the point-set topological reparametrisation API needed before later smooth or PL knot
presentations identify parametrised embeddings that differ by a source coordinate change. It does
not introduce a knot type or assert that a continuous class has a smooth representative.

## Main definitions

* `TauCeti.AmbientIsotopyClass.precompHomeomorphEquiv`: source reparametrisation by a
  homeomorphism, as an equivalence of ambient-isotopy class quotients.
* `TauCeti.AmbientIsotopyClass.postcompHomeomorphPrecompEquiv`: the two-sided coordinate-change
  equivalence obtained by a source homeomorphism and an ambient homeomorphism.
-/

public section

namespace TauCeti

open ContinuousMap

variable {U W X Y Z : Type*} [TopologicalSpace U] [TopologicalSpace W]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace AmbientIsotopyClass

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

/-- The two-sided coordinate-change equivalence on ambient-isotopy classes: precompose the source
by a homeomorphism and postcompose the ambient space by a homeomorphism. -/
def postcompHomeomorphPrecompEquiv (h : Y ≃ₜ Z) (e : W ≃ₜ X) :
    AmbientIsotopyClass X Y ≃ AmbientIsotopyClass W Z where
  toFun := postcompHomeomorphPrecomp h (e : C(W, X))
  invFun := postcompHomeomorphPrecomp h.symm (e.symm : C(X, W))
  left_inv x := by
    refine induction_on x ?_
    intro f
    rw [postcompHomeomorphPrecomp_mk, postcompHomeomorphPrecomp_mk]
    apply mk_eq_mk
    convert AmbientIsotopic.refl f using 1
    ext x
    simp
  right_inv x := by
    refine induction_on x ?_
    intro f
    rw [postcompHomeomorphPrecomp_mk, postcompHomeomorphPrecomp_mk]
    apply mk_eq_mk
    convert AmbientIsotopic.refl f using 1
    ext x
    simp

/-- Computation rule for two-sided coordinate change on representatives. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_mk (h : Y ≃ₜ Z) (e : W ≃ₜ X) (f : C(X, Y)) :
    postcompHomeomorphPrecompEquiv h e (mk f) =
      mk ((h : C(Y, Z)).comp (f.comp (e : C(W, X)))) :=
  postcompHomeomorphPrecomp_mk h (e : C(W, X)) f

/-- The two-sided coordinate-change equivalence factors as ambient postcomposition after source
reparametrisation. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_apply_eq (h : Y ≃ₜ Z) (e : W ≃ₜ X)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv h e x =
      postcompHomeomorph h (precompHomeomorphEquiv e x) := by
  exact postcompHomeomorphPrecomp_apply h (e : C(W, X)) x

/-- With the identity source reparametrisation, the two-sided coordinate-change equivalence is
ambient postcomposition. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_refl_source_apply (h : Y ≃ₜ Z)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv h (Homeomorph.refl X) x = postcompHomeomorph h x := by
  rw [postcompHomeomorphPrecompEquiv_apply_eq, precompHomeomorphEquiv_refl_apply]

/-- With the identity ambient homeomorphism, the two-sided coordinate-change equivalence is source
reparametrisation. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_refl_ambient_apply (e : W ≃ₜ X)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv (Homeomorph.refl Y) e x =
      precompHomeomorphEquiv e x := by
  rw [postcompHomeomorphPrecompEquiv_apply_eq, postcompHomeomorph_refl]

/-- The two-sided coordinate-change equivalence is the identity when both coordinate changes are
identities. -/
@[simp]
theorem postcompHomeomorphPrecompEquiv_refl_refl_apply (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphPrecompEquiv (Homeomorph.refl Y) (Homeomorph.refl X) x = x := by
  rw [postcompHomeomorphPrecompEquiv_refl_source_apply, postcompHomeomorph_refl]

end AmbientIsotopyClass

end TauCeti
