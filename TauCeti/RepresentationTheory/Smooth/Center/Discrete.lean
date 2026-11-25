/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Center.Basic

/-!
# The smooth centre of a discrete group

For a discrete group `G` every representation is smooth, the regular representation `A[G]` among
them, and the homomorphism `TauCeti.SmoothCenter.ofCenter` from the centre of `A[G]` to the smooth
centre `Z(G, A)` is an isomorphism (`TauCeti.SmoothCenter.centerAlgEquiv`). Its inverse sends `z`
to `z` applied to `1` in the regular representation: the map `A[G] → V`, `x ↦ x • v`, is
intertwining for every vector `v` of a representation `V`, so `z` acts on `v` as `z(1)` does
(`TauCeti.SmoothCenter.app_apply_eq_asAlgebraHom`), and right multiplications are endomorphisms
of the regular representation, so `z(1)` is central.

## Main definitions

* `TauCeti.SmoothCenter.centerAlgEquiv`: for a discrete group, the centre of `A[G]` is isomorphic
  to `Z(G, A)`.
-/

public section

open CategoryTheory Representation

universe u v

namespace TauCeti

namespace SmoothCenter

variable {A : Type u} [CommRing A] {G : Type v} [Group G] [TopologicalSpace G]
  [DiscreteTopology G]

/-- The value at `1` of an element `z` of the smooth centre on the regular representation. -/
private noncomputable def toCenterFun (z : SmoothCenter.{max u v} A G) : MonoidAlgebra A G :=
  (z.app (SmoothRep.of (ofMulAction A G G))).hom.hom 1

/-- `z` acts on every vector `v` as the element `toCenterFun z` of `A[G]`. -/
private lemma app_apply_eq_asAlgebraHom_toCenterFun (z : SmoothCenter.{max u v} A G)
    (V : SmoothRep.{max u v} A G) (v : V.obj) :
    (z.app V).hom.hom v = V.obj.ρ.asAlgebraHom (toCenterFun z) v := by
  have := congr($(z.naturality (SmoothRep.orbitHom V v)).hom.hom 1)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp, IntertwiningMap.comp_apply]
    at this
  rw [SmoothRep.orbitHom_hom_hom_apply, SmoothRep.orbitHom_hom_hom_apply, map_one,
    one_apply_eq_self] at this
  exact this

/-- The value `z(1)` on the regular representation is central in `A[G]`: `z` commutes with right
multiplications, which are endomorphisms of the regular representation. -/
private lemma toCenterFun_mem_center (z : SmoothCenter.{max u v} A G) :
    toCenterFun z ∈ Subalgebra.center A (MonoidAlgebra A G) := by
  rw [Subalgebra.mem_center_iff]
  intro x
  have h := app_apply_eq_asAlgebraHom_toCenterFun z (SmoothRep.of (ofMulAction A G G)) x
  have h' := IntertwiningMap.apply_asAlgebraHom (z.app (SmoothRep.of (ofMulAction A G G))).hom.hom
    x 1
  simp only [asAlgebraHom_ofMulAction_smul_eq_mul, mul_one] at h h'
  rw [← h, h', toCenterFun]

/-- `toCenterFun` is a left inverse of `ofCenter`. -/
private lemma toCenterFun_ofCenter (c : Subalgebra.center A (MonoidAlgebra A G)) :
    toCenterFun (ofCenter c) = c := by
  rw [toCenterFun, ofCenter_app_hom_hom_apply, asAlgebraHom_ofMulAction_smul_eq_mul, mul_one]

variable (A G) in
/-- **The smooth centre of a discrete group is the centre of the group algebra**: for `G`
discrete, `ofCenter` is an isomorphism from the centre of `A[G]` to `Z(G, A)`, with inverse
`z ↦ z(1)` on the regular representation. -/
noncomputable def centerAlgEquiv :
    Subalgebra.center A (MonoidAlgebra A G) ≃ₐ[A] SmoothCenter.{max u v} A G where
  __ := ofCenter
  invFun z := ⟨toCenterFun z, toCenterFun_mem_center z⟩
  left_inv c := Subtype.ext (toCenterFun_ofCenter c)
  right_inv z := by
    ext V v
    rw [app_apply_eq_asAlgebraHom_toCenterFun z V v]
    exact ofCenter_app_hom_hom_apply ⟨toCenterFun z, toCenterFun_mem_center z⟩ V v

@[simp] lemma centerAlgEquiv_apply (c : Subalgebra.center A (MonoidAlgebra A G)) :
    centerAlgEquiv A G c = ofCenter c :=
  (rfl)

@[simp] lemma coe_centerAlgEquiv_symm_apply (z : SmoothCenter.{max u v} A G) :
    ((centerAlgEquiv A G).symm z : MonoidAlgebra A G) =
      (z.app (SmoothRep.of (ofMulAction A G G))).hom.hom 1 :=
  (rfl)

/-- **An element of the smooth centre of a discrete group acts through the group algebra**: `z`
acts on every vector `v` as the element `z(1)` of `A[G]`, where `1` lies in the regular
representation. -/
lemma app_apply_eq_asAlgebraHom (z : SmoothCenter.{max u v} A G) (V : SmoothRep.{max u v} A G)
    (v : V.obj) :
    (z.app V).hom.hom v = V.obj.ρ.asAlgebraHom ((centerAlgEquiv A G).symm z) v :=
  app_apply_eq_asAlgebraHom_toCenterFun z V v

end SmoothCenter

end TauCeti
