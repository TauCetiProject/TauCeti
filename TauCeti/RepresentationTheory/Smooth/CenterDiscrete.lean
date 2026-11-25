/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Center
import TauCeti.RepresentationTheory.Intertwining

/-!
# The smooth centre of a discrete group

A central element `c` of the group algebra `A[G]` acts on every representation of `G` by an
intertwining map `v ↦ c • v`, and these maps commute with every morphism. This gives an
`A`-algebra homomorphism `TauCeti.SmoothCenter.ofCenter` from the centre of `A[G]` to the smooth
centre `Z(G, A)`, for any topological group `G`.

For a discrete group `G` every representation is smooth, the regular representation `A[G]` among
them, and `ofCenter` is an isomorphism (`TauCeti.SmoothCenter.centerAlgEquiv`). Its inverse sends
`z` to `z` applied to `1` in the regular representation: the map `A[G] → V`, `x ↦ x • v`, is
intertwining for every vector `v` of a representation `V`, so `z` acts on `v` as `z(1)` does
(`TauCeti.SmoothCenter.app_apply_eq_asAlgebraHom`), and right multiplications are endomorphisms
of the regular representation, so `z(1)` is central.

## Main definitions

* `TauCeti.SmoothCenter.ofCenter`: the `A`-algebra homomorphism from the centre of `A[G]` to the
  smooth centre.
* `TauCeti.SmoothCenter.centerAlgEquiv`: for a discrete group, the centre of `A[G]` is isomorphic
  to `Z(G, A)`.
-/

public section

open CategoryTheory Representation

universe w u v

namespace TauCeti

namespace SmoothCenter

variable {A : Type u} [CommRing A] {G : Type v} [Group G] [TopologicalSpace G]

/-- The element of the smooth centre given by a central element `c` of `A[G]`: it acts on every
smooth representation as `c`, through `Representation.asAlgebraHom`. -/
noncomputable def ofCenterFun (c : Subalgebra.center A (MonoidAlgebra A G)) :
    SmoothCenter.{w} A G :=
  .of
    { app V := ObjectProperty.homMk
        (Rep.ofHom (IntertwiningMap.centralAlgebraMul V.obj.ρ c.property))
      naturality V W f := by
        ext v
        exact (IntertwiningMap.apply_asAlgebraHom f.hom.hom c v).symm }

/-- `ofCenterFun c` acts on `v` as `c`. -/
@[simp] lemma ofCenterFun_app_hom_hom_apply (c : Subalgebra.center A (MonoidAlgebra A G))
    (V : SmoothRep.{w} A G) (v : V.obj) :
    ((ofCenterFun c).app V).hom.hom v = V.obj.ρ.asAlgebraHom c v :=
  (rfl)

/-- A central element of `A[G]`, acting on every smooth representation, as an element of the
smooth centre: the `A`-algebra homomorphism from the centre of `A[G]` to `Z(G, A)`. -/
noncomputable def ofCenter :
    Subalgebra.center A (MonoidAlgebra A G) →ₐ[A] SmoothCenter.{w} A G where
  toFun := ofCenterFun
  map_one' := by ext; simp
  map_mul' c c' := by
    ext V v
    rw [CatCenter.mul_app]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp, IntertwiningMap.comp_apply,
      ofCenterFun_app_hom_hom_apply, Subalgebra.coe_mul]
    rw [Subalgebra.mem_center_iff.1 c'.property, map_mul, mul_apply_eq_comp]
  map_zero' := by ext; simp
  map_add' c c' := by
    ext V v
    rw [CatCenter.app_add]
    change V.obj.ρ.asAlgebraHom (c + c' : Subalgebra.center A (MonoidAlgebra A G)) v =
      V.obj.ρ.asAlgebraHom c v + V.obj.ρ.asAlgebraHom c' v
    simp
  commutes' a := by
    ext V v
    rw [algebraMap_app_hom_hom_apply]
    change V.obj.ρ.asAlgebraHom (algebraMap A (Subalgebra.center A (MonoidAlgebra A G)) a) v = _
    simp

@[simp] lemma ofCenter_app_hom_hom_apply (c : Subalgebra.center A (MonoidAlgebra A G))
    (V : SmoothRep.{w} A G) (v : V.obj) :
    ((ofCenter c).app V).hom.hom v = V.obj.ρ.asAlgebraHom c v :=
  (rfl)

section Discrete

variable [DiscreteTopology G]

/-- For a vector `v` of a representation `V` of a discrete group, the intertwining map
`A[G] → V`, `x ↦ x • v`, from the regular representation. -/
noncomputable def orbitHom (V : SmoothRep.{max u v} A G) (v : V.obj) :
    SmoothRep.of (ofMulAction A G G) ⟶ V :=
  ObjectProperty.homMk (Rep.ofHom ((LinearMap.applyₗ v ∘ₗ V.obj.ρ.asAlgebraHom.toLinearMap)
    |>.intertwiningMap_of_isIntertwiningMap _ _ fun g x ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        LinearMap.applyₗ_apply_apply]
      rw [← asAlgebraHom_of, asAlgebraHom_ofMulAction_smul_eq_mul, map_mul, mul_apply_eq_comp,
        asAlgebraHom_of]))

@[simp] lemma orbitHom_hom_hom_apply (V : SmoothRep.{max u v} A G) (v : V.obj)
    (x : MonoidAlgebra A G) :
    (orbitHom V v).hom.hom x = V.obj.ρ.asAlgebraHom x v :=
  (rfl)

/-- The value at `1` of an element `z` of the smooth centre on the regular representation. -/
noncomputable def toCenterFun (z : SmoothCenter.{max u v} A G) : MonoidAlgebra A G :=
  (z.app (SmoothRep.of (ofMulAction A G G))).hom.hom 1

/-- **An element of the smooth centre of a discrete group acts through the group algebra**: `z`
acts on every vector `v` as the element `z(1)` of `A[G]`, where `1` lies in the regular
representation. -/
lemma app_apply_eq_asAlgebraHom (z : SmoothCenter.{max u v} A G) (V : SmoothRep.{max u v} A G)
    (v : V.obj) : (z.app V).hom.hom v = V.obj.ρ.asAlgebraHom (toCenterFun z) v := by
  have := congr($(z.naturality (orbitHom V v)).hom.hom 1)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Rep.hom_comp, IntertwiningMap.comp_apply]
    at this
  rw [orbitHom_hom_hom_apply, orbitHom_hom_hom_apply, map_one, one_apply_eq_self] at this
  exact this

/-- The value `z(1)` on the regular representation is central in `A[G]`: `z` commutes with right
multiplications, which are endomorphisms of the regular representation. -/
lemma toCenterFun_mem_center (z : SmoothCenter.{max u v} A G) :
    toCenterFun z ∈ Subalgebra.center A (MonoidAlgebra A G) := by
  rw [Subalgebra.mem_center_iff]
  intro x
  have h := app_apply_eq_asAlgebraHom z (SmoothRep.of (ofMulAction A G G)) x
  have h' := IntertwiningMap.apply_asAlgebraHom (z.app (SmoothRep.of (ofMulAction A G G))).hom.hom
    x 1
  simp only [asAlgebraHom_ofMulAction_smul_eq_mul, mul_one] at h h'
  rw [← h, h']
  rfl

variable (A G) in
/-- **The smooth centre of a discrete group is the centre of the group algebra**: for `G`
discrete, `ofCenter` is an isomorphism from the centre of `A[G]` to `Z(G, A)`, with inverse
`z ↦ z(1)` on the regular representation. -/
noncomputable def centerAlgEquiv :
    Subalgebra.center A (MonoidAlgebra A G) ≃ₐ[A] SmoothCenter.{max u v} A G where
  __ := ofCenter
  invFun z := ⟨toCenterFun z, toCenterFun_mem_center z⟩
  left_inv c := Subtype.ext <| by
    change (ofMulAction A G G).asAlgebraHom c 1 = c
    simp
  right_inv z := by
    ext V v
    rw [app_apply_eq_asAlgebraHom z V v]
    rfl

@[simp] lemma centerAlgEquiv_apply (c : Subalgebra.center A (MonoidAlgebra A G)) :
    centerAlgEquiv A G c = ofCenter c :=
  (rfl)

@[simp] lemma coe_centerAlgEquiv_symm_apply (z : SmoothCenter.{max u v} A G) :
    ((centerAlgEquiv A G).symm z : MonoidAlgebra A G) =
      (z.app (SmoothRep.of (ofMulAction A G G))).hom.hom 1 :=
  (rfl)

end Discrete

end SmoothCenter

end TauCeti
