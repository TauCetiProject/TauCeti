/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Stalk

import TauCeti.Topology.KrullDimension.Basic

/-!
# The generic point of an irreducible scheme and the specialization order

The points of a scheme are ordered by specialization: `x ≤ y` when `y` generizes `x`. On an
irreducible scheme the generic point generizes every point, so it is maximal for this order, and
it is the only maximal point: a point with no proper generization is generized by the generic
point and generizes it, hence equals it because the underlying space of a scheme is T₀. Since the
points of coheight zero are the maximal ones, this identifies the points of coheight zero of an
irreducible scheme with its generic point. On an irreducible scheme of dimension at most one,
every other point then has codimension exactly one.

On an integral scheme `X`, the morphism `Spec k(X) ⟶ X` from the spectrum of the function field
to the generic point is quasi-compact, since `Spec k(X)` is a single point. Over a nonempty affine
open `U`, the preimage of `U` is all of `Spec k(X)`, and the induced ring map from `Γ(X, U)` to
its sections `k(X)` makes them a fraction field of `Γ(X, U)`. This is how the normalization of `X`
in its function field is computed on affine opens.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.isMax_genericPoint`: the generic point of an irreducible
  scheme is maximal for the specialization order;
* `TauCeti.AlgebraicGeometry.Scheme.eq_genericPoint_of_isMax`: a point of an irreducible scheme
  which is maximal for the specialization order is the generic point;
* `TauCeti.AlgebraicGeometry.Scheme.isMax_iff_eq_genericPoint`: the maximal points for the
  specialization order on an irreducible scheme are exactly the generic point;
* `TauCeti.AlgebraicGeometry.Scheme.eq_of_specializes_of_notMem`: on an irreducible scheme, a
  generization of a codimension-one point outside a nonempty open is the point itself;
* `TauCeti.AlgebraicGeometry.Scheme.coheight_eq_one_iff_ne_genericPoint`: on an irreducible
  scheme of dimension at most one, the points of codimension one are exactly the points other
  than the generic point.
* `TauCeti.AlgebraicGeometry.Scheme.eq_bot_of_genericPoint_notMem`: on an irreducible scheme, an
  open missing the generic point is empty.
* `TauCeti.AlgebraicGeometry.Scheme.subsingleton_of_genericPoint_notMem` and
  `TauCeti.AlgebraicGeometry.Scheme.subsingleton_preimage_of_genericPoint_notMem`: the sections
  over such an open, or over its preimage under any morphism, form the zero ring.
* `TauCeti.AlgebraicGeometry.Scheme.fromSpecStalk_preimage_eq_top`: the preimage under
  `Spec 𝒪_{X,x} ⟶ X` of an open containing `x` is everything.
* `TauCeti.AlgebraicGeometry.Scheme.quasiCompact_fromSpecStalk_genericPoint`: the generic point
  `Spec k(X) ⟶ X` of an integral scheme is quasi-compact.
* `TauCeti.AlgebraicGeometry.Scheme.isFractionRing_app_fromSpecStalk_genericPoint`: on an integral
  scheme, the sections of `Spec k(X)` over the preimage of a nonempty affine open `U` are a
  fraction field of `Γ(X, U)`.
* `TauCeti.AlgebraicGeometry.Scheme.algEquivAppPreimageSpecExtension`: on an integral scheme, for
  a field extension `L` of `k(X)`, the sections of `Spec L` over the preimage of a nonempty open `U`
  along `Spec L ⟶ Spec k(X) ⟶ X` are `L`, as a `Γ(X, U)`-algebra.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

namespace Scheme

universe u

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- The generic point of an irreducible scheme is maximal for the specialization order: it
generizes every point. -/
theorem isMax_genericPoint : IsMax (genericPoint X) := fun y _ ↦ genericPoint_specializes y

/-- A point of an irreducible scheme which is maximal for the specialization order, that is, a
point of coheight zero, is the generic point. -/
theorem eq_genericPoint_of_isMax {y : X} (hy : IsMax y) : y = genericPoint X :=
  (Specializes.antisymm (hy (genericPoint_specializes y)) (genericPoint_specializes y)).eq

/-- The points of an irreducible scheme which are maximal for the specialization order are
exactly the generic point. -/
theorem isMax_iff_eq_genericPoint {y : X} : IsMax y ↔ y = genericPoint X :=
  ⟨eq_genericPoint_of_isMax, fun h ↦ h ▸ isMax_genericPoint⟩

/-- On an irreducible scheme, a generization `y` of a codimension-one point `x` which lies outside a
nonempty open `U` is `x` itself: a strict generization of `x` is maximal, hence the generic point,
and the generic point lies in every nonempty open. -/
theorem eq_of_specializes_of_notMem {U : X.Opens} (hU : (U : Set X).Nonempty) {x y : X}
    (hx : Order.coheight x = 1) (hyx : y ⤳ x) (hy : y ∉ U) : y = x := by
  by_contra hne
  have hlt : x < y := ⟨hyx, fun hxy ↦ hne (Specializes.antisymm hyx hxy).eq⟩
  have hfin : Order.coheight y < ⊤ :=
    (Order.coheight_anti hlt.le).trans_lt (hx ▸ ENat.one_lt_top)
  have hmax : IsMax y := Order.coheight_eq_zero.mp <| Order.lt_one_iff.mp <|
    hx ▸ Order.coheight_strictAnti hlt hfin
  obtain ⟨u, hu⟩ := hU
  exact hy (eq_genericPoint_of_isMax hmax ▸ (genericPoint_specializes u).mem_open U.isOpen hu)

/-- On an irreducible scheme of dimension at most one, the points of codimension one are exactly
the points other than the generic point. -/
theorem coheight_eq_one_iff_ne_genericPoint
    (hX : topologicalKrullDim X ≤ 1) {y : X} : Order.coheight y = 1 ↔ y ≠ genericPoint X := by
  have hle : Order.coheight y ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hX
  rw [← hle.ge_iff_eq, Order.one_le_iff_pos, Order.coheight_pos, not_iff_not,
    isMax_iff_eq_genericPoint]

/-- On an irreducible scheme, an open which does not contain the generic point is empty: the
generic point generizes every point, so it lies in every nonempty open. -/
theorem eq_bot_of_genericPoint_notMem {U : X.Opens} (h : genericPoint X ∉ U) : U = ⊥ := by
  ext x
  exact ⟨fun hx ↦ h ((genericPoint_specializes x).mem_open U.isOpen hx), fun hx ↦ hx.elim⟩

/-- On an irreducible scheme, the ring of sections over an open missing the generic point is the
zero ring, since the open is empty. -/
theorem subsingleton_of_genericPoint_notMem {U : X.Opens} (h : genericPoint X ∉ U) :
    Subsingleton Γ(X, U) := by
  rw [eq_bot_of_genericPoint_notMem h]
  infer_instance

open CategoryTheory in
/-- On an irreducible scheme `X`, the ring of sections of any `Z ⟶ X` over the preimage of an open
missing the generic point is the zero ring, since the preimage is empty. -/
theorem subsingleton_preimage_of_genericPoint_notMem {Z : Scheme.{u}} (φ : Z ⟶ X) {U : X.Opens}
    (h : genericPoint X ∉ U) : Subsingleton Γ(Z, φ ⁻¹ᵁ U) := by
  rw [eq_bot_of_genericPoint_notMem h, Scheme.Hom.preimage_bot]
  infer_instance

/-- The preimage under `Spec 𝒪_{X,x} ⟶ X` of an open containing `x` is all of `Spec 𝒪_{X,x}`: every
point of `Spec 𝒪_{X,x}` specializes to the closed point, which lies over `x`. -/
theorem fromSpecStalk_preimage_eq_top {X : Scheme.{u}} {x : X} {U : X.Opens} (hx : x ∈ U) :
    X.fromSpecStalk x ⁻¹ᵁ U = ⊤ :=
  top_le_iff.mp fun y _ ↦ (IsLocalRing.specializes_closedPoint y).mem_open
    (X.fromSpecStalk x ⁻¹ᵁ U).isOpen
    ((Scheme.Hom.mem_preimage _).mpr (by rwa [Scheme.fromSpecStalk_closedPoint]))

open CategoryTheory in
/-- For an open `U` containing `x`, the restriction from the global sections of `Spec 𝒪_{X,x}` to
the preimage of `U` under `Spec 𝒪_{X,x} ⟶ X` is an isomorphism, since this preimage is everything.
It is the last factor of `AlgebraicGeometry.Scheme.fromSpecStalk_app`. -/
theorem isIso_presheaf_map_fromSpecStalk_preimage_le_top {X : Scheme.{u}} {x : X} {U : X.Opens}
    (hx : x ∈ U) :
    IsIso ((Spec (X.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : X.fromSpecStalk x ⁻¹ᵁ U ≤ ⊤)).op) := by
  rw [show homOfLE (le_top : X.fromSpecStalk x ⁻¹ᵁ U ≤ ⊤) =
    eqToHom (fromSpecStalk_preimage_eq_top hx) from Subsingleton.elim _ _, eqToHom_op, eqToHom_map]
  infer_instance

/-- The generic point `Spec k(X) ⟶ X` of an integral scheme is quasi-compact, since `Spec k(X)` is
a single point. -/
instance quasiCompact_fromSpecStalk_genericPoint {X : Scheme.{u}} [IsIntegral X] :
    QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
  have : Finite (Spec X.functionField) := inferInstanceAs (Finite (PrimeSpectrum X.functionField))
  ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩

open CategoryTheory in
/-- On an integral scheme `X`, the sections of `Spec k(X)` over the preimage of a nonempty affine
open `U` under `Spec k(X) ⟶ X` are a fraction field of `Γ(X, U)`: the preimage is all of
`Spec k(X)`, whose ring of global sections is `k(X)`. -/
theorem isFractionRing_app_fromSpecStalk_genericPoint {X : Scheme.{u}} [IsIntegral X]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    letI := ((X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
    IsFractionRing Γ(X, U) Γ(Spec X.functionField, X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U) := by
  set f := X.fromSpecStalk (genericPoint X)
  let := (f.app U).hom.toAlgebra
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  let ι := (Scheme.ΓSpecIso X.functionField).inv ≫
    (Spec X.functionField).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op
  have := isIso_presheaf_map_fromSpecStalk_preimage_le_top hη
  have hι : Function.Bijective ι.hom := ConcreteCategory.bijective_of_isIso _
  have key : f.app U = X.germToFunctionField U ≫ ι := Scheme.fromSpecStalk_app hη
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsLocalization.isLocalization_of_algEquiv _ <|
    AlgEquiv.ofBijective ⟨ι.hom, fun a ↦ (ConcreteCategory.congr_hom key a).symm⟩ hι

open CategoryTheory in
/-- Let `L` be a field extension of the function field `k(X)` of an integral scheme `X`. Over a
nonempty open `U` of `X`, the sections of `Spec L` over the preimage of `U` along
`Spec L ⟶ Spec k(X) ⟶ X` are `L`, as a `Γ(X, U)`-algebra through `k(X)`: the preimage is all of
`Spec L`, whose ring of global sections is `L`. -/
noncomputable def algEquivAppPreimageSpecExtension {X : Scheme.{u}} [IsIntegral X] (L : Type u)
    [Field L] [Algebra X.functionField L] {U : X.Opens} [Nonempty U] [Algebra Γ(X, U) L]
    [IsScalarTower Γ(X, U) X.functionField L] :
    letI := ((Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
    L ≃ₐ[Γ(X, U)] Γ(Spec (.of L), (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U) :=
  letI f := Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
    X.fromSpecStalk (genericPoint X)
  letI := (f.app U).hom.toAlgebra
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  -- The preimage of `U` is all of `Spec L`, so restriction from `⊤` is an isomorphism.
  have htop : f ⁻¹ᵁ U = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.fromSpecStalk_preimage_eq_top hη,
      Scheme.Hom.preimage_top]
  have : IsIso ((Spec (.of L)).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op) := by
    rw [show homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤) = eqToHom htop from Subsingleton.elim _ _,
      eqToHom_op, eqToHom_map]
    infer_instance
  let ι := (Scheme.ΓSpecIso (.of L)).inv ≫
    (Spec (.of L)).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op
  have key : f.app U =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) ≫ ι := by
    have hnat : (Scheme.ΓSpecIso X.functionField).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))).app ⊤ =
          CommRingCat.ofHom (algebraMap X.functionField L) ≫ (Scheme.ΓSpecIso (.of L)).inv :=
      (Scheme.ΓSpecIso_inv_naturality _).symm
    rw [Scheme.Hom.comp_app, Scheme.fromSpecStalk_app hη, Category.assoc, Category.assoc,
      Scheme.Hom.naturality, reassoc_of% hnat]
    -- The two restriction maps are along the same inclusion of opens of `Spec L`.
    rfl
  .ofBijective ⟨ι.hom, fun a ↦ by
    rw [IsScalarTower.algebraMap_apply Γ(X, U) X.functionField L, RingHom.algebraMap_toAlgebra,
      key]
    rfl⟩ (ConcreteCategory.bijective_of_isIso ι)

open CategoryTheory in
/-- The underlying ring homomorphism of `algEquivAppPreimageSpecExtension` identifies `L` with the
global sections of `Spec L` and then restricts them to the preimage of `U`. -/
theorem algEquivAppPreimageSpecExtension_toRingHom {X : Scheme.{u}} [IsIntegral X] (L : Type u)
    [Field L] [Algebra X.functionField L] {U : X.Opens} [Nonempty U] [Algebra Γ(X, U) L]
    [IsScalarTower Γ(X, U) X.functionField L] :
    letI := ((Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
    (algEquivAppPreimageSpecExtension L (U := U) : L →+* _) =
      ((Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).presheaf.map (homOfLE (le_top :
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
          X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤)).op).hom := by
  unfold algEquivAppPreimageSpecExtension
  rfl

open CategoryTheory in
/-- `algEquivAppPreimageSpecExtension` sends `a : L` to the restriction of the corresponding global
section of `Spec L` to the preimage of `U`. This is not a `simp` lemma: `simp` rewrites the
preimage `(f ≫ g) ⁻¹ᵁ U` occurring in the type of its left-hand side. -/
theorem algEquivAppPreimageSpecExtension_apply {X : Scheme.{u}} [IsIntegral X] (L : Type u)
    [Field L] [Algebra X.functionField L] {U : X.Opens} [Nonempty U] [Algebra Γ(X, U) L]
    [IsScalarTower Γ(X, U) X.functionField L] (a : L) :
    letI := ((Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
    algEquivAppPreimageSpecExtension L (U := U) a =
      (Spec (.of L)).presheaf.map (homOfLE (le_top :
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
          X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤)).op
        ((Scheme.ΓSpecIso (.of L)).inv a) :=
  RingHom.congr_fun (algEquivAppPreimageSpecExtension_toRingHom L) a

end Scheme

end AlgebraicGeometry

end TauCeti
