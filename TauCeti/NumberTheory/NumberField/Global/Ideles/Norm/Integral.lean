/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Compatibility
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology

/-!
# Integral norm-one ideles and their infinite coordinates

The ideles in a relative norm kernel that are local units at every finite place form an open
subgroup, with a continuous projection to the integral finite ideles. Over the maximal real
subfield of a CM field, each infinite coordinate of the norm kernel lies on the unit circle.
These two kinds of coordinates allow separate prescriptions of the weight and finite part of a
character on the integral subgroup.
-/

public section

open NumberField IsDedekindDomain
open IsDedekindDomain.FiniteAdeleRing (integralUnits)

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The open subgroup of the relative idele norm kernel whose finite components are units. -/
noncomputable def integralNormOne : OpenSubgroup (ideleNormMap K L).ker where
  toSubgroup := (integralUnits (𝓞 L) L).comap
    ((IdeleGroup.toFiniteIdele (𝓞 L) L).comp (ideleNormMap K L).ker.subtype)
  isOpen' := (TauCeti.isOpen_integralUnits (𝓞 L) L).preimage
    ((IdeleGroup.continuous_toFiniteIdele (𝓞 L) L).comp continuous_subtypeVal)

variable {K L}

/-- Membership requires precisely that the finite part be everywhere a local unit. -/
@[simp] theorem mem_integralNormOne_iff (u : (ideleNormMap K L).ker) :
    u ∈ integralNormOne K L ↔ IdeleGroup.toFiniteIdele (𝓞 L) L u.val ∈ integralUnits (𝓞 L) L :=
  (Iff.rfl)

/-- The finite part of an integral norm-one idele, as an integral finite idele. -/
noncomputable def integralNormOneToFinite : integralNormOne K L →ₜ* integralUnits (𝓞 L) L where
  toMonoidHom := ((IdeleGroup.toFiniteIdele (𝓞 L) L).comp
    ((ideleNormMap K L).ker.subtype.comp (integralNormOne K L).toSubgroup.subtype)).codRestrict _
      fun u ↦ (mem_integralNormOne_iff (u : (ideleNormMap K L).ker)).mp u.property
  continuous_toFun := ((IdeleGroup.continuous_toFiniteIdele (𝓞 L) L).comp
    (continuous_subtypeVal.comp continuous_subtypeVal)).subtype_mk _

/-- The finite projection is the ordinary idele projection on underlying elements. -/
theorem coe_integralNormOneToFinite (u : integralNormOne K L) :
    (integralNormOneToFinite u : _) = IdeleGroup.toFiniteIdele (𝓞 L) L u.val.val := (rfl)

end TauCeti.GlobalNumberFields

namespace NumberField.InfinitePlace

open TauCeti.GlobalNumberFields

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

/-- At an infinite place of a CM field a norm-one idele has complex absolute value one. -/
theorem norm_ideleInfiniteCoord_eq_one (w : InfinitePlace L)
    (u : (ideleNormMap (maximalRealSubfield L) L).ker) :
    ‖(w.ideleInfiniteCoord u.val : w.Completion)‖ = 1 := by
  let v := IsCMField.equivInfinitePlace L w
  have hw : w.LiesOver v := InfinitePlace.liesOver_iff_comap_eq.mpr
    (IsCMField.equivInfinitePlace_apply L w).symm
  have hnorm := completionNormalizedAbsValue_ideleInfiniteCoord_ideleNormMap v u.val
  have hu : ideleNormMap (maximalRealSubfield L) L u.val = 1 :=
    MonoidHom.mem_ker.mp u.property
  rw [hu, map_one, Units.val_one, map_one, finprod_eq_single _ ⟨w, hw⟩] at hnorm
  · rw [completionNormalizedAbsValue_of_isComplex w (IsTotallyComplex.isComplex w)] at hnorm
    nlinarith [norm_nonneg (w.ideleInfiniteCoord u.val : w.Completion)]
  · intro w' hne
    exfalso
    apply hne
    apply Subtype.ext
    exact (IsCMField.equivInfinitePlace L).injective
      ((IsCMField.equivInfinitePlace_apply L w'.val).trans (LiesOver.comap_eq w'.val v))

/-- The infinite coordinate, embedded into the circle using the chosen embedding of its place. -/
noncomputable def normOneInfiniteCoord (w : InfinitePlace L) :
    (ideleNormMap (maximalRealSubfield L) L).ker →ₜ* Circle where
  toFun u := ⟨Completion.extensionEmbedding w (w.ideleInfiniteCoord u.val),
    mem_sphere_zero_iff_norm.mpr <| by
      rw [(Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
      exact w.norm_ideleInfiniteCoord_eq_one u⟩
  map_one' := Subtype.ext (by
    simp only [OneMemClass.coe_one, map_one, Units.val_one, Circle.coe_one])
  map_mul' u v := Subtype.ext (by
    simp only [MulMemClass.coe_mul, map_mul, Units.val_mul]
    rfl)
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [coe_ideleInfiniteCoord]
    exact (Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp
        (Units.continuous_val.comp continuous_subtypeVal)))

/-- The circle coordinate is the embedded completion coordinate. -/
theorem coe_normOneInfiniteCoord (w : InfinitePlace L)
    (u : (ideleNormMap (maximalRealSubfield L) L).ker) :
    (w.normOneInfiniteCoord u : ℂ) =
      Completion.extensionEmbedding w (w.ideleInfiniteCoord u.val) := (rfl)

end NumberField.InfinitePlace
