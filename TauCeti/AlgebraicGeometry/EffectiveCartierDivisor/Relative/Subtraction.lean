/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
public import TauCeti.AlgebraicGeometry.IdealSheaf.Flat
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Monoid

/-!
# Residual relative effective Cartier divisors

A relative effective Cartier divisor contained in another can be subtracted over any base.
The residual divisor is cut out by the colon ideal, is flat over the base, and commutes with
arbitrary base change. These properties supply residual families in fixed-degree divisor
functors. The flatness criterion applies more generally to a locally principal denominator
and flat closed subschemes cut out by `D` and `D ⊔ E`.

## References

The local flatness argument adapts `TauCeti.isRelativeEffectiveCartier_mul` in
`TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Sum`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}} {D E : X.IdealSheafData} {f : X ⟶ S}

/-- Subtracting a flat locally principal divisor from a containing relative effective Cartier
divisor gives a relative effective Cartier divisor. -/
theorem IsRelativeEffectiveCartier.colon (hD : D.IsRelativeEffectiveCartier f)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a})
    [Flat (E.subschemeι ≫ f)] (hle : D ≤ E) :
    (D.colon E).IsRelativeEffectiveCartier f := by
  have := hD.flat
  have hflatE : Flat (E.subschemeι ≫ f) := inferInstance
  have : Flat ((D ⊔ E).subschemeι ≫ f) := by
    rwa [sup_eq_right.mpr hle]
  exact (isRelativeEffectiveCartier_iff _ _).mpr
    ⟨hD.isEffectiveCartier.colon hE hle, D.flat_colon_subschemeι_comp E f hE⟩

/-- Residual divisors commute with every cartesian base change, without flatness of the
base-change morphism. -/
theorem IsRelativeEffectiveCartier.comap_colon_of_isPullback
    (hE : E.IsRelativeEffectiveCartier f) (hle : D ≤ E) {T X' : Scheme.{u}}
    {g : T ⟶ S} {p : X' ⟶ X} {f' : X' ⟶ T} (H : IsPullback p f' f g) :
    (D.colon E).comap p = (D.comap p).colon (E.comap p) :=
  D.comap_colon E hE.isEffectiveCartier.locallyPrincipal hle p
    (hE.comap_of_isPullback H).isEffectiveCartier

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Subtract a contained relative effective Cartier divisor over an arbitrary base. -/
noncomputable def relativeEffectiveCartierResidual {T : (Over S)ᵒᵖ}
    (D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) (hle : D.val ≤ E.val) :
    (relativeEffectiveCartierSubfunctor f).toFunctor.obj T := by
  have hD := (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp D.property
  have hE := (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp E.property
  have := hE.flat
  exact ⟨D.val.colon E.val, (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mpr
    (hD.colon hE.isEffectiveCartier.locallyPrincipal hle)⟩

/-- The residual divisor is cut out by the colon ideal. -/
@[simp]
theorem relativeEffectiveCartierResidual_val {T : (Over S)ᵒᵖ}
    (D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) (hle : D.val ≤ E.val) :
    (relativeEffectiveCartierResidual f D E hle).val = D.val.colon E.val := (rfl)

/-- Adding the subtracted divisor to its residual recovers the original divisor. -/
@[simp]
theorem relativeEffectiveCartierResidual_mul {T : (Over S)ᵒᵖ}
    (D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) (hle : D.val ≤ E.val) :
    relativeEffectiveCartierResidual f D E hle * E = D := by
  apply Subtype.ext
  rw [relativeEffectiveCartier_val_mul, relativeEffectiveCartierResidual_val]
  exact (D.val.eq_colon_mul E.val
    ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp
      E.property).isEffectiveCartier.locallyPrincipal hle).symm

/-- A relative divisor is the residual precisely when adding the denominator recovers `D`. -/
theorem relativeEffectiveCartierResidual_eq_iff {T : (Over S)ᵒᵖ}
    (D E C : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) (hle : D.val ≤ E.val) :
    relativeEffectiveCartierResidual f D E hle = C ↔ C * E = D := by
  constructor
  · rintro rfl
    exact relativeEffectiveCartierResidual_mul f D E hle
  · intro hC
    apply Subtype.ext
    have hE := ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp E.property).isEffectiveCartier
    apply hE.mul_left_cancel
    simpa only [relativeEffectiveCartier_val_mul, mul_comm] using
      congrArg Subtype.val ((relativeEffectiveCartierResidual_mul f D E hle).trans hC.symm)

/-- Subtraction is a left inverse to addition of a fixed relative divisor. -/
@[simp]
theorem relativeEffectiveCartierResidual_mul_right {T : (Over S)ᵒᵖ}
    (C E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
    relativeEffectiveCartierResidual f (C * E) E
      (by rw [relativeEffectiveCartier_val_mul]; exact fun _ ↦ Ideal.mul_le_right) = C :=
  (relativeEffectiveCartierResidual_eq_iff f (C * E) E C _).mpr rfl

/-- A contained relative divisor has a unique residual, without properness or degree conditions. -/
theorem existsUnique_relativeEffectiveCartierResidual {T : (Over S)ᵒᵖ}
    (D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) (hle : D.val ≤ E.val) :
    ∃! C : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T, C * E = D := by
  refine ⟨relativeEffectiveCartierResidual f D E hle,
    relativeEffectiveCartierResidual_mul f D E hle, ?_⟩
  intro C hC
  exact ((relativeEffectiveCartierResidual_eq_iff f D E C hle).mpr hC).symm

/-- Residual relative divisors commute with arbitrary base change of the test scheme. -/
theorem relativeEffectiveCartierResidual_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) (hle : D.val ≤ E.val) :
    (relativeEffectiveCartierSubfunctor f).toFunctor.map φ
        (relativeEffectiveCartierResidual f D E hle) =
      relativeEffectiveCartierResidual f
        ((relativeEffectiveCartierSubfunctor f).toFunctor.map φ D)
        ((relativeEffectiveCartierSubfunctor f).toFunctor.map φ E)
        (Scheme.IdealSheafData.comap_mono _ hle) := by
  apply Subtype.ext
  simp only [Subfunctor.toFunctor_map, baseChangeIdealSheafFunctor_map_apply,
    relativeEffectiveCartierResidual_val]
  exact ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp E.property).comap_colon_of_isPullback
    hle (Over.isPullback_pullback_map_left f φ.unop)

end TauCeti.AlgebraicGeometry
