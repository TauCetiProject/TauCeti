/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Subtraction

/-!
# Residual divisors of fixed degree

If a relative effective Cartier divisor of degree `e` is contained in one of degree `d + e`,
its residual divisor has degree `d`. The residual is the unique divisor whose sum with the
contained divisor is the original divisor. Its ideal is the colon ideal, and the construction
commutes with arbitrary base change.

This describes the incidence fibres of addition on the fixed-degree divisor functors of a
proper relative curve. Representability and the finite degree of addition are separate results.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}} {D E : X.IdealSheafData} {f : X ⟶ S}

/-- For a finite flat closed subscheme `D` and a contained relative effective Cartier divisor
`E`, the ranks of the residual and of `E` add to the rank of `D`. The ideal `D` may be arbitrary. -/
theorem IsRelativeEffectiveCartier.finrank_colon_add_finrank
    (hE : E.IsRelativeEffectiveCartier f) (hle : D ≤ E)
    [Flat (D.subschemeι ≫ f)] [IsFinite (D.subschemeι ≫ f)] :
    ((D.colon E).subschemeι ≫ f).finrank + (E.subschemeι ≫ f).finrank =
      (D.subschemeι ≫ f).finrank := by
  have := hE.flat
  have : Flat ((D ⊔ E).subschemeι ≫ f) := by
    rw [sup_eq_right.mpr hle]
    infer_instance
  have := D.flat_colon_subschemeι_comp E f hE.isEffectiveCartier.locallyPrincipal
  have hfactor : E * D.colon E = D :=
    (mul_comm _ _).trans (D.eq_colon_mul E hE.isEffectiveCartier.locallyPrincipal hle).symm
  have : IsFinite ((E * D.colon E).subschemeι ≫ f) := by
    rw [hfactor]
    infer_instance
  rw [add_comm, ← hE.finrank_mul_subschemeι_comp_of_flat (D.colon E), hfactor]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [RelativeDimensionLE 1 f]

/-- On a proper relative curve, subtracting degrees `d + e` and `e` gives degree `d`. -/
theorem residual_mem_relativeEffectiveCartierDegreeSubfunctor_obj {d e : ℕ}
    {T : (Over S)ᵒᵖ} {D E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T}
    (hD : D ∈ (relativeEffectiveCartierDegreeSubfunctor f (d + e)).obj T)
    (hE : E ∈ (relativeEffectiveCartierDegreeSubfunctor f e).obj T) (hle : D.val ≤ E.val) :
    relativeEffectiveCartierResidual f D E hle ∈
      (relativeEffectiveCartierDegreeSubfunctor f d).obj T := by
  have hrelD := (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp D.property
  have hrelE := (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp E.property
  have := hrelD.flat
  have := hrelD.isFinite
  rw [mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff] at hD hE ⊢
  rw [relativeEffectiveCartierResidual_val]
  ext t
  have hr := congrFun (hrelE.finrank_colon_add_finrank hle) t
  rw [Pi.add_apply, congrFun hD t, congrFun hE t] at hr
  exact Nat.add_right_cancel hr

/-- Subtract a contained divisor of degree `e` from one of degree `d + e` on a test scheme. -/
noncomputable def relativeEffectiveCartierDegreeResidual {d e : ℕ} {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f (d + e)).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T)
    (hle : D.val.val ≤ E.val.val) :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T :=
  ⟨relativeEffectiveCartierResidual f D.val E.val hle,
    residual_mem_relativeEffectiveCartierDegreeSubfunctor_obj f D.property E.property hle⟩

/-- The underlying ideal of the residual divisor is the colon ideal. -/
@[simp]
theorem relativeEffectiveCartierDegreeResidual_val {d e : ℕ} {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f (d + e)).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T)
    (hle : D.val.val ≤ E.val.val) :
    (relativeEffectiveCartierDegreeResidual f D E hle).val.val = D.val.val.colon E.val.val :=
  relativeEffectiveCartierResidual_val f D.val E.val hle

/-- Adding the contained divisor to the residual recovers the original divisor. -/
@[simp]
theorem relativeEffectiveCartierDegreeResidual_mul {d e : ℕ} {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f (d + e)).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T)
    (hle : D.val.val ≤ E.val.val) :
    (relativeEffectiveCartierDegreeResidual f D E hle).val * E.val = D.val :=
  relativeEffectiveCartierResidual_mul f D.val E.val hle

/-- A degree-`d` divisor is the residual precisely when its sum with `E` is `D`. -/
theorem relativeEffectiveCartierDegreeResidual_eq_iff {d e : ℕ} {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f (d + e)).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T)
    (C : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T)
    (hle : D.val.val ≤ E.val.val) :
    relativeEffectiveCartierDegreeResidual f D E hle = C ↔ C.val * E.val = D.val := by
  constructor
  · rintro rfl
    exact relativeEffectiveCartierDegreeResidual_mul f D E hle
  · intro hC
    apply Subtype.ext
    exact (relativeEffectiveCartierResidual_eq_iff f D.val E.val C.val hle).mpr hC

/-- Fixed-degree subtraction is a left inverse to addition of the denominator. -/
@[simp]
theorem relativeEffectiveCartierDegreeResidual_mul_right {d e : ℕ} {T : (Over S)ᵒᵖ}
    (C : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T) :
    relativeEffectiveCartierDegreeResidual f
        ⟨C.val * E.val,
          mul_mem_relativeEffectiveCartierDegreeSubfunctor_obj f C.property E.property⟩ E
        (by rw [relativeEffectiveCartier_val_mul]; exact fun _ ↦ Ideal.mul_le_right) = C :=
  (relativeEffectiveCartierDegreeResidual_eq_iff f _ E C _).mpr rfl

/-- An incidence pair of degrees `d + e` and `e` has a unique residual divisor of degree `d`. -/
theorem existsUnique_relativeEffectiveCartierDegreeResidual {d e : ℕ} {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f (d + e)).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T)
    (hle : D.val.val ≤ E.val.val) :
    ∃! C : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T,
      C.val * E.val = D.val := by
  refine ⟨relativeEffectiveCartierDegreeResidual f D E hle,
    relativeEffectiveCartierDegreeResidual_mul f D E hle, ?_⟩
  intro C hC
  exact ((relativeEffectiveCartierDegreeResidual_eq_iff f D E C hle).mpr hC).symm

/-- Residual divisors are natural in the test scheme for arbitrary base change. -/
theorem relativeEffectiveCartierDegreeResidual_map {d e : ℕ} {T T' : (Over S)ᵒᵖ}
    (φ : T ⟶ T')
    (D : (relativeEffectiveCartierDegreeSubfunctor f (d + e)).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T)
    (hle : D.val.val ≤ E.val.val) :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.map φ
        (relativeEffectiveCartierDegreeResidual f D E hle) =
      relativeEffectiveCartierDegreeResidual f
        ((relativeEffectiveCartierDegreeSubfunctor f (d + e)).toFunctor.map φ D)
        ((relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.map φ E)
        (Scheme.IdealSheafData.comap_mono _ hle) := by
  apply Subtype.ext
  exact relativeEffectiveCartierResidual_map f φ D.val E.val hle

end TauCeti.AlgebraicGeometry
