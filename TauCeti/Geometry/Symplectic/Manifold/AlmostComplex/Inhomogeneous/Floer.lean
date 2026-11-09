/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Inhomogeneous.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Geometry.Symplectic.JHolomorphic.Line

/-!
# The normalized finite-regularity Floer forcing term

On the standard plane the forcing term is the native antilinear projection of `dt ⊗ X`.
Its values on the two coordinate vectors are `½ J X` and `½ X`, respectively. The construction
uses the joint finite regularity of the data, including the continuous endpoint.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

/-- The standard plane structure, viewed at the specified finite or infinite regularity. -/
def planeDomainStructure (n : ℕ∞) :
    ContMDiffAlmostComplexStructure 𝓘(ℝ, ℝ × ℝ) n (ℝ × ℝ) :=
  (SmoothAlmostComplexStructure.product ℝ).toContMDiff n

@[simp]
theorem planeDomainStructure_apply (n : ℕ∞) (z v : ℝ × ℝ) :
    planeDomainStructure n z v = (-v.2, v.1) := by
  unfold planeDomainStructure
  exact ((SmoothAlmostComplexStructure.product ℝ).toContMDiff_apply n z v).trans
    (SmoothAlmostComplexStructure.product_apply z v)

namespace InhomogeneousTerm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ∞}

/-- The jointly regular ambient Hom section `dt ⊗ X`, before antilinear projection. -/
def timeHom (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X) :
    DomainDependentHomSection 𝓘(ℝ, V) V 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n :=
  DomainDependentHomSection.ofContDiff
    (fun q ↦ (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (X q))
    (contDiff_const.smulRight hX)

@[simp]
theorem timeHom_apply (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X)
    (q : (ℝ × ℝ) × V) (v : ℝ × ℝ) : timeHom X hX q v = v.2 • X q := by
  simp only [timeHom, DomainDependentHomSection.ofContDiff_apply]
  -- The native Hom section inherits the model-space scalar and evaluation operations.
  rfl

/-- The actual Floer forcing term is the canonical native section projection of `dt ⊗ X`. -/
def floer (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V
    𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n) (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X) :
    InhomogeneousTerm (planeDomainStructure n) J :=
  project (planeDomainStructure n) J (timeHom X hX)

/-- The normalized plane forcing term on every tangent vector. -/
theorem floer_apply (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V
    𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n) (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X)
    (q : (ℝ × ℝ) × V) (v : ℝ × ℝ) :
    (floer J X hX).val.tangentHom q v = (2⁻¹ : ℝ) •
      (v.2 • X q + (show V →L[ℝ] V from J.toEndomorphism q) (v.1 • X q)) := by
  have hrot : (planeDomainStructure n).horizontalEndomorphism
      (I := 𝓘(ℝ, V)) (M := V) q v = (-v.2, v.1) :=
    (DFunLike.congr_fun ((planeDomainStructure n).horizontalEndomorphism_apply
      (I := 𝓘(ℝ, V)) (M := V) q) v).trans (planeDomainStructure_apply n q.1 v)
  have htime : (timeHom X hX q)
      ((planeDomainStructure n).horizontalEndomorphism (I := 𝓘(ℝ, V)) (M := V) q v) =
        v.1 • X q :=
    (congrArg (timeHom X hX q) hrot).trans (timeHom_apply X hX q (-v.2, v.1))
  have hsum := congrArg₂
    (fun a b : V ↦ a + (show V →L[ℝ] V from J.toEndomorphism q) b)
      (timeHom_apply X hX q v) htime
  exact ((DomainDependentHomSection.tangentHom_apply
    (project (planeDomainStructure n) J (timeHom X hX)).val q v).trans
      (project_apply (planeDomainStructure n) J (timeHom X hX) q v)).trans
        (congrArg ((2⁻¹ : ℝ) • ·) hsum)

/-- The real-coordinate value is one half of the target rotation of the vector field. -/
@[simp]
theorem floer_apply_real (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V
    𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n) (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X)
    (q : (ℝ × ℝ) × V) : (floer J X hX).val.tangentHom q (1, 0) =
      (2⁻¹ : ℝ) • (show V →L[ℝ] V from J.toEndomorphism q) (X q) := by
  simpa only [zero_smul, one_smul, zero_add] using floer_apply J X hX q (1, 0)

/-- The imaginary-coordinate value is one half of the vector field. -/
@[simp]
theorem floer_apply_imag (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V
    𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n) (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X)
    (q : (ℝ × ℝ) × V) : (floer J X hX).val.tangentHom q (0, 1) = (2⁻¹ : ℝ) • X q := by
  have hzero : (show V →L[ℝ] V from J.toEndomorphism q) 0 = 0 := map_zero _
  simpa only [zero_smul, one_smul, hzero, add_zero] using floer_apply J X hX q (0, 1)

/-- Equality to the normalized forcing term is exactly the Floer equation on the actual linear
jet. In particular the factor one half is required in both coordinate values. -/
theorem complexAntilinearPart_eq_floer_iff
    (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V
      𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n)
    (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X) (q : (ℝ × ℝ) × V)
    (L : (ℝ × ℝ) →L[ℝ] V) :
    complexAntilinearPart (AlmostComplexStructure.product ℝ).toLinearMap
      (show V →L[ℝ] V from J.toEndomorphism q).toLinearMap L.toLinearMap =
        (show (ℝ × ℝ) →L[ℝ] V from (floer J X hX).val.tangentHom q).toLinearMap ↔
      L (1, 0) + (show V →L[ℝ] V from J.toEndomorphism q) (L (0, 1)) =
        (show V →L[ℝ] V from J.toEndomorphism q) (X q) := by
  let K : AlmostComplexStructure V :=
    { toLinearMap := (show V →L[ℝ] V from J.toEndomorphism q).toLinearMap
      square_neg := by ext v; exact J.apply_apply q v }
  let R := complexAntilinearPart (AlmostComplexStructure.product ℝ).toLinearMap
    K.toLinearMap L.toLinearMap
  let T : (ℝ × ℝ) →L[ℝ] V := (floer J X hX).val.tangentHom q
  -- R and T abbreviate the exact maps in the statement. K packages the same target
  -- endomorphism with its square proof; its function coercion evaluates its toLinearMap.
  -- There is no rewrite rule for these local abbreviations: fold only these wrappers
  -- before applying the public projection and Floer evaluation formulas below.
  change R = T.toLinearMap ↔ L (1, 0) + K (L (0, 1)) = K (X q)
  have hR : R stdComplexLineReal = (2⁻¹ : ℝ) •
      (L (1, 0) + K (L (0, 1))) := by
    simp only [R, complexAntilinearPart_apply]
    rw [AlmostComplexStructure.product_apply_stdComplexLineReal]
    rfl
  have hfR : T stdComplexLineReal =
      (2⁻¹ : ℝ) • K (X q) := floer_apply_real J X hX q
  have hfI : T stdComplexLineImag =
      (2⁻¹ : ℝ) • X q := floer_apply_imag J X hX q
  constructor
  · intro he
    have hh := (hR.symm.trans (LinearMap.congr_fun he stdComplexLineReal)).trans hfR
    exact smul_right_injective V (by norm_num : (2⁻¹ : ℝ) ≠ 0) hh
  · intro he
    have hreal : R stdComplexLineReal = (2⁻¹ : ℝ) • K (X q) :=
      hR.trans (congrArg ((2⁻¹ : ℝ) • ·) he)
    have hi : R (AlmostComplexStructure.product ℝ stdComplexLineReal) =
        -K (R stdComplexLineReal) :=
      (complexAntilinearPart_isComplexAntilinear
        (AlmostComplexStructure.product ℝ).square_neg K.square_neg L.toLinearMap).apply
          stdComplexLineReal
    rw [AlmostComplexStructure.product_apply_stdComplexLineReal, hreal] at hi
    have himag : R stdComplexLineImag = (2⁻¹ : ℝ) • X q := by
      simpa only [map_smul, K.apply_apply, smul_neg, neg_neg] using hi
    apply LinearMap.ext
    intro z
    rw [R.apply_stdComplexLine, T.toLinearMap.apply_stdComplexLine, hreal, himag]
    simp only [ContinuousLinearMap.coe_coe, hfR, hfI]

/-- For the actual manifold derivative, read through the canonical model tangent equivalences,
the normalized antilinear equation is precisely the Floer equation in Fréchet coordinates.
For `C¹` maps these are the classical directional derivatives; the operator identity itself
also respects the native zero-derivative convention away from differentiability. -/
theorem mfderiv_eq_floer_iff
    (J : ContMDiffAlmostComplexStructureFamily 𝓘(ℝ, V) V
      𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n)
    (X : (ℝ × ℝ) × V → V) (hX : ContDiff ℝ n X) (u : (ℝ × ℝ) → V) (z : ℝ × ℝ) :
    complexAntilinearPart (AlmostComplexStructure.product ℝ).toLinearMap
      (show V →L[ℝ] V from J.toEndomorphism (z, u z)).toLinearMap
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (u z)).toContinuousLinearMap.comp
        ((mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z).comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap)).toLinearMap =
        (show (ℝ × ℝ) →L[ℝ] V from (floer J X hX).val.tangentHom (z, u z)).toLinearMap ↔
      fderiv ℝ u z (1, 0) +
          (show V →L[ℝ] V from J.toEndomorphism (z, u z)) (fderiv ℝ u z (0, 1)) =
        (show V →L[ℝ] V from J.toEndomorphism (z, u z)) (X (z, u z)) := by
  have hL : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (u z)).toContinuousLinearMap.comp
      ((mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z).comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap) =
        fderiv ℝ u z := by
    rw [mfderiv_eq_fderiv]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hL]
  exact complexAntilinearPart_eq_floer_iff J X hX (z, u z) (fderiv ℝ u z)

end InhomogeneousTerm

end TauCeti
