/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Complexification
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The continuous dual of a complexification

The complex continuous dual of the Taylor-norm complexification of a real seminormed
space is complex-linearly equivalent to the complexification of its real continuous
dual. The inverse reads the real and imaginary parts of the functional on real
vectors. The forward map sends `g + i h` to the functional
`x + i y ↦ g x - h y + i (h x + g y)`.

`TauCeti.Complexification.strongDualEquiv` gives this comparison with forward norm at
most two and inverse norm at most one. These are bounds, not an isometry assertion:
the Taylor norm on the complexified dual need not equal the dual Taylor norm.
No completeness assumption is needed. `strongBidualEquiv` intertwines the canonical
bidual embeddings. Consequently a real seminormed space is reflexive if and only if
its complexification is reflexive, where reflexivity means surjectivity of the
canonical continuous bidual embedding.

The construction reuses Mathlib's norm-preserving `StrongDual.extendRCLike`.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33.
-/

public section

noncomputable section

namespace TauCeti.Complexification

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

private def dualExtension (z : Complexification (StrongDual ℝ X)) :
    StrongDual ℂ (Complexification X) :=
  StrongDual.extendRCLike (z.re.comp (reCLM X) - z.im.comp (imCLM X))

private theorem dualExtension_apply (z : Complexification (StrongDual ℝ X))
    (w : Complexification X) :
    dualExtension z w = (z.re w.re - z.im w.im : ℂ) +
      Complex.I * (z.im w.re + z.re w.im) := by
  apply Complex.ext <;>
    simp [dualExtension, StrongDual.extendRCLike_apply]

private def dualRestriction (f : StrongDual ℂ (Complexification X)) :
    Complexification (StrongDual ℝ X) :=
  ⟨Complex.reCLM.comp ((f.restrictScalars ℝ).comp (ofRealLI X).toContinuousLinearMap),
   Complex.imCLM.comp ((f.restrictScalars ℝ).comp (ofRealLI X).toContinuousLinearMap)⟩

private theorem dualExtension_norm_le (z : Complexification (StrongDual ℝ X)) :
    ‖dualExtension z‖ ≤ 2 * ‖z‖ := by
  rw [dualExtension, StrongDual.norm_extendRCLike]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  calc
    ‖(z.re.comp (reCLM X) - z.im.comp (imCLM X)) w‖
        ≤ ‖z.re w.re‖ + ‖z.im w.im‖ := by
          simpa using norm_sub_le (z.re w.re) (z.im w.im)
    _ ≤ ‖z.re‖ * ‖w.re‖ + ‖z.im‖ * ‖w.im‖ :=
      add_le_add (z.re.le_opNorm _) (z.im.le_opNorm _)
    _ ≤ ‖z‖ * ‖w‖ + ‖z‖ * ‖w‖ := by
      gcongr
      · exact norm_re_le z
      · exact norm_re_le w
      · exact norm_im_le z
      · exact norm_im_le w
    _ = 2 * ‖z‖ * ‖w‖ := by ring

private theorem dualRestriction_norm_le (f : StrongDual ℂ (Complexification X)) :
    ‖dualRestriction f‖ ≤ ‖f‖ := by
  refine norm_le_iff.2 fun u ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
  have heq : (((u : ℂ) • dualRestriction f).re) x =
      ((u : ℂ) * f (ofReal x)).re := by
    simp [dualRestriction, Complex.mul_re]
  rw [heq]
  exact (RCLike.norm_re_le_norm ((u : ℂ) * f (ofReal x))).trans
    (by simpa [norm_mul] using f.le_opNorm (ofReal x))

variable (X)

/-- The complexified real continuous dual is complex-linearly equivalent to the
complex continuous dual of the Taylor complexification. Its forward norm is at most
two and its inverse is contractive. -/
def strongDualEquiv : Complexification (StrongDual ℝ X) ≃L[ℂ]
    StrongDual ℂ (Complexification X) :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := dualExtension
      invFun := dualRestriction
      map_add' := fun z w ↦ by
        ext v
        simp [dualExtension_apply]
        ring
      map_smul' := fun c z ↦ by
        ext v
        apply Complex.ext <;>
          simp [dualExtension_apply, Complex.mul_re, Complex.mul_im] <;> ring
      left_inv := fun z ↦ by
        ext x <;> simp [dualRestriction, dualExtension_apply]
      right_inv := fun f ↦ by
        apply ContinuousLinearMap.coe_injective
        apply ext_ofReal
        intro x
        have hzero : ofReal (0 : X) = 0 := (ofRealLI_apply (0 : X)).symm.trans (map_zero _)
        simp [dualExtension_apply, dualRestriction, hzero, mul_comm Complex.I,
          Complex.re_add_im] }
    2 1 dualExtension_norm_le (fun f ↦ by simpa using dualRestriction_norm_le f)

/-- Evaluation of the dual comparison on arbitrary complexified vectors. -/
@[simp]
theorem strongDualEquiv_apply (z : Complexification (StrongDual ℝ X))
    (w : Complexification X) :
    strongDualEquiv X z w = (z.re w.re - z.im w.im : ℂ) +
      Complex.I * (z.im w.re + z.re w.im) :=
  dualExtension_apply z w

/-- The real coordinate of the inverse dual comparison is real-part restriction. -/
@[simp]
theorem strongDualEquiv_symm_apply_re (f : StrongDual ℂ (Complexification X)) (x : X) :
    ((strongDualEquiv X).symm f).re x = (f (ofReal x)).re := by
  simp [strongDualEquiv, LinearEquiv.toContinuousLinearEquivOfBounds,
    ContinuousLinearEquiv.symm, dualRestriction]

/-- The imaginary coordinate of the inverse dual comparison is imaginary-part restriction. -/
@[simp]
theorem strongDualEquiv_symm_apply_im (f : StrongDual ℂ (Complexification X)) (x : X) :
    ((strongDualEquiv X).symm f).im x = (f (ofReal x)).im := by
  simp [strongDualEquiv, LinearEquiv.toContinuousLinearEquivOfBounds,
    ContinuousLinearEquiv.symm, dualRestriction]

/-- The dual comparison increases norms by at most a factor of two. -/
theorem norm_strongDualEquiv_apply_le (z : Complexification (StrongDual ℝ X)) :
    ‖strongDualEquiv X z‖ ≤ 2 * ‖z‖ :=
  dualExtension_norm_le z

/-- The inverse dual comparison is contractive for the Taylor norm. -/
theorem norm_strongDualEquiv_symm_apply_le (f : StrongDual ℂ (Complexification X)) :
    ‖(strongDualEquiv X).symm f‖ ≤ ‖f‖ :=
  dualRestriction_norm_le f

/-- The operator norm of the dual comparison is at most two. -/
theorem norm_strongDualEquiv_le : ‖(strongDualEquiv X).toContinuousLinearMap‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (norm_strongDualEquiv_apply_le X)

/-- The inverse dual comparison has operator norm at most one. -/
theorem norm_strongDualEquiv_symm_le :
    ‖(strongDualEquiv X).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa using norm_strongDualEquiv_symm_apply_le X

/-- The complexification of the real bidual is equivalent to the complex bidual
of the complexification, through the two dual comparisons. -/
def strongBidualEquiv : Complexification (StrongDual ℝ (StrongDual ℝ X)) ≃L[ℂ]
    StrongDual ℂ (StrongDual ℂ (Complexification X)) :=
  (strongDualEquiv (StrongDual ℝ X)).trans
    ((strongDualEquiv X).arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ))

/-- Evaluation of the bidual comparison uses the inverse dual comparison on its test. -/
@[simp]
theorem strongBidualEquiv_apply (z : Complexification (StrongDual ℝ (StrongDual ℝ X)))
    (f : StrongDual ℂ (Complexification X)) :
    strongBidualEquiv X z f = strongDualEquiv (StrongDual ℝ X) z
      ((strongDualEquiv X).symm f) := by
  simp [strongBidualEquiv]

/-- The bidual comparison intertwines the real and complex canonical embeddings. -/
@[simp]
theorem strongBidualEquiv_complexify_inclusionInDoubleDual (z : Complexification X) :
    strongBidualEquiv X ((NormedSpace.inclusionInDoubleDual ℝ X).complexify z) =
      NormedSpace.inclusionInDoubleDual ℂ (Complexification X) z := by
  ext f
  obtain ⟨g, rfl⟩ := (strongDualEquiv X).surjective f
  simp [strongBidualEquiv_apply, strongDualEquiv_apply, NormedSpace.dual_def, add_comm]

/-- A real seminormed space is reflexive exactly when its Taylor complexification
is reflexive. Completeness is not required as an additional hypothesis. -/
@[simp]
theorem surjective_inclusionInDoubleDual_iff :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (Complexification X)) ↔
      Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X) := by
  constructor
  · intro h φ
    obtain ⟨z, hz⟩ := h (strongBidualEquiv X (ofReal φ))
    have heq : (NormedSpace.inclusionInDoubleDual ℝ X).complexify z = ofReal φ :=
      (strongBidualEquiv X).injective
        ((strongBidualEquiv_complexify_inclusionInDoubleDual X z).trans hz)
    exact ⟨z.re, by simpa using congrArg Complexification.re heq⟩
  · intro h Φ
    let q := (strongBidualEquiv X).symm Φ
    obtain ⟨x, hx⟩ := h q.re
    obtain ⟨y, hy⟩ := h q.im
    have heq : (NormedSpace.inclusionInDoubleDual ℝ X).complexify
        (⟨x, y⟩ : Complexification X) = q := by
      ext <;> simp [hx, hy]
    refine ⟨⟨x, y⟩, ?_⟩
    rw [← strongBidualEquiv_complexify_inclusionInDoubleDual, heq]
    exact (strongBidualEquiv X).apply_symm_apply Φ

end TauCeti.Complexification
