/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Frame
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
public import TauCeti.Analysis.CStarAlgebra.Module.Matrix
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Finite Parseval frames and polar decomposition on Hilbert C⋆-modules

For a right Hilbert `A`-module `E` (`CStarModule Aᵐᵒᵖ E`, with right action `x a = op a • x` and
`⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`), a finite family `x : ι → E` is a *Parseval frame*
(`CStarModule.IsParsevalFrame Aᵐᵒᵖ x`) if `z = ∑ i, x i ⟨x i, z⟩_A` for every `z : E`.

Over any (possibly non-unital) C⋆-algebra `A`, every finite family `x : ι → E` defines an adjoint
pair of bounded complex-linear maps between `E` and `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`: the *analysis map*
`TauCeti.CStarModule.frameAnalysisCLM A x` (`z ↦ (i ↦ ⟨x i, z⟩_A)`) and the *synthesis map*
`TauCeti.CStarModule.frameSynthesisCLM A x` (`v ↦ ∑ i, x i (v i)`). Their composition on
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` is `TauCeti.CStarMatrix.mulVecCLM (CStarMatrix.gram A x)`, so `x` is a
Parseval frame iff Parseval's identity holds, iff `CStarMatrix.gram A x` is a star projection and
synthesis is surjective. Every right Hilbert `A`-module admitting a finite Parseval frame is
complete (`CStarModule.IsParsevalFrame.completeSpace`).

Over a unital C⋆-algebra `A`, Parseval frames correspond unitarily to projection-cutdown modules
`LinearMap.range (TauCeti.CStarMatrix.mulVecLinearMap p)`
(`CStarModule.IsParsevalFrame.equivRangeGram`,
`IsStarProjection.exists_isParsevalFrame_and_gram_eq`), for finite `ι` every complete right
`A`-linear retract of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` admits an `ι`-indexed Parseval frame
(`LinearMap.exists_isParsevalFrame_of_comp_eq_id`, applied downstream in
`TauCeti.Analysis.CStarAlgebra.Module.Projective` to finitely generated projective modules), a
Parseval frame gives an explicit adjoint (`TauCeti.CStarModule.frameAdjoint`) for any `A`-linear
(in particular, right `A`-linear) map out of the module
(`CStarModule.IsParsevalFrame.isAdjointPair_frameAdjoint`), and for `T : E ≃ₗ[Aᵐᵒᵖ] F` into
a complete right Hilbert `A`-module `F` they yield polar decompositions `T = U ∘ |T|`
(`CStarModule.IsParsevalFrame.polarModulus`,
`CStarModule.IsParsevalFrame.polarUnitary`,
`CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`).

## Main declarations

* `CStarModule.IsParsevalFrame.completeSpace`
* `TauCeti.CStarModule.frameAnalysisCLM`, `TauCeti.CStarModule.frameSynthesisCLM`,
  `TauCeti.CStarModule.frameAnalysisLinearMap`, `TauCeti.CStarModule.frameSynthesisLinearMap`
* `CStarModule.IsParsevalFrame.equivRangeGram`,
  `IsStarProjection.exists_isParsevalFrame_and_gram_eq`
* `LinearMap.continuous_of_finite_pi_cstarModule`, `LinearMap.exists_isParsevalFrame_of_comp_eq_id`
* `TauCeti.CStarModule.frameAdjoint`, `TauCeti.CStarModule.polarMatrix`,
  `CStarModule.IsParsevalFrame.polarModulus`,
  `CStarModule.IsParsevalFrame.polarUnitary`,
  `CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1–4 and 6.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
* J. Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
-/

public section

open MulOpposite Matrix CStarModule
open TauCeti.CStarMatrix (mulVecCLM mulVecLinearMap)
open scoped WithCStarModule

/-! ### Finite Parseval frames: edge cases and unitary invariance -/

namespace TauCeti.CStarModule

section Defs

variable {A ι κ E : Type*} [Fintype ι] [Inner A E] [AddCommMonoid E] [SMul A E]

@[simp] theorem _root_.CStarModule.IsParsevalFrame.sum_inner_smul {x : ι → E}
    (hx : IsParsevalFrame A x) (z : E) : ∑ i, inner A (x i) z • x i = z :=
  isParsevalFrame_iff.mp hx z

/-- Every finite family in a subsingleton module is a Parseval frame. -/
theorem isParsevalFrame_of_subsingleton [Subsingleton E] (x : ι → E) : IsParsevalFrame A x :=
  isParsevalFrame_iff.mpr fun _ ↦ Subsingleton.elim _ _

/-- An empty family is a Parseval frame if and only if the module is subsingleton. -/
@[simp] theorem isParsevalFrame_empty_iff [IsEmpty ι] (x : ι → E) :
    IsParsevalFrame A x ↔ Subsingleton E :=
  ⟨fun hx ↦ ⟨fun y z ↦ by rw [← hx.sum_inner_smul y, ← hx.sum_inner_smul z]; simp⟩,
    fun _ ↦ isParsevalFrame_of_subsingleton x⟩

/-- Reindexing a Parseval frame along an equivalence of finite index types preserves the Parseval
property. -/
theorem _root_.CStarModule.IsParsevalFrame.comp_equiv [Fintype κ] {x : ι → E}
    (hx : IsParsevalFrame A x) (e : κ ≃ ι) : IsParsevalFrame A (x ∘ e) :=
  isParsevalFrame_iff.mpr fun z ↦ by
    simpa [Function.comp_apply] using
      (e.sum_comp fun i ↦ inner A (x i) z • x i).trans (hx.sum_inner_smul z)

@[simp] theorem _root_.Equiv.isParsevalFrame_comp_iff [Fintype κ] {x : ι → E} (e : κ ≃ ι) :
    IsParsevalFrame A (x ∘ e) ↔ IsParsevalFrame A x :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp_equiv e.symm, fun h ↦ h.comp_equiv e⟩

private theorem isParsevalFrame_comp_iff_of_bijective {A ι E F G : Type*} [Fintype ι]
    [Inner A E] [AddCommGroup E] [SMul A E] [Inner A F] [AddCommGroup F] [SMul A F]
    [FunLike G E F] [AddMonoidHomClass G E F] (f : G) (hf_bij : Function.Bijective f)
    (hf_smul : ∀ (a : A) (x : E), f (a • x) = a • f x)
    (hf_inner : ∀ x y : E, inner A (f x) (f y) = inner A x y) {x : ι → E} :
    IsParsevalFrame A (f ∘ x) ↔ IsParsevalFrame A x := by
  refine ⟨fun h ↦ isParsevalFrame_iff.mpr fun z ↦ hf_bij.injective ?_,
    fun h ↦ isParsevalFrame_iff.mpr fun w ↦ ?_⟩
  · simpa [Function.comp_apply, map_sum, hf_smul, hf_inner] using h.sum_inner_smul (f z)
  · obtain ⟨z, rfl⟩ := hf_bij.surjective w
    simpa [Function.comp_apply, map_sum, hf_smul, hf_inner] using
      congrArg f (h.sum_inner_smul z)

end Defs

end TauCeti.CStarModule

namespace TauCeti.CStarModuleUnitary

open TauCeti.CStarModule

variable {A ι E F : Type*} [Fintype ι] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [PartialOrder A] [Norm A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Over a (possibly non-unital) coefficient ring, a Hilbert C⋆-module unitary
`U : CStarModuleUnitary A E F` preserves Parseval frames. -/
@[simp] theorem isParsevalFrame_comp_iff (U : CStarModuleUnitary A E F) {x : ι → E} :
    IsParsevalFrame A (U ∘ x) ↔ IsParsevalFrame A x :=
  isParsevalFrame_comp_iff_of_bijective U U.bijective U.map_smul_coeff U.inner_map_map

end TauCeti.CStarModuleUnitary

namespace LinearIsometryEquiv

open TauCeti.CStarModule

variable {A ι E F : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [Module ℂ E] [Module A E] [CStarModule A E]
  [SeminormedAddCommGroup F] [Module ℂ F] [Module A F] [CStarModule A F]

/-- Over a unital C⋆-algebra, a unitary isomorphism `f : E ≃ₗᵢ[A] F` preserves Parseval frames. -/
@[simp] theorem isParsevalFrame_comp_iff (f : E ≃ₗᵢ[A] F) {x : ι → E} :
    IsParsevalFrame A (f ∘ x) ↔ IsParsevalFrame A x :=
  isParsevalFrame_comp_iff_of_bijective f f.bijective f.map_smul f.inner_map_map_cstarModule

end LinearIsometryEquiv

/-! ### Analysis and synthesis operators, Parseval's identity, and Gram projections -/

namespace TauCeti.CStarModule

/-- **Parseval's identity** (general algebraic form): `x : ι → E` is a Parseval frame iff
`∑ i, ⟪x i, z⟫_A * (⟪x i, z⟫_A)⋆ = ⟪z, z⟫_A` for all `z : E`. -/
theorem isParsevalFrame_iff_sum_inner_mul_star_inner {A ι E : Type*} [Fintype ι] [NonUnitalRing A]
    [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
    [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E] {x : ι → E} :
    IsParsevalFrame A x ↔ ∀ z : E, ∑ i, inner A (x i) z * star (inner A (x i) z) = inner A z z := by
  refine ⟨fun hx z ↦ ?_, fun h ↦ isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  · conv_rhs => arg 3; rw [← hx.sum_inner_smul z]
    rw [inner_sum_right']; simp
  · let Q : E → E := fun w ↦ (∑ i, inner A (x i) w • x i) - w
    have hQ_add (u v : E) : Q (u + v) = Q u + Q v := by
      simp only [Q, CStarModule.inner_add_right, CStarModule.add_smul, Finset.sum_add_distrib]
      abel
    have hQ_sa (u v : E) : inner A u (Q v) = inner A (Q u) v := by
      have h_l : inner A (∑ i, inner A (x i) u • x i) v =
          ∑ i, inner A (x i) v * inner A u (x i) := star_injective <| by
        simp [inner_sum_right', CStarModule.inner_op_smul_right, star_sum]
      simp [Q, sub_eq_add_neg, CStarModule.inner_neg_right', CStarModule.inner_neg_left',
        inner_sum_right', h_l]
    have hQ_diag (w : E) : inner A w (Q w) = 0 := by
      have hw := h w; simp only [star_inner] at hw
      simp [Q, sub_eq_add_neg, CStarModule.inner_neg_right', inner_sum_right', hw]
    have h2 : (2 : ℂ) • inner A (Q z) (Q z) = 0 := by
      simpa [hQ_add, hQ_diag z, hQ_diag (Q z), hQ_sa z (Q z), ← two_smul ℂ] using hQ_diag (z + Q z)
    exact sub_eq_zero.mp <| (CStarModule.inner_self (A := A)).mp <| by
      simpa using congrArg ((2 : ℂ)⁻¹ • ·) h2

/-- **Parseval's identity** (right-module algebraic form): `x : ι → E` is a Parseval frame iff
`∑ i, ⟨x i, z⟩_A⋆ ⟨x i, z⟩_A = ⟨z, z⟩_A` for all `z : E`. -/
theorem isParsevalFrame_iff_sum_star_unop_inner_mul_unop_inner {A ι E : Type*} [Fintype ι]
    [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ]
    [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E]
    [CStarModule Aᵐᵒᵖ E] {x : ι → E} : IsParsevalFrame Aᵐᵒᵖ x ↔ ∀ z : E, ∑ i,
      star (unop (inner Aᵐᵒᵖ (x i) z)) * unop (inner Aᵐᵒᵖ (x i) z) = unop (inner Aᵐᵒᵖ z z) := by
  rw [isParsevalFrame_iff_sum_inner_mul_star_inner]
  exact ⟨fun h z ↦ by simpa only [Finset.unop_sum, unop_mul, unop_star] using congrArg unop (h z),
    fun h z ↦ unop_injective (by simpa only [Finset.unop_sum, unop_mul, unop_star] using h z)⟩

section NonUnital

section SynthesisCLM

variable {A ι E : Type*} [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- The *synthesis operator* of a finite family `x : ι → E` in a right Hilbert `A`-module, sending
`v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` to `∑ i, x i (v i)`. -/
noncomputable def frameSynthesisCLM (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →L[ℂ] E :=
  ∑ i : ι, ((opSMulCLM A (x i)).comp <|
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ A) i).comp
      (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := ι → A)).toContinuousLinearMap)

@[simp] theorem frameSynthesisCLM_apply (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameSynthesisCLM A x v = ∑ i, op (v i) • x i := by simp [frameSynthesisCLM]

theorem frameSynthesisCLM_op_smul (x : ι → E) (a : A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameSynthesisCLM A x (op a • v) = op a • frameSynthesisCLM A x v := by
  let _ := CStarModule.distribSMul Aᵐᵒᵖ E
  rw [frameSynthesisCLM_apply, frameSynthesisCLM_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp [MulOpposite.smul_eq_mul_unop, op_mul, (CStarModule.semigroupAction Aᵐᵒᵖ E).mul_smul]

end SynthesisCLM

variable {A ι E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- The *analysis operator* of a family `x : ι → E` in a right Hilbert `A`-module, sending `z : E`
to `i ↦ ⟨x i, z⟩_A` in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`. -/
noncomputable def frameAnalysisCLM (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    E →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := ι → A)).symm.toContinuousLinearMap.comp <|
    ContinuousLinearMap.pi fun i ↦ LinearMap.mkContinuous
      { toFun := fun z ↦ unop (inner Aᵐᵒᵖ (x i) z)
        map_add' := fun _ _ ↦ by simp [CStarModule.inner_add_right]
        map_smul' := fun _ _ ↦ by simp }
      ‖x i‖ fun z ↦ by simpa using norm_unop_inner_le (x i) z

@[simp] theorem frameAnalysisCLM_apply_apply (x : ι → E) (z : E) (i : ι) :
    frameAnalysisCLM A x z i = unop (inner Aᵐᵒᵖ (x i) z) := by simp [frameAnalysisCLM]

theorem frameAnalysisCLM_op_smul (x : ι → E) (a : A) (z : E) :
    frameAnalysisCLM A x (op a • z) = op a • frameAnalysisCLM A x z := by
  ext i; simp [MulOpposite.smul_eq_mul_unop]

variable [Fintype ι]

/-- The synthesis and analysis operators of any finite family form a module adjoint pair. -/
theorem isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (x : ι → E) : LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))).flip (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (frameSynthesisCLM A x) (frameAnalysisCLM A x) := by
  rw [isAdjointPair_inner_iff]; intro v z; apply unop_injective
  simp [WithCStarModule.pi_inner, inner_sum_left, Finset.unop_sum]

theorem frameSynthesisCLM_frameAnalysisCLM_apply (x : ι → E) (z : E) :
    frameSynthesisCLM A x (frameAnalysisCLM A x z) = ∑ i, inner Aᵐᵒᵖ (x i) z • x i := by simp

theorem frameAnalysisCLM_frameSynthesisCLM_apply (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameAnalysisCLM A x (frameSynthesisCLM A x v) = mulVecCLM (CStarMatrix.gram A x) v := by
  ext i; simp [inner_sum_right, Finset.unop_sum]

/-- For any finite family `x : ι → E`, composing analysis after synthesis on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`
yields left multiplication by the Gram matrix `CStarMatrix.gram A x` (contrast
`isParsevalFrame_iff_frameSynthesisCLM_comp_frameAnalysisCLM_eq_id` for the reverse order, which
equals the identity iff `x` is a Parseval frame). -/
@[simp] theorem frameAnalysisCLM_comp_frameSynthesisCLM (x : ι → E) :
    (frameAnalysisCLM A x).comp (frameSynthesisCLM A x) = mulVecCLM (CStarMatrix.gram A x) :=
  ContinuousLinearMap.ext fun v ↦ frameAnalysisCLM_frameSynthesisCLM_apply x v

/-- A finite family `x` is a Parseval frame iff synthesis after analysis is the identity. -/
theorem isParsevalFrame_iff_frameSynthesisCLM_comp_frameAnalysisCLM_eq_id {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔ (frameSynthesisCLM A x).comp (frameAnalysisCLM A x) = .id ℂ E := by
  simp [isParsevalFrame_iff, ContinuousLinearMap.ext_iff]

/-- A finite family `x` is a Parseval frame iff its analysis operator preserves `⟪·, ·⟫_{Aᵐᵒᵖ}`. -/
theorem isParsevalFrame_iff_inner_frameAnalysisCLM_frameAnalysisCLM {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      ∀ y z : E, inner Aᵐᵒᵖ (frameAnalysisCLM A x y) (frameAnalysisCLM A x z) = inner Aᵐᵒᵖ y z := by
  have hadj := (isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x).symm_cstarModule
  refine ⟨fun hx y z ↦ ?_, fun h ↦ isParsevalFrame_iff.mpr fun z ↦ ext_inner_left (A := Aᵐᵒᵖ)
    fun y ↦ ?_⟩
  · rw [hadj.inner_eq_cstarModule, frameSynthesisCLM_frameAnalysisCLM_apply, hx.sum_inner_smul z]
  · rw [← frameSynthesisCLM_frameAnalysisCLM_apply, ← hadj.inner_eq_cstarModule, h y z]

/-- Over any C⋆-algebra (possibly non-unital), a finite family `x` is a Parseval frame iff its Gram
matrix is a star projection and its synthesis operator is surjective. -/
theorem isParsevalFrame_iff_isStarProjection_gram_and_frameSynthesisCLM_surjective {x : ι → E} :
    IsParsevalFrame Aᵐᵒᵖ x ↔
      IsStarProjection (CStarMatrix.gram A x) ∧ Function.Surjective (frameSynthesisCLM A x) := by
  refine ⟨fun hx ↦ ⟨CStarMatrix.isStarProjection_gram hx, fun z ↦ ⟨frameAnalysisCLM A x z,
    by simpa using hx.sum_inner_smul z⟩⟩, fun ⟨hp, hsurj⟩ ↦ isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  obtain ⟨v, rfl⟩ := hsurj z; set w := mulVecCLM (CStarMatrix.gram A x) v - v
  have hΦw : frameSynthesisCLM A x w = 0 := (inner_self (A := Aᵐᵒᵖ)).mp <| by
    rw [(isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x).inner_eq_cstarModule,
      frameAnalysisCLM_frameSynthesisCLM_apply, map_sub, CStarMatrix.mulVecCLM_mulVecCLM,
      hp.isIdempotentElem.eq, sub_self, CStarModule.inner_zero_right']
  rw [map_sub, sub_eq_zero, ← frameAnalysisCLM_frameSynthesisCLM_apply] at hΦw
  simpa only [frameSynthesisCLM_apply, frameAnalysisCLM_apply_apply, op_unop] using hΦw

/-- Over any (possibly non-unital) C⋆-algebra `A`, every right Hilbert `A`-module admitting a
finite Parseval frame is automatically complete. -/
theorem _root_.CStarModule.IsParsevalFrame.completeSpace {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    CompleteSpace E := by
  let f : E →ₗᵢ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    (frameAnalysisCLM A x).toLinearMap.isometryOfInnerCStarModule fun z ↦
      isParsevalFrame_iff_inner_frameAnalysisCLM_frameAnalysisCLM.mp hx z z
  exact f.isometry.isUniformInducing.completeSpace
    (Function.LeftInverse.isClosed_range (fun z ↦ by simpa [f] using hx.sum_inner_smul z)
      (frameSynthesisCLM A x).continuous f.continuous).isComplete

end NonUnital

/-! ### Unital coefficient algebras: algebraic frame maps and projection comparison -/

section UnitalAlgebraic

/-- The synthesis operator of `x : ι → E` bundled as a right `A`-linear (`Aᵐᵒᵖ`-linear) map. -/
def frameSynthesisLinearMap (A : Type*) {ι E : Type*} [Fintype ι] [Ring A] [AddCommMonoid E]
    [Module Aᵐᵒᵖ E] (x : ι → E) : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E where
  toFun v := ∑ i, op (v i) • x i
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [WithCStarModule.smul_apply, MulOpposite.smul_eq_mul_unop,
    op_mul, mul_smul, Finset.smul_sum]

section Synthesis

variable {A ι E : Type*} [Fintype ι] [Ring A] [AddCommMonoid E] [Module Aᵐᵒᵖ E]

@[simp] theorem frameSynthesisLinearMap_apply (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    frameSynthesisLinearMap A x v = ∑ i, op (v i) • x i := by simp [frameSynthesisLinearMap]

theorem frameSynthesisLinearMap_single_one [DecidableEq ι] (x : ι → E) (i : ι) :
    frameSynthesisLinearMap A x ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))) =
      x i := by simp [Pi.single_apply, apply_ite op, ite_smul]

/-- Any right `A`-linear map out of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` equals the synthesis map of its values on
the standard basis. -/
theorem _root_.LinearMap.eq_frameSynthesisLinearMap [DecidableEq ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) : f = frameSynthesisLinearMap A
      (fun i ↦ f ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)))) := by
  ext v; conv_lhs => rw [← WithCStarModule.sum_op_smul_single_one v]
  simp [map_sum]

end Synthesis

/-- The analysis operator of `x : ι → E` bundled as a right `A`-linear (`Aᵐᵒᵖ`-linear) map. -/
def frameAnalysisLinearMap (A : Type*) {ι E : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [Norm E]
    [CStarModule Aᵐᵒᵖ E] (x : ι → E) : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) where
  toFun z := (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm fun i ↦ unop (inner Aᵐᵒᵖ (x i) z)
  map_add' _ _ := by ext i; simp [CStarModule.inner_add_right]
  map_smul' _ _ := by ext i; simp [MulOpposite.smul_eq_mul_unop, inner_op_smul_right]

section Analysis

variable {A ι E : Type*} [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ]
  [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

@[simp] theorem frameAnalysisLinearMap_apply_apply (x : ι → E) (z : E) (i : ι) :
    frameAnalysisLinearMap A x z i = unop (inner Aᵐᵒᵖ (x i) z) := by simp [frameAnalysisLinearMap]

variable [Fintype ι]

/-/-- Synthesis after analysis equals the identity when `x` is a Parseval frame. -/
theorem _root_.CStarModule.IsParsevalFrame.frameSynthesisLinearMap_comp_frameAnalysisLinearMap_eq_id
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    (frameSynthesisLinearMap A x).comp (frameAnalysisLinearMap A x) = LinearMap.id := by
  ext z; simpa [LinearMap.comp_apply] using hx.sum_inner_smul z

/-- Analysis after synthesis equals multiplication by the Gram matrix `CStarMatrix.gram A x`
for any finite family `x : ι → E`. -/
@[simp] theorem frameAnalysisLinearMap_comp_frameSynthesisLinearMap (x : ι → E) :
    (frameAnalysisLinearMap A x).comp (frameSynthesisLinearMap A x) =
      mulVecLinearMap (CStarMatrix.gram A x) := by ext v i; simp [inner_sum_right', Finset.unop_sum]

/-- The range of `frameAnalysisLinearMap A x` for a Parseval frame `x` is
`LinearMap.range (TauCeti.CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x))`. -/
theorem _root_.CStarModule.IsParsevalFrame.range_frameAnalysisLinearMap {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    LinearMap.range (frameAnalysisLinearMap A x) =
      LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x)) := by
  refine le_antisymm ?_ (frameAnalysisLinearMap_comp_frameSynthesisLinearMap (A := A) x ▸
    LinearMap.range_comp_le_range _ _)
  rintro _ ⟨z, rfl⟩; refine ⟨frameAnalysisLinearMap A x z, ?_⟩
  rw [← frameAnalysisLinearMap_comp_frameSynthesisLinearMap, LinearMap.comp_apply]
  simpa using congrArg (frameAnalysisLinearMap A x) (hx.sum_inner_smul z)

end Analysis

end UnitalAlgebraic

section Unital

@[simp] theorem coe_frameSynthesisLinearMap {A ι E : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    ⇑(frameSynthesisLinearMap A x) = ⇑(frameSynthesisCLM A x) := by funext v; simp

theorem frameSynthesisCLM_single_one {A ι E : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] [DecidableEq ι] (x : ι → E) (i : ι) :
    frameSynthesisCLM A x ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))) =
      x i := by
  let _ := CStarModule.module Aᵐᵒᵖ E
  exact coe_frameSynthesisLinearMap (A := A) x ▸ frameSynthesisLinearMap_single_one x i

variable {A ι E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

@[simp] theorem coe_frameAnalysisLinearMap (x : ι → E) :
    ⇑(frameAnalysisLinearMap A x) = ⇑(frameAnalysisCLM A x) := by funext z; ext i; simp

variable [Fintype ι]

/-- The standard basis `i ↦ Pi.single i 1` of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` is a Parseval frame. -/
theorem isParsevalFrame_single_one [DecidableEq ι] : IsParsevalFrame Aᵐᵒᵖ
    (fun i : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))) :=
  isParsevalFrame_iff.mpr fun v ↦ by
    simpa [WithCStarModule.inner_single_left, inner_mulOpposite] using
      WithCStarModule.sum_op_smul_single_one v

/-- The analysis map of a Parseval frame is a right `A`-linear isometry into
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.frameAnalysisIsometry {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) : E →ₗᵢ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (frameAnalysisLinearMap A x).isometryOfInnerCStarModule fun z ↦
    isParsevalFrame_iff_inner_frameAnalysisCLM_frameAnalysisCLM.mp hx z z

@[simp] theorem _root_.CStarModule.IsParsevalFrame.coe_frameAnalysisIsometry {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) : ⇑hx.frameAnalysisIsometry = ⇑(frameAnalysisCLM A x) :=
  (LinearMap.coe_isometryOfInnerCStarModule _ _).trans (coe_frameAnalysisLinearMap x)

@[simp] theorem _root_.CStarModule.IsParsevalFrame.frameAnalysisIsometry_toLinearMap {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    hx.frameAnalysisIsometry.toLinearMap = frameAnalysisLinearMap A x :=
  LinearMap.isometryOfInnerCStarModule_toLinearMap _ _

/-- A Parseval frame `x : ι → E` identifies `E` unitarily (`E ≃ₗᵢ[Aᵐᵒᵖ] _`) with
`LinearMap.range (TauCeti.CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x))`, with inverse given
by restricting `frameSynthesisLinearMap A x`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.equivRangeGram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x)) := by
  let S := LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x))
  let f : E →ₗᵢ[Aᵐᵒᵖ] S :=
    { toLinearMap := (frameAnalysisLinearMap A x).codRestrict S fun z ↦ by
        dsimp only [S]; rw [← hx.range_frameAnalysisLinearMap]; exact LinearMap.mem_range_self _ z
      norm_map' := fun z ↦ by simpa using hx.frameAnalysisIsometry.norm_map z }
  refine LinearIsometryEquiv.ofLinearIsometry f ((frameSynthesisLinearMap A x).comp S.subtype) ?_
    (LinearMap.ext fun z ↦ by simpa [f, LinearMap.comp_apply] using hx.sum_inner_smul z)
  apply LinearMap.ext; rintro ⟨w, v, rfl⟩; apply Subtype.ext
  dsimp only [f, LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearIsometry.coe_toLinearMap,
    Submodule.coe_subtype, LinearMap.id_apply]
  rw [← LinearMap.comp_apply, frameAnalysisLinearMap_comp_frameSynthesisLinearMap,
    CStarMatrix.mulVecLinearMap_mulVecLinearMap,
    (CStarMatrix.isStarProjection_gram hx).isIdempotentElem.eq]

@[simp] theorem _root_.CStarModule.IsParsevalFrame.coe_equivRangeGram_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (z : E) :
    (hx.equivRangeGram z : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) = frameAnalysisCLM A x z := by
  simp [_root_.CStarModule.IsParsevalFrame.equivRangeGram]

@[simp] theorem _root_.CStarModule.IsParsevalFrame.equivRangeGram_symm_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (u : LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x))) :
    hx.equivRangeGram.symm u = frameSynthesisLinearMap A x u.val := by
  simp [_root_.CStarModule.IsParsevalFrame.equivRangeGram]

/-- If `p : CStarMatrix ι ι A` is a star projection and
`U : E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (TauCeti.CStarMatrix.mulVecLinearMap p)` is a unitary isomorphism,
then `E` admits an `ι`-indexed Parseval frame whose Gram matrix is `p`. -/
theorem _root_.IsStarProjection.exists_isParsevalFrame_and_gram_eq {p : CStarMatrix ι ι A}
    (hp : IsStarProjection p) (U : E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (mulVecLinearMap p)) :
    ∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x ∧ CStarMatrix.gram A x = p := by
  classical
  let e := fun j : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single j (1 : A))
  let u : ι → LinearMap.range (mulVecLinearMap p) := fun j ↦ ⟨mulVecLinearMap p (e j), e j, rfl⟩
  let x : ι → E := fun j ↦ U.symm (u j)
  have hgram : CStarMatrix.gram A x = p := by
    have hU : CStarMatrix.gram A x = CStarMatrix.gram A (fun j ↦ mulVecCLM p (e j)) := by
      ext i j; simp [x, u]
    rw [hU, CStarMatrix.gram_mulVecCLM_single_one, ← CStarMatrix.star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  refine ⟨x, isParsevalFrame_iff_isStarProjection_gram_and_frameSynthesisCLM_surjective.mpr
    ⟨hgram ▸ hp, fun z ↦ ?_⟩, hgram⟩
  obtain ⟨v, hv⟩ := (U z).property; refine ⟨v, U.toLinearEquiv.injective (Subtype.ext ?_)⟩
  rw [frameSynthesisCLM_apply, map_sum]; simp only [map_smul, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [← hv]; conv_rhs => rw [← WithCStarModule.sum_op_smul_single_one v, map_sum]
  simp [x, u, e]

/-- Over a unital C⋆-algebra, `E` admits an `ι`-indexed Parseval frame iff `E` is unitarily
isomorphic to `LinearMap.range (TauCeti.CStarMatrix.mulVecLinearMap p)` for a star projection `p`.
-/
theorem exists_isParsevalFrame_iff_exists_isStarProjection_linearIsometryEquiv :
    (∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x) ↔
      ∃ p : CStarMatrix ι ι A, IsStarProjection p ∧
        Nonempty (E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (mulVecLinearMap p)) :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨CStarMatrix.gram A x, CStarMatrix.isStarProjection_gram hx, ⟨hx.equivRangeGram⟩⟩,
    fun ⟨_, hp, ⟨U⟩⟩ ↦ (hp.exists_isParsevalFrame_and_gram_eq U).imp fun _ h ↦ h.1⟩

end Unital

end TauCeti.CStarModule

/-! ### Splitting Gram matrices and Parseval frames on retracts of free modules -/

namespace LinearMap

open TauCeti.CStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem algebraMap_inv_le_gram_of_le_smul {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module ℂ W] [SMul Aᵐᵒᵖ W] [Norm W] [CStarModule Aᵐᵒᵖ W]
    (y : ι → W) {C : ℝ} (hC : 0 < C) (hbound : ∀ w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A),
      unop (inner Aᵐᵒᵖ w w) ≤ C • unop (inner Aᵐᵒᵖ (∑ i, op (w i) • y i) (∑ i, op (w i) • y i))) :
    algebraMap ℝ (CStarMatrix ι ι A) C⁻¹ ≤ CStarMatrix.gram A y := by
  rw [CStarMatrix.algebraMap_le_iff_forall_sum_le]; intro a
  let w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm a
  have hw : ∑ i, star (a i) * a i = unop (inner Aᵐᵒᵖ w w) := by
    simp [WithCStarModule.pi_inner, Finset.unop_sum, w]
  rw [hw, CStarMatrix.sum_star_mul_gram_mul, inv_smul_le_iff_of_pos hC]; exact hbound w

private theorem exists_gram_eq_one_of_isStrictlyPositive {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module ℂ W] [Module Aᵐᵒᵖ W] [Norm W] [CStarModule Aᵐᵒᵖ W] {y : ι → W}
    (hM : IsStrictlyPositive (CStarMatrix.gram A y)) :
    ∃ B S : CStarMatrix ι ι A, CStarMatrix.gram A (fun j ↦ ∑ k, op (B k j) • y k) = 1 ∧
      ∀ k, ∑ j, op (S j k) • ∑ l, op (B l j) • y l = y k := by
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  set M := CStarMatrix.gram A y; set S := CFC.sqrt M; set B := CFC.sqrt (Ring.inverse M)
  have hBS : B * S = 1 := by
    change CFC.sqrt (Ring.inverse M) * S = 1
    rw [CFC.sqrt_ringInverse]; exact Ring.inverse_mul_cancel S (hM.sqrt M).isUnit
  refine ⟨B, S, ?_, fun k ↦ ?_⟩
  · ext i j; rw [CStarMatrix.gram_apply, ← CStarMatrix.sum_star_mul_gram_mul]
    have hmul : (star B * M * B) i j = ∑ k, ∑ l, star (B k i) * M k l * B l j := by
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    rw [← hmul, (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, ← CFC.conjSqrt_apply,
      CFC.conjSqrt_ringInverse_self M hM]
  · simp only [Finset.smul_sum, ← mul_smul, ← op_mul]; rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Finset.op_sum, ← CStarMatrix.mul_apply, hBS,
      CStarMatrix.one_apply, apply_ite op, ite_smul]; simp

section FreeSource

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E]
  [CStarModule Aᵐᵒᵖ E]

/-- Any right `A`-linear map out of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` into a right Hilbert `A`-module equals the
synthesis map of its values on the standard basis, and is therefore bounded and complex-linear. -/
theorem apply_eq_frameSynthesisCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) : f v = frameSynthesisCLM A
      (fun i ↦ f ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)))) v := by
  rw [← coe_frameSynthesisLinearMap]; exact LinearMap.congr_fun f.eq_frameSynthesisLinearMap v

/-- Every right `A`-linear map out of a finitely generated free right Hilbert `A`-module
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` into a right Hilbert `A`-module is continuous. -/
theorem continuous_of_finite_pi_cstarModule {ι : Type*} [Finite ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) : Continuous f := by
  classical
  cases nonempty_fintype ι
  exact (frameSynthesisCLM A _).continuous.congr fun v ↦ (f.apply_eq_frameSynthesisCLM v).symm

end FreeSource

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E]
  [CStarModule Aᵐᵒᵖ E] [CompleteSpace E]

/-- If `f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E` and `g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` satisfy
`f ∘ₗ g = .id` on a complete right Hilbert `A`-module `E`, then `g` is continuous. -/
theorem continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule {ι : Type*} [Finite ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))
    (hfg : f ∘ₗ g = LinearMap.id) : Continuous g := by
  classical
  cases nonempty_fintype ι
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := CStarModule.isScalarTower _ _
  have hfg_apply (z : E) : f (g z) = z := LinearMap.congr_fun hfg z
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x ↦
    (CStarModule.norm_zero_iff Aᵐᵒᵖ x).mp
  refine (g.restrictScalars ℂ).continuous_of_isClosed_graph ?_
  rw [show ((g.restrictScalars ℂ).graph : Set (E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))) =
      {p : E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) | f p.2 = p.1 ∧ (g ∘ₗ f) p.2 = p.2} from Set.ext fun ⟨x, y⟩ ↦ by
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, LinearMap.restrictScalars_apply,
      Set.mem_ofPred_eq, LinearMap.comp_apply]
    exact ⟨fun h ↦ ⟨by rw [h, hfg_apply], by rw [h, hfg_apply]⟩, fun ⟨h1, h2⟩ ↦ by rw [← h1, h2]⟩]
  exact (isClosed_eq (f.continuous_of_finite_pi_cstarModule.comp continuous_snd)
    continuous_fst).inter (isClosed_eq
      ((g ∘ₗ f).continuous_of_finite_pi_cstarModule.comp continuous_snd) continuous_snd)

private theorem isStrictlyPositive_gram_splitting {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))
    (hfg : f ∘ₗ g = LinearMap.id) :
    let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x ↦
      (CStarModule.norm_zero_iff Aᵐᵒᵖ x).mp
    IsStrictlyPositive (CStarMatrix.gram A fun i : ι ↦
      (WithCStarModule.equiv Aᵐᵒᵖ (E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))).symm
        (f ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))),
          (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)) -
            g (f ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)))))) := by
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x ↦
    (CStarModule.norm_zero_iff Aᵐᵒᵖ x).mp
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := CStarModule.isScalarTower _ _
  let gL : E →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    ⟨g.restrictScalars ℂ, f.continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule g hfg⟩
  let h : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _).symm.toLinearMap ∘ₗ f.prod (LinearMap.id - g ∘ₗ f)
  have hh (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
      h v = (WithCStarModule.equiv Aᵐᵒᵖ _).symm (f v, v - g (f v)) := by simp [h]
  have hC : (0 : ℝ) < 2 * (1 + ‖gL‖ ^ 2) := by positivity
  refine (isStrictlyPositive_algebraMap (inv_pos.mpr hC)).of_le <|
    algebraMap_inv_le_gram_of_le_smul _ hC fun w ↦ ?_
  have hw_sum : (∑ i, op (w i) • (WithCStarModule.equiv Aᵐᵒᵖ _).symm
      (f ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))),
        (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)) -
          g (f ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A)))))) = h w := by
    simp_rw [← hh, ← map_smul, ← map_sum, WithCStarModule.sum_op_smul_single_one]
  rw [hw_sum, hh w, WithCStarModule.prod_inner, WithCStarModule.equiv_symm_fst,
    WithCStarModule.equiv_symm_snd, unop_add]
  set u := unop (inner Aᵐᵒᵖ (f w) (f w)); set v := unop (inner Aᵐᵒᵖ (w - g (f w)) (w - g (f w)))
  have hg_le : unop (inner Aᵐᵒᵖ (g (f w)) (g (f w))) ≤ ‖gL‖ ^ 2 • u :=
    gL.unop_inner_map_map_le_norm_sq_smul (fun b z ↦ g.map_smul (op b) z) (f w)
  have hw_split : unop (inner Aᵐᵒᵖ w w) ≤ (2 : ℝ) • (‖gL‖ ^ 2 • u + v) := by
    have hadd := unop_inner_add_add_self_le (A := A) (g (f w)) (w - g (f w))
    rw [add_sub_cancel] at hadd
    exact hadd.trans
      ((nsmul_le_nsmul_right (add_le_add hg_le (le_refl v)) 2).trans_eq (by simp only [two_smul]))
  have hu : 0 ≤ u := unop_nonneg.mpr CStarModule.inner_self_nonneg
  have hv : 0 ≤ v :=
    unop_nonneg.mpr (CStarModule.inner_self_nonneg (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)))
  have hCu : ‖gL‖ ^ 2 • u + v ≤ (1 + ‖gL‖ ^ 2) • (u + v) :=
    (add_le_add (le_add_of_nonneg_left hu)
      (le_add_of_nonneg_right (smul_nonneg (sq_nonneg _) hv))).trans_eq
      (by rw [add_add_add_comm, add_smul, one_smul, smul_add])
  exact hw_split.trans
    ((smul_le_smul_of_nonneg_left hCu zero_le_two).trans_eq (mul_smul _ _ _).symm)

/-- Any complete right Hilbert `A`-module `E` that splits as a right `A`-linear retract of
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` (`f ∘ₗ g = LinearMap.id`) admits an `ι`-indexed Parseval frame. -/
theorem exists_isParsevalFrame_of_comp_eq_id {ι : Type*} [Fintype ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))
    (hfg : f ∘ₗ g = LinearMap.id) : ∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x := by
  classical
  let : NormedAddCommGroup E := NormedAddCommGroup.ofSeparation fun x ↦
    (CStarModule.norm_zero_iff Aᵐᵒᵖ x).mp
  let e := fun i : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))
  let h : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _).symm.toLinearMap ∘ₗ f.prod (LinearMap.id - g ∘ₗ f)
  let y : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    fun i ↦ (WithCStarModule.equiv Aᵐᵒᵖ _).symm (f (e i), e i - g (f (e i)))
  have hy (i : ι) : y i = h (e i) := by simp [y, h]
  obtain ⟨B, S, hgram_η, hy_recover⟩ :=
    exists_gram_eq_one_of_isStrictlyPositive (y := y) (isStrictlyPositive_gram_splitting f g hfg)
  let η : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) := fun j ↦ ∑ k, op (B k j) • y k
  let x : ι → E := fun j ↦ ∑ k, op (B k j) • f (e k)
  let π_fst : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) →ₗ[Aᵐᵒᵖ] E :=
    LinearMap.fst Aᵐᵒᵖ _ _ ∘ₗ (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _).toLinearMap
  have hπ_fst (w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))) : π_fst w = w.fst := by simp [π_fst]
  have hη_fst (j : ι) : (η j).fst = x j := by rw [← hπ_fst, map_sum]; simp [hπ_fst, y, x]
  refine ⟨x, isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  let u₀ : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) := (WithCStarModule.equiv Aᵐᵒᵖ _).symm (z, 0)
  have hfg_z : f (g z) = z := LinearMap.congr_fun hfg z
  have hu₀_eq : h (g z) = u₀ := (WithCStarModule.equiv Aᵐᵒᵖ _).injective <|
    Prod.ext (by simp [u₀, h, hfg_z]) (by simp [u₀, h, hfg_z])
  have hu₀_span : ∃ c : ι → A, ∑ j, op (c j) • η j = u₀ := ⟨fun j ↦ ∑ k, S j k * g z k, by
    calc ∑ j, op (∑ k, S j k * g z k) • η j
        = ∑ k, op (g z k) • ∑ j, op (S j k) • η j := by
            simp_rw [Finset.op_sum, Finset.sum_smul, op_mul, mul_smul, Finset.smul_sum]
            exact Finset.sum_comm
      _ = h (∑ k, op (g z k) • e k) := by simp_rw [η, hy_recover, hy, ← map_smul, ← map_sum]
      _ = u₀ := by rw [WithCStarModule.sum_op_smul_single_one, hu₀_eq]⟩
  have hu₀_rec : ∑ i, inner Aᵐᵒᵖ (η i) u₀ • η i = u₀ :=
    TauCeti.CStarMatrix.sum_inner_smul_of_gram_eq_one hgram_η hu₀_span
  have hinner_x (i : ι) : inner Aᵐᵒᵖ (x i) z = inner Aᵐᵒᵖ (η i) u₀ := by
    rw [WithCStarModule.prod_inner]; simp [u₀, hη_fst]
  calc ∑ i, inner Aᵐᵒᵖ (x i) z • x i
      = π_fst (∑ i, inner Aᵐᵒᵖ (η i) u₀ • η i) := by
          simp_rw [hinner_x, map_sum, map_smul, hπ_fst, hη_fst]
    _ = z := by rw [hu₀_rec, hπ_fst, WithCStarModule.equiv_symm_fst]

end LinearMap

namespace TauCeti.CStarModule

/-! ### Frame-formula adjoints and polar decomposition -/

/-- Explicit frame-formula candidate adjoint `y ↦ ∑ i, ⟪T (x i), y⟫_A • x i` of a function
`T : E → F` with respect to a finite family `x : ι → E`. -/
def frameAdjoint (A : Type*) {ι E F : Type*} [Fintype ι] [Semiring A] [StarRing A] [Module ℂ A]
    [PartialOrder A] [Norm A] [AddCommMonoid E] [Module A E] [AddCommGroup F] [Module ℂ F]
    [Module A F] [Norm F] [CStarModule A F] (x : ι → E) (T : E → F) : F →ₗ[A] E where
  toFun y := ∑ i, inner A (T (x i)) y • x i
  map_add' _ _ := by simp [CStarModule.inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [inner_op_smul_right, mul_smul, Finset.smul_sum]

@[simp] theorem frameAdjoint_apply {A ι E F : Type*} [Fintype ι] [Semiring A] [StarRing A]
    [Module ℂ A] [PartialOrder A] [Norm A] [AddCommMonoid E] [Module A E] [AddCommGroup F]
    [Module ℂ F] [Module A F] [Norm F] [CStarModule A F] (x : ι → E) (T : E → F) (y : F) :
    frameAdjoint A x T y = ∑ i, inner A (T (x i)) y • x i := by simp [frameAdjoint]

/-- Every `A`-linear map `T` out of a C⋆-module equipped with a finite Parseval frame `x : ι → E`
forms a module adjoint pair with `frameAdjoint A x T`. -/
theorem _root_.CStarModule.IsParsevalFrame.isAdjointPair_frameAdjoint {A ι E F 𝓕 : Type*}
    [Fintype ι] [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [Norm A]
    [AddCommGroup E] [Module ℂ E] [Module A E] [Norm E] [CStarModule A E]
    [AddCommGroup F] [Module ℂ F] [Module A F] [Norm F] [CStarModule A F]
    [FunLike 𝓕 E F] [LinearMapClass 𝓕 A E F] {x : ι → E} (hx : IsParsevalFrame A x) (T : 𝓕) :
    LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T (frameAdjoint A x T) := by
  rw [isAdjointPair_inner_iff]; intro z y
  conv_lhs => rw [← hx.sum_inner_smul z, map_sum]
  simp only [map_smul, inner_sum_left, inner_sum_right, inner_op_smul_left, inner_op_smul_right,
    frameAdjoint_apply, star_inner]

section Polar

/-- Matrix `CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x)` in
`CStarMatrix ι ι A` for a family `x : ι → E` and a function `T : E → F`. When `x` is a Parseval
frame and `T` is right `A`-linear, this represents `T* T ⊕ 1` on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` with
the identity on the complementary summand `ker (CStarMatrix.gram A x)`. -/
def polarMatrix (A : Type*) {ι E F : Type*} [DecidableEq ι] [AddGroupWithOne A] [Inner Aᵐᵒᵖ E]
    [Inner Aᵐᵒᵖ F] (x : ι → E) (T : E → F) : CStarMatrix ι ι A :=
  CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x)

section PolarBasic

variable {A ι E F : Type*} [DecidableEq ι] [AddGroupWithOne A] [Inner Aᵐᵒᵖ E] [Inner Aᵐᵒᵖ F]

theorem polarMatrix_def (x : ι → E) (T : E → F) :
    polarMatrix A x T = CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x) := (rfl)

@[simp] theorem polarMatrix_apply (x : ι → E) (T : E → F) (i j : ι) : polarMatrix A x T i j =
    unop (inner Aᵐᵒᵖ (T (x i)) (T (x j))) + (1 - CStarMatrix.gram A x) i j := by
  simp [polarMatrix_def]

end PolarBasic

/-- Over a unital C⋆-algebra, for a Parseval frame `x` and an arbitrary function `T : E → F`,
`polarMatrix A x T` is positive (`0 ≤ polarMatrix A x T`). -/
theorem _root_.CStarModule.IsParsevalFrame.polarMatrix_nonneg {A ι E F : Type*} [Fintype ι]
    [DecidableEq ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]
    [AddCommGroup F] [Module ℂ F] [SMul Aᵐᵒᵖ F] [Norm F] [CStarModule Aᵐᵒᵖ F]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E → F) : 0 ≤ polarMatrix A x T :=
  add_nonneg (CStarMatrix.gram_nonneg _) (CStarMatrix.isStarProjection_gram hx).one_sub.nonneg

section PolarAlg

variable {A ι E F 𝓕 : Type*} [Fintype ι] [DecidableEq ι] [SeminormedRing A] [StarRing A]
  [Module ℂ A] [StarModule ℂ A] [PartialOrder A] [AddCommGroup E] [Module ℂ E]
  [Module Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E] [AddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F]
  [Norm F] [CStarModule Aᵐᵒᵖ F] [FunLike 𝓕 E F] [LinearMapClass 𝓕 Aᵐᵒᵖ E F]

/-- When `T` is right `A`-linear, multiplying `polarMatrix A x T` on the right by the Gram
projection `CStarMatrix.gram A x` isolates the Gram matrix of `T ∘ x`:
`polarMatrix A x T * CStarMatrix.gram A x = CStarMatrix.gram A (fun i ↦ T (x i))`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarMatrix_mul_gram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : 𝓕) :
    polarMatrix A x T * CStarMatrix.gram A x = CStarMatrix.gram A (fun i ↦ T (x i)) := by
  rw [polarMatrix_def, add_mul, (CStarMatrix.isStarProjection_gram hx).one_sub_mul_self, add_zero]
  ext i j
  conv_rhs => rw [CStarMatrix.gram_apply, ← hx.sum_inner_smul (x j), map_sum, inner_sum_right']
  simp [CStarMatrix.mul_apply, map_smul, Finset.unop_sum]

/-- When `T` is right `A`-linear, `polarMatrix A x T` commutes with the Gram projection
`CStarMatrix.gram A x`, so functional-calculus operations on `polarMatrix A x T` preserve the
Gram range. -/
theorem _root_.CStarModule.IsParsevalFrame.commute_polarMatrix_gram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : 𝓕) : Commute (polarMatrix A x T) (CStarMatrix.gram A x) :=
  IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ _ _
    ((TauCeti.CStarMatrix.isSelfAdjoint_gram _).add
      (CStarMatrix.isStarProjection_gram hx).one_sub.isSelfAdjoint)
    (CStarMatrix.isStarProjection_gram hx).isSelfAdjoint (TauCeti.CStarMatrix.isSelfAdjoint_gram _)
    (hx.polarMatrix_mul_gram T)

end PolarAlg

variable {A ι E F : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

private theorem frameSynthesis_mulVec_comp_eq_id [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) {M N : CStarMatrix ι ι A} (hMN : M * N = 1)
    (hcomm : Commute N (CStarMatrix.gram A x)) :
    (frameSynthesisLinearMap A x ∘ₗ mulVecLinearMap M ∘ₗ frameAnalysisLinearMap A x) ∘ₗ
      (frameSynthesisLinearMap A x ∘ₗ mulVecLinearMap N ∘ₗ frameAnalysisLinearMap A x) =
      LinearMap.id := by
  have hmul : M * (CStarMatrix.gram A x * N) = CStarMatrix.gram A x := by
    rw [← hcomm.eq, ← mul_assoc, hMN, one_mul]
  ext z
  simp only [LinearMap.comp_apply, LinearMap.id_apply, coe_frameAnalysisLinearMap,
    coe_frameSynthesisLinearMap, CStarMatrix.coe_mulVecLinearMap,
    frameAnalysisCLM_frameSynthesisCLM_apply, CStarMatrix.mulVecCLM_mulVecCLM]
  rw [hmul, ← frameAnalysisCLM_frameSynthesisCLM_apply]
  simp_rw [frameSynthesisCLM_frameAnalysisCLM_apply, hx.sum_inner_smul]

variable [CompleteSpace F]

/-- When `x : ι → E` is a Parseval frame and `T : E ≃ₗ[Aᵐᵒᵖ] F` is a right `A`-linear
equivalence into a complete right Hilbert `A`-module `F`, `polarMatrix A x T` is strictly positive
in `CStarMatrix ι ι A`. -/
theorem _root_.CStarModule.IsParsevalFrame.isStrictlyPositive_polarMatrix [DecidableEq ι]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    IsStrictlyPositive (polarMatrix A x T) := by
  let : NormedAddCommGroup F := NormedAddCommGroup.ofSeparation fun z ↦
    (CStarModule.norm_zero_iff Aᵐᵒᵖ z).mp
  let e := fun i : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))
  let f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] F := T.toLinearMap ∘ₗ frameSynthesisLinearMap A x
  let g : F →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := frameAnalysisLinearMap A x ∘ₗ T.symm.toLinearMap
  have hfg : f ∘ₗ g = LinearMap.id := LinearMap.ext fun w ↦ by
    simpa [f, g, LinearMap.comp_apply] using congrArg T
      (LinearMap.congr_fun hx.frameSynthesisLinearMap_comp_frameAnalysisLinearMap_eq_id (T.symm w))
  let y : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, F × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    fun i ↦ (WithCStarModule.equiv Aᵐᵒᵖ _).symm (f (e i), e i - g (f (e i)))
  suffices polarMatrix A x T = CStarMatrix.gram A y from
    this ▸ LinearMap.isStrictlyPositive_gram_splitting f g hfg
  set p := CStarMatrix.gram A x with hp_def
  have hfe (i : ι) : f (e i) = T (x i) := by
    rw [LinearMap.comp_apply, frameSynthesisLinearMap_single_one, LinearEquiv.coe_coe]
  have h1p (i : ι) : mulVecCLM (1 - p) (e i) = e i - g (f (e i)) := by
    rw [hfe, ← CStarMatrix.coe_mulVecLinearMap, map_sub, LinearMap.sub_apply,
      TauCeti.CStarMatrix.mulVecLinearMap_one, LinearMap.id_apply, hp_def,
      ← frameAnalysisLinearMap_comp_frameSynthesisLinearMap, LinearMap.comp_apply,
      frameSynthesisLinearMap_single_one]; simp [g]
  have hy_fst (i : ι) : (y i).fst = T (x i) := by simp [y, hfe]
  have hy_snd (i : ι) : (y i).snd = mulVecCLM (1 - p) (e i) := by rw [h1p]; simp [y]
  have h1p_gram : CStarMatrix.gram A (fun j ↦ mulVecCLM (1 - p) (e j)) = 1 - p := by
    rw [CStarMatrix.gram_mulVecCLM_single_one, ← CStarMatrix.star_eq_conjTranspose,
      (CStarMatrix.isStarProjection_gram hx).one_sub.isSelfAdjoint.star_eq,
      (CStarMatrix.isStarProjection_gram hx).one_sub.isIdempotentElem.eq]
  ext i j
  rw [polarMatrix_apply, ← hp_def, CStarMatrix.gram_apply, WithCStarModule.prod_inner, unop_add,
    hy_fst, hy_fst, hy_snd, hy_snd,
    ← CStarMatrix.gram_apply (A := A) (x := fun k ↦ mulVecCLM (1 - p) (e k)), h1p_gram]

theorem _root_.CStarModule.IsParsevalFrame.isUnit_sqrt_polarMatrix [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : IsUnit (CFC.sqrt (polarMatrix A x T)) :=
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  (hx.isStrictlyPositive_polarMatrix T).isUnit_cfcSqrt _

/-- Positive self-adjoint modulus `|T| : E ≃ₗ[Aᵐᵒᵖ] E` of `T : E ≃ₗ[Aᵐᵒᵖ] F` into a complete right
Hilbert `A`-module `F`, constructed from `hx` via `frameAnalysisLinearMap A x`,
`TauCeti.CStarMatrix.mulVecLinearMap (CFC.sqrt (polarMatrix A x T))`, and
`frameSynthesisLinearMap A x`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗ[Aᵐᵒᵖ] E :=
  letI := Classical.decEq ι
  let S := CFC.sqrt (polarMatrix A x T)
  LinearEquiv.ofLinearMap
    ((frameSynthesisLinearMap A x).comp ((mulVecLinearMap S).comp (frameAnalysisLinearMap A x)))
    ((frameSynthesisLinearMap A x).comp
      ((mulVecLinearMap (Ring.inverse S)).comp (frameAnalysisLinearMap A x)))
    (frameSynthesis_mulVec_comp_eq_id hx (Ring.mul_inverse_cancel S (hx.isUnit_sqrt_polarMatrix T))
      (by rw [Ring.inverse_of_isUnit (hx.isUnit_sqrt_polarMatrix T)]
          exact Commute.units_inv_left <| (hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt))
    (frameSynthesis_mulVec_comp_eq_id hx (Ring.inverse_mul_cancel S (hx.isUnit_sqrt_polarMatrix T))
      ((hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt))

theorem _root_.CStarModule.IsParsevalFrame.polarModulus_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T z = frameSynthesisCLM A x
      (mulVecCLM (CFC.sqrt (polarMatrix A x T)) (frameAnalysisCLM A x z)) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  simp [_root_.CStarModule.IsParsevalFrame.polarModulus]

theorem _root_.CStarModule.IsParsevalFrame.polarModulus_symm_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    (hx.polarModulus T).symm z = frameSynthesisCLM A x
      (mulVecCLM (Ring.inverse (CFC.sqrt (polarMatrix A x T))) (frameAnalysisCLM A x z)) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  simp [_root_.CStarModule.IsParsevalFrame.polarModulus]

/-- `hx.polarModulus T` is self-adjoint as a module operator on `E`. -/
theorem _root_.CStarModule.IsParsevalFrame.isAdjointPair_polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (hx.polarModulus T) (hx.polarModulus T) := by
  classical
  have hadj := isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x
  rw [isAdjointPair_inner_iff]; intro y z
  rw [hx.polarModulus_apply T y, hx.polarModulus_apply T z, hadj.inner_eq_cstarModule,
    (CStarMatrix.isAdjointPair_mulVecCLM_star _).inner_eq_cstarModule,
    (CFC.sqrt_nonneg (polarMatrix A x T)).isSelfAdjoint.star_eq,
    hadj.symm_cstarModule.inner_eq_cstarModule]

/-- `hx.polarModulus T` is positive: `0 ≤ ⟨z, |T| z⟩_A` for all `z : E`. -/
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_right_nonneg {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    0 ≤ inner Aᵐᵒᵖ z (hx.polarModulus T z) := by
  classical
  rw [hx.polarModulus_apply T z]
  set S := CFC.sqrt (polarMatrix A x T); set R := CFC.sqrt S
  have hRR (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) : mulVecCLM S v = mulVecCLM (star R) (mulVecCLM R v) := by
    rw [(CFC.sqrt_nonneg S).isSelfAdjoint.star_eq, CStarMatrix.mulVecCLM_mulVecCLM,
      CFC.sqrt_mul_sqrt_self S (CFC.sqrt_nonneg _)]
  have hadj := (isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x).symm_cstarModule
  rw [← hadj.inner_eq_cstarModule, hRR,
    ← (CStarMatrix.isAdjointPair_mulVecCLM_star R).inner_eq_cstarModule]
  exact CStarModule.inner_self_nonneg (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))

/-- `hx.polarModulus T` has the same Gram inner products as `T`:
`⟨|T| y, |T| z⟩_A = ⟨T y, T z⟩_A`. -/
@[simp]
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (y z : E) :
    inner Aᵐᵒᵖ (hx.polarModulus T y) (hx.polarModulus T z) = inner Aᵐᵒᵖ (T y) (T z) := by
  classical
  apply unop_injective; rw [hx.polarModulus_apply T y, hx.polarModulus_apply T z]
  set S := CFC.sqrt (polarMatrix A x T)
  have hSpS : S * CStarMatrix.gram A x * S = CStarMatrix.gram A (fun i ↦ T (x i)) := by
    have hcomm : Commute S (CStarMatrix.gram A x) :=
      (hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self _ (hx.polarMatrix_nonneg T),
      hx.polarMatrix_mul_gram T]
  rw [(isAdjointPair_frameSynthesisCLM_frameAnalysisCLM (A := A) x).inner_eq_cstarModule,
    frameAnalysisCLM_frameSynthesisCLM_apply,
    (CStarMatrix.isAdjointPair_mulVecCLM_star S).inner_eq_cstarModule,
    (CFC.sqrt_nonneg (polarMatrix A x T)).isSelfAdjoint.star_eq,
    CStarMatrix.mulVecCLM_mulVecCLM, CStarMatrix.mulVecCLM_mulVecCLM, hSpS]
  have hT (w : E) : ∑ i, op (frameAnalysisCLM A x w i) • T (x i) = T w := by
    conv_rhs => rw [← hx.sum_inner_smul w, map_sum]
    simp
  have hquad := CStarMatrix.sum_star_mul_gram_mul (A := A) (fun i ↦ T (x i))
    (frameAnalysisCLM A x y) (frameAnalysisCLM A x z)
  rw [hT y, hT z] at hquad
  simpa [WithCStarModule.pi_inner, Finset.unop_sum, CStarMatrix.mulVecCLM_apply_apply,
    Finset.mul_sum, mul_assoc] using hquad

/-- The square of `hx.polarModulus T` equals `T* ∘ T`:
`|T| (|T| z) = frameAdjoint Aᵐᵒᵖ x T (T z)`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T (hx.polarModulus T z) = frameAdjoint Aᵐᵒᵖ x T (T z) :=
  ext_inner_left (A := Aᵐᵒᵖ) fun y ↦ by
    rw [← (hx.isAdjointPair_polarModulus T).inner_eq_cstarModule,
      hx.inner_polarModulus_polarModulus T y z,
      (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule]

/-- Polar unitary `U = T ∘ |T|⁻¹ : E ≃ₗᵢ[Aᵐᵒᵖ] F` of a right `A`-linear equivalence
`T : E ≃ₗ[Aᵐᵒᵖ] F` into a complete right Hilbert `A`-module `F`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.polarUnitary {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗᵢ[Aᵐᵒᵖ] F :=
  ((hx.polarModulus T).symm.trans T).isometryOfInnerCStarModule fun z ↦ by
    simp only [LinearEquiv.trans_apply]
    rw [← hx.inner_polarModulus_polarModulus T, LinearEquiv.apply_symm_apply]

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T z = T ((hx.polarModulus T).symm z) := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_symm_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (w : F) :
    (hx.polarUnitary T).symm w = hx.polarModulus T (T.symm w) := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

/-- The polar decomposition factorization `T = U ∘ |T|`: applying `hx.polarUnitary T` after
`hx.polarModulus T` recovers `T`. -/
@[simp] theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T (hx.polarModulus T z) = T z := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

@[simp] theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_symm_map {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    (hx.polarUnitary T).symm (T z) = hx.polarModulus T z := by
  rw [hx.polarUnitary_symm_apply, T.symm_apply_apply]

end Polar

end TauCeti.CStarModule
