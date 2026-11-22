/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
public import TauCeti.Geometry.Lie.Tangent.Differential
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic

import TauCeti.Geometry.Manifold.DifferentialForm.VectorField

/-!
# Left-invariant differential forms on a Lie group

Let `G` be a Lie group with Lie algebra `𝔤 = T₁G` (`GroupLieAlgebra I G`). An alternating
`k`-linear map `a` on `𝔤`, with values in a normed space `F`, spreads over `G` by left translation
to the differential `k`-form

`j(a)_g(v₁, …, v_k) = a(dL_{g⁻¹} v₁, …, dL_{g⁻¹} v_k)`,

the *left-invariant form* of `a` (`TauCeti.leftInvariantForm`). The map `a ↦ j(a)` is the left
trivialization comparing the Chevalley–Eilenberg cochains of `𝔤` with differential forms on `G`;
its image is exactly the left-invariant forms, with inverse the evaluation at the identity.

The main result is that `j` intertwines the exterior derivative with the Chevalley–Eilenberg
differential `d` of `TauCeti.LieModule.Cohomology.d`, for coefficients on which `𝔤` acts trivially:
`d j(a) = j(d a)`. Evaluated on left-invariant vector fields, `j(a)` is constant, so in the
invariant formula for the exterior derivative only the Lie bracket terms survive, and the bracket of
left-invariant vector fields is the left-invariant vector field of the bracket in `𝔤`. Hence `j(a)`
is closed exactly when `a` is a cocycle. For instance, the Cartan three-form
`a(X, Y, Z) = B(X, [Y, Z])` of an invariant bilinear form `B` is a cocycle, so `j(a)` is a closed
three-form. Its pullback along a homomorphism is again left-invariant, the left-invariant form of
`a` precomposed with the differential of the homomorphism at the identity. In top degree, if that
precomposition is nonzero and the source group is compact of positive dimension, the integral of
the pullback is positive (`TauCeti.integralTopForm_leftInvariantForm_pos`), which is how such
forms detect nontrivial homotopy classes of maps of spheres.

## Main definitions

* `TauCeti.leftInvariantForm a`: the left-invariant form with value `a` at the identity.
* `TauCeti.leftInvariantSmoothForm a`: the same form, bundled as a smooth form on a
  finite-dimensional smooth Lie group; it is linear and injective in `a`, and invariant under
  left translations (`TauCeti.SmoothForm.mpullback_mul_left_leftInvariantSmoothForm`).

## Main results

* `TauCeti.leftInvariantForm_one`, `TauCeti.leftInvariantForm_apply_mulInvariantVectorField`: at
  the identity `j(a)` is `a`, and on left-invariant vector fields it is constant.
* `TauCeti.leftInvariantForm_apply_ne_zero`: `j(a)` vanishes nowhere unless `a = 0`.
* `TauCeti.mpullback_mul_left_leftInvariantForm`, `TauCeti.exists_eq_leftInvariantForm_iff`: the
  left-invariant forms are exactly the forms invariant under all left translations.
* `TauCeti.mpullback_leftInvariantForm`: the pullback along a homomorphism `φ` is the
  left-invariant form of `a` precomposed with the differential of `φ` at the identity.
* `TauCeti.isSmoothForm_leftInvariantForm`: `j(a)` is smooth.
* `TauCeti.integralTopForm_leftInvariantForm_pos`: on a compact Lie group of positive dimension, a
  nonzero left-invariant top form has positive integral for the orientation it defines.
* `TauCeti.mextDeriv_leftInvariantForm_apply`: `d j(a) = j(d a)`.
* `TauCeti.mextDeriv_leftInvariantForm_eq_zero_iff`, `TauCeti.isClosed_leftInvariantSmoothForm_iff`:
  `j(a)` is closed exactly when `a` is a Chevalley–Eilenberg cocycle.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124, §§2–5.
* J. L. Dupont, *Fibre Bundles and Chern–Weil Theory*, Lecture Notes Series 69, Aarhus
  University (2003), Appendix A, Proposition A.2.
-/

public section

noncomputable section

open Bundle Function Manifold VectorField
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The **left-invariant form** with value `a` at the identity: at `g`, the alternating map `a` on
the Lie algebra `T₁G` precomposed with the derivative of the left translation by `g⁻¹`,
`j(a)_g(v₁, …, v_k) = a(dL_{g⁻¹} v₁, …, dL_{g⁻¹} v_k)`. -/
def leftInvariantForm (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) : RoughForm I G F k :=
  fun g ↦ a.compContinuousLinearMap (mfderiv I I (g⁻¹ * ·) g)

/-- The defining formula of the left-invariant form: at `g`, translate the tangent vectors back
to the identity and apply `a`. -/
theorem leftInvariantForm_apply (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) (g : G)
    (v : Fin k → TangentSpace I g) :
    leftInvariantForm a g v = a fun i ↦ mfderiv I I (g⁻¹ * ·) g (v i) :=
  (rfl)

/-- Evaluated on vector fields, the left-invariant form of `a` is `a` evaluated on the left
Maurer-Cartan form of the fields. -/
theorem leftInvariantForm_apply_vectorField (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F)
    (V : Fin k → Π g : G, TangentSpace I g) (g : G) :
    leftInvariantForm a g (V · g) = a fun i ↦ leftMaurerCartanEval (E := E) (V i) g := by
  simp only [leftInvariantForm_apply, leftMaurerCartanEval_apply]

@[simp]
theorem leftInvariantForm_zero :
    leftInvariantForm (0 : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) = 0 :=
  (rfl)

@[simp]
theorem leftInvariantForm_add (a b : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantForm (a + b) = leftInvariantForm a + leftInvariantForm b :=
  (rfl)

@[simp]
theorem leftInvariantForm_smul (c : ℝ) (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantForm (c • a) = c • leftInvariantForm a :=
  (rfl)

@[simp]
theorem leftInvariantForm_neg (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantForm (-a) = -leftInvariantForm a :=
  (rfl)

@[simp]
theorem leftInvariantForm_sub (a b : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantForm (a - b) = leftInvariantForm a - leftInvariantForm b :=
  (rfl)

/-- At the identity, translating back to the identity is the identity. -/
private theorem mfderiv_one_inv_mul :
    mfderiv I I (fun x : G ↦ (1 : G)⁻¹ * x) 1 =
      ContinuousLinearMap.id ℝ (TangentSpace I (1 : G)) := by
  have h : (fun x : G ↦ (1 : G)⁻¹ * x) = id := funext fun x ↦ by simp
  rw [h, mfderiv_id]

/-- At the identity, the left-invariant form of `a` is `a`. -/
@[simp]
theorem leftInvariantForm_one (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantForm a 1 = a := by
  ext v
  rw [leftInvariantForm_apply, mfderiv_one_inv_mul]
  -- The identity map lands in `TangentSpace I (1⁻¹ * 1)`, which is only definitionally the Lie
  -- algebra, so `ContinuousLinearMap.id_apply` does not rewrite here and the step is `rfl`.
  rfl

/-- The left trivialization is injective: a left-invariant form is determined by its value at the
identity. -/
theorem leftInvariantForm_injective :
    Injective (leftInvariantForm : (GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) → RoughForm I G F k) :=
  fun a b h ↦ by
    simpa only [leftInvariantForm_one] using congrFun h 1

@[simp]
theorem leftInvariantForm_inj {a b : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F} :
    leftInvariantForm a = leftInvariantForm b ↔ a = b :=
  leftInvariantForm_injective.eq_iff

@[simp]
theorem leftInvariantForm_eq_zero_iff {a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F} :
    leftInvariantForm a = 0 ↔ a = 0 :=
  leftInvariantForm_injective.eq_iff' leftInvariantForm_zero

section Translation

variable [ContMDiffMul I 1 G]

/-- On left-invariant vector fields, the left-invariant form of `a` is constant, with value `a`
evaluated on their generators. -/
@[simp]
theorem leftInvariantForm_apply_mulInvariantVectorField
    (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) (w : Fin k → GroupLieAlgebra I G) (g : G) :
    leftInvariantForm a g (fun i ↦ mulInvariantVectorField (w i) g) = a w := by
  rw [leftInvariantForm_apply]
  exact congrArg a (funext fun i ↦ mfderiv_inv_mul_mulInvariantVectorField (w i) g)

/-- A left-invariant form vanishes nowhere unless its value at the identity is zero. -/
theorem leftInvariantForm_apply_ne_zero {a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F} (ha : a ≠ 0)
    (g : G) : leftInvariantForm a g ≠ 0 := by
  intro h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 ha
  apply hw
  rw [← leftInvariantForm_apply_mulInvariantVectorField a w g, h]
  simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- **Left invariance**: the left-invariant form of `a` is its own pullback along every left
translation. -/
@[simp]
theorem mpullback_mul_left_leftInvariantForm (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F)
    (h : G) : mpullback I I (h * ·) (leftInvariantForm a) = leftInvariantForm a := by
  funext g
  ext v
  rw [mpullback_apply, leftInvariantForm_apply, leftInvariantForm_apply]
  refine congrArg a (funext fun i ↦ ?_)
  -- Translating by `h` and then by `(h * g)⁻¹` is translating by `g⁻¹`.
  have hcomp : (fun x : G ↦ (h * g)⁻¹ * x) ∘ (h * ·) = (g⁻¹ * ·) := by
    funext x
    simp [mul_assoc]
  rw [← mfderiv_comp_apply_of_eq g mdifferentiableAt_mul_left mdifferentiableAt_mul_left rfl,
    hcomp]

omit [ContMDiffMul I 1 G] in
/-- A form invariant under all left translations is the left-invariant form of its value at the
identity. -/
theorem eq_leftInvariantForm_of_forall_mpullback_mul_left_eq {φ : RoughForm I G F k}
    (hφ : ∀ h : G, mpullback I I (h * ·) φ = φ) : φ = leftInvariantForm (φ 1) := by
  funext g
  ext v
  have h := congrArg (fun ψ : RoughForm I G F k ↦ ψ g v) (hφ g⁻¹)
  simp only [mpullback_apply] at h
  rw [← h, leftInvariantForm_apply]
  exact φ.apply_congr (inv_mul_cancel g) fun _ ↦ rfl

/-- **The image of the left trivialization**: a form is the left-invariant form of some
alternating map on the Lie algebra exactly when it is invariant under all left translations. -/
theorem exists_eq_leftInvariantForm_iff {φ : RoughForm I G F k} :
    (∃ a, φ = leftInvariantForm a) ↔ ∀ h : G, mpullback I I (h * ·) φ = φ := by
  refine ⟨?_, fun hφ ↦ ⟨_, eq_leftInvariantForm_of_forall_mpullback_mul_left_eq hφ⟩⟩
  rintro ⟨a, rfl⟩ h
  exact mpullback_mul_left_leftInvariantForm a h

end Translation

section Homomorphism

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [ContMDiffMul I' 1 G']
  [ContMDiffMul I 1 G] {n : WithTop ℕ∞}

/-- **Naturality of the left trivialization**: the pullback of a left-invariant form along a
differentiable homomorphism is the left-invariant form of the pullback of its value at the
identity along the differential of the homomorphism. -/
@[simp]
theorem mpullback_leftInvariantForm (φ : ContMDiffMonoidMorphism I I' n G G') (hn : n ≠ 0)
    (a : GroupLieAlgebra I' G' [⋀^Fin k]→L[ℝ] F) :
    mpullback I I' φ (leftInvariantForm a) =
      leftInvariantForm (a.compContinuousLinearMap (φ.toMonoidHom.groupLieAlgebraMap I I')) := by
  have hφ : MDifferentiable I I' φ := φ.contMDiff_toFun.mdifferentiable hn
  funext g
  -- Both sides differentiate `x ↦ φ(g)⁻¹ * φ(x) = φ(g⁻¹ * x)` at `g`.
  have hcomp : (fun y : G' ↦ (φ g)⁻¹ * y) ∘ φ = φ ∘ (g⁻¹ * ·) := by
    funext x
    simp [map_mul, map_inv]
  have key (u : TangentSpace I g) : mfderiv I' I' ((φ g)⁻¹ * ·) (φ g) (mfderiv I I' φ g u) =
      φ.toMonoidHom.groupLieAlgebraMap I I' (mfderiv I I (g⁻¹ * ·) g u) := by
    rw [← mfderiv_comp_apply_of_eq g mdifferentiableAt_mul_left (hφ g) rfl, hcomp,
      mfderiv_comp_apply_of_eq g (hφ _) mdifferentiableAt_mul_left (inv_mul_cancel g)]
    exact (MonoidHom.groupLieAlgebraMap_apply _ _ _).symm
  ext v
  rw [mpullback_apply, leftInvariantForm_apply, leftInvariantForm_apply]
  exact congrArg a (funext fun i ↦ key (v i))

end Homomorphism

section Smooth

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]

/-- **Smoothness of left-invariant forms**: on a finite-dimensional smooth Lie group, the
left-invariant form of an alternating map on the Lie algebra is smooth. -/
theorem isSmoothForm_leftInvariantForm (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    IsSmoothForm I ∞ (leftInvariantForm a) := by
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
  intro x v
  set e := trivializationAt E (TangentSpace I) x
  -- The frame fields of the trivialization are smooth near `x`, and the form evaluated on them is
  -- `a` evaluated on their left Maurer-Cartan forms.
  have hV (i : Fin k) : CMDiffAt ∞ (T% (fun y : G ↦ e.symmL ℝ y (v i))) x :=
    (e.contMDiffAt_symmL (FiberBundle.mem_baseSet_trivializationAt' x)).clm_bundle_apply (by
      rw [contMDiffAt_section_iff]
      exact contMDiffAt_const)
  have hMC : ContMDiffAt I 𝓘(ℝ, Fin k → E) ∞ (fun y ↦ fun i ↦
      leftMaurerCartanEval (E := E) (fun y : G ↦ e.symmL ℝ y (v i)) y) x :=
    contMDiffAt_pi_module_iff.2 fun i ↦ ContMDiffAt.leftMaurerCartanEval (N := ∞) (by simp) (hV i)
  simp only [leftMaurerCartanEval_apply] at hMC
  -- The Lie algebra is the model space, on which `a` is a smooth multilinear map.
  let a' : E [⋀^Fin k]→L[ℝ] F := a
  exact (a'.toContinuousMultilinearMap.contDiff.contMDiff.contMDiffAt).comp x hMC

/-- The left-invariant form of `a`, as a smooth form. -/
def leftInvariantSmoothForm (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) : SmoothForm I G F k :=
  ⟨leftInvariantForm a, (isSmoothForm_leftInvariantForm a).mem_smoothBundleForms⟩

@[simp]
theorem coe_leftInvariantSmoothForm (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    (leftInvariantSmoothForm a).val = leftInvariantForm a :=
  (rfl)

@[simp]
theorem leftInvariantSmoothForm_zero :
    leftInvariantSmoothForm (0 : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) = 0 :=
  (rfl)

@[simp]
theorem leftInvariantSmoothForm_add (a b : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantSmoothForm (a + b) = leftInvariantSmoothForm a + leftInvariantSmoothForm b :=
  (rfl)

@[simp]
theorem leftInvariantSmoothForm_smul (c : ℝ) (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantSmoothForm (c • a) = c • leftInvariantSmoothForm a :=
  (rfl)

@[simp]
theorem leftInvariantSmoothForm_neg (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantSmoothForm (-a) = -leftInvariantSmoothForm a :=
  (rfl)

@[simp]
theorem leftInvariantSmoothForm_sub (a b : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    leftInvariantSmoothForm (a - b) = leftInvariantSmoothForm a - leftInvariantSmoothForm b :=
  (rfl)

/-- The smooth left trivialization is injective. -/
theorem leftInvariantSmoothForm_injective :
    Injective (leftInvariantSmoothForm :
      (GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) → SmoothForm I G F k) :=
  fun _ _ h ↦ leftInvariantForm_injective (congrArg Subtype.val h)

@[simp]
theorem leftInvariantSmoothForm_inj {a b : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F} :
    leftInvariantSmoothForm a = leftInvariantSmoothForm b ↔ a = b :=
  leftInvariantSmoothForm_injective.eq_iff

@[simp]
theorem leftInvariantSmoothForm_eq_zero_iff {a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F} :
    leftInvariantSmoothForm a = 0 ↔ a = 0 :=
  leftInvariantSmoothForm_injective.eq_iff' leftInvariantSmoothForm_zero

/-- **Left invariance** of the smooth left-invariant form of `a`: it is its own pullback along
every left translation. -/
@[simp]
theorem SmoothForm.mpullback_mul_left_leftInvariantSmoothForm
    (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) (h : G) :
    SmoothForm.mpullback (h * ·) contMDiff_mul_left (leftInvariantSmoothForm a) =
      leftInvariantSmoothForm a :=
  Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans (mpullback_mul_left_leftInvariantForm a h))

/-- **A nonzero left-invariant top form has positive integral** over a compact Lie group of
positive dimension, for the orientation it defines. In particular its integral is not zero. -/
theorem integralTopForm_leftInvariantForm_pos [CompactSpace G] [NeZero k]
    (hk : Module.finrank ℝ E = k) {a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] ℝ} (ha : a ≠ 0) :
    0 < integralTopForm (Manifold.Orientation.ofTopForm hk (leftInvariantForm a)
      ((isSmoothForm_leftInvariantForm a).of_le zero_le) (leftInvariantForm_apply_ne_zero ha))
      (leftInvariantForm a) :=
  integralTopForm_ofTopForm_pos hk _ _

end Smooth

section ExteriorDerivative

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G]
  [LieRingModule (GroupLieAlgebra I G) F] [LieModule ℝ (GroupLieAlgebra I G) F]
  [LieModule.IsTrivial (GroupLieAlgebra I G) F]

/-- The exterior derivative of a left-invariant form of positive degree. -/
private theorem mextDeriv_leftInvariantForm_apply_succ {n : ℕ}
    (a : GroupLieAlgebra I G [⋀^Fin (n + 1)]→L[ℝ] F) (g : G)
    (v : Fin (n + 2) → TangentSpace I g) :
    mextDeriv (leftInvariantForm a) g v =
      TauCeti.LieModule.Cohomology.d ℝ (GroupLieAlgebra I G) F (n + 1) a.toAlternatingMap
        fun i ↦ mfderiv I I (g⁻¹ * ·) g (v i) := by
  set w : Fin (n + 2) → GroupLieAlgebra I G := fun i ↦ mfderiv I I (g⁻¹ * ·) g (v i)
  -- Evaluate on the left-invariant vector fields generated by the translates `w` of `v`.
  let V : Fin (n + 2) → Π y : G, TangentSpace I y := fun i ↦ mulInvariantVectorField (w i)
  have hVg : (V · g) = v := funext fun i ↦ mulInvariantVectorField_mfderiv_inv_mul (v i)
  have hφ := SmoothForm.mdifferentiableAt (leftInvariantSmoothForm (I := I) a) g
  have h := mextDeriv_apply_vectorField (φ := leftInvariantForm a) (V := V) hφ
    fun i ↦ mdifferentiableAt_mulInvariantVectorField (w i)
  rw [hVg] at h
  -- On left-invariant vector fields the form is constant, so the derivative terms vanish.
  have hconst (i : Fin (n + 2)) :
      (fun y ↦ leftInvariantForm a y (i.removeNth (V · y))) = fun _ ↦ a (i.removeNth w) :=
    funext fun y ↦ leftInvariantForm_apply_mulInvariantVectorField a (i.removeNth w) y
  -- The bracket of left-invariant vector fields is the left-invariant field of the bracket.
  have hbracket (i j : Fin (n + 2)) :
      mlieBracket I (V i) (V j) g = mulInvariantVectorField ⁅w i, w j⁆ g := by
    rw [GroupLieAlgebra.bracket_def, mulInvariantVector_mlieBracket]
  have hpair (i : Fin (n + 1)) (j : Fin (n + 1)) :
      leftInvariantForm a g (Matrix.vecCons (mlieBracket I (V i.castSucc) (V j.succ) g)
        (j.removeNth (i.castSucc.removeNth v))) =
        a (Matrix.vecCons ⁅w i.castSucc, w j.succ⁆ (j.removeNth (i.castSucc.removeNth w))) := by
    rw [hbracket, ← hVg, ← leftInvariantForm_apply_mulInvariantVectorField a]
    congr 1
    funext l
    cases l using Fin.cases <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, V, w,
      Fin.removeNth]
  rw [h, TauCeti.LieModule.Cohomology.d_succ_apply]
  simp only [hconst, mvfderiv_const, zero_apply, smul_zero,
    Finset.sum_const_zero, zero_sub, hpair, trivial_lie_zero, zero_add]
  -- The two bracket sums agree, with the sign `(-1)^(i + j + 1) = -(-1)^(i + j)`.
  simp only [← Finset.sum_neg_distrib, pow_succ, mul_neg_one, neg_smul,
    ContinuousAlternatingMap.coe_toAlternatingMap]

/-- **The exterior derivative of a left-invariant form is the Chevalley–Eilenberg differential**:
for coefficients on which the Lie algebra acts trivially, `d j(a) = j(d a)`, that is, `d j(a)`
evaluated at `g` is the Chevalley–Eilenberg differential of `a` evaluated on the tangent vectors
translated back to the identity. -/
theorem mextDeriv_leftInvariantForm_apply (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) (g : G)
    (v : Fin (k + 1) → TangentSpace I g) :
    mextDeriv (leftInvariantForm a) g v =
      TauCeti.LieModule.Cohomology.d ℝ (GroupLieAlgebra I G) F k a.toAlternatingMap
        fun i ↦ mfderiv I I (g⁻¹ * ·) g (v i) := by
  cases k with
  | zero =>
    -- In degree zero the form is a constant function, and the differential is an action term.
    have hconst : leftInvariantForm a = RoughForm.ofFunction I fun _ ↦ a 0 := by
      rw [RoughForm.eq_ofFunction (leftInvariantForm a)]
      congr 1
      funext y
      exact congrArg a (Subsingleton.elim _ _)
    have hd := TauCeti.LieModule.Cohomology.d_zero_apply (R := ℝ) (L := GroupLieAlgebra I G)
      (M := F) a.toAlternatingMap fun i ↦ mfderiv I I (g⁻¹ * ·) g (v i)
    rw [hconst, mextDeriv_ofFunction, mvfderiv_const, hd,
      ContinuousAlternatingMap.ofSubsingleton_apply_apply, zero_apply]
    exact (trivial_lie_zero (GroupLieAlgebra I G) F (mfderiv I I (g⁻¹ * ·) g (v 0)) _).symm
  | succ n => exact mextDeriv_leftInvariantForm_apply_succ a g v

/-- **A left-invariant form is closed exactly when its value at the identity is a
Chevalley–Eilenberg cocycle**, for coefficients on which the Lie algebra acts trivially. -/
theorem mextDeriv_leftInvariantForm_eq_zero_iff (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    mextDeriv (leftInvariantForm a) = 0 ↔
      TauCeti.LieModule.Cohomology.d ℝ (GroupLieAlgebra I G) F k a.toAlternatingMap = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- Read the derivative at the identity, where translating back is the identity.
    ext w
    have hw := mextDeriv_leftInvariantForm_apply a 1 w
    rw [h, mfderiv_one_inv_mul] at hw
    exact hw.symm
  · funext g
    ext v
    rw [mextDeriv_leftInvariantForm_apply, h]
    -- Both sides are zero; the translated vectors lie in `TangentSpace I (g⁻¹ * g)`, which is only
    -- definitionally the Lie algebra, so the zero-application lemmas do not rewrite and the step
    -- is `rfl`.
    rfl

/-- The smooth left-invariant form of `a` is closed exactly when `a` is a Chevalley–Eilenberg
cocycle, for coefficients on which the Lie algebra acts trivially. -/
theorem isClosed_leftInvariantSmoothForm_iff (a : GroupLieAlgebra I G [⋀^Fin k]→L[ℝ] F) :
    (leftInvariantSmoothForm a).IsClosed ↔
      TauCeti.LieModule.Cohomology.d ℝ (GroupLieAlgebra I G) F k a.toAlternatingMap = 0 := by
  rw [SmoothForm.isClosed_def, coe_leftInvariantSmoothForm,
    mextDeriv_leftInvariantForm_eq_zero_iff]

end ExteriorDerivative

end TauCeti
