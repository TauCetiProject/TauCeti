/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Homogeneous
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.Riemannian.Section

/-!
# Left-invariant Riemannian metrics on Lie groups

A positive-definite symmetric bilinear form `b` on the Lie algebra `T₁G` of a finite-dimensional
Lie group `G` extends to a unique Riemannian metric for which the left-invariant vector fields
`X_a = mulInvariantVectorField a` have constant inner products `⟪X_a, X_c⟫ = b(a, c)`: at `x`,
evaluate `b` on the translates of two tangent vectors back to the identity by `L_{x⁻¹}`. This
metric is smooth, and every left translation preserves it. If `b` is moreover invariant under the
adjoint action, `b(Ad_g a, Ad_g c) = b(a, c)`, then right translations preserve it too, so it is
bi-invariant.

Conversely, for any Riemannian metric on `G` in which the left-invariant fields have constant inner
products, left multiplication is a homomorphism from `G` to the isometry group. That group then
acts transitively, so `G` is a homogeneous Riemannian manifold. In finite dimensions a homogeneous
Riemannian manifold is complete
(`TauCeti.completeSpace_of_isPretransitive_isom_of_finiteDimensional`), hence every left-invariant
metric on a finite-dimensional Lie group is complete for its Riemannian distance. No compactness
or connectedness of `G` is needed.

The hypothesis that left-invariant fields have constant inner products is the one under which
`TauCeti.Geometry.Manifold.Riemannian.LieGroup.BiInvariant` computes the Levi-Civita connection and
curvature of a left-invariant metric; `inner_mulInvariantVectorField_leftInvariantMetric` supplies
it for the metric constructed here.

## Main definitions

* `TauCeti.leftInvariantBilinearForm b`: the left-invariant extension of a bilinear form `b` on
  `T₁G`.
* `TauCeti.leftInvariantMetric`: the left-invariant Riemannian metric determined by an inner
  product `b` on `T₁G`.
* `TauCeti.mulLeftIsom`: left multiplication, as a homomorphism from `G` to the isometry group of
  a left-invariant metric.

## Main results

* `TauCeti.contMDiff_leftInvariantBilinearForm`: the left-invariant extension of `b` is a `C^m`
  section on a `C^n` Lie group when `m + 1 ≤ n`.
* `TauCeti.leftInvariantMetric_inner_mulInvariantVectorField`: `⟪X_a, X_c⟫ = b(a, c)` everywhere,
  and `TauCeti.eq_leftInvariantMetric`: this property characterizes the metric.
* `TauCeti.leftInvariantMetric_inner_mfderiv_mul_left`: left translations are isometries.
* `TauCeti.leftInvariantMetric_inner_mfderiv_mul_right`: for an `Ad`-invariant `b`, right
  translations are isometries too.
* `TauCeti.isPretransitive_isom_of_inner_mulInvariantVectorField`: a Lie group with a
  left-invariant metric is homogeneous.
* `TauCeti.completeSpace_of_inner_mulInvariantVectorField`,
  `TauCeti.completeSpace_ofRiemannianMetric_of_inner_mulInvariantVectorField` and
  `TauCeti.completeSpace_leftInvariantMetric`: left-invariant metrics on finite-dimensional Lie
  groups are complete.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 3 (invariant metrics on Lie groups) and Chapter 6 (homogeneous manifolds are complete).
* J. Milnor, *Curvatures of left invariant metrics on Lie groups*, Advances in Math. 21 (1976),
  293–329.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section LeftTranslation

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [RiemannianBundle (fun x : G ↦ TangentSpace I x)]

/-- If the left-invariant vector fields have constant inner products, `⟪X_a, X_c⟫ = ⟪a, c⟫` at
every point, then every left translation preserves the inner product of tangent vectors. -/
theorem inner_mfderiv_mul_left_of_inner_mulInvariantVectorField [ContMDiffMul I 1 G]
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c)
    (g x : G) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I I (g * ·) x v) (mfderiv I I (g * ·) x w) = inner ℝ v w := by
  obtain ⟨a, rfl⟩ := exists_mulInvariantVectorField_eq v
  obtain ⟨c, rfl⟩ := exists_mulInvariantVectorField_eq w
  rw [mfderiv_mul_left_mulInvariantVectorField, mfderiv_mul_left_mulInvariantVectorField, hL, hL]

end LeftTranslation

section Construction

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- The left-invariant extension of a bilinear form `b` on the Lie algebra `T₁G`: at `x`, it
evaluates `b` on the translates of two tangent vectors back to the identity by `L_{x⁻¹}`. -/
def leftInvariantBilinearForm
    (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ) (x : G) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (mfderiv I I (x⁻¹ * ·) x)).comp
    (b.comp (mfderiv I I (x⁻¹ * ·) x))

/-- The left-invariant extension of `b` evaluates `b` on the translates to the identity. -/
@[simp]
theorem leftInvariantBilinearForm_apply
    (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ) (x : G)
    (v w : TangentSpace I x) :
    leftInvariantBilinearForm b x v w =
      b (mfderiv I I (x⁻¹ * ·) x v) (mfderiv I I (x⁻¹ * ·) x w) :=
  (rfl)

/-- The left-invariant extension of a bilinear form on the Lie algebra of a `C^n` Lie group is a
`C^m` section of the bundle of bilinear forms on the tangent bundle, when `m + 1 ≤ n`. -/
theorem contMDiff_leftInvariantBilinearForm [IsManifold I 1 G] {m n : ℕ∞ω} [LieGroup I n G]
    (hmn : m + 1 ≤ n)
    (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : G ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (leftInvariantBilinearForm b x)) := by
  -- This is the pullback of the constant form `b` over `x⁻¹ * x = 1` along the derivative of
  -- `L_{x⁻¹}` at `x`, which depends smoothly on `x` in tangent coordinates.
  intro x₀
  refine contMDiffAt_bilinearForm_pullback_of_inTangentCoordinates (f := fun x : G ↦ x⁻¹ * x)
    (b := fun _ ↦ b) ?_ ?_
  · have hconst : (fun x : G ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : G ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (x⁻¹ * x) b) =
        fun _ ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : G ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) 1 b := by
      funext x
      rw [inv_mul_cancel]
    rw [hconst]
    exact contMDiffAt_const
  · exact ContMDiffAt.mfderiv (fun x y : G ↦ x⁻¹ * y) (fun x ↦ x)
      (((contMDiff_inv I n).comp contMDiff_fst).mul contMDiff_snd).contMDiffAt
      contMDiffAt_id hmn

/-- On a `C^n` Lie group with `m + 1 ≤ n`, multiplication is `C^1`. -/
private theorem contMDiffMul_one_of_add_one_le {m n : ℕ∞ω} [LieGroup I n G]
    (hmn : m + 1 ≤ n) : ContMDiffMul I 1 G :=
  ContMDiffMul.of_le (le_add_self.trans hmn)

variable [FiniteDimensional ℝ E] [IsManifold I 1 G] {m n : ℕ∞ω} [LieGroup I n G]

/-- The **left-invariant Riemannian metric** on a Lie group determined by an inner product `b` on
its Lie algebra `T₁G`: the inner product of two tangent vectors at `x` is `b` evaluated on their
translates to the identity by `L_{x⁻¹}`. It is `C^m` on a `C^n` Lie group when `m + 1 ≤ n`. -/
def leftInvariantMetric (hmn : m + 1 ≤ n)
    (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ)
    (hsymm : ∀ v w, b v w = b w v) (hpos : ∀ v, v ≠ 0 → 0 < b v v) :
    ContMDiffRiemannianMetric I m E (fun x : G ↦ TangentSpace I x) :=
  have := contMDiffMul_one_of_add_one_le (I := I) (G := G) hmn
  ContMDiffRiemannianMetric.ofPositiveDefiniteSection
    ⟨leftInvariantBilinearForm b, contMDiff_leftInvariantBilinearForm hmn b⟩
    ((TauCeti.Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(TauCeti.Manifold.mem_symmetricBilinearSections _).2 fun _ _ _ ↦ hsymm _ _,
        fun x _ hv ↦ hpos _ ((map_ne_zero_iff _ (mfderiv_inv_mul_injective x)).2 hv)⟩)

variable (hmn : m + 1 ≤ n) (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ)
  (hsymm : ∀ v w, b v w = b w v) (hpos : ∀ v, v ≠ 0 → 0 < b v v)

/-- The left-invariant metric evaluates `b` on the translates to the identity. -/
@[simp low]
theorem leftInvariantMetric_inner (x : G) (v w : TangentSpace I x) :
    (leftInvariantMetric hmn b hsymm hpos).inner x v w =
      b (mfderiv I I (x⁻¹ * ·) x v) (mfderiv I I (x⁻¹ * ·) x w) :=
  ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner _ _ x v w

/-- At the identity, the left-invariant metric is `b`. -/
@[simp]
theorem leftInvariantMetric_inner_one :
    (leftInvariantMetric hmn b hsymm hpos).inner 1 = b := by
  ext v w
  rw [leftInvariantMetric_inner, show ((1 : G)⁻¹ * ·) = id by funext y; simp, mfderiv_id]
  rfl

/-- Left-invariant vector fields have constant inner products for the left-invariant metric:
`⟪X_a, X_c⟫ = b(a, c)` at every point. -/
@[simp]
theorem leftInvariantMetric_inner_mulInvariantVectorField (x : G)
    (a c : TangentSpace I (1 : G)) :
    (leftInvariantMetric hmn b hsymm hpos).inner x (mulInvariantVectorField a x)
        (mulInvariantVectorField c x) = b a c := by
  have := contMDiffMul_one_of_add_one_le (I := I) (G := G) hmn
  rw [leftInvariantMetric_inner, mfderiv_inv_mul_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField]

/-- For the Riemannian bundle structure given by the left-invariant metric of `b`, the
left-invariant vector fields have the constant inner products `⟪X_a, X_c⟫ = ⟪a, c⟫`: this is the
hypothesis of `TauCeti.mulLeftIsom` and of the completeness theorems below. -/
theorem inner_mulInvariantVectorField_leftInvariantMetric (x : G)
    (a c : TangentSpace I (1 : G)) :
    letI : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
      ⟨(leftInvariantMetric hmn b hsymm hpos).toRiemannianMetric⟩
    inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c :=
  -- The inner product of the installed bundle is `(leftInvariantMetric hmn b hsymm hpos).inner`
  -- by definition of the instance, at every point including the identity.
  (leftInvariantMetric_inner_mulInvariantVectorField hmn b hsymm hpos x a c).trans
    (DFunLike.congr_fun (DFunLike.congr_fun (leftInvariantMetric_inner_one hmn b hsymm hpos) a)
      c).symm

/-- Left translations preserve the left-invariant metric. -/
theorem leftInvariantMetric_inner_mfderiv_mul_left (g x : G) (v w : TangentSpace I x) :
    (leftInvariantMetric hmn b hsymm hpos).inner (g * x) (mfderiv I I (g * ·) x v)
        (mfderiv I I (g * ·) x w) =
      (leftInvariantMetric hmn b hsymm hpos).inner x v w := by
  have := contMDiffMul_one_of_add_one_le (I := I) (G := G) hmn
  let : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
    ⟨(leftInvariantMetric hmn b hsymm hpos).toRiemannianMetric⟩
  -- The inner product of the installed bundle is `(leftInvariantMetric hmn b hsymm hpos).inner`
  -- by definition of the instance.
  exact inner_mfderiv_mul_left_of_inner_mulInvariantVectorField
    (inner_mulInvariantVectorField_leftInvariantMetric hmn b hsymm hpos) g x v w

/-- A Riemannian metric in which the left-invariant vector fields have the constant inner products
`⟪X_a, X_c⟫ = b(a, c)` is the left-invariant metric of `b`. -/
theorem eq_leftInvariantMetric (g : ContMDiffRiemannianMetric I m E (fun x : G ↦ TangentSpace I x))
    (hg : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      g.inner x (mulInvariantVectorField a x) (mulInvariantVectorField c x) = b a c) :
    g = leftInvariantMetric hmn b hsymm hpos := by
  have := contMDiffMul_one_of_add_one_le (I := I) (G := G) hmn
  ext x v w
  obtain ⟨a, rfl⟩ := exists_mulInvariantVectorField_eq v
  obtain ⟨c, rfl⟩ := exists_mulInvariantVectorField_eq w
  rw [hg, leftInvariantMetric_inner_mulInvariantVectorField]

end Construction

section BiInvariant

-- The instance `LieGroup I 1 G`, implied by `hmn`, is needed to state the adjoint action.
variable [FiniteDimensional ℝ E] {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {m n : ℕ∞ω} [LieGroup I n G] [LieGroup I 1 G] (hmn : m + 1 ≤ n)
  (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ)
  (hsymm : ∀ v w, b v w = b w v) (hpos : ∀ v, v ≠ 0 → 0 < b v v)

/-- If `b` is invariant under the adjoint action, `b(Ad_g a, Ad_g c) = b(a, c)`, then right
translations also preserve the left-invariant metric of `b`, which is therefore bi-invariant. -/
theorem leftInvariantMetric_inner_mfderiv_mul_right
    (had : ∀ (g : G) (a c : TangentSpace I (1 : G)),
      b (Lie.adjointContinuousLinearMap g a) (Lie.adjointContinuousLinearMap g c) = b a c)
    (g x : G) (v w : TangentSpace I x) :
    (leftInvariantMetric hmn b hsymm hpos).inner (x * g) (mfderiv I I (· * g) x v)
        (mfderiv I I (· * g) x w) =
      (leftInvariantMetric hmn b hsymm hpos).inner x v w := by
  obtain ⟨a, rfl⟩ := exists_mulInvariantVectorField_eq v
  obtain ⟨c, rfl⟩ := exists_mulInvariantVectorField_eq w
  rw [Lie.mfderiv_mul_right_mulInvariantVectorField, Lie.mfderiv_mul_right_mulInvariantVectorField,
    leftInvariantMetric_inner_mulInvariantVectorField,
    leftInvariantMetric_inner_mulInvariantVectorField, had]

end BiInvariant

section Isometry

variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [RiemannianBundle (fun x : G ↦ TangentSpace I x)]

variable [LieGroup I ∞ G]

/-- Left multiplication by `g`, as an isometry of a left-invariant metric. -/
private def mulLeftIsometry
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c)
    (g : G) : Isom I G where
  toFun := (g * ·)
  invFun := (g⁻¹ * ·)
  left_inv := inv_mul_cancel_left g
  right_inv := mul_inv_cancel_left g
  contMDiff_toFun := contMDiff_mul_left
  contMDiff_invFun := contMDiff_mul_left
  inner_mfderiv' :=
    have := contMDiffMul_one_of_add_one_le (I := I) (G := G) (m := 0) (n := ∞) (by simp)
    inner_mfderiv_mul_left_of_inner_mulInvariantVectorField hL g

/-- Left multiplication, as a homomorphism from a Lie group to the isometry group of a
left-invariant Riemannian metric on it. -/
def mulLeftIsom
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c) :
    G →* Isom I G where
  toFun := mulLeftIsometry hL
  map_one' := RiemannianIsometry.ext fun x ↦ by
    rw [RiemannianIsometry.one_apply]
    exact one_mul x
  map_mul' g g' := RiemannianIsometry.ext fun x ↦ by
    rw [RiemannianIsometry.mul_apply]
    exact mul_assoc g g' x

/-- The isometry `mulLeftIsom hL g` is left multiplication by `g`. -/
@[simp]
theorem mulLeftIsom_apply
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c)
    (g x : G) : mulLeftIsom hL g x = g * x :=
  (rfl)

/-- A Lie group with a left-invariant Riemannian metric is homogeneous: its isometry group acts
transitively, already through left multiplications. -/
theorem isPretransitive_isom_of_inner_mulInvariantVectorField
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c) :
    MulAction.IsPretransitive (Isom I G) G :=
  .of_smul_eq (mulLeftIsom hL) fun {_ _} ↦ by
    rw [RiemannianIsometry.smul_def, mulLeftIsom_apply, smul_eq_mul]

end Isometry

section Completeness

variable [FiniteDimensional ℝ E]

/-- **Left-invariant metrics are complete.** A finite-dimensional Lie group with a left-invariant
Riemannian metric is complete for its Riemannian distance. -/
theorem completeSpace_of_inner_mulInvariantVectorField
    {G : Type*} [PseudoEMetricSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
    [RiemannianBundle (fun x : G ↦ TangentSpace I x)] [IsRiemannianManifold I G]
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c) :
    CompleteSpace G :=
  have := isPretransitive_isom_of_inner_mulInvariantVectorField hL
  completeSpace_of_isPretransitive_isom_of_finiteDimensional (I := I) G

variable {G : Type*} [TopologicalSpace G] [T2Space G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- A finite-dimensional Hausdorff Lie group with a continuous left-invariant Riemannian metric is
complete for the distance that this metric induces. A Lie group is a topological group, hence
regular, which is what `EMetricSpace.ofRiemannianMetric` needs. -/
theorem completeSpace_ofRiemannianMetric_of_inner_mulInvariantVectorField
    [RiemannianBundle (fun x : G ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : G ↦ TangentSpace I x)]
    (hL : ∀ (x : G) (a c : TangentSpace I (1 : G)),
      inner ℝ (mulInvariantVectorField a x) (mulInvariantVectorField c x) = inner ℝ a c) :
    letI : EMetricSpace G :=
      haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
      EMetricSpace.ofRiemannianMetric I G
    CompleteSpace G :=
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := isPretransitive_isom_of_inner_mulInvariantVectorField hL
  completeSpace_ofRiemannianMetric_of_isPretransitive_isom (I := I) G

/-- The left-invariant metric of an inner product `b` on the Lie algebra of a finite-dimensional
Hausdorff Lie group is complete for the distance that it induces. -/
theorem completeSpace_leftInvariantMetric {m : ℕ∞ω} (hm : m + 1 ≤ ∞)
    (b : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) →L[ℝ] ℝ)
    (hsymm : ∀ v w, b v w = b w v) (hpos : ∀ v, v ≠ 0 → 0 < b v v) :
    letI : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
      ⟨(leftInvariantMetric hm b hsymm hpos).toRiemannianMetric⟩
    haveI : IsContinuousRiemannianBundle E (fun x : G ↦ TangentSpace I x) :=
      Bundle.instIsContinuousRiemannianBundle
        (leftInvariantMetric hm b hsymm hpos).toContinuousRiemannianMetric
    letI : EMetricSpace G :=
      haveI := topologicalGroup_of_lieGroup I ∞ (G := G)
      EMetricSpace.ofRiemannianMetric I G
    CompleteSpace G :=
  letI : RiemannianBundle (fun x : G ↦ TangentSpace I x) :=
    ⟨(leftInvariantMetric hm b hsymm hpos).toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle E (fun x : G ↦ TangentSpace I x) :=
    Bundle.instIsContinuousRiemannianBundle
      (leftInvariantMetric hm b hsymm hpos).toContinuousRiemannianMetric
  completeSpace_ofRiemannianMetric_of_inner_mulInvariantVectorField
    (inner_mulInvariantVectorField_leftInvariantMetric hm b hsymm hpos)

end Completeness

end TauCeti
