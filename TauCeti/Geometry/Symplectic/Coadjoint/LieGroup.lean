/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Geometry.Lie.InvariantVectorField.Distribution
public import TauCeti.Geometry.Lie.LeftInvariantForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap
public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Pullback

/-!
# The Kirillov form of a coadjoint vector on its Lie group

Let `G` be a real Lie group with finite-dimensional model, Lie algebra `𝔤 = GroupLieAlgebra I G`,
and fix `ν ∈ 𝔤*`. The coadjoint orbit through `ν` is the image of the orbit map
`g ↦ Ad*_g ν`, and its Kirillov–Kostant–Souriau form `ω_ν(ξ_O, η_O) = ν ⁅ξ, η⁆` pulls back
along this map to a two-form on `G` itself. This file constructs that two-form directly on `G`,
together with the properties needed to descend it to `G ⧸ G_ν`, without a manifold structure on
the orbit.

* `Module.Dual.leftInvariantCovector ν : G → T*G` is the section `g ↦ g • ν` of the cotangent
  bundle obtained by moving the covector `ν` at the identity with the cotangent lift of left
  multiplication. Its value at `g` is `ν ∘ d(L_{g⁻¹})_g`.
* `Module.Dual.leftInvariantForm ν` is the corresponding smooth one-form `α_ν`, the pullback of
  the Liouville form along this section. It is the left-invariant one-form with value `ν` at the
  identity: `α_ν(X^L_ξ) = ν ξ` for the left-invariant vector field `X^L_ξ` of `ξ`.
* `Module.Dual.leftInvariantKirillovForm ν` is the two-form `σ_ν = -dα_ν`, which is also the
  pullback of the canonical symplectic form `ω = -dλ` of `T*G` along the section.

By the invariant formula for the exterior derivative and the bracket of left-invariant vector
fields, `σ_ν(X^L_ξ, X^L_η) = ν ⁅ξ, η⁆` everywhere. So `σ_ν` is the left-invariant extension of the
Kirillov form `ν ⁅ξ, η⁆` of `ν` (`Module.Dual.kirillovForm`), and the properties of the form on
the coadjoint orbit appear on `G` as follows.

* **Closedness.** `σ_ν` is exact, hence closed. On the orbit this is the closedness of the KKS
  form, since pullback along a surjective submersion detects closedness; the Jacobi identity is
  built into the exterior derivative of `α_ν`.
* **Kernel.** The kernel of `σ_ν` at `g` is the left translate `d(L_g)(𝔤_ν)` of the coadjoint
  stabilizer `𝔤_ν` (`Module.Dual.ker_bilinFormAt_leftInvariantKirillovForm`), which is the
  tangent space at `g` of the coset `g G_ν`, the vertical space of `G → G ⧸ G_ν`.
* **Invariance.** Left translations preserve `σ_ν`, and right translation by `h` carries
  `σ_ν` to `σ_{Ad*_h ν}`; in particular right translations by elements of the stabilizer `G_ν`
  preserve `σ_ν`.
* **Moment map.** For the action of `G` on itself by left multiplication, the orbit map
  `g ↦ Ad*_g ν` is a coadjoint-equivariant moment map of `σ_ν`
  (`Module.Dual.isEquivariantMomentMap_leftInvariantKirillovForm`). It is the composite of the
  section with the cotangent moment map of the lifted action; on the orbit it is the statement
  that the inclusion of the orbit into `𝔤*` is a moment map for the KKS form.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Chapter 14 (the KKS form and its pullback to the group).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.
-/

public section

open Bundle TauCeti TauCeti.Lie
open scoped Manifold ContDiff

noncomputable section

namespace Module.Dual

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  (ν : Module.Dual ℝ (GroupLieAlgebra I G))

/-- The covector `ν` at the identity of `G`. -/
private def covectorAtOne : CotangentBundle I G :=
  TotalSpace.mk' (E →L[ℝ] ℝ) (1 : G) (LinearMap.toContinuousLinearMap (show E →ₗ[ℝ] ℝ from ν))

omit [LieGroup I ∞ G] in
@[simp]
private theorem proj_covectorAtOne : (covectorAtOne ν).proj = 1 :=
  rfl

omit [LieGroup I ∞ G] in
-- The covector at the identity is `ν` read as a continuous functional on the model space, which
-- is definitional because `GroupLieAlgebra I G` is an abbreviation for the tangent space at `1`.
private theorem covectorAtOne_snd_apply (v : TangentSpace I (1 : G)) :
    (covectorAtOne ν).snd v = ν v :=
  rfl

/-! ### The left-invariant covector field -/

/-- The **left-invariant covector field** of `ν ∈ 𝔤*`: the section of the cotangent bundle of `G`
whose value at `g` is the image `g • ν` of the covector `ν` at the identity under the cotangent
lift of left multiplication, the covector `ν ∘ d(L_{g⁻¹})_g` at `g`. -/
def leftInvariantCovector (g : G) : CotangentBundle I G :=
  g • covectorAtOne ν

/-- The left-invariant covector field is a section of the cotangent bundle. -/
@[simp]
theorem proj_leftInvariantCovector (g : G) : (ν.leftInvariantCovector g).proj = g := by
  rw [leftInvariantCovector, CotangentBundle.proj_smul, smul_eq_mul]
  exact mul_one g

/-- The value at `g` of the left-invariant covector field of `ν` is `ν ∘ d(L_{g⁻¹})_g`. -/
theorem leftInvariantCovector_snd_apply (g : G) (v : TangentSpace I g) :
    (ν.leftInvariantCovector g).snd v = ν (mfderiv I I (g⁻¹ * ·) g v) := by
  have h := CotangentBundle.smul_snd_apply g (covectorAtOne ν) v
  simp only [smul_eq_mul] at h
  rw [leftInvariantCovector, h, proj_covectorAtOne, mul_one]
  exact covectorAtOne_snd_apply ν _

/-- The left-invariant covector field is equivariant for left multiplication on `G` and the
cotangent-lifted action on `T*G`. -/
theorem leftInvariantCovector_mul (g h : G) :
    ν.leftInvariantCovector (g * h) = g • ν.leftInvariantCovector h :=
  mul_smul g h _

/-- The left-invariant covector field is a smooth section of the cotangent bundle. -/
theorem contMDiff_leftInvariantCovector :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ν.leftInvariantCovector :=
  contMDiff_id.smul contMDiff_const

omit [LieGroup I ∞ G] in
private theorem momentMap_covectorAtOne : CotangentBundle.momentMap I G (covectorAtOne ν) = ν := by
  ext ξ
  have h : (fun g : G ↦ g • (covectorAtOne ν).proj) = id := funext fun g ↦ mul_one g
  rw [CotangentBundle.momentMap_apply, fundamentalVectorField_apply, h, mfderiv_id]
  exact covectorAtOne_snd_apply ν ξ

/-- The cotangent moment map of left multiplication sends the left-invariant covector field of `ν`
to the coadjoint orbit map: `μ(g • ν) = Ad*_g ν`. -/
@[simp]
theorem momentMap_leftInvariantCovector (g : G) :
    CotangentBundle.momentMap I G (ν.leftInvariantCovector g) =
      coadjointRepresentation ℝ I G g ν := by
  rw [leftInvariantCovector, CotangentBundle.momentMap_smul, momentMap_covectorAtOne]

/-! ### The left-invariant one-form -/

/-- The **left-invariant one-form** `α_ν` of `ν ∈ 𝔤*`, with value `ν` at the identity: the pullback
of the Liouville form of `T*G` along the left-invariant covector field of `ν`. -/
def leftInvariantForm : SmoothForm I G ℝ 1 :=
  SmoothForm.mpullback ν.leftInvariantCovector ν.contMDiff_leftInvariantCovector
    (CotangentBundle.liouvilleForm I G)

/-- The left-invariant one-form of `ν` evaluates a tangent vector `v` at `g` to
`ν (d(L_{g⁻¹})_g v)`. -/
theorem leftInvariantForm_apply (g : G) (v : Fin 1 → TangentSpace I g) :
    ν.leftInvariantForm.val g v = ν (mfderiv I I (g⁻¹ * ·) g (v 0)) := by
  rw [leftInvariantForm, SmoothForm.coe_mpullback,
    CotangentBundle.mpullback_liouvilleForm_apply_of_proj_comp_eq (g := id)
      (fun y ↦ ν.proj_leftInvariantCovector y)
      (ν.contMDiff_leftInvariantCovector.mdifferentiableAt (by simp)),
    mfderiv_id, ContinuousLinearMap.id_apply, leftInvariantCovector_snd_apply]

/-- The left-invariant one-form of `ν` is constant, equal to `ν ξ`, on the left-invariant vector
field of `ξ`. -/
@[simp]
theorem leftInvariantForm_apply_mulInvariantVectorField (ξ : GroupLieAlgebra I G) (g : G) :
    ν.leftInvariantForm.val g ![mulInvariantVectorField ξ g] = ν ξ := by
  rw [leftInvariantForm_apply, Matrix.cons_val_zero, mfderiv_inv_mul_mulInvariantVectorField]

/-- The left-invariant one-form is invariant under left translations. -/
@[simp]
theorem mpullback_mul_left_leftInvariantForm (h : G) :
    SmoothForm.mpullback (h * ·) contMDiff_mul_left ν.leftInvariantForm = ν.leftInvariantForm := by
  rw [leftInvariantForm, SmoothForm.mpullback_mpullback_of_comp_eq contMDiff_mul_left
    ν.contMDiff_leftInvariantCovector ν.contMDiff_leftInvariantCovector
    (contMDiff_const_smul h) (funext fun g ↦ ν.leftInvariantCovector_mul h g),
    CotangentBundle.mpullback_smul_liouvilleForm]

/-- Right translation by `h` pulls the left-invariant one-form of `ν` back to that of the
coadjoint translate `Ad*_h ν`. -/
@[simp]
theorem mpullback_mul_right_leftInvariantForm (h : G) :
    SmoothForm.mpullback (· * h) contMDiff_mul_right ν.leftInvariantForm =
      (coadjointRepresentation ℝ I G h ν).leftInvariantForm := by
  apply Subtype.ext
  funext g
  ext v
  obtain ⟨ξ, hξ⟩ := exists_mulInvariantVectorField_eq (v 0)
  rw [SmoothForm.coe_mpullback, TauCeti.mpullback_apply, leftInvariantForm_apply,
    leftInvariantForm_apply, ← hξ, mfderiv_mul_right_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    coadjointRepresentation_apply]

/-- The left-invariant one-form of `ν` is the left-invariant form `TauCeti.leftInvariantForm` of
`ν`, read as an alternating map of degree one. -/
theorem coe_leftInvariantForm :
    ν.leftInvariantForm.val = TauCeti.leftInvariantForm
      (ContinuousAlternatingMap.ofSubsingleton ℝ (GroupLieAlgebra I G) ℝ (0 : Fin 1)
        (LinearMap.toContinuousLinearMap ν)) := by
  funext g
  ext v
  rw [leftInvariantForm_apply, TauCeti.leftInvariantForm_apply]
  exact (ContinuousAlternatingMap.ofSubsingleton_apply_apply ℝ (GroupLieAlgebra I G) ℝ (0 : Fin 1)
    (LinearMap.toContinuousLinearMap ν) fun i ↦ mfderiv I I (g⁻¹ * ·) g (v i)).symm

/-! ### The left-invariant Kirillov form -/

/-- The **left-invariant Kirillov form** `σ_ν = -dα_ν` of `ν ∈ 𝔤*` on `G`, where `α_ν` is the
left-invariant one-form of `ν`. It is the left-invariant two-form with value the Kirillov form
`ν ⁅ξ, η⁆` at the identity (`Module.Dual.bilinFormAt_one_leftInvariantKirillovForm`), the pullback
of the Kirillov–Kostant–Souriau form of the coadjoint orbit of `ν` along `g ↦ Ad*_g ν`. -/
def leftInvariantKirillovForm : SmoothTwoForm I G :=
  -mextDerivₗ I 1 ν.leftInvariantForm

theorem leftInvariantKirillovForm_def :
    ν.leftInvariantKirillovForm = -mextDerivₗ I 1 ν.leftInvariantForm :=
  (rfl)

/-- The left-invariant Kirillov form of `ν` is the pullback of the canonical symplectic form of
`T*G` along the left-invariant covector field of `ν`. -/
theorem leftInvariantKirillovForm_eq_mpullback_symplecticForm :
    ν.leftInvariantKirillovForm = SmoothForm.mpullback ν.leftInvariantCovector
      ν.contMDiff_leftInvariantCovector (CotangentBundle.symplecticForm I G) := by
  rw [leftInvariantKirillovForm, leftInvariantForm, SmoothForm.mextDerivₗ_mpullback,
    CotangentBundle.symplecticForm_eq_neg_mextDerivₗ, map_neg]

/-- The left-invariant Kirillov form is closed. -/
theorem isClosed_leftInvariantKirillovForm : ν.leftInvariantKirillovForm.IsClosed :=
  (SmoothForm.isClosed_mextDerivₗ _).neg

/-- The left-invariant Kirillov form of `ν` pairs the left-invariant vector fields of `ξ` and `η`
to the constant `ν ⁅ξ, η⁆`. -/
theorem eval₂_leftInvariantKirillovForm_mulInvariantVectorField (ξ η : GroupLieAlgebra I G)
    (g : G) :
    ν.leftInvariantKirillovForm.eval₂ g (mulInvariantVectorField ξ g)
      (mulInvariantVectorField η g) = ν ⁅ξ, η⁆ := by
  have hconst (ζ : GroupLieAlgebra I G) :
      (fun y ↦ ν.leftInvariantForm.val y ![mulInvariantVectorField ζ y]) = fun _ ↦ ν ζ :=
    funext fun y ↦ ν.leftInvariantForm_apply_mulInvariantVectorField ζ y
  -- The invariant formula: `dα(X, Y) = X(α Y) - Y(α X) - α [X, Y]`, and `α` is constant on
  -- left-invariant vector fields, whose bracket is the left-invariant field of `⁅ξ, η⁆`.
  rw [SmoothBundleForm.eval₂_apply, leftInvariantKirillovForm, NegMemClass.coe_neg, Pi.neg_apply,
    mextDerivₗ_apply, ContinuousAlternatingMap.neg_apply,
    SmoothForm.mextDeriv_apply_one (mdifferentiable_mulInvariantVectorField ξ g)
      (mdifferentiable_mulInvariantVectorField η g),
    hconst, hconst, mvfderiv_const, mvfderiv_const, ← mulInvariantVector_mlieBracket,
    leftInvariantForm_apply_mulInvariantVectorField, ← GroupLieAlgebra.bracket_def]
  simp

/-- At the identity the left-invariant Kirillov form of `ν` is the Kirillov form
`ν ⁅ξ, η⁆`. -/
@[simp]
theorem bilinFormAt_one_leftInvariantKirillovForm :
    ν.leftInvariantKirillovForm.bilinFormAt 1 = ν.kirillovForm := by
  ext ξ η
  rw [SmoothForm.bilinFormAt_apply, kirillovForm_apply,
    ← ν.eval₂_leftInvariantKirillovForm_mulInvariantVectorField ξ η 1,
    mulInvariantVectorField_one, mulInvariantVectorField_one]

/-- The left-invariant Kirillov form of `ν` pairs tangent vectors `v` and `w` at `g` to
`ν ⁅d(L_{g⁻¹})_g v, d(L_{g⁻¹})_g w⁆`, the Kirillov form of their translates to the identity. -/
theorem bilinFormAt_leftInvariantKirillovForm_apply (g : G) (v w : TangentSpace I g) :
    ν.leftInvariantKirillovForm.bilinFormAt g v w =
      ν.kirillovForm (mfderiv I I (g⁻¹ * ·) g v) (mfderiv I I (g⁻¹ * ·) g w) := by
  obtain ⟨ξ, rfl⟩ := exists_mulInvariantVectorField_eq v
  obtain ⟨η, rfl⟩ := exists_mulInvariantVectorField_eq w
  rw [SmoothForm.bilinFormAt_apply, eval₂_leftInvariantKirillovForm_mulInvariantVectorField,
    mfderiv_inv_mul_mulInvariantVectorField, mfderiv_inv_mul_mulInvariantVectorField,
    kirillovForm_apply]

/-- **The kernel of the left-invariant Kirillov form** of `ν` at `g` is the left translate
`d(L_g)(𝔤_ν)` of the coadjoint stabilizer `𝔤_ν` of `ν`, the tangent space of the coset `g G_ν`. -/
theorem ker_bilinFormAt_leftInvariantKirillovForm (g : G) :
    LinearMap.ker (ν.leftInvariantKirillovForm.bilinFormAt g) =
      mulInvariantDistribution (lieAnnihilator ℝ (GroupLieAlgebra I G) ν).toSubmodule g := by
  ext v
  rw [mem_mulInvariantDistribution_iff, ← ker_kirillovForm]
  -- Unfold kernel membership on both sides. The translate lies in `TangentSpace I (g⁻¹ * g)`,
  -- which is definitionally `GroupLieAlgebra I G` (both are the model space), but `rw` and `simp`
  -- with `LinearMap.mem_ker` cannot see this through the membership instance, so it is retyped
  -- by the ascription.
  change ν.leftInvariantKirillovForm.bilinFormAt g v = 0 ↔
    ν.kirillovForm (mfderiv I I (g⁻¹ * ·) g v : GroupLieAlgebra I G) = 0
  simp only [LinearMap.ext_iff, bilinFormAt_leftInvariantKirillovForm_apply, LinearMap.zero_apply]
  refine ⟨fun h η ↦ ?_, fun h w ↦ h _⟩
  simpa only [mfderiv_inv_mul_mulInvariantVectorField] using h (mulInvariantVectorField η g)

/-- The left-invariant Kirillov form is invariant under left translations. -/
@[simp]
theorem mpullback_mul_left_leftInvariantKirillovForm (h : G) :
    SmoothForm.mpullback (h * ·) contMDiff_mul_left ν.leftInvariantKirillovForm =
      ν.leftInvariantKirillovForm := by
  rw [leftInvariantKirillovForm, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_mul_left_leftInvariantForm]

/-- Right translation by `h` pulls the left-invariant Kirillov form of `ν` back to that of the
coadjoint translate `Ad*_h ν`. -/
@[simp]
theorem mpullback_mul_right_leftInvariantKirillovForm (h : G) :
    SmoothForm.mpullback (· * h) contMDiff_mul_right ν.leftInvariantKirillovForm =
      (coadjointRepresentation ℝ I G h ν).leftInvariantKirillovForm := by
  rw [leftInvariantKirillovForm, leftInvariantKirillovForm, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_mul_right_leftInvariantForm]

/-- Right translations by elements of the coadjoint stabilizer `G_ν` preserve the left-invariant
Kirillov form of `ν`. -/
theorem mpullback_mul_right_leftInvariantKirillovForm_of_mem_stabilizer {h : G}
    (hh : h ∈ Representation.stabilizer (coadjointRepresentation ℝ I G) ν) :
    SmoothForm.mpullback (· * h) contMDiff_mul_right ν.leftInvariantKirillovForm =
      ν.leftInvariantKirillovForm := by
  rw [mpullback_mul_right_leftInvariantKirillovForm, Representation.mem_stabilizer.mp hh]

/-- **The coadjoint orbit map is a moment map for the left-invariant Kirillov form.** For the action
of `G` on itself by left multiplication, `g ↦ Ad*_g ν` is a coadjoint-equivariant moment map of
the left-invariant Kirillov form of `ν`. -/
theorem isEquivariantMomentMap_leftInvariantKirillovForm [T2Space G] [I.Boundaryless] :
    ν.leftInvariantKirillovForm.IsEquivariantMomentMap
      fun g : G ↦ coadjointRepresentation ℝ I G g ν := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  -- Pull the cotangent moment map of the lifted action back along the equivariant section.
  have h := (CotangentBundle.isEquivariantMomentMap_momentMap (IG := I) (G := G) (I := I)
    (M := G)).mpullback ν.contMDiff_leftInvariantCovector
      (fun g y ↦ ν.leftInvariantCovector_mul g y)
  rw [leftInvariantKirillovForm_eq_mpullback_symplecticForm]
  convert h using 1
  funext g
  rw [Function.comp_apply, momentMap_leftInvariantCovector]

end Module.Dual
