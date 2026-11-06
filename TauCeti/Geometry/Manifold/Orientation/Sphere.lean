/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.Orientation.TopForm

/-!
# The orientation of the unit sphere and the antipodal map

Let `E` be a real inner product space of dimension `n + 1`, and `Sⁿ = sphere (0 : E) 1` its unit
sphere, with Mathlib's smooth structure modelled on `ℝⁿ`. An orientation `o` of `E` induces an
orientation `TauCeti.Manifold.Orientation.sphere o` of `Sⁿ` by the outward normal first
convention: a basis `(v₁, …, vₙ)` of the tangent space at `x` is positive exactly when
`(x, v₁, …, vₙ)` is a positive basis of `E` for `o`
(`TauCeti.Manifold.Orientation.orientation_eq_orientationAt_sphere_iff`), the tangent vectors
being read in `E` through the derivative of the inclusion. This is the outward normal first
convention by which a boundary, here that of the unit ball, is oriented. It is the orientation of
the top form `x ↦ ι^*(ω(x, ·))`, where `ω` is a positive volume form of `E`; reversing `o`
reverses it.

The antipodal map `x ↦ -x` pulls this top form back to `(-1)^(n+1)` times itself, since it negates
both the point `x` and the tangent vectors. So it preserves the orientation of `Sⁿ` when `n` is
odd and reverses it when `n` is even. When `n ≥ 1` the sphere is connected, so it has exactly two
orientations, and the antipodal map has orientation sign `(-1)^(n+1)` for every orientation of
`Sⁿ`. Since every point has exactly one antipodal preimage, the antipodal map has degree
`(-1)^(n+1)` at every value (`TauCeti.Manifold.Orientation.degreeAtRegularValue_neg_sphere`).
These local signs are what the degree computations of maps out of and into spheres use, for
instance for families of great circles, which are invariant under the antipodal map of a sphere
factor.

## Main definitions

* `TauCeti.Manifold.Orientation.sphere o`: the orientation of the unit sphere induced by an
  orientation `o` of `E`, outward normal first.

## Main results

* `TauCeti.Manifold.Orientation.orientation_eq_orientationAt_sphere_iff`: a tangent basis `b` at
  `x` is positive exactly when `(x, b)` is positive for `o`.
* `TauCeti.Manifold.Orientation.sphere_neg`: reversing `o` reverses the orientation of the sphere.
* `TauCeti.orientable_sphere`: the unit sphere is orientable.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_neg_sphere`,
  `TauCeti.Manifold.Orientation.isOrientationReversingAt_neg_sphere`: the antipodal map of `Sⁿ`
  preserves its orientation for odd `n` and reverses it for even `n`.
* `TauCeti.Manifold.Orientation.orientationSign_neg_sphere`: for `n ≥ 1` and every orientation of
  `Sⁿ`, the antipodal map has orientation sign `(-1)^(n+1)` at every point.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_neg_sphere`: for `n ≥ 1` the antipodal map
  of `Sⁿ` has degree `(-1)^(n+1)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (the orientation of the sphere as a boundary) and Chapter 17,
  section Degree Theory (the degree of the antipodal map).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Module
open scoped Manifold InnerProductSpace

namespace TauCeti.Manifold.Orientation

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The form `y ↦ Ω(y, ·)` on `E`, for a top form `Ω` of `E`. -/
private def ambientTopForm (Ω : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) : RoughForm 𝓘(ℝ, E) E ℝ n :=
  fun y ↦ Ω.curryLeft y

private theorem ambientTopForm_apply (Ω : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) (y : E) (v : Fin n → E) :
    ambientTopForm Ω y v = Ω (Matrix.vecCons y v) := (rfl)

variable [Fact (finrank ℝ E = n + 1)]

/-- The top form `ι^*(Ω(x, ·))` on the unit sphere, for a top form `Ω` of the ambient space. -/
private def sphereTopForm (Ω : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) :
    RoughForm (𝓡 n) (Metric.sphere (0 : E) 1) ℝ n :=
  mpullback (𝓡 n) 𝓘(ℝ, E) ((↑) : Metric.sphere (0 : E) 1 → E) (ambientTopForm Ω)

private theorem sphereTopForm_apply (Ω : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) (x : Metric.sphere (0 : E) 1)
    (v : Fin n → TangentSpace (𝓡 n) x) :
    sphereTopForm Ω x v = Ω (Matrix.vecCons (x : E)
      fun i ↦ mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x (v i)) := by
  rw [sphereTopForm, mpullback_apply]
  simp only [mvfderiv_apply_eq_mfderiv_apply]
  -- The tangent spaces of `E` are `E` itself, so the tangent vectors are arguments of `Ω`.
  exact ambientTopForm_apply Ω _ _

private theorem isSmoothForm_sphereTopForm (Ω : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) :
    IsSmoothForm (𝓡 n) 0 (sphereTopForm Ω) :=
  ((isSmoothForm_modelSpace_iff (n := 0)).mpr Ω.curryLeft.contDiff).mpullback contMDiff_coe_sphere

/-- A point of the sphere followed by the image of a linearly independent family of tangent
vectors is linearly independent in the ambient space: the tangent vectors are orthogonal to the
point. -/
private theorem linearIndependent_vecCons_mvfderiv (x : Metric.sphere (0 : E) 1)
    {v : Fin n → TangentSpace (𝓡 n) x} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (Matrix.vecCons (x : E)
      fun i ↦ mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x (v i)) := by
  let d : TangentSpace (𝓡 n) x →ₗ[ℝ] E :=
    (mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x).toLinearMap
  have hd : LinearMap.ker d = ⊥ :=
    LinearMap.ker_eq_bot.mpr (injective_mvfderiv_subtypeVal_sphere x)
  -- The span of the image lies in the range of the derivative, the orthogonal complement of `x`.
  have hrange : Submodule.span ℝ (Set.range fun i ↦ d (v i)) ≤ (ℝ ∙ (x : E))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := n) x, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range_self _ _
  refine (hv.map' d hd).finCons fun hx ↦ ?_
  have hxx : ⟪(x : E), (x : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hrange hx)
  exact ne_zero_of_mem_unit_sphere x (inner_self_eq_zero.mp hxx)

/-- A point of the sphere followed by the image of a basis of its tangent space is a basis of the
ambient space. -/
private def sphereFrame (x : Metric.sphere (0 : E) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) : Basis (Fin (n + 1)) ℝ E :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_vecCons_mvfderiv x b.linearIndependent)
    (by simp [(Fact.out : finrank ℝ E = n + 1)])

private theorem coe_sphereFrame (x : Metric.sphere (0 : E) 1)
    (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x)) :
    ⇑(sphereFrame x b) = Matrix.vecCons (x : E)
      fun i ↦ mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x (b i) :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

private theorem sphereTopForm_ne_zero {Ω : E [⋀^Fin (n + 1)]→L[ℝ] ℝ} (hΩ : Ω ≠ 0)
    (x : Metric.sphere (0 : E) 1) : sphereTopForm Ω x ≠ 0 := by
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) x) (finrank_euclideanSpace_fin (n := n))
  refine ((sphereTopForm Ω x).map_basis_ne_zero_iff b).mp ?_
  rw [sphereTopForm_apply, ← coe_sphereFrame]
  exact (Ω.map_basis_ne_zero_iff _).mpr hΩ

/-- The determinant form of a positive basis of `E` chosen from an orientation. -/
private def positiveTopForm (o : _root_.Orientation ℝ E (Fin (n + 1))) :
    E [⋀^Fin (n + 1)]→L[ℝ] ℝ :=
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  (o.someBasis (by simp [(Fact.out : finrank ℝ E = n + 1)])).continuousDet

/-- The determinant form of an orientation is positive exactly on the positive bases. -/
private theorem positiveTopForm_pos_iff (o : _root_.Orientation ℝ E (Fin (n + 1)))
    (B : Basis (Fin (n + 1)) ℝ E) : 0 < positiveTopForm o B ↔ B.orientation = o := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  rw [positiveTopForm, Basis.continuousDet_apply, ← Basis.orientation_eq_iff_det_pos,
    Orientation.someBasis_orientation, eq_comm]

private theorem positiveTopForm_ne_zero (o : _root_.Orientation ℝ E (Fin (n + 1))) :
    positiveTopForm o ≠ 0 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h : Fintype.card (Fin (n + 1)) = finrank ℝ E := by simp [(Fact.out : finrank ℝ E = n + 1)]
  refine ((positiveTopForm o).map_basis_ne_zero_iff (o.someBasis h)).mp (ne_of_gt ?_)
  exact (positiveTopForm_pos_iff o _).mpr (o.someBasis_orientation h)

/-- The orientation of the unit sphere `Sⁿ` of `E` induced by an orientation `o` of `E`, outward
normal first: a basis `b` of the tangent space at `x` is positive exactly when `x` followed by `b`
is a positive basis of `E` (`orientation_eq_orientationAt_sphere_iff`), the convention by which
the boundary of the unit ball is oriented. -/
def sphere (o : _root_.Orientation ℝ E (Fin (n + 1))) :
    Orientation (𝓡 n) (Metric.sphere (0 : E) 1) (Fin n) :=
  ofTopForm finrank_euclideanSpace_fin (sphereTopForm (positiveTopForm o))
    (isSmoothForm_sphereTopForm _) (sphereTopForm_ne_zero (positiveTopForm_ne_zero o))

/-- **The outward normal first convention.** A basis `b` of the tangent space of the unit sphere
at `x` is positive for `sphere o` exactly when the basis `B = (x, b)` of `E`, with the tangent
vectors read in `E` through the derivative of the inclusion, is positive for `o`. -/
theorem orientation_eq_orientationAt_sphere_iff (o : _root_.Orientation ℝ E (Fin (n + 1)))
    {x : Metric.sphere (0 : E) 1} (b : Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (B : Basis (Fin (n + 1)) ℝ E) (hB : ⇑B = Matrix.vecCons (x : E)
      fun i ↦ mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x (b i)) :
    b.orientation = (sphere o).orientationAt x ↔ B.orientation = o := by
  rw [sphere, orientation_eq_orientationAt_ofTopForm_iff, sphereTopForm_apply, ← hB,
    positiveTopForm_pos_iff]

/-- Reversing the orientation of `E` reverses the induced orientation of its unit sphere. -/
@[simp]
theorem sphere_neg (o : _root_.Orientation ℝ E (Fin (n + 1))) : sphere (-o) = -sphere o := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  ext x
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) x) (finrank_euclideanSpace_fin (n := n))
  have hcard : Fintype.card (Fin n) = finrank ℝ (TangentSpace (𝓡 n) x) := by simp
  have hcard' : Fintype.card (Fin (n + 1)) = finrank ℝ E := by
    simp [(Fact.out : finrank ℝ E = n + 1)]
  have h := orientation_eq_orientationAt_sphere_iff o b _ (coe_sphereFrame x b)
  have h' := orientation_eq_orientationAt_sphere_iff (-o) b _ (coe_sphereFrame x b)
  rw [orientationAt_neg]
  -- Both tangent orientations are read off whether the frame `(x, b)` is positive for `o`, and
  -- `b` is positive for exactly one of them.
  rcases (sphereFrame x b).orientation.eq_or_eq_neg o hcard' with hB | hB
  · have hne : (sphere (-o)).orientationAt x ≠ b.orientation := fun hs ↦
      Module.Ray.ne_neg_self o (hB.symm.trans (h'.mp hs.symm))
    rw [(Orientation.ne_iff_eq_neg _ _ hcard).mp hne, h.mpr hB]
  · have hne : (sphere o).orientationAt x ≠ b.orientation := fun hs ↦
      Module.Ray.ne_neg_self o (hB ▸ h.mp hs.symm).symm
    rw [(Orientation.ne_iff_eq_neg _ _ hcard).mp hne,
      neg_neg (G := _root_.Orientation ℝ (TangentSpace (𝓡 n) x) (Fin n)), h'.mpr hB]

/-- The antipodal map `x ↦ -x` pulls the top form `ι^*(Ω(x, ·))` of the sphere back to
`(-1)^(n+1)` times itself: it negates both the point and the tangent vectors. -/
private theorem mpullback_neg_sphereTopForm (Ω : E [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (x : Metric.sphere (0 : E) 1) :
    mpullback (𝓡 n) (𝓡 n) (fun y : Metric.sphere (0 : E) 1 ↦ -y) (sphereTopForm Ω) x =
      ((-1 : ℝ) ^ (n + 1)) • sphereTopForm Ω x := by
  have hneg : MDifferentiableAt (𝓡 n) (𝓡 n) (fun y : Metric.sphere (0 : E) 1 ↦ -y) x :=
    (contMDiff_neg_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have hcoe : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : Metric.sphere (0 : E) 1 → E) (-x) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  -- The inclusion intertwines the antipodal maps of the sphere and of `E`.
  have hd (w : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) (-x)
          (mfderiv (𝓡 n) (𝓡 n) (fun y ↦ -y) x w) =
        -mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x w := by
    have hcomp : ((↑) : Metric.sphere (0 : E) 1 → E) ∘ (fun y ↦ -y) = -((↑) : _ → E) :=
      funext fun y ↦ coe_neg_sphere y
    rw [← mvfderiv_comp_apply x hcoe hneg, hcomp, mvfderiv_neg]
    -- Negation of continuous linear maps is pointwise.
    rfl
  ext v
  rw [mpullback_apply, sphereTopForm_apply, ContinuousAlternatingMap.smul_apply,
    sphereTopForm_apply, coe_neg_sphere]
  simp_rw [hd]
  have hcons : Matrix.vecCons (-(x : E))
      (fun i ↦ -mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x (v i)) =
      fun i ↦ (-1 : ℝ) • Matrix.vecCons (x : E)
        (fun i ↦ mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : E) 1 → E) x (v i)) i := by
    ext i
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, neg_one_smul]
  rw [hcons, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The antipodal map of an odd-dimensional sphere preserves orientation.** -/
theorem isOrientationPreservingAt_neg_sphere (o : _root_.Orientation ℝ E (Fin (n + 1)))
    (hn : Odd n) (x : Metric.sphere (0 : E) 1) :
    IsOrientationPreservingAt (sphere o) (sphere o) (fun y ↦ -y) x := by
  rw [sphere]
  refine isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _ ?_
    (mpullback_neg_sphereTopForm _ x)
  rw [hn.add_one.neg_one_pow]
  exact one_pos

/-- **The antipodal map of an even-dimensional sphere reverses orientation.** -/
theorem isOrientationReversingAt_neg_sphere (o : _root_.Orientation ℝ E (Fin (n + 1)))
    (hn : Even n) (x : Metric.sphere (0 : E) 1) :
    IsOrientationReversingAt (sphere o) (sphere o) (fun y ↦ -y) x := by
  rw [sphere]
  refine isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _ ?_
    (mpullback_neg_sphereTopForm _ x)
  rw [hn.add_one.neg_one_pow]
  exact neg_one_lt_zero

/-- **The orientation sign of the antipodal map.** For `n ≥ 1` and every orientation of the
connected sphere `Sⁿ`, the antipodal map has orientation sign `(-1)^(n+1)` at every point. -/
theorem orientationSign_neg_sphere [NeZero n]
    (o : Orientation (𝓡 n) (Metric.sphere (0 : E) 1) (Fin n)) (x : Metric.sphere (0 : E) 1) :
    orientationSign o o (fun y ↦ -y) x = (-1) ^ (n + 1) := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : PreconnectedSpace (Metric.sphere (0 : E) 1) :=
    Subtype.preconnectedSpace <| isPreconnected_sphere (by
      rw [← finrank_eq_rank, hE]
      have := NeZero.ne n
      exact_mod_cast (by omega : 1 < n + 1)) 0 1
  -- Compare `o` with the orientation induced by an orientation of `E`.
  let oE := (finBasisOfFinrankEq ℝ E hE).orientation
  have key : orientationSign (sphere oE) (sphere oE) (fun y ↦ -y) x = (-1) ^ (n + 1) := by
    rcases Nat.even_or_odd n with hn | hn
    · rw [orientationSign_of_isOrientationReversingAt (isOrientationReversingAt_neg_sphere oE hn x),
        hn.add_one.neg_one_pow]
    · rw [orientationSign_of_isOrientationPreservingAt
        (isOrientationPreservingAt_neg_sphere oE hn x), hn.add_one.neg_one_pow]
  rcases o.eq_or_eq_neg (sphere oE) with rfl | rfl
  · exact key
  · rw [orientationSign_neg_left, orientationSign_neg_right, neg_neg, key]

/-- **The degree of the antipodal map.** For `n ≥ 1` and every orientation of `Sⁿ`, the antipodal
map has degree `(-1)^(n+1)` at every value: its only preimage is the antipodal point. -/
theorem degreeAtRegularValue_neg_sphere [NeZero n]
    (o : Orientation (𝓡 n) (Metric.sphere (0 : E) 1) (Fin n)) (y : Metric.sphere (0 : E) 1) :
    degreeAtRegularValue o o (fun x ↦ -x) y = (-1) ^ (n + 1) := by
  rw [degreeAtRegularValue_eq_sum (s := {-y}) fun x ↦ by
    rw [Finset.mem_singleton, neg_eq_iff_eq_neg], Finset.sum_singleton,
    orientationSign_neg_sphere]

end TauCeti.Manifold.Orientation

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = n + 1)]

/-- The unit sphere of a finite-dimensional real inner product space is orientable. -/
theorem orientable_sphere : Orientable (𝓡 n) (Metric.sphere (0 : E) 1) := by
  have hE : Module.finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  constructor
  rw [finrank_euclideanSpace_fin]
  exact ⟨Manifold.Orientation.sphere (Module.finBasisOfFinrankEq ℝ E hE).orientation⟩

end TauCeti
