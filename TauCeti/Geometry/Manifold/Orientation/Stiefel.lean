/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.LinearAlgebra.Basis.Exact

/-!
# The normal orientation of Stiefel manifolds

Let `E` be a finite-dimensional real inner product space of dimension `n`. The Stiefel manifold
`TauCeti.stiefel E k` of orthonormal `k`-frames `v = (v₀, …, v_{k-1})` is the regular level set of
the Gram map `v ↦ (s(i, j) ↦ ⟪v i, v j⟫)` in the space `Fin k → E` of `k`-families, a manifold of
dimension `m = k n - (k + 1).choose 2`. For each unordered pair `s = s(i, j)` of indices the
**normal vector field** `ν_s` (`TauCeti.stiefelNormal`) puts `v j` in slot `i`, `v i` in slot `j`
and `0` elsewhere; it is the gradient of `⟪v i, v j⟫` (half of it when `i = j`). At a frame the
derivative of the Gram map sends `ν_s v` to `2` times the coordinate vector of `s`
(`TauCeti.gramSym2Deriv_stiefelNormal`) and the tangent vectors to `0`, so the `(k + 1).choose 2`
normals together with the tangent space span `Fin k → E`.

So an orientation `O` of the space of `k`-families orients the Stiefel manifold, once the normals
are put in an order `σ : Fin N ≃ Sym2 (Fin k)`, exactly as an orientation of `E` orients its unit
sphere by the outward normal: a tangent basis `t₁, …, t_m` at `v` is positive for the *normal
orientation* `O.stiefelOrientation σ hm` exactly when

`ν_{σ 0} v, …, ν_{σ (N - 1)} v, t₁, …, t_m`,

with the tangent vectors read in `Fin k → E` through the derivative of the inclusion, is a positive
basis for `O` (`Orientation.orientation_eq_orientationAt_stiefelOrientation_iff`). Reversing `O`
reverses it (`Orientation.stiefelOrientation_neg`). For instance this orients the manifold
`V₃(ℝⁿ⁺¹)` of orthonormal three-frames, the parameter space of the family
`TauCeti.stiefelSphereFamily` of round two-spheres in `Sⁿ` of Barraud–Damian–Humilière–Oancea,
Example 6.16, which is required to be a closed oriented manifold there.

For two-frames, with the normals in the order `s(0, 0), s(1, 1), s(0, 1)`, that is

`(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)`,

this is `O.stiefelTwoOrientation`, the orientation of the unit tangent bundle of the unit sphere
of `E` (`Orientation.orientation_eq_orientationAt_stiefelTwoOrientation_iff`). When `E` has
dimension `n + 2`, the **frame reflection** `(u, v) ↦ (u, -v)` (`TauCeti.stiefelTwoReflection`)
is the restriction of the linear map `(a, b) ↦ (a, -b)` of determinant `(-1)ⁿ⁺²`. It sends the
normals at `(u, v)` to `(u, 0)`, `(0, -v)` and `-(-v, u)`, the normals at `(u, -v)` up to the sign
of the third, so it pulls the top form back to `-(-1)ⁿ⁺² = (-1)ⁿ⁺¹` times itself: it preserves the
normal orientation when `n` is odd and reverses it when `n` is even
(`TauCeti.isOrientationPreservingAt_stiefelTwoReflection`,
`TauCeti.isOrientationReversingAt_stiefelTwoReflection`). This is the sign by which the two
preimages of a point under the rotation map of Proposition 6.17 of the same paper are compared,
and the two-frame orientation orients the domain `T¹Sⁿ⁺¹ × S¹` of that map.

The orientation is constructed, as for the sphere, from a nowhere-vanishing continuous top form:
the pullback to the Stiefel manifold of the contraction of a volume form of `Fin k → E` with the
normal vector fields. It does not vanish because the normals are sent by the derivative of the
Gram map to independent vectors, while the tangent vectors are sent to zero.

## Main declarations

* `TauCeti.stiefelNormal`: the normal vector field `ν_s` of the Stiefel manifold.
* `TauCeti.gramSym2Deriv_stiefelNormal`: the derivative of the Gram map sends `ν_s v` to `2` times
  the coordinate vector of `s`.
* `Orientation.stiefelOrientation`: the normal orientation of the Stiefel manifold of orthonormal
  `k`-frames.
* `Orientation.orientation_eq_orientationAt_stiefelOrientation_iff`,
  `Orientation.orientation_eq_neg_orientationAt_stiefelOrientation_iff`: a tangent basis is
  positive (negative) exactly when the normals followed by it form a positive (negative) basis of
  `Fin k → E`.
* `Orientation.stiefelOrientation_neg`: reversing the orientation of `Fin k → E` reverses the
  normal orientation.
* `Orientation.stiefelTwoOrientation`: the normal orientation of the Stiefel manifold of
  orthonormal two-frames, with the normals `(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)`.
* `TauCeti.isOrientationPreservingAt_stiefelTwoReflection`,
  `TauCeti.isOrientationReversingAt_stiefelTwoReflection`: the frame reflection `(u, v) ↦ (u, -v)`
  preserves or reverses the normal orientation according to the parity of the dimension.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (orientations from nonvanishing top forms and orientations of
  hypersurfaces) and Chapter 5 (regular level sets).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2 (Example 6.16 and
  Proposition 6.17).
-/

public section

noncomputable section

open Module Set TauCeti.Manifold.Orientation
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-! ### The normal vector fields -/

section Normal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

/-- The **normal vector field** `ν_s` of the Stiefel manifold indexed by an unordered pair
`s = s(i, j)` of indices: at a family `v`, the family `ν_s v` has `v j` in slot `i` and `v i` in
slot `j`, and `0` in the other slots (so `ν_{s(i, i)} v` has `v i` in slot `i`). It is the
gradient of `v ↦ ⟪v i, v j⟫` for `i ≠ j` and half the gradient of `v ↦ ⟪v i, v i⟫`. -/
def stiefelNormal (s : Sym2 (Fin k)) : (Fin k → E) →L[ℝ] Fin k → E :=
  ContinuousLinearMap.pi fun l ↦ ∑ j, if s(l, j) = s then ContinuousLinearMap.proj j else 0

/-- The slot `l` of `ν_s v` is the sum of the vectors `v j` over the indices `j` with
`s(l, j) = s`. -/
theorem stiefelNormal_apply (s : Sym2 (Fin k)) (v : Fin k → E) (l : Fin k) :
    stiefelNormal s v l = ∑ j, if s(l, j) = s then v j else 0 := by
  simp only [stiefelNormal, ContinuousLinearMap.pi_apply, sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> rfl

end Normal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- At an orthonormal family `v`, the derivative of the Gram map sends the normal `ν_s v` to
`2` times the indicator of `s`: the normals are dual to the coordinates of the Gram map. -/
theorem gramSym2Deriv_stiefelNormal {v : Fin k → E} (hv : Orthonormal ℝ v) (s : Sym2 (Fin k)) :
    gramSym2Deriv E k v (stiefelNormal s v) = Pi.single s 2 := by
  have key (a b : Fin k) : ⟪v a, stiefelNormal s v b⟫ = if s(a, b) = s then 1 else 0 := by
    rw [stiefelNormal_apply, inner_sum, Finset.sum_eq_single a]
    · rw [Sym2.eq_swap]
      split_ifs <;> simp [hv.1 a]
    · intro j _ hj
      split_ifs
      · rw [orthonormal_iff_ite.1 hv]
        exact ite_eq_right_iff.2 fun h ↦ absurd h.symm hj
      · exact inner_zero_right _
    · simp
  funext s'
  induction s' using Sym2.ind with
  | _ a b =>
    rw [gramSym2Deriv_apply_mk, key, real_inner_comm, key, Sym2.eq_swap, Pi.single_apply]
    split_ifs <;> norm_num

/-! ### The contraction with the normals -/

/-- The contraction of a continuous alternating form with the vectors `u 0, …, u (N - 1)` in its
first `N` slots. -/
private def curryNormals {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ} :
    {N : ℕ} → (V [⋀^Fin (m + N)]→L[ℝ] ℝ) → (Fin N → V) → V [⋀^Fin m]→L[ℝ] ℝ
  | 0, f, _ => f
  | N + 1, f, u => curryNormals (ContinuousAlternatingMap.curryLeft (n := m + N) f (u 0))
      (Fin.tail u)

private theorem curryNormals_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m : ℕ} : ∀ {N : ℕ} (f : V [⋀^Fin (m + N)]→L[ℝ] ℝ) (u : Fin N → V) (t : Fin m → V),
      curryNormals f u t = f (Matrix.vecAppend (Nat.add_comm m N) u t)
  | 0, f, u, t => by
    rw [curryNormals]
    congr 1
    funext i
    simp [Matrix.vecAppend_eq_ite]
  | N + 1, f, u, t => by
    rw [curryNormals, curryNormals_apply, ContinuousAlternatingMap.curryLeft_apply_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [Matrix.vecAppend_eq_ite]
    · simp only [Matrix.vecAppend_eq_ite, Matrix.cons_val_succ, Fin.val_succ, Fin.tail]
      split_ifs with h₁ h₂ h₂
      · rfl
      · omega
      · omega
      · congr 1
        ext
        simp

private theorem continuous_curryNormals {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {m : ℕ} {X : Type*} [TopologicalSpace X] :
    ∀ {N : ℕ} {F : X → V [⋀^Fin (m + N)]→L[ℝ] ℝ} {u : X → Fin N → V}, Continuous F →
      Continuous u → Continuous fun x ↦ curryNormals (F x) (u x)
  | 0, _, _, hF, _ => hF
  | N + 1, F, u, hF, hu =>
    continuous_curryNormals (F := fun x ↦ ContinuousAlternatingMap.curryLeft (n := m + N) (F x)
        (u x 0)) (u := fun x ↦ Fin.tail (u x))
      (((ContinuousAlternatingMap.curryLeftLI (n := m + N)).continuous.comp hF).clm_apply
        ((continuous_apply 0).comp hu))
      (continuous_pi fun i ↦ (continuous_apply i.succ).comp hu)

/-! ### The normal orientation of `V_k(E)` -/

variable [FiniteDimensional ℝ E] {N m : ℕ}

/-- The model space of the Stiefel manifold of orthonormal `k`-frames of `E`. -/
local notation "𝓥" => 𝓘(ℝ, Fin (k * finrank ℝ E - Nat.choose (k + 1) 2) → ℝ)

/-- A volume form of the space of `k`-families, positive on the bases of orientation `O`. -/
private def stiefelVolume (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) :
    (Fin k → E) [⋀^Fin (m + N)]→L[ℝ] ℝ :=
  AlternatingMap.toContinuousAlternatingMap (Module.Ray.someVector O)

/-- The contraction of `stiefelVolume O` with the normal vector fields `ν_{σ 0}, …, ν_{σ (N - 1)}`,
a form of degree `m` on the space of `k`-families. -/
private def stiefelNormalForm (σ : Fin N ≃ Sym2 (Fin k))
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) :
    (Fin k → E) → (Fin k → E) [⋀^Fin m]→L[ℝ] ℝ := fun x ↦
  curryNormals (stiefelVolume O) fun i ↦ stiefelNormal (σ i) x

private theorem stiefelNormalForm_apply (σ : Fin N ≃ Sym2 (Fin k))
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) (x : Fin k → E)
    (t : Fin m → Fin k → E) :
    stiefelNormalForm σ O x t = Module.Ray.someVector O
      (Matrix.vecAppend (Nat.add_comm m N) (fun i ↦ stiefelNormal (σ i) x) t) := by
  rw [stiefelNormalForm, curryNormals_apply, stiefelVolume,
    AlternatingMap.coe_toContinuousAlternatingMap]

/-- `stiefelNormalForm σ O`, as a form on the space of `k`-families. -/
private def stiefelNormalRoughForm (σ : Fin N ≃ Sym2 (Fin k))
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) :
    RoughForm 𝓘(ℝ, Fin k → E) (Fin k → E) ℝ m :=
  stiefelNormalForm σ O

/-- The top form of the Stiefel manifold: the pullback along the inclusion of the contraction of
a volume form of the space of `k`-families with the normal vector fields. -/
private def stiefelTopForm (σ : Fin N ≃ Sym2 (Fin k))
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) : RoughForm 𝓥 (stiefel E k) ℝ m :=
  mpullback _ 𝓘(ℝ, Fin k → E) ((↑) : stiefel E k → Fin k → E) (stiefelNormalRoughForm σ O)

private theorem stiefelTopForm_apply (σ : Fin N ≃ Sym2 (Fin k))
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) (v : stiefel E k)
    (t : Fin m → TangentSpace 𝓥 v) :
    stiefelTopForm σ O v t = Module.Ray.someVector O (Matrix.vecAppend (Nat.add_comm m N)
      (fun i ↦ stiefelNormal (σ i) (v : Fin k → E))
      fun i ↦ mfderiv 𝓥 𝓘(ℝ, Fin k → E) ((↑) : stiefel E k → Fin k → E) v (t i)) := by
  rw [stiefelTopForm, mpullback_apply]
  exact stiefelNormalForm_apply σ O _ _

private theorem isSmoothForm_stiefelTopForm (σ : Fin N ≃ Sym2 (Fin k))
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) :
    IsSmoothForm 𝓥 0 (stiefelTopForm σ O) :=
  (isSmoothForm_modelSpace_iff.2 (contDiff_zero.2 (continuous_curryNormals continuous_const
    (continuous_pi fun i ↦ (stiefelNormal (σ i)).continuous)))).mpullback
    (contMDiff_coe_stiefel E k)

/-- At a frame `v`, the normals `ν_{σ 0} v, …, ν_{σ (N - 1)} v` followed by the image in
`Fin k → E` of a tangent basis `b` form a basis of the space of `k`-families: the derivative of
the Gram map sends the normals to `2` times the coordinate vectors, and the tangent space is its
kernel (`Module.Basis.ofExactLift`). -/
private theorem exists_basis_coe_eq_vecAppend_stiefelNormal (σ : Fin N ≃ Sym2 (Fin k))
    {v : stiefel E k} (b : Basis (Fin m) ℝ (TangentSpace 𝓥 v)) :
    ∃ B : Basis (Fin (m + N)) ℝ (Fin k → E), ⇑B = Matrix.vecAppend (Nat.add_comm m N)
      (fun i ↦ stiefelNormal (σ i) (v : Fin k → E))
      fun i ↦ mfderiv 𝓥 𝓘(ℝ, Fin k → E) ((↑) : stiefel E k → Fin k → E) v (b i) := by
  set f : TangentSpace 𝓥 v →ₗ[ℝ] Fin k → E :=
    (mfderiv 𝓥 𝓘(ℝ, Fin k → E) ((↑) : stiefel E k → Fin k → E) v).toLinearMap
  have hfg : Function.Exact f (gramSym2Deriv E k v).toLinearMap :=
    LinearMap.exact_iff.2 (range_mfderiv_coe_stiefel v).symm
  -- The basis `2 • e_{σ i}` of the target of the Gram map, lifted by the normals.
  let c : Basis (Fin N) ℝ (Sym2 (Fin k) → ℝ) :=
    ((Pi.basisFun ℝ (Sym2 (Fin k))).reindex σ.symm).unitsSMul
      fun _ ↦ Units.mk0 (2 : ℝ) two_ne_zero
  have hs (i : Fin N) : gramSym2Deriv E k v (stiefelNormal (σ i) v) = c i := by
    ext s
    simp [c, gramSym2Deriv_stiefelNormal (mem_stiefel_iff.1 v.2), Pi.single_apply,
      Basis.unitsSMul_apply]
  let B₀ : Basis (Fin m ⊕ Fin N) ℝ (Fin k → E) :=
    Basis.ofExactLift (injective_mfderiv_coe_stiefel v) hfg b c _ hs
  -- Listing the normals first and the tangent vectors after them.
  let e : Fin (m + N) ≃ Fin m ⊕ Fin N :=
    (finCongr (Nat.add_comm m N)).trans (finSumFinEquiv.symm.trans (Equiv.sumComm _ _))
  refine ⟨B₀.reindex e.symm, funext fun i ↦ ?_⟩
  rw [Basis.reindex_apply, Equiv.symm_symm]
  -- The tangent vectors are read in `Fin k → E`, which is the tangent space of the model by
  -- definition, so `vecAppend_eq_ite` applies up to unfolding rather than by rewriting.
  refine Eq.trans ?_ (congrFun (Matrix.vecAppend_eq_ite _ _ _) i).symm
  -- The coercions of `B₀` to `Fin k → E` and to the tangent space of the model agree by
  -- definition, so the characterizing lemmas of `ofExactLift` apply up to unfolding.
  by_cases h : (i : ℕ) < N
  · refine Eq.trans ?_ (dite_eq_left_of_eq_true (eq_true h)).symm
    have he : e i = Sum.inr ⟨i, h⟩ := by
      have hi : Fin.cast (Nat.add_comm m N) i = Fin.castAdd m ⟨i, h⟩ := Fin.ext rfl
      simp only [e, Equiv.trans_apply, finCongr_apply, hi, finSumFinEquiv_symm_apply_castAdd,
        Equiv.sumComm_apply, Sum.swap_inl]
    rw [he]
    exact Basis.ofExactLift_inr (injective_mfderiv_coe_stiefel v) hfg b c _ hs _
  · refine Eq.trans ?_ (dite_eq_right_of_eq_false (eq_false h)).symm
    have he : e i = Sum.inl ⟨i - N, by omega⟩ := by
      have hi : Fin.cast (Nat.add_comm m N) i = Fin.natAdd N ⟨i - N, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)
      simp only [e, Equiv.trans_apply, finCongr_apply, hi, finSumFinEquiv_symm_apply_natAdd,
        Equiv.sumComm_apply, Sum.swap_inr]
    rw [he]
    exact Basis.ofExactLift_inl (injective_mfderiv_coe_stiefel v) hfg b c _ hs _

private theorem stiefelTopForm_ne_zero (σ : Fin N ≃ Sym2 (Fin k))
    (hm : k * finrank ℝ E - (k + 1).choose 2 = m)
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) (v : stiefel E k) :
    stiefelTopForm σ O v ≠ 0 := by
  let b := Module.finBasisOfFinrankEq ℝ (TangentSpace 𝓥 v) ((Module.finrank_fin_fun ℝ).trans hm)
  obtain ⟨B, hB⟩ := exists_basis_coe_eq_vecAppend_stiefelNormal σ b
  intro h
  have hb := DFunLike.congr_fun h ⇑b
  rw [stiefelTopForm_apply, ← hB] at hb
  exact ((Module.Ray.someVector O).map_basis_ne_zero_iff B).2
    (Module.Ray.someVector_ne_zero O) hb

/-- The **normal orientation** of the Stiefel manifold `V_k(E)` of orthonormal `k`-frames, for an
orientation `O` of the space `Fin k → E` of `k`-families and an ordering `σ` of the unordered pairs
of indices: a tangent basis `t` at `v` is positive exactly when the normals
`ν_{σ 0} v, …, ν_{σ (N - 1)} v` (`TauCeti.stiefelNormal`) followed by `t`, read in `Fin k → E`,
form a positive basis for `O`
(`Orientation.orientation_eq_orientationAt_stiefelOrientation_iff`). Here `m` is the dimension
`k n - (k + 1).choose 2` of `V_k(E)`, for `n` the dimension of `E`. -/
def _root_.Orientation.stiefelOrientation (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N)))
    (σ : Fin N ≃ Sym2 (Fin k)) (hm : k * finrank ℝ E - (k + 1).choose 2 = m) :
    Manifold.Orientation 𝓥 (stiefel E k) (Fin m) :=
  Manifold.Orientation.ofTopForm ((Module.finrank_fin_fun ℝ).trans hm) (stiefelTopForm σ O)
    (isSmoothForm_stiefelTopForm σ O) (stiefelTopForm_ne_zero σ hm O)

omit [FiniteDimensional ℝ E] in
/-- A volume form positive on the bases of orientation `O` is a positive multiple of the
determinant of any basis of orientation `O`. -/
private theorem exists_pos_someVector_eq_smul_det
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) (e : Basis (Fin (m + N)) ℝ (Fin k → E))
    (he : e.orientation = O) : ∃ r : ℝ, 0 < r ∧ Module.Ray.someVector O = r • e.det := by
  have h : SameRay ℝ e.det (Module.Ray.someVector O) := by
    rw [← ray_eq_iff e.det_ne_zero (Module.Ray.someVector_ne_zero O), Module.Ray.someVector_ray]
    exact he
  obtain ⟨r, hr, h⟩ := h.exists_pos_left e.det_ne_zero (Module.Ray.someVector_ne_zero O)
  exact ⟨r, hr, h.symm⟩

/-- A tangent basis `b` of `V_k(E)` at `v` is positive for the normal orientation of `O` and `σ`
exactly when the normals `ν_{σ 0} v, …, ν_{σ (N - 1)} v` followed by `b`, read in `Fin k → E`
through the derivative of the inclusion, have positive determinant in a basis `e` of
orientation `O`, that is, form a positive basis for `O`. -/
theorem _root_.Orientation.orientation_eq_orientationAt_stiefelOrientation_iff
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) (σ : Fin N ≃ Sym2 (Fin k))
    (hm : k * finrank ℝ E - (k + 1).choose 2 = m) {v : stiefel E k}
    (b : Basis (Fin m) ℝ (TangentSpace 𝓥 v)) (e : Basis (Fin (m + N)) ℝ (Fin k → E))
    (he : e.orientation = O) :
    b.orientation = (O.stiefelOrientation σ hm).orientationAt v ↔
      0 < e.det (Matrix.vecAppend (Nat.add_comm m N)
        (fun i ↦ stiefelNormal (σ i) (v : Fin k → E))
        fun i ↦ mfderiv 𝓥 𝓘(ℝ, Fin k → E) ((↑) : stiefel E k → Fin k → E) v (b i)) := by
  rw [Orientation.stiefelOrientation,
    Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff, stiefelTopForm_apply]
  obtain ⟨r, hr, h⟩ := exists_pos_someVector_eq_smul_det O e he
  -- Scalar multiples of alternating maps are evaluated pointwise.
  have key (w : Fin (m + N) → Fin k → E) : Module.Ray.someVector O w = r * e.det w :=
    (congrArg (fun f ↦ f w) h).trans rfl
  rw [key]
  exact mul_pos_iff_of_pos_left hr

/-- The normals followed by the image of a tangent basis have nonzero determinant in any basis of
the space of `k`-families. -/
private theorem det_vecAppend_stiefelNormal_ne_zero (σ : Fin N ≃ Sym2 (Fin k)) {v : stiefel E k}
    (b : Basis (Fin m) ℝ (TangentSpace 𝓥 v)) (e : Basis (Fin (m + N)) ℝ (Fin k → E)) :
    e.det (Matrix.vecAppend (Nat.add_comm m N) (fun i ↦ stiefelNormal (σ i) (v : Fin k → E))
      fun i ↦ mfderiv 𝓥 𝓘(ℝ, Fin k → E) ((↑) : stiefel E k → Fin k → E) v (b i)) ≠ 0 := by
  obtain ⟨B, hB⟩ := exists_basis_coe_eq_vecAppend_stiefelNormal σ b
  rw [← hB]
  exact (e.isUnit_det B).ne_zero

/-- A tangent basis `b` of `V_k(E)` at `v` is negative for the normal orientation of `O` and `σ`
exactly when the normals `ν_{σ 0} v, …, ν_{σ (N - 1)} v` followed by `b` have negative determinant
in a basis `e` of orientation `O`. -/
theorem _root_.Orientation.orientation_eq_neg_orientationAt_stiefelOrientation_iff
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) (σ : Fin N ≃ Sym2 (Fin k))
    (hm : k * finrank ℝ E - (k + 1).choose 2 = m) {v : stiefel E k}
    (b : Basis (Fin m) ℝ (TangentSpace 𝓥 v)) (e : Basis (Fin (m + N)) ℝ (Fin k → E))
    (he : e.orientation = O) :
    b.orientation = -(O.stiefelOrientation σ hm).orientationAt v ↔
      e.det (Matrix.vecAppend (Nat.add_comm m N)
        (fun i ↦ stiefelNormal (σ i) (v : Fin k → E))
        fun i ↦ mfderiv 𝓥 𝓘(ℝ, Fin k → E) ((↑) : stiefel E k → Fin k → E) v (b i)) < 0 := by
  rw [← _root_.Orientation.ne_iff_eq_neg _ _
      (((O.stiefelOrientation σ hm).finrank_tangentSpace_eq v).symm),
    Ne, O.orientation_eq_orientationAt_stiefelOrientation_iff σ hm b e he, not_lt]
  exact (det_vecAppend_stiefelNormal_ne_zero σ b e).le_iff_lt

omit [FiniteDimensional ℝ E] in
/-- The volume form of `-O` is a negative multiple of that of `O`. -/
private theorem exists_pos_someVector_neg_eq_smul
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) :
    ∃ r : ℝ, 0 < r ∧ Module.Ray.someVector (-O) = r • -Module.Ray.someVector O := by
  have h : SameRay ℝ (-Module.Ray.someVector O) (Module.Ray.someVector (-O)) := by
    rw [← ray_eq_iff (neg_ne_zero.2 (Module.Ray.someVector_ne_zero O))
      (Module.Ray.someVector_ne_zero (-O)),
      ← neg_rayOfNeZero ℝ (Module.Ray.someVector O) (Module.Ray.someVector_ne_zero O),
      Module.Ray.someVector_ray, Module.Ray.someVector_ray]
  obtain ⟨r, hr, h⟩ := h.exists_pos_left (neg_ne_zero.2 (Module.Ray.someVector_ne_zero O))
    (Module.Ray.someVector_ne_zero (-O))
  exact ⟨r, hr, h.symm⟩

/-- Reversing the orientation of the space of `k`-families reverses the normal orientation of the
Stiefel manifold. -/
@[simp]
theorem _root_.Orientation.stiefelOrientation_neg
    (O : _root_.Orientation ℝ (Fin k → E) (Fin (m + N))) (σ : Fin N ≃ Sym2 (Fin k))
    (hm : k * finrank ℝ E - (k + 1).choose 2 = m) :
    (-O).stiefelOrientation σ hm = -O.stiefelOrientation σ hm := by
  ext v
  have hcard := ((O.stiefelOrientation σ hm).finrank_tangentSpace_eq v).symm
  let b := Module.finBasisOfFinrankEq ℝ (TangentSpace 𝓥 v) ((Module.finrank_fin_fun ℝ).trans hm)
  obtain ⟨r, hr, hO⟩ := exists_pos_someVector_neg_eq_smul O
  -- The top form of `-O` is `-r` times that of `O`.
  have hφ : stiefelTopForm σ (-O) v b = -(r * stiefelTopForm σ O v b) := by
    rw [stiefelTopForm_apply, stiefelTopForm_apply, hO, smul_apply, neg_apply, smul_eq_mul,
      mul_neg]
  have hne : stiefelTopForm σ O v b ≠ 0 :=
    ((stiefelTopForm σ O v).map_basis_ne_zero_iff b).2 (stiefelTopForm_ne_zero σ hm O v)
  have h₁ : b.orientation = ((-O).stiefelOrientation σ hm).orientationAt v ↔
      stiefelTopForm σ O v b < 0 := by
    rw [Orientation.stiefelOrientation,
      Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff, hφ, neg_pos]
    exact ⟨fun h ↦ neg_of_mul_neg_right h hr.le, fun h ↦ mul_neg_of_pos_of_neg hr h⟩
  have h₂ : b.orientation = (O.stiefelOrientation σ hm).orientationAt v ↔
      0 < stiefelTopForm σ O v b := by
    rw [Orientation.stiefelOrientation,
      Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff]
  rw [Manifold.Orientation.orientationAt_neg]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [← h₁.2 hlt]
    exact ((b.orientation).eq_or_eq_neg _ hcard).resolve_left fun h ↦
      (h₂.1 h).not_gt hlt
  · have hb := ((b.orientation).eq_or_eq_neg (((-O).stiefelOrientation σ hm).orientationAt v)
      hcard).resolve_left fun h ↦ (h₁.1 h).not_gt hgt
    rw [← h₂.2 hgt, hb]
    exact (neg_neg (G := _root_.Orientation ℝ (TangentSpace 𝓥 v) (Fin m)) _).symm

/-! ### Orthonormal two-frames -/

section Two

variable {n : ℕ} [Fact (finrank ℝ E = n + 1 + 1)]

/-- The order `s(0, 0)`, `s(1, 1)`, `s(0, 1)` of the unordered pairs of indices of two-frames. -/
private def stiefelTwoNormalOrder : Fin 3 ≃ Sym2 (Fin 2) :=
  Equiv.ofBijective ![s(0, 0), s(1, 1), s(0, 1)] (by decide)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1 + 1)] in
/-- For two-frames, the normals in the order of `stiefelTwoNormalOrder` are
`(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)`. -/
private theorem vecAppend_stiefelTwoNormal (v : Fin 2 → E) {m : ℕ} (t : Fin m → Fin 2 → E) :
    Matrix.vecAppend (Nat.add_comm m 3) (fun i ↦ stiefelNormal (stiefelTwoNormalOrder i) v) t =
      Fin.cons ![v 0, 0] (Fin.cons ![0, v 1] (Fin.cons ![v 1, v 0] t)) := by
  have h (s : Sym2 (Fin 2)) (l : Fin 2) :
      stiefelNormal s v l = ∑ j, if s(l, j) = s then v j else 0 := stiefelNormal_apply s v l
  funext i
  refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i) i
  · rw [Fin.cons_zero]
    funext l
    fin_cases l <;> simp [h, stiefelTwoNormalOrder]
  · rw [Fin.cons_succ, Fin.cons_zero]
    funext l
    fin_cases l <;> simp [Matrix.vecAppend_eq_ite, h, stiefelTwoNormalOrder]
  · rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_zero]
    funext l
    fin_cases l <;> simp [Matrix.vecAppend_eq_ite, h, stiefelTwoNormalOrder,
      Nat.mod_eq_of_lt (show 2 < m + 3 by omega)]
  · simp only [Matrix.vecAppend_eq_ite, Fin.cons_succ]
    split_ifs with hi
    · simp at hi
      omega
    · exact congrArg t (Fin.ext (by simp))

/-- The space of pairs of vectors of `E` has dimension `2 n + 4`. -/
private theorem finrank_fin_two_fun : finrank ℝ (Fin 2 → E) = 2 * n + 4 := by
  rw [Module.finrank_pi_fintype, Fin.sum_univ_two, Fact.out (p := finrank ℝ E = n + 1 + 1)]
  ring

omit [FiniteDimensional ℝ E] in
/-- The manifold of orthonormal two-frames of `E` has dimension `2 n + 1`. -/
private theorem stiefelTwo_dim : 2 * finrank ℝ E - (2 + 1).choose 2 = 2 * n + 1 := by
  rw [Fact.out (p := finrank ℝ E = n + 1 + 1)]
  simp only [Nat.choose, Nat.reduceAdd]
  omega

omit [Fact (finrank ℝ E = n + 1 + 1)] in
/-- The top form of the normal orientation of two-frames, evaluated on a family `t` of tangent
vectors: the volume of the normals `(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)` followed by `t`. -/
private theorem stiefelTopForm_stiefelTwoNormalOrder_apply
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) (v : stiefel E 2)
    (t : Fin (2 * n + 1) →
      TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v) :
    stiefelTopForm (m := 2 * n + 1) stiefelTwoNormalOrder O v t =
      Module.Ray.someVector O (Fin.cons ![(v : Fin 2 → E) 0, 0]
        (Fin.cons ![0, (v : Fin 2 → E) 1] (Fin.cons ![(v : Fin 2 → E) 1, (v : Fin 2 → E) 0]
          fun i ↦ mfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 𝓘(ℝ, Fin 2 → E)
            ((↑) : stiefel E 2 → Fin 2 → E) v (t i)))) := by
  rw [stiefelTopForm_apply]
  exact congrArg _ (vecAppend_stiefelTwoNormal _ _)

/-- The **normal orientation** of the Stiefel manifold of orthonormal two-frames of `E`, for an
orientation `O` of the space `Fin 2 → E` of pairs: a tangent basis `t` at `v` is positive exactly
when the normals `(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)` followed by `t`, read in `Fin 2 → E`, form a
positive basis for `O` (`Orientation.orientation_eq_orientationAt_stiefelTwoOrientation_iff`).
It is `O.stiefelOrientation` for the order `s(0, 0)`, `s(1, 1)`, `s(0, 1)` of the normals. -/
def _root_.Orientation.stiefelTwoOrientation
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    Manifold.Orientation 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) (stiefel E 2)
      (Fin (2 * n + 1)) :=
  O.stiefelOrientation (m := 2 * n + 1) (N := 3) stiefelTwoNormalOrder stiefelTwo_dim

/-- A tangent basis `b` of the Stiefel manifold at `v` is positive for the normal orientation of
`O` exactly when the normals `(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)` followed by `b`, read in `Fin 2 → E`
through the derivative of the inclusion, have positive determinant in a basis `e` of
orientation `O`, that is, form a positive basis for `O`. -/
theorem _root_.Orientation.orientation_eq_orientationAt_stiefelTwoOrientation_iff
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) {v : stiefel E 2}
    (b : Basis (Fin (2 * n + 1)) ℝ
      (TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v))
    (e : Basis (Fin (2 * n + 4)) ℝ (Fin 2 → E)) (he : e.orientation = O) :
    b.orientation = O.stiefelTwoOrientation.orientationAt v ↔
      0 < e.det (Fin.cons ![(v : Fin 2 → E) 0, 0] (Fin.cons ![0, (v : Fin 2 → E) 1]
        (Fin.cons ![(v : Fin 2 → E) 1, (v : Fin 2 → E) 0] fun i ↦
          mfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 𝓘(ℝ, Fin 2 → E)
            ((↑) : stiefel E 2 → Fin 2 → E) v (b i)))) := by
  rw [Orientation.stiefelTwoOrientation,
    O.orientation_eq_orientationAt_stiefelOrientation_iff (m := 2 * n + 1) (N := 3) _ _ b e he]
  exact iff_of_eq (congrArg (fun w ↦ 0 < e.det w) (vecAppend_stiefelTwoNormal _ _))

/-- A tangent basis `b` of the Stiefel manifold at `v` is negative for the normal orientation of
`O` exactly when the normals `(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)` followed by `b` have negative
determinant in a basis `e` of orientation `O`. -/
theorem _root_.Orientation.orientation_eq_neg_orientationAt_stiefelTwoOrientation_iff
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) {v : stiefel E 2}
    (b : Basis (Fin (2 * n + 1)) ℝ
      (TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v))
    (e : Basis (Fin (2 * n + 4)) ℝ (Fin 2 → E)) (he : e.orientation = O) :
    b.orientation = -O.stiefelTwoOrientation.orientationAt v ↔
      e.det (Fin.cons ![(v : Fin 2 → E) 0, 0] (Fin.cons ![0, (v : Fin 2 → E) 1]
        (Fin.cons ![(v : Fin 2 → E) 1, (v : Fin 2 → E) 0] fun i ↦
          mfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 𝓘(ℝ, Fin 2 → E)
            ((↑) : stiefel E 2 → Fin 2 → E) v (b i)))) < 0 := by
  rw [Orientation.stiefelTwoOrientation,
    O.orientation_eq_neg_orientationAt_stiefelOrientation_iff (m := 2 * n + 1) (N := 3) _ _ b e he]
  exact iff_of_eq (congrArg (fun w ↦ e.det w < 0) (vecAppend_stiefelTwoNormal _ _))

/-- Reversing the orientation of the space of pairs reverses the normal orientation of the
Stiefel manifold of two-frames. -/
@[simp]
theorem _root_.Orientation.stiefelTwoOrientation_neg
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    (-O).stiefelTwoOrientation = -O.stiefelTwoOrientation :=
  O.stiefelOrientation_neg (m := 2 * n + 1) (N := 3) _ _

/-! ### The frame reflection -/

/-- The model space of the Stiefel manifold of orthonormal two-frames of `E`. -/
local notation "𝓢" => 𝓘(ℝ, Fin (2 * finrank ℝ E - Nat.choose (2 + 1) 2) → ℝ)

/-- The linear map `(a, b) ↦ (a, -b)` of the space of pairs. -/
private def frameFlip : (Fin 2 → E) →L[ℝ] Fin 2 → E :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 1]

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1 + 1)] in
private theorem frameFlip_apply (w : Fin 2 → E) : frameFlip w = ![w 0, -w 1] := by
  ext i : 1
  fin_cases i <;> rfl

omit [Fact (finrank ℝ E = n + 1 + 1)] in
/-- The map `(a, b) ↦ (a, -b)` has determinant `(-1) ^ finrank ℝ E`. -/
private theorem det_frameFlip :
    LinearMap.det (frameFlip (E := E) : (Fin 2 → E) →ₗ[ℝ] Fin 2 → E) = (-1) ^ finrank ℝ E := by
  have h : (frameFlip (E := E) : (Fin 2 → E) →ₗ[ℝ] Fin 2 → E) =
      LinearMap.pi fun i ↦ (![LinearMap.id, -LinearMap.id] i : E →ₗ[ℝ] E).comp
        (LinearMap.proj i) := by
    refine LinearMap.ext fun w ↦ funext fun i ↦ ?_
    fin_cases i <;> simp [frameFlip_apply]
  rw [h, LinearMap.det_pi, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.det_id, one_mul]
  rw [← neg_one_smul ℝ (LinearMap.id : E →ₗ[ℝ] E), LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- A top-degree alternating form of the space of pairs is multiplied by `(-1) ^ finrank ℝ E`
under `(a, b) ↦ (a, -b)`. -/
private theorem alternatingMap_frameFlip_comp
    (f : (Fin 2 → E) [⋀^Fin (2 * n + 4)]→ₗ[ℝ] ℝ) (w : Fin (2 * n + 4) → Fin 2 → E) :
    f (frameFlip ∘ w) = (-1) ^ finrank ℝ E * f w := by
  let e := Module.finBasisOfFinrankEq ℝ (Fin 2 → E) (finrank_fin_two_fun (n := n))
  -- Scalar multiples of alternating maps are evaluated pointwise.
  have hf (u : Fin (2 * n + 4) → Fin 2 → E) : f u = f e * e.det u :=
    (congrArg (fun g ↦ g u) (f.eq_smul_basis_det e)).trans rfl
  have hdet := e.det_comp (frameFlip (E := E) : (Fin 2 → E) →ₗ[ℝ] Fin 2 → E) w
  rw [det_frameFlip, ContinuousLinearMap.coe_coe] at hdet
  rw [hf, hf w, hdet]
  ring

/-- The derivative of the frame reflection, read in `Fin 2 → E`, is `(a, b) ↦ (a, -b)`. -/
private theorem mfderiv_coe_mfderiv_stiefelTwoReflection (w : stiefel E 2)
    (t : TangentSpace 𝓢 w) :
    mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) (stiefelTwoReflection w)
        (mfderiv 𝓢 𝓢 stiefelTwoReflection w t) =
      frameFlip (mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) w t) := by
  have hι (w' : stiefel E 2) : MDifferentiableAt 𝓢 𝓘(ℝ, Fin 2 → E)
      ((↑) : stiefel E 2 → Fin 2 → E) w' :=
    ((contMDiff_coe_stiefel E 2 (r := 1)) w').mdifferentiableAt one_ne_zero
  have hK : MDifferentiableAt 𝓢 𝓢 (stiefelTwoReflection (E := E)) w :=
    ((contMDiff_stiefelTwoReflection (r := 1)) w).mdifferentiableAt one_ne_zero
  have hcomp : ((↑) : stiefel E 2 → Fin 2 → E) ∘ stiefelTwoReflection =
      frameFlip ∘ ((↑) : stiefel E 2 → Fin 2 → E) := by
    funext w'
    simp [frameFlip_apply]
  rw [← mfderiv_comp_apply w (hι _) hK, hcomp,
    mfderiv_comp_apply w frameFlip.mdifferentiableAt (hι w), ContinuousLinearMap.mfderiv_eq]
  -- Both sides now read `frameFlip (mfderiv ... w t)`; they differ only in whether the tangent
  -- space of the model `𝓘(ℝ, Fin 2 → E)` is written as `TangentSpace` or as `Fin 2 → E`, which
  -- agree by definition.
  rfl

/-- The frame reflection pulls the top form of the normal orientation back to `(-1)ⁿ⁺¹` times
itself: the normals `(u, 0)`, `(0, v)`, `(v, u)` at `(u, v)` are carried by `(a, b) ↦ (a, -b)` to
`(u, 0)`, `(0, -v)`, `-(-v, u)`, the normals at `(u, -v)` up to the sign of the third. -/
private theorem mpullback_stiefelTwoReflection_stiefelTopForm
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) (w : stiefel E 2) :
    mpullback 𝓢 𝓢 stiefelTwoReflection (stiefelTopForm (m := 2 * n + 1) stiefelTwoNormalOrder O)
        w =
      (-(-1) ^ finrank ℝ E : ℝ) • stiefelTopForm (m := 2 * n + 1) stiefelTwoNormalOrder O w := by
  classical
  ext t
  rw [mpullback_apply, stiefelTopForm_stiefelTwoNormalOrder_apply,
    ContinuousAlternatingMap.smul_apply, stiefelTopForm_stiefelTwoNormalOrder_apply]
  simp only [mfderiv_coe_mfderiv_stiefelTwoReflection]
  set f := Module.Ray.someVector O
  set τ := fun i ↦ mfderiv 𝓢 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) w (t i)
  -- The normals at `(u, -v)` are the images of those at `(u, v)`, up to the sign of the third.
  have h₁ : (![(w : Fin 2 → E) 0, 0] : Fin 2 → E) = frameFlip ![(w : Fin 2 → E) 0, 0] := by
    simp [frameFlip_apply]
  have h₂ : (![0, -(w : Fin 2 → E) 1] : Fin 2 → E) = frameFlip ![0, (w : Fin 2 → E) 1] := by
    simp [frameFlip_apply]
  have h₃ : (![-(w : Fin 2 → E) 1, (w : Fin 2 → E) 0] : Fin 2 → E) =
      -frameFlip ![(w : Fin 2 → E) 1, (w : Fin 2 → E) 0] := by
    simp [frameFlip_apply]
  have hneg (x y z : Fin 2 → E) (r : Fin (2 * n + 1) → Fin 2 → E) :
      f (Fin.cons x (Fin.cons y (Fin.cons (-z) r))) =
        -f (Fin.cons x (Fin.cons y (Fin.cons z r))) := by
    -- Evaluating `f` on `Fin.cons` is, by definition, evaluating its iterated `curryLeft`.
    change ((f.curryLeft x).curryLeft y).curryLeft (-z) r =
      -((f.curryLeft x).curryLeft y).curryLeft z r
    rw [map_neg, neg_apply]
  have hfam (x y z : Fin 2 → E)
      (r : Fin (2 * n + 1) → TangentSpace 𝓘(ℝ, Fin 2 → E) (w : Fin 2 → E)) :
      (Fin.cons (frameFlip x) (Fin.cons (frameFlip y) (Fin.cons (frameFlip z)
        (frameFlip ∘ r))) : Fin (2 * n + 1 + 1 + 1 + 1) → Fin 2 → E) =
        frameFlip ∘ Fin.cons x (Fin.cons y (Fin.cons z r)) := by
    funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i) i) i
  have hdet := alternatingMap_frameFlip_comp f
    (Fin.cons ![(w : Fin 2 → E) 0, 0] (Fin.cons ![0, (w : Fin 2 → E) 1]
      (Fin.cons ![(w : Fin 2 → E) 1, (w : Fin 2 → E) 0] τ)))
  rw [coe_stiefelTwoReflection]
  -- The `set` above could not abstract `τ` inside `fun i ↦ frameFlip (mfderiv ... w (t i))`, the
  -- form produced by `mfderiv_coe_mfderiv_stiefelTwoReflection`; that family is `frameFlip ∘ τ`
  -- once `Function.comp` and the local definition `τ` are unfolded.
  change f (Fin.cons ![(w : Fin 2 → E) 0, 0] (Fin.cons ![0, -(w : Fin 2 → E) 1]
    (Fin.cons ![-(w : Fin 2 → E) 1, (w : Fin 2 → E) 0] (frameFlip ∘ τ)))) = _
  conv_lhs => rw [h₁, h₂, h₃, hneg, hfam]
  rw [hdet, smul_eq_mul]
  ring

/-- **The frame reflection in odd dimension.** When `n` is odd, the frame reflection
`(u, v) ↦ (u, -v)` of the orthonormal two-frames of the `(n + 2)`-dimensional space `E` preserves
the normal orientation `O.stiefelTwoOrientation`. -/
theorem isOrientationPreservingAt_stiefelTwoReflection (hn : Odd n)
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) (w : stiefel E 2) :
    IsOrientationPreservingAt O.stiefelTwoOrientation O.stiefelTwoOrientation
      stiefelTwoReflection w := by
  refine isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _ (c := 1)
    one_pos ?_
  have hc : (-(-1) ^ finrank ℝ E : ℝ) = 1 := by
    rw [(Fact.out : finrank ℝ E = n + 1 + 1), pow_succ, pow_succ, hn.neg_one_pow]
    norm_num
  rw [mpullback_stiefelTwoReflection_stiefelTopForm, hc]

/-- **The frame reflection in even dimension.** When `n` is even, the frame reflection
`(u, v) ↦ (u, -v)` of the orthonormal two-frames of the `(n + 2)`-dimensional space `E` reverses
the normal orientation `O.stiefelTwoOrientation`. -/
theorem isOrientationReversingAt_stiefelTwoReflection (hn : Even n)
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) (w : stiefel E 2) :
    IsOrientationReversingAt O.stiefelTwoOrientation O.stiefelTwoOrientation
      stiefelTwoReflection w := by
  refine isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _ (c := -1)
    (by norm_num) ?_
  have hc : (-(-1) ^ finrank ℝ E : ℝ) = -1 := by
    rw [(Fact.out : finrank ℝ E = n + 1 + 1), pow_succ, pow_succ, hn.neg_one_pow]
    norm_num
  rw [mpullback_stiefelTwoReflection_stiefelTopForm, hc]

end Two

end TauCeti
