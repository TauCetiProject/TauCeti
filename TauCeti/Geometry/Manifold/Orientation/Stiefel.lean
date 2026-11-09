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

/-!
# The normal orientation of the Stiefel manifold of orthonormal two-frames

Let `E` be a real inner product space of dimension `n + 2`. The Stiefel manifold
`TauCeti.stiefel E 2` of orthonormal pairs `(v₀, v₁)` is the unit tangent bundle of the unit
sphere of `E`, a manifold of dimension `2 n + 1`. It is the regular level set of the Gram map
`(v₀, v₁) ↦ (⟪v₀, v₀⟫, ⟪v₁, v₁⟫, ⟪v₀, v₁⟫)` in the space `Fin 2 → E` of pairs, and the gradients of
these three functions give three normal vectors at every frame,

`(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)`,

which together with the tangent space span `Fin 2 → E`. So an orientation `O` of the space of
pairs orients the Stiefel manifold, exactly as an orientation of `E` orients its unit sphere by
the outward normal: a tangent basis `t₁, …, t₂ₙ₊₁` at `v` is positive for the *normal orientation*
`O.stiefelTwoOrientation` exactly when

`(v₀, 0), (0, v₁), (v₁, v₀), t₁, …, t₂ₙ₊₁`,

with the tangent vectors read in `Fin 2 → E` through the derivative of the inclusion, is a positive
basis for `O` (`Orientation.orientation_eq_orientationAt_stiefelTwoOrientation_iff`). Reversing `O`
reverses it (`Orientation.stiefelTwoOrientation_neg`).

The orientation is constructed, as for the sphere, from a nowhere-vanishing continuous top form:
the pullback to the Stiefel manifold of the contraction of a volume form of `Fin 2 → E` with the
three normal vector fields. It does not vanish because the three normals are sent by the
derivative of the Gram map to the three coordinate directions, while the tangent vectors are sent
to zero.

This orients the domain `T¹Sⁿ⁺¹ × S¹` of the map `((u, v), θ) ↦ (u, u cos θ + v sin θ)` of
Barraud–Damian–Humilière–Oancea, Proposition 6.17, whose degree is a signed count of preimages for
these orientations.

## Main declarations

* `Orientation.stiefelTwoOrientation`: the normal orientation of the Stiefel manifold of
  orthonormal two-frames.
* `Orientation.orientation_eq_orientationAt_stiefelTwoOrientation_iff`,
  `Orientation.orientation_eq_neg_orientationAt_stiefelTwoOrientation_iff`: a tangent basis is
  positive (negative) exactly when the three normals followed by it form a positive (negative)
  basis of `Fin 2 → E`.
* `Orientation.stiefelTwoOrientation_neg`: reversing the orientation of `Fin 2 → E` reverses the
  normal orientation.

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

open Module Set
open scoped Manifold RealInnerProductSpace

namespace TauCeti

-- `FiniteDimensional` follows from the dimension hypothesis, but is the instance through which
-- the manifold structure of the Stiefel manifold is stated.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1 + 1)]

/-- The space of pairs of vectors of `E` has dimension `2 n + 4`. -/
private theorem finrank_fin_two_fun : finrank ℝ (Fin 2 → E) = 2 * n + 4 := by
  rw [Module.finrank_pi_fintype, Fin.sum_univ_two, Fact.out (p := finrank ℝ E = n + 1 + 1)]
  ring

omit [FiniteDimensional ℝ E] in
/-- The model space of the Stiefel manifold of orthonormal two-frames has dimension `2 n + 1`. -/
private theorem finrank_stiefel_two_model :
    finrank ℝ (Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) = 2 * n + 1 := by
  rw [Module.finrank_fin_fun, Fact.out (p := finrank ℝ E = n + 1 + 1)]
  norm_num [Nat.choose]
  omega

/-- The three normals `(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)` at a pair `v`, the gradients of
`⟪v₀, v₀⟫ / 2`, `⟪v₁, v₁⟫ / 2` and `⟪v₀, v₁⟫`, followed by a family `t`. -/
private def stiefelNormalCons (v : Fin 2 → E) {m : ℕ} (t : Fin m → Fin 2 → E) :
    Fin (m + 1 + 1 + 1) → Fin 2 → E :=
  Fin.cons ![v 0, 0] (Fin.cons ![0, v 1] (Fin.cons ![v 1, v 0] t))

/-- A top form of the space of pairs, positive on the bases of orientation `O`. -/
private def pairVolume (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    (Fin 2 → E) [⋀^Fin (2 * n + 4)]→L[ℝ] ℝ :=
  AlternatingMap.toContinuousAlternatingMap
    (O.someBasis (by rw [Fintype.card_fin, finrank_fin_two_fun (n := n)])).det

/-- The contraction of `pairVolume O` with the three normal vector fields, a form of degree
`2 n + 1` on the space of pairs. -/
private def stiefelNormalForm (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    (Fin 2 → E) → (Fin 2 → E) [⋀^Fin (2 * n + 1)]→L[ℝ] ℝ := fun x ↦
  (((pairVolume O).curryLeft ![x 0, 0]).curryLeft ![0, x 1]).curryLeft ![x 1, x 0]

private theorem stiefelNormalForm_apply (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)))
    (x : Fin 2 → E) (t : Fin (2 * n + 1) → Fin 2 → E) :
    stiefelNormalForm O x t =
      (O.someBasis (by rw [Fintype.card_fin, finrank_fin_two_fun (n := n)])).det
        (stiefelNormalCons x t) := by
  rw [stiefelNormalForm, ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    pairVolume, AlternatingMap.coe_toContinuousAlternatingMap]
  -- `Matrix.vecCons`, produced by `curryLeft`, is `Fin.cons` by definition.
  rfl

/-- `stiefelNormalForm O`, as a form on the space of pairs. -/
private def stiefelNormalRoughForm (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    RoughForm 𝓘(ℝ, Fin 2 → E) (Fin 2 → E) ℝ (2 * n + 1) :=
  stiefelNormalForm O

private theorem continuous_stiefelNormalForm
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    Continuous (stiefelNormalForm O) := by
  -- Each normal is a continuous linear function of the pair.
  have hpair (f g : (Fin 2 → E) → E) (hf : Continuous f) (hg : Continuous g) :
      Continuous fun x ↦ (![f x, g x] : Fin 2 → E) :=
    continuous_pi fun i ↦ by fin_cases i <;> simpa
  have h0 := continuous_apply (A := fun _ : Fin 2 ↦ E) 0
  have h1 := continuous_apply (A := fun _ : Fin 2 ↦ E) 1
  have c₁ : Continuous fun x : Fin 2 → E ↦ (pairVolume O).curryLeft ![x 0, 0] :=
    (pairVolume O).curryLeft.continuous.comp (hpair _ _ h0 continuous_const)
  have c₂ : Continuous fun x : Fin 2 → E ↦
      ((pairVolume O).curryLeft ![x 0, 0]).curryLeft ![0, x 1] :=
    (ContinuousAlternatingMap.curryLeftLI.continuous.comp c₁).clm_apply
      (hpair _ _ continuous_const h1)
  exact (ContinuousAlternatingMap.curryLeftLI.continuous.comp c₂).clm_apply (hpair _ _ h1 h0)

/-- The top form of the Stiefel manifold: the pullback along the inclusion of the contraction of
a volume form of the space of pairs with the three normal vector fields. -/
private def stiefelTopForm (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    RoughForm 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) (stiefel E 2) ℝ
      (2 * n + 1) :=
  mpullback _ 𝓘(ℝ, Fin 2 → E) ((↑) : stiefel E 2 → Fin 2 → E) (stiefelNormalRoughForm O)

private theorem stiefelTopForm_apply (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)))
    (v : stiefel E 2)
    (t : Fin (2 * n + 1) →
      TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v) :
    stiefelTopForm O v t =
      (O.someBasis (by rw [Fintype.card_fin, finrank_fin_two_fun (n := n)])).det
        (stiefelNormalCons (v : Fin 2 → E) fun i ↦
          mfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 𝓘(ℝ, Fin 2 → E)
            ((↑) : stiefel E 2 → Fin 2 → E) v (t i)) := by
  rw [stiefelTopForm, mpullback_apply]
  exact stiefelNormalForm_apply O _ _

private theorem isSmoothForm_stiefelTopForm
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    IsSmoothForm 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 0 (stiefelTopForm O) :=
  (isSmoothForm_modelSpace_iff.2 (contDiff_zero.2 (continuous_stiefelNormalForm O))).mpullback
    (contMDiff_coe_stiefel E 2)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1 + 1)] in
/-- At an orthonormal pair `v`, the three normals followed by a linearly independent family of
the kernel of the derivative of the Gram map are linearly independent: the derivative of the
Gram map sends the normals to `2 • s(0, 0)`, `2 • s(1, 1)` and `2 • s(0, 1)` and the family to
zero. -/
private theorem linearIndependent_stiefelNormalCons {v : Fin 2 → E} (hv : v ∈ stiefel E 2)
    {m : ℕ} {t : Fin m → Fin 2 → E} (ht : LinearIndependent ℝ t)
    (hker : ∀ i, gramSym2Deriv E 2 v (t i) = 0) :
    LinearIndependent ℝ (stiefelNormalCons v t) := by
  obtain ⟨h₀, h₁, h₀₁⟩ := mem_stiefel_two_iff.1 hv
  have h₁₀ : ⟪v 1, v 0⟫ = 0 := by rw [real_inner_comm, h₀₁]
  -- The coordinate `s(i, j)` of the derivative of the Gram map, as a linear functional.
  let D (i j : Fin 2) : (Fin 2 → E) →ₗ[ℝ] ℝ :=
    (LinearMap.proj s(i, j)).comp (gramSym2Deriv E 2 v).toLinearMap
  have hD (i j : Fin 2) (a : Fin 2 → E) : D i j a = ⟪v i, a j⟫ + ⟪a i, v j⟫ :=
    gramSym2Deriv_apply_mk v a i j
  -- A vector on which a functional vanishing on a family is nonzero is not in its span.
  have notMem {k : ℕ} (f : (Fin 2 → E) →ₗ[ℝ] ℝ) {x : Fin 2 → E} {s : Fin k → Fin 2 → E}
      (hx : f x ≠ 0) (hs : ∀ i, f (s i) = 0) : x ∉ Submodule.span ℝ (range s) := fun h ↦
    hx (LinearMap.mem_ker.1
      (Submodule.span_le.2 (range_subset_iff.2 fun i ↦ LinearMap.mem_ker.2 (hs i)) h))
  have hDt (i j : Fin 2) (l : Fin m) : D i j (t l) = 0 := by
    simp only [D, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hker, LinearMap.proj_apply,
      Pi.zero_apply]
  refine (((ht.finCons (x := ![v 1, v 0])
    (notMem (D 0 1) ?_ (hDt 0 1))).finCons
    (x := ![0, v 1]) (notMem (D 1 1) ?_ fun l ↦ ?_)).finCons
    (x := ![v 0, 0]) (notMem (D 0 0) ?_ fun l ↦ ?_))
  · simp [hD, h₀, h₁]
  · simp [hD, h₁]
  · cases l using Fin.cases with
    | zero => simp [hD, h₀₁, h₁₀]
    | succ l => simpa using hDt 1 1 l
  · simp [hD, h₀]
  · cases l using Fin.cases with
    | zero => simp [hD]
    | succ l =>
      cases l using Fin.cases with
      | zero => simp [hD, h₀₁, h₁₀]
      | succ l => simpa using hDt 0 0 l

/-- The three normals followed by the image of a tangent basis form a basis of the space of pairs:
the determinant of any basis does not vanish on them. -/
private theorem isUnit_det_stiefelNormalCons (v : stiefel E 2)
    (b : Basis (Fin (2 * n + 1)) ℝ
      (TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v))
    (e : Basis (Fin (2 * n + 4)) ℝ (Fin 2 → E)) :
    IsUnit (e.det (stiefelNormalCons (v : Fin 2 → E) fun i ↦
      mfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 𝓘(ℝ, Fin 2 → E)
        ((↑) : stiefel E 2 → Fin 2 → E) v (b i))) := by
  have hli := linearIndependent_stiefelNormalCons v.2
    (b.linearIndependent.map' _ (LinearMap.ker_eq_bot_of_injective
      (injective_mfderiv_coe_stiefel v)))
    fun i ↦ by
      have h := LinearMap.mem_range_self (mfderiv
        𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 𝓘(ℝ, Fin 2 → E)
        ((↑) : stiefel E 2 → Fin 2 → E) v).toLinearMap (b i)
      rw [range_mfderiv_coe_stiefel] at h
      exact LinearMap.mem_ker.1 h
  exact e.is_basis_iff_det.1 ⟨hli, hli.span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, finrank_fin_two_fun (n := n)])⟩

private theorem stiefelTopForm_ne_zero (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4)))
    (v : stiefel E 2) : stiefelTopForm O v ≠ 0 := by
  let b := Module.finBasisOfFinrankEq ℝ
    (TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v)
    (by exact finrank_stiefel_two_model (E := E) (n := n))
  intro h
  have hb := DFunLike.congr_fun h ⇑b
  rw [stiefelTopForm_apply] at hb
  exact (isUnit_det_stiefelNormalCons v b _).ne_zero hb

/-- The **normal orientation** of the Stiefel manifold of orthonormal two-frames of `E`, for an
orientation `O` of the space `Fin 2 → E` of pairs: a tangent basis `t` at `v` is positive exactly
when the normals `(v₀, 0)`, `(0, v₁)`, `(v₁, v₀)` followed by `t`, read in `Fin 2 → E`, form a
positive basis for `O` (`Orientation.orientation_eq_orientationAt_stiefelTwoOrientation_iff`). -/
def _root_.Orientation.stiefelTwoOrientation
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    Manifold.Orientation 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) (stiefel E 2)
      (Fin (2 * n + 1)) :=
  Manifold.Orientation.ofTopForm finrank_stiefel_two_model (stiefelTopForm O)
    (isSmoothForm_stiefelTopForm O) (stiefelTopForm_ne_zero O)

/-- The determinant of a basis `e` of orientation `O` has the sign of the top form of the normal
orientation of `O`. -/
private theorem det_pos_iff_stiefelTopForm_pos
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) {v : stiefel E 2}
    (b : Basis (Fin (2 * n + 1)) ℝ
      (TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v))
    (e : Basis (Fin (2 * n + 4)) ℝ (Fin 2 → E)) (he : e.orientation = O) :
    0 < e.det (stiefelNormalCons (v : Fin 2 → E) fun i ↦
      mfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) 𝓘(ℝ, Fin 2 → E)
        ((↑) : stiefel E 2 → Fin 2 → E) v (b i)) ↔ 0 < stiefelTopForm O v b := by
  set B := O.someBasis (by rw [Fintype.card_fin, finrank_fin_two_fun (n := n)])
  have hB : 0 < e.det B := (e.orientation_eq_iff_det_pos B).1 (by rw [he, O.someBasis_orientation])
  -- Scalar multiples of alternating maps are evaluated pointwise.
  have key (w : Fin (2 * n + 4) → Fin 2 → E) : e.det w = e.det B * B.det w :=
    (congrArg (fun f ↦ f w) (e.det.eq_smul_basis_det B)).trans rfl
  rw [stiefelTopForm_apply, key]
  exact mul_pos_iff_of_pos_left hB

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
    Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff]
  exact (det_pos_iff_stiefelTopForm_pos O b e he).symm

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
  rw [← _root_.Orientation.ne_iff_eq_neg _ _
      ((O.stiefelTwoOrientation.finrank_tangentSpace_eq v).symm),
    Ne, O.orientation_eq_orientationAt_stiefelTwoOrientation_iff b e he, not_lt]
  exact (isUnit_det_stiefelNormalCons v b e).ne_zero.le_iff_lt

/-- Reversing the orientation of the space of pairs reverses the normal orientation of the
Stiefel manifold. -/
@[simp]
theorem _root_.Orientation.stiefelTwoOrientation_neg
    (O : _root_.Orientation ℝ (Fin 2 → E) (Fin (2 * n + 4))) :
    (-O).stiefelTwoOrientation = -O.stiefelTwoOrientation := by
  ext v
  have hcard := ((-O).stiefelTwoOrientation.finrank_tangentSpace_eq v).symm
  let b := Module.finBasisOfFinrankEq ℝ
    (TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v)
    (by exact finrank_stiefel_two_model (E := E) (n := n))
  let e := O.someBasis (by rw [Fintype.card_fin, finrank_fin_two_fun (n := n)])
  have he : e.orientation = O := O.someBasis_orientation _
  -- Negating the first vector of `e` gives a basis of orientation `-O` and negates determinants.
  let e' := e.unitsSMul (Function.update 1 0 (-1))
  have he' : e'.orientation = -O := by rw [e.orientation_neg_single, he]
  have hdet (w : Fin (2 * n + 4) → Fin 2 → E) : e'.det w = -e.det w := by
    rw [e.det_unitsSMul, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  -- A tangent basis is positive for `-O` exactly when it is negative for `O`.
  have h : b.orientation = (-O).stiefelTwoOrientation.orientationAt v ↔
      b.orientation = -O.stiefelTwoOrientation.orientationAt v := by
    rw [(-O).orientation_eq_orientationAt_stiefelTwoOrientation_iff b e' he', hdet, neg_pos,
      O.orientation_eq_neg_orientationAt_stiefelTwoOrientation_iff b e he]
  rw [Manifold.Orientation.orientationAt_neg]
  rcases b.orientation.eq_or_eq_neg ((-O).stiefelTwoOrientation.orientationAt v) hcard with
    hb | hb
  · exact hb.symm.trans (h.mp hb)
  · have hne : b.orientation ≠ (-O).stiefelTwoOrientation.orientationAt v := fun h' ↦
      Module.Ray.ne_neg_self _ (h'.symm.trans hb)
    have hpos := (_root_.Orientation.ne_iff_eq_neg _ _ hcard).mp (mt h.mpr hne)
    rw [neg_neg] at hpos
    rw [← hpos, hb]
    exact (neg_neg (G := _root_.Orientation ℝ
      (TangentSpace 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ) v)
      (Fin (2 * n + 1))) _).symm

end TauCeti
