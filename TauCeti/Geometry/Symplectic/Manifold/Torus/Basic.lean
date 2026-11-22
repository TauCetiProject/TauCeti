/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Symplectic.Complex.CoordinateSpace
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Algebra.AddCircle

/-!
# The standard symplectic torus

For positive periods `p i`, `i : ι ⊕ ι`, the torus `T = ∀ i, AddCircle (p i)` of dimension
`2 |ι|` carries the **standard symplectic form**

`ω_T = ∑ j, dt_(inl j) ∧ dt_(inr j)`

(`TauCeti.torusSymplecticForm p`), built from the coordinate time forms `dt_i` of the torus
(`TauCeti.torusTimeForm`). The left copy of `ι` stands for the real parts and the right copy for
the imaginary parts of complex coordinates: the covering map

`π : (ι → ℂ) → T`, `π z = ([Re z_j], [Im z_j])`

(`TauCeti.complexPiTorusCover p`) is a smooth local diffeomorphism whose derivative at every point
is `v ↦ (Re v_j, Im v_j)`, that is `TauCeti.complexToRealPi`, and it pulls `ω_T` back to the
standard symplectic form `ω₀ = ∑ j, ds_j ∧ dt_j` of complex coordinate space
(`TauCeti.stdComplexPiSymplecticForm`). Since `π` is onto, `ω_T` is a symplectic form.

Two points of `ι → ℂ` have the same image under `π` exactly when, coordinatewise, their real parts
differ by an integer multiple of the left period and their imaginary parts by an integer multiple
of the right period. So `π` is injective on every set in which these parts vary by less than the
periods, in particular on every open ball of radius `r` with `2 r` at most every period. There it
restricts to a partial diffeomorphism onto its image (`TauCeti.complexPiTorusChart`) pulling `ω_T`
back to `ω₀`, a symplectic embedding of the ball into the torus. Choosing the periods large,
every bounded open subset of `ℂⁿ` thus embeds symplectically into a torus of real dimension `2 n`.
This is the torus factor of the product `S²(a) × T^(2n-2)` into which Gromov's proof of the
nonsqueezing theorem embeds a ball.

## Main definitions

* `TauCeti.torusSymplecticForm p`: the standard symplectic form `∑ j, dt_(inl j) ∧ dt_(inr j)` of
  the torus `∀ i : ι ⊕ ι, AddCircle (p i)`.
* `TauCeti.complexPiTorusCover p`: the covering map `z ↦ ([Re z_j], [Im z_j])` from `ι → ℂ` onto
  the torus.
* `TauCeti.complexPiTorusChart p c hr`: the covering map on the open ball of radius `r` about `c`,
  as a partial diffeomorphism onto its image.

## Main results

* `TauCeti.eval₂_torusSymplecticForm`: on tangent vectors `v, w : ι ⊕ ι → ℝ`,
  `ω_T(v, w) = ∑ j, (v_(inl j) w_(inr j) - v_(inr j) w_(inl j))`.
* `TauCeti.isLocalDiffeomorph_complexPiTorusCover`, `TauCeti.complexPiTorusCover_surjective`: the
  covering map is a surjective smooth local diffeomorphism, with derivative
  `TauCeti.complexToRealPi` (`TauCeti.mfderiv_complexPiTorusCover`), whose coordinates are given by
  `TauCeti.mfderiv_complexPiTorusCover_apply_inl` and
  `TauCeti.mfderiv_complexPiTorusCover_apply_inr`.
* `TauCeti.mpullback_complexPiTorusCover_torusSymplecticForm`: `π^* ω_T = ω₀`.
* `TauCeti.isSymplectic_torusSymplecticForm`: `ω_T` is symplectic.
* `TauCeti.complexPiTorusCover_eq_complexPiTorusCover_iff`: the fibres of the covering map.
* `TauCeti.injOn_complexPiTorusCover`, `TauCeti.injOn_complexPiTorusCover_ball`: injectivity on
  sets whose real and imaginary parts vary by less than the periods, and on small balls.
* `TauCeti.eval₂_torusSymplecticForm_mfderiv_complexPiTorusCover`: the covering map, and hence
  every chart `TauCeti.complexPiTorusChart`, is symplectic for `ω₀` and `ω_T`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.3 (symplectic manifolds).
* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347, §0.3.A (the nonsqueezing theorem, proved through `S² × T^(2n-2)`).
-/

public section

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} (p : ι ⊕ ι → ℝ)

/-! ### The covering map by complex coordinate space -/

/-- The **covering map** `π z = ([Re z_j], [Im z_j])` from complex coordinate space `ι → ℂ` onto
the torus `∀ i : ι ⊕ ι, AddCircle (p i)`: the left coordinates of `π z` are the classes of the real
parts of `z`, and the right coordinates those of its imaginary parts. -/
def complexPiTorusCover (z : ι → ℂ) : ∀ i, AddCircle (p i) :=
  fun i ↦ (Sum.elim (fun j ↦ (z j).re) (fun j ↦ (z j).im) i : AddCircle (p i))

/-- The left coordinates of the covering map are the classes of the real parts. -/
@[simp]
theorem complexPiTorusCover_apply_inl (z : ι → ℂ) (j : ι) :
    complexPiTorusCover p z (.inl j) = ((z j).re : AddCircle (p (.inl j))) :=
  (rfl)

/-- The right coordinates of the covering map are the classes of the imaginary parts. -/
@[simp]
theorem complexPiTorusCover_apply_inr (z : ι → ℂ) (j : ι) :
    complexPiTorusCover p z (.inr j) = ((z j).im : AddCircle (p (.inr j))) :=
  (rfl)

/-- The coordinates of the covering map are the classes of the coordinates of
`TauCeti.complexToRealPi`, `Re z_j` at `inl j` and `Im z_j` at `inr j`. -/
theorem complexPiTorusCover_apply [Fintype ι] (z : ι → ℂ) (i : ι ⊕ ι) :
    complexPiTorusCover p z i = (complexToRealPi ι z i : AddCircle (p i)) := by
  cases i <;> simp

/-- The covering map is onto. -/
theorem complexPiTorusCover_surjective : Surjective (complexPiTorusCover p) := fun x ↦ by
  choose t ht using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  refine ⟨fun j ↦ ⟨t (.inl j), t (.inr j)⟩, funext fun i ↦ ?_⟩
  cases i <;> exact ht _

/-! ### The fibres of the covering map -/

/-- Two points of `ι → ℂ` have the same image in the torus exactly when, coordinatewise, their real
parts differ by an integer multiple of the left period and their imaginary parts by an integer
multiple of the right period. -/
theorem complexPiTorusCover_eq_complexPiTorusCover_iff {z w : ι → ℂ} :
    complexPiTorusCover p z = complexPiTorusCover p w ↔
      ∀ j, (∃ m : ℤ, m • p (.inl j) = (z j).re - (w j).re) ∧
        ∃ n : ℤ, n • p (.inr j) = (z j).im - (w j).im := by
  simp only [funext_iff, Sum.forall, complexPiTorusCover_apply_inl,
    complexPiTorusCover_apply_inr, AddCircle.coe_eq_coe_iff_exists_zsmul]
  exact ⟨fun h j ↦ ⟨h.1 j, h.2 j⟩, fun h ↦ ⟨fun j ↦ (h j).1, fun j ↦ (h j).2⟩⟩

variable [Fintype ι] [∀ i, Fact (0 < p i)]

/-! ### The symplectic form -/

/-- The **standard symplectic form** `ω_T = ∑ j, dt_(inl j) ∧ dt_(inr j)` of the torus
`∀ i : ι ⊕ ι, AddCircle (p i)`, pairing the coordinate time form of each left coordinate with that
of the corresponding right coordinate. -/
def torusSymplecticForm :
    SmoothTwoForm (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  ∑ j, SmoothForm.wedge (torusTimeForm p (.inl j)) (torusTimeForm p (.inr j))

/-- The standard symplectic form of the torus is `∑ j, dt_(inl j) ∧ dt_(inr j)`. -/
theorem torusSymplecticForm_def :
    torusSymplecticForm p =
      ∑ j, SmoothForm.wedge (torusTimeForm p (.inl j)) (torusTimeForm p (.inr j)) :=
  (rfl)

/-- The standard symplectic form of the torus on a pair `v 0, v 1 : ι ⊕ ι → ℝ` of tangent vectors
is `∑ j, (v 0 (inl j) * v 1 (inr j) - v 0 (inr j) * v 1 (inl j))`. -/
@[simp]
theorem torusSymplecticForm_apply (x : ∀ i, AddCircle (p i))
    (v : Fin 2 → TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) x) :
    (torusSymplecticForm p).val x v =
      ∑ j, (v 0 (.inl j) * v 1 (.inr j) - v 0 (.inr j) * v 1 (.inl j)) := by
  have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
  rw [hv]
  simp [torusSymplecticForm_def, Finset.sum_apply, SmoothForm.wedge_apply_one_one, mul_comm]

/-- The standard symplectic form of the torus on tangent vectors `v, w : ι ⊕ ι → ℝ` is
`∑ j, (v_(inl j) w_(inr j) - v_(inr j) w_(inl j))`. -/
theorem eval₂_torusSymplecticForm (x : ∀ i, AddCircle (p i))
    (v w : TangentSpace (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) x) :
    (torusSymplecticForm p).eval₂ x v w =
      ∑ j, (v (.inl j) * w (.inr j) - v (.inr j) * w (.inl j)) := by
  simp [SmoothBundleForm.eval₂_apply]

/-! ### Smoothness and derivative of the covering map -/

/-- The covering map is smooth. -/
theorem contMDiff_complexPiTorusCover {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) n
      (complexPiTorusCover p) := by
  rw [funext₂ (complexPiTorusCover_apply p)]
  exact contMDiff_pi_iff.2 fun i ↦ (AddCircle.contMDiff_coe (p i) n).comp
    ((ContinuousLinearMap.proj i).comp (complexToRealPi ι : (ι → ℂ) →L[ℝ] ι ⊕ ι → ℝ)).contMDiff

/-- The covering map has derivative `TauCeti.complexToRealPi`, `v ↦ (Re v_j, Im v_j)`, at every
point. -/
theorem hasMFDerivAt_complexPiTorusCover (z : ι → ℂ) :
    HasMFDerivAt 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
      (complexPiTorusCover p) z (complexToRealPi ι : (ι → ℂ) →L[ℝ] ι ⊕ ι → ℝ) := by
  rw [funext₂ (complexPiTorusCover_apply p)]
  exact hasMFDerivAt_pi fun i ↦ ((AddCircle.hasMFDerivAt_coe (p i) _).comp z
    ((ContinuousLinearMap.proj i).comp
      (complexToRealPi ι : (ι → ℂ) →L[ℝ] ι ⊕ ι → ℝ)).hasMFDerivAt).congr_mfderiv
    (ContinuousLinearMap.id_comp _)

/-- The derivative of the covering map at every point is `TauCeti.complexToRealPi`,
`v ↦ (Re v_j, Im v_j)`. -/
theorem mfderiv_complexPiTorusCover (z : ι → ℂ) :
    mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (complexPiTorusCover p) z =
      (complexToRealPi ι : (ι → ℂ) →L[ℝ] ι ⊕ ι → ℝ) :=
  (hasMFDerivAt_complexPiTorusCover p z).mfderiv

/-- The left coordinates of the derivative of the covering map are the real parts. -/
@[simp]
theorem mfderiv_complexPiTorusCover_apply_inl (z v : ι → ℂ) (j : ι) :
    mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (complexPiTorusCover p) z v
      (.inl j) = (v j).re := by
  rw [mfderiv_complexPiTorusCover]
  exact complexToRealPi_apply ι v (.inl j)

/-- The right coordinates of the derivative of the covering map are the imaginary parts. -/
@[simp]
theorem mfderiv_complexPiTorusCover_apply_inr (z v : ι → ℂ) (j : ι) :
    mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (complexPiTorusCover p) z v
      (.inr j) = (v j).im := by
  rw [mfderiv_complexPiTorusCover]
  exact complexToRealPi_apply ι v (.inr j)

/-- The covering map is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_complexPiTorusCover :
    IsLocalDiffeomorph 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) ∞
      (complexPiTorusCover p) := fun z ↦ by
  refine isLocalDiffeomorphAt_of_injective_mfderiv (s := univ)
    (contMDiff_complexPiTorusCover p).contMDiffOn isOpen_univ (mem_univ z)
    BoundarylessManifold.isInteriorPoint (by simp) (fun (v w : ι → ℂ) h ↦ funext fun j ↦ ?_) ?_
  · -- The derivative records the real and imaginary parts of every coordinate.
    have hre := congrFun h (.inl j)
    have him := congrFun h (.inr j)
    simp only [mfderiv_complexPiTorusCover_apply_inl, mfderiv_complexPiTorusCover_apply_inr]
      at hre him
    exact Complex.ext hre him
  · simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Fintype.card_sum, mul_two]

/-! ### The covering map is symplectic -/

/-- The covering map is symplectic: `ω_T (dπ v, dπ w) = ω₀ (v, w)` for the standard symplectic
form `ω₀` of `ι → ℂ`. -/
theorem eval₂_torusSymplecticForm_mfderiv_complexPiTorusCover (z v w : ι → ℂ) :
    (torusSymplecticForm p).eval₂ (complexPiTorusCover p z)
        (mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
          (complexPiTorusCover p) z v)
        (mfderiv 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ))
          (complexPiTorusCover p) z w) =
      stdComplexPiSymplecticForm ι v w := by
  rw [eval₂_torusSymplecticForm]
  simp [Finset.sum_sub_distrib]

/-- The covering map pulls the standard symplectic form of the torus back to the standard
symplectic form `ω₀ = ∑ j, ds_j ∧ dt_j` of complex coordinate space. -/
@[simp]
theorem mpullback_complexPiTorusCover_torusSymplecticForm :
    SmoothForm.mpullback (complexPiTorusCover p) (contMDiff_complexPiTorusCover p)
        (torusSymplecticForm p) =
      (stdComplexPiSymplecticForm ι).constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback]
  exact (eval₂_torusSymplecticForm_mfderiv_complexPiTorusCover p z v w).trans
    (SymplecticForm.constSmooth_apply _ _ _ _).symm

/-- **The standard symplectic form of the torus is symplectic.** -/
theorem isSymplectic_torusSymplecticForm : (torusSymplecticForm p).IsSymplectic := by
  rw [← (isLocalDiffeomorph_complexPiTorusCover p).isSymplectic_mpullback_iff
    (complexPiTorusCover_surjective p), mpullback_complexPiTorusCover_torusSymplecticForm]
  exact SymplecticForm.isSymplectic_constSmooth _

/-! ### Injectivity on small sets -/

omit [Fintype ι] [∀ i, Fact (0 < p i)] in
/-- The covering map is injective on every set in which the real and imaginary parts of each
coordinate vary by less than the corresponding periods. -/
theorem injOn_complexPiTorusCover {s : Set (ι → ℂ)}
    (hs : ∀ z ∈ s, ∀ w ∈ s, ∀ j,
      |(z j).re - (w j).re| < p (.inl j) ∧ |(z j).im - (w j).im| < p (.inr j)) :
    InjOn (complexPiTorusCover p) s := fun z hz w hw h ↦ funext fun j ↦
  Complex.ext (AddCircle.eq_of_coe_eq_of_abs_sub_lt (congrFun h (.inl j)) (hs z hz w hw j).1)
    (AddCircle.eq_of_coe_eq_of_abs_sub_lt (congrFun h (.inr j)) (hs z hz w hw j).2)

omit [∀ i, Fact (0 < p i)] in
/-- The covering map is injective on every open ball of radius `r` such that `2 r` is at most every
period. -/
theorem injOn_complexPiTorusCover_ball (c : ι → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i) :
    InjOn (complexPiTorusCover p) (ball c r) := by
  refine injOn_complexPiTorusCover p fun z hz w hw j ↦ ?_
  -- Each real or imaginary part of `z - w` is bounded by `‖z - w‖ < 2 r`.
  have hzw : ‖z j - w j‖ < 2 * r := by
    calc ‖z j - w j‖ ≤ ‖z - w‖ := norm_le_pi_norm (z - w) j
      _ ≤ dist z c + dist w c := by rw [← dist_eq_norm]; exact dist_triangle_right z w c
      _ < 2 * r := by linarith [mem_ball.1 hz, mem_ball.1 hw]
  refine ⟨?_, ?_⟩
  · calc |(z j).re - (w j).re| = |(z j - w j).re| := by rw [Complex.sub_re]
      _ ≤ ‖z j - w j‖ := Complex.abs_re_le_norm _
      _ < p (.inl j) := hzw.trans_le (hr _)
  · calc |(z j).im - (w j).im| = |(z j - w j).im| := by rw [Complex.sub_im]
      _ ≤ ‖z j - w j‖ := Complex.abs_im_le_norm _
      _ < p (.inr j) := hzw.trans_le (hr _)

/-! ### Symplectic charts on small balls -/

/-- The covering map on the open ball of radius `r` about `c`, as a partial diffeomorphism onto its
image, when `2 r` is at most every period. It pulls the standard symplectic form of the torus back
to the standard symplectic form of `ι → ℂ`
(`TauCeti.eval₂_torusSymplecticForm_mfderiv_complexPiTorusCover`), so it is a symplectic embedding
of the ball into the torus. -/
def complexPiTorusChart (c : ι → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i) :
    PartialDiffeomorph 𝓘(ℝ, ι → ℂ) (ModelWithCorners.pi fun _ : ι ⊕ ι ↦ 𝓘(ℝ)) (ι → ℂ)
      (∀ i, AddCircle (p i)) ∞ :=
  ((isLocalDiffeomorph_complexPiTorusCover p).isLocalDiffeomorphOn _).partialDiffeomorphOfInjOn
    isOpen_ball (injOn_complexPiTorusCover_ball p c hr)

variable {p} (c : ι → ℂ) {r : ℝ} (hr : ∀ i, 2 * r ≤ p i)

/-- The source of the chart is the ball. -/
@[simp]
theorem complexPiTorusChart_source : (complexPiTorusChart p c hr).source = ball c r :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source _ _ _

/-- The target of the chart is the image of the ball under the covering map. -/
@[simp]
theorem complexPiTorusChart_target :
    (complexPiTorusChart p c hr).target = complexPiTorusCover p '' ball c r :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target _ _ _

/-- The chart is the covering map. -/
@[simp]
theorem coe_complexPiTorusChart : ⇑(complexPiTorusChart p c hr) = complexPiTorusCover p :=
  IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn _ _ _

end TauCeti
