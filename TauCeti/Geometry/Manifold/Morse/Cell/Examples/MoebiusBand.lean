/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.RealProjectivePlane
public import TauCeti.Topology.VectorBundle.Moebius
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic

/-!
# The lower sublevels of the height on `ℝP²` are Möbius bands

On the real projective plane consider the height `f [x : y : z] = (y² + 2z²) / (x² + y² + z²)`, the
projective moment function with weights `(0, 1, 2)`, with minimum `[1 : 0 : 0]`, saddle
`[0 : 1 : 0]` and maximum `[0 : 0 : 1]` at the values `0`, `1` and `2`. For `1 < c < 2` the lower
sublevel `{f ≤ c}`, below which the top cell of `ℝP²` is attached, is a Möbius band: it is
homeomorphic to the closed unit disc bundle of the Möbius line bundle over the circle
(`TauCeti.moebiusCore`), by `TauCeti.projectivePlaneSublevelMoebiusHomeomorph`. The core of the
band is the projective line `z = 0`, which goes to the zero section, and its boundary is the level
`f = c`, which goes to the unit sphere bundle.

Explicitly, `[x : y : z]` lies in `{f ≤ c}` exactly when `(x, y) ≠ 0` and
`(2 - c) z² ≤ c x² + (c - 1) y²`. A vector `u` of the Möbius line bundle over `z₀` goes to
`[cos θ : sin θ : u h(θ)]`, where `cos θ + i sin θ` is the square root of `z₀` that trivializes the
bundle over the chart of `z₀`, and `h(θ) = √((c cos² θ + (c - 1) sin² θ) / (2 - c))` is the
half-height of the sublevel over `[cos θ : sin θ : 0]`. The two square roots chosen over the two
charts of the Möbius line bundle agree on the upper half-circle and are opposite on the lower one,
exactly as the transition function of the bundle, so this point does not depend on the chart. The
map is a continuous bijection from the compact disc bundle onto the Hausdorff sublevel, hence a
homeomorphism. For `c = 1` the inequality degenerates to `z² ≤ x²`, which pinches the sublevel at
the saddle `[0 : 1 : 0]`, and for `c ≥ 2` the sublevel is the whole of `ℝP²`.

## Main results

* `TauCeti.projectivePlaneSublevelMoebiusHomeomorph`: for `1 < c < 2` the sublevel `{f ≤ c}` is
  homeomorphic to the unit disc bundle of the Möbius line bundle.
* `TauCeti.proj_projectivePlaneSublevelMoebiusHomeomorph`: the bundle projection is the circle map
  `[x : y : z] ↦ (x + i y)² / (x² + y²)` of `TauCeti.projectivePlaneSublevelCircleEquiv`.
* `TauCeti.norm_sq_snd_projectivePlaneSublevelMoebiusHomeomorph_of_eq`: the fibre coordinate of the
  image of `[x : y : z]` has square `(2 - c) z² / (c x² + (c - 1) y²)`.
* `TauCeti.projectivePlaneSublevelMoebiusHomeomorph_mem_sphereBundle_iff`: the level `f = c` is the
  boundary of the band.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §2 (the Möbius line bundle).
-/

public section

noncomputable section

open Bundle Set Projectivization
open scoped Real LinearAlgebra.Projectivization

namespace TauCeti

section MoebiusBand

variable {c : ℝ}

/-- The angle of a square root of `z`, chosen continuously over the chart `i` of the Möbius line
bundle: half the argument of `z` over the circle minus `-1` (`i = true`), and half the argument of
`-z` plus `π / 2` over the circle minus `1` (`i = false`). -/
private def moebiusRootAngle (i : Bool) (z : Circle) : ℝ :=
  if i then Complex.arg (z : ℂ) / 2 else Complex.arg (-(z : ℂ)) / 2 + π / 2

/-- `cos θ + i sin θ` is a square root of `z` for the angle `θ` of either chart. -/
private theorem moebiusRootAngle_sq (i : Bool) (z : Circle) :
    ((Real.cos (moebiusRootAngle i z) : ℂ) + Real.sin (moebiusRootAngle i z) * Complex.I) ^ 2 =
      z := by
  have key (w : ℂ) (hw : ‖w‖ = 1) : Complex.exp (Complex.arg w * Complex.I) = w := by
    simpa [hw] using Complex.norm_mul_exp_arg_mul_I w
  rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, sq, ← Complex.exp_add]
  cases i
  · simp only [moebiusRootAngle, Bool.false_eq_true, ↓reduceIte]
    calc Complex.exp _
        = Complex.exp (Complex.arg (-(z : ℂ)) * Complex.I) * Complex.exp (π * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
      _ = z := by rw [key _ (by simp), Complex.exp_pi_mul_I]; ring
  · simp only [moebiusRootAngle, ↓reduceIte]
    calc Complex.exp _ = Complex.exp (Complex.arg (z : ℂ) * Complex.I) := by
          congr 1; push_cast; ring
      _ = z := key _ (by simp)

/-- The angle of the chart `i` is continuous on the chart. -/
private theorem continuousAt_moebiusRootAngle {i : Bool} {z : Circle}
    (hz : z ∈ moebiusBaseSet i) : ContinuousAt (moebiusRootAngle i) z := by
  have hcoe : Continuous fun w : Circle ↦ (w : ℂ) := continuous_subtypeVal
  cases i
  · -- Off `1`, the point `-z` lies in the slit plane, where the argument is continuous.
    have hz' : -(z : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra! h
      rcases (Circle.im_coe_eq_zero_iff z).1 (by simpa using h.2) with rfl | rfl
      · exact mem_moebiusBaseSet.1 hz (by simp)
      · norm_num at h
    unfold moebiusRootAngle
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (((Complex.continuousAt_arg hz').comp (f := fun w : Circle ↦ -(w : ℂ))
      hcoe.neg.continuousAt).div_const 2).add continuousAt_const
  · -- Off `-1`, the point `z` lies in the slit plane.
    have hz' : (z : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra! h
      rcases (Circle.im_coe_eq_zero_iff z).1 h.2 with rfl | rfl
      · norm_num at h
      · exact mem_moebiusBaseSet.1 hz (by simp)
    unfold moebiusRootAngle
    simp only [↓reduceIte]
    exact ((Complex.continuousAt_arg hz').comp hcoe.continuousAt).div_const 2

/-- On the upper half-circle the two charts choose the same square root. -/
private theorem moebiusRootAngle_false_of_im_pos {z : Circle} (hz : 0 < (z : ℂ).im) :
    moebiusRootAngle false z = moebiusRootAngle true z := by
  simp only [moebiusRootAngle, Bool.false_eq_true, ↓reduceIte,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
  ring

/-- On the lower half-circle the two charts choose opposite square roots. -/
private theorem moebiusRootAngle_false_of_im_neg {z : Circle} (hz : (z : ℂ).im < 0) :
    moebiusRootAngle false z = moebiusRootAngle true z + π := by
  simp only [moebiusRootAngle, Bool.false_eq_true, ↓reduceIte,
    Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
  ring

/-- The half-height `√((c cos² θ + (c - 1) sin² θ) / (2 - c))` of the sublevel `{f ≤ c}` over
the point `[cos θ : sin θ : 0]`: the point `[cos θ : sin θ : t]` lies in the sublevel exactly when
`|t|` is at most it. -/
private def moebiusHeight (c θ : ℝ) : ℝ :=
  √((c * Real.cos θ ^ 2 + (c - 1) * Real.sin θ ^ 2) / (2 - c))

private theorem moebiusHeight_add_pi (c θ : ℝ) : moebiusHeight c (θ + π) = moebiusHeight c θ := by
  simp [moebiusHeight, Real.cos_add_pi, Real.sin_add_pi]

private theorem moebiusHeight_aux (c θ : ℝ) :
    c * Real.cos θ ^ 2 + (c - 1) * Real.sin θ ^ 2 = Real.cos θ ^ 2 + (c - 1) := by
  linear_combination (c - 1) * Real.cos_sq_add_sin_sq θ

private theorem two_sub_mul_moebiusHeight_sq (hc₁ : 1 < c) (hc₂ : c < 2) (θ : ℝ) :
    (2 - c) * moebiusHeight c θ ^ 2 = c * Real.cos θ ^ 2 + (c - 1) * Real.sin θ ^ 2 := by
  rw [moebiusHeight, Real.sq_sqrt (div_nonneg (by rw [moebiusHeight_aux]; positivity)
    (by linarith))]
  field_simp [show (2 - c) ≠ 0 by linarith]

private theorem moebiusHeight_pos (hc₁ : 1 < c) (hc₂ : c < 2) (θ : ℝ) : 0 < moebiusHeight c θ := by
  refine Real.sqrt_pos.2 (div_pos ?_ (by linarith))
  rw [moebiusHeight_aux]
  nlinarith [sq_nonneg (Real.cos θ)]

/-- The homogeneous coordinates `(cos θ, sin θ, u h(θ))` of the point of the Möbius band at angle
`θ` and fibre coordinate `u`. -/
private def moebiusVec (c θ u : ℝ) : Fin 3 → ℝ :=
  ![Real.cos θ, Real.sin θ, u * moebiusHeight c θ]

private theorem moebiusVec_ne_zero (c θ u : ℝ) : moebiusVec c θ u ≠ 0 := fun h ↦ by
  have h0 : Real.cos θ = 0 := congrFun h 0
  have h1 : Real.sin θ = 0 := congrFun h 1
  simpa [h0, h1] using Real.cos_sq_add_sin_sq θ

private theorem continuous_moebiusVec (c : ℝ) :
    Continuous fun p : ℝ × ℝ ↦ moebiusVec c p.1 p.2 := by
  refine continuous_pi fun k ↦ ?_
  fin_cases k <;>
    simp only [moebiusVec, moebiusHeight, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop

/-- The height `f` at the point of the Möbius band at angle `θ` and fibre coordinate `u`. -/
private theorem sub_projectiveMomentFunction_mk_moebiusVec (hc₁ : 1 < c) (hc₂ : c < 2)
    (θ u : ℝ) :
    c - projectiveMomentFunction ℝ ![0, 1, 2] (mk ℝ (moebiusVec c θ u) (moebiusVec_ne_zero c θ u)) =
      (2 - c) * moebiusHeight c θ ^ 2 * (1 - u ^ 2) / (1 + u ^ 2 * moebiusHeight c θ ^ 2) := by
  have h2c := two_sub_mul_moebiusHeight_sq hc₁ hc₂ θ
  have hcs := Real.cos_sq_add_sin_sq θ
  rw [projectiveMomentFunction_zero_one_two_mk]
  simp only [moebiusVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hpos : 0 < 1 + u ^ 2 * moebiusHeight c θ ^ 2 := by positivity
  have hpos' : Real.cos θ ^ 2 + Real.sin θ ^ 2 + (u * moebiusHeight c θ) ^ 2 =
      1 + u ^ 2 * moebiusHeight c θ ^ 2 := by rw [hcs]; ring
  rw [hpos', eq_div_iff hpos.ne', sub_mul, div_mul_cancel₀ _ hpos.ne']
  linear_combination -h2c - c * hcs

private theorem projectiveMomentFunction_mk_moebiusVec_le_iff (hc₁ : 1 < c) (hc₂ : c < 2)
    (θ u : ℝ) :
    projectiveMomentFunction ℝ ![0, 1, 2] (mk ℝ (moebiusVec c θ u) (moebiusVec_ne_zero c θ u)) ≤
      c ↔ |u| ≤ 1 := by
  have hh := moebiusHeight_pos hc₁ hc₂ θ
  rw [← sub_nonneg, sub_projectiveMomentFunction_mk_moebiusVec hc₁ hc₂,
    le_div_iff₀ (by positivity), zero_mul,
    mul_nonneg_iff_of_pos_left (mul_pos (by linarith) (by positivity)), sub_nonneg,
    sq_le_one_iff_abs_le_one]

private theorem projectiveMomentFunction_mk_moebiusVec_eq_iff (hc₁ : 1 < c) (hc₂ : c < 2)
    (θ u : ℝ) :
    projectiveMomentFunction ℝ ![0, 1, 2] (mk ℝ (moebiusVec c θ u) (moebiusVec_ne_zero c θ u)) =
      c ↔ |u| = 1 := by
  have hh := moebiusHeight_pos hc₁ hc₂ θ
  rw [eq_comm, ← sub_eq_zero, sub_projectiveMomentFunction_mk_moebiusVec hc₁ hc₂,
    div_eq_zero_iff, or_iff_left (by positivity), mul_eq_zero,
    or_iff_right (mul_pos (by linarith) (by positivity)).ne', sub_eq_zero, eq_comm,
    sq_eq_one_iff, abs_eq zero_le_one]

/-- The point `[cos θ : sin θ : u h(θ)]` of `ℝP²` determined by a vector `u` of the Möbius line
bundle over `z`, with `θ` the angle of the square root of `z` in the chart of `z`. -/
private def moebiusBandMap (c : ℝ) (p : TotalSpace ℝ moebiusCore.Fiber) : ℙ ℝ (Fin 3 → ℝ) :=
  mk ℝ (moebiusVec c (moebiusRootAngle (moebiusCore.indexAt p.proj) p.proj) p.snd)
    (moebiusVec_ne_zero _ _ _)

/-- Reading a vector of the Möbius line bundle in another chart gives the same point of `ℝP²`. -/
private theorem mk_moebiusVec_coordChange {i j : Bool} {z : Circle} (hi : z ∈ moebiusBaseSet i)
    (hj : z ∈ moebiusBaseSet j) (u : ℝ) :
    mk ℝ (moebiusVec c (moebiusRootAngle j z) (moebiusCore.coordChange i j z u))
        (moebiusVec_ne_zero _ _ _) =
      mk ℝ (moebiusVec c (moebiusRootAngle i z) u) (moebiusVec_ne_zero _ _ _) := by
  rw [moebiusCore_coordChange]
  by_cases hij : i = j
  · subst hij
    simp
  · simp only [hij, ↓reduceIte, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rcases (im_ne_zero_of_mem_moebiusBaseSet hij hi hj).lt_or_gt with h | h
    · -- On the lower half-circle the angles differ by `π` and the coordinates by a sign.
      rw [moebiusSign_of_neg h]
      refine (mk_eq_mk_iff' ℝ _ _ _ _).2 ⟨-1, ?_⟩
      cases i <;> cases j <;> simp only [not_true_eq_false, reduceCtorEq,
        not_false_eq_true] at hij <;>
        ext k <;> fin_cases k <;>
        simp [moebiusVec, moebiusRootAngle_false_of_im_neg h, moebiusHeight_add_pi,
          Real.cos_add_pi, Real.sin_add_pi]
    · rw [moebiusSign_of_pos h]
      cases i <;> cases j <;> simp only [not_true_eq_false, reduceCtorEq,
        not_false_eq_true] at hij <;>
        simp [moebiusRootAngle_false_of_im_pos h]

private theorem continuous_moebiusBandMap (c : ℝ) : Continuous (moebiusBandMap c) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  set i := moebiusCore.indexAt p.proj
  let e := moebiusCore.localTriv i
  have hp : p ∈ e.source :=
    (moebiusCore.mem_localTriv_source _ _).2 (moebiusCore.mem_baseSet_at _)
  -- In the chart `i`, the map reads `(z, u) ↦ [cos θᵢ(z) : sin θᵢ(z) : u h(θᵢ(z))]`.
  have hv : ContinuousAt (fun q : Circle × ℝ ↦ moebiusVec c (moebiusRootAngle i q.1) q.2) (e p) :=
    (continuous_moebiusVec c).continuousAt.comp
      (((continuousAt_moebiusRootAngle (by
        simp only [e, VectorBundleCore.localTriv_apply, ← moebiusCore_baseSet]
        exact moebiusCore.mem_baseSet_at p.proj)).comp continuousAt_fst).prodMk continuousAt_snd)
  have hsub : ContinuousAt (fun q : Circle × ℝ ↦ (⟨moebiusVec c (moebiusRootAngle i q.1) q.2,
      moebiusVec_ne_zero _ _ _⟩ : {v : Fin 3 → ℝ // v ≠ 0})) (e p) :=
    Topology.IsEmbedding.subtypeVal.isInducing.continuousAt_iff.2 hv
  have hG := continuous_mk' (K := ℝ).continuousAt.comp hsub
  refine (hG.comp (e.continuousOn.continuousAt (e.open_source.mem_nhds hp))).congr ?_
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  simp only [Function.comp_apply, e, VectorBundleCore.localTriv_apply]
  exact mk_moebiusVec_coordChange
    (by rw [← moebiusCore_baseSet]; exact moebiusCore.mem_baseSet_at _)
    (by rw [← moebiusCore_baseSet]; exact (moebiusCore.mem_localTriv_source _ _).1 hq) _

/-- Homogeneous coordinates `v` of the image of a vector `u` over `z` are a multiple of
`(cos θ, sin θ, u h(θ))`. -/
private theorem exists_of_moebiusBandMap_eq_mk {z : Circle} {u : ℝ} {v : Fin 3 → ℝ}
    {hv : v ≠ 0} (h : moebiusBandMap c ⟨z, u⟩ = mk ℝ v hv) :
    ∃ a : ℝ, Real.cos (moebiusRootAngle (moebiusCore.indexAt z) z) = a * v 0 ∧
      Real.sin (moebiusRootAngle (moebiusCore.indexAt z) z) = a * v 1 ∧
      u * moebiusHeight c (moebiusRootAngle (moebiusCore.indexAt z) z) = a * v 2 := by
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff' ℝ _ _ _ _).1 h
  exact ⟨a, (congrFun ha 0).symm, (congrFun ha 1).symm, (congrFun ha 2).symm⟩

/-- The base point of a vector of the Möbius band is the square of the normalized first two
homogeneous coordinates of its image. -/
private theorem coe_of_moebiusBandMap_eq_mk {z : Circle} {u : ℝ} {v : Fin 3 → ℝ}
    {hv : v ≠ 0} (h : moebiusBandMap c ⟨z, u⟩ = mk ℝ v hv) :
    (z : ℂ) = (v 0 + v 1 * Complex.I) ^ 2 / (v 0 ^ 2 + v 1 ^ 2 : ℝ) := by
  obtain ⟨a, h0, h1, -⟩ := exists_of_moebiusBandMap_eq_mk h
  have ha : a ^ 2 * (v 0 ^ 2 + v 1 ^ 2) = 1 := by
    rw [← Real.cos_sq_add_sin_sq (moebiusRootAngle (moebiusCore.indexAt z) z), h0, h1]
    ring
  have ha' : (a : ℂ) ^ 2 * ((v 0 ^ 2 + v 1 ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast ha
  have hne : ((v 0 ^ 2 + v 1 ^ 2 : ℝ) : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one ha'
  rw [← moebiusRootAngle_sq, h0, h1, eq_div_iff hne]
  push_cast at ha' ⊢
  linear_combination ((v 0 : ℂ) + v 1 * Complex.I) ^ 2 * ha'

/-- The square of the fibre coordinate of a vector of the Möbius band, read off from the
homogeneous coordinates of its image. -/
private theorem sq_of_moebiusBandMap_eq_mk (hc₁ : 1 < c) (hc₂ : c < 2) {z : Circle} {u : ℝ}
    {v : Fin 3 → ℝ} {hv : v ≠ 0} (h : moebiusBandMap c ⟨z, u⟩ = mk ℝ v hv) :
    u ^ 2 = (2 - c) * v 2 ^ 2 / (c * v 0 ^ 2 + (c - 1) * v 1 ^ 2) := by
  obtain ⟨a, h0, h1, h2⟩ := exists_of_moebiusBandMap_eq_mk h
  set θ := moebiusRootAngle (moebiusCore.indexAt z) z
  have ha : a ^ 2 * (v 0 ^ 2 + v 1 ^ 2) = 1 := by
    rw [← Real.cos_sq_add_sin_sq θ, h0, h1]
    ring
  have ha0 : a ^ 2 ≠ 0 := left_ne_zero_of_mul_eq_one ha
  have hD : 0 < c * v 0 ^ 2 + (c - 1) * v 1 ^ 2 := by
    have : 0 < v 0 ^ 2 + v 1 ^ 2 := lt_of_le_of_ne (by positivity)
      (right_ne_zero_of_mul_eq_one ha).symm
    nlinarith [sq_nonneg (v 0)]
  have E1 : u ^ 2 * moebiusHeight c θ ^ 2 = a ^ 2 * v 2 ^ 2 := by
    rw [← mul_pow, ← mul_pow]
    exact congrArg (· ^ 2) h2
  have E2 := two_sub_mul_moebiusHeight_sq hc₁ hc₂ θ
  rw [eq_div_iff hD.ne']
  refine mul_left_cancel₀ ha0 ?_
  linear_combination (2 - c) * E1 - u ^ 2 * E2 -
    u ^ 2 * (c * (Real.cos θ + a * v 0) * h0 + (c - 1) * (Real.sin θ + a * v 1) * h1)

private theorem moebiusBandMap_injective (hc₁ : 1 < c) (hc₂ : c < 2) :
    Function.Injective (moebiusBandMap c) := by
  rintro ⟨z, u⟩ ⟨z', u'⟩ h
  -- Both base points are read off from the same homogeneous coordinates.
  have hz : z = z' := Circle.ext ((coe_of_moebiusBandMap_eq_mk h).trans
    (coe_of_moebiusBandMap_eq_mk (z := z') (u := u') rfl).symm)
  subst hz
  -- Over the same base point the angles agree, so the scalar is `1`.
  obtain ⟨a, h0, h1, h2⟩ := exists_of_moebiusBandMap_eq_mk h
  set θ := moebiusRootAngle (moebiusCore.indexAt z) z
  simp only [moebiusVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have ha : a = 1 := by
    have : (a - 1) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) = 0 := by
      linear_combination (-Real.cos θ) * h0 - Real.sin θ * h1
    rw [Real.cos_sq_add_sin_sq, mul_one, sub_eq_zero] at this
    exact this
  subst ha
  rw [one_mul] at h2
  have := mul_right_cancel₀ (moebiusHeight_pos hc₁ hc₂ θ).ne' h2
  subst this
  rfl

/-- The square root of `exp (2 i α)` chosen in either chart is a real multiple (in fact `±1`) of
`exp (i α)`. -/
private theorem exists_cos_moebiusRootAngle_eq (i : Bool) (α : ℝ) :
    ∃ σ : ℝ, Real.cos (moebiusRootAngle i (Circle.exp (2 * α))) = σ * Real.cos α ∧
      Real.sin (moebiusRootAngle i (Circle.exp (2 * α))) = σ * Real.sin α := by
  set θ := moebiusRootAngle i (Circle.exp (2 * α))
  have hsq : ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) ^ 2 =
      ((Real.cos α : ℂ) + Real.sin α * Complex.I) ^ 2 := by
    rw [moebiusRootAngle_sq, Circle.coe_exp, Complex.ofReal_cos, Complex.ofReal_sin,
      ← Complex.exp_mul_I, sq, ← Complex.exp_add]
    push_cast
    ring_nf
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · refine ⟨1, ?_, ?_⟩
    · simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.re h
    · simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.im h
  · refine ⟨-1, ?_, ?_⟩
    · simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.re h
    · simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using congrArg Complex.im h

/-- Every point of `ℝP²` below the maximum is the image of a vector of the Möbius line bundle. -/
private theorem exists_moebiusBandMap_eq (hc₁ : 1 < c) (hc₂ : c < 2)
    {y : ℙ ℝ (Fin 3 → ℝ)} (hy : projectiveMomentFunction ℝ ![0, 1, 2] y < 2) :
    ∃ p, moebiusBandMap c p = y := by
  induction y using ind with | h v hv =>
  have hd := coords_ne_zero_of_projectiveMomentFunction_lt_two hy rfl
  set w : ℂ := v 0 + v 1 * Complex.I
  have hw : w ≠ 0 := fun h ↦ hd (by
    have h0 : v 0 = 0 := by simpa [w] using congrArg Complex.re h
    have h1 : v 1 = 0 := by simpa [w] using congrArg Complex.im h
    ext k; fin_cases k <;> simp [h0, h1])
  set α := Complex.arg w
  set r := ‖w‖
  have hr : 0 < r := norm_pos_iff.2 hw
  have hwr : (r : ℂ) * Complex.exp (α * Complex.I) = w := Complex.norm_mul_exp_arg_mul_I w
  have hv0 : v 0 = r * Real.cos α := by
    have := congrArg Complex.re hwr
    simpa [w, Complex.exp_ofReal_mul_I_re] using this.symm
  have hv1 : v 1 = r * Real.sin α := by
    have := congrArg Complex.im hwr
    simpa [w, Complex.exp_ofReal_mul_I_im] using this.symm
  -- The base point is the square of `w / ‖w‖`, and its square root in its chart is `±w / ‖w‖`.
  obtain ⟨σ, hcos, hsin⟩ :=
    exists_cos_moebiusRootAngle_eq (moebiusCore.indexAt (Circle.exp (2 * α))) α
  set z : Circle := Circle.exp (2 * α)
  set θ := moebiusRootAngle (moebiusCore.indexAt z) z
  have hh := (moebiusHeight_pos hc₁ hc₂ θ).ne'
  refine ⟨⟨z, σ * v 2 / (r * moebiusHeight c θ)⟩, (mk_eq_mk_iff' ℝ _ _ _ _).2 ⟨σ / r, ?_⟩⟩
  -- The constructed vector lies over `z`, so its angle is `θ`.
  change (σ / r) • v = moebiusVec c θ (σ * v 2 / (r * moebiusHeight c θ))
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, hv0, smul_eq_mul, moebiusVec, hcos,
      Matrix.cons_val_zero]
    field_simp
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, hv1, smul_eq_mul, moebiusVec, hsin,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
  · simp only [Fin.reduceFinMk, Pi.smul_apply, Fin.isValue, smul_eq_mul, moebiusVec,
      Matrix.cons_val]
    field_simp

/-- The map from the unit disc bundle of the Möbius line bundle to the sublevel `{f ≤ c}`. -/
private def moebiusDiscBundleMap (hc₁ : 1 < c) (hc₂ : c < 2) (p : discBundle ℝ moebiusCore.Fiber) :
    {y | projectiveMomentFunction ℝ ![0, 1, 2] y ≤ c} :=
  ⟨moebiusBandMap c p, (projectiveMomentFunction_mk_moebiusVec_le_iff hc₁ hc₂ _ _).2
    ((norm_moebiusCore_fiber _).symm.trans_le (mem_discBundle.1 p.property))⟩

private theorem bijective_moebiusDiscBundleMap (hc₁ : 1 < c) (hc₂ : c < 2) :
    Function.Bijective (moebiusDiscBundleMap hc₁ hc₂) := by
  refine ⟨fun p q h ↦ Subtype.ext (moebiusBandMap_injective hc₁ hc₂ (congrArg Subtype.val h)),
    fun y ↦ ?_⟩
  obtain ⟨p, hp⟩ := exists_moebiusBandMap_eq hc₁ hc₂ (y.property.trans_lt hc₂)
  -- The preimage lies in the disc bundle because its image lies in the sublevel.
  have hpD : p ∈ discBundle ℝ moebiusCore.Fiber :=
    mem_discBundle.2 ((norm_moebiusCore_fiber _).trans_le
      ((projectiveMomentFunction_mk_moebiusVec_le_iff hc₁ hc₂ _ _).1 (hp ▸ y.property)))
  exact ⟨⟨p, hpD⟩, Subtype.ext hp⟩

/-- **The lower sublevels of the height on `ℝP²` are Möbius bands.** Let
`f [x : y : z] = (y² + 2z²) / (x² + y² + z²)` on `ℝP²`, with minimum `[1 : 0 : 0]`, saddle
`[0 : 1 : 0]` and maximum `[0 : 0 : 1]` at the values `0`, `1` and `2`. For `1 < c < 2`, the
sublevel `{f ≤ c}` is homeomorphic to the closed unit disc bundle of the Möbius line bundle over
the circle. The base point of the image of `[x : y : z]` is `(x + i y)² / (x² + y²)`
(`TauCeti.proj_projectivePlaneSublevelMoebiusHomeomorph`), its fibre coordinate has square
`(2 - c) z² / (c x² + (c - 1) y²)`
(`TauCeti.norm_sq_snd_projectivePlaneSublevelMoebiusHomeomorph_of_eq`), and the level `f = c` is
the unit sphere bundle (`TauCeti.projectivePlaneSublevelMoebiusHomeomorph_mem_sphereBundle_iff`).
-/
def projectivePlaneSublevelMoebiusHomeomorph (hc₁ : 1 < c) (hc₂ : c < 2) :
    {y | projectiveMomentFunction ℝ ![0, 1, 2] y ≤ c} ≃ₜ discBundle ℝ moebiusCore.Fiber :=
  -- The disc bundle is compact, being proper over the circle, and the sublevel is Hausdorff.
  haveI : CompactSpace (discBundle ℝ moebiusCore.Fiber) := isCompact_univ_iff.1 (by
    simpa using (isProperMap_discBundle_proj ℝ ℝ moebiusCore.Fiber).isCompact_preimage
      (isCompact_univ (X := Circle)))
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (bijective_moebiusDiscBundleMap hc₁ hc₂))
    (((continuous_moebiusBandMap c).comp continuous_subtypeVal).subtype_mk _)).symm

/-- The sublevel point is the image of its Möbius band vector. -/
private theorem moebiusBandMap_projectivePlaneSublevelMoebiusHomeomorph (hc₁ : 1 < c) (hc₂ : c < 2)
    (y : {y | projectiveMomentFunction ℝ ![0, 1, 2] y ≤ c}) :
    moebiusBandMap c (projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y).val = y :=
  congrArg Subtype.val ((projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂).symm_apply_apply y)

/-- The base point of the Möbius band vector of `[x : y : z]` is `(x + i y)² / (x² + y²)`. -/
theorem coe_proj_projectivePlaneSublevelMoebiusHomeomorph_of_eq (hc₁ : 1 < c) (hc₂ : c < 2)
    {y : {y | projectiveMomentFunction ℝ ![0, 1, 2] y ≤ c}} {v : Fin 3 → ℝ} {hv : v ≠ 0}
    (hy : (y : ℙ ℝ (Fin 3 → ℝ)) = mk ℝ v hv) :
    ((projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y).val.proj : ℂ) =
      (v 0 + v 1 * Complex.I) ^ 2 / (v 0 ^ 2 + v 1 ^ 2 : ℝ) :=
  coe_of_moebiusBandMap_eq_mk
    ((moebiusBandMap_projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y).trans hy)

/-- **The Möbius band is fibred over the core circle.** The bundle projection of the Möbius band
`{f ≤ c}` is the homotopy equivalence `[x : y : z] ↦ (x + i y)² / (x² + y²)` of the sublevel with
the circle (`TauCeti.projectivePlaneSublevelCircleEquiv`). -/
@[simp]
theorem proj_projectivePlaneSublevelMoebiusHomeomorph (hc₁ : 1 < c) (hc₂ : c < 2)
    (y : {y | projectiveMomentFunction ℝ ![0, 1, 2] y ≤ c}) :
    (projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y).val.proj =
      projectivePlaneSublevelCircleEquiv hc₁.le hc₂ y := by
  obtain ⟨y', hy'⟩ := y
  induction y' using ind with | h v hv =>
  exact Circle.ext ((coe_proj_projectivePlaneSublevelMoebiusHomeomorph_of_eq hc₁ hc₂ rfl).trans
    (coe_projectivePlaneSublevelCircleEquiv_apply_of_eq hc₁.le hc₂ rfl).symm)

/-- The fibre coordinate of the Möbius band vector of `[x : y : z]` has square
`(2 - c) z² / (c x² + (c - 1) y²)`. In particular the projective line `z = 0` is the zero
section. -/
theorem norm_sq_snd_projectivePlaneSublevelMoebiusHomeomorph_of_eq (hc₁ : 1 < c) (hc₂ : c < 2)
    {y : {y | projectiveMomentFunction ℝ ![0, 1, 2] y ≤ c}} {v : Fin 3 → ℝ} {hv : v ≠ 0}
    (hy : (y : ℙ ℝ (Fin 3 → ℝ)) = mk ℝ v hv) :
    ‖(projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y).val.snd‖ ^ 2 =
      (2 - c) * v 2 ^ 2 / (c * v 0 ^ 2 + (c - 1) * v 1 ^ 2) := by
  have h := sq_of_moebiusBandMap_eq_mk hc₁ hc₂
    ((moebiusBandMap_projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y).trans hy)
  rw [norm_moebiusCore_fiber]
  exact (sq_abs _).trans h

/-- **The boundary of the Möbius band is the level `f = c`.** A point of the sublevel `{f ≤ c}` goes
to the unit sphere bundle of the Möbius line bundle exactly when it lies on the level `f = c`. -/
theorem projectivePlaneSublevelMoebiusHomeomorph_mem_sphereBundle_iff (hc₁ : 1 < c) (hc₂ : c < 2)
    (y : {y | projectiveMomentFunction ℝ ![0, 1, 2] y ≤ c}) :
    (projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y).val ∈
        sphereBundle ℝ moebiusCore.Fiber ↔
      projectiveMomentFunction ℝ ![0, 1, 2] y = c := by
  conv_rhs => rw [← moebiusBandMap_projectivePlaneSublevelMoebiusHomeomorph hc₁ hc₂ y]
  rw [mem_sphereBundle, norm_moebiusCore_fiber]
  exact (projectiveMomentFunction_mk_moebiusVec_eq_iff hc₁ hc₂ _ _).symm

end MoebiusBand

end TauCeti
