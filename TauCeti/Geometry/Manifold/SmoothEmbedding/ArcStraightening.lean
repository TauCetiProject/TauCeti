/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ApproximatesLinearOn
public import TauCeti.Analysis.Calculus.FDeriv.Strip
public import TauCeti.Analysis.Calculus.MeanValue
public import TauCeti.Analysis.Calculus.Splice
public import TauCeti.Analysis.Convex.Prod
public import TauCeti.Geometry.Manifold.ContMDiff.Atlas
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
public import TauCeti.Topology.Circle.Arc
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Straightening a concordance near an arc

Let `F : S¹ × ℝ → M × ℝ` be a smooth concordance (`TauCeti.SmoothEmbedding.Concordance`) from a
circle embedding `f` to a circle embedding `g` in a boundaryless manifold `M` modelled on a
finite-dimensional real normed space, and let `L : S¹ → M` be a smooth map with which `f` and `g`
agree near a point `z₀`. If `F` agrees with the strip `L × id : (z, t) ↦ (L z, t)` to first order
along the whole line `{z₀} × ℝ` (same values and same derivatives at every `(z₀, t)`), then `F` can
be replaced by a concordance from `f` to `g` which coincides with `L × id` on a neighbourhood of
that line, and with `F` off any prescribed neighbourhood of it
(`TauCeti.SmoothEmbedding.Concordance.exists_eventuallyEq_prodMap_of_mfderiv_eq`).

This is the concordance analogue of straightening a circle embedding near a point
(`TauCeti.SmoothEmbedding.exists_smoothIsotopy_eventuallyEq_of_mfderiv_eq`), with the point
replaced by a line of the annulus. For knots in a sphere it is how a concordance between knots in
connected-sum position is made the standard strip near an arc, which is what the connected sum of
concordances needs.

The new concordance is a splice in coordinates. Read `F` and `L × id` in the coordinates
`(θ, t) ↦ (z₀ exp (θ i), t)` of the annulus and in the chart at `L z₀` times the identity of the
time line, as two maps `k` and `l` of a strip `|θ| < r` into `E × ℝ`. They agree on the line
`θ = 0`, have there the same injective derivative `A` (which does not depend on `t`), and agree
outright near the two ends `t ≤ 0` and `t ≥ 1`, where `F` is `f × id` or `g × id`. With a smooth
cutoff `χ` which is `1` on `[-1, 1]` and vanishes off `(-2, 2)`, the spliced map
`k + χ (θ / δ) (l - k)` (`TauCeti.spliceAlong`) is `l` for `|θ| ≤ δ` and `k` for `|θ| ≥ 2δ`.

* Since `l - k` vanishes on the line, it is `o(θ)` uniformly in `t`, so the term coming from the
  derivative of the cutoff is small, and on a fixed strip the derivative of every spliced map stays
  close to `A`, uniformly in `δ`. A left inverse `P` of `A` then makes `P` of the spliced map
  approximate the identity on the convex strip, so the spliced map is injective there, with
  injective derivative (`Convex.injOn_and_injective_of_norm_hasFDerivAt_sub_le`, via Mathlib's
  `ApproximatesLinearOn.injOn`).
* The image under `F` of the complement of the arc is closed, since `F` is a closed embedding, and
  misses the compact segment `F ({z₀} × [0, 1])`; for small `δ` the modified stretch stays in a
  uniform neighbourhood of that segment avoiding it.
* The splice is a convex combination of `k` and `l`, so it keeps the open slab `0 < t < 1`, and it
  is `k` near the two ends, so the collars are kept.

Read back through the chart, the spliced map is a smooth embedding which is a collared track from
`f` to `g`, that is, a concordance.

## Main results

* `TauCeti.SmoothEmbedding.Concordance.exists_eventuallyEq_prodMap_of_mfderiv_eq`: a concordance
  which agrees with `L × id` to first order along `{z₀} × ℝ` can be replaced by one which agrees
  with `L × id` near `{z₀} × ℝ`, and with the original concordance off a given neighbourhood of
  that line.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer (1976),
  Chapter 8, for concordances and isotopies of embeddings.
* J. F. P. Hudson, *Concordance, isotopy, and diffeotopy*, Ann. of Math. 91 (1970), 425–448.
-/

public section

noncomputable section

open Set Filter Topology Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

/-! ### Coordinates along the line `{z₀} × ℝ` of `S¹ × ℝ` -/

section Coordinates

open Complex (arg)

attribute [local instance] finrank_real_complex_fact'

/-- The angle of `z` seen from `z₀`, in `(-π, π]`. -/
private def angle (z₀ z : Circle) : ℝ := arg (z₀⁻¹ * z : Circle)

/-- Coordinates `(θ, t) ↦ (z₀ exp (θ i), t)` of `S¹ × ℝ` near `{z₀} × ℝ`. -/
private def toCyl (z₀ : Circle) (u : ℝ × ℝ) : Circle × ℝ := (z₀ * Circle.exp u.1, u.2)

/-- The inverse coordinates `(z, t) ↦ (angle z₀ z, t)`. -/
private def ofCyl (z₀ : Circle) (x : Circle × ℝ) : ℝ × ℝ := (angle z₀ x.1, x.2)

private theorem ofCyl_fst (z₀ : Circle) (x : Circle × ℝ) :
    (ofCyl z₀ x).1 = angle z₀ x.1 := rfl

private theorem mul_exp_angle (z₀ z : Circle) : z₀ * Circle.exp (angle z₀ z) = z := by
  simp only [angle, Circle.exp_arg, mul_inv_cancel_left]

private theorem toCyl_ofCyl (z₀ : Circle) (x : Circle × ℝ) : toCyl z₀ (ofCyl z₀ x) = x := by
  simp only [toCyl, ofCyl, angle, Circle.exp_arg, mul_inv_cancel_left]

private theorem angle_mul_exp {z₀ : Circle} {θ : ℝ} (hθ : |θ| < Real.pi) :
    angle z₀ (z₀ * Circle.exp θ) = θ := by
  rw [angle, inv_mul_cancel_left]
  exact Circle.arg_exp (neg_lt_of_abs_lt hθ) (lt_of_abs_lt hθ).le

private theorem ofCyl_toCyl {z₀ : Circle} {u : ℝ × ℝ} (hu : |u.1| < Real.pi) :
    ofCyl z₀ (toCyl z₀ u) = u := by
  simp only [toCyl, ofCyl, angle_mul_exp hu]

private theorem toCyl_zero (z₀ : Circle) (t : ℝ) : toCyl z₀ (0, t) = (z₀, t) := by
  simp [toCyl]

private theorem angle_self (z₀ : Circle) : angle z₀ z₀ = 0 := by
  simp [angle]

private theorem isOpen_setOf_abs_angle_lt (z₀ : Circle) {a : ℝ} (ha : a ≤ Real.pi) :
    IsOpen {z | |angle z₀ z| < a} := by
  have h : {z | |angle z₀ z| < a} = (z₀⁻¹ * ·) ⁻¹' Circle.centeredArc a := by
    ext z; simp only [mem_ofPred_eq, mem_preimage, angle, Circle.mem_centeredArc ha]
  rw [h]
  exact (Circle.isOpen_centeredArc a).preimage (continuous_const.mul continuous_id)

private theorem isOpen_setOf_lt_abs_angle (z₀ : Circle) (a : ℝ) :
    IsOpen {z | a < |angle z₀ z|} := by
  have h : {z | a < |angle z₀ z|} = (z₀⁻¹ * ·) ⁻¹' (Circle.exp '' Icc (-a) a)ᶜ := by
    ext z; simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, angle,
      mem_circleExp_image_Icc_neg_iff, not_le]
  rw [h]
  exact (isClosed_circleExp_image_Icc (-a) a).isOpen_compl.preimage
    (continuous_const.mul continuous_id)

private theorem continuous_toCyl (z₀ : Circle) : Continuous (toCyl z₀) :=
  (continuous_const.mul (Circle.exp.continuous.comp continuous_fst)).prodMk continuous_snd

private theorem contMDiff_toCyl (z₀ : Circle) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ)) ∞ (toCyl z₀) :=
  (contMDiff_mul_left.comp (contMDiff_circleExp.comp contDiff_fst.contMDiff)).prodMk
    contDiff_snd.contMDiff

private theorem contMDiffAt_ofCyl {z₀ : Circle} {x : Circle × ℝ}
    (hx : |angle z₀ x.1| < Real.pi) :
    ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞ (ofCyl z₀) x :=
  (((contMDiffAt_circle_arg hx).comp x.1 contMDiff_mul_left.contMDiffAt).comp x
    contMDiffAt_fst).prodMk_space contMDiffAt_snd

private theorem injective_mfderiv_ofCyl {z₀ : Circle} {x : Circle × ℝ}
    (hx : |angle z₀ x.1| < Real.pi) :
    Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) (ofCyl z₀) x) :=
  (hasLeftInverse_mfderiv_of_comp_eventuallyEq_id
    ((contMDiffAt_ofCyl hx).mdifferentiableAt (by simp))
    ((contMDiff_toCyl z₀).mdifferentiableAt (by simp))
    (Eventually.of_forall fun x => toCyl_ofCyl z₀ x)).injective

end Coordinates

/-! ### Splicing a track in coordinates along the line -/

section Track

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The map `F : S¹ × ℝ → M × ℝ` with its values over the arc `|angle z₀ z| < ρ` replaced by those
of a map `h` of the strip, read through the chart `φ`. -/
private def spliceTrack (F : Circle × ℝ → M × ℝ) (φ : OpenPartialHomeomorph M E) (z₀ : Circle)
    (ρ : ℝ) (h : ℝ × ℝ → E × ℝ) (x : Circle × ℝ) : M × ℝ :=
  if |angle z₀ x.1| < ρ then Prod.map φ.symm id (h (ofCyl z₀ x)) else F x

variable {F : Circle × ℝ → M × ℝ} {φ : OpenPartialHomeomorph M E} {z₀ : Circle} {ρ : ℝ}
  {h : ℝ × ℝ → E × ℝ}

omit [NormedSpace ℝ E] [ChartedSpace E M] in
private theorem spliceTrack_of_abs_lt {x : Circle × ℝ} (hx : |angle z₀ x.1| < ρ) :
    spliceTrack F φ z₀ ρ h x = Prod.map φ.symm id (h (ofCyl z₀ x)) := by
  simp [spliceTrack, hx]

omit [NormedSpace ℝ E] [ChartedSpace E M] in
/-- Where `h` is `F` read in the chart, the spliced track is `F`. -/
private theorem spliceTrack_of_eq (hFφ : ∀ u : ℝ × ℝ, |u.1| < ρ → (F (toCyl z₀ u)).1 ∈ φ.source)
    {x : Circle × ℝ} (hx : |angle z₀ x.1| < ρ →
      h (ofCyl z₀ x) = Prod.map φ id (F (toCyl z₀ (ofCyl z₀ x)))) :
    spliceTrack F φ z₀ ρ h x = F x := by
  unfold spliceTrack
  split_ifs with hlt
  · rw [hx hlt, toCyl_ofCyl]
    have := hFφ (ofCyl z₀ x) hlt
    rw [toCyl_ofCyl] at this
    ext <;> simp [φ.left_inv this]
  · rfl

/-- **The spliced track is immersive over the arc.** Where it is read through the chart, the spliced
track is `h` in the coordinates of the strip, so its derivative is injective wherever that of `h`
is. -/
private theorem injective_mfderiv_spliceTrack (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hρπ : ρ ≤ Real.pi) (hhφ : ∀ u : ℝ × ℝ, |u.1| < ρ → (h u).1 ∈ φ.target)
    (hC : ContDiffOn ℝ ∞ h {u | |u.1| < ρ})
    (hdh : ∀ u : ℝ × ℝ, |u.1| < ρ → Injective (fderiv ℝ h u)) {x : Circle × ℝ}
    (hG : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) (spliceTrack F φ z₀ ρ h) x)
    (hx : |angle z₀ x.1| < ρ) :
    Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) (spliceTrack F φ z₀ ρ h) x) := by
  have hπ : |angle z₀ x.1| < Real.pi := hx.trans_le hρπ
  have hGx : (spliceTrack F φ z₀ ρ h x).1 ∈ φ.source := by
    rw [spliceTrack_of_abs_lt hx]
    exact φ.map_target (hhφ _ hx)
  have hΦ : MDifferentiableAt (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) (Prod.map φ id)
      (spliceTrack F φ z₀ ρ h x) :=
    (contMDiffAt_prodMap_id_of_mem_maximalAtlas hφ hGx).mdifferentiableAt (by simp)
  have hcomp : Prod.map φ id ∘ spliceTrack F φ z₀ ρ h =ᶠ[𝓝 x] h ∘ ofCyl z₀ := by
    filter_upwards [((isOpen_setOf_abs_angle_lt z₀ hρπ).preimage continuous_fst).mem_nhds hx]
      with x' hx'
    rw [comp_apply, spliceTrack_of_abs_lt hx']
    ext <;> simp [φ.right_inv (hhφ (ofCyl z₀ x') hx')]
  have hD := mfderiv_comp x hΦ hG
  rw [hcomp.mfderiv_eq] at hD
  have hinjD : Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) (h ∘ ofCyl z₀) x) := by
    have hS : IsOpen {u : ℝ × ℝ | |u.1| < ρ} :=
      isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
    have hhd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E × ℝ) h (ofCyl z₀ x) :=
      ((hC.contDiffAt (hS.mem_nhds hx)).contMDiffAt).mdifferentiableAt (by simp)
    rw [mfderiv_comp x hhd ((contMDiffAt_ofCyl hπ).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    exact (((NormedSpace.fromTangentSpace _).symm.injective.comp (hdh _ hx)).comp
      (NormedSpace.fromTangentSpace _).injective).comp (injective_mfderiv_ofCyl hπ)
  have hinjD' : Injective ((mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) (Prod.map φ id)
      (spliceTrack F φ z₀ ρ h x)).comp
      (mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) (spliceTrack F φ z₀ ρ h) x)) := by
    rw [← hD]
    exact (tangentSpaceCast 𝓘(ℝ, E × ℝ) _ _).injective.comp hinjD
  exact Injective.of_comp hinjD'

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **The spliced track is a smooth embedding and a collared track.** Let `F` be a smooth
embedding which is a collared track from `f` to `g`, and let `h` be a smooth map of the strip
`|u.1| < ρ` into the chart, injective with injective derivative there, which is `F` read in the
chart where `a ≤ |u.1|` or near the two ends, and whose remaining values avoid the image under `F`
of the complement of the arc. Then the spliced track is again such an embedding. -/
private theorem isSmoothEmbedding_spliceTrack {f g : Circle → M}
    (hF : IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) ∞ F)
    (hFc : IsCollaredTrack f g F) (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {a c₀ c₁ : ℝ} (haρ : a < ρ) (hρπ : ρ ≤ Real.pi)
    (hFφ : ∀ u : ℝ × ℝ, |u.1| < ρ → (F (toCyl z₀ u)).1 ∈ φ.source)
    (hhF : ∀ u : ℝ × ℝ, |u.1| < ρ → (a ≤ |u.1| ∨ u.2 ≤ c₀ ∨ 1 - c₁ ≤ u.2) →
      h u = Prod.map φ id (F (toCyl z₀ u)))
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hhφ : ∀ u : ℝ × ℝ, |u.1| < ρ → (h u).1 ∈ φ.target)
    (hfar : ∀ u : ℝ × ℝ, |u.1| < ρ → h u ≠ Prod.map φ id (F (toCyl z₀ u)) →
      Prod.map φ.symm id (h u) ∉ F '' ({z | ρ ≤ |angle z₀ z|} ×ˢ univ))
    (hsnd : ∀ u : ℝ × ℝ, |u.1| < ρ → u.2 ∈ Ioo 0 1 → (h u).2 ∈ Ioo 0 1)
    (hC : ContDiffOn ℝ ∞ h {u | |u.1| < ρ}) (hinj : InjOn h {u | |u.1| < ρ})
    (hdh : ∀ u : ℝ × ℝ, |u.1| < ρ → Injective (fderiv ℝ h u)) :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) ∞ (spliceTrack F φ z₀ ρ h) ∧
      IsCollaredTrack f g (spliceTrack F φ z₀ ρ h) := by
  set G := spliceTrack F φ z₀ ρ h
  have hFc' : Continuous F := hF.contMDiff.continuous
  have hFinj : Injective F := hF.isEmbedding.injective
  have hS : IsOpen {u : ℝ × ℝ | |u.1| < ρ} := isOpen_lt (continuous_abs.comp continuous_fst)
    continuous_const
  have hA : IsOpen {x : Circle × ℝ | |angle z₀ x.1| < ρ} :=
    (isOpen_setOf_abs_angle_lt z₀ hρπ).preimage continuous_fst
  have hB : IsOpen {x : Circle × ℝ | a < |angle z₀ x.1|} :=
    (isOpen_setOf_lt_abs_angle z₀ a).preimage continuous_fst
  have hGa {x : Circle × ℝ} (hx : |angle z₀ x.1| < ρ) :
      G x = Prod.map φ.symm id (h (ofCyl z₀ x)) :=
    spliceTrack_of_abs_lt hx
  -- `G` is `F` wherever `h` is `F` read in the chart.
  have hGF {x : Circle × ℝ} (hx : |angle z₀ x.1| < ρ →
      h (ofCyl z₀ x) = Prod.map φ id (F (toCyl z₀ (ofCyl z₀ x)))) : G x = F x :=
    spliceTrack_of_eq hFφ hx
  have hGF_far {x : Circle × ℝ} (hx : a ≤ |angle z₀ x.1|) : G x = F x :=
    hGF fun hlt => hhF _ hlt (Or.inl hx)
  -- Near a point of the arc, `G` is `h` read back through the chart.
  have hev {x : Circle × ℝ} (hx : |angle z₀ x.1| < ρ) :
      G =ᶠ[𝓝 x] Prod.map φ.symm id ∘ (h ∘ ofCyl z₀) := by
    filter_upwards [hA.mem_nhds hx] with x' hx'
    exact hGa hx'
  -- Near a point off the arc, `G` is `F`.
  have hevF {x : Circle × ℝ} (hx : ρ ≤ |angle z₀ x.1|) : G =ᶠ[𝓝 x] F := by
    have hax : a < |angle z₀ x.1| := haρ.trans_le hx
    filter_upwards [hB.mem_nhds hax] with x' hx'
    exact hGF_far (le_of_lt hx')
  have hπ {x : Circle × ℝ} (hx : |angle z₀ x.1| < ρ) : |angle z₀ x.1| < Real.pi :=
    hx.trans_le hρπ
  have hhC {x : Circle × ℝ} (hx : |angle z₀ x.1| < ρ) :
      ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) ∞ (h ∘ ofCyl z₀) x :=
    ((hC.contDiffAt (hS.mem_nhds hx)).contMDiffAt).comp x (contMDiffAt_ofCyl (hπ hx))
  have hsmooth : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) ∞ G := by
    intro x
    by_cases hx : |angle z₀ x.1| < ρ
    · exact ((contMDiffAt_prodMap_symm_id_of_mem_maximalAtlas hφ (hhφ _ hx)).comp x
        (hhC hx)).congr_of_eventuallyEq (hev hx)
    · exact (hF.contMDiff x).congr_of_eventuallyEq (hevF (not_lt.1 hx))
  -- Injectivity.
  have hinner {x y : Circle × ℝ} (hx : |angle z₀ x.1| < ρ) (hy : |angle z₀ y.1| < ρ)
      (hxy : G x = G y) : x = y := by
    rw [hGa hx, hGa hy] at hxy
    have h1 : (h (ofCyl z₀ x)).1 = (h (ofCyl z₀ y)).1 :=
      φ.symm.injOn (hhφ _ hx) (hhφ _ hy) (congrArg Prod.fst hxy)
    have h2 : (h (ofCyl z₀ x)).2 = (h (ofCyl z₀ y)).2 := by
      simpa [] using congrArg Prod.snd hxy
    have hxstrip : ofCyl z₀ x ∈ {u : ℝ × ℝ | |u.1| < ρ} := by
      simpa only [mem_ofPred_eq, ofCyl_fst] using hx
    have hystrip : ofCyl z₀ y ∈ {u : ℝ × ℝ | |u.1| < ρ} := by
      simpa only [mem_ofPred_eq, ofCyl_fst] using hy
    have := hinj hxstrip hystrip (Prod.ext h1 h2)
    rw [← toCyl_ofCyl z₀ x, ← toCyl_ofCyl z₀ y, this]
  have hmixed {x y : Circle × ℝ} (hx : |angle z₀ x.1| < ρ) (hy : ρ ≤ |angle z₀ y.1|)
      (hxy : G x = G y) : x = y := by
    rw [hevF hy |>.eq_of_nhds] at hxy
    by_cases hk : h (ofCyl z₀ x) = Prod.map φ id (F (toCyl z₀ (ofCyl z₀ x)))
    · rw [hGF fun _ => hk] at hxy
      exact hFinj hxy
    · refine absurd (⟨y, ⟨hy, mem_univ _⟩, hxy.symm⟩ :
        G x ∈ F '' ({z | ρ ≤ |angle z₀ z|} ×ˢ univ)) ?_
      rw [hGa hx]
      exact hfar _ hx hk
  have hGinj : Injective G := by
    intro x y hxy
    by_cases hx : |angle z₀ x.1| < ρ <;> by_cases hy : |angle z₀ y.1| < ρ
    · exact hinner hx hy hxy
    · exact hmixed hx (not_lt.1 hy) hxy
    · exact (hmixed hy (not_lt.1 hx) hxy.symm).symm
    · rw [hevF (not_lt.1 hx) |>.eq_of_nhds, hevF (not_lt.1 hy) |>.eq_of_nhds] at hxy
      exact hFinj hxy
  -- The collars.
  have hGc : IsCollaredTrack f g G := by
    obtain ⟨ε₀, hε₀, hF₀⟩ := hFc.exists_pos_apply_eq_left
    obtain ⟨ε₁, hε₁, hF₁⟩ := hFc.exists_pos_apply_eq_right
    have hcol {x : Circle × ℝ} (ht : x.2 ≤ c₀ ∨ 1 - c₁ ≤ x.2) : G x = F x :=
      hGF fun hlt => hhF _ hlt (Or.inr ht)
    refine ⟨⟨min ε₀ c₀, lt_min hε₀ hc₀, fun z t ht => ?_⟩,
      ⟨min ε₁ c₁, lt_min hε₁ hc₁, fun z t ht => ?_⟩, fun z t ht => ?_⟩
    · rw [hcol (Or.inl (ht.trans (min_le_right _ _)))]
      exact hF₀ z t (ht.trans (min_le_left _ _))
    · rw [hcol (Or.inr ((sub_le_sub_left (min_le_right _ _) 1).trans ht))]
      exact hF₁ z t ((sub_le_sub_left (min_le_left _ _) 1).trans ht)
    · by_cases hz : |angle z₀ z| < ρ
      · rw [hGa (x := (z, t)) hz]
        exact hsnd (ofCyl z₀ (z, t)) hz ht
      · rw [hevF (x := (z, t)) (not_lt.1 hz) |>.eq_of_nhds]
        exact hFc.snd_apply_mem_Ioo z t ht
  -- Immersion.
  have himm (x : Circle × ℝ) : IsImmersionAt ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) ∞ G x := by
    by_cases hx : |angle z₀ x.1| < ρ
    · exact ((hsmooth.contMDiffOn (s := univ)).isImmersionAt_iff_injective_mfderiv isOpen_univ
        (mem_univ x) (by simp)).2
        (injective_mfderiv_spliceTrack hφ hρπ hhφ hC hdh (hsmooth.mdifferentiableAt (by simp)) hx)
    · exact (hF.isImmersion.isImmersionAt x).congr_of_eventuallyEq (hevF (not_lt.1 hx)).symm
  exact ⟨⟨isImmersion_iff_forall_isImmersionAt.2 himm,
    (hGc.isClosedEmbedding hsmooth.continuous hGinj).isEmbedding⟩, hGc⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- **The derivatives along the line, read in coordinates.** If `F` and `L × id` agree to first
order at the points `(z₀, t)`, then so do the maps `k` and `l` reading them in the coordinates of
the strip and in the chart, and their common derivative is injective when `F` is an immersion. -/
private theorem exists_hasFDerivAt_prodMap_comp {F : Circle × ℝ → M × ℝ}
    (hF : IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) ∞ F) {L : Circle → M}
    (hL : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ L) (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hLφ : L z₀ ∈ φ.source) {t : ℝ} (h₀ : F (z₀, t) = (L z₀, t))
    (h₁ : mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) F (z₀, t) =
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) (Prod.map L id) (z₀, t)) :
    ∃ D : ℝ × ℝ →L[ℝ] E × ℝ, Injective D ∧
      HasFDerivAt (fun u => Prod.map φ id (F (toCyl z₀ u))) D (0, t) ∧
      HasFDerivAt (fun u => Prod.map φ id (Prod.map L id (toCyl z₀ u))) D (0, t) := by
  set x := toCyl z₀ (0, t) with hx
  have hxz : x = (z₀, t) := toCyl_zero z₀ t
  have h₀' : F x = Prod.map L id x := by rw [hxz]; exact h₀
  have h₁' : mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) F x =
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) (Prod.map L id) x := by
    rw [hxz]; exact h₁
  have hFx : (F x).1 ∈ φ.source := by rw [h₀', hxz]; exact hLφ
  set DΦ := mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) (Prod.map φ id) (F x)
  set DF := mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) F x
  set Dc := mfderiv 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ)) (toCyl z₀) (0, t)
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) ((𝓡 1).prod 𝓘(ℝ)) (toCyl z₀) (0, t) Dc :=
    ((contMDiff_toCyl z₀).mdifferentiableAt (by simp)).hasMFDerivAt
  have hΦ : ∀ y, y = F x → HasMFDerivAt (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E × ℝ) (Prod.map φ id) y DΦ := by
    rintro y rfl
    exact ((contMDiffAt_prodMap_id_of_mem_maximalAtlas hφ hFx).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hFd : HasMFDerivAt ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) F x DF :=
    (hF.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have hLd : HasMFDerivAt ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) (Prod.map L id) x DF := by
    have := ((hL.prodMap (contMDiff_id (I := 𝓘(ℝ, ℝ)) (M := ℝ))).mdifferentiableAt (x := x)
      (by simp)).hasMFDerivAt
    rwa [← h₁'] at this
  have hk := (hΦ _ rfl).comp (0, t) (hFd.comp (0, t) hc)
  have hl := (hΦ _ h₀'.symm).comp (0, t) (hLd.comp (0, t) hc)
  refine ⟨DΦ.comp (DF.comp Dc), ?_, hk.hasFDerivAt, hl.hasFDerivAt⟩
  -- Each factor has a left inverse near its point.
  have hΦi : Injective DΦ := by
    refine (hasLeftInverse_mfderiv_of_comp_eventuallyEq_id (g := Prod.map φ.symm id)
      ((contMDiffAt_prodMap_id_of_mem_maximalAtlas hφ hFx).mdifferentiableAt (by simp))
      ?_ ?_).injective
    · exact (contMDiffAt_prodMap_symm_id_of_mem_maximalAtlas hφ (y := Prod.map φ id (F x))
        (φ.map_source hFx)).mdifferentiableAt (by simp)
    · filter_upwards [(φ.open_source.preimage continuous_fst).mem_nhds hFx] with y hy
      ext <;> simp [φ.left_inv hy]
  have hFi : Injective DF := (hF.isImmersion.isImmersionAt x).mfderiv_injective (by simp)
  have hci : Injective Dc := by
    refine (hasLeftInverse_mfderiv_of_comp_eventuallyEq_id (g := ofCyl z₀)
      ((contMDiff_toCyl z₀).mdifferentiableAt (by simp))
      ((contMDiffAt_ofCyl (by rw [toCyl_zero, angle_self, abs_zero]; exact Real.pi_pos)
        ).mdifferentiableAt (by simp)) ?_).injective
    have hzero : |((0 : ℝ), t).1| < Real.pi := by simpa using Real.pi_pos
    filter_upwards [(isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).mem_nhds
      hzero] with u hu
    exact ofCyl_toCyl hu
  exact hΦi.comp (hFi.comp hci)

end Track

section Strip

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M]

/-- **A strip of coordinates along the line.** For a collared track `F` from `f` to `g` which is
`L × id` along `{z₀} × ℝ`, where `f` and `g` agree with `L` near `z₀`, there is a strip
`|u.1| < r` of coordinates on which `F` and `L × id` land in the chart `φ` at `L z₀` and agree near
the two ends, and whose arc lies in a given neighbourhood `U` of `z₀`. -/
private theorem exists_pos_strip {f g L : Circle → M} {F : Circle × ℝ → M × ℝ}
    (hFc : IsCollaredTrack f g F) (hF : Continuous F) (hL : Continuous L) {z₀ : Circle}
    {φ : OpenPartialHomeomorph M E} (hLφ : L z₀ ∈ φ.source) (hf : f =ᶠ[𝓝 z₀] L)
    (hg : g =ᶠ[𝓝 z₀] L) (h₀ : ∀ t, F (z₀, t) = (L z₀, t)) {U : Set Circle} (hU : U ∈ 𝓝 z₀) :
    ∃ r > 0, r ≤ Real.pi ∧ ∃ c₀ > 0, ∃ c₁ > 0,
      (∀ u : ℝ × ℝ, |u.1| < r → (F (toCyl z₀ u)).1 ∈ φ.source) ∧
      (∀ u : ℝ × ℝ, |u.1| < r → L (toCyl z₀ u).1 ∈ φ.source) ∧
      (∀ u : ℝ × ℝ, |u.1| < r → (u.2 ≤ c₀ ∨ 1 - c₁ ≤ u.2) →
        F (toCyl z₀ u) = Prod.map L id (toCyl z₀ u)) ∧
      ∀ z, |angle z₀ z| < r → z ∈ U := by
  obtain ⟨c₀, hc₀, hF₀⟩ := hFc.exists_pos_apply_eq_left
  obtain ⟨c₁, hc₁, hF₁⟩ := hFc.exists_pos_apply_eq_right
  -- Near `0`, the circle coordinate `θ ↦ z₀ exp (θ i)` lands where `f`, `g` and `L` agree, in the
  -- chart, and in `U`.
  have hc : Tendsto (fun θ : ℝ => z₀ * Circle.exp θ) (𝓝 0) (𝓝 z₀) := by
    have h := (continuous_const_mul (M := Circle) z₀).comp Circle.exp.continuous |>.tendsto (0 : ℝ)
    rwa [comp_apply, Circle.exp_zero, mul_one] at h
  have hLsource : ∀ᶠ z in 𝓝 z₀, L z ∈ φ.source :=
    hL.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hLφ)
  have hΘ : ∀ᶠ θ in 𝓝 (0 : ℝ), f (z₀ * Circle.exp θ) = L (z₀ * Circle.exp θ) ∧
      g (z₀ * Circle.exp θ) = L (z₀ * Circle.exp θ) ∧ L (z₀ * Circle.exp θ) ∈ φ.source ∧
      z₀ * Circle.exp θ ∈ U :=
    hc.eventually (hf.and (hg.and (hLsource.and hU)))
  obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hΘ
  have hball' {θ : ℝ} (hθ : |θ| < r₁) := hball θ (by simpa [Real.dist_eq] using hθ)
  -- Over the segment `{0} × [0, 1]`, `F` lands in the chart on a strip.
  obtain ⟨r₂, hr₂, htube⟩ := Metric.eventually_nhds_iff.1
    (isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
      (P := fun θ t => (F (toCyl z₀ (θ, t))).1 ∈ φ.source) fun t _ =>
      (φ.open_source.preimage (continuous_fst.comp (hF.comp (continuous_toCyl z₀)))).mem_nhds
        (x := ((0 : ℝ), t))
        (by simpa [toCyl_zero, h₀] using hLφ))
  simp only [Real.dist_0_eq_abs] at htube
  set r := min (min r₁ r₂) Real.pi
  have hr₁' {u : ℝ × ℝ} (hu : |u.1| < r) : |u.1| < r₁ :=
    hu.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hr₂' {u : ℝ × ℝ} (hu : |u.1| < r) : |u.1| < r₂ :=
    hu.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  -- Near the two ends, `F` is `f × id` or `g × id`, which is `L × id` over the arc.
  have hends (u : ℝ × ℝ) (hu : |u.1| < r) (ht : u.2 ≤ c₀ ∨ 1 - c₁ ≤ u.2) :
      F (toCyl z₀ u) = Prod.map L id (toCyl z₀ u) := by
    obtain ⟨hfθ, hgθ, -, -⟩ := hball' (hr₁' hu)
    rcases ht with ht | ht
    · rw [toCyl, hF₀ _ _ ht]
      simp [hfθ]
    · rw [toCyl, hF₁ _ _ ht]
      simp [hgθ]
  refine ⟨r, lt_min (lt_min hr₁ hr₂) Real.pi_pos, min_le_right _ _, c₀, hc₀, c₁, hc₁,
    fun u hu => ?_, fun u hu => (hball' (hr₁' hu)).2.2.1, hends, fun z hz => ?_⟩
  · by_cases ht : u.2 ∈ Icc (0 : ℝ) 1
    · exact htube (hr₂' hu) u.2 ht
    · rw [hends u hu (by
        rcases not_and_or.1 ht with h | h
        · exact Or.inl ((not_le.1 h).le.trans hc₀.le)
        · exact Or.inr (by linarith [not_le.1 h]))]
      exact (hball' (hr₁' hu)).2.2.1
  · have := (hball' (hr₁' (u := (angle z₀ z, 0)) hz)).2.2.2
    rwa [mul_exp_angle] at this

end Strip

/-! ### Straightening -/

section Straighten

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

namespace SmoothEmbedding.Concordance

/-- **Straightening a concordance near a line.** Let `F` be a smooth concordance from `f` to `g`
between circle embeddings in a boundaryless manifold `M`, and `L` a smooth map of the circle into
`M` with which `f` and `g` agree near `z₀`. If `F` agrees with `L × id` to first order at every
point `(z₀, t)`, then there is a concordance `G` from `f` to `g` which is `L × id` on a
neighbourhood of the line `{z₀} × ℝ`, and is `F` off `U × ℝ` for any given neighbourhood `U` of
`z₀`. -/
theorem exists_eventuallyEq_prodMap_of_mfderiv_eq
    {f g : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ Circle M} (F : Concordance f g)
    {L : Circle → M} (hL : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ L) {z₀ : Circle}
    (hf : ⇑f =ᶠ[𝓝 z₀] L) (hg : ⇑g =ᶠ[𝓝 z₀] L) (h₀ : ∀ t, F (z₀, t) = (L z₀, t))
    (h₁ : ∀ t, mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) F (z₀, t) =
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)) (Prod.map L _root_.id) (z₀, t))
    {U : Set Circle} (hU : U ∈ 𝓝 z₀) :
    ∃ G : Concordance f g, (∀ᶠ z in 𝓝 z₀, ∀ t, G (z, t) = (L z, t)) ∧
      ∀ z ∉ U, ∀ t, G (z, t) = F (z, t) := by
  have hF := F.toSmoothEmbedding.isSmoothEmbedding
  have hFc := F.isCollaredTrack
  set p := L z₀
  set φ := chartAt E p
  have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hpφ : p ∈ φ.source := mem_chart_source E p
  -- Step 1: a strip of coordinates along the line `{z₀} × ℝ`.
  obtain ⟨r, hr, hrπ, c₀, hc₀, c₁, hc₁, hFφ, hLφ, hends, hrU⟩ :=
    exists_pos_strip hFc hF.contMDiff.continuous hL.continuous hpφ hf hg h₀ hU
  set k : ℝ × ℝ → E × ℝ := fun u => Prod.map φ _root_.id (F (toCyl z₀ u)) with hk_def
  set l : ℝ × ℝ → E × ℝ := fun u => Prod.map φ _root_.id (Prod.map L _root_.id (toCyl z₀ u))
    with hl_def
  set W : Set (ℝ × ℝ) := {u | |u.1| < r}
  have hW : IsOpen W := isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hkC : ContDiffOn ℝ ∞ k W := contMDiffOn_iff_contDiffOn.1 fun u hu =>
    ((contMDiffAt_prodMap_id_of_mem_maximalAtlas hφ (hFφ u hu)).comp u
      ((hF.contMDiff.comp (contMDiff_toCyl z₀)) u)).contMDiffWithinAt
  have hlC : ContDiffOn ℝ ∞ l W := contMDiffOn_iff_contDiffOn.1 fun u hu =>
    ((contMDiffAt_prodMap_id_of_mem_maximalAtlas hφ (hLφ u hu)).comp u
      (((hL.prodMap (contMDiff_id (I := 𝓘(ℝ, ℝ)) (M := ℝ))).comp
        (contMDiff_toCyl z₀)) u)).contMDiffWithinAt
  have hkl (u : ℝ × ℝ) (hu : |u.1| < r) (ht : u.2 ≤ c₀ ∨ 1 - c₁ ≤ u.2) : k u = l u := by
    simp only [hk_def, hl_def, hends u hu ht]
  have hkl0 (t : ℝ) : k (0, t) = l (0, t) := by
    simp only [hk_def, hl_def, toCyl_zero, h₀]; rfl
  -- Step 2: along the line, `k` and `l` have the same injective derivative `A`; the derivative of
  -- `l` does not depend on the time coordinate.
  choose D hDi hDk hDl using fun t =>
    exists_hasFDerivAt_prodMap_comp (z₀ := z₀) (t := t) hF hL hφ hpφ (h₀ t) (h₁ t)
  have hlt (u : ℝ × ℝ) (s : ℝ) : fderiv ℝ l (u + (0, s)) = fderiv ℝ l u := by
    have : (fun v => l (v + (0, s))) = fun v => l v + (0, s) := by
      funext v
      simp [hl_def, toCyl]
    rw [← fderiv_comp_add_right, this, fderiv_add_const]
  set A := fderiv ℝ l (0, 0)
  have hA : Injective A := by
    have : A = D 0 := (hDl 0).fderiv
    rw [this]; exact hDi 0
  have hlA (t : ℝ) : fderiv ℝ l (0, t) = A := by simpa using hlt (0, 0) t
  have hkA (t : ℝ) : fderiv ℝ k (0, t) = A :=
    calc fderiv ℝ k (0, t) = D t := (hDk t).fderiv
      _ = fderiv ℝ l (0, t) := (hDl t).fderiv.symm
      _ = A := hlA t
  obtain ⟨P, hP⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hA
  obtain ⟨B, hB⟩ := exists_abs_deriv_spliceCutoff_le
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set ε : ℝ := 1 / (2 * ((‖P‖ + 1) * (3 + 4 * B)))
  have hε : 0 < ε := by positivity
  have hPε : ‖P‖ * ((3 + 4 * B) * ε) ≤ 1 / 2 := by
    have h34 : 0 < 3 + 4 * B := by positivity
    have hscale : ‖P‖ * ((3 + 4 * B) * ε) = ‖P‖ / (2 * (‖P‖ + 1)) := by
      simp only [ε]
      field_simp
    rw [hscale, div_le_iff₀ (by positivity)]
    linarith [norm_nonneg P]
  -- Step 3: on a thinner strip both derivatives stay within `ε` of `A`.
  obtain ⟨ρ₁', hρ₁'0, hρ₁'r, hbound⟩ :=
    exists_pos_forall_norm_fderiv_sub_lt hr zero_le_one hε (hkC.of_le (by simp))
      (hlC.of_le (by simp)) (fun u hu ht => hkl u hu (ht.imp (fun h => (h.trans hc₀).le)
        fun h => by linarith)) hlt (fun t _ => hkA t) fun t _ => hlA t
  have hρ₁r {u : ℝ × ℝ} (hu : |u.1| < ρ₁') : |u.1| < r := hu.trans_le hρ₁'r
  -- Step 4: the image under `F` of the complement of the arc `|angle z₀ z| < ρ` is closed, and a
  -- uniform neighbourhood of the segment `{φ p} × [0, 1]` in the chart avoids it.
  set ρ := ρ₁' / 2
  have hρ : 0 < ρ := half_pos hρ₁'0
  have hρρ₁ : ρ < ρ₁' := half_lt_self hρ₁'0
  have hρπ : ρ ≤ Real.pi := (hρρ₁.trans_le hρ₁'r).le.trans hrπ
  set Cl := F '' ({z | ρ ≤ |angle z₀ z|} ×ˢ univ)
  have hCl : IsClosed Cl := by
    refine (hFc.isClosedEmbedding hF.contMDiff.continuous hF.isEmbedding.injective).isClosedMap _
      (IsClosed.prod ?_ isClosed_univ)
    simpa [compl_ofPred, not_lt] using (isOpen_setOf_abs_angle_lt z₀ hρπ).isClosed_compl
  set O' := (φ.target ×ˢ univ) ∩ Prod.map φ.symm _root_.id ⁻¹' Clᶜ
  have hO' : IsOpen O' :=
    ((φ.continuousOn_symm.comp continuousOn_fst
      fun (y : E × ℝ) (hy : y ∈ φ.target ×ˢ univ) => hy.1).prodMk
      continuousOn_snd).isOpen_inter_preimage (φ.open_target.prod isOpen_univ) hCl.isOpen_compl
  have hpO' (t : ℝ) : (φ p, t) ∈ O' := by
    refine ⟨⟨φ.map_source hpφ, mem_univ _⟩, ?_⟩
    rintro ⟨⟨z, s⟩, ⟨hz, -⟩, hzs⟩
    have : (z, s) = (z₀, t) := by
      have hzs' : F (z, s) = F (z₀, t) := by
        rw [hzs, h₀ t]
        simp [φ.left_inv hpφ]
      exact hF.isEmbedding.injective hzs'
    have hz' : ρ ≤ |angle z₀ z| := hz
    have hzz₀ : z = z₀ := congrArg Prod.fst this
    rw [hzz₀, angle_self, abs_zero] at hz'
    exact absurd hz' (not_le.2 hρ)
  obtain ⟨ε', hε', hε'O⟩ := (isCompact_singleton.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1)))
    |>.exists_thickening_subset_open hO' (by
      rintro ⟨y, t⟩ ⟨hy, -⟩
      obtain rfl : y = φ p := hy
      exact hpO' t)
  have hballO' {y : E × ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hy : dist y (φ p, t) < ε') :
      y ∈ O' :=
    hε'O (Metric.mem_thickening_iff.2 ⟨(φ p, t), ⟨rfl, ht⟩, hy⟩)
  -- Near the segment, `k` and `l` stay within `ε'` of it.
  obtain ⟨ρ₂, hρ₂, hρ₂O⟩ := Metric.eventually_nhds_iff.1
    (isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
      (P := fun θ t => ((θ, t) : ℝ × ℝ) ∈
        W ∩ (fun u => (dist (k u) (φ p, u.2), dist (l u) (φ p, u.2))) ⁻¹' Iio ε' ×ˢ Iio ε')
      fun t _ => IsOpen.mem_nhds (x := ((0 : ℝ), t)) (((continuous_dist.comp_continuousOn
        (hkC.continuousOn.prodMk (continuousOn_const.prodMk continuousOn_snd))).prodMk
        (continuous_dist.comp_continuousOn
          (hlC.continuousOn.prodMk (continuousOn_const.prodMk continuousOn_snd)))
        ).isOpen_inter_preimage hW (isOpen_Iio.prod isOpen_Iio))
      ⟨by simpa [W] using hr, by simpa [hk_def, hl_def, toCyl_zero, h₀, p] using hε'⟩)
  simp only [Real.dist_0_eq_abs] at hρ₂O
  -- Step 5: the splice at a small scale `δ`.
  set δ := min ρ ρ₂ / 4
  have hδ : 0 < δ := by positivity
  have hm : 0 < min ρ ρ₂ := lt_min hρ hρ₂
  have hδρ : 2 * δ < ρ := by simp only [δ]; linarith [min_le_left ρ ρ₂]
  have hδρ₂ : 2 * δ < ρ₂ := by simp only [δ]; linarith [min_le_right ρ ρ₂]
  set h := spliceAlong (ContinuousLinearMap.fst ℝ ℝ ℝ) k l δ
  have hhk (u : ℝ × ℝ) (hu : |u.1| < r) (h' : 2 * δ ≤ |u.1| ∨ u.2 ≤ c₀ ∨ 1 - c₁ ≤ u.2) :
      h u = k u := by
    rcases h' with h' | h'
    · exact spliceAlong_of_le_abs hδ h'
    · exact spliceAlong_of_eq (hkl u hu h')
  -- Where `h` differs from `k`, it lies in `O'`.
  have hhO' (u : ℝ × ℝ) (hu : |u.1| < r) (hne : h u ≠ k u) : h u ∈ O' := by
    have hu₁ : |u.1| < 2 * δ := not_le.1 fun h' => hne (hhk u hu (Or.inl h'))
    have ht : u.2 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · by_contra h'; exact hne (hhk u hu (Or.inr (Or.inl (by linarith [not_le.1 h']))))
      · by_contra h'; exact hne (hhk u hu (Or.inr (Or.inr (by linarith [not_le.1 h']))))
    have hmem := (hρ₂O (hu₁.trans hδρ₂) u.2 ht).2
    exact hballO' ht (spliceAlong_mem (convex_ball (φ p, u.2) ε') (Metric.mem_ball.2 hmem.1)
      (Metric.mem_ball.2 hmem.2))
  -- The derivative of the splice stays close to `A`.
  have hdk (v : ℝ × ℝ) (hv : |v.1| < ρ₁') : HasFDerivAt k (fderiv ℝ k v) v :=
    ((hkC.contDiffAt (hW.mem_nhds (hρ₁r hv))).differentiableAt (by simp)).hasFDerivAt
  have hdl (v : ℝ × ℝ) (hv : |v.1| < ρ₁') : HasFDerivAt l (fderiv ℝ l v) v :=
    ((hlC.contDiffAt (hW.mem_nhds (hρ₁r hv))).differentiableAt (by simp)).hasFDerivAt
  have hderiv (u : ℝ × ℝ) (hu : |u.1| < ρ₁') :
      ∃ h' : ℝ × ℝ →L[ℝ] E × ℝ, HasFDerivAt h h' u ∧ ‖h' - A‖ ≤ (3 + 4 * B) * ε := by
    -- `l - k` vanishes on the line `u.1 = 0`, so it is at most `2 ε |u.1|` on the strip.
    have hzero : ((0 : ℝ), u.2) ∈ {v : ℝ × ℝ | |v.1| < ρ₁'} := by
      simpa using hρ₁'0
    have hdist : ‖u - ((0 : ℝ), u.2)‖ = |u.1| := by
      simp [Prod.norm_def, Real.norm_eq_abs]
    have hlk := (convex_setOf_abs_fst_lt (W := ℝ) ρ₁').norm_sub_le_of_norm_hasFDerivWithin_sub_le
      (fun v hv => (hdk v hv).hasFDerivWithinAt) (fun v hv => (hdl v hv).hasFDerivWithinAt)
      (fun v hv => (hbound v hv).1.le) (fun v hv => (hbound v hv).2.le) hu
      hzero (hkl0 u.2)
    rw [hdist] at hlk
    exact exists_hasFDerivAt_spliceAlong_sub_le hδ (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) hB
      (hdk u hu) (hdl u hu) (hbound u hu).1.le (hbound u hu).2.le hlk
  choose! h' hh' hh'A using hderiv
  obtain ⟨hinj, hinj'⟩ :=
    (convex_setOf_abs_fst_lt (W := ℝ) ρ₁').injOn_and_injective_of_norm_hasFDerivAt_sub_le hP hh'
      fun u hu => (mul_le_mul_of_nonneg_left (hh'A u hu) (norm_nonneg P)).trans hPε
  have hstrip {u : ℝ × ℝ} (hu : |u.1| < ρ) : |u.1| < ρ₁' := hu.trans hρρ₁
  obtain ⟨hemb, hcol⟩ := isSmoothEmbedding_spliceTrack (h := h) (a := 2 * δ) hF hFc hφ hδρ hρπ
    (fun u hu => hFφ u (hρ₁r (hstrip hu))) (fun u hu h'' => hhk u (hρ₁r (hstrip hu)) h'') hc₀ hc₁
    (fun u hu => by
      by_cases hne : h u = k u
      · rw [hne]; exact φ.map_source (hFφ u (hρ₁r (hstrip hu)))
      · exact (hhO' u (hρ₁r (hstrip hu)) hne).1.1)
    (fun u hu hne => (hhO' u (hρ₁r (hstrip hu)) hne).2)
    (fun u hu ht => by
      have hS : Convex ℝ {y : E × ℝ | y.2 ∈ Ioo (0 : ℝ) 1} :=
        (convex_Ioo (0 : ℝ) 1).linear_preimage (LinearMap.snd ℝ E ℝ)
      exact spliceAlong_mem hS (hFc.snd_apply_mem_Ioo _ _ ht) ht)
    ((contDiffOn_spliceAlong hkC hlC _ δ).mono fun u hu => hρ₁r (hstrip hu))
    (hinj.mono fun u hu => hstrip hu)
    (fun u hu => (hh' u (hstrip hu)).fderiv ▸ hinj' u (hstrip hu))
  let G : Concordance f g := ⟨SmoothEmbedding.ofIsSmoothEmbedding _ hemb, by simpa using hcol⟩
  have hG (x : Circle × ℝ) : G x = spliceTrack F φ z₀ ρ h x := by
    rw [← coe_toSmoothEmbedding, SmoothEmbedding.ofIsSmoothEmbedding_apply]
    rfl
  refine ⟨G, ?_, fun z hz t => ?_⟩
  · -- Near `z₀`, the new track is `L × id`.
    have hz₀ : |angle z₀ z₀| < δ := by simpa only [angle_self, abs_zero] using hδ
    filter_upwards [(isOpen_setOf_abs_angle_lt z₀ (by linarith : δ ≤ Real.pi)).mem_nhds hz₀]
      with z hz t
    have hzρ : |angle z₀ (z, t).1| < ρ := (le_of_lt hz).trans_lt (by linarith)
    have hhl : h (ofCyl z₀ (z, t)) = l (ofCyl z₀ (z, t)) :=
      spliceAlong_of_abs_le hδ (le_of_lt hz)
    rw [hG, spliceTrack_of_abs_lt hzρ, hhl]
    have hL' := hLφ (ofCyl z₀ (z, t)) (hρ₁r (hstrip hzρ))
    simp only [hl_def, toCyl_ofCyl] at hL' ⊢
    simp [φ.left_inv hL']
  · -- Off `U`, the new track is `F`.
    have hzρ : ρ ≤ |angle z₀ z| := by
      by_contra h''
      exact hz (hrU z ((not_le.1 h'').trans (hρρ₁.trans_le hρ₁'r)))
    have hzfar : ¬ |angle z₀ (z, t).1| < ρ := not_lt.2 hzρ
    simp only [hG, spliceTrack, hzfar, ite_false]

end SmoothEmbedding.Concordance

end Straighten

end TauCeti
