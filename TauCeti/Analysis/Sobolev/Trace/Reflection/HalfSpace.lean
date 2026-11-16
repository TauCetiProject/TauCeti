/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Analysis.Sobolev.Trace.Reflection.Higher

/-!
# Finite-order extension across a half-space boundary

Functions of class Cᵏ on a closed half-space admit Cᵏ extensions by finite reflection.
The `K`-term operator preserves Cⁿ regularity whenever `n < K`.
Local versions extend near a boundary point; slab versions give Cⁿ regularity of the reflection
on `Ioo (-T) T ×ˢ A`.

## References

M. R. Hestenes, “Extension of the range of a differentiable function”,
Duke Math. J. 8 (1941), 183–192.

Related public formalization work (these repository links do not identify a ported file):
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped Topology ContDiff BigOperators

noncomputable section

namespace TauCeti.HalfSpaceExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The bounded linear time dilation leaving the spatial coordinate unchanged. -/
def timeScale (a : ℝ) : (ℝ × E) →L[ℝ] ℝ × E :=
  (a • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)

/-- Time dilation multiplies only the time coordinate. -/
@[simp] theorem timeScale_apply (a : ℝ) (x : ℝ × E) :
    timeScale a x = (a * x.1, x.2) := (rfl)

/-- Expand a time-dilated multilinear term by its subset of time-direction slots. -/
theorem map_timeScale_eq_sum_pow_card_smul {m : ℕ}
    (A : (ℝ × E) [×m]→L[ℝ] F) (a : ℝ) (v : Fin m → ℝ × E) :
    A (fun i ↦ timeScale a (v i)) =
      ∑ s : Finset (Fin m), a ^ s.card •
        A (s.piecewise (fun i ↦ ((v i).1, (0 : E))) (fun i ↦ (0, (v i).2))) := by
  classical
  let vt : Fin m → ℝ × E := fun i ↦ ((v i).1, 0)
  let vx : Fin m → ℝ × E := fun i ↦ (0, (v i).2)
  have hsplit : (fun i ↦ timeScale a (v i)) = (fun i ↦ a • vt i) + vx := by
    funext i
    ext <;> simp [vt, vx]
  rw [hsplit, A.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  have hpiece : s.piecewise (fun i ↦ a • vt i) vx =
      fun i ↦ (if i ∈ s then a else 1) • s.piecewise vt vx i := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hpiece, A.map_smul_univ]
  congr 1
  simp

/-- For multilinear order `m < K`, the coefficient-weighted sum of a multilinear map
precomposed with the reflection time dilations equals the original map. -/
theorem sum_higherReflectionCoeff_smul_compContinuousLinearMap_timeScale
    {K m : ℕ} (A : (ℝ × E) [×m]→L[ℝ] F) (hm : m < K) :
    (∑ j, higherReflectionCoeff K j •
      A.compContinuousLinearMap (fun _ ↦ timeScale (higherReflectionNode j))) = A := by
  classical
  ext v
  simp only [sum_apply, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [map_timeScale_eq_sum_pow_card_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hmoment (s : Finset (Fin m)) :
      ∑ j, higherReflectionCoeff K j * higherReflectionNode j ^ s.card = 1 := by
    have hcard : s.card ≤ m := by simpa using s.card_le_univ
    exact sum_higherReflectionCoeff_mul_pow (hcard.trans_lt hm)
  simp_rw [hmoment, one_smul]
  rw [← A.map_add_univ]
  congr 1
  funext i
  ext <;> simp

/-- The closed nonnegative-time half-space, with unrestricted spatial coordinate. -/
def upperHalfSpace (E : Type*) : Set (ℝ × E) := Ici 0 ×ˢ univ

/-- The closed nonpositive-time half-space, with unrestricted spatial coordinate. -/
def lowerHalfSpace (E : Type*) : Set (ℝ × E) := Iic 0 ×ˢ univ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Membership in the upper half-space is nonnegativity of time. -/
@[simp] theorem mem_upperHalfSpace {x : ℝ × E} : x ∈ upperHalfSpace E ↔ 0 ≤ x.1 := by
  simp [upperHalfSpace]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Membership in the lower half-space is nonpositivity of time. -/
@[simp] theorem mem_lowerHalfSpace {x : ℝ × E} : x ∈ lowerHalfSpace E ↔ x.1 ≤ 0 := by
  simp [lowerHalfSpace]

omit [NormedSpace ℝ E] in
/-- The upper half-space is closed. -/
theorem isClosed_upperHalfSpace : IsClosed (upperHalfSpace E) :=
  isClosed_Ici.prod isClosed_univ

omit [NormedSpace ℝ E] in
/-- The lower half-space is closed. -/
theorem isClosed_lowerHalfSpace : IsClosed (lowerHalfSpace E) :=
  isClosed_Iic.prod isClosed_univ

/-- Within-set derivatives are unique on the upper half-space. -/
theorem uniqueDiffOn_upperHalfSpace : UniqueDiffOn ℝ (upperHalfSpace E) :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- Within-set derivatives are unique on the lower half-space. -/
theorem uniqueDiffOn_lowerHalfSpace : UniqueDiffOn ℝ (lowerHalfSpace E) :=
  (uniqueDiffOn_Iic 0).prod uniqueDiffOn_univ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The two closed time half-spaces cover the whole product space. -/
theorem upperHalfSpace_union_lowerHalfSpace : upperHalfSpace E ∪ lowerHalfSpace E = univ := by
  ext x
  simp only [mem_union, mem_upperHalfSpace, mem_lowerHalfSpace, mem_univ, iff_true]
  exact le_total 0 x.1

/-- `K`-term higher-order reflection of `f` along each time line `t ↦ f (t, x.2)`, extending
`f` from the upper half-space. -/
def halfSpaceReflection (K : ℕ) (f : ℝ × E → F) (x : ℝ × E) : F :=
  higherReflection K (fun t ↦ f (t, x.2)) x.1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Half-space reflection is additive in the input. -/
theorem halfSpaceReflection_add (K : ℕ) (f g : ℝ × E → F) :
    halfSpaceReflection K (f + g) = halfSpaceReflection K f + halfSpaceReflection K g := by
  funext x
  exact congrFun (higherReflection_add K (fun t ↦ f (t, x.2)) (fun t ↦ g (t, x.2))) x.1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Half-space reflection commutes with real scalar multiplication. -/
theorem halfSpaceReflection_smul (K : ℕ) (c : ℝ) (f : ℝ × E → F) :
    halfSpaceReflection K (c • f) = c • halfSpaceReflection K f := by
  funext x
  exact congrFun (higherReflection_smul K c (fun t ↦ f (t, x.2))) x.1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Reflection agrees with the input at nonnegative times. -/
@[simp] theorem halfSpaceReflection_of_nonneg (K : ℕ) (f : ℝ × E → F)
    {x : ℝ × E} (hx : 0 ≤ x.1) : halfSpaceReflection K f x = f x :=
  higherReflection_of_nonneg K _ hx

/-- At negative times reflection is the coefficient-weighted sum of time dilations. -/
@[simp] theorem halfSpaceReflection_of_neg (K : ℕ) (f : ℝ × E → F)
    {x : ℝ × E} (hx : x.1 < 0) :
    halfSpaceReflection K f x =
      ∑ j, higherReflectionCoeff K j • f (timeScale (higherReflectionNode j) x) := by
  simp only [halfSpaceReflection, higherReflection_of_neg K _ hx,
    higherReflectionLower_apply, timeScale_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Reflection extends the input on the closed upper half-space. -/
theorem halfSpaceReflection_eqOn_upperHalfSpace (K : ℕ) (f : ℝ × E → F) :
    EqOn (halfSpaceReflection K f) f (upperHalfSpace E) :=
  fun _ hx ↦ halfSpaceReflection_of_nonneg K f (mem_upperHalfSpace.mp hx)

/-- Reflecting a nonpositive time at a negative node lands in the upper half-space. -/
theorem timeScale_higherReflectionNode_mem_upperHalfSpace {K : ℕ} (j : Fin K)
    {x : ℝ × E} (hx : x.1 ≤ 0) : timeScale (higherReflectionNode j) x ∈ upperHalfSpace E :=
  mem_upperHalfSpace.mpr (mul_nonneg_of_nonpos_of_nonpos (higherReflectionNode_neg j).le hx)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Reflection depends only on the input on the upper half-space. -/
theorem halfSpaceReflection_congr {K : ℕ} {f g : ℝ × E → F}
    (hfg : EqOn f g (upperHalfSpace E)) : halfSpaceReflection K f = halfSpaceReflection K g := by
  funext x
  exact congrFun (higherReflection_congr
    (fun t ht ↦ hfg ((mem_upperHalfSpace (x := (t, x.2))).mpr ht))) x.1

/-- The `K`-term reflection of a Cⁿ map on the closed upper half-space is globally Cⁿ
whenever `n < K`. -/
theorem contDiff_halfSpaceReflection {n K : ℕ} (hn : n < K)
    (f : ℝ × E → F)
    (hf : ContDiffOn ℝ n f (upperHalfSpace E)) :
    ContDiff ℝ n (halfSpaceReflection K f) := by
  classical
  let p : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F :=
    ftaylorSeriesWithin ℝ f (upperHalfSpace E)
  have hp : HasFTaylorSeriesUpToOn n f p (upperHalfSpace E) :=
    hf.ftaylorSeriesWithin uniqueDiffOn_upperHalfSpace
  let g : ℝ × E → F := fun x ↦
    ∑ j, higherReflectionCoeff K j • f (timeScale (higherReflectionNode j) x)
  let q : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F := fun x m ↦
    ∑ j, higherReflectionCoeff K j •
      (p (timeScale (higherReflectionNode j) x) m).compContinuousLinearMap
      (fun _ ↦ timeScale (higherReflectionNode j))
  have hq : HasFTaylorSeriesUpToOn n g q (lowerHalfSpace E) := by
    apply HasFTaylorSeriesUpToOn.sum (u := Finset.univ)
    intro j _
    apply ((hp.compContinuousLinearMap (timeScale (higherReflectionNode j))).const_smul
      (higherReflectionCoeff K j)).mono
    intro x hx
    exact timeScale_higherReflectionNode_mem_upperHalfSpace j (mem_lowerHalfSpace.mp hx)
  have hmatch : ∀ x ∈ upperHalfSpace E ∩ lowerHalfSpace E,
      ∀ m : ℕ, m ≤ (n : ℕ∞) → p x m = q x m := by
    intro x hx m hm
    have htime : x.1 = 0 := le_antisymm (mem_lowerHalfSpace.mp hx.2) (mem_upperHalfSpace.mp hx.1)
    have hscale (j : Fin K) : timeScale (higherReflectionNode j) x = x := by
      ext <;> simp [htime]
    dsimp only [q]
    simp_rw [hscale]
    exact (sum_higherReflectionCoeff_smul_compContinuousLinearMap_timeScale (p x m) (by
      exact lt_of_le_of_lt (by exact_mod_cast hm) hn)).symm
  have hglue := hp.contDiff_piecewise hq isClosed_upperHalfSpace isClosed_lowerHalfSpace
    upperHalfSpace_union_lowerHalfSpace hmatch
  convert hglue using 1
  funext x
  by_cases hx : 0 ≤ x.1
  · rw [halfSpaceReflection_of_nonneg _ _ hx,
      Set.piecewise_eq_of_mem _ _ _ (mem_upperHalfSpace.mpr hx)]
  · rw [halfSpaceReflection_of_neg _ _ (lt_of_not_ge hx),
      Set.piecewise_eq_of_notMem _ _ _ (fun h ↦ hx (mem_upperHalfSpace.mp h))]

/-- Every Cᵏ function on the closed upper half-space admits a constructed global Cᵏ extension. -/
theorem exists_contDiff_extension_halfSpace (k : ℕ) (f : ℝ × E → F)
    (hf : ContDiffOn ℝ k f (upperHalfSpace E)) :
    ∃ g : ℝ × E → F, ContDiff ℝ k g ∧ EqOn g f (upperHalfSpace E) := by
  exact ⟨halfSpaceReflection (k + 1) f,
    contDiff_halfSpaceReflection (Nat.lt_succ_self k) f hf,
    halfSpaceReflection_eqOn_upperHalfSpace (k + 1) f⟩

/-- A Cᵏ function near a boundary point on the closed upper half-space has a global Cᵏ extension
agreeing locally on that side. -/
theorem exists_local_contDiff_extension_halfSpace [HasContDiffBump (ℝ × E)]
    (k : ℕ) (f : ℝ × E → F) {V : Set (ℝ × E)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ k f (upperHalfSpace E ∩ V)) (p : E) (hp : (0, p) ∈ V) :
    ∃ g : ℝ × E → F, ContDiff ℝ k g ∧
      ∀ᶠ z in 𝓝 ((0 : ℝ), p), 0 ≤ z.1 → g z = f z := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hp)
  let β : ContDiffBump ((0 : ℝ), p) :=
    { rIn := δ / 4
      rOut := δ / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hβV : tsupport β ⊆ V := by
    rw [β.tsupport_eq]
    intro z hz
    apply hsub
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by dsimp [β]; linarith)
  let H : ℝ × E → F := fun z ↦ β z • f z
  have hH : ContDiffOn ℝ k H (upperHalfSpace E) := by
    intro z hz
    by_cases hzβ : z ∈ tsupport β
    · have hlocal : ContDiffWithinAt ℝ k f (upperHalfSpace E) z :=
        (contDiffWithinAt_inter (hV.mem_nhds (hβV hzβ))).mp (hf z ⟨hz, hβV hzβ⟩)
      exact β.contDiffAt.contDiffWithinAt.smul hlocal
    · have hzero : ContDiffAt ℝ k H z := by
        apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzβ] with y hy
        simp only [H, hy, Pi.zero_apply, zero_smul]
      exact hzero.contDiffWithinAt
  obtain ⟨g, hg, hgeq⟩ := exists_contDiff_extension_halfSpace k H hH
  refine ⟨g, hg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds ((0 : ℝ), p) β.rIn_pos] with z hz htime
  rw [hgeq (mem_upperHalfSpace.mpr htime)]
  dsimp only [H]
  rw [β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul]

/-- Reflection preserves local equality on the upper side near the time-zero boundary. -/
theorem halfSpaceReflection_eventuallyEq_nhds_boundary {K : ℕ} {f g : ℝ × E → F} {p : E}
    (hfg : ∀ᶠ z in 𝓝 ((0 : ℝ), p), 0 ≤ z.1 → f z = g z) :
    halfSpaceReflection K f =ᶠ[𝓝 ((0 : ℝ), p)] halfSpaceReflection K g := by
  classical
  have hscaled : ∀ j : Fin K, ∀ᶠ z in 𝓝 ((0 : ℝ), p),
      0 ≤ (timeScale (higherReflectionNode j) z).1 →
        f (timeScale (higherReflectionNode j) z) =
          g (timeScale (higherReflectionNode j) z) := by
    intro j
    have ht : Tendsto (timeScale (higherReflectionNode j) : ℝ × E → ℝ × E)
        (𝓝 ((0 : ℝ), p)) (𝓝 ((0 : ℝ), p)) := by
      have hcont : ContinuousAt (timeScale (higherReflectionNode j) : ℝ × E → ℝ × E)
          ((0 : ℝ), p) := (timeScale (higherReflectionNode j)).continuous.continuousAt
      simpa only [timeScale_apply, mul_zero] using hcont.tendsto
    exact ht.eventually hfg
  filter_upwards [hfg, Filter.eventually_all.mpr hscaled] with z hz hzs
  by_cases htime : 0 ≤ z.1
  · simp only [halfSpaceReflection_of_nonneg _ _ htime]
    exact hz htime
  · have hneg : z.1 < 0 := lt_of_not_ge htime
    simp only [halfSpaceReflection_of_neg _ _ hneg]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun v : F ↦ higherReflectionCoeff K j • v)
      (hzs j (mem_upperHalfSpace.mp
        (timeScale_higherReflectionNode_mem_upperHalfSpace j hneg.le)))

/-- If `f` is Cⁿ on the upper half-space near `(0, p)` and `n < K`, then
`halfSpaceReflection K f` is Cⁿ at `(0, p)`. -/
theorem contDiffAt_halfSpaceReflection_boundary [HasContDiffBump (ℝ × E)]
    {n K : ℕ} (hn : n < K)
    (f : ℝ × E → F) {V : Set (ℝ × E)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ n f (upperHalfSpace E ∩ V)) (p : E) (hp : (0, p) ∈ V) :
    ContDiffAt ℝ n (halfSpaceReflection K f) (0, p) := by
  obtain ⟨g, hg, hgeq⟩ := exists_local_contDiff_extension_halfSpace n f hV hf p hp
  apply (contDiff_halfSpaceReflection hn g hg.contDiffOn).contDiffAt.congr_of_eventuallyEq
  exact halfSpaceReflection_eventuallyEq_nhds_boundary
    (hgeq.mono (fun _ h htime ↦ (h htime).symm))

/-- If `n < K`, the `K`-term reflection of a forward-time Cⁿ function on an open spatial
domain is Cⁿ on the two-sided slab `Ioo (-T) T ×ˢ A`. -/
theorem contDiffOn_halfSpaceReflection_slab [HasContDiffBump (ℝ × E)]
    {n K : ℕ} (hn : n < K)
    (f : ℝ × E → F) {T : ℝ} {A : Set E} (hA : IsOpen A)
    (hf : ContDiffOn ℝ n f (Ico 0 T ×ˢ A)) :
    ContDiffOn ℝ n (halfSpaceReflection K f)
      (Ioo (-T) T ×ˢ A) := by
  classical
  apply (isOpen_Ioo.prod hA).contDiffOn_iff.mpr
  intro ⟨t, x⟩ ht
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · have hscaled (j : Fin K) : timeScale (higherReflectionNode j) (t, x) ∈
        Ioo 0 T ×ˢ A := by
      have hj : 1 ≤ (j : ℝ) + 1 := by
        linarith [Nat.cast_nonneg (α := ℝ) (j : ℕ)]
      refine ⟨⟨mul_pos_of_neg_of_neg (higherReflectionNode_neg j) hneg, ?_⟩, ht.2⟩
      calc
        higherReflectionNode j * t = (-t) / ((j : ℝ) + 1) := by
          rw [higherReflectionNode_eq]
          ring
        _ ≤ -t := div_le_self (neg_nonneg.mpr hneg.le) hj
        _ < T := by linarith [ht.1.1]
    have hsum : ContDiffAt ℝ n
        (fun z : ℝ × E ↦ ∑ j, higherReflectionCoeff K j •
          f (timeScale (higherReflectionNode j) z)) (t, x) := by
      apply ContDiffAt.sum
      intro j _
      have hfj : ContDiffAt ℝ n f (timeScale (higherReflectionNode j) (t, x)) :=
        hf.contDiffAt (prod_mem_nhds (Ico_mem_nhds_iff.mpr (hscaled j).1)
          (hA.mem_nhds (hscaled j).2))
      have hscaleSmooth : ContDiff ℝ n
          (timeScale (higherReflectionNode j) : (ℝ × E) → ℝ × E) :=
        (timeScale (higherReflectionNode j) : (ℝ × E) →L[ℝ] ℝ × E).contDiff
      exact (hfj.comp (t, x) hscaleSmooth.contDiffAt).const_smul (higherReflectionCoeff K j)
    apply hsum.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hneg] with z hz
    exact halfSpaceReflection_of_neg K f hz
  · subst t
    have hf0 : ContDiffOn ℝ n f (upperHalfSpace E ∩ (Iio T ×ˢ A)) :=
      hf.mono (fun _ hz ↦ ⟨⟨mem_upperHalfSpace.mp hz.1, hz.2.1⟩, hz.2.2⟩)
    exact contDiffAt_halfSpaceReflection_boundary hn f
      (isOpen_Iio.prod hA) hf0 x ⟨ht.1.2, ht.2⟩
  · have hft : ContDiffAt ℝ n f (t, x) :=
      hf.contDiffAt (prod_mem_nhds (Ico_mem_nhds_iff.mpr ⟨hpos, ht.1.2⟩)
        (hA.mem_nhds ht.2))
    apply hft.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hpos] with z hz
    exact halfSpaceReflection_of_nonneg _ _ hz.le

end TauCeti.HalfSpaceExtension

end
