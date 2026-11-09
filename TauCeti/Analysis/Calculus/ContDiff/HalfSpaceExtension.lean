/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Finite-order extension across a half-space boundary

Functions of class Cᵏ on a closed half-space admit Cᵏ extensions by finite reflection.
The coefficients solve the Vandermonde moment equations through order k. The reflected
Taylor series match at the boundary. Local and slab versions support initial-time
extensions of coordinate vector fields for smooth Ricci-flow restart.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter Matrix
open scoped Topology ContDiff BigOperators

noncomputable section

namespace TauCeti.HalfSpaceExtension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Matching values and one common Taylor series glue across two closed sets at every allowed
Taylor order. -/
private theorem hasFTaylorSeriesUpToOn_union {k : ℕ∞ω} {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F} {s t : Set E}
    (hs : IsClosed s) (ht : IsClosed t)
    (hfs : HasFTaylorSeriesUpToOn k f p s)
    (hft : HasFTaylorSeriesUpToOn k f p t) :
    HasFTaylorSeriesUpToOn k f p (s ∪ t) := by
  classical
  constructor
  · intro x hx
    exact hx.elim (hfs.zero_eq x) (hft.zero_eq x)
  · intro m hm x _
    apply HasFDerivWithinAt.union
    · by_cases hx : x ∈ s
      · exact hfs.fderivWithin m hm x hx
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [hs.closure_eq] using hx)
    · by_cases hx : x ∈ t
      · exact hft.fderivWithin m hm x hx
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [ht.closure_eq] using hx)
  · intro m hm
    exact (hfs.cont m hm).union_of_isClosed (hft.cont m hm) hs ht

/-- A finite sum of functions with Taylor series has the finite sum series on the same set. -/
private theorem hasFTaylorSeriesUpToOn_sum {k : ℕ∞ω} {ι : Type*} (u : Finset ι)
    {f : ι → E → F} {p : ι → E → FormalMultilinearSeries ℝ E F} {s : Set E}
    (hf : ∀ i ∈ u, HasFTaylorSeriesUpToOn k (f i) (p i) s) :
    HasFTaylorSeriesUpToOn k (fun x ↦ ∑ i ∈ u, f i x)
      (fun x m ↦ ∑ i ∈ u, p i x m) s := by
  constructor
  · intro x hx
    simp only [ContinuousMultilinearMap.curry0_apply, sum_apply]
    exact Finset.sum_congr rfl (fun i hi ↦ (hf i hi).zero_eq x hx)
  · intro m hm x hx
    have hder : HasFDerivWithinAt (fun y ↦ ∑ i ∈ u, p i y m)
        (∑ i ∈ u, (p i x m.succ).curryLeft) s x :=
      HasFDerivWithinAt.fun_sum (fun i hi ↦ (hf i hi).fderivWithin m hm x hx)
    apply hder.congr_fderiv
    ext v w
    simp only [ContinuousMultilinearMap.curryLeft_apply, sum_apply]
  · intro m hm
    exact continuousOn_finsetSum u (fun i hi ↦ (hf i hi).cont m hm)

/-- Constant real scalar multiplication scales every term of a within-set Taylor series. -/
private theorem hasFTaylorSeriesUpToOn_const_smul {k : ℕ∞ω} {f : E → F}
    {p : E → FormalMultilinearSeries ℝ E F} {s : Set E}
    (hf : HasFTaylorSeriesUpToOn k f p s) (c : ℝ) :
    HasFTaylorSeriesUpToOn k (fun x ↦ c • f x) (fun x m ↦ c • p x m) s := by
  constructor
  · intro x hx
    simpa only [ContinuousMultilinearMap.curry0_apply, smul_apply] using
      congrArg (fun v : F ↦ c • v) (hf.zero_eq x hx)
  · intro m hm x hx
    have hder : HasFDerivWithinAt (fun y ↦ c • p y m)
        (c • (p x m.succ).curryLeft) s x :=
      (hf.fderivWithin m hm x hx).const_smul c
    apply hder.congr_fderiv
    ext v w
    simp only [ContinuousMultilinearMap.curryLeft_apply, smul_apply]
  · intro m hm
    exact (hf.cont m hm).const_smul c

/-- Piecewise functions on two closed sets covering the space are Cᵏ when all boundary Taylor
terms through order k agree. -/
private theorem contDiff_piecewise_of_matching_taylor {k : ℕ∞} {f g : E → F}
    {p q : E → FormalMultilinearSeries ℝ E F} {s t : Set E}
    [DecidablePred (· ∈ s)]
    (hs : IsClosed s) (ht : IsClosed t) (hcover : s ∪ t = univ)
    (hf : HasFTaylorSeriesUpToOn k f p s) (hg : HasFTaylorSeriesUpToOn k g q t)
    (hmatch : ∀ x ∈ s ∩ t, ∀ m : ℕ, m ≤ k → p x m = q x m) :
    ContDiff ℝ k (s.piecewise f g) := by
  classical
  let r : E → FormalMultilinearSeries ℝ E F := s.piecewise p q
  have hvalue (x : E) (hx : x ∈ s ∩ t) : f x = g x := by
    rw [← hf.zero_eq x hx.1, ← hg.zero_eq x hx.2, hmatch x hx 0 (by simp)]
  have hf' : HasFTaylorSeriesUpToOn k (s.piecewise f g) r s := by
    apply (hf.congr (fun x hx ↦ by simp [hx])).congr_series
    intro m hm x hx
    simp [r, hx]
  have hg' : HasFTaylorSeriesUpToOn k (s.piecewise f g) r t := by
    have hfunction : HasFTaylorSeriesUpToOn k (s.piecewise f g) q t := by
      apply hg.congr
      intro x hx
      by_cases hxs : x ∈ s
      · simpa only [Set.piecewise_eq_of_mem s f g hxs] using hvalue x ⟨hxs, hx⟩
      · simp [hxs]
    apply hfunction.congr_series
    intro m hm x hx
    by_cases hxs : x ∈ s
    · simpa only [r, Set.piecewise_eq_of_mem s p q hxs] using
        (hmatch x ⟨hxs, hx⟩ m (by exact_mod_cast hm)).symm
    · simp [r, hxs]
  have hglobal := hasFTaylorSeriesUpToOn_union hs ht hf' hg'
  rw [hcover] at hglobal
  exact contDiffOn_univ.mp hglobal.contDiffOn

/-- The distinct negative integer time scales used in finite-order reflection. -/
def reflectionScale (k : ℕ) (j : Fin (k + 1)) : ℝ := -((j : ℕ) + 1 : ℝ)

/-- Every finite-order reflection scale is strictly negative. -/
theorem reflectionScale_neg (k : ℕ) (j : Fin (k + 1)) : reflectionScale k j < 0 := by
  dsimp [reflectionScale]
  apply neg_lt_zero.mpr
  positivity

/-- The finite reflection time scales are pairwise distinct. -/
theorem reflectionScale_injective (k : ℕ) : Function.Injective (reflectionScale k) := by
  intro i j hij
  apply Fin.ext
  dsimp [reflectionScale] at hij
  have hcast : (i : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast hcast

/-- Invert the actual Vandermonde matrix to construct weights matching all time moments through
order k. -/
theorem exists_reflectionWeights (k : ℕ) :
    ∃ c : Fin (k + 1) → ℝ, ∀ m : Fin (k + 1),
      ∑ j, c j * reflectionScale k j ^ (m : ℕ) = 1 := by
  let A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    (Matrix.vandermonde (reflectionScale k)).transpose
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (reflectionScale_injective k)
  let c : Fin (k + 1) → ℝ := A⁻¹ *ᵥ fun _ ↦ 1
  have hc : A *ᵥ c = fun _ ↦ 1 := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  refine ⟨c, fun m ↦ ?_⟩
  simpa only [A, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.vandermonde_apply, mul_comm] using congrFun hc m

/-- The bounded linear time dilation leaving the spatial coordinate unchanged. -/
def timeScale (a : ℝ) : (ℝ × E) →L[ℝ] ℝ × E :=
  (a • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)

/-- Time dilation multiplies only the time coordinate. -/
@[simp] theorem timeScale_apply (a : ℝ) (x : ℝ × E) :
    timeScale a x = (a * x.1, x.2) := (rfl)

/-- Expand a time-dilated multilinear term by its subset of time-direction slots. -/
theorem multilinear_timeScale_expansion {m : ℕ}
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

/-- The constructed moment identities make the weighted reflected multilinear jet exactly the
original jet. -/
theorem weighted_timeScale_jet {k m : ℕ} (hm : m ≤ k)
    (c : Fin (k + 1) → ℝ)
    (hc : ∀ l : Fin (k + 1), ∑ j, c j * reflectionScale k j ^ (l : ℕ) = 1)
    (A : (ℝ × E) [×m]→L[ℝ] F) :
    (∑ j, c j • A.compContinuousLinearMap (fun _ ↦ timeScale (reflectionScale k j))) = A := by
  classical
  ext v
  simp only [sum_apply, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [multilinear_timeScale_expansion, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hmoment (s : Finset (Fin m)) : ∑ j, c j * reflectionScale k j ^ s.card = 1 := by
    have hcard : s.card ≤ m := by simpa using s.card_le_univ
    exact hc ⟨s.card, Nat.lt_succ_of_le (hcard.trans hm)⟩
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
/-- The two closed time half-spaces cover the whole product space. -/
theorem upper_lower_cover : upperHalfSpace E ∪ lowerHalfSpace E = univ := by
  ext x
  simp only [upperHalfSpace, lowerHalfSpace, mem_union, mem_prod, mem_Ici, mem_Iic,
    mem_univ, and_true, iff_true]
  exact le_total 0 x.1

/-- Retain the actual field at nonnegative times and use the finite weighted time reflections at
negative times. -/
def reflectionExtension {k : ℕ} (c : Fin (k + 1) → ℝ) (f : ℝ × E → F) : ℝ × E → F := by
  classical
  exact (upperHalfSpace E).piecewise f
    (fun x ↦ ∑ j, c j • f (timeScale (reflectionScale k j) x))

/-- The reflected extension agrees with the original function on the entire nonnegative
half-space. -/
theorem reflectionExtension_eqOn_upper {k : ℕ} (c : Fin (k + 1) → ℝ) (f : ℝ × E → F) :
    EqOn (reflectionExtension c f) f (upperHalfSpace E) := by
  classical
  intro x hx
  simp [reflectionExtension, hx]

/-- At negative times the extension is exactly the prescribed finite weighted reflection sum. -/
theorem reflectionExtension_of_negative {k : ℕ} (c : Fin (k + 1) → ℝ)
    (f : ℝ × E → F) {x : ℝ × E} (hx : x.1 < 0) :
    reflectionExtension c f x = ∑ j, c j • f (timeScale (reflectionScale k j) x) := by
  classical
  have hx' : x ∉ upperHalfSpace E := by
    simpa only [upperHalfSpace, mem_prod, mem_Ici, mem_univ, and_true] using not_le.mpr hx
  simp [reflectionExtension, hx']

/-- Moment-matched reflected Taylor jets construct a global Cᵏ extension of a Cᵏ function on the
closed upper half-space. -/
theorem contDiff_reflectionExtension (k : ℕ) (c : Fin (k + 1) → ℝ)
    (hc : ∀ m : Fin (k + 1), ∑ j, c j * reflectionScale k j ^ (m : ℕ) = 1)
    (f : ℝ × E → F)
    (hf : ContDiffOn ℝ k f (upperHalfSpace E)) :
    ContDiff ℝ k (reflectionExtension c f) := by
  classical
  let p : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F :=
    ftaylorSeriesWithin ℝ f (upperHalfSpace E)
  have hp : HasFTaylorSeriesUpToOn k f p (upperHalfSpace E) :=
    hf.ftaylorSeriesWithin ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ)
  let g : ℝ × E → F := fun x ↦ ∑ j, c j • f (timeScale (reflectionScale k j) x)
  let q : (ℝ × E) → FormalMultilinearSeries ℝ (ℝ × E) F := fun x m ↦
    ∑ j, c j • (p (timeScale (reflectionScale k j) x) m).compContinuousLinearMap
      (fun _ ↦ timeScale (reflectionScale k j))
  have hq : HasFTaylorSeriesUpToOn k g q (lowerHalfSpace E) := by
    apply hasFTaylorSeriesUpToOn_sum Finset.univ
    intro j _
    apply (hasFTaylorSeriesUpToOn_const_smul
      (hp.compContinuousLinearMap (timeScale (reflectionScale k j))) (c j)).mono
    intro x hx
    exact ⟨mul_nonneg_of_nonpos_of_nonpos (reflectionScale_neg k j).le hx.1, mem_univ _⟩
  have hmatch : ∀ x ∈ upperHalfSpace E ∩ lowerHalfSpace E,
      ∀ m : ℕ, m ≤ (k : ℕ∞) → p x m = q x m := by
    intro x hx m hm
    have htime : x.1 = 0 := le_antisymm hx.2.1 hx.1.1
    have hscale (j : Fin (k + 1)) : timeScale (reflectionScale k j) x = x := by
      ext <;> simp [htime]
    change p x m = ∑ j, c j • (p (timeScale (reflectionScale k j) x) m).compContinuousLinearMap
      (fun _ ↦ timeScale (reflectionScale k j))
    simp_rw [hscale]
    exact (weighted_timeScale_jet (by exact_mod_cast hm) c hc (p x m)).symm
  exact contDiff_piecewise_of_matching_taylor (isClosed_Ici.prod isClosed_univ)
    (isClosed_Iic.prod isClosed_univ) upper_lower_cover hp hq hmatch

/-- Every Cᵏ function on the closed upper half-space admits a constructed global Cᵏ extension. -/
theorem exists_contDiff_extension_halfSpace (k : ℕ) (f : ℝ × E → F)
    (hf : ContDiffOn ℝ k f (upperHalfSpace E)) :
    ∃ g : ℝ × E → F, ContDiff ℝ k g ∧ EqOn g f (upperHalfSpace E) := by
  obtain ⟨c, hc⟩ := exists_reflectionWeights k
  exact ⟨reflectionExtension c f, contDiff_reflectionExtension k c hc f hf,
    reflectionExtension_eqOn_upper c f⟩

/-- A Cᵏ function near a boundary point on the closed upper half-space has a global Cᵏ extension
agreeing locally on that side. -/
theorem exists_local_contDiff_extension_halfSpace [FiniteDimensional ℝ E]
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
  rw [hgeq ⟨htime, mem_univ _⟩]
  change β z • f z = f z
  rw [β.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), one_smul]

/-- Reflection preserves local equality on the upper side near the time-zero boundary. -/
theorem reflectionExtension_congr_nhds_boundary {k : ℕ}
    (c : Fin (k + 1) → ℝ) {f g : ℝ × E → F} {p : E}
    (hfg : ∀ᶠ z in 𝓝 ((0 : ℝ), p), 0 ≤ z.1 → f z = g z) :
    reflectionExtension c f =ᶠ[𝓝 ((0 : ℝ), p)] reflectionExtension c g := by
  classical
  have hscaled : ∀ j : Fin (k + 1), ∀ᶠ z in 𝓝 ((0 : ℝ), p),
      0 ≤ (timeScale (reflectionScale k j) z).1 →
        f (timeScale (reflectionScale k j) z) =
          g (timeScale (reflectionScale k j) z) := by
    intro j
    have ht : Tendsto (timeScale (reflectionScale k j) : ℝ × E → ℝ × E)
        (𝓝 ((0 : ℝ), p)) (𝓝 ((0 : ℝ), p)) := by
      have hcont : ContinuousAt (timeScale (reflectionScale k j) : ℝ × E → ℝ × E)
          ((0 : ℝ), p) := (timeScale (reflectionScale k j)).continuous.continuousAt
      simpa only [timeScale_apply, mul_zero] using hcont.tendsto
    exact ht.eventually hfg
  filter_upwards [hfg, Filter.eventually_all.mpr hscaled] with z hz hzs
  by_cases htime : 0 ≤ z.1
  · rw [reflectionExtension_eqOn_upper c f ⟨htime, mem_univ _⟩,
      reflectionExtension_eqOn_upper c g ⟨htime, mem_univ _⟩]
    exact hz htime
  · have hneg : z.1 < 0 := lt_of_not_ge htime
    rw [reflectionExtension_of_negative c f hneg, reflectionExtension_of_negative c g hneg]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun v : F ↦ c j • v)
      (hzs j (mul_nonneg_of_nonpos_of_nonpos (reflectionScale_neg k j).le hneg.le))

/-- The actual moment-matched reflected extension is Cᵏ at the time-zero boundary using local
upper-side regularity. -/
theorem contDiffAt_reflectionExtension_boundary [FiniteDimensional ℝ E]
    (k : ℕ) (c : Fin (k + 1) → ℝ)
    (hc : ∀ m : Fin (k + 1), ∑ j, c j * reflectionScale k j ^ (m : ℕ) = 1)
    (f : ℝ × E → F) {V : Set (ℝ × E)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ k f (upperHalfSpace E ∩ V)) (p : E) (hp : (0, p) ∈ V) :
    ContDiffAt ℝ k (reflectionExtension c f) (0, p) := by
  obtain ⟨g, hg, hgeq⟩ := exists_local_contDiff_extension_halfSpace k f hV hf p hp
  apply (contDiff_reflectionExtension k c hc g hg.contDiffOn).contDiffAt.congr_of_eventuallyEq
  exact reflectionExtension_congr_nhds_boundary c
    (hgeq.mono (fun _ h htime ↦ (h htime).symm))

/-- A forward-time Cᵏ function on an open spatial domain has a Cᵏ reflected extension on a
definite two-sided time slab. -/
theorem contDiffOn_reflectionExtension_slab_on [FiniteDimensional ℝ E]
    (k : ℕ) (c : Fin (k + 1) → ℝ)
    (hc : ∀ m : Fin (k + 1), ∑ j, c j * reflectionScale k j ^ (m : ℕ) = 1)
    (f : ℝ × E → F) {T : ℝ} (hT : 0 < T) {A : Set E} (hA : IsOpen A)
    (hf : ContDiffOn ℝ k f (Ico 0 T ×ˢ A)) :
    ContDiffOn ℝ k (reflectionExtension c f)
      (Ioo (-T / ((k : ℝ) + 1)) T ×ˢ A) := by
  classical
  apply (isOpen_Ioo.prod hA).contDiffOn_iff.mpr
  intro ⟨t, x⟩ ht
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have hbound : ((k : ℝ) + 1) * (-t) < T := by
      have h := (div_lt_iff₀ hkpos).mp ht.1.1
      nlinarith
    have hscaled (j : Fin (k + 1)) : timeScale (reflectionScale k j) (t, x) ∈
        Ioo 0 T ×ˢ A := by
      have hj : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_of_lt j.is_lt
      refine ⟨⟨mul_pos_of_neg_of_neg (reflectionScale_neg k j) hneg, ?_⟩, ht.2⟩
      calc
        reflectionScale k j * t = ((j : ℝ) + 1) * (-t) := by
          dsimp [reflectionScale]
          ring
        _ ≤ ((k : ℝ) + 1) * (-t) :=
          mul_le_mul_of_nonneg_right hj (neg_nonneg.mpr hneg.le)
        _ < T := hbound
    have hsum : ContDiffAt ℝ k
        (fun z : ℝ × E ↦ ∑ j, c j • f (timeScale (reflectionScale k j) z)) (t, x) := by
      apply ContDiffAt.sum
      intro j _
      have hfj : ContDiffAt ℝ k f (timeScale (reflectionScale k j) (t, x)) :=
        hf.contDiffAt (prod_mem_nhds (Ico_mem_nhds_iff.mpr (hscaled j).1)
          (hA.mem_nhds (hscaled j).2))
      have hscaleSmooth : ContDiff ℝ k
          (timeScale (reflectionScale k j) : (ℝ × E) → ℝ × E) :=
        (timeScale (reflectionScale k j) : (ℝ × E) →L[ℝ] ℝ × E).contDiff
      exact (hfj.comp (t, x) hscaleSmooth.contDiffAt).const_smul (c j)
    apply hsum.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hneg] with z hz
    exact reflectionExtension_of_negative c f hz
  · subst t
    have hf0 : ContDiffOn ℝ k f (upperHalfSpace E ∩ (Iio T ×ˢ A)) :=
      hf.mono (fun _ hz ↦ ⟨⟨hz.1.1, hz.2.1⟩, hz.2.2⟩)
    exact contDiffAt_reflectionExtension_boundary k c hc f
      (isOpen_Iio.prod hA) hf0 x ⟨hT, ht.2⟩
  · have hft : ContDiffAt ℝ k f (t, x) :=
      hf.contDiffAt (prod_mem_nhds (Ico_mem_nhds_iff.mpr ⟨hpos, ht.1.2⟩)
        (hA.mem_nhds ht.2))
    apply hft.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hpos] with z hz
    exact reflectionExtension_eqOn_upper c f ⟨hz.le, mem_univ _⟩

/-- Forward-time Cᵏ regularity with unrestricted space yields the constructed two-sided
reflected slab extension. -/
theorem contDiffOn_reflectionExtension_slab [FiniteDimensional ℝ E]
    (k : ℕ) (c : Fin (k + 1) → ℝ)
    (hc : ∀ m : Fin (k + 1), ∑ j, c j * reflectionScale k j ^ (m : ℕ) = 1)
    (f : ℝ × E → F) {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ k f (Ico 0 T ×ˢ univ)) :
    ContDiffOn ℝ k (reflectionExtension c f)
      (Ioo (-T / ((k : ℝ) + 1)) T ×ˢ univ) :=
  contDiffOn_reflectionExtension_slab_on k c hc f hT isOpen_univ hf

end TauCeti.HalfSpaceExtension

end
