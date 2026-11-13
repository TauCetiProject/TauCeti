/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import TauCeti.Analysis.Calculus.FDeriv.Submodule
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Taylor derivative series: transport, limits, and gluing

For `HasFTaylorSeriesUpTo n f q`, if `f` takes values in a closed subspace,
then the Taylor coefficients `q x m` take values there at every order `m ≤ n`. The proof uses
the closed-subspace derivative criterion at each successive order.

A linear isometry lifts a Taylor derivative series when its coefficients lie in the
isometry’s range; this lifting does not require the range to be closed.

Over a real or complex normed field, locally uniform limits of the coefficients of Taylor
derivative series are again Taylor derivative series, provided the underlying functions converge
pointwise. This is the derivative-compatibility step in completeness of smooth function spaces.
The limit argument uses Mathlib's `hasFDerivAt_of_tendstoLocallyUniformlyOn`.

Taylor series with matching coefficients glue across two closed sets on their union.
For a closed cover of the whole space this gives a global piecewise Cᵏ criterion.
Finite sums and constant scalar multiples carry the corresponding coefficientwise series.
-/

public section

open Filter Set
open scoped ContDiff Topology

variable {𝕜 D F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : D → F} {q : D → FormalMultilinearSeries 𝕜 D F}
  {S : Submodule 𝕜 F}

/-- For a Taylor derivative series up to order `n` of a function valued in a closed subspace,
the coefficients of every order `m ≤ n` take values in that subspace. -/
theorem HasFTaylorSeriesUpTo.apply_mem_of_range_subset
    (hq : HasFTaylorSeriesUpTo n f q) (hS : IsClosed (S : Set F))
    (hf : range f ⊆ S) (m : ℕ) (hm : m ≤ n) (x : D) (v : Fin m → D) : q x m v ∈ S := by
  let R (m : ℕ) : Submodule 𝕜 (D [×m]→L[𝕜] F) :=
    { carrier := {a | ∀ v, a v ∈ S}
      zero_mem' := fun _ ↦ S.zero_mem
      add_mem' := fun ha hb v ↦ S.add_mem (ha v) (hb v)
      smul_mem' := fun c _ ha v ↦ S.smul_mem c (ha v) }
  have hR (m : ℕ) : IsClosed (R m : Set (D [×m]→L[𝕜] F)) := by
    -- Unfold the carrier so closedness follows from the evaluation preimages.
    change IsClosed {a : D [×m]→L[𝕜] F | ∀ v, a v ∈ S}
    simp only [ofPred_forall]
    exact isClosed_iInter fun v ↦ hS.preimage (continuous_eval_const v)
  induction m generalizing x with
  | zero =>
    rw [hq.zero_eq']
    exact hf ⟨x, rfl⟩
  | succ m ih =>
    have hmn : (m : WithTop ℕ∞) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
    have hv := (hq.fderiv m hmn x).apply_mem_of_eventually_sub_mem (hR m)
      (Eventually.of_forall fun y ↦ (R m).sub_mem
        (ih (le_of_lt hmn) y) (ih (le_of_lt hmn) x)) (v 0)
    simpa only [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]
      using hv (Fin.tail v)

/-- On an open set, locally uniform limits of Taylor derivative series are Taylor derivative
series of the pointwise limit. No completeness of the target is needed once limits are given. -/
theorem HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn [IsRCLikeNormedField 𝕜]
    {s : Set D} (hs : IsOpen s) {ι : Type*} {l : Filter ι} [l.NeBot]
    {fᵢ : ι → D → F} {qᵢ : ι → D → FormalMultilinearSeries 𝕜 D F}
    (h : ∀ i, HasFTaylorSeriesUpToOn n (fᵢ i) (qᵢ i) s)
    (hq : ∀ m : ℕ, m ≤ n →
      TendstoLocallyUniformlyOn (fun i x ↦ qᵢ i x m) (fun x ↦ q x m) l s)
    (hf : ∀ x ∈ s, Tendsto (fun i ↦ fᵢ i x) l (𝓝 (f x))) :
    HasFTaylorSeriesUpToOn n f q s := by
  constructor
  · intro x hx
    have hzero := ((continuousMultilinearCurryFin0 𝕜 D F).continuous.tendsto (q x 0)).comp
      ((hq 0 (by simp)).tendsto_at hx)
    exact tendsto_nhds_unique hzero (by
      simpa only [Function.comp_def, continuousMultilinearCurryFin0_apply,
        ← ContinuousMultilinearMap.curry0_apply, (h _).zero_eq _ hx] using hf x hx)
  · intro m hm x hx
    have hsuc : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ n :=
      ENat.add_one_natCast_le_withTop_of_lt hm
    have hc := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) ↦ D) F).isometry
    have hlim := hc.uniformContinuous.comp_tendstoLocallyUniformlyOn (hq (m + 1) hsuc)
    exact (hasFDerivAt_of_tendstoLocallyUniformlyOn hs hlim
      (fun i y hy ↦ ((h i).fderivWithin m hm y hy).hasFDerivAt (hs.mem_nhds hy))
      (fun y hy ↦ (hq m hm.le).tendsto_at hy) hx).hasFDerivWithinAt
  · intro m hm
    exact (hq m hm).continuousOn (Filter.Eventually.of_forall fun i ↦ (h i).cont m hm).frequently

/-- Locally uniform limits of Taylor derivative series are Taylor derivative series of the
pointwise limit. This is the whole-source specialization of the open-set result. -/
theorem HasFTaylorSeriesUpTo.of_tendstoLocallyUniformly [IsRCLikeNormedField 𝕜]
    {ι : Type*} {l : Filter ι} [l.NeBot] {fᵢ : ι → D → F}
    {qᵢ : ι → D → FormalMultilinearSeries 𝕜 D F}
    (h : ∀ i, HasFTaylorSeriesUpTo n (fᵢ i) (qᵢ i))
    (hq : ∀ m : ℕ, m ≤ n → TendstoLocallyUniformly (fun i x ↦ qᵢ i x m) (fun x ↦ q x m) l)
    (hf : ∀ x, Tendsto (fun i ↦ fᵢ i x) l (𝓝 (f x))) :
    HasFTaylorSeriesUpTo n f q :=
  hasFTaylorSeriesUpToOn_univ_iff.mp
    (HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn isOpen_univ
      (fun i ↦ (h i).hasFTaylorSeriesUpToOn univ)
      (fun m hm ↦ (hq m hm).tendstoLocallyUniformlyOn) (fun x _ ↦ hf x))

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A Taylor derivative series of `i ∘ f` lifts through the linear isometry `i` when its
coefficients of orders `m ≤ n` lie in the range of `i`. No closed-range assumption is needed. -/
theorem LinearIsometry.exists_hasFTaylorSeriesUpTo_of_comp (i : E →ₗᵢ[𝕜] F)
    {f : D → E} {n : WithTop ℕ∞} {q : D → FormalMultilinearSeries 𝕜 D F}
    (hq : HasFTaylorSeriesUpTo n (i ∘ f) q)
    (hQ : ∀ m : ℕ, m ≤ n → ∀ x v, q x m v ∈ i.toLinearMap.range) :
    ∃ p : D → FormalMultilinearSeries 𝕜 D E, HasFTaylorSeriesUpTo n f p := by
  classical
  -- Lift each coefficient through the range equivalence. Isometric postcomposition
  -- then reflects the continuity and derivative relations required by the series.
  let J (m : ℕ) : (D [×m]→L[𝕜] E) →ₗᵢ[𝕜] (D [×m]→L[𝕜] F) :=
    { toLinearMap := (ContinuousLinearMap.compContinuousMultilinearMapL
        𝕜 (fun _ : Fin m ↦ D) E F i.toContinuousLinearMap).toLinearMap
      norm_map' := i.norm_compContinuousMultilinearMap }
  let p : D → FormalMultilinearSeries 𝕜 D E := fun x m ↦
    if hm : (m : WithTop ℕ∞) ≤ n then
      i.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
        ((q x m).codRestrict i.toLinearMap.range (hQ m hm x))
    else 0
  have hJp (m : ℕ) (hm : (m : WithTop ℕ∞) ≤ n) (x : D) : J m (p x m) = q x m := by
    ext v
    -- J is postcomposition by i, so its evaluation is definitionally i (p x m v).
    -- Exposing this expression lets the range-equivalence cancellation below apply.
    change i (p x m v) = q x m v
    simp only [p, dite_eq_left hm, ContinuousLinearMap.compContinuousMultilinearMap_coe,
      Function.comp_apply]
    exact congrArg Subtype.val (i.equivRange.apply_symm_apply ⟨q x m v, hQ m hm x v⟩)
  refine ⟨p, ?_⟩
  constructor
  · intro x
    apply i.injective
    rw [ContinuousMultilinearMap.curry0_apply]
    -- Postcomposition by i at the unique zero-arity tuple is evaluation of J 0.
    -- This definitional conversion puts the goal in the form established by hJp.
    change J 0 (p x 0) 0 = i (f x)
    rw [hJp 0 (by simp)]
    exact hq.zero_eq x
  · intro m hm x
    have hm' : (m : WithTop ℕ∞) ≤ n := le_of_lt hm
    have hs : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hm
    have hc : Continuous (fun y ↦ p y m) :=
      (J m).comp_continuous_iff.mp
        (by simpa only [Function.comp_def, hJp m hm'] using hq.cont m hm')
    have hd : (J m).toContinuousLinearMap.comp (p x (m + 1)).curryLeft =
        (q x (m + 1)).curryLeft := by
      ext v w
      exact congrArg (fun a : D [×(m + 1)]→L[𝕜] F ↦ a (Fin.cons v w)) (hJp (m + 1) hs x)
    exact HasFDerivAt.of_comp_of_isEmbedding hc.continuousAt
      (J m).toContinuousLinearMap.hasFDerivAt (J m).isEmbedding
      (by simpa only [hd] using hq.fderiv m hm x)
      (Eventually.of_forall fun y ↦ hJp m hm' y)
  · intro m hm
    exact (J m).comp_continuous_iff.mp
      (by simpa only [Function.comp_def, hJp m hm] using hq.cont m hm)

section ClosedCoverOperations

open scoped BigOperators

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Matching values and one common Taylor series glue across two closed sets at every allowed
Taylor order. -/
theorem _root_.HasFTaylorSeriesUpToOn.union_of_isClosed {k : ℕ∞ω} {f : E → F}
    {p : E → FormalMultilinearSeries 𝕜 E F} {s t : Set E}
    (hfs : HasFTaylorSeriesUpToOn k f p s)
    (hft : HasFTaylorSeriesUpToOn k f p t)
    (hs : IsClosed s) (ht : IsClosed t) :
    HasFTaylorSeriesUpToOn k f p (s ∪ t) := by
  classical
  constructor
  · intro x hx
    exact hx.elim (hfs.zero_eq x) (hft.zero_eq x)
  · intro m hm x _
    apply HasFDerivWithinAt.union
    · by_cases hx : x ∈ s
      · exact hfs.fderivWithin m hm x hx
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [hs.closure_eq])
    · by_cases hx : x ∈ t
      · exact hft.fderivWithin m hm x hx
      · exact HasFDerivWithinAt.of_notMem_closure (by rwa [ht.closure_eq])
  · intro m hm
    exact (hfs.cont m hm).union_of_isClosed (hft.cont m hm) hs ht

/-- A finite sum of functions with Taylor series has the finite sum series on the same set. -/
theorem _root_.HasFTaylorSeriesUpToOn.sum {k : ℕ∞ω} {ι : Type*} {u : Finset ι}
    {f : ι → E → F} {p : ι → E → FormalMultilinearSeries 𝕜 E F} {s : Set E}
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

/-- Constant scalar multiplication scales every term of a within-set Taylor series. -/
theorem _root_.HasFTaylorSeriesUpToOn.const_smul {k : ℕ∞ω} {f : E → F}
    {p : E → FormalMultilinearSeries 𝕜 E F} {s : Set E}
    (hf : HasFTaylorSeriesUpToOn k f p s) (c : 𝕜) :
    HasFTaylorSeriesUpToOn k (fun x ↦ c • f x) (fun x m ↦ c • p x m) s := by
  exact (hf.continuousLinearMap_comp (c • ContinuousLinearMap.id 𝕜 F)).congr_series
    (fun m _ x _ ↦ by ext; simp)

/-- Piecewise functions on two closed sets covering the space are Cᵏ when all boundary Taylor
terms through order k agree. -/
theorem _root_.HasFTaylorSeriesUpToOn.contDiff_piecewise {k : ℕ∞} {f g : E → F}
    {p q : E → FormalMultilinearSeries 𝕜 E F} {s t : Set E}
    [DecidablePred (· ∈ s)]
    (hf : HasFTaylorSeriesUpToOn k f p s) (hg : HasFTaylorSeriesUpToOn k g q t)
    (hs : IsClosed s) (ht : IsClosed t) (hcover : s ∪ t = univ)
    (hmatch : ∀ x ∈ s ∩ t, ∀ m : ℕ, m ≤ k → p x m = q x m) :
    ContDiff 𝕜 k (s.piecewise f g) := by
  classical
  let r : E → FormalMultilinearSeries 𝕜 E F := s.piecewise p q
  have hvalue (x : E) (hx : x ∈ s ∩ t) : f x = g x := by
    rw [← hf.zero_eq x hx.1, ← hg.zero_eq x hx.2, hmatch x hx 0 (by simp)]
  have hf' : HasFTaylorSeriesUpToOn k (s.piecewise f g) r s := by
    apply (hf.congr (fun x hx ↦ by simp [hx])).congr_series
    intro m _ x hx
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
  have hglobal := hf'.union_of_isClosed hg' hs ht
  rw [hcover] at hglobal
  exact contDiffOn_univ.mp hglobal.contDiffOn

end ClosedCoverOperations
