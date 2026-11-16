/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Compactness.Uniform
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Topology.Algebra.IsUniformGroup.Basic

/-!
# Classical `Cᵏ` convergence of local Rellich subsequences for `p > 2`

Let `Ω` be an open subset of `ℂ` and `2 < p ≤ ∞`. A sequence `u m` bounded in `W^{k+1,p}` on every
relatively compact open subset of `Ω` has a subsequence converging in `W^{k,p}` on every such
subset to some `v` (`TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`), and by
`TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_iteratedGradient_of_tendsto_wkp` the
precise representatives of the values and of the iterated weak gradients converge locally
uniformly. This file restates that convergence with classical derivatives.

By Morrey's embedding (`TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq`) every `u m` agrees almost
everywhere on `Ω` with a map `f m` that is `Cᵏ` on `Ω`. The limit `v` itself lies only in
`W^{k,p}_loc`, so Morrey's embedding gives it no `Cᵏ` representative. Nevertheless the precise
representative of `v` is `Cᵏ` on `Ω`
(`TauCeti.contDiffOn_preciseRepresentative_of_tendsto_wkp`), and for every `i ≤ k` the classical
derivatives `iteratedFDeriv ℝ i (f m)` converge to its `i`-th derivative locally uniformly on `Ω`
(`TauCeti.tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp`). This is `Cᵏ` convergence on
compact subsets of `Ω` in its classical form.

The proof identifies the iterated weak gradients of `u m` with the classical iterated gradients of
`f m` almost everywhere, through uniqueness of weak derivatives
(`TauCeti.HasWeakFDerivOn.ae_eq_fderiv`). The classical iterated gradients have the same pointwise
difference norms as the multilinear derivatives (`TauCeti.norm_iteratedGradientChain_sub`), so the
derivatives `iteratedFDeriv ℝ i (f m)` are uniformly Cauchy on compact subsets of `Ω` for every
`i ≤ k`. Their locally uniform limits are the derivatives of one `Cᵏ` map by
`HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn`, and that map is the precise representative
of `v` on `Ω`.

## Main declarations

* `TauCeti.contDiffOn_preciseRepresentative_of_tendsto_wkp`: the precise representative of a
  local Rellich limit is `Cᵏ` on `Ω`.
* `TauCeti.tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp`: the classical derivatives of
  orders `0` through `k` of `Cᵏ` representatives converge locally uniformly on `Ω` to those of the
  precise representative of the limit.
* `TauCeti.exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv`: local Rellich compactness with
  classical `Cᵏ` convergence on compact subsets, for real functions.
* `Module.Basis.contDiffOn_preciseRepresentative_of_tendsto_wkp`,
  `Module.Basis.tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp` and
  `Module.Basis.exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv`: the vector-valued versions,
  through the coordinates in a basis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Morrey's embedding and Rellich's theorem for local Sobolev spaces).
-/

public section

noncomputable section

open Filter Metric Set MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology ContDiff

namespace TauCeti

/-- Maps that are `Cᵏ` on an open `s ⊆ ℂ`, with derivatives of every order `i ≤ k` uniformly
Cauchy on compact subsets of `s`, converge in all these derivatives, locally uniformly on `s`, to a
map that is `Cᵏ` on `s`. -/
private theorem exists_contDiffOn_tendstoLocallyUniformlyOn_iteratedFDeriv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s : Set ℂ} (hs : IsOpen s) {k : ℕ}
    {f : ℕ → ℂ → F} (hf : ∀ m, ContDiffOn ℝ k (f m) s)
    (hc : ∀ i ≤ k, ∀ K : Set ℂ, IsCompact K → K ⊆ s →
      UniformCauchySeqOn (fun m => iteratedFDeriv ℝ i (f m)) atTop K) :
    ∃ g : ℂ → F, ContDiffOn ℝ k g s ∧ ∀ i ≤ k,
      TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f m)) (iteratedFDeriv ℝ i g)
        atTop s := by
  set Q : (i : ℕ) → ℂ → ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) F :=
    fun i x => limUnder atTop fun m => iteratedFDeriv ℝ i (f m) x
  have hpt : ∀ i ≤ k, ∀ x ∈ s,
      Tendsto (fun m => iteratedFDeriv ℝ i (f m) x) atTop (𝓝 (Q i x)) := fun i hi x hx =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      ((hc i hi {x} isCompact_singleton (singleton_subset_iff.2 hx)).cauchySeq (mem_singleton x)))
  have hloc : ∀ i ≤ k,
      TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f m)) (Q i) atTop s := fun i hi =>
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hs).2 fun K hKs hK =>
      (hc i hi K hK hKs).tendstoUniformlyOn_of_tendsto fun x hx => hpt i hi x (hKs hx)
  have hT : HasFTaylorSeriesUpToOn k (fun x => Q 0 x 0) (fun x i => Q i x) s :=
    HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn hs
      (fun m => (hf m).ftaylorSeriesWithin hs.uniqueDiffOn)
      (fun i hi => (hloc i (by exact_mod_cast hi)).congr fun m x hx =>
        (iteratedFDerivWithin_of_isOpen i hs hx).symm)
      fun x hx => by
        simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
          ((continuous_eval_const (0 : Fin 0 → ℂ)).tendsto (Q 0 x)).comp
            (hpt 0 (Nat.zero_le k) x hx)
  refine ⟨fun x => Q 0 x 0, hT.contDiffOn, fun i hi => (hloc i hi).congr_right fun x hx => ?_⟩
  exact (hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hi) hs.uniqueDiffOn
    hx).trans (iteratedFDerivWithin_of_isOpen i hs hx)

variable {p : ℝ≥0∞} {Ω : Opens ℂ} {k : ℕ}

/-- The fields of a chain of iterated weak gradients of `u` on `Ω` through order `k` agree almost
everywhere on `Ω` with the classical iterated gradients of a representative `f` of `u` that is
`Cᵏ` on `Ω`. -/
private theorem ae_eq_iteratedGradientChain {u f : ℂ → ℝ} (hf : ContDiffOn ℝ k f Ω)
    (huf : u =ᵐ[volume.restrict Ω] f) {G : (i : ℕ) → ℂ → IteratedGradient ℂ i}
    (hG0 : HasWeakFDerivOn volume Ω u fun z => innerSL ℝ (G 0 z))
    (hG : ∀ i < k, HasWeakFDerivOn volume Ω (G i) (G (i + 1))) {j : ℕ} (hj : j < k) :
    G j =ᵐ[volume.restrict Ω] iteratedGradientChain f j := by
  induction j with
  | zero =>
    have hf1 : ContDiffOn ℝ 1 f Ω := hf.of_le (by exact_mod_cast hj)
    have hd := (hG0.congr_ae huf).ae_eq_fderiv
      ((hf1.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).locallyIntegrableOn
        Ω.isOpen.measurableSet)
      fun x hx => (hf1.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt one_ne_zero
    filter_upwards [hd] with x hx
    exact (InnerProductSpace.toDual ℝ ℂ).injective (by
      ext y
      simpa only [iteratedGradientChain_zero, gradient, LinearIsometryEquiv.apply_symm_apply,
        InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] using
        congrArg (fun l : ℂ →L[ℝ] ℝ => l y) hx)
  | succ j ih =>
    have hs : ContDiffOn ℝ 1 (iteratedGradientChain f j) Ω := fun x hx =>
      (contDiffAt_iteratedGradientChain (hf.contDiffAt (Ω.isOpen.mem_nhds hx)) j
        (by exact_mod_cast (by omega : 1 + j + 1 ≤ k))).contDiffWithinAt
    have hd := ((hG j (by omega)).congr_ae (ih (by omega))).ae_eq_fderiv
      ((hs.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).locallyIntegrableOn
        Ω.isOpen.measurableSet)
      fun x hx => (hs.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt one_ne_zero
    simpa only [iteratedGradientChain_succ] using hd

/-- Under the hypotheses of
`TauCeti.tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp`, the derivatives of
orders `i ≤ k` of `Cᵏ` representatives `f m` of the `u m` are uniformly Cauchy on every compact
subset of `Ω`. -/
private theorem uniformCauchySeqOn_iteratedFDeriv_of_tendsto_wkp [Fact (1 ≤ p)] (hp : 2 < p)
    {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] u m) →
        Wkp.value k w =ᵐ[volume.restrict W] v → Tendsto y atTop (𝓝 w))
    {f : ℕ → ℂ → ℝ} (hf : ∀ m, ContDiffOn ℝ k (f m) Ω)
    (huf : ∀ m, u m =ᵐ[volume.restrict Ω] f m) {i : ℕ} (hi : i ≤ k) {K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    UniformCauchySeqOn (fun m => iteratedFDeriv ℝ i (f m)) atTop K := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hum := memWkpLoc_of_forall_exists_wkp_norm_le hu
  rcases i with _ | j
  · have h0 := (tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp hp hu hv
      hlim).congr fun m => eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
        ((hum m).memLpLoc.locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed) (huf m)
        (hf m).continuousOn
    simpa only [iteratedFDeriv_zero_eq_comp] using
      (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm.isometry.uniformContinuous
        |>.comp_uniformCauchySeqOn
          (((tendstoLocallyUniformlyOn_iff_forall_isCompact Ω.isOpen).1 h0 K hKΩ
            hK).uniformCauchySeqOn)
  -- The chain fields of order `j` converge, and agree with the classical iterated gradients.
  choose _ G hG0 hG hGp using fun m => (memWkpLoc_succ_iff_exists_iteratedGradient k).1 (hum m)
  obtain ⟨H, hH0, hH⟩ : ∃ H : (i : ℕ) → ℂ → IteratedGradient ℂ i,
      (0 < k → HasWeakFDerivOn volume Ω v fun z => innerSL ℝ (H 0 z)) ∧
        ∀ i, i + 1 < k → HasWeakFDerivOn volume Ω (H i) (H (i + 1)) := by
    rcases k with _ | n
    · exact ⟨fun _ _ => 0, by simp, by simp⟩
    · obtain ⟨-, H, hH0, hH, -⟩ := (memWkpLoc_succ_iff_exists_iteratedGradient n).1 hv
      exact ⟨H, fun _ => hH0, fun i hi => hH i (by omega)⟩
  have hGc := (tendstoLocallyUniformlyOn_preciseRepresentative_iteratedGradient_of_tendsto_wkp hp
    hu hv hlim hG0 hG hH0 hH (by omega : j < k)).congr fun m =>
      eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
        ((hGp m j (by omega)).locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed)
        (ae_eq_iteratedGradientChain (hf m) (huf m) (hG0 m) (hG m) (by omega))
        fun x hx => (contDiffAt_iteratedGradientChain ((hf m).contDiffAt (Ω.isOpen.mem_nhds hx))
          j (m := 0) (by exact_mod_cast (by omega : 0 + j + 1 ≤ k))).continuousAt.continuousWithinAt
  have hC := ((tendstoLocallyUniformlyOn_iff_forall_isCompact Ω.isOpen).1 hGc K hKΩ
    hK).uniformCauchySeqOn
  rw [Metric.uniformCauchySeqOn_iff] at hC ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hC ε hε
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  have hxΩ := Ω.isOpen.mem_nhds (hKΩ hx)
  rw [dist_eq_norm, ← norm_iteratedGradientChain_sub j
    (((hf m).contDiffAt hxΩ).of_le (by exact_mod_cast hi))
    (((hf n).contDiffAt hxΩ).of_le (by exact_mod_cast hi)), ← dist_eq_norm]
  exact hN m hm n hn x hx

/-- The combined statement behind `TauCeti.contDiffOn_preciseRepresentative_of_tendsto_wkp` and
`TauCeti.tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp`. -/
private theorem contDiffOn_and_tendstoLocallyUniformlyOn_iteratedFDeriv [Fact (1 ≤ p)]
    (hp : 2 < p) {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] u m) →
        Wkp.value k w =ᵐ[volume.restrict W] v → Tendsto y atTop (𝓝 w))
    {f : ℕ → ℂ → ℝ} (hf : ∀ m, ContDiffOn ℝ k (f m) Ω)
    (huf : ∀ m, u m =ᵐ[volume.restrict Ω] f m) :
    ContDiffOn ℝ k (preciseRepresentative volume v) Ω ∧ ∀ i ≤ k,
      TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f m))
        (iteratedFDeriv ℝ i (preciseRepresentative volume v)) atTop Ω := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hum := memWkpLoc_of_forall_exists_wkp_norm_le hu
  obtain ⟨g, hg, hgl⟩ := exists_contDiffOn_tendstoLocallyUniformlyOn_iteratedFDeriv Ω.isOpen hf
    fun i hi K hK hKΩ =>
      uniformCauchySeqOn_iteratedFDeriv_of_tendsto_wkp hp hu hv hlim hf huf hi hK hKΩ
  have h0 := (tendstoLocallyUniformlyOn_preciseRepresentative_of_tendsto_wkp hp hu hv hlim).congr
    fun m => eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
      ((hum m).memLpLoc.locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed) (huf m)
      (hf m).continuousOn
  have hgv : EqOn g (preciseRepresentative volume v) Ω := fun x hx =>
    tendsto_nhds_unique (by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        ((continuous_eval_const (0 : Fin 0 → ℂ)).tendsto _).comp
          ((hgl 0 (Nat.zero_le k)).tendsto_at hx)) (h0.tendsto_at hx)
  refine ⟨hg.congr fun x hx => (hgv hx).symm, fun i hi => (hgl i hi).congr_right fun x hx => ?_⟩
  exact ((eventuallyEq_of_mem (Ω.isOpen.mem_nhds hx) hgv).iteratedFDeriv ℝ i).eq_of_nhds

/-- **The limit of a local Rellich sequence is classically `Cᵏ`.** Let `2 < p ≤ ∞`. Let `u m` be
real functions bounded in `W^{k+1,p}` on every relatively compact open subset `W` of `Ω`, as in
`TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`, which converge in `W^{k,p}` on every such `W` to
`v ∈ MemWkpLoc p Ω k`. Then the precise representative of `v` is `Cᵏ` on `Ω`, although Morrey's
embedding applied to `v` alone gives only `C^{k-1}`. -/
theorem contDiffOn_preciseRepresentative_of_tendsto_wkp [Fact (1 ≤ p)] (hp : 2 < p)
    {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] u m) →
        Wkp.value k w =ᵐ[volume.restrict W] v → Tendsto y atTop (𝓝 w)) :
    ContDiffOn ℝ k (preciseRepresentative volume v) Ω := by
  choose f hf huf using fun m =>
    (memWkpLoc_of_forall_exists_wkp_norm_le hu m).exists_contDiffOn_ae_eq hp
  exact (contDiffOn_and_tendstoLocallyUniformlyOn_iteratedFDeriv hp hu hv hlim hf huf).1

/-- **Classical `Cᵏ` convergence of local Rellich limits.** Let `2 < p ≤ ∞` and let `u m` and `v`
be as in `TauCeti.contDiffOn_preciseRepresentative_of_tendsto_wkp`. Let `f m` be `Cᵏ` on `Ω` and
equal to `u m` almost everywhere on `Ω`; such representatives exist by Morrey's embedding
`TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq`. Then for every `i ≤ k` the derivatives
`iteratedFDeriv ℝ i (f m)` converge locally uniformly on `Ω`, that is uniformly on compact subsets
of `Ω`, to the `i`-th derivative of the precise representative of `v`. -/
theorem tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp [Fact (1 ≤ p)] (hp : 2 < p)
    {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] u m) →
        Wkp.value k w =ᵐ[volume.restrict W] v → Tendsto y atTop (𝓝 w))
    {f : ℕ → ℂ → ℝ} (hf : ∀ m, ContDiffOn ℝ k (f m) Ω)
    (huf : ∀ m, u m =ᵐ[volume.restrict Ω] f m) {i : ℕ} (hi : i ≤ k) :
    TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f m))
      (iteratedFDeriv ℝ i (preciseRepresentative volume v)) atTop Ω :=
  (contDiffOn_and_tendstoLocallyUniformlyOn_iteratedFDeriv hp hu hv hlim hf huf).2 i hi

/-- **Local Rellich compactness with classical `Cᵏ` convergence on compact sets.** Let
`2 < p ≤ ∞` and let `u m` be real functions bounded in `W^{k+1,p}` on every relatively compact
open subset of `Ω`, as in `TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`. Then there are a
subsequence `u (φ m)` and a limit `v ∈ MemWkpLoc p Ω k` whose precise representative is `Cᵏ` on
`Ω`, such that for any representatives `f m` of the `u m` that are `Cᵏ` on `Ω` and every `i ≤ k`,
the derivatives `iteratedFDeriv ℝ i (f (φ m))` converge to the `i`-th derivative of the precise
representative of `v`, locally uniformly on `Ω`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv [Fact (1 ≤ p)] (hp : 2 < p)
    {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ, MemWkpLoc p Ω k v ∧
      ContDiffOn ℝ k (preciseRepresentative volume v) Ω ∧
      ∀ f : ℕ → ℂ → ℝ, (∀ m, ContDiffOn ℝ k (f m) Ω) →
        (∀ m, u m =ᵐ[volume.restrict Ω] f m) → ∀ i ≤ k,
          TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f (φ m)))
            (iteratedFDeriv ℝ i (preciseRepresentative volume v)) atTop Ω := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := exists_subseq_memWkpLoc_tendsto_wkp hu
  have hu' : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] u (φ m) := fun W hWc hWΩ => by
    obtain ⟨R, hR⟩ := hu W hWc hWΩ
    exact ⟨R, fun m => hR (φ m)⟩
  exact ⟨φ, hφ, v, hv, contDiffOn_preciseRepresentative_of_tendsto_wkp hp hu' hv hlim,
    fun f hf huf i hi => tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp hp hu' hv hlim
      (fun m => hf (φ m)) (fun m => huf (φ m)) hi⟩

section Basis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}

/-- The derivatives of a combination `∑ j, h j z • b j` of the vectors of a finite basis are
the combinations of the derivatives of the coefficients. -/
private theorem iteratedFDeriv_sum_smul [Fintype ι] (b : Module.Basis ι ℝ F) {h : ι → ℂ → ℝ} {x : ℂ}
    {i : ℕ} (hh : ∀ j, ContDiffAt ℝ i (h j) x) :
    iteratedFDeriv ℝ i (fun z => ∑ j, h j z • b j) x =
      ∑ j, ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ i (h j) x) := by
  have hfun : (fun z => ∑ j, h j z • b j) =
      ∑ j, ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j)) ∘ h j := by
    funext z
    simp [Finset.sum_apply]
  rw [hfun, iteratedFDeriv_sum_apply fun j _ =>
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j)).contDiff.contDiffAt.comp x (hh j)]
  exact Finset.sum_congr rfl fun j _ =>
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j)).iteratedFDeriv_comp_left (hh j) le_rfl

/-- **The limit of a vector-valued local Rellich sequence is classically `Cᵏ`.** Let `F` be a
finite-dimensional real vector space with basis `b`, let `2 < p ≤ ∞`, and let `u m : ℂ → F` have
coordinates bounded in `W^{k+1,p}` on every relatively compact open subset `W` of `Ω` which
converge in `W^{k,p}` on every such `W` to the coordinates of `v ∈ MemWkpLoc p Ω k`, as produced by
`Module.Basis.exists_subseq_memWkpLoc_tendsto_wkp`. Then the precise representative of `v` is `Cᵏ`
on `Ω`. -/
theorem _root_.Module.Basis.contDiffOn_preciseRepresentative_of_tendsto_wkp [Finite ι]
    [Fact (1 ≤ p)] (b : Module.Basis ι ℝ F) (hp : 2 < p) {u : ℕ → ℂ → F} {v : ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] fun z => b.repr (u m z) i)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] fun z => b.repr (u m z) i) →
        Wkp.value k w =ᵐ[volume.restrict W] (fun z => b.repr (v z) i) →
        Tendsto y atTop (𝓝 w)) :
    ContDiffOn ℝ k (preciseRepresentative volume v) Ω := by
  have := Fintype.ofFinite ι
  have hc : ∀ j, ContDiffOn ℝ k (preciseRepresentative volume fun z => b.repr (v z) j) Ω :=
    fun j => TauCeti.contDiffOn_preciseRepresentative_of_tendsto_wkp hp
      (fun W hWc hWΩ => hu W hWc hWΩ j) (b.memWkpLoc_iff.1 hv j) fun W hWc hWΩ => hlim W hWc hWΩ j
  have hs : ContDiffOn ℝ k
      (fun z => ∑ j, preciseRepresentative volume (fun w => b.repr (v w) j) z • b j) Ω :=
    ContDiffOn.sum fun j _ => (hc j).smul contDiffOn_const
  refine hs.congr fun x hx => ?_
  exact b.eqOn_preciseRepresentative_sum_repr (one_le_two.trans hp.le) hv.memLpLoc
    (fun j => (hc j).continuousOn) hx

/-- **Classical `Cᵏ` convergence of vector-valued local Rellich limits.** Let `F`, `b`, `p`, `u m`
and `v` be as in `Module.Basis.contDiffOn_preciseRepresentative_of_tendsto_wkp`, and let
`f m : ℂ → F` be `Cᵏ` on `Ω` and equal to `u m` almost everywhere on `Ω`. Then for every `i ≤ k`
the derivatives `iteratedFDeriv ℝ i (f m)` converge to the `i`-th derivative of the precise
representative of `v`, locally uniformly on `Ω`. -/
theorem _root_.Module.Basis.tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp [Finite ι]
    [Fact (1 ≤ p)] (b : Module.Basis ι ℝ F) (hp : 2 < p) {u : ℕ → ℂ → F} {v : ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] fun z => b.repr (u m z) i)
    (hv : MemWkpLoc p Ω k v)
    (hlim : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i (y : ℕ → Wkp volume W p k) (w : Wkp volume W p k),
        (∀ m, Wkp.value k (y m) =ᵐ[volume.restrict W] fun z => b.repr (u m z) i) →
        Wkp.value k w =ᵐ[volume.restrict W] (fun z => b.repr (v z) i) →
        Tendsto y atTop (𝓝 w))
    {f : ℕ → ℂ → F} (hf : ∀ m, ContDiffOn ℝ k (f m) Ω)
    (huf : ∀ m, u m =ᵐ[volume.restrict Ω] f m) {i : ℕ} (hi : i ≤ k) :
    TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f m))
      (iteratedFDeriv ℝ i (preciseRepresentative volume v)) atTop Ω := by
  have := Fintype.ofFinite ι
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  have hcf : ∀ j m, ContDiffOn ℝ k (fun z => b.repr (f m z) j) Ω := fun j m =>
    ((ContinuousLinearMap.proj j).comp b.equivFunL.toContinuousLinearMap).contDiff.comp_contDiffOn
      (hf m)
  have hcu : ∀ j m,
      (fun z => b.repr (u m z) j) =ᵐ[volume.restrict Ω] fun z => b.repr (f m z) j := fun j m => by
    filter_upwards [huf m] with z hz
    rw [hz]
  have hcv : ∀ j, ContDiffOn ℝ k (preciseRepresentative volume fun z => b.repr (v z) j) Ω :=
    fun j => TauCeti.contDiffOn_preciseRepresentative_of_tendsto_wkp hp
      (fun W hWc hWΩ => hu W hWc hWΩ j) (b.memWkpLoc_iff.1 hv j) fun W hWc hWΩ => hlim W hWc hWΩ j
  have hterm : ∀ j, TendstoLocallyUniformlyOn
      (fun m x => ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ i (fun z => b.repr (f m z) j) x))
      (fun x => ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ i (preciseRepresentative volume fun z => b.repr (v z) j) x)) atTop Ω :=
    fun j => (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i => ℂ) ℝ F
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (b j))).uniformContinuous
        |>.comp_tendstoLocallyUniformlyOn
          (TauCeti.tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp hp
            (fun W hWc hWΩ => hu W hWc hWΩ j) (b.memWkpLoc_iff.1 hv j)
            (fun W hWc hWΩ => hlim W hWc hWΩ j) (hcf j) (hcu j) hi)
  refine ((TendstoLocallyUniformlyOn.finsetSum Finset.univ fun j _ => hterm j).congr
    fun m x hx => ?_).congr_right fun x hx => ?_
  · rw [← iteratedFDeriv_sum_smul b fun j =>
      ((hcf j m).contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by exact_mod_cast hi)]
    simp only [b.sum_repr]
  · dsimp only
    rw [← iteratedFDeriv_sum_smul b fun j =>
      ((hcv j).contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by exact_mod_cast hi)]
    exact ((eventuallyEq_of_mem (Ω.isOpen.mem_nhds hx)
      (b.eqOn_preciseRepresentative_sum_repr (one_le_two.trans hp.le) hv.memLpLoc
        fun j => (hcv j).continuousOn)).iteratedFDeriv ℝ i).eq_of_nhds.symm

/-- **Local Rellich compactness with classical `Cᵏ` convergence, vector-valued version.** Let `F`
be a finite-dimensional real vector space with basis `b`, let `2 < p ≤ ∞`, and let `u m : ℂ → F`
have coordinates bounded in `W^{k+1,p}` on every relatively compact open subset of `Ω`. Then there
are a subsequence `u (φ m)` and a limit `v ∈ MemWkpLoc p Ω k` whose precise representative is `Cᵏ`
on `Ω`, such that for any representatives `f m` of the `u m` that are `Cᵏ` on `Ω` and every
`i ≤ k`, the derivatives `iteratedFDeriv ℝ i (f (φ m))` converge to the `i`-th derivative of the
precise representative of `v`, locally uniformly on `Ω`. -/
theorem _root_.Module.Basis.exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv [Finite ι]
    [Fact (1 ≤ p)] (b : Module.Basis ι ℝ F) (hp : 2 < p) {u : ℕ → ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] fun z => b.repr (u m z) i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F, MemWkpLoc p Ω k v ∧
      ContDiffOn ℝ k (preciseRepresentative volume v) Ω ∧
      ∀ f : ℕ → ℂ → F, (∀ m, ContDiffOn ℝ k (f m) Ω) →
        (∀ m, u m =ᵐ[volume.restrict Ω] f m) → ∀ i ≤ k,
          TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f (φ m)))
            (iteratedFDeriv ℝ i (preciseRepresentative volume v)) atTop Ω := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := b.exists_subseq_memWkpLoc_tendsto_wkp hu
  have hu' : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ y : Wkp volume W p (k + 1),
        ‖y‖ ≤ R ∧ Wkp.value (k + 1) y =ᵐ[volume.restrict W] fun z => b.repr (u (φ m) z) i :=
    fun W hWc hWΩ i => by
      obtain ⟨R, hR⟩ := hu W hWc hWΩ i
      exact ⟨R, fun m => hR (φ m)⟩
  exact ⟨φ, hφ, v, hv, b.contDiffOn_preciseRepresentative_of_tendsto_wkp hp hu' hv hlim,
    fun f hf huf i hi => b.tendstoLocallyUniformlyOn_iteratedFDeriv_of_tendsto_wkp hp hu' hv hlim
      (fun m => hf (φ m)) (fun m => huf (φ m)) hi⟩

end Basis

end TauCeti
