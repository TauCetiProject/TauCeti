/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Basic
public import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Completeness of the weak Whitney topology in one chart

The jet of a `C^n` map records its continuous derivatives through order `n`. Over a real or
complex normed field and a locally compact source, the image of this jet map is closed in the
product of compact-open continuous-map spaces. Indeed, compact-open convergence is locally
uniform convergence, which preserves the derivative relations between successive coefficients.
The zeroth coefficient recovers the limiting function. This holds for finite regularity and
smooth regularity, but does not assert closedness of analytic jets.

We equip the existing weak Whitney topology with the uniformity induced by the jet. For a
complete target this uniform space is complete. This is the local completeness result used
when smooth bundle sections are reconstructed from compatible limits in charts and frames.
No countability or finite-dimensionality assumption on the target is required.

The topology convention is that of M. Hirsch, *Differential Topology*, Chapter 2, §1.
The derivative-limit argument uses Mathlib's Taylor derivative series and
`HasFTaylorSeriesUpTo.of_tendstoLocallyUniformly`.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Uniformity

variable {n : ℕ∞ω}

/-- The compact-open derivative uniformity on `C^n` maps. Its topology is the existing weak
Whitney topology, not a newly chosen topology on the map carrier. -/
instance instUniformSpaceWeakWhitney : UniformSpace C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ :=
  isEmbedding_weakWhitneyJet.comapUniformSpace weakWhitneyJet

/-- The jet map uniformly embeds the weak Whitney map space. -/
theorem isUniformEmbedding_weakWhitneyJet :
    IsUniformEmbedding (weakWhitneyJet : C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ →
      (m : {m : ℕ // m ≤ n}) → C(E, E [×(m : ℕ)]→L[𝕜] F)) :=
  Embedding.to_isUniformEmbedding _ isEmbedding_weakWhitneyJet

end Uniformity

variable [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] {n : ℕ∞}

/-- A compact-open limit of jets of `C^n` maps is the jet of a `C^n` map. Here `n` may be
finite or infinite, but not analytic regularity. -/
theorem exists_weakWhitneyJet_eq_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → C^(n : ℕ∞ω)⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯}
    {g : (m : {m : ℕ // m ≤ (n : ℕ∞ω)}) → C(E, E [×(m : ℕ)]→L[𝕜] F)}
    (hg : Tendsto (fun i ↦ weakWhitneyJet (f i)) l (𝓝 g)) :
    ∃ h : C^(n : ℕ∞ω)⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯, weakWhitneyJet h = g := by
  classical
  -- Complete the truncated family by zero above its regularity; those entries are never used.
  let p : E → FormalMultilinearSeries 𝕜 E F := fun x m ↦
    if hm : (m : ℕ∞ω) ≤ n then g ⟨m, hm⟩ x else 0
  have hp (m : ℕ) (hm : (m : ℕ∞ω) ≤ n) (x : E) : p x m = g ⟨m, hm⟩ x := by
    simp only [p, dite_eq_left hm]
  have hlim (m : ℕ) (hm : (m : ℕ∞ω) ≤ n) :
      TendstoLocallyUniformly (fun i x ↦ ftaylorSeries 𝕜 (f i) x m) (fun x ↦ p x m) l := by
    have ht := (tendsto_pi_nhds.1 hg) ⟨m, hm⟩
    simpa only [hp m hm, weakWhitneyJet_apply, iteratedFDerivContinuousMap_apply,
      ftaylorSeries] using ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 ht
  let h : E → F := fun x ↦ (p x 0).curry0
  have hh : HasFTaylorSeriesUpTo (n : ℕ∞ω) h p :=
    HasFTaylorSeriesUpTo.of_tendstoLocallyUniformly
      (fun i ↦ (f i).contMDiff.contDiff.ftaylorSeries) hlim fun x ↦ by
        have ht := ((continuousMultilinearCurryFin0 𝕜 E F).continuous.tendsto (p x 0)).comp
          ((hlim 0 (by simp)).tendstoLocallyUniformlyOn.tendsto_at (mem_univ x))
        simpa only [h, ftaylorSeries, Function.comp_def, iteratedFDeriv_zero_eq_comp,
          continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.curry0_apply,
          continuousMultilinearCurryFin0_symm_apply_apply] using ht
  let H : C^(n : ℕ∞ω)⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ := ⟨h, hh.contDiff.contMDiff⟩
  refine ⟨H, funext fun m ↦ ?_⟩
  apply ContinuousMap.ext
  intro x
  rw [weakWhitneyJet_apply H m, iteratedFDerivContinuousMap_apply]
  exact (hh.eq_iteratedFDeriv m.property x).symm.trans (hp m m.property x)

/-- The weak Whitney jet realizes the `C^n` map space as a closed subspace of the product of
its compact-open derivative spaces. -/
theorem isClosedEmbedding_weakWhitneyJet :
    IsClosedEmbedding (weakWhitneyJet :
      C^(n : ℕ∞ω)⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ →
        (m : {m : ℕ // m ≤ (n : ℕ∞ω)}) → C(E, E [×(m : ℕ)]→L[𝕜] F)) := by
  refine ⟨isEmbedding_weakWhitneyJet, isClosed_of_closure_subset fun g hg ↦ ?_⟩
  let l := Filter.comap (Subtype.val : range (weakWhitneyJet (𝕜 := 𝕜)
    (E := E) (F := F) (n := (n : ℕ∞ω))) → _) (𝓝 g)
  have : l.NeBot := mem_closure_iff_comap_neBot.1 hg
  let f := fun z : range (weakWhitneyJet (𝕜 := 𝕜) (E := E) (F := F) (n := (n : ℕ∞ω))) ↦
    Classical.choose z.property
  have hf : (fun z ↦ weakWhitneyJet (f z)) = Subtype.val :=
    funext fun z ↦ Classical.choose_spec z.property
  exact exists_weakWhitneyJet_eq_of_tendsto (l := l) (f := f) (by rw [hf]; exact tendsto_comap)

/-- For a complete target, the weak Whitney `C^n` map space is complete. This includes the
smooth map space, with uniform convergence of every derivative on compact subsets. -/
theorem completeSpace_weakWhitney [CompleteSpace F] :
    CompleteSpace C^(n : ℕ∞ω)⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ :=
  (completeSpace_iff_isComplete_range isUniformEmbedding_weakWhitneyJet.isUniformInducing).2
    isClosedEmbedding_weakWhitneyJet.isClosed_range.isComplete

/-- Finite and smooth regularity give complete weak Whitney map spaces. The native `LEInfty`
class permits instance synthesis for both numeral regularities and variable exponents. -/
instance instCompleteSpaceWeakWhitney [CompleteSpace F] {m : ℕ∞ω} [hm : ENat.LEInfty m] :
    CompleteSpace C^m⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯ := by
  obtain ⟨q, rfl⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (by simp : (∞ : ℕ∞ω) ≠ ⊤) hm.out)
  exact completeSpace_weakWhitney (n := q)

end ContMDiffMap
