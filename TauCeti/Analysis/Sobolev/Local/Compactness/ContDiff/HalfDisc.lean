/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Compactness.ContDiff
public import TauCeti.Analysis.Sobolev.Local.Reflection.Bound
import TauCeti.Analysis.Sobolev.Local.Morrey.HalfDisc

/-!
# Classical `Cᵏ` convergence of local Rellich subsequences up to the real axis

Let `Ω` be an open subset of `ℂ`, let `U = Ω ∩ {0 ≤ im}` be the corresponding relatively open
subset of the closed upper half-plane, and let `2 < p ≤ ∞`. A sequence `u m` bounded in
`W^{k+1,p}` on the upper half `W⁺ = W ∩ {0 < im}` of every open `W` whose closure is compact and
contained in `Ω` has a subsequence whose classical derivatives of orders `0` through `k` converge
uniformly on compact subsets of `U`, including compact sets that meet the real axis. This is the
half-disc form of `TauCeti.exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn_iteratedFDeriv`.

By Morrey's embedding up to the real axis
(`TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq_inter_setOf_im_nonneg`), every `u m` agrees almost
everywhere on `U` with a map that is `Cᵏ` on an open neighbourhood of `U`, and the derivatives of
such a representative on `U` do not depend on its choice
(`TauCeti.eqOn_iteratedFDeriv_inter_setOf_im_nonneg_of_ae_eq`). The statements below are about
these derivatives.

The proof reflects. The order-`(k + 1)` higher reflections of the `u m` are bounded in
`W^{k+1,p}` on every relatively compact open subset of the reflection core of `Ω`
(`TauCeti.exists_uniform_wkp_planarReflection_norm_le`), an open set between `U` and `Ω`. The
interior theorem on the reflection core gives a subsequence whose classical derivatives converge
locally uniformly on the core, hence on `U`. On `U` the reflections agree with the `u m`, so
their `Cᵏ` representatives have the same derivatives there as those of the `u m`.

## Main declarations

* `TauCeti.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendstoLocallyUniformlyOn_iteratedFDeriv`:
  local Rellich compactness with classical `Cᵏ` convergence up to the real axis, for real
  functions.
* The vector-valued version, through the coordinates in a basis, in the namespace `Module.Basis`:
  `exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendstoLocallyUniformlyOn_iteratedFDeriv`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces on half-discs and Rellich's theorem).
-/

public section

noncomputable section

open Filter Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff

namespace TauCeti

variable {p : ℝ≥0∞} {Ω : Opens ℂ} {k : ℕ}

/-- The transfer from the reflection core to `Ω ∩ {0 ≤ im}`. Let `g m` be `Cᵏ` on the reflection
core of `Ω` and agree almost everywhere there with the order-`(k + 1)` reflections of the `u m`,
and let the derivatives of order `i ≤ k` of `g (φ m)` converge locally uniformly on the core to
those of `w`. Then the same derivatives of any representatives `f m` of the `u m` that are `Cᵏ`
on open neighbourhoods of `Ω ∩ {0 ≤ im}` converge to those of `w`, locally uniformly on
`Ω ∩ {0 ≤ im}`. -/
private theorem tendstoLocallyUniformlyOn_iteratedFDeriv_inter_setOf_im_nonneg
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u g : ℕ → ℂ → F} {w : ℂ → F}
    {φ : ℕ → ℕ} (hg : ∀ m, ContDiffOn ℝ k (g m) Ω.reflectionCore)
    (hRg : ∀ m, planarReflection (higherReflectionCoeff (k + 1)) (u m)
      =ᵐ[volume.restrict (Ω.reflectionCore : Set ℂ)] g m)
    {i : ℕ} (hi : i ≤ k)
    (hconv : TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (g (φ m)))
      (iteratedFDeriv ℝ i w) atTop Ω.reflectionCore)
    {f : ℕ → ℂ → F}
    (hf : ∀ m, ∃ V : Set ℂ, IsOpen V ∧ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧ ContDiffOn ℝ k (f m) V)
    (huf : ∀ m, u m =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] f m) :
    TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f (φ m)))
      (iteratedFDeriv ℝ i w) atTop ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have hUV := Ω.inter_setOf_im_nonneg_subset_reflectionCore
  have hU : MeasurableSet ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const Complex.measurable_im)
  refine (hconv.mono hUV).congr fun m => ?_
  obtain ⟨V, hVo, hUV', hfV⟩ := hf (φ m)
  -- On `Ω ∩ {0 ≤ im}` the reflection is `u m` itself, so `g` and `f` agree almost everywhere.
  have hgf : g (φ m) =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] f (φ m) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUV (hRg (φ m)), huf (φ m),
      ae_restrict_mem hU] with z hz hzf hzU
    rw [← hz, planarReflection_of_nonneg _ _ hzU.2, hzf]
  exact eqOn_iteratedFDeriv_inter_setOf_im_nonneg_of_ae_eq Ω.reflectionCore.isOpen hVo hUV hUV'
    (hg (φ m)) hfV hgf hi

/-- **Local Rellich compactness with classical `Cᵏ` convergence up to the real axis.** Let
`2 < p ≤ ∞` and let `u m` be real functions bounded in `W^{k+1,p}` on the upper half `W⁺` of every
open `W` whose closure is compact and contained in `Ω`, as in
`TauCeti.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp`. Then there are a subsequence
`u (φ m)` and a limit `v ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` that is `Cᵏ` on an open set `V` with
`Ω ∩ {0 ≤ im} ⊆ V ⊆ Ω`, such that for any representatives `f m` of the `u m` that are `Cᵏ` on open
neighbourhoods of `Ω ∩ {0 ≤ im}` and every `i ≤ k`, the derivatives `iteratedFDeriv ℝ i (f (φ m))`
converge to the `i`-th derivative of `v`, uniformly on compact subsets of `Ω ∩ {0 ≤ im}`. Such
representatives exist by `TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq_inter_setOf_im_nonneg`. -/
theorem exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendstoLocallyUniformlyOn_iteratedFDeriv
    [Fact (1 ≤ p)] (hp : 2 < p) {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k v ∧
      (∃ V : Opens ℂ, (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧ (V : Set ℂ) ⊆ Ω ∧ ContDiffOn ℝ k v V) ∧
      ∀ f : ℕ → ℂ → ℝ,
        (∀ m, ∃ V : Set ℂ, IsOpen V ∧ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧
          ContDiffOn ℝ k (f m) V) →
        (∀ m, u m =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] f m) → ∀ i ≤ k,
          TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f (φ m)))
            (iteratedFDeriv ℝ i v) atTop ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have hR := fun (W : Opens ℂ) (hWc : IsCompact (closure (W : Set ℂ)))
      (hWΩ : closure (W : Set ℂ) ⊆ Ω.reflectionCore) =>
    exists_uniform_wkp_planarReflection_norm_le hu hWc hWΩ
  obtain ⟨φ, hφ, w, hw, hwc, hconv⟩ :=
    exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn_iteratedFDeriv (Ω := Ω.reflectionCore) hp hR
  choose g hg hRg using fun m =>
    (memWkpLoc_of_forall_exists_wkp_norm_le hR m).exists_contDiffOn_ae_eq hp
  refine ⟨φ, hφ, w, hw.mono Ω.inter_setOf_im_nonneg_subset_reflectionCore,
    ⟨Ω.reflectionCore, Ω.inter_setOf_im_nonneg_subset_reflectionCore, Ω.reflectionCore_le, hwc⟩,
    fun f hf huf i hi => ?_⟩
  exact tendstoLocallyUniformlyOn_iteratedFDeriv_inter_setOf_im_nonneg hg hRg hi
    (hconv g (fun m => (hg m).continuousOn) hRg i hi) hf huf

end TauCeti

namespace Module.Basis

open TauCeti

variable {p : ℝ≥0∞} {Ω : Opens ℂ} {k : ℕ}

/-- **Local Rellich compactness with classical `Cᵏ` convergence up to the real axis,
vector-valued version.** Let `F` be a finite-dimensional real vector space with basis `b`, let
`2 < p ≤ ∞`, and let `u m : ℂ → F` have coordinates bounded in `W^{k+1,p}` on the upper half `W⁺`
of every open `W` whose closure is compact and contained in `Ω`. Then there are a subsequence
`u (φ m)` and a limit `v ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` that is `Cᵏ` on an open set `V` with
`Ω ∩ {0 ≤ im} ⊆ V ⊆ Ω`, such that for any representatives `f m` of the `u m` that are `Cᵏ` on open
neighbourhoods of `Ω ∩ {0 ≤ im}` and every `i ≤ k`, the derivatives `iteratedFDeriv ℝ i (f (φ m))`
converge to the `i`-th derivative of `v`, uniformly on compact subsets of `Ω ∩ {0 ≤ im}`. -/
theorem exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendstoLocallyUniformlyOn_iteratedFDeriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι] [Fact (1 ≤ p)]
    (b : Module.Basis ι ℝ F) (hp : 2 < p) {u : ℕ → ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)]
          fun z => b.repr (u m z) i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k v ∧
      (∃ V : Opens ℂ, (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧ (V : Set ℂ) ⊆ Ω ∧ ContDiffOn ℝ k v V) ∧
      ∀ f : ℕ → ℂ → F,
        (∀ m, ∃ V : Set ℂ, IsOpen V ∧ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧
          ContDiffOn ℝ k (f m) V) →
        (∀ m, u m =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] f m) → ∀ i ≤ k,
          TendstoLocallyUniformlyOn (fun m => iteratedFDeriv ℝ i (f (φ m)))
            (iteratedFDeriv ℝ i v) atTop ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  have : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  -- The coordinates of a reflection are the reflections of the coordinates.
  have hcoord : ∀ (m : ℕ) (i : ι), (fun z => b.repr
      (planarReflection (higherReflectionCoeff (k + 1)) (u m) z) i) =
        planarReflection (higherReflectionCoeff (k + 1)) fun z => b.repr (u m z) i :=
    fun m i => funext fun z => map_planarReflection (b.coord i) _ (u m) z
  have hR : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ Ω.reflectionCore → ∀ i, ∃ R : ℝ, ∀ m,
        ∃ v : Wkp volume W p (k + 1), ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict W]
          fun z => b.repr (planarReflection (higherReflectionCoeff (k + 1)) (u m) z) i :=
    fun W hWc hWΩ i => by
      simpa only [hcoord] using exists_uniform_wkp_planarReflection_norm_le
        (u := fun m z => b.repr (u m z) i) (fun W hWc hWΩ => hu W hWc hWΩ i) hWc hWΩ
  obtain ⟨φ, hφ, w, hw, hwc, hconv⟩ :=
    b.exists_subseq_memWkpLoc_tendstoLocallyUniformlyOn_iteratedFDeriv (Ω := Ω.reflectionCore) hp
      hR
  choose g hg hRg using fun m => (b.memWkpLoc_iff.2 fun i =>
    memWkpLoc_of_forall_exists_wkp_norm_le (fun W hWc hWΩ => hR W hWc hWΩ i)
      m).exists_contDiffOn_ae_eq hp
  refine ⟨φ, hφ, w, hw.mono Ω.inter_setOf_im_nonneg_subset_reflectionCore,
    ⟨Ω.reflectionCore, Ω.inter_setOf_im_nonneg_subset_reflectionCore, Ω.reflectionCore_le, hwc⟩,
    fun f hf huf i hi => ?_⟩
  exact tendstoLocallyUniformlyOn_iteratedFDeriv_inter_setOf_im_nonneg hg hRg hi
    (hconv g (fun m => (hg m).continuousOn) hRg i hi) hf huf

end Module.Basis
