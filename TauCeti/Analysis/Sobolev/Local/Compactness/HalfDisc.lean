/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.Local.Compactness
import TauCeti.Analysis.Sobolev.Local.Reflection.Bound
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local Rellich compactness up to the real axis

Let `Ω` be an open subset of `ℂ`, `1 ≤ p ≤ ∞`, and `U = Ω ∩ {0 ≤ im}`. A sequence of real
functions `u m` which is bounded in `W^{k+1,p}` on the upper half `W ∩ {0 < im}` of every relatively
compact open subset `W` of `Ω` (an open set whose closure is compact and contained in `Ω`, so `W`
may cross the real axis) has a subsequence converging in `W^{k,p}` on every such upper half, to a
limit in `MemWkpLoc p U k`. Boundedness and convergence are expressed through the scalar Sobolev
spaces `TauCeti.Wkp` on the open upper halves `TopologicalSpace.Opens.upperHalf W`, as in the
interior statement `TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`.

The proof reduces to the interior statement on one open set. The reflection core
`TopologicalSpace.Opens.reflectionCore V` of an open set `V` consists of the points of `V` in the
open upper half-plane together with the points `z` of `V` whose vertical segment
`{z.re + c * z.im * I | -1 ≤ c ≤ 1}` lies in `V`. It is open, lies between `V ∩ {0 ≤ im}` and
`V`, and is stable under the normal dilations below the real axis, so the order-`k + 1` higher
reflection `TauCeti.planarReflection (higherReflectionCoeff (k + 1))` extends a map in
`W^{k+1,p}_loc` of its closed upper half to a map in `W^{k+1,p}_loc` of the core, with every
derivative bounded by `TauCeti.higherReflectionBound (k + 1) p` times the corresponding derivative
of the original map
(`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_reflectionCore_bound`). Each
relatively compact open subset of the core of `Ω` lies, with its closure, in the core of a
relatively compact open subset `V` of `Ω`, so the reflected sequence is bounded in `W^{k+1,p}` on
every relatively compact open subset of the core of `Ω`. The interior statement on the core then
gives the subsequence and the limit. Finally, the upper half of every relatively compact open
subset of `Ω` is relatively compact in the core, and there the reflected functions are the
original ones.

## Main declarations

* `TauCeti.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp`: local Rellich up to the real
  axis for real functions.
* `Module.Basis.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp`: the same for
  functions valued in a finite-dimensional real vector space, through the coordinates in a basis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces and Rellich's theorem on half-discs).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19 (extension by higher
  order reflection).
-/

public section

noncomputable section

open Filter Metric Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace TauCeti

variable {p : ℝ≥0∞} {k : ℕ}

/-! ### Uniform bounds for the reflected sequence -/

variable [Fact (1 ≤ p)]

/-- **The reflection of one Sobolev function is bounded on the reflection core.** If `u` is
represented by `v` in `W^{k+1,p}` on the upper half of `V`, then on every open `W` whose closure is
compact and contained in the reflection core of `V`, the order-`k + 1` higher reflection of `u` is
represented by an element of `W^{k+1,p}(W)` of norm at most
`(k + 2) * higherReflectionBound (k + 1) p * ‖v‖`. -/
private theorem exists_wkp_planarReflection_norm_le_of_wkp {V W : Opens ℂ} {u : ℂ → ℝ}
    (v : Wkp volume V.upperHalf p (k + 1))
    (hv : Wkp.value (k + 1) v =ᵐ[volume.restrict (V.upperHalf : Set ℂ)] u)
    (hWc : IsCompact (closure (W : Set ℂ))) (hWV : closure (W : Set ℂ) ⊆ V.reflectionCore) :
    ∃ w : Wkp volume W p (k + 1), ENNReal.ofReal ‖w‖ ≤
        ((k : ℝ≥0∞) + 2) * (higherReflectionBound (k + 1) p * ENNReal.ofReal ‖v‖) ∧
      Wkp.value (k + 1) w =ᵐ[volume.restrict W]
        planarReflection (higherReflectionCoeff (k + 1)) u := by
  have hp : 1 ≤ p := Fact.out
  set C := higherReflectionBound (k + 1) p
  set H := V.reflectionCore
  set T : Set ℂ := (V : Set ℂ) ∩ {z | 0 ≤ z.im}
  obtain ⟨G, h0, hG, -, hGn, -⟩ := Wkp.exists_iteratedGradient_chain k v
  -- Up to the real axis, which is null, `V ∩ {0 ≤ im}` is the upper half of `V`.
  have hVae : T =ᵐ[volume] (V.upperHalf : Set ℂ) := by
    rw [Opens.coe_upperHalf]
    exact ae_eq_set_inter .rfl (Complex.setOf_le_im_ae_eq 0)
  have hint := Opens.interior_inter_setOf_im_nonneg_eq_upperHalf V
  have hT : MemWkpLoc p T (k + 1) u := by
    refine (Wkp.memWkpLoc_value_of_ae_le hint hVae.subset v).congr_ae ?_
    rw [Measure.restrict_congr_set hVae]
    exact hv
  -- Reflect, and compare the iterated gradients of the reflection with those of `v`.
  obtain ⟨hrefl, hchain⟩ := hT.planarReflection_higherReflectionCoeff_reflectionCore_bound hp
  obtain ⟨hrp, Gf, hf0, hfG, hfGp⟩ := (memWkpLoc_succ_iff_exists_iteratedGradient k).1 hrefl
  have hbd : ∀ i ≤ k, eLpNorm (Gf i) p (volume.restrict H) ≤
      C * eLpNorm (G i) p (volume.restrict T) := fun i hi =>
    hchain.eLpNorm_iteratedGradient_le (by rw [Opens.interior_coe]; exact hf0)
      (by rw [hint]; exact h0.congr_ae hv) (fun i hi => by rw [Opens.interior_coe]; exact hfG i hi)
      (fun i hi => by rw [hint]; exact hG i hi) hi
  have hTV : volume.restrict T ≤ volume.restrict (V.upperHalf : Set ℂ) :=
    (Measure.restrict_congr_set hVae).le
  have hGT : ∀ i ≤ k, eLpNorm (G i) p (volume.restrict T) ≤ ENNReal.ofReal ‖v‖ := fun i hi =>
    (eLpNorm_mono_measure _ hTV).trans (hGn i hi)
  have huT : eLpNorm u p (volume.restrict T) ≤ ENNReal.ofReal ‖v‖ := by
    refine (eLpNorm_mono_measure _ hTV).trans ?_
    rw [← eLpNorm_congr_ae hv, ← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Wkp.norm_value_le _ v)
  -- Assemble the representative on `W` from the reflected chain.
  have hWH : W ≤ H := SetLike.coe_subset_coe.1 (subset_closure.trans hWV)
  have hWS : volume.restrict (W : Set ℂ) ≤ volume.restrict (H : Set ℂ) :=
    Measure.restrict_mono (SetLike.coe_subset_coe.2 hWH) le_rfl
  obtain ⟨w, hw, -, hwn⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain (Omega := W) k
    (hrp.memLp_of_closure_subset hWc hWV) (hf0.mono hWH) (fun i hi => (hfG i hi).mono hWH)
    fun i hi => (hfGp i hi).memLp_of_closure_subset hWc hWV
  refine ⟨w, hwn.trans ?_, hw⟩
  have h1 : eLpNorm (planarReflection (higherReflectionCoeff (k + 1)) u) p
      (volume.restrict W) ≤ C * ENNReal.ofReal ‖v‖ :=
    (eLpNorm_mono_measure _ hWS).trans (hchain.eLpNorm_le.trans (by gcongr))
  have h2 : ∀ i ∈ Finset.range (k + 1), eLpNorm (Gf i) p (volume.restrict W) ≤
      C * ENNReal.ofReal ‖v‖ := fun i hi =>
    (eLpNorm_mono_measure _ hWS).trans ((hbd i (Finset.mem_range_succ_iff.1 hi)).trans
      (by gcongr; exact hGT i (Finset.mem_range_succ_iff.1 hi)))
  calc _ ≤ C * ENNReal.ofReal ‖v‖ + ∑ _ ∈ Finset.range (k + 1), C * ENNReal.ofReal ‖v‖ :=
        add_le_add h1 (Finset.sum_le_sum h2)
    _ = ((k : ℝ≥0∞) + 2) * (C * ENNReal.ofReal ‖v‖) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **The reflected sequence is bounded on the reflection core.** If the `u m` are bounded in
`W^{k+1,p}` on the upper half of every relatively compact open subset of `Ω`, then their order
`k + 1` higher reflections are bounded in `W^{k+1,p}` on every relatively compact open subset of the
reflection core of `Ω`. -/
private theorem exists_wkp_planarReflection_norm_le {Ω : Opens ℂ} {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u m)
    {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω.reflectionCore) :
    ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W p (k + 1), ‖v‖ ≤ R ∧
      Wkp.value (k + 1) v =ᵐ[volume.restrict W]
        planarReflection (higherReflectionCoeff (k + 1)) (u m) := by
  obtain ⟨V, hVc, hVΩ, hWV⟩ := Opens.exists_isCompact_closure_subset_reflectionCore hWc hWΩ
  obtain ⟨R, hR⟩ := hu V hVc hVΩ
  have hne : ((k : ℝ≥0∞) + 2) * (higherReflectionBound (k + 1) p * ENNReal.ofReal R) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (higherReflectionBound_ne_top _ _)
      ENNReal.ofReal_ne_top)
  refine ⟨(((k : ℝ≥0∞) + 2) * (higherReflectionBound (k + 1) p * ENNReal.ofReal R)).toReal,
    fun m => ?_⟩
  obtain ⟨v, hvR, hv⟩ := hR m
  obtain ⟨w, hwn, hw⟩ := exists_wkp_planarReflection_norm_le_of_wkp v hv hWc hWV
  exact ⟨w, (ENNReal.ofReal_le_iff_le_toReal hne).1
    (hwn.trans (by gcongr)), hw⟩

/-! ### Local Rellich compactness up to the real axis -/

variable {Ω : Opens ℂ}

/-- **Local Rellich compactness up to the real axis for vector-valued functions.** Let `F` be a
finite-dimensional real vector space with basis `b`, let `1 ≤ p ≤ ∞`, and let `u m : ℂ → F` have
coordinates bounded in `W^{k+1,p}` on the upper half `W ∩ {0 < im}` of every relatively compact
open subset `W` of `Ω`. Then a subsequence `u (φ j)` converges in `W^{k,p}` on every such upper
half, coordinate by coordinate, to a limit `v` in `MemWkpLoc p (Ω ∩ {0 ≤ im}) k`. -/
theorem _root_.Module.Basis.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ F) {u : ℕ → ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)]
          fun z => b.repr (u m z) i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ i (y : ℕ → Wkp volume W.upperHalf p k) (w : Wkp volume W.upperHalf p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict (W.upperHalf : Set ℂ)]
            fun z => b.repr (u (φ j) z) i) →
          Wkp.value k w =ᵐ[volume.restrict (W.upperHalf : Set ℂ)]
            (fun z => b.repr (v z) i) →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := b.exists_subseq_memWkpLoc_tendsto_wkp (Ω := Ω.reflectionCore)
    (u := fun m => planarReflection (higherReflectionCoeff (k + 1)) (u m))
    fun W hWc hWΩ i => by
      simpa only [← Module.Basis.coord_apply, map_planarReflection] using
        exists_wkp_planarReflection_norm_le (u := fun m z => b.repr (u m z) i)
          (fun W' hW'c hW'Ω => hu W' hW'c hW'Ω i) hWc hWΩ
  refine ⟨φ, hφ, v, hv.mono Ω.inter_setOf_im_nonneg_subset_reflectionCore,
    fun W hWc hWΩ i y w hy hw => ?_⟩
  refine hlim W.upperHalf (Opens.isCompact_closure_upperHalf hWc)
    (Opens.closure_upperHalf_subset_reflectionCore hWΩ) i y w (fun j => (hy j).trans ?_) hw
  filter_upwards [ae_restrict_mem W.upperHalf.isOpen.measurableSet] with z hz
  simp [planarReflection_of_nonneg _ _ (Opens.mem_upperHalf.1 hz).2.le]

/-- **Local Rellich compactness up to the real axis.** Let `1 ≤ p ≤ ∞` and let `u m` be real
functions bounded in `W^{k+1,p}` on the upper half `W ∩ {0 < im}` of every relatively compact open
subset `W` of `Ω` (which may cross the real axis): each `u m` is represented there by an element
of `Wkp volume W.upperHalf p (k + 1)` of norm at most a bound depending only on `W`. Then a
subsequence `u (φ j)` converges in `W^{k,p}` on every such upper half to a limit `v` in
`MemWkpLoc p (Ω ∩ {0 ≤ im}) k`: any representatives of `u (φ j)` in
`Wkp volume W.upperHalf p k` converge to the representative of `v`. -/
theorem exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W.upperHalf p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ (y : ℕ → Wkp volume W.upperHalf p k) (w : Wkp volume W.upperHalf p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] u (φ j)) →
          Wkp.value k w =ᵐ[volume.restrict (W.upperHalf : Set ℂ)] v →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ :=
    (Module.Basis.singleton Unit ℝ).exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp
      (p := p) (k := k) (Ω := Ω) (u := u) fun W hWc hWΩ _ => by
        simpa only [Module.Basis.singleton_repr] using hu W hWc hWΩ
  exact ⟨φ, hφ, v, hv, fun W hWc hWΩ y w hy hw => hlim W hWc hWΩ () y w
    (by simpa only [Module.Basis.singleton_repr] using hy)
    (by simpa only [Module.Basis.singleton_repr] using hw)⟩

end TauCeti
