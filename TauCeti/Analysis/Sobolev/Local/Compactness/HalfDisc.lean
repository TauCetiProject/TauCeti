/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Compactness
public import TauCeti.Analysis.Sobolev.Local.Reflection.Bound
public import TauCeti.Analysis.Sobolev.Local.RellichExamples
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local Rellich compactness up to the real axis

Let `Ω` be an open subset of `ℂ`, `1 ≤ p ≤ ∞`, and `U = Ω ∩ {0 ≤ im}`. A sequence of real
functions `u m` which is bounded in `W^{k+1,p}` on the upper half `W ∩ {0 < im}` of every relatively
compact open subset `W` of `Ω` (an open set whose closure is compact and contained in `Ω`, so `W`
may cross the real axis) has a subsequence converging in `W^{k,p}` on every such upper half, to a
limit in `MemWkpLoc p U k`. Boundedness and convergence are expressed through the scalar Sobolev
spaces `TauCeti.Wkp` on the open sets `W ∩ {0 < im}`, as in the interior statement
`TauCeti.exists_subseq_memWkpLoc_tendsto_wkp`.

The proof reduces to the interior statement on one open set. The *reflection hull* of an open set
`V` consists of the points of `V` in the open upper half-plane together with the points `z` of `V`
whose vertical segment `{z.re + c * z.im * I | -1 ≤ c ≤ 1}` lies in `V`. It is open, contains
`V ∩ {0 ≤ im}`, and is stable under the normal dilations below the real axis, so the order-`k + 1`
higher reflection `TauCeti.planarReflection (higherReflectionCoeff (k + 1))` extends a map in
`W^{k+1,p}_loc` of its closed upper half to a map in `W^{k+1,p}_loc` of the hull, with every
derivative bounded by `TauCeti.higherReflectionBound (k + 1) p` times the corresponding derivative
of the original map (`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_bound`). Each
relatively compact open subset of the hull of `Ω` lies, with its closure, in the hull of a
relatively compact open subset `V` of `Ω`, so the reflected sequence is bounded in `W^{k+1,p}` on
every relatively compact open subset of the hull of `Ω`. The interior statement on the hull then
gives the subsequence and the limit. Finally, the upper half of every relatively compact open
subset of `Ω` is relatively compact in the hull, and there the reflected functions are the
original ones.

## Main declarations

* `TauCeti.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp`: local Rellich up to the real
  axis for real functions.
* `Module.Basis.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp`: the same for
  functions valued in a finite-dimensional real vector space, through the coordinates in a basis.
* `TauCeti.RellichExamples.exists_wkp_halfSine_norm_le`,
  `TauCeti.RellichExamples.exists_subseq_memWkpLoc_halfDisc_tendsto_wkp_halfSine`: the sequence
  `m⁻¹ sin (m * z.im)` of `TauCeti.Analysis.Sobolev.Local.RellichExamples` is bounded in
  `W^{1,p}` up to the real axis, so the theorem applies to it at `k = 0`; its derivatives have no
  convergent subsequence, so the conclusion cannot be improved to `W^{k+1,p}`.

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

/-! ### Upper halves and reflection hulls -/

/-- The open upper half `W ∩ {0 < im}` of an open planar set `W`. -/
private abbrev upperPart (W : Opens ℂ) : Opens ℂ :=
  ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
    W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩

/-- The points `z` whose vertical segment `{imDilation c z | -1 ≤ c ≤ 1}`, from `z` to its
conjugate, lies in `V`. -/
private def verticalCore (V : Set ℂ) : Set ℂ :=
  {z | ∀ c ∈ Icc (-1 : ℝ) 1, imDilation c z ∈ V}

/-- The vertical core of an open set is open, by compactness of `[-1, 1]`. -/
private theorem isOpen_verticalCore {V : Set ℂ} (hV : IsOpen V) : IsOpen (verticalCore V) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  have hc : Continuous fun q : ℂ × ℝ => imDilation q.2 q.1 :=
    continuous_imDilation_uncurry.comp continuous_swap
  exact isCompact_Icc.eventually_forall_of_forall_eventually fun c hcI =>
    hc.continuousAt.preimage_mem_nhds (hV.mem_nhds (hz c hcI))

/-- The reflection hull of `V`: its points in the open upper half-plane, together with its points
whose vertical segment to the conjugate point lies in `V`. -/
private def reflectionHull (V : Opens ℂ) : Opens ℂ :=
  ⟨(upperPart V : Set ℂ) ∪ verticalCore V,
    (upperPart V).isOpen.union (isOpen_verticalCore V.isOpen)⟩

private theorem reflectionHull_le (V : Opens ℂ) : reflectionHull V ≤ V := by
  rintro z (hz | hz)
  · exact hz.1
  · simpa using hz 1 ⟨by norm_num, le_rfl⟩

private theorem inter_setOf_im_nonneg_subset_reflectionHull (V : Opens ℂ) :
    (V : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ reflectionHull V := by
  rintro z ⟨hzV, hz⟩
  have him : 0 ≤ z.im := hz
  rcases him.lt_or_eq with hpos | hzero
  · exact Or.inl ⟨hzV, hpos⟩
  · exact Or.inr fun c _ => by rwa [imDilation_of_im_eq_zero c hzero.symm]

private theorem mem_verticalCore_of_mem_reflectionHull {V : Opens ℂ} {z : ℂ}
    (hz : z ∈ reflectionHull V) (him : z.im ≤ 0) : z ∈ verticalCore V :=
  hz.resolve_left fun h => not_lt.2 him h.2

/-- The reflection hull is stable under the node dilations below the real axis. -/
private theorem imDilation_higherReflectionNode_mem_reflectionHull {V : Opens ℂ} {n : ℕ}
    (j : Fin n) {z : ℂ} (hz : z ∈ reflectionHull V) (him : z.im < 0) :
    imDilation (higherReflectionNode j) z ∈ reflectionHull V := by
  refine Or.inr fun c hc => ?_
  have hn : |higherReflectionNode j| ≤ 1 := by
    rw [higherReflectionNode_eq, abs_neg, abs_inv, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by simp)
  have hcn : |c * higherReflectionNode j| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (abs_le.2 hc) hn (abs_nonneg _) zero_le_one).trans (one_mul 1).le
  rw [imDilation_imDilation]
  exact mem_verticalCore_of_mem_reflectionHull hz him.le _ (abs_le.1 hcn)

/-- A relatively compact open subset of the reflection hull of `Ω` lies, with its closure, in the
reflection hull of a relatively compact open subset of `Ω`. -/
private theorem exists_closure_subset_reflectionHull {Ω W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ reflectionHull Ω) :
    ∃ V : Opens ℂ, IsCompact (closure (V : Set ℂ)) ∧ closure (V : Set ℂ) ⊆ Ω ∧
      closure (W : Set ℂ) ⊆ reflectionHull V := by
  set K := closure (W : Set ℂ)
  have hK' : IsCompact (K ∪ (fun q : ℝ × ℂ => imDilation q.1 q.2) ''
      (Icc (-1 : ℝ) 1 ×ˢ (K ∩ {z | z.im ≤ 0}))) :=
    hWc.union ((isCompact_Icc.prod (hWc.inter_right
      (isClosed_le Complex.continuous_im continuous_const))).image continuous_imDilation_uncurry)
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK' Ω.isOpen (by
    rintro _ (hz | ⟨⟨c, z⟩, ⟨hc, hzK, hz⟩, rfl⟩)
    · exact reflectionHull_le Ω (hWΩ hz)
    · exact mem_verticalCore_of_mem_reflectionHull (hWΩ hzK) hz c hc)
  refine ⟨⟨V, hVo⟩, hVc, hVΩ, fun z hz => ?_⟩
  rcases lt_or_ge 0 z.im with h | h
  · exact Or.inl ⟨hKV (Or.inl hz), h⟩
  · exact Or.inr fun c hc => hKV (Or.inr ⟨(c, z), ⟨hc, hz, h⟩, rfl⟩)

/-- The upper half of a relatively compact open subset of `Ω` is relatively compact in the
reflection hull of `Ω`. -/
private theorem closure_upperPart_subset_reflectionHull {Ω W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    IsCompact (closure (upperPart W : Set ℂ)) ∧
      closure (upperPart W : Set ℂ) ⊆ reflectionHull Ω := by
  have hsub : closure (upperPart W : Set ℂ) ⊆ closure (W : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    closure_minimal (inter_subset_inter subset_closure fun z (h : 0 < z.im) => h.le)
      (isClosed_closure.inter (isClosed_le continuous_const Complex.continuous_im))
  exact ⟨(hWc.inter_right (isClosed_le continuous_const Complex.continuous_im)).of_isClosed_subset
    isClosed_closure hsub, hsub.trans ((inter_subset_inter_left _ hWΩ).trans
      (inter_setOf_im_nonneg_subset_reflectionHull Ω))⟩

/-! ### Local Sobolev classes from upper halves -/

/-- A subset of `V ∩ {0 ≤ im}` lies in the upper half of `V` up to a subset of the real axis. -/
private theorem ae_le_upperPart {V : Opens ℂ} {K : Set ℂ}
    (hK : K ⊆ (V : Set ℂ) ∩ {z | 0 ≤ z.im}) : K ≤ᵐ[volume] (upperPart V : Set ℂ) := by
  refine ae_le_set.2 (measure_mono_null (fun z hz => ?_) (Complex.volume_setOf_im_eq 0))
  exact le_antisymm (not_lt.1 fun h => hz.2 ⟨(hK hz.1).1, h⟩) (hK hz.1).2

/-- `Lᵖ` on the upper half of `V` gives local `Lᵖ` up to the real axis. -/
private theorem memLpLoc_inter_of_memLp_upperPart {E : Type*} [NormedAddCommGroup E]
    {V : Opens ℂ} {f : ℂ → E} (hf : MemLp f p (volume.restrict (upperPart V : Set ℂ))) :
    MemLpLoc p ((V : Set ℂ) ∩ {z | 0 ≤ z.im}) f :=
  memLpLoc_iff.2 fun _ hK _ => hf.mono_measure (Measure.restrict_mono_ae (ae_le_upperPart hK))

/-- An `Lᵖ` chain of iterated weak gradients on the upper half of `V` gives local Sobolev
membership on `A ∩ {0 ≤ im}` for every open `A ⊆ V`, up to the real axis. -/
private theorem memWkpLoc_inter_of_iteratedGradient_chain {A V : Opens ℂ} (hAV : A ≤ V) (n : ℕ)
    {u : ℂ → ℝ} {G : (i : ℕ) → ℂ → IteratedGradient ℂ i}
    (hu : MemLp u p (volume.restrict (upperPart V : Set ℂ)))
    (h0 : HasWeakFDerivOn volume (upperPart V) u fun z => innerSL ℝ (G 0 z))
    (hG : ∀ i < n, HasWeakFDerivOn volume (upperPart V) (G i) (G (i + 1)))
    (hGp : ∀ i ≤ n, MemLp (G i) p (volume.restrict (upperPart V : Set ℂ))) :
    MemWkpLoc p ((A : Set ℂ) ∩ {z | 0 ≤ z.im}) (n + 1) u := by
  have hsub : (A : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (V : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    inter_subset_inter_left _ hAV
  have hint : Opens.interior ((A : Set ℂ) ∩ {z | 0 ≤ z.im}) ≤ upperPart V := by
    refine SetLike.coe_subset_coe.1 ?_
    rw [Opens.coe_interior, interior_inter_setOf_im_nonneg A.isOpen]
    exact inter_subset_inter_left _ hAV
  refine memWkpLoc_succ_iff.2 ⟨(memLpLoc_inter_of_memLp_upperPart hu).mono_set hsub, _,
    h0.mono hint, ?_⟩
  exact (memWkpLoc_of_iteratedGradient_chain n 0 G (fun i _ hi => (hG i (by omega)).mono hint)
    fun i _ hi => (memLpLoc_inter_of_memLp_upperPart (hGp i (by omega))).mono_set hsub).clm_comp
      (innerSL ℝ)

/-! ### Uniform bounds for the reflected sequence -/

variable [Fact (1 ≤ p)]

/-- **The reflected sequence is bounded on the reflection hull.** If the `u m` are bounded in
`W^{k+1,p}` on the upper half of every relatively compact open subset of `Ω`, then their order
`k + 1` higher reflections are bounded in `W^{k+1,p}` on every relatively compact open subset of the
reflection hull of `Ω`. -/
private theorem exists_wkp_planarReflection_norm_le {Ω : Opens ℂ} {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ v : Wkp volume (upperPart W) p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict (upperPart W : Set ℂ)] u m)
    {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ reflectionHull Ω) :
    ∃ R : ℝ, ∀ m, ∃ v : Wkp volume W p (k + 1), ‖v‖ ≤ R ∧
      Wkp.value (k + 1) v =ᵐ[volume.restrict W]
        planarReflection (higherReflectionCoeff (k + 1)) (u m) := by
  have hp : 1 ≤ p := Fact.out
  obtain ⟨V, hVc, hVΩ, hWV⟩ := exists_closure_subset_reflectionHull hWc hWΩ
  obtain ⟨R, hR⟩ := hu V hVc hVΩ
  set C := higherReflectionBound (k + 1) p
  have hne : ((k : ℝ≥0∞) + 2) * (C * ENNReal.ofReal R) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (higherReflectionBound_ne_top _ _)
      ENNReal.ofReal_ne_top)
  refine ⟨(((k : ℝ≥0∞) + 2) * (C * ENNReal.ofReal R)).toReal, fun m => ?_⟩
  obtain ⟨v, hvR, hv⟩ := hR m
  obtain ⟨G, h0, hG, hGp, hGn, -⟩ := Wkp.exists_iteratedGradient_chain k v
  have hum : MemLp (u m) p (volume.restrict (upperPart V : Set ℂ)) := (Lp.memLp _).ae_eq hv
  have h0' := h0.congr_ae hv
  set H := reflectionHull V
  set T : Set ℂ := (H : Set ℂ) ∩ {z | 0 ≤ z.im}
  have hT : MemWkpLoc p T (k + 1) (u m) :=
    memWkpLoc_inter_of_iteratedGradient_chain (reflectionHull_le V) k hum h0' hG hGp
  obtain ⟨hrefl, hchain⟩ := hT.planarReflection_higherReflectionCoeff_bound (Ω := H) hp
    fun z hz hz0 j => imDilation_higherReflectionNode_mem_reflectionHull j hz hz0
  obtain ⟨hrp, Gf, hf0, hfG, hfGp⟩ := (memWkpLoc_succ_iff_exists_iteratedGradient k).1 hrefl
  have hint : Opens.interior T ≤ upperPart V := by
    refine SetLike.coe_subset_coe.1 ?_
    rw [Opens.coe_interior, interior_inter_setOf_im_nonneg H.isOpen]
    exact inter_subset_inter_left _ (reflectionHull_le V)
  have hc := hchain.weakFDeriv (Df := fun z => innerSL ℝ (Gf 0 z))
    (Dg := fun z => innerSL ℝ (G 0 z)) (by rw [Opens.interior_coe]; exact hf0) (h0'.mono hint)
  let L0 : IteratedGradient ℂ 0 →ₗᵢ[ℝ] (ℂ →L[ℝ] ℝ) :=
    { (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).toLinearMap with norm_map' := innerSL_apply_norm ℝ }
  have hbd := eLpNorm_le_of_weakDerivChainLe_iteratedGradient k 0 L0 Gf G hc
    (fun i _ hi => by rw [Opens.interior_coe]; exact hfG i (by omega))
    fun i _ hi => (hG i (by omega)).mono hint
  have hTV : volume.restrict T ≤ volume.restrict (upperPart V : Set ℂ) :=
    Measure.restrict_mono_ae (ae_le_upperPart (inter_subset_inter_left _ (reflectionHull_le V)))
  have hGT : ∀ i ≤ k, eLpNorm (G i) p (volume.restrict T) ≤ ENNReal.ofReal R := fun i hi =>
    (eLpNorm_mono_measure _ hTV).trans ((hGn i hi).trans (ENNReal.ofReal_le_ofReal hvR))
  have huT : eLpNorm (u m) p (volume.restrict T) ≤ ENNReal.ofReal R := by
    refine (eLpNorm_mono_measure _ hTV).trans ?_
    rw [← eLpNorm_congr_ae hv, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((Wkp.norm_value_le _ v).trans hvR)
  have hWH : W ≤ H := SetLike.coe_subset_coe.1 (subset_closure.trans hWV)
  have hWS : volume.restrict (W : Set ℂ) ≤ volume.restrict (H : Set ℂ) :=
    Measure.restrict_mono (SetLike.coe_subset_coe.2 hWH) le_rfl
  obtain ⟨w, hw, -, hwn⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain (Omega := W) k
    (hrp.memLp_of_closure_subset hWc hWV) (hf0.mono hWH) (fun i hi => (hfG i hi).mono hWH)
    fun i hi => (hfGp i hi).memLp_of_closure_subset hWc hWV
  refine ⟨w, (ENNReal.ofReal_le_iff_le_toReal hne).1 (hwn.trans ?_), hw⟩
  have h1 : eLpNorm (planarReflection (higherReflectionCoeff (k + 1)) (u m)) p
      (volume.restrict W) ≤ C * ENNReal.ofReal R :=
    (eLpNorm_mono_measure _ hWS).trans (hchain.eLpNorm_le.trans (by gcongr))
  have h2 : ∀ i ∈ Finset.range (k + 1), eLpNorm (Gf i) p (volume.restrict W) ≤
      C * ENNReal.ofReal R := fun i hi =>
    (eLpNorm_mono_measure _ hWS).trans ((hbd i (Nat.zero_le i)
      (by simpa using Finset.mem_range_succ_iff.1 hi)).trans
        (by gcongr; exact hGT i (Finset.mem_range_succ_iff.1 hi)))
  calc _ ≤ C * ENNReal.ofReal R + ∑ _ ∈ Finset.range (k + 1), C * ENNReal.ofReal R :=
        add_le_add h1 (Finset.sum_le_sum h2)
    _ = ((k : ℝ≥0∞) + 2) * (C * ENNReal.ofReal R) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### Local Rellich compactness up to the real axis -/

variable {Ω : Opens ℂ}

/-- **Local Rellich compactness up to the real axis.** Let `1 ≤ p ≤ ∞` and let `u m` be real
functions bounded in `W^{k+1,p}` on the upper half `W ∩ {0 < im}` of every relatively compact open
subset `W` of `Ω` (which may cross the real axis): each `u m` is represented there by an element
of `Wkp volume (W ∩ {0 < im}) p (k + 1)` of norm at most a bound depending only on `W`. Then a
subsequence `u (φ j)` converges in `W^{k,p}` on every such upper half to a limit `v` in
`MemWkpLoc p (Ω ∩ {0 ≤ im}) k`: any representatives of `u (φ j)` in
`Wkp volume (W ∩ {0 < im}) p k` converge to the representative of `v`. -/
theorem exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp {u : ℕ → ℂ → ℝ}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ R : ℝ, ∀ m, ∃ v : Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
          W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p (k + 1),
        ‖v‖ ≤ R ∧
          Wkp.value (k + 1) v =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})] u m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ (y : ℕ → Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
            W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p k)
          (w : Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
            W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})]
            u (φ j)) →
          Wkp.value k w =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})] v →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := exists_subseq_memWkpLoc_tendsto_wkp (Ω := reflectionHull Ω)
    (u := fun m => planarReflection (higherReflectionCoeff (k + 1)) (u m))
    fun W hWc hWΩ => exists_wkp_planarReflection_norm_le hu hWc hWΩ
  refine ⟨φ, hφ, v, hv.mono (inter_setOf_im_nonneg_subset_reflectionHull Ω),
    fun W hWc hWΩ y w hy hw => ?_⟩
  obtain ⟨hWc', hWΩ'⟩ := closure_upperPart_subset_reflectionHull hWc hWΩ
  refine hlim (upperPart W) hWc' hWΩ' y w (fun j => (hy j).trans ?_) hw
  filter_upwards [ae_restrict_mem (upperPart W).isOpen.measurableSet] with z hz
  exact (planarReflection_of_nonneg _ _ hz.2.le).symm

/-- **Local Rellich compactness up to the real axis for vector-valued functions.** Let `F` be a
finite-dimensional real vector space with basis `b`, let `1 ≤ p ≤ ∞`, and let `u m : ℂ → F` have
coordinates bounded in `W^{k+1,p}` on the upper half `W ∩ {0 < im}` of every relatively compact
open subset `W` of `Ω`. Then a subsequence `u (φ j)` converges in `W^{k,p}` on every such upper
half, coordinate by coordinate, to a limit `v` in `MemWkpLoc p (Ω ∩ {0 ≤ im}) k`. -/
theorem _root_.Module.Basis.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ F) {u : ℕ → ℂ → F}
    (hu : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∀ i, ∃ R : ℝ, ∀ m, ∃ v : Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
          W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p (k + 1),
        ‖v‖ ≤ R ∧ Wkp.value (k + 1) v =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})]
          fun z => b.repr (u m z) i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → F,
      MemWkpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) k v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∀ i (y : ℕ → Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
            W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p k)
          (w : Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
            W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p k),
          (∀ j, Wkp.value k (y j) =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})]
            fun z => b.repr (u (φ j) z) i) →
          Wkp.value k w =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})]
            (fun z => b.repr (v z) i) →
          Tendsto y atTop (𝓝 w) := by
  obtain ⟨φ, hφ, v, hv, hlim⟩ := b.exists_subseq_memWkpLoc_tendsto_wkp (Ω := reflectionHull Ω)
    (u := fun m => planarReflection (higherReflectionCoeff (k + 1)) (u m))
    fun W hWc hWΩ i => by
      simpa only [← Module.Basis.coord_apply, LinearMap.map_planarReflection] using
        exists_wkp_planarReflection_norm_le (u := fun m z => b.repr (u m z) i)
          (fun W' hW'c hW'Ω => hu W' hW'c hW'Ω i) hWc hWΩ
  refine ⟨φ, hφ, v, hv.mono (inter_setOf_im_nonneg_subset_reflectionHull Ω),
    fun W hWc hWΩ i y w hy hw => ?_⟩
  obtain ⟨hWc', hWΩ'⟩ := closure_upperPart_subset_reflectionHull hWc hWΩ
  refine hlim (upperPart W) hWc' hWΩ' i y w (fun j => (hy j).trans ?_) hw
  filter_upwards [ae_restrict_mem (upperPart W).isOpen.measurableSet] with z hz
  simp [planarReflection_of_nonneg _ _ hz.2.le]

/-! ### The oscillating example on the half-disc -/

namespace RellichExamples

/-- **The oscillating sequence is bounded in `W^{1,p}` up to the real axis.** On the upper half of
every open `W` with compact closure, `halfSine m z = m⁻¹ sin (m * z.im)` is represented by an
element of `Wkp volume (W ∩ {0 < im}) p 1` of norm at most `2 * volume (W ∩ {0 < im}) ^ (1 / p)`,
uniformly in `m`. So the sequence satisfies the hypothesis of
`TauCeti.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp` at `k = 0`, while its
derivatives have no subsequence converging in `Lᵖ` on the half-disc
(`TauCeti.RellichExamples.not_tendsto_eLpNorm_fderiv_halfSine_sub`). -/
theorem exists_wkp_halfSine_norm_le {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ))) :
    ∃ R : ℝ, ∀ m, ∃ v : Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
        W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p 1,
      ‖v‖ ≤ R ∧
        Wkp.value 1 v =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})] halfSine m := by
  set P := upperPart W
  have hP : volume (P : Set ℂ) ≠ ⊤ :=
    ((measure_mono (inter_subset_left.trans subset_closure)).trans_lt hWc.measure_lt_top).ne
  set c := volume (P : Set ℂ) ^ p.toReal⁻¹
  have hc : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hP
  refine ⟨(2 * c).toReal, fun m => ?_⟩
  let G : (i : ℕ) → ℂ → IteratedGradient ℂ i := Function.update (fun i _ => 0) 0
    fun z => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (halfSine m) z)
  have hG0 : G 0 = fun z => (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (halfSine m) z) :=
    Function.update_self ..
  have hcont : Continuous (fderiv ℝ (halfSine m)) :=
    (contDiff_halfSine m (n := 1)).continuous_fderiv one_ne_zero
  have hGc : Continuous (G 0) := by
    rw [hG0]
    exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp hcont
  have hu1 : eLpNorm (halfSine m) p (volume.restrict P) ≤ c :=
    (eLpNorm_halfSine_le m p P).trans (mul_le_of_le_one_right' (ENNReal.ofReal_le_one.2
      (Nat.cast_inv_le_one m)))
  have hG1 : eLpNorm (G 0) p (volume.restrict P) ≤ c := by
    refine le_of_eq_of_le ?_ (eLpNorm_fderiv_halfSine_le m p P)
    refine eLpNorm_congr_norm_ae hGc.aestronglyMeasurable hcont.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [hG0, LinearIsometryEquiv.norm_map]
  have hu : MemLp (halfSine m) p (volume.restrict P) :=
    memLp_iff.2 (hu1.trans_lt (lt_top_iff_ne_top.2 hc))
  have h0 : HasWeakFDerivOn volume P (halfSine m) fun z => innerSL ℝ (G 0 z) := by
    have hD : (fun z => innerSL ℝ (G 0 z)) = fderiv ℝ (halfSine m) := by
      funext z
      rw [hG0, InnerProductSpace.innerSL_toDual_symm]
    rw [hD]
    exact hasWeakFDerivOn_of_differentiableOn (hcont.locallyIntegrable.locallyIntegrableOn _)
      fun z _ => (contDiff_halfSine m (n := 1)).differentiable one_ne_zero z
  obtain ⟨v, hv, -, hvn⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain (Omega := P) 0 hu h0
    (fun i hi => absurd hi (Nat.not_lt_zero i)) fun i hi => by
      obtain rfl := Nat.le_zero.1 hi
      exact memLp_iff.2 (hG1.trans_lt (lt_top_iff_ne_top.2 hc))
  refine ⟨v, (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top (by simp) hc)).1 ?_, hv⟩
  have hs : ∑ i ∈ Finset.range (0 + 1), eLpNorm (G i) p (volume.restrict P) =
      eLpNorm (G 0) p (volume.restrict P) := Finset.sum_range_one _
  rw [hs] at hvn
  exact hvn.trans ((add_le_add hu1 hG1).trans (two_mul c).ge)

/-- **The half-disc Check for Rellich.** The sequence `m⁻¹ sin (m * z.im)` has a subsequence
converging in `Lᵖ` on the upper half of every relatively compact open subset of the unit disc, to a
locally `Lᵖ` limit on the half-disc, by
`TauCeti.exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp` at `k = 0`. -/
theorem exists_subseq_memWkpLoc_halfDisc_tendsto_wkp_halfSine :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → ℝ, MemWkpLoc p halfDisc 0 v ∧
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ ball 0 1 →
        ∀ (y : ℕ → Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
            W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p 0)
          (w : Wkp volume ⟨(W : Set ℂ) ∩ {z : ℂ | 0 < z.im},
            W.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)⟩ p 0),
          (∀ j, Wkp.value 0 (y j) =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})]
            halfSine (φ j)) →
          Wkp.value 0 w =ᵐ[volume.restrict ((W : Set ℂ) ∩ {z : ℂ | 0 < z.im})] v →
          Tendsto y atTop (𝓝 w) := by
  rw [halfDisc_def]
  exact exists_subseq_memWkpLoc_inter_setOf_im_nonneg_tendsto_wkp (Ω := ⟨ball 0 1, isOpen_ball⟩)
    fun _ hWc _ => exists_wkp_halfSine_norm_le hWc

end RellichExamples

end TauCeti
