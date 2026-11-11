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

/-- The normal dilation depends continuously on the factor and the point together. -/
private theorem continuous_imDilation_uncurry :
    Continuous fun q : ℝ × ℂ => imDilation q.1 q.2 := by
  have h : (fun q : ℝ × ℂ => imDilation q.1 q.2) =
      fun q => (q.2.re : ℂ) + ((q.1 * q.2.im : ℝ) : ℂ) * Complex.I := by
    funext q
    apply Complex.ext <;> simp
  rw [h]
  fun_prop

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
  rcases (show 0 ≤ z.im from hz).lt_or_eq with hz | hz
  · exact Or.inl ⟨hzV, hz⟩
  · exact Or.inr fun c _ => by rwa [imDilation_of_im_eq_zero c hz.symm]

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

/-- A chain of iterated gradients, each the weak derivative of the previous one on the interior of
`U` and each locally `Lᵖ` on `U`, gives local Sobolev membership on `U`. -/
private theorem memWkpLoc_of_iteratedGradient_chain {U : Set ℂ} (n : ℕ) :
    ∀ (j : ℕ) (G : (i : ℕ) → ℂ → IteratedGradient ℂ i),
      (∀ i, j ≤ i → i < j + n → HasWeakFDerivOn volume (Opens.interior U) (G i) (G (i + 1))) →
      (∀ i, j ≤ i → i ≤ j + n → MemLpLoc p U (G i)) → MemWkpLoc p U n (G j) := by
  induction n with
  | zero => exact fun j G _ hGp => memWkpLoc_zero_iff.2 (hGp j le_rfl (by omega))
  | succ n ih =>
    intro j G hG hGp
    exact memWkpLoc_succ_iff.2 ⟨hGp j le_rfl (by omega), G (j + 1), hG j le_rfl (by omega),
      ih (j + 1) G (fun i hji hi => hG i (by omega) (by omega))
        fun i hji hi => hGp i (by omega) (by omega)⟩

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

/-! ### Chains of weak gradients with norm bounds -/

section Norms

variable [Fact (1 ≤ p)]

/-- The iterated weak gradients of an element `v` of `W^{n+1,p}(V)` have `Lᵖ` norms at most the
norm of `v`. -/
private theorem exists_iteratedGradient_chain_eLpNorm_le {V : Opens ℂ} (n : ℕ)
    (v : Wkp volume V p (n + 1)) :
    ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i,
      HasWeakFDerivOn volume V (Wkp.value (n + 1) v) (fun z => innerSL ℝ (G 0 z)) ∧
      (∀ i < n, HasWeakFDerivOn volume V (G i) (G (i + 1))) ∧
      (∀ i ≤ n, MemLp (G i) p (volume.restrict V)) ∧
      (∀ i ≤ n, eLpNorm (G i) p (volume.restrict V) ≤ ENNReal.ofReal ‖v‖) ∧
      G n =ᵐ[volume.restrict V] Wkp.iteratedGradient n v := by
  induction n with
  | zero =>
    refine ⟨Function.update (fun i _ => 0) 0 (Wkp.iteratedGradient 0 v), ?_,
      fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => ?_, fun i hi => ?_, ?_⟩
    · simpa only [Function.update_self] using Wkp.hasWeakFDerivOn_value v
    · obtain rfl := Nat.le_zero.1 hi
      simpa only [Function.update_self] using Lp.memLp (Wkp.iteratedGradient 0 v)
    · obtain rfl := Nat.le_zero.1 hi
      rw [Function.update_self, ← Lp.enorm_def, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Wkp.norm_iteratedGradient_le 0 v)
    · simp only [Function.update_self, Filter.EventuallyEq.rfl]
  | succ n ih =>
    obtain ⟨G, h0, hG, hGp, hGn, htop⟩ := ih (Wkp.lowerOrder (n + 1) v)
    have hlow : ENNReal.ofReal ‖Wkp.lowerOrder (n + 1) v‖ ≤ ENNReal.ofReal ‖v‖ :=
      ENNReal.ofReal_le_ofReal (Wkp.norm_lowerOrder_le (n + 1) v)
    refine ⟨Function.update G (n + 1) (Wkp.iteratedGradient (n + 1) v), ?_, fun i hi => ?_,
      fun i hi => ?_, fun i hi => ?_, ?_⟩
    · rw [Function.update_of_ne (Nat.succ_ne_zero n).symm, Wkp.value_succ]
      exact h0
    · rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hG i hi
      · rw [Function.update_self]
        exact (Wkp.hasWeakFDerivOn_iteratedGradient i v).congr_ae htop.symm
    · rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hGp i (by omega)
      · rw [Function.update_self]
        exact Lp.memLp _
    · rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (hGn i (by omega)).trans hlow
      · rw [Function.update_self, ← Lp.enorm_def, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (Wkp.norm_iteratedGradient_le (n + 1) v)
    · simp only [Function.update_self, Filter.EventuallyEq.rfl]

/-- An `Lᵖ` chain of iterated weak gradients on `W` is represented by an element of
`W^{n+1,p}(W)` whose norm is at most the sum of the `Lᵖ` norms of the function and the gradients. -/
private theorem exists_wkp_of_chain_norm_le {W : Opens ℂ} (n : ℕ) {u : ℂ → ℝ}
    {G : (i : ℕ) → ℂ → IteratedGradient ℂ i} (hu : MemLp u p (volume.restrict W))
    (h0 : HasWeakFDerivOn volume W u (fun z => innerSL ℝ (G 0 z)))
    (hG : ∀ i < n, HasWeakFDerivOn volume W (G i) (G (i + 1)))
    (hGp : ∀ i ≤ n, MemLp (G i) p (volume.restrict W)) :
    ∃ v : Wkp volume W p (n + 1), Wkp.value (n + 1) v =ᵐ[volume.restrict W] u ∧
      Wkp.iteratedGradient n v =ᵐ[volume.restrict W] G n ∧
      ENNReal.ofReal ‖v‖ ≤ eLpNorm u p (volume.restrict W) +
        ∑ i ∈ Finset.range (n + 1), eLpNorm (G i) p (volume.restrict W) := by
  induction n with
  | zero =>
    obtain ⟨v, hv, htop⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain 0 hu h0 hG hGp
    refine ⟨v, hv, htop, ?_⟩
    have h := Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 v
    have hlow : ENNReal.ofReal ‖Wkp.lowerOrder 0 v‖ = eLpNorm u p (volume.restrict W) := by
      have hval : Wkp.value 1 v = Wkp.lowerOrder 0 v := by rw [Wkp.value_succ, Wkp.value_zero]
      rw [← eLpNorm_congr_ae hv, ← Lp.enorm_def, ← ofReal_norm, hval]
    have hgrad : ENNReal.ofReal ‖Wkp.iteratedGradient 0 v‖ =
        eLpNorm (G 0) p (volume.restrict W) := by
      rw [← eLpNorm_congr_ae htop, ← Lp.enorm_def, ← ofReal_norm]
    have hs : ∑ i ∈ Finset.range (0 + 1), eLpNorm (G i) p (volume.restrict W) =
        eLpNorm (G 0) p (volume.restrict W) := Finset.sum_range_one _
    rw [hs, ← hlow, ← hgrad]
    exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le
  | succ n ih =>
    obtain ⟨v, hv, htop, hvn⟩ := ih (fun i hi => hG i (by omega)) (fun i hi => hGp i (by omega))
    have hg := hGp (n + 1) le_rfl
    have hD : HasWeakFDerivOn volume W (Wkp.iteratedGradient n v) (hg.toLp (G (n + 1))) :=
      ((hG n (Nat.lt_succ_self n)).congr_ae htop.symm).congr_ae_deriv hg.coeFn_toLp.symm
    refine ⟨Wkp.mk n v _ hD, ?_, ?_, ?_⟩
    · rw [Wkp.value_mk]
      exact hv
    · rw [Wkp.iteratedGradient_mk]
      exact hg.coeFn_toLp
    · have h := Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient (n + 1) (Wkp.mk n v _ hD)
      rw [Wkp.lowerOrder_mk, Wkp.iteratedGradient_mk, Lp.norm_toLp] at h
      rw [Finset.sum_range_succ, ← add_assoc]
      exact (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_add_le.trans
        (add_le_add hvn ENNReal.ofReal_toReal_le))

end Norms

/-- A chain bound for two chains of iterated weak gradients, read through a linear isometry at the
first level, bounds the `Lᵖ` norm of every later level of the first chain by the bound constant
times the `Lᵖ` norm of the same level of the second chain. -/
private theorem eLpNorm_le_of_weakDerivChainLe_iteratedGradient {S T : Set ℂ} {C : ℝ≥0∞}
    (n : ℕ) : ∀ (j : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (L : IteratedGradient ℂ j →ₗᵢ[ℝ] F) (Gf Gg : (i : ℕ) → ℂ → IteratedGradient ℂ i),
      WeakDerivChainLe p S T C n (fun z => L (Gf j z)) (fun z => L (Gg j z)) →
      (∀ i, j ≤ i → i < j + n →
        HasWeakFDerivOn volume (Opens.interior S) (Gf i) (Gf (i + 1))) →
      (∀ i, j ≤ i → i < j + n →
        HasWeakFDerivOn volume (Opens.interior T) (Gg i) (Gg (i + 1))) →
      ∀ i, j ≤ i → i ≤ j + n →
        eLpNorm (Gf i) p (volume.restrict S) ≤ C * eLpNorm (Gg i) p (volume.restrict T) := by
  have hL : ∀ {j : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (L : IteratedGradient ℂ j →ₗᵢ[ℝ] F) (g : ℂ → IteratedGradient ℂ j) (μ : Measure ℂ),
      eLpNorm (fun z => L (g z)) p μ = eLpNorm g p μ := fun L g μ => by
    have h : ∀ z, ‖L (g z)‖ₑ = ‖g z‖ₑ := fun z => by
      simp only [enorm, LinearIsometry.nnnorm_map]
    have hm : AEStronglyMeasurable (fun z => L (g z)) μ ↔ AEStronglyMeasurable g μ :=
      L.isometry.isEmbedding.aestronglyMeasurable_comp_iff
    by_cases hg : AEStronglyMeasurable g μ
    · simp only [eLpNorm, eLpNorm', eLpNormEssSup, h, hm.2 hg, hg, ite_true]
    · simp only [eLpNorm, eLpNorm', eLpNormEssSup, h, mt hm.1 hg, hg, ite_false]
  induction n with
  | zero =>
    intro j F _ _ _ L Gf Gg h _ _ i hji hi
    obtain rfl : i = j := by omega
    simpa only [hL] using h.eLpNorm_le
  | succ n ih =>
    intro j F _ _ _ L Gf Gg h hGf hGg i hji hi
    rcases Nat.lt_or_eq_of_le hji with hji | rfl
    · have hc := h.weakFDeriv ((hGf j le_rfl (by omega)).clm_comp L.toContinuousLinearMap)
        ((hGg j le_rfl (by omega)).clm_comp L.toContinuousLinearMap)
      let L' : IteratedGradient ℂ (j + 1) →ₗᵢ[ℝ] (ℂ →L[ℝ] F) := LinearIsometry.postcomp L
      exact ih (j + 1) L' Gf Gg hc
        (fun i hji hi => hGf i (by omega) (by omega)) (fun i hji hi => hGg i (by omega) (by omega))
        i (by omega) (by omega)
    · simpa only [hL] using h.eLpNorm_le

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
  obtain ⟨G, h0, hG, hGp, hGn, -⟩ := exists_iteratedGradient_chain_eLpNorm_le k v
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
  obtain ⟨w, hw, -, hwn⟩ := exists_wkp_of_chain_norm_le (W := W) k
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
  calc _ ≤ C * ENNReal.ofReal R + ∑ i ∈ Finset.range (k + 1), C * ENNReal.ofReal R :=
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

/-- The coordinates of a reflection are the reflections of the coordinates. -/
private theorem repr_planarReflection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (b : Module.Basis ι ℝ F) {n : ℕ} (d : Fin n → ℝ) (g : ℂ → F) (i : ι) :
    (fun z => b.repr (planarReflection d g z) i) =
      planarReflection d fun z => b.repr (g z) i := by
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · simp [planarReflection_of_neg _ _ (not_le.1 hz)]

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
      simpa only [repr_planarReflection] using
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
  obtain ⟨v, hv, -, hvn⟩ := exists_wkp_of_chain_norm_le (W := P) 0 hu h0
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
