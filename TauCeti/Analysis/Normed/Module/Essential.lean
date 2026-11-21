/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import TauCeti.Analysis.Normed.Ring.ApproximateUnit
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Bounded approximate identities on essential modules

Let `A` be a possibly nonunital normed algebra acting on a seminormed space `E` on the left through
a bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`, or on the right
through `R : A →L[𝕜] E →L[𝕜] E` with `R (a * b) x = R b (R a x)`. A left approximate identity of
`A` is a filter `l` on `A` with `e * a → a` along `l` for every `a`, and a right approximate
identity satisfies `a * e → a`; it is bounded by `C` when `‖e‖ ≤ C` eventually along `l`.

The *essential submodule* of a bounded action `M : A →L[𝕜] E →L[𝕜] E` is the closed linear span
`ContinuousLinearMap.essentialSubmodule M = closure (span (M · ·))`; for a bimodule `(L, R)` the
two-sided essential submodule is the intersection
`ContinuousLinearMap.essentialBimoduleSubmodule L R = L.essentialSubmodule ⊓ R.essentialSubmodule`.
This file proves:

* invariance of `M.essentialSubmodule` under any commuting bounded action, and invariance of
  `essentialBimoduleSubmodule L R` under both `L` and `R`;
* that a bounded one-sided approximate identity converges to the identity pointwise on the
  corresponding essential submodule, and that, for a proper filter, the essential submodule consists
  exactly of the points where it does;
* that in the presence of a bounded two-sided approximate identity, `L.essentialSubmodule ⊓
  R.essentialSubmodule` equals the closed linear span of `A · E · A`.

## Main definitions

* `ContinuousLinearMap.essentialSubmodule`: the closed linear span of `M · ·` for a bounded
  bilinear action `M`.
* `ContinuousLinearMap.essentialBimoduleSubmodule`: the intersection
  `L.essentialSubmodule ⊓ R.essentialSubmodule` for a bounded bimodule `(L, R)`.

## Main results

* `ContinuousLinearMap.apply_mem_essentialSubmodule` and
  `ContinuousLinearMap.apply_mem_essentialSubmodule_of_comm`: invariance of `M.essentialSubmodule`
  under `M` and under any commuting bounded bilinear action.
* `ContinuousLinearMap.apply_left_mem_essentialBimoduleSubmodule` and
  `ContinuousLinearMap.apply_right_mem_essentialBimoduleSubmodule`: invariance of
  `essentialBimoduleSubmodule L R` under both actions.
* `ContinuousLinearMap.tendsto_apply_of_mem_essentialSubmodule` and
  `ContinuousLinearMap.tendsto_apply_iff_mem_essentialSubmodule`: convergence and characterization
  on the left essential submodule.
* `ContinuousLinearMap.tendsto_apply_of_mem_essentialSubmodule_right` and
  `ContinuousLinearMap.tendsto_apply_iff_mem_essentialSubmodule_right`: convergence and
  characterization on the right essential submodule.
* `ContinuousLinearMap.essentialBimoduleSubmodule_eq_topologicalClosure_span`: with a bounded
  two-sided approximate identity, `essentialBimoduleSubmodule L R = closure (span (A · E · A))`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.9.
* V. Runde, *Lectures on Amenability*, Springer, 2002, Proposition 2.1.5.
-/

public section

open Filter Topology Submodule

namespace ContinuousLinearMap

section EssentialSubmodule

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The essential submodule of a bounded bilinear action `M : A →L[𝕜] E →L[𝕜] E`, defined as the
closed linear span of `{M a x | a : A, x : E}`. -/
@[expose] def essentialSubmodule (M : A →L[𝕜] E →L[𝕜] E) : Submodule 𝕜 E :=
  (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure

/-- Unfolding lemma for `ContinuousLinearMap.essentialSubmodule`. -/
theorem essentialSubmodule_eq_topologicalClosure_span (M : A →L[𝕜] E →L[𝕜] E) :
    M.essentialSubmodule = (span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)).topologicalClosure :=
  rfl

/-- The essential submodule of a bounded action is closed. -/
theorem isClosed_essentialSubmodule (M : A →L[𝕜] E →L[𝕜] E) :
    IsClosed (M.essentialSubmodule : Set E) :=
  isClosed_topologicalClosure _

/-- Every image `M a x` lies in `M.essentialSubmodule`. -/
theorem apply_mem_essentialSubmodule (M : A →L[𝕜] E →L[𝕜] E) (a : A) (x : E) :
    M a x ∈ M.essentialSubmodule :=
  le_topologicalClosure _ (subset_span ⟨(a, x), rfl⟩)

/-- If two bounded bilinear actions `M` and `N` commute (`M a (N b x) = N b (M a x)`), then `N b`
leaves `M.essentialSubmodule` invariant. -/
theorem apply_mem_essentialSubmodule_of_comm {M N : A →L[𝕜] E →L[𝕜] E}
    (hMN : ∀ a b x, M a (N b x) = N b (M a x)) (b : A) {x : E}
    (hx : x ∈ M.essentialSubmodule) :
    N b x ∈ M.essentialSubmodule := by
  set S := span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2)
  have hinv : S ∈ Module.End.invtSubmodule (N b).toLinearMap := by
    rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_span_le]
    rintro _ ⟨⟨a, y⟩, rfl⟩
    dsimp only
    rw [ContinuousLinearMap.coe_coe, ← hMN]
    exact subset_span ⟨(a, N b y), rfl⟩
  exact Submodule.topologicalClosure_mem_invtSubmodule hinv hx

/-- The two-sided essential submodule of a bounded bimodule `(L, R)`, defined as the intersection
`L.essentialSubmodule ⊓ R.essentialSubmodule`. -/
@[expose] def essentialBimoduleSubmodule (L R : A →L[𝕜] E →L[𝕜] E) : Submodule 𝕜 E :=
  L.essentialSubmodule ⊓ R.essentialSubmodule

/-- Unfolding lemma for `ContinuousLinearMap.essentialBimoduleSubmodule`. -/
theorem essentialBimoduleSubmodule_eq_inf (L R : A →L[𝕜] E →L[𝕜] E) :
    essentialBimoduleSubmodule L R = L.essentialSubmodule ⊓ R.essentialSubmodule :=
  rfl

/-- The two-sided essential submodule of a bounded bimodule is closed. -/
theorem isClosed_essentialBimoduleSubmodule (L R : A →L[𝕜] E →L[𝕜] E) :
    IsClosed (essentialBimoduleSubmodule L R : Set E) := by
  rw [essentialBimoduleSubmodule_eq_inf, Submodule.coe_inf]
  exact (isClosed_essentialSubmodule L).inter (isClosed_essentialSubmodule R)

/-- The two-sided essential submodule is invariant under the left action `L`. -/
theorem apply_left_mem_essentialBimoduleSubmodule {L R : A →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (a : A) {x : E}
    (hx : x ∈ essentialBimoduleSubmodule L R) :
    L a x ∈ essentialBimoduleSubmodule L R :=
  ⟨apply_mem_essentialSubmodule L a x,
    apply_mem_essentialSubmodule_of_comm (fun b c y ↦ (hLR c b y).symm) a hx.2⟩

/-- The two-sided essential submodule is invariant under the right action `R`. -/
theorem apply_right_mem_essentialBimoduleSubmodule {L R : A →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (a : A) {x : E}
    (hx : x ∈ essentialBimoduleSubmodule L R) :
    R a x ∈ essentialBimoduleSubmodule L R :=
  ⟨apply_mem_essentialSubmodule_of_comm hLR a hx.1,
    apply_mem_essentialSubmodule R a x⟩

end EssentialSubmodule

section ApproximateIdentity

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalSeminormedRing A]
  [NormedSpace 𝕜 A] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Shared convergence argument: if an eventually bounded filter `l` acts as the identity in the
limit on every generator `M a w`, then it does so on the entire essential submodule
`M.essentialSubmodule`. -/
private theorem tendsto_apply_of_mem_essentialSubmodule_aux (M : A →L[𝕜] E →L[𝕜] E)
    {l : Filter A} {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hgen : ∀ a w, Tendsto (fun e ↦ M e (M a w)) l (𝓝 (M a w))) {z : E}
    (hz : z ∈ M.essentialSubmodule) :
    Tendsto (fun e ↦ M e z) l (𝓝 z) := by
  classical
  let S : Submodule 𝕜 E :=
    { carrier := {z | Tendsto (fun e ↦ M e z) l (𝓝 z)}
      add_mem' := fun hz hw ↦ by simpa using hz.add hw
      zero_mem' := by simpa using tendsto_const_nhds
      smul_mem' := fun c _ hz ↦ by simpa using hz.const_smul c }
  have hspan : span 𝕜 (Set.range fun p : A × E ↦ M p.1 p.2) ≤ S := by
    rw [span_le]
    rintro _ ⟨⟨a, w⟩, rfl⟩
    exact hgen a w
  let M' : A → E →L[𝕜] E := fun e ↦ if ‖e‖ ≤ C then M e else 0
  have hM' : ∃ C', ∀ e, ‖M' e‖ ≤ C' := ⟨‖M‖ * max C 0, fun e ↦ by
    dsimp only [M']
    split_ifs with he
    · exact (M.le_opNorm e).trans (mul_le_mul_of_nonneg_left (he.trans (le_max_left C 0))
        (norm_nonneg M))
    · simp only [norm_zero]
      positivity⟩
  have hequi : Equicontinuous (DFunLike.coe ∘ M') :=
    ((NormedSpace.equicontinuous_tfae M').out 2 6).2 hM'
  have hclosed' : IsClosed {z : E | Tendsto (fun e ↦ M' e z) l (𝓝 z)} :=
    hequi.isClosed_setOfPred_tendsto continuous_id
  have hclosed : IsClosed (S : Set E) := by
    convert hclosed' using 1
    ext z
    refine tendsto_congr' (hC.mono fun e he ↦ ?_)
    simp [M', he]
  exact topologicalClosure_minimal _ hspan hclosed hz

/-- A bounded left approximate identity of `A` converges to the identity at every point of
`L.essentialSubmodule`. -/
theorem tendsto_apply_of_mem_essentialSubmodule (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E}
    (hz : z ∈ L.essentialSubmodule) :
    Tendsto (fun e ↦ L e z) l (𝓝 z) :=
  tendsto_apply_of_mem_essentialSubmodule_aux L hC
    (fun a w ↦ by simpa [Function.comp_def, hL] using ((L.flip w).continuous.tendsto a).comp (hl a))
    hz

/-- For a proper bounded left approximate identity, `L.essentialSubmodule` consists exactly of the
points at which it converges to the identity. -/
theorem tendsto_apply_iff_mem_essentialSubmodule (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ L e z) l (𝓝 z) ↔ z ∈ L.essentialSubmodule :=
  ⟨fun h ↦ (isClosed_essentialSubmodule L).mem_of_tendsto h <| .of_forall fun e ↦
      apply_mem_essentialSubmodule L e z,
    tendsto_apply_of_mem_essentialSubmodule L hL hC hl⟩

/-- A bounded left approximate identity of `A` converges to the identity at every point of the
essential part `closure (span (A · E))` of a left `A`-module `E`. -/
theorem tendsto_apply_of_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E}
    (hz : z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure) :
    Tendsto (fun e ↦ L e z) l (𝓝 z) :=
  tendsto_apply_of_mem_essentialSubmodule L hL hC hl hz

/-- The essential part `closure (span (A · E))` of a left `A`-module `E` consists exactly of the
points at which a bounded left approximate identity of `A` converges to the identity. -/
theorem tendsto_apply_iff_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ L e z) l (𝓝 z) ↔
      z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure :=
  tendsto_apply_iff_mem_essentialSubmodule L hL hC hl

/-- A bounded right approximate identity of `A` converges to the identity at every point of
`R.essentialSubmodule`. -/
theorem tendsto_apply_of_mem_essentialSubmodule_right (R : A →L[𝕜] E →L[𝕜] E)
    (hR : ∀ a b z, R (a * b) z = R b (R a z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {z : E}
    (hz : z ∈ R.essentialSubmodule) :
    Tendsto (fun e ↦ R e z) l (𝓝 z) :=
  tendsto_apply_of_mem_essentialSubmodule_aux R hC
    (fun a w ↦ by simpa [Function.comp_def, hR] using ((R.flip w).continuous.tendsto a).comp (hl a))
    hz

/-- For a proper bounded right approximate identity, `R.essentialSubmodule` consists exactly of the
points at which it converges to the identity. -/
theorem tendsto_apply_iff_mem_essentialSubmodule_right (R : A →L[𝕜] E →L[𝕜] E)
    (hR : ∀ a b z, R (a * b) z = R b (R a z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ R e z) l (𝓝 z) ↔ z ∈ R.essentialSubmodule :=
  ⟨fun h ↦ (isClosed_essentialSubmodule R).mem_of_tendsto h <| .of_forall fun e ↦
      apply_mem_essentialSubmodule R e z,
    tendsto_apply_of_mem_essentialSubmodule_right R hR hC hl⟩

/-- In a bounded bimodule over a normed algebra with a bounded two-sided approximate identity, the
two-sided essential submodule `essentialBimoduleSubmodule L R = L.essentialSubmodule ⊓
R.essentialSubmodule` equals the closed linear span of `A · E · A`. -/
theorem essentialBimoduleSubmodule_eq_topologicalClosure_span
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {l : Filter A} (hl : l.IsApproximateUnit)
    {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    essentialBimoduleSubmodule L R =
      (span 𝕜 (Set.range fun p : A × A × E ↦ L p.1 (R p.2.1 p.2.2))).topologicalClosure := by
  have := hl.neBot
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxL, hxR⟩
    -- Along `l`, `L e (R e x) - x = L e (R e x - x) + (L e x - x) → 0`.
    have hLx := tendsto_apply_of_mem_essentialSubmodule L hL hC hl.tendsto_mul_right hxL
    have hRx := tendsto_apply_of_mem_essentialSubmodule_right R hR hC hl.tendsto_mul_left hxR
    have hLRx : Tendsto (fun e ↦ L e (R e x)) l (𝓝 x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at hLx hRx ⊢
      have hdom : Tendsto (fun e ↦ ‖L‖ * |C| * ‖R e x - x‖ + ‖L e x - x‖) l (𝓝 0) := by
        simpa using (hRx.const_mul (‖L‖ * |C|)).add hLx
      refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hdom
      filter_upwards [hC] with e he
      calc ‖L e (R e x) - x‖
          = ‖L e (R e x - x) + (L e x - x)‖ := by rw [map_sub]; abel_nf
        _ ≤ ‖L e (R e x - x)‖ + ‖L e x - x‖ := norm_add_le _ _
        _ ≤ ‖L‖ * ‖e‖ * ‖R e x - x‖ + ‖L e x - x‖ := by gcongr; exact L.le_opNorm₂ _ _
        _ ≤ ‖L‖ * |C| * ‖R e x - x‖ + ‖L e x - x‖ := by gcongr; exact he.trans (le_abs_self C)
    exact (isClosed_topologicalClosure _).mem_of_tendsto hLRx <| .of_forall fun e ↦
      le_topologicalClosure _ <| subset_span ⟨(e, e, x), rfl⟩
  · refine topologicalClosure_minimal _ (span_le.2 ?_)
        (isClosed_essentialBimoduleSubmodule L R)
    rintro _ ⟨⟨a, b, x⟩, rfl⟩
    refine ⟨apply_mem_essentialSubmodule L a (R b x), ?_⟩
    dsimp only
    rw [hLR]
    exact apply_mem_essentialSubmodule R b (L a x)

end ApproximateIdentity

end ContinuousLinearMap
