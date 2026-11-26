/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Order.LiminfLimsup
public import TauCeti.Analysis.Normed.Ring.TwoSidedIdeal
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Two-sided ideals of bounded continuous functions vanishing along a filter

For a topological space `α`, a filter `l : Filter α`, and a possibly nonunital seminormed ring `R`,
the bounded continuous functions `f : α →ᵇ R` tending to `0` along `l` form a closed two-sided
ideal `BoundedContinuousFunction.tendstoZeroIdeal R l` of `α →ᵇ R`.

When `α = Set.Ici a` (`a : ℝ`), `l = atTop`, and `R` is also a normed `ℝ`-vector space, the
quotient seminorm on `(Set.Ici a →ᵇ R) ⧸ tendstoZeroIdeal R atTop` is given by the asymptotic upper
limit `‖mk (tendstoZeroIdeal R atTop) f‖ = limsup (fun t ↦ ‖f t‖) atTop`. Specializing `a = 1` and
`R` to a C⋆-algebra `B` yields the asymptotic C⋆-algebra `C_b([1, ∞), B) / C₀([1, ∞), B)` and its
asymptotic seminorm formula (Blackadar, *K-Theory for Operator Algebras*, §25.1).

## Main definitions and results

* `BoundedContinuousFunction.tendstoZeroIdeal`: the closed two-sided ideal
  `{f : α →ᵇ R | Tendsto f l (𝓝 0)}` of `α →ᵇ R`.
* `BoundedContinuousFunction.isClosed_tendstoZeroIdeal`: `tendstoZeroIdeal R l` is norm-closed.
* `BoundedContinuousFunction.norm_mk_tendstoZeroIdeal_Ici_eq_limsup`: the quotient norm modulo
  `tendstoZeroIdeal R atTop` on `Set.Ici a →ᵇ R` equals `limsup (fun t ↦ ‖f t‖) atTop`.

## References

* Bruce Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**, Cambridge
  University Press, 1998, §25.1.
-/

public section

open Filter Metric Set Topology
open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

section GeneralIdeal

variable {α : Type*} [TopologicalSpace α]

/-- The two-sided ideal of bounded continuous functions `α →ᵇ R` tending to `0` along a filter
`l : Filter α`. -/
noncomputable def tendstoZeroIdeal (R : Type*) [NonUnitalSeminormedRing R] (l : Filter α) :
    TwoSidedIdeal (α →ᵇ R) :=
  TwoSidedIdeal.mk' {f : α →ᵇ R | Tendsto f l (𝓝 0)} tendsto_const_nhds
    (fun {_ _} hf hg ↦ by
      rw [mem_ofPred_eq] at hf hg ⊢
      simpa only [FunLike.coe_add, Pi.add_def, add_zero] using hf.add hg)
    (fun {_} hf ↦ by
      rw [mem_ofPred_eq] at hf ⊢
      simpa only [FunLike.coe_neg, Pi.neg_def, neg_zero] using hf.neg)
    (fun f {g} hg ↦ by
      rw [mem_ofPred_eq, tendsto_zero_iff_norm_tendsto_zero] at hg ⊢
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun x ↦ (norm_mul_le (f x) (g x)).trans
          (mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg (g x))))
        (by simpa only [mul_zero] using hg.const_mul ‖f‖))
    (fun {f} g hf ↦ by
      rw [mem_ofPred_eq, tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
      exact squeeze_zero (fun _ ↦ norm_nonneg _)
        (fun x ↦ (norm_mul_le (f x) (g x)).trans
          (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm x) (norm_nonneg (f x))))
        (by simpa only [zero_mul] using hf.mul_const ‖g‖))

@[simp, grind =]
theorem mem_tendstoZeroIdeal_iff {R : Type*} [NonUnitalSeminormedRing R] {l : Filter α}
    {f : α →ᵇ R} : f ∈ tendstoZeroIdeal R l ↔ Tendsto f l (𝓝 0) :=
  (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ f).trans mem_ofPred

theorem mem_tendstoZeroIdeal_iff_norm {R : Type*} [NonUnitalSeminormedRing R] {l : Filter α}
    {f : α →ᵇ R} : f ∈ tendstoZeroIdeal R l ↔ Tendsto (fun x ↦ ‖f x‖) l (𝓝 0) :=
  mem_tendstoZeroIdeal_iff.trans tendsto_zero_iff_norm_tendsto_zero

/-- The ideal `tendstoZeroIdeal R l` of bounded continuous functions vanishing along `l` is closed
in the supremum norm. -/
instance isClosed_tendstoZeroIdeal (R : Type*) [NonUnitalSeminormedRing R] (l : Filter α) :
    IsClosed (tendstoZeroIdeal R l : Set (α →ᵇ R)) := by
  have h : (tendstoZeroIdeal R l : Set (α →ᵇ R)) = {f | Tendsto (fun x ↦ f x) l (𝓝 0)} := by
    ext f; exact mem_tendstoZeroIdeal_iff
  rw [h]
  exact (LipschitzWith.uniformEquicontinuous (fun x (f : α →ᵇ R) ↦ f x) 1
    lipschitz_eval_const).equicontinuous.isClosed_setOfPred_tendsto continuous_const

theorem mk_tendstoZeroIdeal_eq_zero_iff {R : Type*} [NonUnitalSeminormedRing R] {l : Filter α}
    {f : α →ᵇ R} :
    TwoSidedIdeal.Quotient.mk (tendstoZeroIdeal R l) f = 0 ↔ Tendsto f l (𝓝 0) :=
  TwoSidedIdeal.Quotient.eq_zero_iff_mem.trans mem_tendstoZeroIdeal_iff

theorem mk_tendstoZeroIdeal_eq_iff {R : Type*} [NonUnitalSeminormedRing R] {l : Filter α}
    {f g : α →ᵇ R} :
    TwoSidedIdeal.Quotient.mk (tendstoZeroIdeal R l) f =
      TwoSidedIdeal.Quotient.mk (tendstoZeroIdeal R l) g ↔
      Tendsto (fun x ↦ f x - g x) l (𝓝 0) := by
  rw [← sub_eq_zero, ← map_sub, mk_tendstoZeroIdeal_eq_zero_iff]; rfl

end GeneralIdeal

section Ici

variable {a : ℝ}

/-- Piecewise-linear cutoff on `Set.Ici a` equal to `1` on `[a, T]` and `0` on `[T + 1, ∞)`. -/
private def cutoffIci (T t : Ici a) : ℝ := max 0 (min 1 ((T : ℝ) + 1 - (t : ℝ)))

private theorem continuous_cutoffIci (T : Ici a) : Continuous (cutoffIci T) := by
  unfold cutoffIci; fun_prop

private theorem cutoffIci_nonneg (T t : Ici a) : 0 ≤ cutoffIci T t := le_max_left _ _

private theorem cutoffIci_le_one (T t : Ici a) : cutoffIci T t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem cutoffIci_eq_one_of_le {T t : Ici a} (ht : t ≤ T) : cutoffIci T t = 1 := by
  have h1 : 1 ≤ (T : ℝ) + 1 - (t : ℝ) := by linarith [Subtype.coe_le_coe.mpr ht]
  simp [cutoffIci, min_eq_left h1]

private theorem cutoffIci_eq_zero_of_add_one_le {T t : Ici a} (ht : (T : ℝ) + 1 ≤ (t : ℝ)) :
    cutoffIci T t = 0 :=
  max_eq_left ((min_le_right _ _).trans (by linarith))

/-- On `Set.Ici a →ᵇ R` for a normed `ℝ`-space seminormed ring `R`, the quotient norm modulo
`tendstoZeroIdeal R atTop` equals `limsup (fun t ↦ ‖f t‖) atTop`. -/
theorem norm_mk_tendstoZeroIdeal_Ici_eq_limsup {R : Type*} [NonUnitalSeminormedRing R]
    [NormedSpace ℝ R] (f : Ici a →ᵇ R) :
    ‖TwoSidedIdeal.Quotient.mk (tendstoZeroIdeal R atTop) f‖ =
      limsup (fun t : Ici a ↦ ‖f t‖) atTop := by
  have : Nonempty (Ici a) := ⟨⟨a, le_rfl⟩⟩
  have hb : IsBoundedUnder (· ≤ ·) (atTop : Filter (Ici a)) (fun t ↦ ‖f t‖) :=
    ⟨‖f‖, eventually_map.mpr (Eventually.of_forall f.norm_coe_le_norm)⟩
  have hc : IsCoboundedUnder (· ≤ ·) (atTop : Filter (Ici a)) (fun t ↦ ‖f t‖) :=
    isCoboundedUnder_le_of_eventually_le _ (Eventually.of_forall fun t ↦ norm_nonneg (f t))
  have hL_nonneg : 0 ≤ limsup (fun t : Ici a ↦ ‖f t‖) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun t ↦ norm_nonneg (f t)) hb
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) ?_
  · set L := limsup (fun t : Ici a ↦ ‖f t‖) atTop
    obtain ⟨T, hT⟩ :=
      eventually_atTop.mp (eventually_lt_of_limsup_lt (lt_add_of_pos_right L hε) hb)
    let g : Ici a →ᵇ R :=
      ofNormedAddCommGroup (fun t ↦ -(cutoffIci T t • f t))
        (((continuous_cutoffIci T).smul f.continuous).neg) ‖f‖ fun t ↦ by
          rw [norm_neg, norm_smul, Real.norm_of_nonneg (cutoffIci_nonneg T t)]
          exact (mul_le_of_le_one_left (norm_nonneg _) (cutoffIci_le_one T t)).trans
            (f.norm_coe_le_norm t)
    have hg_apply (t : Ici a) : g t = -(cutoffIci T t • f t) :=
      congrFun (coe_ofNormedAddCommGroup _ _ _ _) t
    have hg_mem : g ∈ tendstoZeroIdeal R atTop := by
      rw [mem_tendstoZeroIdeal_iff]
      refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨⟨(T : ℝ) + 1, ?_⟩, fun t ht ↦ ?_⟩)
      · exact mem_Ici.mpr (by linarith [mem_Ici.mp T.property])
      · rw [hg_apply, cutoffIci_eq_zero_of_add_one_le (Subtype.coe_le_coe.mpr ht),
          zero_smul, neg_zero]
    have hmk : TwoSidedIdeal.Quotient.mk (tendstoZeroIdeal R atTop) f =
        TwoSidedIdeal.Quotient.mk (tendstoZeroIdeal R atTop) (f + g) := by
      rw [map_add, TwoSidedIdeal.Quotient.eq_zero_iff_mem.mpr hg_mem, add_zero]
    rw [hmk]
    refine (TwoSidedIdeal.Quotient.norm_mk_le _ (f + g)).trans
      ((BoundedContinuousFunction.norm_le (by linarith)).mpr fun t ↦ ?_)
    have hval : (f + g) t = (1 - cutoffIci T t) • f t := by
      rw [add_apply, hg_apply, sub_smul, one_smul, sub_eq_add_neg]
    rw [hval, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr (cutoffIci_le_one T t))]
    rcases le_total t T with htT | hTt
    · rw [cutoffIci_eq_one_of_le htT, sub_self, zero_mul]; linarith
    · exact (mul_le_of_le_one_left (norm_nonneg _)
        (sub_le_self 1 (cutoffIci_nonneg T t))).trans (hT t hTt).le
  · rw [TwoSidedIdeal.Quotient.norm_mk_eq]
    refine le_csInf ⟨‖f + 0‖, 0, (tendstoZeroIdeal R atTop).zero_mem, rfl⟩ ?_
    rintro _ ⟨g, hg, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε ↦ limsup_le_of_le hc ?_
    filter_upwards [(Metric.tendsto_nhds.mp (mem_tendstoZeroIdeal_iff_norm.mp hg)) ε hε] with t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at ht
    calc ‖f t‖ = ‖(f + g) t - g t‖ := by simp
      _ ≤ ‖f + g‖ + ε :=
        (norm_sub_le _ _).trans (add_le_add ((f + g).norm_coe_le_norm t) ht.le)

end Ici

end BoundedContinuousFunction
