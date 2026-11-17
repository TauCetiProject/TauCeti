/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Analysis.Matrix.HermitianSignature.Continuity
public import TauCeti.Analysis.Matrix.HermitianSignature.Crossing
import TauCeti.Data.Finset.Basic

/-!
# The negative index along a path with regular crossings

Let `t ↦ V t` be a continuous path of symmetric bilinear forms on a finite-dimensional real
normed space, over a compact interval `[a, b]` with nondegenerate endpoints. Suppose every
*crossing* `t` (a parameter at which `V t` is degenerate) is *regular*: `V` is differentiable at
`t` and its crossing form `ContinuousLinearMap.crossingForm (V t) (V' t)` is nondegenerate. Then
the crossings are finite in number, and the negative index drops from `a` to `b` by the sum of
the signatures of the crossing forms:
`sigNeg (V a) - sigNeg (V b) = ∑ᶠ t ∈ (a, b), (sigPos Γₜ - sigNeg Γₜ)`.

For a path of symmetric matrices with invertible endpoints, the left side is the spectral flow,
the net number of eigenvalues that cross zero from negative to positive. This is therefore the
finite-dimensional case of Robbin and Salamon's formula expressing the spectral flow as the sum of
the signatures of the crossing forms, in which a positive definite crossing form counts
positively. The local jump at one regular crossing is
`ContinuousLinearMap.eventually_sigNeg_sub_sigNeg_eq_sigPos_sub_sigNeg_crossingForm`; between
crossings the negative index is constant, because it is locally constant at nondegenerate forms
(`ContinuousLinearMap.sigNeg_toBilinForm_eq_of_isPreconnected`), and nondegenerate forms are
open (`ContinuousLinearMap.isOpen_setOf_nondegenerate_toBilinForm`).

The endpoints may also be regular crossings. Then the signature of `V t`, the difference of its
positive and negative indices, changes from `a` to `b` by the signatures of the crossing forms,
those at the endpoints counting once and those inside `(a, b)` twice: just after `a` the signature
is that of `V a` plus the signature of the crossing form at `a`
(`ContinuousLinearMap.eventually_sigPos_sub_sigNeg_eq_add_crossingForm`), just before `b` it is
that of `V b` minus the signature of the crossing form at `b`, and in between the formula with
nondegenerate endpoints applies. Half of this change is Robbin and Salamon's spectral flow of a
path with possibly degenerate endpoints, in which an endpoint crossing contributes half its
signature.

## Main results

* `ContinuousLinearMap.finite_setOf_not_nondegenerate_toBilinForm`: a path with nondegenerate
  endpoints and only regular crossings has finitely many crossings.
* `ContinuousLinearMap.sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm`: the negative
  index drops by the sum of the signatures of the crossing forms.
* `ContinuousLinearMap.sigPos_sub_sigNeg_sub_sigPos_sub_sigNeg_eq_crossingForm_add_two_mul_finsum`:
  with crossings allowed at the endpoints, the signature changes by the signatures of the endpoint
  crossing forms plus twice those of the interior ones.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827--844,
  Section 2 (crossing forms and regular crossings).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4 (the spectral flow as a sum of crossing signatures).
-/

public section

open Filter Set Topology
open scoped Finset

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {V V' : ℝ → E →L[ℝ] E →L[ℝ] ℝ} {a b : ℝ}

/-- **Regular crossings are finite in number.** Let `V` be continuous on `[a, b]`, symmetric
there, and nondegenerate at both endpoints. If at every crossing `t ∈ (a, b)` the path `V` is
differentiable with nondegenerate crossing form, then the crossings in `[a, b]` form a finite
set. -/
theorem finite_setOf_not_nondegenerate_toBilinForm (hc : ContinuousOn V (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, (V t).toBilinForm.IsSymm) (ha : (V a).toBilinForm.Nondegenerate)
    (hb : (V b).toBilinForm.Nondegenerate)
    (hV : ∀ t ∈ Ioo a b, ¬(V t).toBilinForm.Nondegenerate → HasDerivAt V (V' t) t)
    (hreg : ∀ t ∈ Ioo a b, ¬(V t).toBilinForm.Nondegenerate →
      (crossingForm (V t) (V' t)).Nondegenerate) :
    {t ∈ Icc a b | ¬(V t).toBilinForm.Nondegenerate}.Finite := by
  by_contra hinf
  obtain ⟨z, hz, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc
    (sep_subset _ _)
  refine (accPt_iff_frequently_nhdsNE.1 hacc) ?_
  by_cases hnz : (V z).toBilinForm.Nondegenerate
  · -- Near a nondegenerate parameter of `[a, b]`, every parameter of `[a, b]` is nondegenerate.
    have hopen := eventually_nhdsWithin_iff.1 <|
      (hc z hz).eventually (isOpen_setOf_nondegenerate_toBilinForm.mem_nhds hnz)
    filter_upwards [nhdsWithin_le_nhds hopen] with t ht htD
    exact htD.2 (ht htD.1)
  · -- A crossing lies in `(a, b)`, and regular crossings are isolated.
    have hz' : z ∈ Ioo a b := ⟨lt_of_le_of_ne hz.1 fun h ↦ hnz (h ▸ ha),
      lt_of_le_of_ne hz.2 fun h ↦ hnz (h ▸ hb)⟩
    filter_upwards [eventually_nondegenerate_of_crossingForm_nondegenerate
      (eventually_of_mem (Icc_mem_nhds hz'.1 hz'.2) hsymm) (hV z hz' hnz) (hreg z hz' hnz)]
      with t ht htD
    exact htD.2 ht

/-- The negative index of `V` is constant from a nondegenerate `s ∈ [a, b]` to `u ≤ b` when no
crossing lies in `(s, u]`. -/
private theorem sigNeg_toBilinForm_eq_of_forall_lt (hc : ContinuousOn V (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, (V t).toBilinForm.IsSymm) {S : Finset ℝ}
    (hS : ∀ t, t ∈ S ↔ t ∈ Icc a b ∧ ¬(V t).toBilinForm.Nondegenerate)
    {s u : ℝ} (hs : s ∈ Icc a b) (hns : (V s).toBilinForm.Nondegenerate) (hsu : s ≤ u)
    (hu : u ≤ b) (hno : ∀ t ∈ S, s < t → u < t) :
    sigNeg (V s).toBilinForm.toQuadraticMap = sigNeg (V u).toBilinForm.toQuadraticMap := by
  have hsub : Icc s u ⊆ Icc a b := Icc_subset_Icc hs.1 hu
  refine sigNeg_toBilinForm_eq_of_isPreconnected isPreconnected_Icc (hc.mono hsub)
    (fun t ht ↦ hsymm t (hsub ht)) (fun t ht ↦ ?_) ⟨le_rfl, hsu⟩ ⟨hsu, le_rfl⟩
  by_contra hnt
  have htS : t ∈ S := (hS t).2 ⟨hsub ht, hnt⟩
  have hst : s < t := lt_of_le_of_ne ht.1 fun h ↦ hnt (h ▸ hns)
  exact (hno t htS hst).not_ge ht.2

/-- Let `S` be the finite set of crossings in `[a, b]`. For every nondegenerate `s ∈ [a, b]`, the
negative index drops from `s` to `b` by the sum of the signatures of the crossing forms at the
crossings after `s`. -/
private theorem sigNeg_sub_sigNeg_eq_sum (hc : ContinuousOn V (Icc a b))
    (hsymm : ∀ t ∈ Icc a b, (V t).toBilinForm.IsSymm) (hb : (V b).toBilinForm.Nondegenerate)
    (hV : ∀ t ∈ Ioo a b, ¬(V t).toBilinForm.Nondegenerate → HasDerivAt V (V' t) t)
    (hreg : ∀ t ∈ Ioo a b, ¬(V t).toBilinForm.Nondegenerate →
      (crossingForm (V t) (V' t)).Nondegenerate)
    {S : Finset ℝ} (hS : ∀ t, t ∈ S ↔ t ∈ Icc a b ∧ ¬(V t).toBilinForm.Nondegenerate)
    {s : ℝ} (hs : s ∈ Icc a b) (hns : (V s).toBilinForm.Nondegenerate) :
    (sigNeg (V s).toBilinForm.toQuadraticMap : ℤ) - sigNeg (V b).toBilinForm.toQuadraticMap =
      ∑ t ∈ S with s < t,
        ((sigPos (crossingForm (V t) (V' t)) : ℤ) - sigNeg (crossingForm (V t) (V' t))) := by
  induction hn : #{t ∈ S | s < t} using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  -- Induct on the number of crossings after `s`: the first crossing `c` after `s` is passed with
  -- `eventually_sigNeg_sub_sigNeg_eq_sigPos_sub_sigNeg_crossingForm`, landing at a nondegenerate
  -- `t₂ > c` with no crossing in `(c, t₂]`.
  rcases Finset.eq_empty_or_nonempty {t ∈ S | s < t} with hempty | hne
  · -- No crossing after `s`.
    rw [hempty, Finset.sum_empty, sub_eq_zero, Nat.cast_inj]
    exact sigNeg_toBilinForm_eq_of_forall_lt hc hsymm hS hs hns hs.2 le_rfl fun t ht hst ↦
      (Finset.eq_empty_iff_forall_notMem.1 hempty t (Finset.mem_filter.2 ⟨ht, hst⟩)).elim
  · -- `c` is the first crossing after `s`.
    set c := Finset.min' _ hne
    have hcmem := Finset.mem_filter.1 (Finset.min'_mem _ hne)
    have hcmin : ∀ t ∈ S, s < t → c ≤ t := fun t ht hst ↦
      Finset.min'_le _ t (Finset.mem_filter.2 ⟨ht, hst⟩)
    obtain ⟨hcI, hnc⟩ := (hS c).1 hcmem.1
    have hsc : s < c := hcmem.2
    have hcb : c < b := lt_of_le_of_ne hcI.2 fun h ↦ hnc (h ▸ hb)
    have hc' : c ∈ Ioo a b := ⟨hs.1.trans_lt hsc, hcb⟩
    have hsymmc : ∀ᶠ t in 𝓝 c, (V t).toBilinForm.IsSymm :=
      eventually_of_mem (Icc_mem_nhds hc'.1 hc'.2) hsymm
    -- Just after `c` there is no crossing up to some `u > c`.
    obtain ⟨u, hcu, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 <|
      (eventually_nondegenerate_of_crossingForm_nondegenerate hsymmc (hV c hc' hnc)
        (hreg c hc' hnc)).filter_mono (nhdsWithin_mono _ fun _ h ↦ ne_of_gt h)
    -- Pick `t₁ ∈ (s, c)` and `t₂ ∈ (c, min u b)` across which the negative index jumps by the
    -- signature of the crossing form at `c`.
    obtain ⟨t₁, hjump, ht₁⟩ :=
      ((eventually_sigNeg_sub_sigNeg_eq_sigPos_sub_sigNeg_crossingForm (hsymm c hcI)
        (hV c hc' hnc) (hreg c hc' hnc)).and (Ioo_mem_nhdsLT hsc)).exists
    obtain ⟨t₂, hjump, ht₂⟩ := (hjump.and (Ioo_mem_nhdsGT (lt_min hcu hcb))).exists
    have hnt₂ : (V t₂).toBilinForm.Nondegenerate := hu ⟨ht₂.1, ht₂.2.trans_le (min_le_left _ _)⟩
    have ht₂I : t₂ ∈ Icc a b := ⟨hc'.1.le.trans ht₂.1.le, (ht₂.2.trans_le (min_le_right _ _)).le⟩
    -- The crossings after `s` are `c` and the crossings after `t₂`.
    have hsplit : {t ∈ S | s < t} = insert c {t ∈ S | t₂ < t} :=
      Finset.filter_lt_eq_insert_of_forall_lt hcmem.1 hsc hcmin ht₂.1 fun t htS h ↦
        lt_of_not_ge fun htt₂ ↦ ((hS t).1 htS).2
          (hu ⟨h, htt₂.trans_lt (ht₂.2.trans_le (min_le_left _ _))⟩)
    have hcnot : c ∉ {t ∈ S | t₂ < t} := fun h ↦ (Finset.mem_filter.1 h).2.not_gt ht₂.1
    have hcard : #{t ∈ S | t₂ < t} < n := by
      rw [← hn, hsplit, Finset.card_insert_of_notMem hcnot]
      exact Nat.lt_succ_self _
    -- Assemble: no change on `[s, t₁]`, the jump at `c`, and the induction hypothesis at `t₂`.
    have h₁ : sigNeg (V s).toBilinForm.toQuadraticMap = sigNeg (V t₁).toBilinForm.toQuadraticMap :=
      sigNeg_toBilinForm_eq_of_forall_lt hc hsymm hS hs hns ht₁.1.le (ht₁.2.trans hcb).le
        fun t htS hst ↦ ht₁.2.trans_le (hcmin t htS hst)
    rw [hsplit, Finset.sum_insert hcnot, ← hjump, ← ih _ hcard ht₂I hnt₂ rfl, h₁]
    ring

/-- **The regular-crossing formula for the negative index.** Let `V` be a path of symmetric
continuous bilinear forms on a finite-dimensional real space, continuous on `[a, b]` and
nondegenerate at both endpoints. Suppose that at every crossing `t ∈ (a, b)`, where `V t` is
degenerate, `V` has derivative `V' t` and the crossing form of `V t` and `V' t` is nondegenerate.
Then the negative index of `V a` exceeds that of `V b` by the sum, over the (finitely many)
crossings, of the signatures of the crossing forms. Parameters where `V t` is nondegenerate
contribute zero to the sum. -/
theorem sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm (hab : a ≤ b)
    (hc : ContinuousOn V (Icc a b)) (hsymm : ∀ t ∈ Icc a b, (V t).toBilinForm.IsSymm)
    (ha : (V a).toBilinForm.Nondegenerate) (hb : (V b).toBilinForm.Nondegenerate)
    (hV : ∀ t ∈ Ioo a b, ¬(V t).toBilinForm.Nondegenerate → HasDerivAt V (V' t) t)
    (hreg : ∀ t ∈ Ioo a b, ¬(V t).toBilinForm.Nondegenerate →
      (crossingForm (V t) (V' t)).Nondegenerate) :
    (sigNeg (V a).toBilinForm.toQuadraticMap : ℤ) - sigNeg (V b).toBilinForm.toQuadraticMap =
      ∑ᶠ t ∈ Ioo a b,
        ((sigPos (crossingForm (V t) (V' t)) : ℤ) - sigNeg (crossingForm (V t) (V' t))) := by
  have hfin := finite_setOf_not_nondegenerate_toBilinForm hc hsymm ha hb hV hreg
  have hS : ∀ t, t ∈ hfin.toFinset ↔ t ∈ Icc a b ∧ ¬(V t).toBilinForm.Nondegenerate := by
    simp
  have ha' : ∀ t ∈ hfin.toFinset, a < t := fun t ht ↦ by
    obtain ⟨htI, hnt⟩ := (hS t).1 ht
    exact lt_of_le_of_ne htI.1 fun h ↦ hnt (h ▸ ha)
  rw [sigNeg_sub_sigNeg_eq_sum hc hsymm hb hV hreg hS ⟨le_rfl, hab⟩ ha,
    Finset.filter_true_of_mem ha']
  refine (finsum_mem_eq_sum_of_inter_support_eq _ ?_).symm
  ext t
  simp only [mem_inter_iff, Finset.mem_coe, hS, Function.mem_support]
  refine and_congr_left fun hft ↦ ?_
  -- Only crossings contribute, and the crossings in `[a, b]` lie in `(a, b)`.
  have hnt : ¬(V t).toBilinForm.Nondegenerate := fun hnt ↦
    hft (sigPos_sub_sigNeg_crossingForm_eq_zero hnt (V' t))
  refine ⟨fun ht ↦ ⟨Ioo_subset_Icc_self ht, hnt⟩, fun ⟨ht, _⟩ ↦ ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_ne ht.1 fun h ↦ hnt (h ▸ ha)
  · exact lt_of_le_of_ne ht.2 fun h ↦ hnt (h ▸ hb)

/-! ### Degenerate endpoints -/

omit [FiniteDimensional ℝ E] in
/-- Two nondegenerate symmetric forms with the same negative index have the same signature. -/
private theorem sigPos_sub_sigNeg_eq_of_sigNeg_eq {B C : E →L[ℝ] E →L[ℝ] ℝ}
    (hBs : B.toBilinForm.IsSymm) (hB : B.toBilinForm.Nondegenerate) (hCs : C.toBilinForm.IsSymm)
    (hC : C.toBilinForm.Nondegenerate)
    (h : sigNeg B.toBilinForm.toQuadraticMap = sigNeg C.toBilinForm.toQuadraticMap) :
    (sigPos B.toBilinForm.toQuadraticMap : ℤ) - sigNeg B.toBilinForm.toQuadraticMap =
      (sigPos C.toBilinForm.toQuadraticMap : ℤ) - sigNeg C.toBilinForm.toQuadraticMap := by
  have hB' := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _
    ((LinearMap.BilinForm.nondegenerate_toQuadraticMap_iff hBs).2 hB)
  have hC' := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _
    ((LinearMap.BilinForm.nondegenerate_toQuadraticMap_iff hCs).2 hC)
  omega

/-- Near a nondegenerate point `t₀` of a path continuous and symmetric on `s`, the path is
nondegenerate, within `s`, and keeps the signature of `V t₀`. -/
private theorem eventually_nhdsWithin_sigPos_sub_sigNeg_eq {s : Set ℝ} (hc : ContinuousOn V s)
    (hsymm : ∀ t ∈ s, (V t).toBilinForm.IsSymm) (ht₀ : t₀ ∈ s)
    (hnd : (V t₀).toBilinForm.Nondegenerate) :
    ∀ᶠ t in 𝓝[s] t₀, (sigPos (V t).toBilinForm.toQuadraticMap : ℤ) -
        sigNeg (V t).toBilinForm.toQuadraticMap =
      (sigPos (V t₀).toBilinForm.toQuadraticMap : ℤ) - sigNeg (V t₀).toBilinForm.toQuadraticMap ∧
        (V t).toBilinForm.Nondegenerate := by
  have hnd' : ∀ᶠ t in 𝓝[s] t₀, (V t).toBilinForm.Nondegenerate :=
    (hc t₀ ht₀).eventually (isOpen_setOf_nondegenerate_toBilinForm.mem_nhds hnd)
  -- The negative index is locally constant at `t₀` along the subspace `s`.
  have hneg : ∀ᶠ t in 𝓝[s] t₀, sigNeg (V t).toBilinForm.toQuadraticMap =
      sigNeg (V t₀).toBilinForm.toQuadraticMap := by
    rw [nhdsWithin_eq_map_subtype_coe ht₀, eventually_map]
    exact eventually_sigNeg_toBilinForm_eq_of_continuousAt (V := s.domRestrict V) (x := ⟨t₀, ht₀⟩)
      (Eventually.of_forall fun u ↦ hsymm u u.2) hc.domRestrict.continuousAt hnd
  filter_upwards [hnd', hneg, self_mem_nhdsWithin] with t ht hnt hts
  exact ⟨sigPos_sub_sigNeg_eq_of_sigNeg_eq (hsymm t hts) ht (hsymm t₀ ht₀) hnd hnt, ht⟩

/-- Just after the left endpoint of `[a, b]`, a path with a regular crossing or no crossing at `a`
is nondegenerate, and its signature is that of `V a` plus the signature of the crossing form. -/
private theorem eventually_nhdsGT_sigPos_sub_sigNeg_eq_left (hab : a < b)
    (hc : ContinuousOn V (Icc a b)) (hsymm : ∀ t ∈ Icc a b, (V t).toBilinForm.IsSymm)
    (hV : ¬(V a).toBilinForm.Nondegenerate → HasDerivWithinAt V (V' a) (Icc a b) a)
    (hreg : ¬(V a).toBilinForm.Nondegenerate → (crossingForm (V a) (V' a)).Nondegenerate) :
    ∀ᶠ t in 𝓝[>] a, (sigPos (V t).toBilinForm.toQuadraticMap : ℤ) -
        sigNeg (V t).toBilinForm.toQuadraticMap =
      (sigPos (V a).toBilinForm.toQuadraticMap : ℤ) - sigNeg (V a).toBilinForm.toQuadraticMap +
        ((sigPos (crossingForm (V a) (V' a)) : ℤ) - sigNeg (crossingForm (V a) (V' a))) ∧
        (V t).toBilinForm.Nondegenerate := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  by_cases hnd : (V a).toBilinForm.Nondegenerate
  · rw [sigPos_sub_sigNeg_crossingForm_eq_zero hnd, add_zero]
    exact (eventually_nhdsWithin_sigPos_sub_sigNeg_eq hc hsymm ha hnd).filter_mono
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT hab))
  · have hd := HasDerivWithinAt.mono_of_mem_nhdsWithin (f := V) (f' := V' a) (hV hnd)
      (Icc_mem_nhdsGE hab)
    exact (eventually_sigPos_sub_sigNeg_eq_add_crossingForm (hsymm a ha) hd (hreg hnd)).and
      (eventually_nhdsGT_nondegenerate_of_crossingForm_nondegenerate
        (eventually_of_mem (Icc_mem_nhdsGT hab) hsymm) (hsymm a ha) hd (hreg hnd))

/-- Just before the right endpoint of `[a, b]`, a path with a regular crossing or no crossing at
`b` is nondegenerate, and its signature is that of `V b` minus the signature of the crossing
form. -/
private theorem eventually_nhdsLT_sigPos_sub_sigNeg_eq_right (hab : a < b)
    (hc : ContinuousOn V (Icc a b)) (hsymm : ∀ t ∈ Icc a b, (V t).toBilinForm.IsSymm)
    (hV : ¬(V b).toBilinForm.Nondegenerate → HasDerivWithinAt V (V' b) (Icc a b) b)
    (hreg : ¬(V b).toBilinForm.Nondegenerate → (crossingForm (V b) (V' b)).Nondegenerate) :
    ∀ᶠ t in 𝓝[<] b, (sigPos (V t).toBilinForm.toQuadraticMap : ℤ) -
        sigNeg (V t).toBilinForm.toQuadraticMap =
      (sigPos (V b).toBilinForm.toQuadraticMap : ℤ) - sigNeg (V b).toBilinForm.toQuadraticMap -
        ((sigPos (crossingForm (V b) (V' b)) : ℤ) - sigNeg (crossingForm (V b) (V' b))) ∧
        (V t).toBilinForm.Nondegenerate := by
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  by_cases hnd : (V b).toBilinForm.Nondegenerate
  · rw [sigPos_sub_sigNeg_crossingForm_eq_zero hnd, sub_zero]
    exact (eventually_nhdsWithin_sigPos_sub_sigNeg_eq hc hsymm hb hnd).filter_mono
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT hab))
  · have hd := HasDerivWithinAt.mono_of_mem_nhdsWithin (f := V) (f' := V' b) (hV hnd)
      (Icc_mem_nhdsLE hab)
    exact (eventually_sigPos_sub_sigNeg_eq_sub_crossingForm (hsymm b hb) hd (hreg hnd)).and
      (eventually_nhdsLT_nondegenerate_of_crossingForm_nondegenerate
        (eventually_of_mem (Icc_mem_nhdsLT hab) hsymm) (hsymm b hb) hd (hreg hnd))

/-- **The regular-crossing formula for the signature, with endpoint crossings.** Let `V` be a path
of symmetric continuous bilinear forms on a finite-dimensional real space, continuous on `[a, b]`
with `a < b`. Suppose that at every crossing `t ∈ [a, b]`, where `V t` is degenerate, `V` has
derivative `V' t` within `[a, b]` and the crossing form of `V t` and `V' t` is nondegenerate. Then
the signature of `V` changes from `a` to `b` by the signatures of the crossing forms, the
crossings inside `(a, b)` counting twice and those at the endpoints once. In the normalization of
Robbin and Salamon, where the spectral flow is half the change of the signature, an endpoint
crossing contributes half its signature. Parameters where `V t` is nondegenerate contribute zero. -/
theorem sigPos_sub_sigNeg_sub_sigPos_sub_sigNeg_eq_crossingForm_add_two_mul_finsum (hab : a < b)
    (hc : ContinuousOn V (Icc a b)) (hsymm : ∀ t ∈ Icc a b, (V t).toBilinForm.IsSymm)
    (hV : ∀ t ∈ Icc a b, ¬(V t).toBilinForm.Nondegenerate →
      HasDerivWithinAt V (V' t) (Icc a b) t)
    (hreg : ∀ t ∈ Icc a b, ¬(V t).toBilinForm.Nondegenerate →
      (crossingForm (V t) (V' t)).Nondegenerate) :
    (sigPos (V b).toBilinForm.toQuadraticMap : ℤ) - sigNeg (V b).toBilinForm.toQuadraticMap -
        ((sigPos (V a).toBilinForm.toQuadraticMap : ℤ) -
          sigNeg (V a).toBilinForm.toQuadraticMap) =
      (sigPos (crossingForm (V a) (V' a)) : ℤ) - sigNeg (crossingForm (V a) (V' a)) +
        2 * ∑ᶠ t ∈ Ioo a b,
          ((sigPos (crossingForm (V t) (V' t)) : ℤ) - sigNeg (crossingForm (V t) (V' t))) +
        ((sigPos (crossingForm (V b) (V' b)) : ℤ) - sigNeg (crossingForm (V b) (V' b))) := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
  -- Nondegenerate intervals `(a, u)` and `(l, b)` on which the signature is that of the endpoint
  -- corrected by its crossing form.
  obtain ⟨u, hu, hau⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_nhdsGT_sigPos_sub_sigNeg_eq_left hab hc hsymm (hV a ha) (hreg a ha))
  obtain ⟨l, hl, hlb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1
    (eventually_nhdsLT_sigPos_sub_sigNeg_eq_right hab hc hsymm (hV b hb) (hreg b hb))
  set m := (a + b) / 2
  set t₁ := (a + min u m) / 2
  set t₂ := (max l m + b) / 2
  have hum : a < min u m := lt_min hu (by simp only [m]; linarith)
  have hlm : max l m < b := max_lt hl (by simp only [m]; linarith)
  have hat₁ : a < t₁ := by simp only [t₁]; linarith
  have ht₁u : t₁ < min u m := by simp only [t₁]; linarith
  have hlt₂ : max l m < t₂ := by simp only [t₂]; linarith
  have ht₂b : t₂ < b := by simp only [t₂]; linarith
  have ht₁₂ : t₁ < t₂ := ht₁u.trans_le ((min_le_right _ _).trans ((le_max_right _ _).trans
    hlt₂.le))
  obtain ⟨h₁, hnd₁⟩ : _ ∧ _ := hau ⟨hat₁, ht₁u.trans_le (min_le_left _ _)⟩
  obtain ⟨h₂, hnd₂⟩ : _ ∧ _ := hlb ⟨(le_max_left _ _).trans_lt hlt₂, ht₂b⟩
  have hsub : Icc t₁ t₂ ⊆ Icc a b := Icc_subset_Icc hat₁.le ht₂b.le
  have hIoo {t : ℝ} (ht : t ∈ Ioo t₁ t₂) : t ∈ Ioo a b := ⟨hat₁.trans ht.1, ht.2.trans ht₂b⟩
  -- The interior crossings are those of `[t₁, t₂]`, where the existing formula applies.
  have hint := sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm (V' := V') ht₁₂.le
    (hc.mono hsub) (fun t ht ↦ hsymm t (hsub ht)) hnd₁ hnd₂
    (fun t ht hnt ↦ HasDerivWithinAt.hasDerivAt (f := V) (f' := V' t)
      (hV t (hsub (Ioo_subset_Icc_self ht)) hnt) (Icc_mem_nhds (hIoo ht).1 (hIoo ht).2))
    (fun t ht hnt ↦ hreg t (hsub (Ioo_subset_Icc_self ht)) hnt)
  have hsum : ∑ᶠ t ∈ Ioo a b,
        ((sigPos (crossingForm (V t) (V' t)) : ℤ) - sigNeg (crossingForm (V t) (V' t))) =
      ∑ᶠ t ∈ Ioo t₁ t₂,
        ((sigPos (crossingForm (V t) (V' t)) : ℤ) - sigNeg (crossingForm (V t) (V' t))) := by
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext t
    simp only [mem_inter_iff, Function.mem_support]
    refine ⟨fun ⟨ht, hft⟩ ↦ ⟨⟨?_, ?_⟩, hft⟩, fun ⟨ht, hft⟩ ↦ ⟨hIoo ht, hft⟩⟩
    all_goals
      have hnt : ¬(V t).toBilinForm.Nondegenerate := fun hnt ↦
        hft (sigPos_sub_sigNeg_crossingForm_eq_zero hnt (V' t))
    · by_contra! h
      exact hnt (hau ⟨ht.1, h.trans_lt (ht₁u.trans_le (min_le_left _ _))⟩).2
    · by_contra! h
      exact hnt (hlb ⟨(le_max_left _ _).trans_lt (hlt₂.trans_le h), ht.2⟩).2
  have hd₁ := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _
    ((LinearMap.BilinForm.nondegenerate_toQuadraticMap_iff
      (hsymm t₁ (hsub (left_mem_Icc.2 ht₁₂.le)))).2 hnd₁)
  have hd₂ := QuadraticForm.sigPos_add_sigNeg_of_nondegenerate _
    ((LinearMap.BilinForm.nondegenerate_toQuadraticMap_iff
      (hsymm t₂ (hsub (right_mem_Icc.2 ht₁₂.le)))).2 hnd₂)
  rw [hsum]
  omega

end ContinuousLinearMap
