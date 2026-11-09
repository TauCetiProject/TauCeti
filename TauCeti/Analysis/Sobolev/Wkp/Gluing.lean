/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Gluing
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# Gluing arbitrary-order Sobolev functions along finite open covers

Let `V i` be a finite family of open sets covering an open set `Ω`. Sobolev functions
`w i ∈ W^{k,p}(V i)` whose values agree almost everywhere with one function `u` come from a
single `v ∈ W^{k,p}(Ω)` with value `u`, which restricts to `w i` on each `V i` and satisfies
`‖v‖ ≤ ∑ᵢ ‖w i‖` (`TauCeti.Wkp.exists_glue`). Equivalently, a family whose restrictions agree on
the pairwise intersections glues (`TauCeti.Wkp.exists_glue_of_restrictL_eq`). The glued function
is unique, since a Sobolev function on `Ω` is determined by its restrictions to the members of any
countable open cover (`TauCeti.Wkp.ext_of_restrictL_eq`).

These are the statements used to pass between a Sobolev function on a domain and its restrictions
to the charts of a finite atlas, for every order `k` and every `1 ≤ p ≤ ∞`. No boundary
regularity of the sets is used.

The weak derivatives are glued at each order with `TauCeti.exists_hasWeakFDerivOn_iSup`, and the
norm bound comes from subadditivity of `eLpNorm` over a finite union
(`MeasureTheory.eLpNorm_restrict_biUnion_finset_le`). At order one the norm is the `Lᵖ` norm of
the pointwise Euclidean value-gradient norm, so the bound is a single `Lᵖ` estimate; above order
one the norm is the Euclidean product of the lower-order norm and the highest-derivative norm, and
the bound uses the triangle inequality in the plane.

## Main results

* `TauCeti.Wkp.exists_glue`: gluing along a finite open cover with prescribed value.
* `TauCeti.Wkp.exists_glue_of_restrictL_eq`: gluing compatible families along a finite open cover.
* `TauCeti.Wkp.ext_of_restrictL_eq`: restrictions to a countable open cover determine a Sobolev
  function.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1 (localization of Sobolev
  functions with a finite cover).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, §9.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] {mu : Measure E}
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*}

/-- Almost-everywhere statements on the members of a countable cover of `Ω` hold almost
everywhere on `Ω`. -/
private theorem ae_restrict_of_cover [Countable ι] {V : ι → Opens E} (hcov : Omega ≤ ⨆ i, V i)
    {P : E → Prop} (h : ∀ i, ∀ᵐ x ∂mu.restrict (V i : Set E), P x) :
    ∀ᵐ x ∂mu.restrict (Omega : Set E), P x := by
  have hsub : (Omega : Set E) ⊆ ⋃ i, (V i : Set E) := by
    simpa only [Opens.coe_iSup] using SetLike.coe_subset_coe.mpr hcov
  exact ae_mono (Measure.restrict_mono_set mu hsub) ((ae_restrict_iUnion_iff _ _).2 h)

/-- A function in `Lᵖ` on each member of a finite cover of `Ω` is in `Lᵖ` on `Ω`, with
`eLpNorm` at most the sum of the `eLpNorm`s on the members. -/
private theorem memLp_and_eLpNorm_le_of_cover [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    {V : ι → Opens E} (hcov : Omega ≤ ⨆ i, V i) {f : E → F}
    (hf : ∀ i, MemLp f p (mu.restrict (V i : Set E))) :
    MemLp f p (mu.restrict (Omega : Set E)) ∧
      eLpNorm f p (mu.restrict (Omega : Set E)) ≤
        ∑ i, eLpNorm f p (mu.restrict (V i : Set E)) := by
  have hsub : (Omega : Set E) ⊆ ⋃ i, (V i : Set E) := by
    simpa only [Opens.coe_iSup] using SetLike.coe_subset_coe.mpr hcov
  have hU : eLpNorm f p (mu.restrict (⋃ i, (V i : Set E))) ≤
      ∑ i, eLpNorm f p (mu.restrict (V i : Set E)) := by
    simpa only [Finset.mem_univ, iUnion_true] using
      eLpNorm_restrict_biUnion_finset_le (μ := mu) f Fact.out Finset.univ
        fun i => (V i : Set E)
  have hle := (eLpNorm_mono_measure f (Measure.restrict_mono_set mu hsub)).trans hU
  exact ⟨memLp_iff.2 (hle.trans_lt (ENNReal.sum_lt_top.2 fun i _ => (hf i).eLpNorm_lt_top)),
    hle⟩

/-- Gluing at the level of `Lᵖ`: an `Lᵖ` class on `Ω` agreeing with `f` exists, with norm at most
the sum of the norms of local classes agreeing with `f`. -/
private theorem exists_lp_glue [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    {V : ι → Opens E} (hcov : Omega ≤ ⨆ i, V i) {f : E → F}
    (g : ∀ i, Lp F p (mu.restrict (V i : Set E)))
    (hg : ∀ i, g i =ᵐ[mu.restrict (V i : Set E)] f) :
    ∃ G : Lp F p (mu.restrict (Omega : Set E)),
      G =ᵐ[mu.restrict (Omega : Set E)] f ∧ ‖G‖ ≤ ∑ i, ‖g i‖ := by
  have hf : ∀ i, MemLp f p (mu.restrict (V i : Set E)) :=
    fun i => (Lp.memLp (g i)).ae_eq (hg i)
  obtain ⟨hfΩ, hle⟩ := memLp_and_eLpNorm_le_of_cover hcov hf
  refine ⟨hfΩ.toLp f, hfΩ.coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp]
  have hgi : ∀ i, ‖g i‖ = (eLpNorm f p (mu.restrict (V i : Set E))).toReal :=
    fun i => by rw [Lp.norm_def, eLpNorm_congr_ae (hg i)]
  simp only [hgi]
  rw [← ENNReal.toReal_sum fun i _ => (hf i).eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => (hf i).eLpNorm_ne_top) hle

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure]

/-- A Sobolev function on `Ω` and one on an open `V ≤ Ω` whose values agree almost everywhere with
the same function are related by restriction. -/
private theorem restrictL_eq_of_value_ae_eq {V : Opens E} (hV : V ≤ Omega) (k : ℕ)
    {v : Wkp mu Omega p k} {w : Wkp mu V p k} {u : E → ℝ}
    (hv : value k v =ᵐ[mu.restrict (Omega : Set E)] u)
    (hw : value k w =ᵐ[mu.restrict (V : Set E)] u) :
    restrictL hV k v = w := by
  apply ext k
  apply Lp.ext
  refine (value_restrictL_ae hV k v).trans ?_
  exact Filter.EventuallyEq.trans
    (hv.filter_mono (ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hV))))
    hw.symm

omit [FiniteDimensional ℝ E] in
/-- The underlying `Lᵖ` jet of a first-order Sobolev function is its value-gradient pair. -/
private theorem coe_jet_ae_eq (z : W1p mu Omega p) :
    (z : Sobolev1JetLp mu Omega p) =ᵐ[mu.restrict (Omega : Set E)]
      fun x => WithLp.toLp 2 (W1p.value z x, W1p.gradient z x) := by
  filter_upwards [W1p.value_apply_ae z, W1p.gradient_apply_ae z] with x hv hg
  rw [hv, hg]
  rfl

/-- Order one of the gluing theorem, stated for `TauCeti.W1p`. -/
private theorem exists_glue_one [Fintype ι] {V : ι → Opens E} (hcov : Omega ≤ ⨆ i, V i)
    (w : ∀ i, W1p mu (V i) p) {u : E → ℝ}
    (hw : ∀ i, W1p.value (w i) =ᵐ[mu.restrict (V i : Set E)] u) :
    ∃ v : W1p mu Omega p,
      W1p.value v =ᵐ[mu.restrict (Omega : Set E)] u ∧ ‖v‖ ≤ ∑ i, ‖w i‖ := by
  have hloc : ∀ i, HasWeakFDerivOn mu (V i) u (fun x => innerSL ℝ (W1p.gradient (w i) x)) :=
    fun i => (W1p.hasWeakFDerivOn (w i)).congr_ae (hw i)
  obtain ⟨U, hU, hUi⟩ := exists_hasWeakFDerivOn_iSup V _ hloc
  let G : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (U x)
  have hGU : ∀ x, innerSL ℝ (G x) = U x := fun x => by
    ext y
    simp only [G, innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
  have hG : ∀ i, W1p.gradient (w i) =ᵐ[mu.restrict (V i : Set E)] G := fun i => by
    filter_upwards [hUi i] with x hx
    apply (innerSL_inj (𝕜 := ℝ)).1
    rw [hGU, hx]
  obtain ⟨u', hu', -⟩ := exists_lp_glue (p := p) hcov (fun i => W1p.value (w i)) hw
  obtain ⟨G', hG', -⟩ := exists_lp_glue (p := p) hcov (fun i => W1p.gradient (w i)) hG
  have hmk : HasWeakFDerivOn mu Omega u' (fun x => innerSL ℝ (G' x)) := by
    refine ((hU.mono hcov).congr_ae hu'.symm).congr_ae_deriv ?_
    filter_upwards [hG'] with x hx
    rw [hx, hGU]
  refine ⟨W1p.mk u' G' hmk, (W1p.value_mk u' G' hmk).symm ▸ hu', ?_⟩
  let J : E → WithLp 2 (ℝ × E) := fun x => WithLp.toLp 2 (u x, G x)
  obtain ⟨K, hK, hKn⟩ := exists_lp_glue (p := p) (f := J) hcov
    (fun i => (w i : Sobolev1JetLp mu (V i) p)) fun i => by
      filter_upwards [coe_jet_ae_eq (w i), hw i, hG i] with x h₀ h₁ h₂
      rw [h₀, h₁, h₂]
  have hvK : (W1p.mk u' G' hmk : Sobolev1JetLp mu Omega p) = K := by
    apply Lp.ext
    filter_upwards [coe_jet_ae_eq (W1p.mk u' G' hmk), hu', hG', hK] with x h₀ h₁ h₂ h₃
    rw [h₀, h₃, W1p.value_mk, W1p.gradient_mk, h₁, h₂]
  change ‖(W1p.mk u' G' hmk : Sobolev1JetLp mu Omega p)‖ ≤
    ∑ i, ‖(w i : Sobolev1JetLp mu (V i) p)‖
  rw [hvK]
  exact hKn

/-- The triangle inequality in the plane, in the form used for the order-`k + 2` norm: if
`X² = A² + B²` with `A ≤ ∑ aᵢ`, `B ≤ ∑ bᵢ`, and `nᵢ² = aᵢ² + bᵢ²`, then `X ≤ ∑ nᵢ`. -/
private theorem le_sum_of_sq_eq [Fintype ι] {X A B : ℝ} {a b n : ι → ℝ} (hX : 0 ≤ X)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hXAB : X ^ 2 = A ^ 2 + B ^ 2) (hAa : A ≤ ∑ i, a i)
    (hBb : B ≤ ∑ i, b i) (hn : ∀ i, 0 ≤ n i) (hnab : ∀ i, n i ^ 2 = a i ^ 2 + b i ^ 2) :
    X ≤ ∑ i, n i := by
  let z : ι → ℂ := fun i => ⟨a i, b i⟩
  have hz : ∀ i, ‖z i‖ = n i := fun i => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (hn i), Complex.sq_norm, Complex.normSq_apply, hnab i]
    ring
  have hsum : ‖∑ i, z i‖ ^ 2 = (∑ i, a i) ^ 2 + (∑ i, b i) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    ring
  have hXz : X ≤ ‖∑ i, z i‖ := by
    rw [← sq_le_sq₀ hX (norm_nonneg _), hXAB, hsum]
    gcongr
  calc X ≤ ‖∑ i, z i‖ := hXz
    _ ≤ ∑ i, ‖z i‖ := norm_sum_le _ _
    _ = ∑ i, n i := by simp only [hz]

/-- The gluing theorem with norm bound, by induction on the order. -/
private theorem exists_glue_aux [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) : ∀ (k : ℕ) (w : ∀ i, Wkp mu (V i) p k) {u : E → ℝ},
      (∀ i, value k (w i) =ᵐ[mu.restrict (V i : Set E)] u) →
      ∃ v : Wkp mu Omega p k,
        value k v =ᵐ[mu.restrict (Omega : Set E)] u ∧ ‖v‖ ≤ ∑ i, ‖w i‖
  | 0, w, _, hw => by
      simpa only [value_zero] using
        exists_lp_glue (p := p) hcov w fun i => by simpa only [value_zero] using hw i
  | 1, w, _, hw => by
      obtain ⟨v, hv, hvn⟩ := exists_glue_one hcov (fun i => (w i : W1p mu (V i) p))
        fun i => by simpa only [value_one (w i)] using hw i
      exact ⟨v, by simpa only [value_one v] using hv, hvn⟩
  | k + 2, w, u, hw => by
      have hw' : ∀ i, value (k + 1) (lowerOrder (k + 1) (w i)) =ᵐ[mu.restrict (V i : Set E)] u :=
        fun i => by simpa only [value_succ] using hw i
      obtain ⟨v', hv', hv'n⟩ :=
        exists_glue_aux hle hcov (k + 1) (fun i => lowerOrder (k + 1) (w i)) hw'
      have hgi : ∀ i, iteratedGradient k v' =ᵐ[mu.restrict (V i : Set E)]
          iteratedGradient k (lowerOrder (k + 1) (w i)) := fun i => by
        rw [← restrictL_eq_of_value_ae_eq (hle i) (k + 1) hv' (hw' i)]
        exact (iteratedGradient_restrictL_ae (hle i) k v').symm
      have hloc : ∀ i, HasWeakFDerivOn mu (V i) (iteratedGradient k v')
          (iteratedGradient (k + 1) (w i)) :=
        fun i => (hasWeakFDerivOn_iteratedGradient k (w i)).congr_ae (hgi i).symm
      obtain ⟨U, hU, hUi⟩ := exists_hasWeakFDerivOn_iSup V _ hloc
      obtain ⟨D, hD, hDn⟩ := exists_lp_glue (p := p)
        (f := fun x => (U x : IteratedGradient E (k + 1))) hcov
        (fun i => iteratedGradient (k + 1) (w i)) fun i => (hUi i).symm
      have hmk : HasWeakFDerivOn mu Omega (iteratedGradient k v') D :=
        (hU.mono hcov).congr_ae_deriv hD.symm
      refine ⟨mk k v' D hmk, by rw [value_mk]; exact hv', ?_⟩
      have heq := norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k
        (mk k v' D hmk)
      rw [lowerOrder_mk, iteratedGradient_mk] at heq
      exact le_sum_of_sq_eq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) heq hv'n hDn
        (fun i => norm_nonneg _) fun i =>
          norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k (w i)

/-- **Gluing Sobolev functions along a finite open cover.** Let the open sets `V i`, finitely
many, cover `Ω` and lie in `Ω`. If `w i ∈ W^{k,p}(V i)` has value `u` almost everywhere on `V i`
for every `i`, then some `v ∈ W^{k,p}(Ω)` has value `u` almost everywhere on `Ω`, restricts to
`w i` on each `V i`, and satisfies `‖v‖ ≤ ∑ᵢ ‖w i‖`. It is unique by
`TauCeti.Wkp.ext_of_restrictL_eq`. -/
theorem exists_glue [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (w : ∀ i, Wkp mu (V i) p k) {u : E → ℝ}
    (hw : ∀ i, value k (w i) =ᵐ[mu.restrict (V i : Set E)] u) :
    ∃ v : Wkp mu Omega p k, value k v =ᵐ[mu.restrict (Omega : Set E)] u ∧
      (∀ i, restrictL (hle i) k v = w i) ∧ ‖v‖ ≤ ∑ i, ‖w i‖ := by
  obtain ⟨v, hv, hvn⟩ := exists_glue_aux hle hcov k w hw
  exact ⟨v, hv, fun i => restrictL_eq_of_value_ae_eq (hle i) k hv (hw i), hvn⟩

/-- **Restrictions to a cover determine a Sobolev function.** Two elements of `W^{k,p}(Ω)` with
the same restrictions to the members of a countable open cover of `Ω` are equal. -/
theorem ext_of_restrictL_eq [Countable ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) {v v' : Wkp mu Omega p k}
    (h : ∀ i, restrictL (hle i) k v = restrictL (hle i) k v') : v = v' := by
  apply ext k
  apply Lp.ext
  refine ae_restrict_of_cover hcov fun i => ?_
  filter_upwards [value_restrictL_ae (hle i) k v, value_restrictL_ae (hle i) k v']
    with x h₁ h₂
  rw [← h₁, ← h₂, h i]

/-- **Gluing compatible Sobolev functions along a finite open cover.** Let the open sets `V i`,
finitely many, cover `Ω` and lie in `Ω`. If `w i ∈ W^{k,p}(V i)` and `w j` have the same
restriction to `V i ⊓ V j` for all `i` and `j`, then some `v ∈ W^{k,p}(Ω)` restricts to `w i` on
each `V i`, and `‖v‖ ≤ ∑ᵢ ‖w i‖`. -/
theorem exists_glue_of_restrictL_eq [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (w : ∀ i, Wkp mu (V i) p k)
    (hw : ∀ i j, restrictL (inf_le_left : V i ⊓ V j ≤ V i) k (w i) =
      restrictL (inf_le_right : V i ⊓ V j ≤ V j) k (w j)) :
    ∃ v : Wkp mu Omega p k, (∀ i, restrictL (hle i) k v = w i) ∧ ‖v‖ ≤ ∑ i, ‖w i‖ := by
  obtain ⟨u, hu⟩ : ∃ u : E → ℝ, ∀ i, value k (w i) =ᵐ[mu.restrict (V i : Set E)] u := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨0, fun i => isEmptyElim i⟩
    · obtain ⟨f, hf⟩ := exists_surjective_nat ι
      obtain ⟨u, hu⟩ := TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter
        (μ := mu) (L := fun n => (V (f n) : Set E)) (fun n => (V (f n)).isOpen.measurableSet)
        (a := fun n => (value k (w (f n)) : E → ℝ)) fun n m => by
          have hnm := congrArg (value k) (hw (f n) (f m))
          change ∀ᵐ x ∂mu.restrict ((V (f n) ⊓ V (f m) : Opens E) : Set E), _
          filter_upwards [value_restrictL_ae (inf_le_left : V (f n) ⊓ V (f m) ≤ V (f n)) k
              (w (f n)),
            value_restrictL_ae (inf_le_right : V (f n) ⊓ V (f m) ≤ V (f m)) k (w (f m))]
            with x h₁ h₂
          rw [← h₁, ← h₂, hnm]
      refine ⟨u, fun i => ?_⟩
      obtain ⟨n, rfl⟩ := hf i
      exact (hu n).symm
  obtain ⟨v, -, hv, hvn⟩ := exists_glue hle hcov k w hu
  exact ⟨v, hv, hvn⟩

end TauCeti.Wkp
