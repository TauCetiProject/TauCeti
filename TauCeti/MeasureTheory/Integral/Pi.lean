/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.HasLaw
import TauCeti.MeasureTheory.Function.Lp.Iterated

/-!
# Integrals over finite product measures

This file collects integration results for finite product measures. In addition to the lower
integral product formula, it gives a Fubini identity obtained by refreshing two coordinates with
independent samples.

The `ℝ≥0∞`-valued companion of Mathlib's `MeasureTheory.integral_fintype_prod_eq_prod`: over
`MeasureTheory.Measure.pi`, the lower integral of a product `∏ i, f i (x i)` of functions each
depending on a single coordinate is the product of the one-dimensional lower integrals.

Mathlib proves the Bochner version (and the matching integrability statements) but not this one,
even though the `ℝ≥0∞` version needs no integrability hypothesis at all, since every factor is
automatically "integrable" in the lower-integral sense. The proof is the same induction as
Mathlib's: reduce a `Fin (n + 1)`-indexed product to a binary product measure along
`MeasureTheory.measurePreserving_piFinSuccAbove`, split it with
`MeasureTheory.lintegral_prod_mul`, and transfer an arbitrary `Fintype` index to `Fin` along
`MeasureTheory.measurePreserving_piCongrLeft`.

## Main statements

* `TauCeti.lintegral_fintype_prod_eq_prod`: the product formula, for measurable factors.
* `TauCeti.lintegral_fintype_prod_eq_prod₀`: the same for almost everywhere measurable factors.
* `TauCeti.lintegral_pi_update`: refreshing a coordinate preserves lower integrals.
* `TauCeti.ae_memLp_two_pi_update`: almost every refreshed coordinate slice is in L².
* `TauCeti.integral_pi_eq_integral_integral_update`: the two-coordinate Fubini
  identity.
* `TauCeti.integral_pi_succ`: splitting off the zeroth coordinate of a finite product measure.
* `TauCeti.integral_integral_update_pi`: the one-coordinate Fubini identity.
* `TauCeti.integral_pi_sum_mul`: Fubini over a sum of index types, for a product of a function of
  each block of coordinates.
* `TauCeti.setIntegral_prod_le_exp_mul_pow`: the exponential-moment (Chernoff) bound for the
  integral of `∏ i, g (x i)` over the half-space `∑ i, x i ≤ s`, by the `card ι`-th power of the
  one-dimensional integral of `exp (-(l * x)) * g x`.
-/

public section

open Function MeasureTheory MeasureTheory.Measure

open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]

/-- Refreshing one coordinate with an independent sample preserves the lower integral over a
finite product of probability measures. -/
theorem lintegral_pi_update (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (∀ i, α i) → ℝ≥0∞} (hg : Measurable g) (i : ι) :
    (∫⁻ x, ∫⁻ y, g (Function.update x i y) ∂μ i ∂Measure.pi μ) =
      ∫⁻ x, g x ∂Measure.pi μ := by
  have hm : Measurable (fun q : (∀ j, α j) × α i ↦ g (Function.update q.1 i q.2)) :=
    hg.comp measurable_update'
  apply lintegral_eq_of_lmarginal_eq (μ := μ) {i} hm.lintegral_prod_right hg
  simp only [lmarginal_singleton]
  funext x
  simp only [Function.update_idem]
  simp

/-- For an L² function on a finite product of probability spaces, almost every one-coordinate
slice obtained by an independent refresh is again in L². -/
theorem ae_memLp_two_pi_update (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (∀ i, α i) → ℝ} (hg : Measurable g) (hL : MemLp g 2 (Measure.pi μ)) (i : ι) :
    ∀ᵐ x ∂Measure.pi μ, MemLp (fun y ↦ g (Function.update x i y)) 2 (μ i) := by
  have hm : Measurable (fun q : (∀ j, α j) × α i ↦ g (Function.update q.1 i q.2)) :=
    hg.comp measurable_update'
  have hupdate : MemLp (fun q : (∀ j, α j) × α i ↦ g (Function.update q.1 i q.2))
      2 ((Measure.pi μ).prod (μ i)) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)
      hm.aestronglyMeasurable).mpr
    simp only [ENNReal.toReal_ofNat]
    rw [lintegral_prod _ (hm.enorm.pow_const (2 : ℝ)).aemeasurable,
      lintegral_pi_update μ (hg.enorm.pow_const (2 : ℝ)) i]
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)
      hg.aestronglyMeasurable).mp hL
  exact hupdate.ae_memLp_prod_right

/-- **Fubini after a two-coordinate refresh.** An integral against a finite product of sigma-finite
measures is an outer integral over the assignment and an inner integral over a fresh independent
pair placed at the two distinct probability coordinates `a` and `b`. -/
theorem integral_pi_eq_integral_integral_update {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] {a b : ι}
    [IsProbabilityMeasure (μ a)] [IsProbabilityMeasure (μ b)] (hab : a ≠ b)
    {f : (∀ i, α i) → E} (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂(Measure.pi μ) =
      ∫ z, (∫ p : α a × α b, f (update (update z a p.1) b p.2) ∂(μ a).prod (μ b))
        ∂(Measure.pi μ) := by
  set g : ((∀ i, α i) × α a × α b) → (∀ i, α i) :=
    fun w => update (update w.1 a w.2.1) b w.2.2
  have hmp := measurePreserving_update_update μ hab
  have hcomp : Integrable (fun w => f (g w)) ((Measure.pi μ).prod ((μ a).prod (μ b))) :=
    hmp.integrable_comp_of_integrable hf
  have hae : AEStronglyMeasurable f
      (Measure.map g ((Measure.pi μ).prod ((μ a).prod (μ b)))) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  calc ∫ x, f x ∂(Measure.pi μ)
      = ∫ x, f x ∂(Measure.map g ((Measure.pi μ).prod ((μ a).prod (μ b)))) := by
        rw [hmp.map_eq]
    _ = ∫ w, f (g w) ∂((Measure.pi μ).prod ((μ a).prod (μ b))) :=
        integral_map hmp.measurable.aemeasurable hae
    _ = ∫ z, (∫ p : α a × α b, f (update (update z a p.1) b p.2) ∂(μ a).prod (μ b))
          ∂(Measure.pi μ) := integral_prod _ hcomp

/-- Averaging an integrable function over a freshly resampled probability coordinate preserves its
expectation under `Measure.pi`. -/
theorem integral_integral_update_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (i : ι) [IsProbabilityMeasure (μ i)]
    {h : (∀ j, α j) → E} (hh : Integrable h (Measure.pi μ)) :
    ∫ x, ∫ y, h (Function.update x i y) ∂μ i ∂Measure.pi μ = ∫ x, h x ∂Measure.pi μ := by
  have hmp := measurePreserving_update_prod_pi μ i
  have hint := hmp.integrable_comp_of_integrable hh
  refine (integral_prod _ hint).symm.trans ?_
  exact hmp.hasLaw.integral_comp hh.aestronglyMeasurable

/-- The product formula for a `Fin n`-indexed product measure, by induction on `n`. -/
private theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {α : Fin n → Type*}
    {mα : ∀ i, MeasurableSpace (α i)} {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]
    {f : ∀ i, α i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- Peel off the zeroth coordinate: `Measure.pi μ` becomes a binary product measure.
      have hprodm : Measurable fun z : ∀ j : Fin n, α ((0 : Fin (n + 1)).succAbove j) =>
          ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z j) :=
        Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)
      calc ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ
          = ∫⁻ x : ∀ i, α i, f 0 ((MeasurableEquiv.piFinSuccAbove α 0 x).1)
              * ∏ j, f ((0 : Fin (n + 1)).succAbove j)
                  ((MeasurableEquiv.piFinSuccAbove α 0 x).2 j) ∂Measure.pi μ :=
            lintegral_congr fun x => Fin.prod_univ_succAbove (fun i => f i (x i)) 0
        _ = ∫⁻ z, f 0 z.1 * ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z.2 j)
              ∂(μ 0).prod (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j)) :=
            ((measurePreserving_piFinSuccAbove μ 0).lintegral_map_equiv
              (fun z : α 0 × ∀ j : Fin n, α ((0 : Fin (n + 1)).succAbove j) =>
                f 0 z.1 * ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z.2 j))
              (MeasurableEquiv.piFinSuccAbove α 0)).symm
        _ = (∫⁻ y, f 0 y ∂μ 0)
              * ∫⁻ z, ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z j)
                  ∂Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j) :=
            lintegral_prod_mul (hf 0).aemeasurable hprodm.aemeasurable
        _ = (∫⁻ y, f 0 y ∂μ 0) * ∏ j, ∫⁻ y, f ((0 : Fin (n + 1)).succAbove j) y
              ∂μ ((0 : Fin (n + 1)).succAbove j) := by rw [ih fun j => hf _]
        _ = ∏ i, ∫⁻ y, f i y ∂μ i :=
            (Fin.prod_univ_succAbove (fun i => ∫⁻ y, f i y ∂μ i) 0).symm

/-- **The product formula for lower integrals over a finite product measure.** The lower integral
of `∏ i, f i (x i)` against `MeasureTheory.Measure.pi μ` is `∏ i, ∫⁻ y, f i y ∂μ i`.

This is the `ℝ≥0∞` analogue of `MeasureTheory.integral_fintype_prod_eq_prod`; unlike the Bochner
statement it needs no integrability of the factors. See
`TauCeti.lintegral_fintype_prod_eq_prod₀` for the almost everywhere measurable version, which is
obtained from this one by passing to measurable representatives. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι]
    {α : ι → Type*} {mα : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {f : ∀ i, α i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  -- Transfer the index type to `Fin (card ι)` and apply the `Fin`-indexed statement.
  let e := (Fintype.equivFin ι).symm
  calc ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∫⁻ y : ∀ j, α (e j), ∏ i, f i (MeasurableEquiv.piCongrLeft α e y i)
          ∂Measure.pi fun j => μ (e j) :=
        (measurePreserving_piCongrLeft μ e).lintegral_map_equiv _
          (MeasurableEquiv.piCongrLeft α e)
    _ = ∫⁻ y : ∀ j, α (e j), ∏ j, f (e j) (y j) ∂Measure.pi fun j => μ (e j) := by
        refine lintegral_congr fun y => ?_
        rw [← e.prod_comp fun i => f i (MeasurableEquiv.piCongrLeft α e y i)]
        exact Finset.prod_congr rfl fun j _ => by
          simp [MeasurableEquiv.piCongrLeft_apply_apply]
    _ = ∏ j, ∫⁻ z, f (e j) z ∂μ (e j) := lintegral_fin_nat_prod_eq_prod fun j => hf _
    _ = ∏ i, ∫⁻ y, f i y ∂μ i := e.prod_comp fun i => ∫⁻ y, f i y ∂μ i

/-- **The product formula for lower integrals over a finite product measure**, for almost
everywhere measurable factors; see `TauCeti.lintegral_fintype_prod_eq_prod` for the measurable
version. -/
theorem lintegral_fintype_prod_eq_prod₀ {ι : Type*} [Fintype ι] {α : ι → Type*}
    {mα : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    {f : ∀ i, α i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  -- Each factor may be replaced by a measurable representative: a `μ i`-null exceptional set
  -- pulls back to a `Measure.pi μ`-null one along the `i`-th coordinate.
  have hae : ∀ᵐ x : ∀ i, α i ∂Measure.pi μ, ∀ i, f i (x i) = (hf i).mk (f i) (x i) :=
    Filter.eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (hf i).ae_eq_mk
  rw [lintegral_congr_ae (hae.mono fun x hx => Finset.prod_congr rfl fun i _ => hx i),
    lintegral_fintype_prod_eq_prod μ fun i => (hf i).measurable_mk]
  exact Finset.prod_congr rfl fun i _ => (lintegral_congr_ae (hf i).ae_eq_mk).symm

/-- **Fubini over a sum of index types.** Over a finite product measure indexed by `ι ⊕ ι'`, the
integral of a function of the `ι` coordinates times a function of the `ι'` coordinates is the
product of the two integrals. -/
theorem integral_pi_sum_mul {ι ι' : Type*} [Fintype ι] [Fintype ι'] {α : ι ⊕ ι' → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    {L : Type*} [RCLike L] (f : (∀ i, α (.inl i)) → L) (g : (∀ i, α (.inr i)) → L) :
    ∫ x, f (fun i => x (.inl i)) * g (fun i => x (.inr i)) ∂Measure.pi μ =
      (∫ y, f y ∂Measure.pi fun i => μ (.inl i)) * ∫ y, g y ∂Measure.pi fun i => μ (.inr i) := by
  rw [← (measurePreserving_sumPiEquivProdPi_symm μ).integral_comp']
  exact integral_prod_mul f g

/-- **Exponential-moment bound over a half-space.** For a nonnegative weight `g` on `ℝ` and
`0 ≤ l` such that `exp (-(l * x)) * g x` is integrable, the integral of `∏ i, g (x i)` over the
half-space `∑ i, x i ≤ s` of `ι → ℝ` is at most
`exp (l * s) * (∫ x, exp (-(l * x)) * g x) ^ card ι`. No integrability of `g` itself is
assumed. -/
theorem setIntegral_prod_le_exp_mul_pow {ι : Type*} [Fintype ι] {g : ℝ → ℝ}
    (hg : ∀ x, 0 ≤ g x) {l : ℝ} (hl : 0 ≤ l)
    (hint : Integrable fun x ↦ Real.exp (-(l * x)) * g x) (s : ℝ) :
    ∫ x in {x : ι → ℝ | ∑ i, x i ≤ s}, ∏ i, g (x i) ≤
      Real.exp (l * s) * (∫ x, Real.exp (-(l * x)) * g x) ^ Fintype.card ι := by
  -- On the half-space `1 ≤ exp (l * (s - ∑ i, x i))`. After multiplying by this factor the
  -- integrand `F` splits into a product over the coordinates, whose integral over all of
  -- `ι → ℝ` is the `card ι`-th power of a one-dimensional integral.
  set F : (ι → ℝ) → ℝ := fun x ↦ Real.exp (l * s) * ∏ i, (Real.exp (-(l * x i)) * g (x i))
  have hF : Integrable F := (Integrable.fintype_prod fun _ ↦ hint).const_mul _
  have hF₀ : ∀ x, 0 ≤ F x := fun x ↦
    mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ ↦ mul_nonneg (Real.exp_pos _).le
      (hg _))
  have hS : MeasurableSet {x : ι → ℝ | ∑ i, x i ≤ s} :=
    measurableSet_le (by fun_prop) measurable_const
  calc ∫ x in {x : ι → ℝ | ∑ i, x i ≤ s}, ∏ i, g (x i)
      ≤ ∫ x in {x : ι → ℝ | ∑ i, x i ≤ s}, F x := by
        refine integral_mono_of_nonneg (.of_forall fun x ↦ Finset.prod_nonneg fun i _ ↦ hg _)
          hF.integrableOn (ae_restrict_of_forall_mem hS fun x (hx : ∑ i, x i ≤ s) ↦ ?_)
        -- `F x = exp (l * (s - ∑ i, x i)) * ∏ i, g (x i)`, and the exponent is nonnegative.
        simp only [F, Finset.prod_mul_distrib, ← Real.exp_sum, ← mul_assoc, ← Real.exp_add]
        refine le_mul_of_one_le_left (Finset.prod_nonneg fun i _ ↦ hg _) (Real.one_le_exp ?_)
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
        nlinarith
    _ ≤ ∫ x, F x := setIntegral_le_integral hF (.of_forall hF₀)
    _ = _ := by
      rw [integral_const_mul,
        integral_fintype_prod_volume_eq_pow fun x ↦ Real.exp (-(l * x)) * g x]

/-- Integrating over a finite product measure on `Fin (n + 1)` splits off the zeroth coordinate.
The remaining coordinates retain their dependent types, and the codomain of `f` can be any real
normed space. -/
theorem integral_pi_succ {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (∀ i, α i) → E) :
    ∫ x, f x ∂Measure.pi μ =
      ∫ p : α 0 × (∀ i : Fin n, α (Fin.succAbove (0 : Fin (n + 1)) i)),
        f ((MeasurableEquiv.piFinSuccAbove α 0).symm p)
          ∂((μ 0).prod (Measure.pi fun i ↦ μ (Fin.succAbove (0 : Fin (n + 1)) i))) := by
  rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']

end TauCeti
