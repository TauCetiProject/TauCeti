/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.PowerSeries.Weierstrass.Strassmann
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Module.InfiniteSum
import TauCeti.Analysis.Normed.Ring.Finsupp
import TauCeti.Data.Finsupp.Weight
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Fintype.Option

/-!
# Evaluating module-valued restricted series

Let `E` be a complete ultrametric normed space over a normed field `K`, and let
`a : (σ →₀ ℕ) → E` be a coefficient family restricted at a polyradius `c`. At every point
`x : σ → K` of the closed polydisc `‖xᵢ‖ ≤ cᵢ`, the terms of

```text
a(x) = ∑ₜ xᵗ • a t,      xᵗ = ∏ᵢ xᵢ ^ tᵢ,
```

satisfy `‖xᵗ • a t‖ ≤ ‖a t‖ cᵗ → 0`, so the sum converges. This is the value at `x` of the
`E`-valued analytic function with coefficients `a`. It is additive and `K`-linear in `a`,
takes the convolution action `f • a` of a restricted scalar series `f` to `f(x) • a(x)`,
commutes with continuous linear maps applied coefficientwise, and is invariant under renaming the
variables.

The main result recovers the coefficients from the values. Suppose `K` is nontrivially normed and
ultrametric, and `E` carries a jointly injective family of continuous `K`-linear maps `φⱼ : E → Lⱼ`
into complete normed field extensions `Lⱼ` of `K`. If `a(x) = 0` for every `x` in a product of
infinite subsets `Sᵢ` of the discs `‖xᵢ‖ ≤ cᵢ`, then `a = 0`. In one variable, each `φⱼ ∘ a` is the
coefficient sequence of an `Lⱼ`-valued restricted series vanishing on an infinite subset of a closed
disc, which is zero by Strassmann's theorem (`TauCeti.PowerSeries.eq_zero_of_hasSum_pow_smul`).
Several variables are handled by splitting off one variable at a time: the coefficients of the
remaining variables, evaluated at fixed points, form a one-variable restricted family.

The functionals are a hypothesis: a general Banach space over `ℚ_p` need not admit such a family
into fields. The family exists, for instance, when `E` is itself a complete normed field extension
of `K`. Over `ℚ_p`, given such functionals, a restricted family at the unit polyradius is
determined by its values on `ℤ_pⁿ`
(`TauCeti.MvPowerSeries.IsRestrictedFamily.eq_zero_of_familyEval_padicInt_eq_zero`).
The sets `Sᵢ` must be infinite: over `𝔽_p((t))`, the nonzero polynomial `X ^ p - X` vanishes on
the finite set `𝔽_p`.

## Main definitions

* `TauCeti.MvPowerSeries.familyEval`: the value `∑ₜ xᵗ • a t` of a coefficient family at `x`.

## Main results

* `TauCeti.MvPowerSeries.IsRestrictedFamily.hasSum_familyEval`: in the closed polydisc, the value
  is the sum of the convergent series `∑ₜ xᵗ • a t`.
* `TauCeti.MvPowerSeries.norm_familyEval_le`: the value is bounded by any bound of the weighted
  coefficient norms.
* `TauCeti.MvPowerSeries.IsRestrictedFamily.map_familyEval`: evaluation commutes with continuous
  linear maps.
* `TauCeti.MvPowerSeries.IsRestrictedFamily.familyEval_convSMul`: evaluation takes the action of
  restricted scalar series by convolution to multiplication by their values.
* `TauCeti.MvPowerSeries.IsRestrictedFamily.eq_zero_of_familyEval_eq_zero`: a restricted family
  vanishing on a product of infinite subsets of the closed polydisc is zero, given a jointly
  injective family of functionals into complete field extensions.
* `TauCeti.MvPowerSeries.IsRestrictedFamily.eq_zero_of_familyEval_padicInt_eq_zero`: its
  specialisation to unit-radius series over `ℚ_p` evaluated on `ℤ_pⁿ`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace TauCeti.MvPowerSeries

open Filter
open scoped Topology

variable {σ K E F : Type*}

section Eval

variable [NormedField K] [NormedAddCommGroup E] [NormedSpace K E] {c : σ → ℝ}

/-- The value `∑ₜ xᵗ • a t` at a point `x : σ → K` of the power series with coefficient family
`a`, where `xᵗ = ∏ᵢ xᵢ ^ tᵢ`. It is zero when the series is not summable. When `E` is complete
and ultrametric, the series of a family restricted at `c` converges at every `x` with `‖xᵢ‖ ≤ cᵢ`
(`TauCeti.MvPowerSeries.IsRestrictedFamily.hasSum_familyEval`). -/
noncomputable def familyEval (x : σ → K) (a : (σ →₀ ℕ) → E) : E :=
  ∑' t, t.prod (x · ^ ·) • a t

theorem familyEval_def (x : σ → K) (a : (σ →₀ ℕ) → E) :
    familyEval x a = ∑' t, t.prod (x · ^ ·) • a t :=
  (rfl)

@[simp]
theorem familyEval_zero (x : σ → K) : familyEval x (0 : (σ →₀ ℕ) → E) = 0 := by
  simp [familyEval_def]

/-- A family with a single nonzero coefficient `e` at `t` takes the value `xᵗ • e`. -/
@[simp]
theorem familyEval_single [DecidableEq σ] (x : σ → K) (t : σ →₀ ℕ) (e : E) :
    familyEval x (Pi.single t e) = t.prod (x · ^ ·) • e := by
  rw [familyEval_def, tsum_eq_single t fun s hs ↦ by simp [hs], Pi.single_eq_same]

/-- Evaluation is invariant under renaming the variables. -/
theorem familyEval_comp_equivMapDomain {τ : Type*} (e : σ ≃ τ) (x : τ → K)
    (a : (τ →₀ ℕ) → E) :
    familyEval (x ∘ e) (a ∘ Finsupp.equivMapDomain e) = familyEval x a := by
  rw [familyEval_def, familyEval_def, ← (Finsupp.equivCongrLeft e).tsum_eq]
  simp [Finsupp.prod_equivMapDomain]

variable [IsUltrametricDist E]

/-- On the closed polydisc of polyradius `c`, the value of a family is bounded by every bound of
its weighted coefficient norms `‖a t‖ cᵗ`. -/
theorem norm_familyEval_le {a : (σ →₀ ℕ) → E} {x : σ → K} (hx : ∀ i, ‖x i‖ ≤ c i) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ t, ‖a t‖ * t.prod (c · ^ ·) ≤ C) : ‖familyEval x a‖ ≤ C :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun t ↦ by
    rw [norm_smul, mul_comm]
    exact (mul_le_mul_of_nonneg_left (t.norm_prod_pow_le hx) (norm_nonneg _)).trans (h t)

variable [CompleteSpace E]

/-- A family restricted at `c` is summable at every point of the closed polydisc of polyradius
`c`, with sum its value there. -/
theorem IsRestrictedFamily.hasSum_familyEval {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a)
    {x : σ → K} (hx : ∀ i, ‖x i‖ ≤ c i) :
    HasSum (fun t ↦ t.prod (x · ^ ·) • a t) (familyEval x a) := by
  rw [familyEval_def]
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (squeeze_zero_norm (fun t ↦ ?_) (isRestrictedFamily_iff.mp ha))).hasSum
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (t.norm_prod_pow_le hx) (norm_nonneg _)

/-- On the closed polydisc, evaluation of restricted families is additive. -/
theorem IsRestrictedFamily.familyEval_add {a b : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a)
    (hb : IsRestrictedFamily c b) {x : σ → K} (hx : ∀ i, ‖x i‖ ≤ c i) :
    familyEval x (a + b) = familyEval x a + familyEval x b := by
  rw [familyEval_def]
  refine HasSum.tsum_eq ?_
  simpa only [Pi.add_apply, smul_add] using
    (ha.hasSum_familyEval hx).add (hb.hasSum_familyEval hx)

/-- On the closed polydisc, evaluation of restricted families commutes with scalars. -/
theorem IsRestrictedFamily.familyEval_smul {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a)
    {x : σ → K} (hx : ∀ i, ‖x i‖ ≤ c i) (r : K) :
    familyEval x (r • a) = r • familyEval x a := by
  rw [familyEval_def]
  refine HasSum.tsum_eq ?_
  simpa only [Pi.smul_apply, smul_comm r] using (ha.hasSum_familyEval hx).const_smul r

/-- Evaluation of a restricted family commutes with a continuous linear map applied to the
coefficients. -/
theorem IsRestrictedFamily.map_familyEval [NormedAddCommGroup F] [NormedSpace K F]
    (φ : E →L[K] F) {a : (σ →₀ ℕ) → E} (ha : IsRestrictedFamily c a) {x : σ → K}
    (hx : ∀ i, ‖x i‖ ≤ c i) :
    φ (familyEval x a) = familyEval x (φ ∘ a) := by
  rw [familyEval_def (a := φ ∘ a)]
  refine (HasSum.tsum_eq ?_).symm
  simpa only [Function.comp_def, map_smul] using (ha.hasSum_familyEval hx).map φ φ.continuous

/-- On the closed polydisc, evaluation turns the convolution action of a restricted scalar series
`f` into multiplication by the value of `f`: `(f • a)(x) = f(x) • a(x)`. -/
theorem IsRestrictedFamily.familyEval_convSMul [IsUltrametricDist K] [CompleteSpace K]
    {f : MvPowerSeries σ K} (hf : MvPowerSeries.IsRestricted c f) {a : (σ →₀ ℕ) → E}
    (ha : IsRestrictedFamily c a) {x : σ → K} (hx : ∀ i, ‖x i‖ ≤ c i) :
    familyEval x (MvPowerSeries.convSMul f a) =
      familyEval x (fun t ↦ MvPowerSeries.coeff t f) • familyEval x a := by
  classical
  rw [familyEval_def (a := MvPowerSeries.convSMul f a)]
  refine HasSum.tsum_eq ?_
  convert ((((MvPowerSeries.isRestrictedFamily_coeff_iff f).mpr hf).hasSum_familyEval
    hx).sum_smul_antidiagonal_of_nonarchimedean (ha.hasSum_familyEval hx)) using 1
  funext t
  rw [MvPowerSeries.convSMul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [← Finset.mem_antidiagonal.mp hp,
    Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _]
  simp only [smul_eq_mul, mul_smul, smul_comm (p.2.prod (x · ^ ·))]

end Eval

section Injective

variable [NontriviallyNormedField K] [IsUltrametricDist K] [NormedAddCommGroup E] [NormedSpace K E]
  [IsUltrametricDist E] [CompleteSpace E] {ι : Type*} {L : ι → Type*}
  [∀ j, NormedField (L j)] [∀ j, NormedAlgebra K (L j)] [∀ j, CompleteSpace (L j)]

/-- The statement proved by induction on the variables, for a fixed coefficient space. -/
private def VanishingPrinciple (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (σ : Type*) : Prop :=
  ∀ (c : σ → ℝ) (a : (σ →₀ ℕ) → E) (S : σ → Set K), IsRestrictedFamily c a →
    (∀ i, (S i).Infinite) → (∀ i, ∀ x ∈ S i, ‖x‖ ≤ c i) →
    (∀ x ∈ Set.univ.pi S, familyEval x a = 0) → a = 0

omit [IsUltrametricDist K] [IsUltrametricDist E] [CompleteSpace E] in
private theorem vanishingPrinciple_of_equiv {α β : Type*} (e : α ≃ β)
    (h : VanishingPrinciple (K := K) E α) : VanishingPrinciple (K := K) E β := by
  intro c a S ha hS hSc hzero
  have h0 := h (c ∘ e) (a ∘ Finsupp.equivMapDomain e) (S ∘ e) ?_ (fun i ↦ hS (e i))
    (fun i ↦ hSc (e i)) ?_
  · funext t
    simpa only [Function.comp_apply, ← Finsupp.equivCongrLeft_apply, Equiv.apply_symm_apply,
      Pi.zero_apply] using congrFun h0 ((Finsupp.equivCongrLeft e).symm t)
  · refine isRestrictedFamily_iff.mpr <| ((isRestrictedFamily_iff.mp ha).comp
      (Finsupp.equivCongrLeft e).injective.tendsto_cofinite).congr fun t ↦ ?_
    simp [Finsupp.prod_equivMapDomain]
  · intro x hx
    have hx' := familyEval_comp_equivMapDomain e (x ∘ e.symm) a
    rw [Function.comp_assoc, e.symm_comp_self, Function.comp_id] at hx'
    rw [hx']
    exact hzero _ fun i _ ↦ by simpa using hx (e.symm i) (Set.mem_univ _)

omit [IsUltrametricDist K] [IsUltrametricDist E] [CompleteSpace E] in
private theorem vanishingPrinciple_pempty : VanishingPrinciple (K := K) E PEmpty := by
  intro c a S _ _ _ hzero
  have h0 := hzero isEmptyElim fun i ↦ isEmptyElim i
  rw [familyEval_def, tsum_eq_single 0 fun t ht ↦ absurd (Subsingleton.elim t 0) ht,
    Finsupp.prod_zero_index, one_smul] at h0
  funext t
  rwa [Subsingleton.elim t 0]

/-- Splitting off the variable `none`: if every slice of a restricted family `a` in the remaining
variables vanishes on a product of infinite sets, so does `a`. The one-variable sequences
`k ↦ a_k(y)` of values of the slices are restricted, and their power series are values of `a`. -/
private theorem vanishingPrinciple_option (φ : ∀ j, E →L[K] L j)
    (hφ : ∀ e, (∀ j, φ j e = 0) → e = 0) {α : Type*} (h : VanishingPrinciple (K := K) E α) :
    VanishingPrinciple (K := K) E (Option α) := by
  intro c a S ha hS hSc hzero
  have hc := (hS none).nontrivial.pos_of_forall_norm_le (hSc none)
  -- the slice of `a` with exponent `k` in the variable `none`
  set a' : ℕ → (α →₀ ℕ) → E := fun k t ↦ a (t.optionElim k) with ha'_def
  have hweight (k : ℕ) (t : α →₀ ℕ) : ‖a' k t‖ * t.prod (fun i n ↦ c (some i) ^ n) =
      (c none ^ k)⁻¹ * (‖a (t.optionElim k)‖ * (t.optionElim k).prod (c · ^ ·)) := by
    rw [Finsupp.prod_pow_optionElim, ha'_def]
    field_simp
  have hslice (k : ℕ) : IsRestrictedFamily (c ∘ some) (a' k) := ha.comp_optionElim hc k
  -- for fixed `y`, the values of the slices form a restricted one-variable family
  have hrestr (y : α → K) (hy : ∀ i, ‖y i‖ ≤ c (some i)) :
      Tendsto (fun k ↦ ‖familyEval y (a' k)‖ * c none ^ k) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun b hb ↦ .of_forall fun k ↦ hb.trans_le (by positivity),
      fun ε hε ↦ ?_⟩
    have hfin := eventually_cofinite.mp
      ((isRestrictedFamily_iff.mp ha).eventually (gt_mem_nhds (half_pos hε)))
    obtain ⟨N, hN⟩ := (hfin.image fun t ↦ t none).bddAbove
    filter_upwards [eventually_gt_atTop N] with k hk
    have hpow : 0 < c none ^ k := pow_pos hc k
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    rw [← le_div_iff₀ hpow]
    refine norm_familyEval_le hy (by positivity) fun t ↦ ?_
    rw [hweight, inv_mul_le_iff₀ hpow, mul_div_cancel₀ _ hpow.ne']
    by_contra hlt
    exact hk.not_ge (hN ⟨_, (not_lt.mpr (le_of_not_ge hlt)), Finsupp.optionElim_apply_none k t⟩)
  -- the power series of these values are values of `a`
  have hsum (y : α → K) (hy : ∀ i, y i ∈ S (some i)) (x : K) (hx : x ∈ S none) :
      HasSum (fun k ↦ x ^ k • familyEval y (a' k)) 0 := by
    have hpt : Option.elim' x y ∈ Set.univ.pi S := by
      rintro (_ | i) -; exacts [hx, hy i]
    have hxc : ∀ i, ‖Option.elim' x y i‖ ≤ c i := by
      rintro (_ | i); exacts [hSc none x hx, hSc (some i) (y i) (hy i)]
    have htot := hzero _ hpt ▸ ha.hasSum_familyEval hxc
    rw [← Finsupp.optionEquiv.symm.hasSum_iff] at htot
    refine htot.prod_fiberwise fun k ↦ ?_
    -- `Finsupp.optionElim` is defined as the inverse of `Finsupp.optionEquiv`
    have he (t : α →₀ ℕ) : Finsupp.optionEquiv.symm (k, t) = t.optionElim k := rfl
    simpa only [Function.comp_def, he, Finsupp.prod_pow_optionElim, mul_smul, ha'_def,
      Option.elim'_none, Option.elim'_some] using
      ((hslice k).hasSum_familyEval fun i ↦ hxc (some i)).const_smul (x ^ k)
  have hzero' (k : ℕ) : a' k = 0 := by
    refine h (c ∘ some) (a' k) (S ∘ some) (hslice k) (fun i ↦ hS (some i))
      (fun i ↦ hSc (some i)) fun y hy ↦ ?_
    have hy' : ∀ i, y i ∈ S (some i) := fun i ↦ hy i (Set.mem_univ _)
    exact congrFun (TauCeti.PowerSeries.eq_zero_of_hasSum_pow_smul φ hφ
      (hrestr y fun i ↦ hSc (some i) _ (hy' i)) (hS none) (hSc none) (hsum y hy')) k
  funext t
  rw [Pi.zero_apply, ← Finsupp.optionElim_some t]
  exact congrFun (hzero' (t none)) t.some

/-- **Coefficient recovery for module-valued restricted series.** Let `E` be a complete
ultrametric normed space over an ultrametric normed field `K`, with a jointly injective family of
continuous linear maps `φⱼ : E → Lⱼ` into complete normed field extensions of `K`. A family
restricted at `c`, in finitely many variables, whose value vanishes at every point of a product
of infinite subsets `Sᵢ` of the discs `‖xᵢ‖ ≤ cᵢ`, is zero. -/
theorem IsRestrictedFamily.eq_zero_of_familyEval_eq_zero [Finite σ] (φ : ∀ j, E →L[K] L j)
    (hφ : ∀ e, (∀ j, φ j e = 0) → e = 0) {c : σ → ℝ} {a : (σ →₀ ℕ) → E}
    (ha : IsRestrictedFamily c a) {S : σ → Set K} (hS : ∀ i, (S i).Infinite)
    (hSc : ∀ i, ∀ x ∈ S i, ‖x‖ ≤ c i) (h : ∀ x ∈ Set.univ.pi S, familyEval x a = 0) :
    a = 0 :=
  Finite.induction_empty_option (P := VanishingPrinciple (K := K) E)
    vanishingPrinciple_of_equiv vanishingPrinciple_pempty
    (vanishingPrinciple_option φ hφ) σ c a S ha hS hSc h

/-- **Coefficient recovery on `ℤ_pⁿ`.** Let `E` be an ultrametric Banach space over `ℚ_p` with a
jointly injective family of continuous linear maps into complete normed field extensions of `ℚ_p`.
A unit-radius restricted family in finitely many variables with values in `E`, vanishing at every
point of `ℤ_pⁿ`, is zero. -/
theorem IsRestrictedFamily.eq_zero_of_familyEval_padicInt_eq_zero {p : ℕ} [Fact p.Prime]
    [Finite σ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [IsUltrametricDist E]
    [CompleteSpace E] {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)]
    [∀ j, NormedAlgebra ℚ_[p] (L j)] [∀ j, CompleteSpace (L j)] (φ : ∀ j, E →L[ℚ_[p]] L j)
    (hφ : ∀ e, (∀ j, φ j e = 0) → e = 0) {a : (σ →₀ ℕ) → E}
    (ha : IsRestrictedFamily (fun _ ↦ 1) a)
    (h : ∀ x : σ → ℤ_[p], familyEval (fun i ↦ (x i : ℚ_[p])) a = 0) : a = 0 := by
  have : Infinite ℤ_[p] := .of_injective (fun n : ℕ ↦ (n : ℤ_[p])) Nat.cast_injective
  refine ha.eq_zero_of_familyEval_eq_zero φ hφ (S := fun _ ↦ Set.range ((↑) : ℤ_[p] → ℚ_[p]))
    (fun _ ↦ Set.infinite_range_of_injective (α := ℤ_[p]) fun _ _ ↦ PadicInt.ext) ?_ fun x hx ↦ ?_
  · rintro - - ⟨z, rfl⟩
    exact PadicInt.norm_le_one z
  · choose z hz using fun i ↦ hx i (Set.mem_univ i)
    simpa [hz] using h z

end Injective

end TauCeti.MvPowerSeries
