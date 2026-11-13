/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.W1p.ChainRule
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Composition with a smooth function in `W^{k+1,p}`

Let `Ω` have compact closure inside an open set `U`, let `Φ : ℝ → ℝ` be `Cᵏ⁺¹` and let `w` be `Cᵏ`
on `U`. If `w` also lies in `W^{k+1,p}(Ω)`, `1 ≤ p < ∞`, then so does `Φ ∘ w`
(`TauCeti.Wkp.exists_value_ae_eq_comp_of_contDiffOn`): Sobolev regularity one order above the
classical regularity of `w` passes to `Φ ∘ w`.

This is the composition step of a regularity bootstrap for a semilinear elliptic equation
`-∂ᵢ(aⁱʲ ∂ⱼu) = A(x) Φ(u) + C(x)`, where interior regularity gains two Sobolev orders and the
Sobolev embedding converts them back into classical derivatives.

## The argument

The first-order input is the chain rule for an essentially bounded `u ∈ W^{1,p}(Ω)` and a `C¹`
function `Φ` with no bound on `Φ'` (`TauCeti.W1p.hasWeakFDerivOn_comp_of_ae_abs_le`): on the
essential range of `u`, `Φ` agrees with a compactly supported `C¹` function, to which the chain rule
`TauCeti.W1p.hasWeakFDerivOn_comp` applies. Since `w` is bounded on `closure Ω`, this gives the weak
derivative `∂ᵥ(Φ ∘ w) = Φ'(w) ∂ᵥw` in every direction `v`.

The composition theorem is then proved by induction on `k`. By the description of the Sobolev
scale through first derivatives (`TauCeti.Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn`), it
remains to show `Φ'(w) ∂ᵥw ∈ W^{k,p}(Ω)`. For `k = 0` this holds because `Φ'(w)` is bounded on `Ω`.
For the induction step both factors lie in `W^{k,p}(Ω)` and have `Cᵏ⁻¹` representatives on `U`:
`Φ'(w)` by the induction hypothesis, and `∂ᵥw` because the weak derivative of the `C¹` function
`w` is its classical one. The polarization identity `4 a b = (a + b)² - (a - b)²` and the induction
hypothesis for the square then put the product in `W^{k,p}(Ω)`. Thus the only product rule used is
the one hidden in the chain rule for the square.

## Main results

* `TauCeti.Wkp.exists_value_ae_eq_comp_of_contDiffOn`: `Φ ∘ w ∈ W^{k+1,p}(Ω)` for `Φ ∈ Cᵏ⁺¹` and
  `w ∈ Cᵏ(U) ∩ W^{k+1,p}(Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.3 and §6.3.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.5.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff NNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

namespace Wkp

/-- **The chain rule on a domain with compact closure.** If `w` is continuous on an open set
containing the compact set `closure Ω` and agrees on `Ω` with an element of `W^{k+1,p}(Ω)`, whose
weak derivative in the direction `v` is `d`, then `Φ ∘ w` has weak derivative `Φ'(w) d` in the
direction `v`, for every `C¹` function `Φ`. -/
private theorem hasWeakLineDerivOn_comp (hp : p ≠ ⊤) {U : Set E}
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) {k : ℕ}
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {w : E → ℝ} (hw : ContinuousOn w U)
    (u : Wkp mu Omega p (k + 1)) (hu : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] w)
    {v : E} {d : E → ℝ} (hd : HasWeakLineDerivOn mu Omega (value (k + 1) u) d v) :
    HasWeakLineDerivOn mu Omega (fun x => Φ (w x)) (fun x => deriv Φ (w x) * d x) v := by
  obtain ⟨M, hM⟩ := hΩ.exists_bound_of_continuousOn (hw.mono hΩU)
  set u₁ := firstOrder k u
  have hval : (W1p.value u₁ : E → ℝ) = value (k + 1) u := by rw [value_firstOrder]
  have hmem := ae_restrict_mem (μ := mu) Omega.isOpen.measurableSet
  -- The chain rule for `Φ ∘ u₁`, read in the direction `v`.
  have hchain := (W1p.hasWeakFDerivOn_comp_of_ae_abs_le hp hΦ (u := u₁) (M := M) (by
    filter_upwards [hu, hmem] with x hx hxΩ
    rw [hval, hx]
    simpa using hM x (subset_closure hxΩ))).hasWeakLineDerivOn v
  -- The weak derivative `d` is the component of the weak gradient of `u₁` along `v`.
  have hgrad : d =ᵐ[mu.restrict Omega] fun x => innerSL ℝ (W1p.gradient u₁ x) v :=
    hd.ae_eq (hval ▸ (W1p.hasWeakFDerivOn u₁).hasWeakLineDerivOn v)
  refine (hchain.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [hu] with x hx
    rw [hval, hx]
  · filter_upwards [hu, hgrad] with x hx hdx
    rw [hval, hx, hdx]
    simp

/-- The assembly step: if, in every direction, `Φ'(w)` times the weak derivative of `w` lies in
`W^{k,p}(Ω)`, then `Φ ∘ w` lies in `W^{k+1,p}(Ω)`. -/
private theorem exists_value_ae_eq_comp_of_forall_exists (hp : p ≠ ⊤) {U : Set E}
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) {k : ℕ}
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {w : E → ℝ} (hw : ContinuousOn w U)
    (u : Wkp mu Omega p (k + 1)) (hu : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] w)
    (h : ∀ (v : E) (d : Wkp mu Omega p k),
      HasWeakLineDerivOn mu Omega (value (k + 1) u) (value k d) v →
        ∃ D : Wkp mu Omega p k,
          (value k D : E → ℝ) =ᵐ[mu.restrict Omega] fun x => deriv Φ (w x) * value k d x) :
    ∃ g : Wkp mu Omega p (k + 1),
      (value (k + 1) g : E → ℝ) =ᵐ[mu.restrict Omega] fun x => Φ (w x) := by
  choose d hd using exists_hasWeakLineDerivOn_value k u
  choose D hD using fun v => h v (d v) (hd v)
  exact exists_value_ae_eq_of_forall_hasWeakLineDerivOn k
    (((hΦ.continuous.comp_continuousOn hw).mono hΩU).memLp_restrict_of_subset_isCompact hΩ
      Omega.isOpen.measurableSet subset_closure p) D
    fun v => (hasWeakLineDerivOn_comp hp hΩ hΩU hΦ hw u hu (hd v)).congr_ae_deriv (hD v).symm

/-- **Composition with a smooth function in `W^{k+1,p}`.** Let `Ω` have compact closure inside an
open set `U`, let `1 ≤ p < ∞`, let `Φ : ℝ → ℝ` be `Cᵏ⁺¹` and let `w` be `Cᵏ` on `U`. If `w`
agrees almost everywhere on `Ω` with an element of `W^{k+1,p}(Ω)`, then so does `Φ ∘ w`. -/
theorem exists_value_ae_eq_comp_of_contDiffOn (hp : p ≠ ⊤) {U : Set E} (hU : IsOpen U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ (k + 1) Φ) {w : E → ℝ} (hw : ContDiffOn ℝ k w U)
    (u : Wkp mu Omega p (k + 1)) (hu : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] w) :
    ∃ g : Wkp mu Omega p (k + 1),
      (value (k + 1) g : E → ℝ) =ᵐ[mu.restrict Omega] fun x => Φ (w x) := by
  have hΩm := Omega.isOpen.measurableSet
  have value_sub : ∀ (j : ℕ) (X Y : Wkp mu Omega p j), value j (X - Y) = value j X - value j Y :=
    fun j X Y => by simpa only [valueL_apply] using map_sub (valueL (mu := mu) j) X Y
  induction k generalizing Φ w with
  | zero =>
    refine exists_value_ae_eq_comp_of_forall_exists hp hΩ hΩU (by simpa using hΦ)
      hw.continuousOn u hu fun v d _ => ?_
    -- `Φ'(w)` is bounded on `Ω`, so the product stays in `Lᵖ(Ω)`.
    have hm : MemLp (fun x => deriv Φ (w x) * value 0 d x) p (mu.restrict Omega) :=
      ((((hΦ.continuous_deriv (by simp)).comp_continuousOn hw.continuousOn).mono
        hΩU).memLp_top_restrict_of_subset_isCompact hΩ hΩm subset_closure).fun_mul (Lp.memLp _)
    exact ⟨hm.toLp _, by simpa only [value_zero] using hm.coeFn_toLp⟩
  | succ k ih =>
    refine exists_value_ae_eq_comp_of_forall_exists hp hΩ hΩU (hΦ.of_le (by simp))
      hw.continuousOn u hu fun v d hd => ?_
    have hwk : ContDiffOn ℝ k w U := hw.of_le (by exact_mod_cast k.le_succ)
    -- The factor `a = Φ'(w)` lies in `W^{k+1,p}(Ω)` by the induction hypothesis.
    have hΦ' : ContDiff ℝ (k + 1) (deriv Φ) := by exact_mod_cast hΦ.deriv'
    set a : E → ℝ := fun x => deriv Φ (w x)
    have ha : ContDiffOn ℝ k a U := (hΦ'.of_le (by simp)).comp_contDiffOn hwk
    obtain ⟨A, hA⟩ := ih hΦ' hwk (lowerOrder (k + 1) u) (by rwa [← value_succ])
    -- The factor `∂ᵥw` is the classical derivative `b` of the `C^{k+1}` function `w`.
    set b : E → ℝ := fun x => fderiv ℝ w x v
    have hb : ContDiffOn ℝ k b U :=
      (hw.fderiv_of_isOpen hU (by exact_mod_cast le_rfl)).clm_apply contDiffOn_const
    have hdb : (value (k + 1) d : E → ℝ) =ᵐ[mu.restrict Omega] b := by
      have hw1 : ContDiffOn ℝ 1 w Omega :=
        (hw.mono (subset_closure.trans hΩU)).of_le (by exact_mod_cast Nat.succ_le_succ k.zero_le)
      have hcl := hasWeakFDerivOn_of_differentiableOn (μ := mu) (Ω := Omega)
        ((hw1.continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl).locallyIntegrableOn hΩm)
        fun x hx => (hw1.differentiableOn one_ne_zero).differentiableAt
          (Omega.isOpen.mem_nhds hx)
      exact hd.ae_eq ((hcl.hasWeakLineDerivOn v).congr_ae hu.symm)
    -- Polarization: `a b = ((a + b)² - (a - b)²) / 4`, and both squares lie in `W^{k+1,p}(Ω)`.
    have hsq : ContDiff ℝ (k + 1) fun t : ℝ => t ^ 2 := contDiff_id.pow 2
    obtain ⟨S₁, hS₁⟩ := ih hsq (ha.add hb) (A + d) (by
      filter_upwards [value_add (k + 1) A d ▸ Lp.coeFn_add (value (k + 1) A) (value (k + 1) d),
        hA, hdb] with x hx h₁ h₂
      rw [hx, Pi.add_apply, h₁, h₂])
    obtain ⟨S₂, hS₂⟩ := ih hsq (ha.sub hb) (A - d) (by
      filter_upwards [value_sub (k + 1) A d ▸ Lp.coeFn_sub (value (k + 1) A) (value (k + 1) d),
        hA, hdb] with x hx h₁ h₂
      rw [hx, Pi.sub_apply, h₁, h₂])
    refine ⟨(4⁻¹ : ℝ) • (S₁ - S₂), ?_⟩
    filter_upwards [value_smul (k + 1) (4⁻¹ : ℝ) (S₁ - S₂) ▸
        Lp.coeFn_smul (4⁻¹ : ℝ) (value (k + 1) (S₁ - S₂)),
      value_sub (k + 1) S₁ S₂ ▸ Lp.coeFn_sub (value (k + 1) S₁) (value (k + 1) S₂),
      hS₁, hS₂, hdb] with x hx hsub h₁ h₂ hdx
    rw [hx, Pi.smul_apply, hsub, Pi.sub_apply, h₁, h₂, hdx, smul_eq_mul]
    ring

end Wkp

end TauCeti
