/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Analysis.Pseudodifferential.Symbol.Integral

/-!
# Averaging symbols over a compact group

Let `G` be a compact group with a finite measure `μ`, such as the normalized Haar measure, acting
on the fibres `V` and `W` by continuous representations `σ_V` and `σ_W`. The average
`TauCeti.Symbol.average μ σ_V σ_W a` of a symbol `a` of order `m` has coefficient

`(x, ξ) ↦ ∫ σ_W(g) ∘ a(x, ξ) ∘ σ_V(g)⁻¹ dμ(g)`.

It is the integral `TauCeti.Symbol.integral` of the compact family of conjugates
`g ↦ σ_W(g) ∘ a ∘ σ_V(g)⁻¹`, so it is again a symbol of order `m`. Its seminorms are controlled
by those of `a` and the bounds of the representations (`TauCeti.Symbol.seminorm_average_le`).
For a left-invariant measure its coefficients are invariant under conjugation by the action
(`TauCeti.Symbol.comp_coefficient_average_comp`), and for a probability measure the average fixes
the invariant symbols (`TauCeti.Symbol.average_eq_self`), so it is a linear projection onto them
(`TauCeti.Symbol.average_average`). Here the group acts only on the fibres; it acts trivially on
the positions and frequencies.

## Main declarations

* `TauCeti.Symbol.average`, with `TauCeti.Symbol.coefficient_average`;
* `TauCeti.Symbol.average_add`, `TauCeti.Symbol.average_smul`: linearity;
* `TauCeti.Symbol.seminorm_average_le`: the seminorm bound;
* `TauCeti.Symbol.comp_coefficient_average_comp`: invariance of the average;
* `TauCeti.Symbol.average_eq_smul`, `TauCeti.Symbol.average_eq_self`,
  `TauCeti.Symbol.average_average`: the average of an invariant symbol, and idempotence.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §5, (5.5)–(5.6): averaging pseudodifferential operators over a compact group.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Definition 7.8.1, for
  the symbol seminorms.
-/

public section

noncomputable section

open MeasureTheory Set
open TopologicalSpace (Compacts)

namespace TauCeti.Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- Conjugation `T ↦ S ∘ T ∘ R` of the coefficients. -/
private def conjCLM (S : W →L[ℂ] W) (R : V →L[ℂ] V) : (V →L[ℂ] W) →L[ℂ] V →L[ℂ] W :=
  (ContinuousLinearMap.compL ℂ V W W S).comp ((ContinuousLinearMap.compL ℂ V V W).flip R)

@[simp]
private theorem conjCLM_apply (S : W →L[ℂ] W) (R : V →L[ℂ] V) (T : V →L[ℂ] W) :
    conjCLM S R T = S ∘L T ∘L R := (rfl)

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G]
  (σV : G →ₜ* (V →L[ℂ] V)) (σW : G →ₜ* (W →L[ℂ] W))

private theorem continuous_conjCLM [IsTopologicalGroup G] :
    Continuous fun g => conjCLM (σW g) (σV g⁻¹) :=
  ((ContinuousLinearMap.compL ℂ V W W).continuous.comp σW.continuous).clm_comp
    ((ContinuousLinearMap.compL ℂ V V W).flip.continuous.comp (σV.continuous.comp continuous_inv))

/-- The conjugate `σ_W(g) ∘ a ∘ σ_V(g)⁻¹` of a symbol. -/
private def conj (a : Symbol n V W m) (g : G) : Symbol n V W m :=
  a.map ((conjCLM (σW g) (σV g⁻¹)).restrictScalars ℝ)

private theorem coefficient_conj (a : Symbol n V W m) (g : G)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (conj σV σW a g).coefficient p = σW g ∘L a.coefficient p ∘L σV g⁻¹ :=
  coefficient_map _ a p

private theorem coefficient_conj_eq_comp (a : Symbol n V W m) (g : G) :
    (conj σV σW a g).coefficient = (conjCLM (σW g) (σV g⁻¹)).restrictScalars ℝ ∘ a.coefficient :=
  funext fun p => coefficient_map _ a p

/-- The spatial jets of the conjugates are jointly continuous in the group element and the
position-frequency variables. -/
private theorem continuous_iteratedFDeriv_conj [IsTopologicalGroup G] (a : Symbol n V W m) (k : ℕ) :
    Continuous fun q : G × (CoordinateSpace n × CoordinateSpace n) =>
      iteratedFDeriv ℝ k (conj σV σW a q.1).coefficient q.2 := by
  have h (q : G × (CoordinateSpace n × CoordinateSpace n)) :
      iteratedFDeriv ℝ k (conj σV σW a q.1).coefficient q.2 =
        ((conjCLM (σW q.1) (σV q.1⁻¹)).restrictScalars ℝ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ k a.coefficient q.2) := by
    rw [coefficient_conj_eq_comp]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left _ a.contDiff_coefficient.contDiffAt
      (by exact_mod_cast le_top)
  refine Continuous.congr ?_ fun q => (h q).symm
  exact (isBoundedBilinearMap_compMultilinear (𝕜 := ℝ)
    (E := fun _ : Fin k => CoordinateSpace n × CoordinateSpace n)).continuous.comp
    ((((ContinuousLinearMap.restrictScalarsIsometry ℂ (V →L[ℂ] W) (V →L[ℂ] W) ℝ ℝ).continuous.comp
      (continuous_conjCLM σV σW)).comp continuous_fst).prodMk
      ((a.contDiff_coefficient.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
        continuous_snd))

private theorem norm_mixedDeriv_conj_le (a : Symbol n V W m) (g : G) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    ‖mixedDeriv α β (conj σV σW a g).coefficient x ξ‖ ≤
      ‖σW g‖ * ‖σV g⁻¹‖ * ‖mixedDeriv α β a.coefficient x ξ‖ := by
  calc ‖mixedDeriv α β (conj σV σW a g).coefficient x ξ‖
      = ‖σW g ∘L mixedDeriv α β a.coefficient x ξ ∘L σV g⁻¹‖ := by
        rw [coefficient_conj_eq_comp, ContinuousLinearMap.mixedDeriv_comp_left _
          a.contDiff_coefficient]
        rfl
    _ ≤ ‖σW g‖ * (‖mixedDeriv α β a.coefficient x ξ‖ * ‖σV g⁻¹‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by ring

/-- The symbol estimates of the conjugates hold uniformly in the group element. -/
private theorem exists_bound_conj [IsTopologicalGroup G] [CompactSpace G] (a : Symbol n V W m)
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (conj σV σW a g).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((σW.continuous.norm.mul (σV.continuous.comp continuous_inv).norm).continuousOn)
  obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α β
  refine ⟨max A 0 * C, by positivity, fun g x hx ξ => ?_⟩
  calc ‖mixedDeriv α β (conj σV σW a g).coefficient x ξ‖
      ≤ ‖σW g‖ * ‖σV g⁻¹‖ * ‖mixedDeriv α β a.coefficient x ξ‖ :=
        norm_mixedDeriv_conj_le σV σW a g α β x ξ
    _ ≤ max A 0 * (C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) := by
        gcongr
        · exact (le_abs_self _).trans ((hA g (mem_univ g)).trans (le_max_left _ _))
        · exact hC x hx ξ
    _ = _ := by ring

end Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ]
  (σV : G →ₜ* (V →L[ℂ] V)) (σW : G →ₜ* (W →L[ℂ] W))

private theorem integrable_conj (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹) μ := by
  have hc : Continuous fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹ :=
    (continuous_conjCLM σV σW).clm_apply continuous_const
  exact hc.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- The average `∫ σ_W(g) ∘ a ∘ σ_V(g)⁻¹ dμ(g)` of a symbol over a compact group `G` acting on the
fibres `V` and `W` by continuous representations `σ_V` and `σ_W`, a symbol of the same order. -/
def average (a : Symbol n V W m) : Symbol n V W m :=
  integral μ (conj σV σW a) (continuous_iteratedFDeriv_conj σV σW a) (exists_bound_conj σV σW a)

@[simp]
theorem coefficient_average (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ σV σW a).coefficient p = ∫ g, σW g ∘L a.coefficient p ∘L σV g⁻¹ ∂μ := by
  simp only [average, coefficient_integral, coefficient_conj]

theorem average_add (a b : Symbol n V W m) :
    average μ σV σW (a + b) = average μ σV σW a + average μ σV σW b := by
  refine Symbol.ext (funext fun p => ?_)
  simpa [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add] using
    MeasureTheory.integral_add (integrable_conj μ σV σW a p) (integrable_conj μ σV σW b p)

theorem average_smul (c : ℂ) (a : Symbol n V W m) :
    average μ σV σW (c • a) = c • average μ σV σW a := by
  refine Symbol.ext (funext fun p => ?_)
  simpa [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using
    MeasureTheory.integral_smul c fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹

/-- If the representations are bounded by `A` and `B`, then
`p_{K,α,β}(average a) ≤ μ(G) A B p_{K,α,β}(a)`. -/
theorem seminorm_average_le (a : Symbol n V W m) {K : Compacts (CoordinateSpace n)}
    {α β : List (Fin n)} {A B : ℝ} (hA : ∀ g, ‖σW g‖ ≤ A) (hB : ∀ g, ‖σV g‖ ≤ B) :
    Symbol.seminorm K α β (average μ σV σW a) ≤
      μ.real univ * (A * B * Symbol.seminorm K α β a) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  refine seminorm_integral_le μ (conj σV σW a) (continuous_iteratedFDeriv_conj σV σW a)
    (exists_bound_conj σV σW a) K α β (by positivity) fun g =>
      seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_
  calc ‖mixedDeriv α β (conj σV σW a g).coefficient x ξ‖
      ≤ ‖σW g‖ * ‖σV g⁻¹‖ * ‖mixedDeriv α β a.coefficient x ξ‖ :=
        norm_mixedDeriv_conj_le σV σW a g α β x ξ
    _ ≤ A * B * (Symbol.seminorm K α β a * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) := by
        gcongr
        exacts [hA g, hB g⁻¹, le_seminorm K α β a hx ξ]
    _ = _ := by ring

/-- **The average is invariant.** For a left-invariant measure, conjugating the coefficients of the
average by the action of any `h ∈ G` returns them. -/
theorem comp_coefficient_average_comp [CompleteSpace W] [μ.IsMulLeftInvariant] (a : Symbol n V W m)
    (h : G) (p : CoordinateSpace n × CoordinateSpace n) :
    σW h ∘L (average μ σV σW a).coefficient p ∘L σV h⁻¹ = (average μ σV σW a).coefficient p := by
  rw [coefficient_average, ← conjCLM_apply,
    ← (conjCLM (σW h) (σV h⁻¹)).integral_comp_comm (integrable_conj μ σV σW a p)]
  have hg (g : G) : conjCLM (σW h) (σV h⁻¹) (σW g ∘L a.coefficient p ∘L σV g⁻¹) =
      σW (h * g) ∘L a.coefficient p ∘L σV (h * g)⁻¹ := by
    simp only [conjCLM_apply, map_mul, mul_inv_rev, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  simp_rw [hg]
  exact integral_mul_left_eq_self (fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹) h

/-- The average of an invariant symbol is the symbol multiplied by the total mass. -/
theorem average_eq_smul [CompleteSpace W] (a : Symbol n V W m)
    (ha : ∀ g p, σW g ∘L a.coefficient p ∘L σV g⁻¹ = a.coefficient p) :
    average μ σV σW a = (μ.real univ : ℂ) • a := by
  refine Symbol.ext (funext fun p => ?_)
  rw [coefficient_average]
  simp only [ha, MeasureTheory.integral_const, coefficient_smul, Pi.smul_apply]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (μ.real univ) (a.coefficient p)

/-- For a probability measure the average fixes the invariant symbols. -/
theorem average_eq_self [CompleteSpace W] [IsProbabilityMeasure μ] (a : Symbol n V W m)
    (ha : ∀ g p, σW g ∘L a.coefficient p ∘L σV g⁻¹ = a.coefficient p) :
    average μ σV σW a = a := by
  simp [average_eq_smul μ σV σW a ha]

/-- For a left-invariant probability measure, such as the normalized Haar measure, averaging is a
projection onto the invariant symbols. -/
@[simp]
theorem average_average [CompleteSpace W] [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (a : Symbol n V W m) :
    average μ σV σW (average μ σV σW a) = average μ σV σW a :=
  average_eq_self μ σV σW _ (comp_coefficient_average_comp μ σV σW a)

end TauCeti.Symbol
