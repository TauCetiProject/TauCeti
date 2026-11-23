/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.QuadraticEstimate
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.Analysis.Sobolev.Morrey.Basic

/-!
# The quadratic estimate for the Floer operator in `W^{1,p}` on convex domains

Let `(V, ω)` be a finite-dimensional symplectic vector space and let
`F(u) = ∂s u - X_Ks(u) + J(u)(∂t u - X_Kt(u))` be the Floer operator
(`TauCeti.SymplecticForm.floerOperator`) with linearization `D_w` at a map `w`
(`TauCeti.SymplecticForm.floerLinearization`). Gluing and transversality solve `F(w + ξ) = 0`
near an approximate solution `w` by the Newton iteration of
`TauCeti.exists_mem_range_norm_le_add_add_eq_zero`, in a Banach space of increments `ξ` with a
bounded right inverse of `D_w`. That theorem asks for the nonlinear part
`N_w(ξ) = F(w + ξ) - F(w) - D_w ξ` to be quadratically small in its norms,

`‖N_w(ξ₁) - N_w(ξ₂)‖ ≤ (L / 2) (‖ξ₁‖ + ‖ξ₂‖) ‖ξ₁ - ξ₂‖`.

The usual choice is `ξ ∈ W^{1,p}` and `N_w(ξ) ∈ Lᵖ` for `p > 2`, the dimension of the domain.
`TauCeti.Geometry.Symplectic.Floer.QuadraticEstimate` proves this on the cylinder, for increments
of period one in `t`
(`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_jet`).
This file proves it for increments without periodicity, over a convex open set `Ω` of the domain
`ℝ × ℝ`. As there, the coefficients `J`, `Ks`, `Kt` are pulled back along a parameter map
`φ : ℝ × ℝ → P`, they are jointly `C²`, `C³` and `C³`, and the graph of `(φ, w)` over `Ω` lies in a
compact set `K`.

For `p > 2`, Morrey's supremum bound (`TauCeti.exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv`)
controls the supremum norms on `Ω` by the `W^{1,p}` norm
`‖ξ‖_{1,p} = ‖ξ‖_{Lᵖ(Ω)} + ‖Dξ‖_{Lᵖ(Ω)}`. Inserting it into the `Lᵖ` estimate with supremum norms
(`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le`)
gives, for `‖ξ₁‖_{1,p}, ‖ξ₂‖_{1,p} ≤ δ` and slice defect `‖∂t w - X_Kt(w)‖ ≤ B` on `Ω`,
`‖N_w(ξ₁) - N_w(ξ₂)‖_{Lᵖ(Ω)} ≤ C (1 + B) (‖ξ₁‖_{1,p} + ‖ξ₂‖_{1,p}) ‖ξ₁ - ξ₂‖_{1,p}`
(`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex`).
Its case `ξ₂ = 0` is `‖F(w + ξ) - F(w) - D_w ξ‖_{Lᵖ(Ω)} ≤ C (1 + B) ‖ξ‖_{1,p}²`.

The constants do not depend on the size of `Ω`: they only depend on `p` and on a radius `r` and a
measure `m > 0` with `m ≤ |Ω ∩ B(z, r)|` for every `z ∈ Ω`. The rectangles `(a, b) × (c, d)` with
sides of length at least one satisfy this with `r = m = 1`
(`TauCeti.one_le_volume_Ioo_prod_Ioo_inter_ball`), so the estimate is uniform over the long necks
`(-R, R) × (0, 1)` of glued Floer solutions, with the coefficients `t`-dependent through
`φ z = z.2` as on cylindrical ends.

The increments are `C¹` on `Ω`. No Sobolev completion is constructed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.5, on the quadratic estimate in `W^{1,p}` and the implicit function theorem, and
  Chapter 10, on gluing.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

namespace TauCeti.SymplecticForm

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ω : SymplecticForm V)
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {J : P → V → V →L[ℝ] V} {Ks Kt : P → V → ℝ} {K : Set (P × V)}

/-- The arithmetic combining the three terms of the `Lᵖ` estimate with supremum norms into the
quadratic `W^{1,p}` bound, with `a` the constant of Morrey's supremum bound. -/
private theorem quadratic_terms_le {a e d d' S S₁ S₂ B : ℝ≥0∞} (he : e ≤ S) (hd : d ≤ S₁ + S₂)
    (hd' : d' ≤ S) :
    a * (S₁ + S₂) * (1 + B) * e + a * S * d + a * (S₁ + S₂) * d' ≤
      3 * a * (1 + B) * (S₁ + S₂) * S := by
  have h₁ : a * (S₁ + S₂) * S ≤ a * (S₁ + S₂) * (1 + B) * S :=
    calc a * (S₁ + S₂) * S = a * (S₁ + S₂) * 1 * S := by ring
      _ ≤ a * (S₁ + S₂) * (1 + B) * S := by gcongr; exact le_self_add
  calc a * (S₁ + S₂) * (1 + B) * e + a * S * d + a * (S₁ + S₂) * d' ≤
        a * (S₁ + S₂) * (1 + B) * S + a * (S₁ + S₂) * S + a * (S₁ + S₂) * S :=
        add_le_add (add_le_add (mul_le_mul_right he _)
          ((mul_le_mul_right hd _).trans_eq (by ring))) (mul_le_mul_right hd' _)
    _ ≤ a * (S₁ + S₂) * (1 + B) * S + a * (S₁ + S₂) * (1 + B) * S +
        a * (S₁ + S₂) * (1 + B) * S := by gcongr
    _ = 3 * a * (1 + B) * (S₁ + S₂) * S := by ring

/-- The choice of the radius `δ₁ / (2 (a + 1))` in the `W^{1,p}` estimate makes `a` times the sum of
two such radii at most `δ₁`. -/
private theorem mul_add_div_two_mul_add_one_le (a δ₁ : ℝ≥0) :
    a * (δ₁ / (2 * (a + 1)) + δ₁ / (2 * (a + 1))) ≤ δ₁ := by
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [← add_div, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [a.coe_nonneg, δ₁.coe_nonneg]

/-- **The quadratic estimate for the Floer operator in `W^{1,p}`.** Let `J` be jointly `C²` and
the Hamiltonians `Ks`, `Kt` jointly `C³` in the parameter and the target point, let `K` be a
compact set of pairs `(p, y)`, let `p > 2`, and let `r : ℝ` and `m ≠ 0`. There are `δ > 0` and `C`
such that the following holds for every convex open set `Ω` of the domain with
`m ≤ |Ω ∩ B(z, r)|` for all `z ∈ Ω`, and every parameter map `φ` measurable on `Ω`. Write
`‖ξ‖_{1,p} = ‖ξ‖_{Lᵖ(Ω)} + ‖Dξ‖_{Lᵖ(Ω)}`. Let `w` be differentiable on `Ω`, with graph
`(φ z, w z) ∈ K` and slice defect `‖∂t w - X_Kt(w)‖ ≤ B` over `Ω`, and let `ξ₁`, `ξ₂` be `C¹` on
`Ω` with `‖ξ₁‖_{1,p}, ‖ξ₂‖_{1,p} ≤ δ`. Then the Floer operator with coefficients `J (φ z)`,
`Ks (φ z)`, `Kt (φ z)` satisfies
`‖F(w + ξ₁) - F(w + ξ₂) - D_w(ξ₁ - ξ₂)‖_{Lᵖ(Ω)}
  ≤ C (1 + B) (‖ξ₁‖_{1,p} + ‖ξ₂‖_{1,p}) ‖ξ₁ - ξ₂‖_{1,p}`.
The constants do not depend on the size of `Ω`. For the remainder `ξ ↦ F(w + ξ) - F(w) - D_w ξ`
this has the form of the quadratic hypothesis of `TauCeti.exists_mem_range_norm_le_add_add_eq_zero`;
applying that theorem still needs a Banach space of increments (a Sobolev completion). -/
theorem
    exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex
    (hK : IsCompact K) (hJ : ContDiff ℝ 2 (Function.uncurry J))
    (hKs : ContDiff ℝ 3 (Function.uncurry Ks)) (hKt : ContDiff ℝ 3 (Function.uncurry Kt))
    {p : ℝ≥0} (hp : 2 < p) (r : ℝ) {m : ℝ≥0∞} (hm : m ≠ 0) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0, ∀ (Ω : Set (ℝ × ℝ)) (φ : ℝ × ℝ → P) (w ξ₁ ξ₂ : ℝ × ℝ → V)
      (B : ℝ≥0), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, m ≤ volume (Ω ∩ ball z r)) →
      AEStronglyMeasurable φ (volume.restrict Ω) → DifferentiableOn ℝ w Ω →
      ContDiffOn ℝ 1 ξ₁ Ω → ContDiffOn ℝ 1 ξ₂ Ω → (∀ z ∈ Ω, (φ z, w z) ∈ K) →
      (∀ z ∈ Ω,
        ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ₑ ≤ B) →
      eLpNorm ξ₁ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₁) p (volume.restrict Ω) ≤ δ →
      eLpNorm ξ₂ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₂) p (volume.restrict Ω) ≤ δ →
      eLpNorm (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₁) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ₂) z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w
            (ξ₁ - ξ₂) z) p (volume.restrict Ω) ≤
        C * (1 + B) *
          (eLpNorm ξ₁ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₁) p (volume.restrict Ω) +
            (eLpNorm ξ₂ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ₂) p (volume.restrict Ω))) *
          (eLpNorm (ξ₁ - ξ₂) p (volume.restrict Ω) +
            eLpNorm (fderiv ℝ (ξ₁ - ξ₂)) p (volume.restrict Ω)) := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨CM, hCM⟩ := exists_enorm_le_mul_eLpNorm_add_eLpNorm_fderiv (μ := volume)
    (E := ℝ × ℝ) (F := V) hp1 (by rw [finrank_prod, finrank_self]; norm_num; exact hp) r hm
  obtain ⟨δ₁, hδ₁, C₁, h₁⟩ :=
    ω.exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le hK hJ
      hKs hKt
  refine ⟨δ₁.toNNReal / (2 * (CM + 1)), div_pos (Real.toNNReal_pos.2 hδ₁) (by positivity),
    3 * C₁ * CM, fun Ω φ w ξ₁ ξ₂ B hΩ hΩc hfat hφ hw hξ₁ hξ₂ hwK hB hS₁ hS₂ => ?_⟩
  set μ := volume.restrict Ω
  set S₁ := eLpNorm ξ₁ p μ + eLpNorm (fderiv ℝ ξ₁) p μ
  set S₂ := eLpNorm ξ₂ p μ + eLpNorm (fderiv ℝ ξ₂) p μ
  set S := eLpNorm (ξ₁ - ξ₂) p μ + eLpNorm (fderiv ℝ (ξ₁ - ξ₂)) p μ
  have hξ : ContDiffOn ℝ 1 (ξ₁ - ξ₂) Ω := hξ₁.sub hξ₂
  have hd₁ := hξ₁.differentiableOn one_ne_zero
  have hd₂ := hξ₂.differentiableOn one_ne_zero
  -- The `W^{1,p}` norm of the difference is finite.
  have hSle : S ≤ S₁ + S₂ :=
    eLpNorm_sub_add_eLpNorm_fderiv_sub_le (by exact_mod_cast hp1) hΩ hd₁ hd₂
  have hS₁₂ : S₁ + S₂ ≠ ∞ := ENNReal.add_ne_top.2
    ⟨ne_top_of_le_ne_top ENNReal.coe_ne_top hS₁, ne_top_of_le_ne_top ENNReal.coe_ne_top hS₂⟩
  have hS : S ≠ ∞ := (hSle.trans_lt hS₁₂.lt_top).ne
  -- The supremum bounds, by Morrey's inequality, in real form.
  have hsup {ξ : ℝ × ℝ → V} (hξ : ContDiffOn ℝ 1 ξ Ω) {T : ℝ≥0∞} (hT : T ≠ ∞)
      (h : CM * (eLpNorm ξ p μ + eLpNorm (fderiv ℝ ξ) p μ) ≤ T) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      ‖ξ z‖ ≤ T.toReal := by
    rw [← toReal_eNorm]
    exact ENNReal.toReal_mono hT ((hCM Ω ξ z hΩ (hΩc.starConvex hz) hξ (hfat z hz)).trans h)
  have ha : ENNReal.ofReal (CM * (S₁ + S₂)).toReal = CM * (S₁ + S₂) :=
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hS₁₂)
  have hb : ENNReal.ofReal (CM * S).toReal = CM * S :=
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hS)
  have haδ : (CM * (S₁ + S₂)).toReal ≤ δ₁ := by
    refine ENNReal.toReal_le_of_le_ofReal hδ₁.le ?_
    calc (CM : ℝ≥0∞) * (S₁ + S₂) ≤ CM * ((δ₁.toNNReal / (2 * (CM + 1)) : ℝ≥0) +
          (δ₁.toNNReal / (2 * (CM + 1)) : ℝ≥0)) := by gcongr
      _ = ((CM * (δ₁.toNNReal / (2 * (CM + 1)) + δ₁.toNNReal / (2 * (CM + 1))) : ℝ≥0) :
          ℝ≥0∞) := by norm_cast
      _ ≤ δ₁.toNNReal := ENNReal.coe_le_coe.2 (mul_add_div_two_mul_add_one_le CM δ₁.toNNReal)
  have h := h₁ volume (p := p) (by exact_mod_cast hp1) (a := (CM * (S₁ + S₂)).toReal) (A := B)
    (b := (CM * S).toReal) hΩ.measurableSet hφ (fun z hz => hw.differentiableAt (hΩ.mem_nhds hz))
    (fun z hz => hd₁.differentiableAt (hΩ.mem_nhds hz))
    (fun z hz => hd₂.differentiableAt (hΩ.mem_nhds hz)) hwK haδ
    (hsup hξ₁ (ENNReal.mul_ne_top ENNReal.coe_ne_top hS₁₂) (mul_le_mul_right le_self_add _))
    (hsup hξ₂ (ENNReal.mul_ne_top ENNReal.coe_ne_top hS₁₂) (mul_le_mul_right le_add_self _))
    (hsup hξ (ENNReal.mul_ne_top ENNReal.coe_ne_top hS) le_rfl)
    (fun z hz => by exact_mod_cast eNorm_le_coe.1 (hB z hz))
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ha, hb, ENNReal.ofReal_add zero_le_one B.coe_nonneg,
    ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal] at h
  -- The slice derivatives are bounded by the full derivatives.
  have hDi (L : ℝ × ℝ →L[ℝ] V) : ‖L stdComplexLineImag‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans_eq (by simp [stdComplexLineImag_eq])
  have hm₁ : AEStronglyMeasurable (fun z ↦ fderiv ℝ ξ₁ z stdComplexLineImag) μ :=
    ((hξ₁.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
      continuousOn_const).aestronglyMeasurable hΩ.measurableSet
  have hm₂ : AEStronglyMeasurable (fun z ↦ fderiv ℝ ξ₂ z stdComplexLineImag) μ :=
    ((hξ₂.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
      continuousOn_const).aestronglyMeasurable hΩ.measurableSet
  have hd : eLpNorm (fun z ↦ fderiv ℝ ξ₁ z stdComplexLineImag) p μ ≤ S₁ + S₂ :=
    (eLpNorm_mono hm₁ fun z => hDi _).trans ((le_add_self : _ ≤ S₁).trans le_self_add)
  have hd' : eLpNorm (fun z ↦ fderiv ℝ ξ₁ z stdComplexLineImag -
      fderiv ℝ ξ₂ z stdComplexLineImag) p μ ≤ S := by
    refine (eLpNorm_mono_ae (hm₁.sub hm₂)
      (ae_restrict_of_forall_mem hΩ.measurableSet fun z hz => ?_)).trans le_add_self
    rw [fderiv_sub (hd₁.differentiableAt (hΩ.mem_nhds hz)) (hd₂.differentiableAt (hΩ.mem_nhds hz))]
    exact hDi (fderiv ℝ ξ₁ z - fderiv ℝ ξ₂ z)
  refine (h.trans (mul_le_mul_right (quadratic_terms_le le_self_add hd hd') _)).trans_eq ?_
  push_cast
  ring

/-- **The quadratic estimate for the Floer operator at a map, in `W^{1,p}`.** Under the
hypotheses of
`exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex`,
there are `δ > 0` and `C` such that every increment `ξ` which is `C¹` on `Ω` with
`‖ξ‖_{1,p} = ‖ξ‖_{Lᵖ(Ω)} + ‖Dξ‖_{Lᵖ(Ω)} ≤ δ` satisfies
`‖F(w + ξ) - F(w) - D_w ξ‖_{Lᵖ(Ω)} ≤ C (1 + B) ‖ξ‖_{1,p}²`. -/
theorem
exists_pos_forall_eLpNorm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le_of_convex
    (hK : IsCompact K) (hJ : ContDiff ℝ 2 (Function.uncurry J))
    (hKs : ContDiff ℝ 3 (Function.uncurry Ks)) (hKt : ContDiff ℝ 3 (Function.uncurry Kt))
    {p : ℝ≥0} (hp : 2 < p) (r : ℝ) {m : ℝ≥0∞} (hm : m ≠ 0) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ≥0, ∀ (Ω : Set (ℝ × ℝ)) (φ : ℝ × ℝ → P) (w ξ : ℝ × ℝ → V)
      (B : ℝ≥0), IsOpen Ω → Convex ℝ Ω → (∀ z ∈ Ω, m ≤ volume (Ω ∩ ball z r)) →
      AEStronglyMeasurable φ (volume.restrict Ω) → DifferentiableOn ℝ w Ω →
      ContDiffOn ℝ 1 ξ Ω → (∀ z ∈ Ω, (φ z, w z) ∈ K) →
      (∀ z ∈ Ω,
        ‖fderiv ℝ w z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (w z)‖ₑ ≤ B) →
      eLpNorm ξ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ) p (volume.restrict Ω) ≤ δ →
      eLpNorm (fun z ↦
        ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (w + ξ) z -
          ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w z -
          ω.floerLinearization (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) w ξ z)
        p (volume.restrict Ω) ≤
        C * (1 + B) *
          (eLpNorm ξ p (volume.restrict Ω) + eLpNorm (fderiv ℝ ξ) p (volume.restrict Ω)) ^ 2 := by
  obtain ⟨δ, hδ, C, h⟩ :=
    ω.exists_pos_forall_eLpNorm_floerOperator_sub_floerOperator_sub_floerLinearization_le_of_convex
      hK hJ hKs hKt hp r hm
  refine ⟨δ, hδ, C, fun Ω φ w ξ B hΩ hΩc hfat hφ hw hξ hwK hB hS => ?_⟩
  have h0 : ContDiffOn ℝ 1 (0 : ℝ × ℝ → V) Ω := contDiffOn_const
  have hzero : eLpNorm (0 : ℝ × ℝ → V) p (volume.restrict Ω) +
      eLpNorm (fderiv ℝ (0 : ℝ × ℝ → V)) p (volume.restrict Ω) = 0 := by
    rw [fderiv_zero, eLpNorm_zero, eLpNorm_zero (ε := ℝ × ℝ →L[ℝ] V), add_zero]
  have := h Ω φ w ξ 0 B hΩ hΩc hfat hφ hw hξ h0 hwK hB hS (by rw [hzero]; positivity)
  simp only [add_zero, sub_zero, hzero] at this
  rw [sq, ← mul_assoc]
  exact this

end TauCeti.SymplecticForm
