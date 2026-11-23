/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.EvolutionSpace.Basic
import TauCeti.Analysis.PDE.Parabolic.EnergyEstimate
import TauCeti.Analysis.PDE.Parabolic.Existence
import TauCeti.MeasureTheory.Function.EssSup
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The solution operator of a linear parabolic equation

Let `ι : V →L[ℝ] H` be a continuous linear map with dense range from a separable real Hilbert space
`V` into a real Hilbert space `H`, so that `V ↪ H ↪ V*` is a Gelfand triple, and let
`A(t) : V →L[ℝ] V*`, `t ∈ (a, b)`, be weakly measurable, essentially bounded by `Λ` and satisfy
Gårding's inequality `α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0` and `β ≥ 0`. The abstract linear
parabolic problem

`u' + A(t) u = f` on `(a, b)`, `u(a) = u₀`,

with `u₀ ∈ H` and `f ∈ L²(a, b; V*)` is well posed in the energy space
`TauCeti.EvolutionSpace ι a b = L²(a, b; V) ∩ H¹(a, b; V*)`: it has exactly one solution there
(`TauCeti.EvolutionSpace.existsUnique_ae_timeDeriv_add_eq`), where the initial value is that of
the canonical continuous representative `TauCeti.EvolutionSpace.toContinuousMap` in
`C([a, b]; H)`. The solution depends linearly and boundedly on the data: this file constructs the
**solution operator**

`TauCeti.EvolutionSpace.parabolicSolutionL : H × L²(a, b; V*) →L[ℝ] EvolutionSpace ι a b`,
`(u₀, f) ↦ u`,

characterized by `TauCeti.EvolutionSpace.eq_parabolicSolutionL_iff`, with the explicit operator
norm bound `1 + (1 + Λ) √(e^{2β(b - a)} (1 + α⁻¹) / α)`
(`TauCeti.EvolutionSpace.norm_parabolicSolutionL_le`). For the parabolic Dirichlet problem of a
divergence-form operator, `V = H¹₀(Ω)`, `H = L²(Ω)` and `A(t)` is the energy form of `L(t)`.

The bound comes from the energy estimate
`TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual`, which for every solution
in the energy space gives

* `‖u‖²_{L²(a, b; V)} ≤ e^{2β(b - a)} (‖u(a)‖² + α⁻¹ ‖f‖²) / α`
  (`TauCeti.EvolutionSpace.norm_value_sq_le_of_ae_timeDeriv_add_eq`), and
* `‖u‖²_{C([a, b]; H)} ≤ e^{2β(b - a)} (‖u(a)‖² + α⁻¹ ‖f‖²)`
  (`TauCeti.EvolutionSpace.norm_toContinuousMap_sq_le_of_ae_timeDeriv_add_eq`),

together with the equation itself, `‖u'‖_{L²(a, b; V*)} ≤ ‖f‖ + Λ ‖u‖_{L²(a, b; V)}`
(`TauCeti.EvolutionSpace.norm_timeDeriv_le_of_ae_timeDeriv_add_eq`). Existence is
`TauCeti.exists_hasWeakLineDerivOn_gelfandDual` and uniqueness is
`TauCeti.HasWeakLineDerivOn.ae_eq_of_gelfandDual`; by uniqueness, the solution map is
linear.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2, Theorems 2, 3 and 4.
-/

public section

noncomputable section

open MeasureTheory Filter Set Real TopologicalSpace

namespace TauCeti

namespace EvolutionSpace

section Estimates

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : V →L[ℝ] H}
  {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b α β Λ : ℝ} {u v : EvolutionSpace ι a b}

/-- **The time derivative of a solution.** If `‖A(t)‖ ≤ Λ` for almost every `t ∈ (a, b)`, every
element of the energy space solving `u' + A(t) u = f` on `(a, b)` satisfies
`‖u'‖_{L²(a, b; V*)} ≤ ‖f‖ + Λ ‖u‖_{L²(a, b; V)}`. -/
theorem norm_timeDeriv_le_of_ae_timeDeriv_add_eq
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ)
    {f : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))}
    (hu : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = f t) :
    ‖timeDeriv u‖ ≤ ‖f‖ + Λ * ‖value u‖ := by
  rcases le_or_gt 0 Λ with hΛ | hΛ
  · simpa only [one_mul] using Lp.norm_le_add_of_ae_norm_le zero_le_one hΛ (f := timeDeriv u)
      (g := f) (h := value u) (by
        filter_upwards [hu, hA_bound] with t ht hAt
        rw [one_mul, eq_sub_of_add_eq ht]
        exact (norm_sub_le _ _).trans (add_le_add_right ((A t).le_of_opNorm_le hAt _) _))
  -- A negative essential bound forces `(a, b)` to be null, where every `L²` norm vanishes.
  have hnull : ∀ᵐ _ ∂volume.restrict (Ioo a b), False :=
    hA_bound.mono fun t ht ↦ (hΛ.trans_le (norm_nonneg (A t))).not_ge ht
  have hd := Lp.norm_le_add_of_ae_norm_le (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
    (f := timeDeriv u) (g := f) (h := f) (hnull.mono fun _ h ↦ h.elim)
  have hv := Lp.norm_le_add_of_ae_norm_le (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
    (f := value u) (g := f) (h := f) (hnull.mono fun _ h ↦ h.elim)
  simp only [zero_mul, add_zero] at hd hv
  rw [le_antisymm hv (norm_nonneg _), mul_zero, add_zero]
  exact hd.trans (norm_nonneg f)

/-- An almost everywhere bound `Λ` on the operators `A t` over `(a, b)` is nonnegative. -/
private theorem nonneg_of_ae_norm_le (hab : a < b)
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) : 0 ≤ Λ :=
  nonneg_of_ae_restrict_abs_le (s := Ioo a b) (g := fun t ↦ ‖A t‖) (by simp [hab])
    (hA_bound.mono fun t ht ↦ (abs_norm (A t)).trans_le ht)

variable [CompleteSpace V] [CompleteSpace H]

/-- **Uniqueness in the energy space.** Let `A(t)` satisfy Gårding's inequality
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0` and `β ≥ 0` for almost every `t ∈ (a, b)`. Two
elements of the energy space solving `u' + A(t) u = f` on `(a, b)` with the same initial value
`u(a)` coincide. -/
theorem eq_of_ae_timeDeriv_add_eq (hab : a < b) (hα : 0 < α) (hβ : 0 ≤ β)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    {f : ℝ → StrongDual ℝ V}
    (hu : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = f t)
    (hv : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv v t + A t (value v t) = f t)
    (h₀ : toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ =
      toContinuousMap hab v ⟨a, left_mem_Icc.2 hab.le⟩) :
    u = v :=
  ext <| Lp.ext <| (hasWeakLineDerivOn u).ae_eq_of_gelfandDual (hasWeakLineDerivOn v)
    (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) hα hβ hA_garding hu hv
    ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousOn
    (value_ae_eq_toContinuousMap hab u)
    ((toContinuousMap hab v).continuous.comp continuous_projIcc).continuousOn
    (value_ae_eq_toContinuousMap hab v)
    (by simpa only [Function.comp_apply, projIcc_left] using h₀)

/-- The energy estimate at time `t` for an element of the energy space solving
`u' + A(t) u = f`. -/
private theorem norm_sq_add_mul_integral_le (hab : a < b) (hα : 0 < α) (hβ : 0 ≤ β)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    {f : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))}
    (hu : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = f t)
    (t : Icc a b) :
    ‖toContinuousMap hab u t‖ ^ 2 + α * ∫ s in a..t, ‖value u s‖ ^ 2 ≤
      exp (2 * β * (t - a)) *
        (‖toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩‖ ^ 2 +
          α⁻¹ * ∫ s in a..t, ‖f s‖ ^ 2) := by
  simpa only [Function.comp_apply, projIcc_of_mem hab.le t.property, projIcc_left] using
    (hasWeakLineDerivOn u).norm_sq_add_mul_integral_le_of_gelfandDual (Lp.memLp _) (Lp.memLp _)
      (Lp.memLp f) hα hβ hA_garding hu
      ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousOn
      (value_ae_eq_toContinuousMap hab u) t.property

/-- **The energy estimate in `L²(a, b; V)`.** Under Gårding's inequality
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0` and `β ≥ 0`, every element of the energy space solving
`u' + A(t) u = f` on `(a, b)` satisfies
`‖u‖²_{L²(a, b; V)} ≤ e^{2β(b - a)} (‖u(a)‖² + α⁻¹ ‖f‖²) / α`. -/
theorem norm_value_sq_le_of_ae_timeDeriv_add_eq (hab : a < b) (hα : 0 < α) (hβ : 0 ≤ β)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    {f : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))}
    (hu : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = f t) :
    ‖value u‖ ^ 2 ≤
      exp (2 * β * (b - a)) *
        (‖toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2) / α := by
  have h := norm_sq_add_mul_integral_le hab hα hβ hA_garding hu ⟨b, right_mem_Icc.2 hab.le⟩
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
    Lp.integral_norm_sq_eq_norm_sq] at h
  have hf : ∫ s in a..b, ‖f s‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    exact Lp.setIntegral_norm_sq_le_norm_sq f subset_rfl
  rw [le_div_iff₀ hα]
  calc ‖value u‖ ^ 2 * α
      ≤ exp (2 * β * (b - a)) * (‖toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩‖ ^ 2 +
          α⁻¹ * ∫ s in a..b, ‖f s‖ ^ 2) := by
        nlinarith [sq_nonneg ‖toContinuousMap hab u ⟨b, right_mem_Icc.2 hab.le⟩‖]
    _ ≤ _ := by gcongr

/-- **The energy estimate in `C([a, b]; H)`.** Under Gårding's inequality
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0` and `β ≥ 0`, every element of the energy space solving
`u' + A(t) u = f` on `(a, b)` has its continuous representative bounded by
`sup_{t ∈ [a, b]} ‖u(t)‖² ≤ e^{2β(b - a)} (‖u(a)‖² + α⁻¹ ‖f‖²)`. -/
theorem norm_toContinuousMap_sq_le_of_ae_timeDeriv_add_eq (hab : a < b) (hα : 0 < α)
    (hβ : 0 ≤ β)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    {f : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))}
    (hu : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = f t) :
    ‖toContinuousMap hab u‖ ^ 2 ≤
      exp (2 * β * (b - a)) *
        (‖toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2) := by
  set R := exp (2 * β * (b - a)) *
    (‖toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩‖ ^ 2 + α⁻¹ * ‖f‖ ^ 2)
  have hR : 0 ≤ R := by positivity
  have hpt (t : Icc a b) : ‖toContinuousMap hab u t‖ ^ 2 ≤ R := by
    have h := norm_sq_add_mul_integral_le hab hα hβ hA_garding hu t
    have hu2 : 0 ≤ α * ∫ s in a..t, ‖value u s‖ ^ 2 :=
      mul_nonneg hα.le (intervalIntegral.integral_nonneg t.property.1 fun _ _ ↦ by positivity)
    have hf2 : 0 ≤ ∫ s in a..t, ‖f s‖ ^ 2 :=
      intervalIntegral.integral_nonneg t.property.1 fun _ _ ↦ by positivity
    have hexp : exp (2 * β * (t - a)) ≤ exp (2 * β * (b - a)) :=
      exp_le_exp.2 (by nlinarith [t.property.2])
    calc ‖toContinuousMap hab u t‖ ^ 2
        ≤ exp (2 * β * (t - a)) * (‖toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩‖ ^ 2 +
            α⁻¹ * ∫ s in a..t, ‖f s‖ ^ 2) := by linarith
      _ ≤ R :=
        mul_le_mul hexp (by
            gcongr
            rw [intervalIntegral.integral_of_le t.property.1, integral_Ioc_eq_integral_Ioo]
            exact Lp.setIntegral_norm_sq_le_norm_sq f (Ioo_subset_Ioo_right t.property.2))
          (add_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.2 hα.le) hf2)) (exp_pos _).le
  have hle : ‖toContinuousMap hab u‖ ≤ √R :=
    (ContinuousMap.norm_le _ (sqrt_nonneg R)).2 fun t ↦ by
      simpa only [abs_norm] using abs_le_sqrt (hpt t)
  calc ‖toContinuousMap hab u‖ ^ 2 ≤ √R ^ 2 := by gcongr
    _ = R := sq_sqrt hR

end Estimates

section Existence

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SeparableSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : V →L[ℝ] H} {A : ℝ → V →L[ℝ] StrongDual ℝ V} {a b α β Λ : ℝ}

/-- **Well-posedness in the energy space.** Let `V ↪ H ↪ V*` be a Gelfand triple, given by
`ι : V →L[ℝ] H` with dense range, `V` separable. Let `A(t) : V →L[ℝ] V*` be weakly measurable,
essentially bounded by `Λ` and satisfy Gårding's inequality `α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with
`α > 0` and `β ≥ 0`, for almost every `t ∈ (a, b)`. Then for every `u₀ ∈ H` and
`f ∈ L²(a, b; V*)` exactly one element of the energy space `L²(a, b; V) ∩ H¹(a, b; V*)` solves
`u' + A(t) u = f` on `(a, b)`, `u(a) = u₀`. -/
theorem existsUnique_ae_timeDeriv_add_eq (hι : DenseRange ι) (hab : a < b)
    (hA : ∀ u v, AEStronglyMeasurable (fun t ↦ A t u v) (volume.restrict (Ioo a b)))
    (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (hα : 0 < α) (hβ : 0 ≤ β)
    (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)
    (u₀ : H) (f : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    ∃! u : EvolutionSpace ι a b,
      (∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = f t) ∧
        toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = u₀ := by
  obtain ⟨u, w, hu, hg, hd, hw, hae, hw₀⟩ :=
    exists_hasWeakLineDerivOn_gelfandDual hι hab.le hA hA_bound hα hA_garding (Lp.memLp f) u₀
  -- The weak solution, with its weak time derivative, is an element of the energy space.
  have hd' : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ ι.gelfandDual (ι (hu.toLp u t))) (hg.toLp _) 1 :=
    (hd.congr_ae (hu.coeFn_toLp.fun_comp fun x ↦ ι.gelfandDual (ι x)).symm).congr_ae_deriv
      hg.coeFn_toLp.symm
  set U : EvolutionSpace ι a b := mk (hu.toLp u) (hg.toLp _) hd'
  have hU : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv U t + A t (value U t) = f t := by
    filter_upwards [hu.coeFn_toLp, hg.coeFn_toLp] with t hut hgt
    rw [timeDeriv_mk, value_mk, hgt, hut, sub_add_cancel]
  -- Its continuous representative is `w`, which starts at `u₀`.
  have hU₀ : toContinuousMap hab U ⟨a, left_mem_Icc.2 hab.le⟩ = u₀ := by
    have hW : toContinuousMap hab U = ⟨fun t ↦ w t, hw.domRestrict⟩ := by
      rw [toContinuousMap_eq_iff, value_mk]
      filter_upwards [hu.coeFn_toLp, hae, ae_restrict_mem measurableSet_Ioo] with t hut ht hmem
      rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem), hut]
      exact ht
    rw [hW]
    exact hw₀
  exact ⟨U, ⟨hU, hU₀⟩, fun v hv ↦
    eq_of_ae_timeDeriv_add_eq hab hα hβ hA_garding hv.1 hU (hv.2.trans hU₀.symm)⟩

variable (hι : DenseRange ι) (hab : a < b)
  (hA : ∀ u v, AEStronglyMeasurable (fun t ↦ A t u v) (volume.restrict (Ioo a b)))
  (hA_bound : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ Λ) (hα : 0 < α) (hβ : 0 ≤ β)
  (hA_garding : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ v, α * ‖v‖ ^ 2 - β * ‖ι v‖ ^ 2 ≤ A t v v)

/-- The solution of `u' + A(t) u = f`, `u(a) = u₀`, for the data `p = (u₀, f)`. -/
private def parabolicSolution (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    EvolutionSpace ι a b :=
  (existsUnique_ae_timeDeriv_add_eq hι hab hA hA_bound hα hβ hA_garding p.1 p.2).exists.choose

private theorem parabolicSolution_spec
    (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    (∀ᵐ t ∂volume.restrict (Ioo a b),
      timeDeriv (parabolicSolution hι hab hA hA_bound hα hβ hA_garding p) t +
        A t (value (parabolicSolution hι hab hA hA_bound hα hβ hA_garding p) t) = p.2 t) ∧
      toContinuousMap hab (parabolicSolution hι hab hA hA_bound hα hβ hA_garding p)
        ⟨a, left_mem_Icc.2 hab.le⟩ = p.1 :=
  (existsUnique_ae_timeDeriv_add_eq hι hab hA hA_bound hα hβ hA_garding p.1 p.2).exists.choose_spec

private theorem eq_parabolicSolution
    (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) {u : EvolutionSpace ι a b}
    (hu : ∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = p.2 t)
    (hu₀ : toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = p.1) :
    u = parabolicSolution hι hab hA hA_bound hα hβ hA_garding p :=
  eq_of_ae_timeDeriv_add_eq hab hα hβ hA_garding hu
    (parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding p).1
    (hu₀.trans (parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding p).2.symm)

/-- The solution map `(u₀, f) ↦ u` as a linear map, before its continuity is proved. -/
private def parabolicSolutionₗ :
    (H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) →ₗ[ℝ] EvolutionSpace ι a b where
  toFun := parabolicSolution hι hab hA hA_bound hα hβ hA_garding
  map_add' p q := by
    set U := parabolicSolution hι hab hA hA_bound hα hβ hA_garding p
    set W := parabolicSolution hι hab hA hA_bound hα hβ hA_garding q
    obtain ⟨hp, hp₀⟩ := parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding p
    obtain ⟨hq, hq₀⟩ := parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding q
    refine (eq_parabolicSolution hι hab hA hA_bound hα hβ hA_garding (p + q) ?_ ?_).symm
    · filter_upwards [hp, hq, Lp.coeFn_add (timeDeriv U) (timeDeriv W),
        Lp.coeFn_add (value U) (value W), Lp.coeFn_add p.2 q.2] with t hpt hqt hd hv hf
      rw [timeDeriv_add, value_add, Prod.snd_add, hd, hv, hf, Pi.add_apply, Pi.add_apply,
        Pi.add_apply, map_add, ← hpt, ← hqt]
      abel
    · rw [map_add, ContinuousMap.add_apply, hp₀, hq₀, Prod.fst_add]
  map_smul' c p := by
    set U := parabolicSolution hι hab hA hA_bound hα hβ hA_garding p
    obtain ⟨hp, hp₀⟩ := parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding p
    refine (eq_parabolicSolution hι hab hA hA_bound hα hβ hA_garding (c • p) ?_ ?_).symm
    · filter_upwards [hp, Lp.coeFn_smul c (timeDeriv U), Lp.coeFn_smul c (value U),
        Lp.coeFn_smul c p.2] with t hpt hd hv hf
      rw [RingHom.id_apply, timeDeriv_smul, value_smul, Prod.smul_snd, hd, hv, hf, Pi.smul_apply,
        Pi.smul_apply, Pi.smul_apply, map_smul, ← hpt, smul_add]
    · rw [RingHom.id_apply, map_smul, ContinuousMap.smul_apply, hp₀, Prod.smul_fst]

private theorem parabolicSolutionₗ_apply
    (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    parabolicSolutionₗ hι hab hA hA_bound hα hβ hA_garding p =
      parabolicSolution hι hab hA hA_bound hα hβ hA_garding p :=
  (rfl)

/-- The operator norm bound of the solution map, from the energy estimate. -/
private theorem norm_parabolicSolutionₗ_apply_le
    (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    ‖parabolicSolutionₗ hι hab hA hA_bound hα hβ hA_garding p‖ ≤
      (1 + (1 + Λ) * √(exp (2 * β * (b - a)) * (1 + α⁻¹) / α)) * ‖p‖ := by
  rw [parabolicSolutionₗ_apply]
  set u := parabolicSolution hι hab hA hA_bound hα hβ hA_garding p
  obtain ⟨hu, hu₀⟩ := parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding p
  have hΛ := nonneg_of_ae_norm_le hab hA_bound
  have h₁ : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h₂ : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  -- The `L²(a, b; V)` part, by the energy estimate.
  have hval : ‖value u‖ ≤ √(exp (2 * β * (b - a)) * (1 + α⁻¹) / α) * ‖p‖ := by
    have h := norm_value_sq_le_of_ae_timeDeriv_add_eq hab hα hβ hA_garding hu
    rw [hu₀] at h
    have h' : ‖value u‖ ^ 2 ≤ exp (2 * β * (b - a)) * (1 + α⁻¹) / α * ‖p‖ ^ 2 := by
      have hp : ‖p.1‖ ^ 2 + α⁻¹ * ‖p.2‖ ^ 2 ≤ (1 + α⁻¹) * ‖p‖ ^ 2 := by
        have h₁' := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
        have h₂' := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
        nlinarith [inv_pos.2 hα]
      refine h.trans ?_
      calc _ ≤ exp (2 * β * (b - a)) * ((1 + α⁻¹) * ‖p‖ ^ 2) / α := by gcongr
        _ = _ := by ring
    calc ‖value u‖ = √(‖value u‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
      _ ≤ √(exp (2 * β * (b - a)) * (1 + α⁻¹) / α * ‖p‖ ^ 2) := sqrt_le_sqrt h'
      _ = _ := by rw [sqrt_mul (by positivity), sqrt_sq (norm_nonneg _)]
  -- The time derivative, from the equation.
  have hder := norm_timeDeriv_le_of_ae_timeDeriv_add_eq hA_bound hu
  have hsum := norm_le_norm_value_add_norm_timeDeriv u
  nlinarith [norm_nonneg p]

/-- **The solution operator of a linear parabolic equation.** Let `V ↪ H ↪ V*` be a Gelfand
triple, given by `ι : V →L[ℝ] H` with dense range, `V` separable, and let `A(t) : V →L[ℝ] V*` be
weakly measurable, essentially bounded by `Λ` and satisfy Gårding's inequality
`α ‖v‖² - β ‖ι v‖² ≤ A(t) v v` with `α > 0` and `β ≥ 0`, for almost every `t ∈ (a, b)`. This is the
bounded linear map sending `(u₀, f) ∈ H × L²(a, b; V*)` to the unique element `u` of the energy
space solving `u' + A(t) u = f` on `(a, b)` with `u(a) = u₀`
(`TauCeti.EvolutionSpace.eq_parabolicSolutionL_iff`). -/
def parabolicSolutionL :
    (H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) →L[ℝ] EvolutionSpace ι a b :=
  (parabolicSolutionₗ hι hab hA hA_bound hα hβ hA_garding).mkContinuous _
    (norm_parabolicSolutionₗ_apply_le hι hab hA hA_bound hα hβ hA_garding)

private theorem parabolicSolutionL_apply
    (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    parabolicSolutionL hι hab hA hA_bound hα hβ hA_garding p =
      parabolicSolution hι hab hA hA_bound hα hβ hA_garding p :=
  (LinearMap.mkContinuous_apply ..).trans (parabolicSolutionₗ_apply ..)

/-- The image of `(u₀, f)` under the solution operator solves `u' + A(t) u = f` on `(a, b)`. -/
theorem ae_timeDeriv_parabolicSolutionL_add_eq
    (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      timeDeriv (parabolicSolutionL hι hab hA hA_bound hα hβ hA_garding p) t +
        A t (value (parabolicSolutionL hι hab hA hA_bound hα hβ hA_garding p) t) = p.2 t := by
  simpa only [parabolicSolutionL_apply] using
    (parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding p).1

/-- The image of `(u₀, f)` under the solution operator starts at `u₀`. -/
@[simp]
theorem toContinuousMap_parabolicSolutionL_left
    (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) :
    toContinuousMap hab (parabolicSolutionL hι hab hA hA_bound hα hβ hA_garding p)
      ⟨a, left_mem_Icc.2 hab.le⟩ = p.1 := by
  simpa only [parabolicSolutionL_apply] using
    (parabolicSolution_spec hι hab hA hA_bound hα hβ hA_garding p).2

/-- **Characterization of the solution operator.** An element of the energy space is the image of
`(u₀, f)` under the solution operator exactly when it solves `u' + A(t) u = f` on `(a, b)` with
`u(a) = u₀`. -/
theorem eq_parabolicSolutionL_iff (p : H × Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b)))
    (u : EvolutionSpace ι a b) :
    u = parabolicSolutionL hι hab hA hA_bound hα hβ hA_garding p ↔
      (∀ᵐ t ∂volume.restrict (Ioo a b), timeDeriv u t + A t (value u t) = p.2 t) ∧
        toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = p.1 := by
  refine ⟨?_, fun hu ↦ eq_of_ae_timeDeriv_add_eq hab hα hβ hA_garding hu.1
    (ae_timeDeriv_parabolicSolutionL_add_eq hι hab hA hA_bound hα hβ hA_garding p)
    (hu.2.trans (toContinuousMap_parabolicSolutionL_left hι hab hA hA_bound hα hβ hA_garding
      p).symm)⟩
  rintro rfl
  exact ⟨ae_timeDeriv_parabolicSolutionL_add_eq hι hab hA hA_bound hα hβ hA_garding p,
    toContinuousMap_parabolicSolutionL_left hι hab hA hA_bound hα hβ hA_garding p⟩

/-- **The solution operator is bounded**, with operator norm at most
`1 + (1 + Λ) √(e^{2β(b - a)} (1 + α⁻¹) / α)`, where `H × L²(a, b; V*)` carries the maximum of the
two norms and the energy space its graph norm. -/
theorem norm_parabolicSolutionL_le :
    ‖parabolicSolutionL hι hab hA hA_bound hα hβ hA_garding‖ ≤
      1 + (1 + Λ) * √(exp (2 * β * (b - a)) * (1 + α⁻¹) / α) := by
  have hΛ := nonneg_of_ae_norm_le hab hA_bound
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end Existence

end EvolutionSpace

end TauCeti
