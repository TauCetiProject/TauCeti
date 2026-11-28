/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.DirichletProblem
public import TauCeti.Analysis.PDE.Parabolic.SolutionOperator
public import TauCeti.Analysis.Sobolev.EvolutionSpace.InitialValue
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Operator.EssentialLimit
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The pivot space is the sharp target of the energy space

Let `V ↪ H ↪ V*` be a Gelfand triple, given by `ι : V →L[ℝ] H` with dense range from a separable
real Hilbert space `V`. Every element of the energy space
`TauCeti.EvolutionSpace ι a b = L²(a, b; V) ∩ H¹(a, b; V*)` has a representative in `C([a, b]; H)`
(`TauCeti.EvolutionSpace.toContinuousMap`), which is how initial values of parabolic equations make
sense. This file shows that `H` cannot be replaced by `V`.

* **Every initial value occurs.** For every `u₀ ∈ H` some element of the energy space starts at
  `u₀` (`TauCeti.EvolutionSpace.exists_toContinuousMap_left_eq`): the solution of
  `u' + A u = 0`, `u(a) = u₀`, for the Riesz map `A : V → V*` of the inner product of `V`.
* **Blow-up.** If `ι` is not surjective, some element of the energy space satisfies
  `‖u(t)‖_V → ∞` as `t → a⁺`, outside a null set
  (`TauCeti.EvolutionSpace.exists_tendsto_norm_value_atTop`): its initial value lies outside
  `ι V`, so `TauCeti.EvolutionSpace.tendsto_norm_value_atTop` applies.
* **Characterization.** For injective `ι`, every element of the energy space has a representative
  in `C([a, b]; V)` exactly when `ι` is surjective, that is, when `V = H` up to an isomorphism
  (`TauCeti.EvolutionSpace.forall_exists_continuousOn_ae_eq_iff`).

For the heat equation on an open set `Ω ⊆ ℝ^{n+1}` with zero boundary values, the triple is
`H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)`. If `Ω` is bounded and nonempty, the value map `H¹₀(Ω) → L²(Ω)` is not
onto (`TauCeti.W1p0.not_surjective_valueL`): nonzero constants lie in `L²(Ω)` but not in `H¹₀(Ω)`.
For every initial value `u₀ ∈ L²(Ω)` outside `H¹₀(Ω)`, the weak solution of `∂ₜu - Δu = 0`,
`u(0) = u₀`, lies in `L²(0, T; H¹₀(Ω))` with `u' ∈ L²(0, T; H⁻¹(Ω))` and is continuous into
`L²(Ω)`, but `‖u(t)‖_{H¹₀(Ω)} → ∞` as `t → 0⁺`, outside a null set of times
(`TauCeti.PDE.exists_hasWeakLineDerivOn_gelfandDual_energyFormH1_and_tendsto_norm_atTop`), so it
is not continuous into `H¹₀(Ω)`. For the explicit series `Σ_k e^{-k²t} sin(kx)/k` on `(0, π)` the
norm tends to infinity pointwise; the limit here is only essential, but it holds for every initial
value outside `H¹₀(Ω)`. The blow-up does not depend on the equation: it holds for every function
whose `L²(Ω)`-valued continuous representative starts outside `H¹₀(Ω)`
(`TauCeti.tendsto_norm_atTop_of_eventuallyEq_of_notMem_range`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 3, and §7.1.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Set Topology TopologicalSpace NormedSpace

namespace EvolutionSpace

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SeparableSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : V →L[ℝ] H} {a b : ℝ}

/-- **Every initial value occurs in the energy space.** For a Gelfand triple `V ↪ H ↪ V*`, given by
`ι : V →L[ℝ] H` with dense range, `V` separable, every `u₀ ∈ H` is the initial value of some
element of the energy space `L²(a, b; V) ∩ H¹(a, b; V*)`. -/
theorem exists_toContinuousMap_left_eq (hι : DenseRange ι) (hab : a < b) (u₀ : H) :
    ∃ u : EvolutionSpace ι a b, toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ = u₀ :=
  -- The solution of `u' + A u = 0` for the Riesz map `A` of `V`, coercive with constant `1`.
  ⟨parabolicSolutionL hι hab (A := fun _ ↦ innerSL ℝ) (fun _ _ ↦ aestronglyMeasurable_const)
      (Eventually.of_forall fun _ ↦ norm_innerSL_le ℝ) one_pos le_rfl
      (Eventually.of_forall fun _ v ↦ by
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
        simp) (u₀, 0),
    toContinuousMap_parabolicSolutionL_left ..⟩

/-- **The pivot space is the sharp target.** For a Gelfand triple `V ↪ H ↪ V*` whose inclusion
`ι : V →L[ℝ] H` is not surjective, some element `u` of the energy space `L²(a, b; V) ∩ H¹(a, b; V*)`
satisfies `‖u(t)‖_V → ∞` as `t → a⁺`, outside a null set; in particular it is not continuous into
`V` (`TauCeti.EvolutionSpace.not_exists_continuousWithinAt_ae_eq`). -/
theorem exists_tendsto_norm_value_atTop (hι : DenseRange ι) (hab : a < b)
    (hsurj : ¬ Function.Surjective ι) :
    ∃ u : EvolutionSpace ι a b,
      Tendsto (fun t ↦ ‖value u t‖) (𝓝[>] a ⊓ ae volume) atTop := by
  obtain ⟨u₀, hu₀⟩ := not_forall.1 hsurj
  obtain ⟨u, hu⟩ := exists_toContinuousMap_left_eq hι hab u₀
  exact ⟨u, tendsto_norm_value_atTop
    (surjective_inclusionInDoubleDual_of_innerProductSpace (𝕜 := ℝ)) hab u (hu ▸ hu₀)⟩

/-- **When the energy space lies in `C([a, b]; V)`.** For a Gelfand triple `V ↪ H ↪ V*` with
injective inclusion `ι`, every element of the energy space `L²(a, b; V) ∩ H¹(a, b; V*)` has a
representative continuous on `[a, b]` with values in `V` if and only if `ι` is surjective, that is,
if and only if `ι` is an isomorphism of `V` onto `H`. -/
theorem forall_exists_continuousOn_ae_eq_iff (hι : DenseRange ι) (hinj : Function.Injective ι)
    (hab : a < b) :
    (∀ u : EvolutionSpace ι a b, ∃ v : ℝ → V, ContinuousOn v (Icc a b) ∧
      value u =ᵐ[volume.restrict (Ioo a b)] v) ↔ Function.Surjective ι := by
  refine ⟨fun h ↦ by_contra fun hsurj ↦ ?_, fun hsurj u ↦ ?_⟩
  · obtain ⟨u₀, hu₀⟩ := not_forall.1 hsurj
    obtain ⟨u, hu⟩ := exists_toContinuousMap_left_eq hι hab u₀
    obtain ⟨v, hv, huv⟩ := h u
    exact not_exists_continuousWithinAt_ae_eq hab u (hu ▸ hu₀)
      ⟨v, (hv a (left_mem_Icc.2 hab.le)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hab), huv⟩
  · -- By the open mapping theorem `ι` is an isomorphism; pull the continuous trace back to `V`.
    let e : V ≃L[ℝ] H :=
      .ofBijective ι (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj)
    refine ⟨fun t ↦ e.symm (toContinuousMap hab u (projIcc a b hab.le t)),
      (e.symm.continuous.comp ((toContinuousMap hab u).continuous.comp
        continuous_projIcc)).continuousOn, ?_⟩
    filter_upwards [value_ae_eq_toContinuousMap hab u] with t ht
    rw [← ht, ContinuousLinearEquiv.ofBijective_symm_apply_apply]

end EvolutionSpace

namespace PDE

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- **The heat equation leaves `H¹₀` at time zero.** Let `Ω ⊆ ℝ^{n+1}` be open, `T > 0`, and let
`u₀ ∈ L²(Ω)` lie outside `H¹₀(Ω)`, for instance a nonzero constant when `Ω` is bounded and nonempty
(`TauCeti.W1p.const_notMem_w1p0Submodule`). The weak solution of the heat equation
`∂ₜu - Δu = 0` in `(0, T) × Ω` with zero boundary values and initial value `u₀` lies in
`L²(0, T; H¹₀(Ω))`, its image in `H⁻¹(Ω)` has a weak time derivative `u' ∈ L²(0, T; H⁻¹(Ω))`, and
`t ↦ u(t) ∈ L²(Ω)` has a representative `w` continuous on `[0, T]` with `w(0) = u₀`. Yet
`‖u(t)‖_{H¹₀(Ω)} → ∞` as `t → 0⁺`, outside a null set. So `L²(Ω)`, not `H¹₀(Ω)`, is the space in
which such solutions are continuous up to `t = 0`. -/
theorem exists_hasWeakLineDerivOn_gelfandDual_energyFormH1_and_tendsto_norm_atTop {T : ℝ}
    (hT : 0 < T) {u₀ : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hu₀ : u₀ ∉ range (W1p0.valueL (mu := volume) (Omega := Omega) (p := 2))) :
    ∃ u : ℝ → W1p0 volume Omega 2, ∃ u' : ℝ → StrongDual ℝ (W1p0 volume Omega 2),
      ∃ w : ℝ → Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))),
      MemLp u 2 (volume.restrict (Ioo 0 T)) ∧ MemLp u' 2 (volume.restrict (Ioo 0 T)) ∧
      HasWeakLineDerivOn volume ⟨Ioo 0 T, isOpen_Ioo⟩
        (fun t ↦ (W1p0.valueL (mu := volume) (Omega := Omega) (p := 2)).gelfandDual
          (W1p0.valueL (u t))) u' 1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T), ∀ v : W1p0 volume Omega 2,
        u' t v + energyFormH1 (fun _ ↦ 1) 0 0 (u t : W1p volume Omega 2)
          (v : W1p volume Omega 2) = 0) ∧
      ContinuousOn w (Icc 0 T) ∧
      (fun t ↦ W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo 0 T)] w ∧ w 0 = u₀ ∧
      Tendsto (fun t ↦ ‖u t‖) (𝓝[>] 0 ⊓ ae volume) atTop := by
  obtain ⟨u, u', w, hu, hu', hd, heq, hw, hae, hw₀⟩ :=
    exists_hasWeakLineDerivOn_gelfandDual_energyFormH1 (a := fun _ _ ↦ 1) (b := fun _ _ ↦ 0)
      (c := fun _ _ ↦ 0) (lam := 1) (Lam := 1) (beta := 0) (gamma := 0) hT
      aestronglyMeasurable_const aestronglyMeasurable_const aestronglyMeasurable_const
      (Eventually.of_forall fun _ ↦ uniformlyEllipticOn_const_one_one _)
      (Eventually.of_forall fun _ _ _ ↦ by simp) (Eventually.of_forall fun _ _ _ ↦ by simp)
      (memLp_const (0 : StrongDual ℝ (W1p0 volume Omega 2))) u₀
  refine ⟨u, u', w, hu, hu', hd, heq, hw, hae, hw₀, ?_⟩
  -- `w` represents `u` at almost every time close to `0` on the right.
  have hae' : ∀ᶠ t in 𝓝[>] 0 ⊓ ae volume, W1p0.valueL (u t) = w t :=
    hae.filter_mono (nhdsGT_inf_ae_le_ae_restrict_Ioo hT)
  exact tendsto_norm_atTop_of_eventuallyEq_of_notMem_range
    (surjective_inclusionInDoubleDual_of_innerProductSpace (𝕜 := ℝ))
    ((hw 0 (left_mem_Icc.2 hT.le)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hT)) hae' (hw₀ ▸ hu₀)

end PDE

end TauCeti
