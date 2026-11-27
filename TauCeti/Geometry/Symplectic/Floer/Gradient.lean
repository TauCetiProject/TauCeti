/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Floer equation as a gradient flow, and its reflection

Let `(V, ω)` be a symplectic vector space and `H : ℝ → V → ℝ` a time-dependent Hamiltonian, with
Hamiltonian vector fields `X_t = X_{H_t}`, `ω(X_t, ·) = dH_t`. The action
`A_H(γ) = ½ ∫₀¹ ω(γ, γ') dt + ∫₀¹ H_t(γ) dt` of a loop (`TauCeti.SymplecticForm.hamiltonianAction`)
has first variation

`d/dε A_H(γ + ε ξ) |_{ε = 0} = ∫₀¹ ω(ξ, γ' - X_t(γ)) dt`

along every periodic variation `ξ` (`SymplecticForm.hasDerivAt_hamiltonianAction_add_smul`), so the
`1`-periodic orbits of `X` are its critical points. On a manifold, the action
`TauCeti.contractibleLoopAction` of contractible loops, a cap area minus `∫₀¹ H_t(γ) dt`, has its
own first variation formula,
`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`.

Two opposite conventions turn this first variation into a gradient. Let `J` be an almost complex
structure such that `-J` is tamed by `ω`, so that `g(v, w) = ω(v, -J w)` is positive on the
diagonal. Since `-J J = 1`,

`ω(ξ, γ' - X_t(γ)) = g(ξ, J (γ' - X_t(γ)))`

(`SymplecticForm.hasDerivAt_hamiltonianAction_add_smul_associatedBilinForm`): when `-J` is
compatible with `ω`, `J (γ' - X(γ))` is the `L²` gradient of the action for the metric `g`, and the
gradient of the Hamiltonian term is `-J X_t`
(`SymplecticForm.associatedBilinForm_neg_apply_neg_hamiltonianVectorField`). Its negative gradient
flow is the Floer equation

`∂_s u + J (∂_t u - X_t(u)) = 0`

with the structure `J` whose *negative* is tamed. This is the convention of Floer–Novikov theory in
which the action decreases along cylinders and the input is the negative end. The standard
convention of `TauCeti.Geometry.Symplectic.Floer.Action` uses a tamed structure, the action
increases, and the input is the positive end.

The two are exchanged by the reflection `(s, t) ↦ (-s, t)`: `u` solves the equation for `J` at
`(-s, t)` exactly when `v(s, t) = u(-s, t)` solves it for `-J` at `(s, t)`
(`SymplecticForm.fderiv_comp_neg_fst_add_neg_apply_eq_zero_iff`), and the energy density of `v`
is minus that of `u` at the reflected point
(`SymplecticForm.floerEnergyDensity_comp_neg_fst`). So along a solution for `J` with `-J` tamed,
the action decreases (`SymplecticForm.antitone_hamiltonianAction_of_floer_neg_tames`) and the
energy `∫ ω(∂_t u - X(u), ∂_s u)`, nonnegative because `-J` is tamed, is the drop of the action
between the two ends
(`SymplecticForm.lintegral_neg_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`):

`E(u) = A_H(x₋) - A_H(x₊)`,

where `x₋` and `x₊` are the ends at `s → -∞` and `s → ∞`.

## Main results

* `SymplecticForm.hasDerivAt_hamiltonianAction_add_smul`: the first variation of the action.
* `SymplecticForm.hasDerivAt_hamiltonianAction_add_smul_associatedBilinForm`: the first
  variation as the pairing with `J (γ' - X(γ))` for the bilinear form `ω(·, -J ·)`.
* `SymplecticForm.fderiv_comp_neg_fst_add_neg_apply_eq_zero_iff`: the reflection exchanges the
  Floer equations for `J` and `-J`.
* `SymplecticForm.floerEnergyDensity_comp_neg_fst`: the reflection negates the energy density.
* `SymplecticForm.antitone_hamiltonianAction_of_floer_neg_tames`: the action decreases along a
  solution of the Floer equation for `J` when `-J` is tamed.
* `SymplecticForm.lintegral_neg_floerEnergyDensity_eq_of_tendsto_hamiltonianAction`: the energy of
  such a solution on the whole cylinder is the action at the negative end minus the action at the
  positive end.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, the action functional and its gradient flow.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, arXiv:math/0111313, the downward gradient flow of the action in Floer–Novikov theory.
-/

public section

open Function MeasureTheory Set Filter Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Variation

variable {γ ξ : ℝ → V}

/-- **The first variation of the action.** Let `H` be a `C¹` time-dependent Hamiltonian, and let
`γ` and `ξ` be `C¹` loops, `γ 1 = γ 0` and `ξ 1 = ξ 0`. The action of the loop `γ + ε ξ` has
derivative

`∫₀¹ ω(ξ, γ' - X_{H_t}(γ)) dt`

at `ε = 0`. In particular `γ` is a critical point of the action along all periodic variations
when it is a `1`-periodic orbit of the Hamiltonian vector field. -/
theorem hasDerivAt_hamiltonianAction_add_smul (ω : SymplecticForm V) {H : ℝ → V → ℝ}
    (hH : ContDiff ℝ 1 (uncurry H)) (hγ : ContDiff ℝ 1 γ) (hξ : ContDiff ℝ 1 ξ)
    (hγ1 : γ 1 = γ 0) (hξ1 : ξ 1 = ξ 0) :
    HasDerivAt (fun ε : ℝ ↦ ω.hamiltonianAction H fun t ↦ γ t + ε • ξ t)
      (∫ t in (0 : ℝ)..1, ω (ξ t) (deriv γ t - ω.hamiltonianVectorField (H t) (γ t))) 0 := by
  -- Differentiate the Hamiltonian term under the integral sign.
  set G : ℝ × ℝ → ℝ := fun p ↦ H p.2 (γ p.2 + p.1 • ξ p.2)
  have hG : ContDiff ℝ 1 G :=
    hH.comp (contDiff_snd.prodMk ((hγ.comp contDiff_snd).add (contDiff_fst.smul
      (hξ.comp contDiff_snd))))
  obtain ⟨-, hHd⟩ := hasDerivAt_intervalIntegral_of_contDiffOn isOpen_univ hG.contDiffOn
    (subset_univ ({(0 : ℝ)} ×ˢ uIcc 0 1)) (x₀ := 0)
  have hslice (t : ℝ) :
      fderiv ℝ G (0, t) (1, 0) = ω (ω.hamiltonianVectorField (H t) (γ t)) (ξ t) := by
    have hHt : DifferentiableAt ℝ (H t) (γ t) :=
      ((hH.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero) (γ t)
    have hline : HasDerivAt (fun ε : ℝ ↦ G (ε, t)) (fderiv ℝ (H t) (γ t) (ξ t)) 0 := by
      have := hHt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
        (((hasDerivAt_id (0 : ℝ)).smul_const (ξ t)).const_add (γ t)) (by simp)
      simpa only [G, comp_def, id, one_smul] using this
    rw [(hasDerivAt_slice_left ((hG.differentiable one_ne_zero) (0, t))).unique hline,
      apply_hamiltonianVectorField]
  simp only [hslice] at hHd
  have hγX : Continuous fun t ↦ ω.hamiltonianVectorField (H t) (γ t) :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 0) (by simpa using hH)).continuous.comp
      (continuous_id.prodMk hγ.continuous)
  have h := (ω.hasDerivAt_loopArea_add_smul hγ hξ hγ1 hξ1).add hHd
  simp only [hamiltonianAction_def]
  convert h using 1
  rw [← intervalIntegral.integral_add
    ((ω.continuous_apply_comp hξ.continuous (hγ.continuous_deriv le_rfl)).intervalIntegrable _ _)
    ((ω.continuous_apply_comp hγX hξ.continuous).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [map_sub, ← ω.neg_eq (ω.hamiltonianVectorField (H t) (γ t))]
  ring

/-- **The first variation of the action as a gradient.** Under the hypotheses of
`TauCeti.SymplecticForm.hasDerivAt_hamiltonianAction_add_smul`, for every family `J t` of almost
complex structures the derivative of the action of `γ + ε ξ` at `ε = 0` is

`∫₀¹ g_t(ξ, J_t (γ' - X_{H_t}(γ))) dt`,  `g_t(v, w) = ω(v, -J_t w)`.

When `ω` is compatible with `-J_t`, `g_t` is an inner product and `J (γ' - X(γ))` is the `L²`
gradient of the action, so the Floer equation `∂_s u + J (∂_t u - X(u)) = 0` is its negative
gradient flow. -/
theorem hasDerivAt_hamiltonianAction_add_smul_associatedBilinForm (ω : SymplecticForm V)
    {H : ℝ → V → ℝ} (J : ℝ → AlmostComplexStructure V) (hH : ContDiff ℝ 1 (uncurry H))
    (hγ : ContDiff ℝ 1 γ) (hξ : ContDiff ℝ 1 ξ) (hγ1 : γ 1 = γ 0) (hξ1 : ξ 1 = ξ 0) :
    HasDerivAt (fun ε : ℝ ↦ ω.hamiltonianAction H fun t ↦ γ t + ε • ξ t)
      (∫ t in (0 : ℝ)..1, ω.associatedBilinForm (-J t) (ξ t)
        (J t (deriv γ t - ω.hamiltonianVectorField (H t) (γ t)))) 0 := by
  simpa only [associatedBilinForm_apply, AlmostComplexStructure.neg_apply,
    AlmostComplexStructure.apply_apply, neg_neg] using
    ω.hasDerivAt_hamiltonianAction_add_smul hH hγ hξ hγ1 hξ1

end Variation

section Reflection

variable {H : ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **Reflection exchanges the two Floer equations.** For `v(s, t) = u(-s, t)`, the map `v` solves
the Floer equation `∂_s v + (-J) (∂_t v - X_{H_t}(v)) = 0` at `z = (s, t)` exactly when `u` solves
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` at `(-s, t)`. -/
theorem fderiv_comp_neg_fst_add_neg_apply_eq_zero_iff (ω : SymplecticForm V)
    (J : AlmostComplexStructure V) (z : ℝ × ℝ) :
    fderiv ℝ (fun w ↦ u (-w.1, w.2)) z stdComplexLineReal +
        (-J) (fderiv ℝ (fun w ↦ u (-w.1, w.2)) z stdComplexLineImag -
          ω.hamiltonianVectorField (H z.2) (u (-z.1, z.2))) = 0 ↔
      fderiv ℝ u (-z.1, z.2) stdComplexLineReal +
        J (fderiv ℝ u (-z.1, z.2) stdComplexLineImag -
          ω.hamiltonianVectorField (H z.2) (u (-z.1, z.2))) = 0 := by
  simp only [stdComplexLineReal, stdComplexLineImag, fderiv_comp_neg_fst_apply_one_zero,
    fderiv_comp_neg_fst_apply_zero_one, AlmostComplexStructure.neg_apply, ← neg_add, neg_eq_zero]

/-- **Reflection negates the energy density.** For the cylindrical perturbation `K = H_t dt`, the
Floer energy density of `v(s, t) = u(-s, t)` at `z` is minus that of `u` at `(-z.1, z.2)`. -/
@[simp]
theorem floerEnergyDensity_comp_neg_fst (ω : SymplecticForm V) (z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (-w.1, w.2)) z =
      -ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (-z.1, z.2) := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag]
  simp only [stdComplexLineReal, stdComplexLineImag, fderiv_comp_neg_fst_apply_one_zero,
    fderiv_comp_neg_fst_apply_zero_one, hamiltonianVectorField_const, Pi.zero_apply, sub_zero,
    map_neg, LinearMap.neg_apply]

/-- **The action decreases along a Floer solution for a structure whose negative is tamed.** Let
`u` be a `C²` map with `1`-periodic loops solving `∂_s u + J_z (∂_t u - X_{H_t}(u)) = 0` on
`ℝ × [0, 1]`, where `-J_z` is tamed by `ω`. Then the action `A_H(u(s, ·))` is antitone in `s`. -/
theorem antitone_hamiltonianAction_of_floer_neg_tames (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hH : ContDiff ℝ 1 (uncurry H)) (hu : ContDiff ℝ 2 u)
    (hper : ∀ s, Periodic (fun t ↦ u (s, t)) 1)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (-J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    Antitone fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t)) := by
  -- The reflected map solves the standard Floer equation for the tamed structures `-J`.
  have hv := ω.monotone_hamiltonianAction_of_floer (u := fun w ↦ u (-w.1, w.2))
    (J := fun z ↦ -J (-z.1, z.2)) hH
    (hu.comp (contDiff_fst.neg.prodMk contDiff_snd))
    (fun s ↦ hper (-s)) (fun z hz ↦ hJ _ ⟨mem_univ _, hz.2⟩) fun z hz ↦ by
      rw [ω.isComplexLinearMap_perturbedFDeriv_iff]
      simpa [hamiltonianVectorField_const] using
        (ω.fderiv_comp_neg_fst_add_neg_apply_eq_zero_iff (H := H) (J (-z.1, z.2)) z).2
          (hfloer _ ⟨mem_univ _, hz.2⟩)
  intro s₁ s₂ hs
  simpa using hv (neg_le_neg hs)

/-- **The energy of a Floer cylinder for a structure whose negative is tamed.** Let `H` be a `C¹`
time-dependent Hamiltonian and `u` a `C²` map on an open neighbourhood `U` of `ℝ × [0, 1]`, with
`u(s, 1) = u(s, 0)`, solving `∂_s u + J_z (∂_t u - X_{H_t}(u)) = 0` there for almost complex
structures `J_z` whose negatives `-J_z` are tamed by `ω`. If the actions of the loops
`t ↦ u(s, t)` tend to `A₁` as `s → -∞` and to `A₂` as `s → ∞`, then the energy
`∫ ω(∂_t u - X(u), ∂_s u)`, the integral of minus the Floer energy density, is `A₁ - A₂`. -/
theorem lintegral_neg_floerEnergyDensity_eq_of_tendsto_hamiltonianAction (ω : SymplecticForm V)
    {J : ℝ × ℝ → AlmostComplexStructure V} {U : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (-J z)) (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hper : ∀ s, u (s, 1) = u (s, 0))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, fderiv ℝ u z stdComplexLineReal +
      J z (fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    {A₁ A₂ : ℝ}
    (hbot : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atBot (𝓝 A₁))
    (htop : Tendsto (fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t))) atTop (𝓝 A₂)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (-ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) =
      ENNReal.ofReal (A₁ - A₂) := by
  set r := LinearIsometryEquiv.negFst ℝ ℝ ℝ
  have hrU : r ⁻¹' ((univ : Set ℝ) ×ˢ Icc 0 1) = (univ : Set ℝ) ×ˢ Icc 0 1 := by
    ext z
    simp [r]
  -- The reflected map `v(s, t) = u(-s, t)` solves the standard Floer equation for the tamed
  -- structures `-J(-s, t)`, with the ends exchanged.
  have hv := ω.lintegral_floerEnergyDensity_eq_of_tendsto_hamiltonianAction
    (u := fun w ↦ u (-w.1, w.2)) (J := fun z ↦ -J (-z.1, z.2))
    (U := (fun w : ℝ × ℝ ↦ (-w.1, w.2)) ⁻¹' U)
    (fun z hz ↦ hJ _ ⟨mem_univ _, hz.2⟩) hH
    (hU.preimage (continuous_fst.neg.prodMk continuous_snd))
    (hu.comp (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn fun _ h ↦ h)
    (fun z hz ↦ hRU ⟨mem_univ _, hz.2⟩) (fun s ↦ hper (-s))
    (fun z hz ↦ (ω.fderiv_comp_neg_fst_add_neg_apply_eq_zero_iff (H := H) (J (-z.1, z.2)) z).2
      (hfloer _ ⟨mem_univ _, hz.2⟩))
    (A₁ := A₂) (A₂ := A₁) (by simpa [comp_def] using htop.comp tendsto_neg_atBot_atTop)
    (by simpa [comp_def] using hbot.comp tendsto_neg_atTop_atBot)
  -- The reflection preserves Lebesgue measure and the strip `ℝ × [0, 1]`.
  rw [← hv, ← LinearIsometryEquiv.measurePreserving_negFst.setLIntegral_comp_preimage_emb
    r.toHomeomorph.measurableEmbedding, hrU]
  refine setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc) fun z _ ↦ ?_
  simp

end Reflection

end TauCeti.SymplecticForm
