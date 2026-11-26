/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm
public import TauCeti.Geometry.Symplectic.Floer.Transversality.WeakCokernel
import TauCeti.Analysis.Sobolev.Cylinder.Periodization
import TauCeti.LinearAlgebra.Submodule.Quotient
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.UniformSpace.UniformConvergence.Periodic

/-!
# The universal linearized Floer operator along a Floer trajectory is surjective

Let `(V, ω)` be a finite-dimensional symplectic vector space, `J_t` a family of almost complex
structures of period one in `t`, and `u` a nonstationary Floer trajectory of a Hamiltonian `H_t`
of period one in `t`, `∂s u + J_t(u) (∂t u - X_{H_t}(u)) = 0`, of period one in `t` and
asymptotic to one-periodic orbits. Its linearized operator `D_u` is realized as a bounded operator
`W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` (`TauCeti.SymplecticForm.floerSobolevOperator`). Varying the
almost complex structure along `J + τ Y` changes the Floer operator at `u` to first order by
`Y_t(u) (∂t u - X_{H_t}(u))`. The *universal* linearized operator adds these variations to `D_u`.
Floer, Hofer and Salamon showed that it is onto; this is the transversality input for choosing
almost complex structures for which every Floer trajectory is regular.

* **Cokernel.** For a real inner product on `V`, an element `η ∈ L²(ℝ × [0, 1], V)` orthogonal
  to the range of `D_u` and to every variation `Y_t(u) (∂t u - X_{H_t}(u))`, for `Y` of period one
  in time, compactly supported in `V` and tangent to the compatible structures, vanishes
  (`TauCeti.SymplecticForm.eq_zero_of_forall_inner_floerSobolevOperator_eq_zero`). The periodic
  extension of `η` is a weak cokernel element of `D_u` on the plane
  (`TauCeti.CylinderSobolev.integral_inner_jet_eq_zero_of_forall_inner_jetOperator_eq_zero`), and
  weak cokernel elements of the universal operator vanish
  (`ae_eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator` in the namespace
  `TauCeti.SymplecticForm`).
* **Surjectivity.** For a complex inner product space `F` with `ω = Im ⟪·, ·⟫`, compatible `J`,
  nondegenerate asymptotic orbits and finite energy, `D_u` is Fredholm
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_compatible`), so its range is closed
  of finite codimension. Hence finitely many variations `Y₁, …, Y_N` already make
  `(ξ, c) ↦ D_u ξ + ∑ cᵢ Yᵢ(u) (∂t u - X_H(u))` onto
  (`TauCeti.SymplecticForm.exists_surjective_floerSobolevOperator_coprod`), by
  `Submodule.sup_eq_top_of_dense` and `Submodule.exists_finset_subset_sup_span_eq_top`. This is
  the universal operator of the family `J + ∑ cᵢ Yᵢ`, in the form taken by the parametric
  transversality theorem of `TauCeti.Analysis.Fredholm.Parametric`.

## References

* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 3.2.1 (the cokernel of the universal operator).
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal NNReal InnerProductSpace Manifold

namespace TauCeti.SymplecticForm

open CylinderSobolev
open StripSobolev (stripMeasure)

variable {V : Type*} [NormedAddCommGroup V]

section Cokernel

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coefficient field on jets of the linearized Floer operator along a map of period one in
`t`, for data `(J_t, 0, H_t dt)` of period one in `t`, has period one in `t`. -/
private lemma floerJetCoeff_add_one (ω : SymplecticForm V) {J : ℝ → V → AlmostComplexStructure V}
    (hJper : ∀ t y, J (t + 1) y = J t y) {H : ℝ → V → ℝ} (hHper : Periodic H 1)
    {u : ℝ × ℝ → V} (huper : ∀ s t, u (s, t + 1) = u (s, t)) (s t : ℝ) :
    ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) u (s, t + 1) =
      ω.floerJetCoeff (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun w ↦ H w.2) u (s, t) := by
  have h := ω.floerJetCoeff_comp_add_right
    (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2) u
    ((0 : ℝ), (1 : ℝ)) (s, t)
  have hu : (fun w ↦ u (w + ((0 : ℝ), (1 : ℝ)))) = u := by
    funext ⟨a, b⟩
    simp [huper]
  simp only [Prod.snd_add, add_zero, hJper, hHper _, hu, Prod.mk_add_mk] at h
  exact h.symm

/-- **The cokernel of the universal linearized Floer operator along a Floer trajectory is
trivial** (Floer, Hofer and Salamon). Let `J_t` be a `Cⁿ` family of almost complex structures
preserving `ω`, `2 ≤ n`, of period one in `t`, and let `u` be a nonstationary `C²` Floer
trajectory `∂s u + J_t(u) (∂t u - X_{H_t}(u)) = 0` of a `C³` Hamiltonian of period one in `t`,
with `J_t` tamed by `ω` along `u`. Let `u` have period one in `t`, with loops converging
uniformly to continuous one-periodic loops `x₋` and `x₊` at `∓∞` and slice defects
`∂t u - X_{H_t}(u)` tending uniformly to zero there. If `η ∈ L²(ℝ × [0, 1], V)` is orthogonal to
the range of the Sobolev realization `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized
operator, and to every variation `Y_t(u) (∂t u - X_{H_t}(u))` of the Floer operator along
`J + τ Y`, for `Cⁿ` fields `Y` of period one in `t`, vanishing outside a compact set of `V` and
tangent to the compatible structures, then `η = 0`. -/
theorem eq_zero_of_forall_inner_floerSobolevOperator_eq_zero (ω : SymplecticForm V) {n : ℕ∞}
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ n fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hn : 2 ≤ n) (hJω : ∀ t y, ω.Invariant (J t y)) (hJper : ∀ t y, J (t + 1) y = J t y)
    {H : ℝ → V → ℝ} (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) (huper : ∀ s t, u (s, t + 1) = u (s, t))
    (hJu : ∀ z, ω.Tames (J z.2 (u z)))
    (hF : ∀ z, ω.floerOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0)
    (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0) {xm xp : ℝ → V} (hxm : Continuous xm)
    (hxmper : Periodic xm 1) (hxp : Continuous xp) (hxpper : Periodic xp 1)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop (Icc 0 1))
    {η : Lp V 2 stripMeasure}
    (hD : ∀ x, ⟪η, ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u x⟫_ℝ = 0)
    (hY : ∀ Y : ℝ × V → V →L[ℝ] V, ContDiff ℝ n Y → (∀ t y, Y (t + 1, y) = Y (t, y)) →
      (∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0) →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p.1 p.2)) →
        ∫ z, ⟪η z, Y (z.2, u z) (sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z)⟫_ℝ
          ∂stripMeasure = 0) :
    η = 0 := by
  set Jd : ℝ × ℝ → V → V →L[ℝ] V := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap
  have hJ1 : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap :=
    hJ.of_le (WithTop.coe_le_coe.2 (le_trans (by norm_num) hn))
  have hg2 : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦ (p.1.2, p.2) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  -- The coefficient field of `D_u` on jets is bounded, continuous and periodic in `t`.
  have hM := ω.memLp_floerJetCoeff (hH.of_le (by norm_num)) hJ1 (hu.of_le one_le_two) huxm huxp
    hδm hδp
  have hMc := ω.continuous_floerJetCoeff (J := Jd) (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2)
    (fun _ ↦ (hJ1.comp (hg2.of_le one_le_two)).contDiffAt) (fun _ ↦ contDiffAt_const)
    (fun _ ↦ ((hH.of_le (by norm_num)).comp hg2).contDiffAt) (hu.of_le one_le_two)
  -- The periodic extension `g` of `η` is a locally `L²` weak annihilator of `D_u` on the plane.
  obtain ⟨g, hg, hgper, hgη⟩ := exists_stronglyMeasurable_periodic_ae_eq η
  set ηc : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ innerSL ℝ (g z)
  have hηc : MemLpLoc ((2 : ℝ≥0) : ℝ≥0∞) univ ηc :=
    (memLpLoc_univ_of_periodic hg hgper one_le_two ((Lp.memLp η).ae_eq hgη.symm)).of_le
      ((innerSL ℝ).continuous.comp_stronglyMeasurable hg).aestronglyMeasurable
      (ae_of_all _ fun z ↦ by simp [ηc, innerSL_apply_norm])
  have hD' : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ →
      ∫ z, ηc z (ω.floerLinearization Jd (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z) = 0 := by
    intro ξ hξ hξc
    simp only [ηc, innerSL_apply_apply, ← floerJetCoeff_jet]
    exact integral_inner_jet_eq_zero_of_forall_inner_jetOperator_eq_zero hM hMc
      (floerJetCoeff_add_one ω hJper hHper huper)
      (fun x hx ↦ by simpa [floerSobolevOperator_def] using hD ⟨x, hx⟩) hg hgper hgη
      (hξ.of_le (WithTop.coe_le_coe.2 le_top)) hξc
  -- It also annihilates the variations of the Floer operator along `J + τ Y`.
  have hY' : ∀ Y : ℝ × V → V →L[ℝ] V, ContDiff ℝ n Y → (∀ t x, Y (t + 1, x) = Y (t, x)) →
      (∀ᶠ p in comap Prod.snd (cocompact V), Y p = 0) →
      (∀ p, (Y p : Module.End ℝ V) ∈ ω.compatibleTangentSpace (J p.1 p.2)) →
        ∫ z in univ ×ˢ Ioo 0 1, ηc z (deriv (fun τ : ℝ ↦ ω.floerOperator
          (fun w x ↦ Jd w x + τ • Y (w.2, x)) (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) 0) = 0 := by
    intro Y h₁ h₂ h₃ h₄
    rw [← StripSobolev.stripMeasure_eq_restrict_univ_prod_Ioo]
    refine (integral_congr_ae ?_).trans (hY Y h₁ h₂ h₃ h₄)
    filter_upwards [hgη] with z hz
    rw [(ω.hasDerivAt_floerOperator_add_smul Jd (fun w x ↦ Y (w.2, x)) _ _ u z 0).deriv]
    simp [ηc, hz, sliceDefect_def, stdComplexLineImag_eq]
  -- Weak cokernel elements of the universal operator vanish.
  have h0 := ω.ae_eq_zero_of_integral_floerLinearization_of_setIntegral_deriv_floerOperator
    (J := fun p : ℝ × V ↦ J p.1 p.2) hJ hn (fun p ↦ hJω p.1 p.2) (fun t x ↦ hJper t x) hJu hH hu
    hF hne hxm hxp (tendsto_prod_of_tendstoUniformlyOn_Icc one_pos huper hxm hxmper huxm)
    (tendsto_prod_of_tendstoUniformlyOn_Icc one_pos huper hxp hxpper huxp) (by norm_num) hηc hD' hY'
  have hg0 : g =ᵐ[stripMeasure] 0 := ae_restrict_of_ae <| h0.mono fun z hz ↦ by
    simpa [ηc, innerSL_apply_norm] using congrArg norm hz
  exact Lp.eq_zero_iff_ae_eq_zero.2 (hgη.symm.trans hg0)

end Cokernel

section Surjective

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The universal linearized Floer operator along a Floer trajectory is onto** (Floer, Hofer
and Salamon). Let `F` be a finite-dimensional complex inner product space whose symplectic form
`ω` is `Im ⟪·, ·⟫`, let `J_t` be a `Cⁿ` family of `ω`-compatible almost complex structures,
`2 ≤ n`, of period one in `t`, and let `H` be a one-periodic, jointly `C³` Hamiltonian whose
suspended vector field is globally Lipschitz, with one-periodic orbits `x₋` and `x₊` whose initial
points are nondegenerate fixed points of the time-one map. Let `u` be a nonstationary `C²` Floer
trajectory of `(J_t, H_t)` of period one in `t`, whose loops converge uniformly to `x₋` and `x₊`
at `∓∞` with slice defects `∂t u - X_{H_t}(u)` tending uniformly to zero there, and of finite
energy: the slice defect is square integrable on the strip.

Then there are finitely many `Cⁿ` fields `Y₁, …, Y_N` of period one in `t`, vanishing outside a
compact set of `F` and tangent to the compatible structures, such that with `yᵢ` the variation
`Yᵢ(u) (∂t u - X_{H_t}(u))` of the Floer operator along `J + τ Yᵢ`, the operator
`(ξ, c) ↦ D_u ξ + ∑ cᵢ yᵢ` from `W^{1,2}(ℝ × S¹, F) × ℝᴺ` to `L²(ℝ × S¹, F)` is onto. -/
theorem exists_surjective_floerSobolevOperator_coprod (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {n : ℕ∞} {J : ℝ → F → AlmostComplexStructure F}
    (hJ : ContDiff ℝ n fun p : ℝ × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hn : 2 ≤ n) (hJc : ∀ t y, ω.Compatible (J t y)) (hJper : ∀ t y, J (t + 1) y = J t y)
    {H : ℝ → F → ℝ} {K : ℝ≥0} (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 3 (uncurry H)) (hHper : Periodic H 1) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t) (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t) (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {u : ℝ × ℝ → F} (hu : ContDiff ℝ 2 u) (huper : ∀ s t, u (s, t + 1) = u (s, t))
    (hF : ∀ z, ω.floerOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0)
    (hne : ∃ z, fderiv ℝ u z stdComplexLineReal ≠ 0)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop (Icc 0 1))
    (hE : MemLp (sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u) 2 stripMeasure) :
    ∃ (N : ℕ) (Y : Fin N → ℝ × F → F →L[ℝ] F) (y : Fin N → Lp F 2 stripMeasure),
      (∀ i, ContDiff ℝ n (Y i) ∧ (∀ t x, Y i (t + 1, x) = Y i (t, x)) ∧
        (∀ᶠ p in comap Prod.snd (cocompact F), Y i p = 0) ∧
        (∀ p, (Y i p : Module.End ℝ F) ∈ ω.compatibleTangentSpace (J p.1 p.2)) ∧
        y i =ᵐ[stripMeasure]
          fun z ↦ Y i (z.2, u z) (sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u z)) ∧
      Function.Surjective ((ω.floerSobolevOperator
        (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun w ↦ H w.2)
          u).coprod (Fintype.linearCombination ℝ y).toContinuousLinearMap) := by
  -- `L²(ℝ × [0, 1], F)` is a real Hilbert space for the real part of the inner product of `F`.
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  set D := ω.floerSobolevOperator (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun w ↦ H w.2) u
  set δ := sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u
  -- The admissible variations of the Floer operator, as elements of `L²`.
  set S : Set (Lp F 2 stripMeasure) := {y | ∃ Y : ℝ × F → F →L[ℝ] F, ContDiff ℝ n Y ∧
    (∀ t x, Y (t + 1, x) = Y (t, x)) ∧ (∀ᶠ p in comap Prod.snd (cocompact F), Y p = 0) ∧
    (∀ p, (Y p : Module.End ℝ F) ∈ ω.compatibleTangentSpace (J p.1 p.2)) ∧
    y =ᵐ[stripMeasure] fun z ↦ Y (z.2, u z) (δ z)}
  have hD : D.IsFredholm := ω.isFredholm_floerSobolevOperator_of_compatible hω
    (hJ.of_le (WithTop.coe_le_coe.2 (le_trans (by norm_num) hn))) hJc hX hH hHper hxm hxmper hndm
    hxp hxpper hndp (hu.of_le one_le_two) huxm hδm huxp hδp
  have := hD.finite_coker
  -- The range of `D_u` and the variations span a dense subspace: its orthogonal is trivial.
  have hdense : Dense ((D.range ⊔ Submodule.span ℝ S : Submodule ℝ (Lp F 2 stripMeasure)) :
      Set (Lp F 2 stripMeasure)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    refine Submodule.topologicalClosure_eq_top_iff.2 ((Submodule.eq_bot_iff _).2 fun η hη ↦ ?_)
    have hcont (x : ℝ → F) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) :
        Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
    refine ω.eq_zero_of_forall_inner_floerSobolevOperator_eq_zero hJ hn
      (fun t y ↦ (hJc t y).invariant) hJper hH hHper hu huper (fun z ↦ (hJc _ _).tames) hF hne
      (hcont xm hxm) hxmper (hcont xp hxp) hxpper huxm hδm huxp hδp
      (fun x ↦ Submodule.inner_left_of_mem_orthogonal
        (le_sup_left (a := D.range) ⟨x, rfl⟩) hη) ?_
    intro Y h₁ h₂ h₃ h₄
    have hm := StripSobolev.memLp_apply_of_eventually_eq_zero h₁.continuous h₃ hu.continuous hE
    have h0 := Submodule.inner_left_of_mem_orthogonal
      (le_sup_right (a := D.range) (Submodule.subset_span
        (⟨Y, h₁, h₂, h₃, h₄, hm.coeFn_toLp⟩ : hm.toLp _ ∈ S))) hη
    rw [MeasureTheory.L2.inner_def] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with z hz
    rw [hz]
  -- Finitely many variations already span a complement of the closed range of `D_u`.
  obtain ⟨t, hts, htop⟩ := Submodule.exists_finset_subset_sup_span_eq_top (by
    simpa only [← sup_assoc, sup_idem] using Submodule.sup_eq_top_of_dense hD.isClosed_range hdense)
  choose! Y hY using fun y (hy : y ∈ t) ↦ hts hy
  set e := t.equivFin
  refine ⟨t.card, fun i ↦ Y (e.symm i), fun i ↦ e.symm i, fun i ↦ hY _ (e.symm i).property, ?_⟩
  have hrange : Set.range (fun i ↦ ((e.symm i : t) : Lp F 2 stripMeasure)) = t := by
    ext y
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ (e.symm i).property, fun hy ↦ ⟨e ⟨y, hy⟩, by simp⟩⟩
  refine LinearMap.range_eq_top.1 ?_
  rw [ContinuousLinearMap.range_coprod, ← htop, ← hrange, ← Fintype.range_linearCombination]
  rw [LinearMap.coe_toContinuousLinearMap]

end Surjective

end TauCeti.SymplecticForm
