/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.SmallEnergy
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.SmallHamiltonian

/-!
# Floer cylinders of small energy for small Hamiltonians are time-independent

Let `(V, ω)` be a symplectic vector space, `J` a constant almost complex structure tamed by `ω`,
`H : V → ℝ` an autonomous `C³` Hamiltonian and `K ⊆ V` compact. For `ε ∈ [0, 1]` consider the
Floer cylinders of `ε H`: maps `u : ℝ × ℝ → V` of period one in `t` solving
`∂s u + J (∂t u - ε X_H(u)) = 0`, with image in `K`.

**The a priori bound.** There are `δ > 0` and `M` such that every such cylinder whose Floer energy
over the strip `ℝ × [0, 1]` is at most `δ` satisfies `‖du‖ ≤ M` everywhere, for every
`ε ∈ [0, 1]`
(`exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le`). This is the
case `Hs ε t = ε H`, `Js ε t = J`, `C = [0, 1]` of the same bound for a compact family of
Hamiltonians and almost complex structures
(`exists_pos_forall_norm_fderiv_le_of_mem_of_setLIntegral_floerEnergyDensity_le`, in
`TauCeti.Geometry.Symplectic.Floer.Compactness.SmallEnergy`): the point is that `δ` and `M` do
not depend on `ε`.

**Time independence.** If moreover the derivatives of `X_H` are bounded everywhere,
`‖dX_H‖ ≤ a` and `‖d²X_H‖ ≤ c`, and the inner product of `V` is the metric `ω(·, J ·)`, then there
is `ε₀ > 0` such that for `0 ≤ ε ≤ ε₀` every such cylinder of energy at most `δ` is independent of
`t`, and `s ↦ u(s, 0)` is an upward gradient line of `ε H`
(`exists_pos_forall_eq_comp_fst_of_setLIntegral_floerEnergyDensity_const_mul_le`).
Indeed `X_{ε H} = ε X_H`, so `‖dX_{ε H}‖ ≤ ε a` and `‖d²X_{ε H}‖ ≤ ε c`, while the a priori
bound `M` does not depend on `ε`. For small `ε` the smallness condition `ε c M < 2 (2π - ε a)²` of
`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv` holds.

This is the step of Floer's comparison of the Floer complex of a `C²`-small Morse Hamiltonian
with its Morse complex that bounds the derivative of the Floer cylinders in terms of the
Hamiltonian. A cylinder of `ε H` between two constant orbits has energy `ε` times the difference
of the values of `H` at them, so for small `ε` its energy is below `δ`; that energy identity is not
used here. The bounds on `X_H` hold for a Hamiltonian with compact support, and for a Hamiltonian
invariant under a lattice `Λ ⊆ V`, the lift of a Hamiltonian on the flat torus `V / Λ`.

## Main results

* `exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le`:
  Floer cylinders of `ε H`, `ε ∈ [0, 1]`, in a compact set and of small energy have uniformly
  bounded derivatives.
* `exists_pos_forall_eq_comp_fst_of_setLIntegral_floerEnergyDensity_const_mul_le`:
  for small `ε` they are independent of `t`, and are gradient lines of `ε H`.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (inhomogeneous equations).
-/

public section

open Real Set Filter Topology MeasureTheory Metric
open scoped Gradient RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ}

/-- **Floer cylinders of small energy for a family of small Hamiltonians have bounded
derivatives.** Let `J` be a constant almost complex structure tamed by `ω`, `H` a `C³` autonomous
Hamiltonian and `K ⊆ V` compact. There are `δ > 0` and `M` with the following property, for every
`ε ∈ [0, 1]`. Let `u` be a `C³` solution of the Floer equation `∂s u + J (∂t u - ε X_H(u)) = 0`
of `ε H dt`, of period one in `t`, with image in `K` and Floer energy at most `δ` over the strip
`ℝ × [0, 1]`. Then `‖du‖ ≤ M` everywhere. This is the case `Hs ε t = ε H`, `Js ε t = J`,
`C = [0, 1]` of `exists_pos_forall_norm_fderiv_le_of_mem_of_setLIntegral_floerEnergyDensity_le`. -/
theorem exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le
    (hJ : ω.Tames J) (hH : ContDiff ℝ 3 H) {K : Set V} (hK : IsCompact K) :
    ∃ δ > 0, ∃ M, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, ε ∈ Icc (0 : ℝ) 1 → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in univ ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z) ≤
        ENNReal.ofReal δ →
      ∀ z, ‖fderiv ℝ u z‖ ≤ M :=
  exists_pos_forall_norm_fderiv_le_of_mem_of_setLIntegral_floerEnergyDensity_le
    (Hs := fun ε _ x ↦ ε * H x) (Js := fun _ _ _ ↦ J)
    (contDiff_fst.mul (hH.comp (contDiff_snd.comp contDiff_snd))) (fun _ _ _ ↦ rfl)
    contDiff_const isCompact_Icc hK fun _ _ _ _ _ ↦ hJ

/-- The Hamiltonian vector field of `ε H` is `ε X_H`, so for `ε ≥ 0` bounds `a` on `‖dX_H‖` and
`c` on `‖d²X_H‖` give the bounds `ε a` on `‖dX_{ε H}‖` and `ε c` on `‖d²X_{ε H}‖`. -/
private theorem norm_fderiv_hamiltonianVectorField_const_mul_le {ε a c : ℝ} (hε0 : 0 ≤ ε)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c) :
    (∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField (fun x ↦ ε * H x)) x‖ ≤ ε * a) ∧
      ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField (fun x ↦ ε * H x))) x‖ ≤ ε * c := by
  have hX : ω.hamiltonianVectorField (fun x ↦ ε * H x) = ε • ω.hamiltonianVectorField H :=
    funext (ω.hamiltonianVectorField_const_mul ε H)
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [hX, fderiv_const_smul_field, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left (ha x) hε0
  · rw [hX, fderiv_const_smul_field, fderiv_const_smul_field, Pi.smul_apply]
    refine (ContinuousLinearMap.opNorm_smul_le ε _).trans ?_
    rw [Real.norm_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left (hc x) hε0

/-- The smallness conditions `ε a < 2π` and `ε b < 2 (2π - ε a)²` hold for
`ε ≤ min (π / (a + 1)) (π² / (b + 1))`. -/
private theorem mul_lt_two_mul_pi_and_mul_lt_of_le_div {ε a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hεa : ε ≤ π / (a + 1)) (hεb : ε ≤ π ^ 2 / (b + 1)) :
    ε * a < 2 * π ∧ ε * b < 2 * (2 * π - ε * a) ^ 2 := by
  have ha : ε * a < π := by
    have h : π / (a + 1) * a < π := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [pi_pos]
    exact (mul_le_mul_of_nonneg_right hεa ha0).trans_lt h
  have hb : ε * b < π ^ 2 := by
    have h : π ^ 2 / (b + 1) * b < π ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [pi_pos]
    exact (mul_le_mul_of_nonneg_right hεb hb0).trans_lt h
  exact ⟨by linarith [pi_pos], by nlinarith [pi_pos]⟩

/-- **Floer cylinders of small energy for a small Hamiltonian are time-independent gradient
lines.** Let the inner product of `V` be the metric `ω(·, J ·)` of a constant compatible almost
complex structure `J`, let `H` be a `C³` autonomous Hamiltonian with `‖dX_H‖ ≤ a` and
`‖d²X_H‖ ≤ c` everywhere, and let `K ⊆ V` be compact. There are `ε₀ > 0` and `δ > 0` with the
following property, for every `ε ∈ [0, ε₀]`. Let `u` be a `C³` solution of the Floer equation
`∂s u + J (∂t u - ε X_H(u)) = 0` of `ε H dt`, of period one in `t`, with image in `K` and Floer
energy at most `δ` over the strip `ℝ × [0, 1]`. Then `u(s, t) = u(s, 0)`, and `γ(s) = u(s, 0)`
solves `γ' = ∇(ε H)(γ)`. -/
theorem exists_pos_forall_eq_comp_fst_of_setLIntegral_floerEnergyDensity_const_mul_le
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 3 H) {a c : ℝ}
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    {K : Set V} (hK : IsCompact K) :
    ∃ ε₀ > 0, ∃ δ > 0, ∀ ⦃ε : ℝ⦄ ⦃u : ℝ × ℝ → V⦄, ε ∈ Icc 0 ε₀ → ContDiff ℝ 3 u →
      (∀ s t, u (s, t + 1) = u (s, t)) →
      (∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ z, u z ∈ K) →
      ∫⁻ z in univ ×ˢ Icc 0 1,
          ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ x ↦ ε * H x) u z) ≤
        ENNReal.ofReal δ →
      u = (fun z ↦ u (z.1, 0)) ∧
        ∀ s, HasDerivAt (fun s ↦ u (s, 0)) (∇ (fun x ↦ ε * H x) (u (s, 0))) s := by
  have hJ : ω.Tames J := fun v hv ↦ by
    rw [hg]
    exact real_inner_self_pos.2 hv
  obtain ⟨δ, hδ, M, hM⟩ :=
    exists_pos_forall_norm_fderiv_le_of_setLIntegral_floerEnergyDensity_const_mul_le hJ hH hK
  have ha0 : 0 ≤ a := (norm_nonneg (fderiv ℝ (ω.hamiltonianVectorField H) 0)).trans (ha 0)
  have hc0 : 0 ≤ c :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) 0)).trans (hc 0)
  set M' := max M 0
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hcM : 0 ≤ c * M' := mul_nonneg hc0 hM'0
  refine ⟨min 1 (min (π / (a + 1)) (π ^ 2 / (c * M' + 1))), by positivity, δ, hδ,
    fun ε u hε hu hper hfl huK hE ↦ ?_⟩
  obtain ⟨hε0, hε₀⟩ := hε
  have hε1 : ε ≤ 1 := hε₀.trans (min_le_left _ _)
  have hεa : ε ≤ π / (a + 1) := hε₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc : ε ≤ π ^ 2 / (c * M' + 1) := hε₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbd (z : ℝ × ℝ) : ‖fderiv ℝ u z‖ ≤ M' :=
    (hM ⟨hε0, hε1⟩ hu hper hfl huK hE z).trans (le_max_left _ _)
  -- The derivatives of `X_{ε H} = ε X_H` are bounded by `ε a` and `ε c`, which are small.
  obtain ⟨hπ, hεc'⟩ := mul_lt_two_mul_pi_and_mul_lt_of_le_div ha0 hcM hεa hεc
  rw [← mul_assoc] at hεc'
  obtain ⟨haε, hcε⟩ := norm_fderiv_hamiltonianVectorField_const_mul_le (ω := ω) hε0 ha hc
  have hH' : ContDiff ℝ 3 (fun x ↦ ε * H x) := contDiff_const.mul hH
  exact ⟨eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv hg hH' haε hcε hπ hεc' hu hper hfl hbd,
    hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv hg hH' haε hcε hπ hεc' hu hper hfl
      hbd⟩

end TauCeti.SymplecticForm
