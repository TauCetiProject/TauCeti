/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.StateSpace
public import TauCeti.Analysis.CStarAlgebra.GNS.RadonNikodym
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Dense
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Separating
import TauCeti.Analysis.CStarAlgebra.Action.KMS.TomitaCommutation
import TauCeti.Analysis.VonNeumannAlgebra.Lattice
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Extreme KMS states and factor states

Let `α` be a point-norm continuous real action on a unital C⋆-algebra `A`, let `β : ℝ`, and let
`ω` be a β-KMS state of `α` with GNS representation `π_ω = ω.toPositiveLinearMap.gnsStarAlgHom`
and GNS von Neumann algebra `M = π_ω(A)''`, whose centre is `Z = π_ω(A)' ∩ π_ω(A)''`.

This file proves Bratteli–Robinson's characterization of the extreme points of `α.kmsStates β` in
the weak-* dual: `ω` is extreme if and only if `ω` is a factor state, i.e., `Z = ℂ · 1` (for every
`β : ℝ`, including `β = 0`). Central operators produce KMS vector functionals via the separating
KMS identity on `M`; conversely, Tomita commutation (`TomitaCommutation`) forces the GNS
Radon–Nikodym operator of any dominated β-KMS functional to lie in `Z`.

## Main statements

* `TauCeti.CStarAction.IsKMSState.gnsVectorFunctional_mul_entireExtension_mul_I`: vector functionals
  of central operators satisfy the analytic β-KMS identity.
* `TauCeti.CStarAction.IsKMSState.gnsRadonNikodym_mem_center`: the GNS Radon–Nikodym operator of a
  dominated β-KMS functional lies in `π_ω(A)' ∩ π_ω(A)''`.
* `TauCeti.CStarAction.mem_extremePoints_kmsStates_iff`: a β-KMS state is an extreme point of
  `α.kmsStates β` if and only if `π_ω(A)' ∩ π_ω(A)''` consists of scalar multiples of `1`.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  second edition, Theorem 5.3.30.
-/

public section

noncomputable section

open Complex ContinuousLinearMap PositiveLinearMap Set
open scoped ComplexOrder CStarAlgebra InnerProductSpace Pointwise

namespace TauCeti.CStarAction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

private theorem mem_center_gnsStarAlgHom_iff (f : A →ₚ[ℂ] ℂ) {x : f.GNS →L[ℂ] f.GNS} :
    x ∈ (VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom)).commutant ⊓
        VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) ↔
      x ∈ Set.centralizer (Set.range f.gnsStarAlgHom) ∩
        Set.centralizer (Set.centralizer (Set.range f.gnsStarAlgHom)) := by
  rw [VonNeumannAlgebra.mem_inf, ← SetLike.mem_coe, ← SetLike.mem_coe,
    VonNeumannAlgebra.coe_commutant_adjoin_range, VonNeumannAlgebra.coe_adjoin_range]; rfl

/-- **Central operators preserve the analytic KMS identity.** For a β-KMS state `ω` and an
operator `z` in the centre `π_ω(A)' ∩ π_ω(A)''`, the vector functional `a ↦ ⟪Ω, z π_ω(a) Ω⟫`
satisfies `φ (a α_{iβ}(b)) = φ (b a)` for every `a : A` and entire analytic `b : A`. -/
theorem IsKMSState.gnsVectorFunctional_mul_entireExtension_mul_I (hω : α.IsKMSState β ω)
    {z : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hz : z ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)))
    (a : A) {b : A} (hb : α.IsEntireAnalytic b) :
    ω.toPositiveLinearMap.gnsVectorFunctional z (a * α.entireExtension b (β * I)) =
      ω.toPositiveLinearMap.gnsVectorFunctional z (b * a) := by
  let f := ω.toPositiveLinearMap; let π := f.gnsStarAlgHom
  have hcomm (x : A) (v : f.GNS) : z (π x v) = π x (z v) := by
    simpa [mul_apply_eq_comp] using congrArg (fun T => T v) (hz.1 (π x) ⟨x, rfl⟩).symm
  calc f.gnsVectorFunctional z (a * α.entireExtension b (β * I))
      = ⟪f.gnsVector, π a (z (π (α.entireExtension b (β * I)) f.gnsVector))⟫_ℂ := by
        rw [gnsVectorFunctional_apply, map_mul, mul_apply_eq_comp, hcomm]
    _ = ⟪(f.toPreGNS (star a) : f.GNS),
          z (f.toPreGNS (α.entireExtension b (β * I)) : f.GNS)⟫_ℂ := by
        rw [show π a = star (π (star a)) by rw [map_star, star_star], star_eq_adjoint,
          adjoint_inner_right]; simp [π, gnsVector_def]
    _ = ⟪(f.toPreGNS (star a * star b) : f.GNS), z (f.toPreGNS 1 : f.GNS)⟫_ℂ :=
        hω.inner_apply_toPreGNS_entireExtension_mul_I
          ((VonNeumannAlgebra.mem_adjoin_range_iff π).mpr hz.2) (star a) hb
    _ = ⟪π (star (b * a)) f.gnsVector, z f.gnsVector⟫_ℂ := by
        simp [π, star_mul, gnsVector_def]
    _ = f.gnsVectorFunctional z (b * a) := by
        rw [map_star, star_eq_adjoint, adjoint_inner_left, ← hcomm, gnsVectorFunctional_apply]

/-- For `β ≠ 0`, any positive linear functional on a unital C⋆-algebra satisfying the analytic
β-KMS identity is invariant under `α`. -/
private theorem apply_action_of_analytic_kms {φ : A →ₚ[ℂ] ℂ} (hβ : β ≠ 0)
    (hkms : ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      φ (a * α.entireExtension b (β * I)) = φ (b * a))
    (t : Multiplicative ℝ) (a : A) : φ (α t a) = φ a := by
  let φc : A →P[ℂ] ℂ := PositiveContinuousLinearMap.ofClass φ
  have hnorm_eq : (‖(φc : A →L[ℂ] ℂ)‖ : ℂ) = φ 1 := by
    simpa [φc] using PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one φc
  by_cases h1 : φ 1 = 0
  · rw [h1, Complex.ofReal_eq_zero, norm_eq_zero] at hnorm_eq
    have hφ0 (x : A) : φ x = 0 := by simpa [φc] using DFunLike.congr_fun hnorm_eq x
    rw [hφ0, hφ0]
  · have hpos1 := Complex.le_def.mp (φ.map_nonneg zero_le_one); set r : ℝ := (φ 1).re
    have hr_pos : 0 < r :=
      lt_of_le_of_ne hpos1.1 fun h => h1 (Complex.ext h.symm hpos1.2.symm)
    let ψ : A →P[ℂ] ℂ := .mk₀ (((r⁻¹ : ℝ) : ℂ) • (φc : A →L[ℂ] ℂ)) fun _ hx =>
      mul_nonneg (Complex.le_def.mpr ⟨inv_nonneg.mpr hr_pos.le, by simp⟩) (φ.map_nonneg hx)
    have hψ_apply (x : A) : ψ x = ((r⁻¹ : ℝ) : ℂ) * φ x := rfl
    have hψ1 : ψ 1 = 1 := by
      rw [hψ_apply, show φ 1 = (r : ℂ) from Complex.ext rfl hpos1.2.symm, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hr_pos.ne', Complex.ofReal_one]
    have hψ_kms : α.IsKMSState β ψ :=
      isKMSState_iff_forall_isEntireAnalytic.mpr ⟨Complex.ofReal_injective (by
        simpa [hψ1] using PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ψ),
        fun x hx y hy => by rw [hψ_apply, hψ_apply, hkms x hx y hy]⟩
    have hinv := hψ_kms.apply_action hβ t a
    rw [hψ_apply, hψ_apply] at hinv
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hr_pos.ne')) hinv

/-- **Dominated KMS functionals have central Radon–Nikodym operators.** If `ω` is a β-KMS state
and `φ` is a positive linear functional dominated by a scalar multiple of `ω` that satisfies the
analytic β-KMS identity, then its GNS Radon–Nikodym operator lies in the centre
`π_ω(A)' ∩ π_ω(A)''`. -/
theorem IsKMSState.gnsRadonNikodym_mem_center (hω : α.IsKMSState β ω) {φ : A →ₚ[ℂ] ℂ}
    {C : ℝ} (hφ : ∀ a, 0 ≤ a → φ a ≤ (C : ℂ) * ω a)
    (hkms : ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      φ (a * α.entireExtension b (β * I)) = φ (b * a)) :
    ω.toPositiveLinearMap.gnsRadonNikodym φ ∈
      Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
        Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) := by
  let f := ω.toPositiveLinearMap; let π := f.gnsStarAlgHom; let T := f.gnsRadonNikodym φ
  have hT_comm : T ∈ Set.centralizer (Set.range π) :=
    gnsRadonNikodym_mem_centralizer_gnsStarAlgHom hφ
  have hT_sa : IsSelfAdjoint T := f.isSelfAdjoint_gnsRadonNikodym φ
  have hJTΩ : hω.modularConjugation (T f.gnsVector) = T f.gnsVector := by
    rcases eq_or_ne β 0 with rfl | hβ
    · rw [hω.modularConjugation_apply_gnsVector_of_zero hT_comm, hT_sa.star_eq]
    · have hinv_ω : ∀ s a, f (α s a) = f a := fun s a => hω.apply_action hβ s a
      let U := α.gnsImplementingGroup hinv_ω
      have hU := α.isUnitary_gnsImplementingGroup hinv_ω
      have hUcomm (t : Multiplicative ℝ) : U t * T = T * U t := by
        ext v; refine ext_inner_left ℂ fun u =>
          f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun a =>
            f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun b => ?_
        have hUa (x : A) (g : Multiplicative ℝ) : U g (f.toGNS x) = f.toGNS (α g x) := by
          simp [U, toGNS_apply]
        simp only [mul_apply_eq_comp]
        rw [(adjoint_inner_left (U t) _ _).symm, hU.adjoint_eq_inv t, hUa, hUa,
          inner_gnsRadonNikodym_toGNS hφ, inner_gnsRadonNikodym_toGNS hφ,
          show star (α t⁻¹ a) * b = α t⁻¹ (star a * α t b) by
            rw [map_mul, map_star, ← CStarAction.mul_apply, inv_mul_cancel, CStarAction.one_apply],
          apply_action_of_analytic_kms hβ hkms]
      rw [hω.modularConjugation_apply_gnsVector_of_commute hβ hT_comm hUcomm, hT_sa.star_eq]
  let B := hω.conjModularConjugation T
  have hB_vN := hω.conjModularConjugation_mem_adjoin hT_comm
  have hBΩ : B f.gnsVector = T f.gnsVector := by simp [B, f, hJTΩ]
  have hB_comm_entire_shift {b : A} (hb : α.IsEntireAnalytic b) :
      B * π (α.entireExtension b (β * I)) = π (α.entireExtension b (β * I)) * B := by
    let c := α.entireExtension b (β * I)
    have hc : π c ∈ VonNeumannAlgebra.adjoin (Set.range π) :=
      VonNeumannAlgebra.subset_adjoin _ ⟨c, rfl⟩
    suffices hkill : (B * π c - π c * B) (f.toPreGNS 1) = 0 from sub_eq_zero.mp
      (hω.eq_zero_of_apply_toPreGNS_one_eq_zero (sub_mem (mul_mem hB_vN hc) (mul_mem hc hB_vN))
        hkill)
    rw [sub_apply, sub_eq_zero]
    refine ext_inner_left ℂ fun u => (denseRange_toGNS_entireAnalytic α f).induction_on u
      (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
    have ha := mem_entireAnalytic.mp a.property
    calc ⟪f.toGNS (a : A), (B * π c) (f.toPreGNS 1)⟫_ℂ
        = ⟪(f.toPreGNS (a : A) : f.GNS), B (f.toPreGNS c)⟫_ℂ := by
          simp [π, mul_apply_eq_comp, toGNS_apply, ← gnsVector_def]
      _ = ⟪(f.toPreGNS ((a : A) * star b) : f.GNS), B (f.toPreGNS 1)⟫_ℂ :=
          hω.inner_apply_toPreGNS_entireExtension_mul_I hB_vN (a : A) hb
      _ = φ (b * star (a : A)) := by
          rw [← gnsVector_def, hBΩ, gnsVector_def, ← toGNS_apply, ← toGNS_apply,
            inner_gnsRadonNikodym_toGNS hφ]; simp [star_mul]
      _ = φ (star (a : A) * c) := (hkms (star (a : A)) ha.star b hb).symm
      _ = ⟪f.toGNS (a : A), (T * π c) f.gnsVector⟫_ℂ := by
          simpa [f, π, mul_apply_eq_comp, toGNS_apply] using
            (inner_gnsRadonNikodym_toGNS hφ (a : A) c).symm
      _ = ⟪f.toGNS (a : A), (π c * B) (f.toPreGNS 1)⟫_ℂ := by
          rw [← hT_comm _ ⟨c, rfl⟩, mul_apply_eq_comp, mul_apply_eq_comp, ← gnsVector_def, hBΩ]
  have hB_comm : B ∈ Set.centralizer (Set.range π) := by
    rintro _ ⟨a, rfl⟩
    refine congrFun (Continuous.ext_on α.dense_entireAnalytic
      ((map_continuous π).mul continuous_const) (continuous_const.mul (map_continuous π))
      fun c hc => ?_) a
    simpa [entireExtension_entireExtension, (mem_entireAnalytic.mp hc).entireExtension_apply_zero]
      using (hB_comm_entire_shift (isEntireAnalytic_entireExtension α c (-(β * I)))).symm
  have hBT : B = T := by
    ext v; refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop))
      fun a => ?_
    calc B (f.toGNS a) = (B * π a) f.gnsVector := by simp [π, mul_apply_eq_comp, toGNS_apply]
      _ = (T * π a) f.gnsVector := by
          rw [← hB_comm _ ⟨a, rfl⟩, mul_apply_eq_comp, hBΩ, ← mul_apply_eq_comp, hT_comm _ ⟨a, rfl⟩]
      _ = T (f.toGNS a) := by simp [π, mul_apply_eq_comp, toGNS_apply]
  exact ⟨hT_comm,
    (VonNeumannAlgebra.mem_adjoin_range_iff π).mp (by simpa [T, B, f, π, hBT] using hB_vN)⟩

/-- Normalizing the vector functional of a positive commutant operator by `t > 0` yields a positive
continuous linear functional. -/
private def kmsStateOfCentralPositive {f : A →ₚ[ℂ] ℂ} {y : f.GNS →L[ℂ] f.GNS}
    (hy : y ∈ Set.centralizer (Set.range f.gnsStarAlgHom)) (hy_pos : y.IsPositive)
    {t : ℝ} (ht_pos : 0 < t) : A →P[ℂ] ℂ :=
  .mk₀ (((t⁻¹ : ℝ) : ℂ) • f.gnsVectorFunctional y) fun _ ha =>
    mul_nonneg (Complex.le_def.mpr ⟨inv_nonneg.mpr ht_pos.le, by simp⟩)
      (gnsVectorFunctional_nonneg f hy hy_pos ha)

private theorem kmsStateOfCentralPositive_apply {f : A →ₚ[ℂ] ℂ} {y : f.GNS →L[ℂ] f.GNS}
    (hy : y ∈ Set.centralizer (Set.range f.gnsStarAlgHom)) (hy_pos : y.IsPositive)
    {t : ℝ} (ht_pos : 0 < t) (a : A) :
    kmsStateOfCentralPositive hy hy_pos ht_pos a = ((t⁻¹ : ℝ) : ℂ) * f.gnsVectorFunctional y a :=
  rfl

private theorem isKMSState_kmsStateOfCentralPositive (hω : α.IsKMSState β ω)
    {y : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hyZ : y ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)))
    (hy_pos : y.IsPositive) {t : ℝ} (ht_pos : 0 < t)
    (hyΩ : ⟪ω.toPositiveLinearMap.gnsVector, y ω.toPositiveLinearMap.gnsVector⟫_ℂ = t) :
    α.IsKMSState β (kmsStateOfCentralPositive hyZ.1 hy_pos ht_pos) := by
  refine isKMSState_iff_forall_isEntireAnalytic.mpr ⟨?_, fun a _ b hb => ?_⟩
  · have h1 : kmsStateOfCentralPositive hyZ.1 hy_pos ht_pos 1 = 1 := by
      simp [kmsStateOfCentralPositive_apply, gnsVectorFunctional_apply, ← gnsVector_def, hyΩ,
        Complex.ofReal_ne_zero.mpr ht_pos.ne']
    exact Complex.ofReal_injective (by
      simpa [h1] using PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
        (kmsStateOfCentralPositive hyZ.1 hy_pos ht_pos))
  · simp only [kmsStateOfCentralPositive_apply,
      hω.gnsVectorFunctional_mul_entireExtension_mul_I hyZ a hb]

/-- Quadratic-form bounds `(1/4)‖v‖² ≤ Re ⟪y v, v⟫ ≤ (3/4)‖v‖²` for the perturbation
`y = (1/2) • 1 + (4 (‖z‖ + 1))⁻¹ • z`. -/
private theorem re_inner_half_add_smul_bounds {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (z : H →L[ℂ] H) (v : H) :
    let r : ℝ := 4 * (‖z‖ + 1)
    let y : H →L[ℂ] H := (2⁻¹ : ℂ) • 1 + ((r⁻¹ : ℝ) : ℂ) • z
    (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (⟪y v, v⟫_ℂ).re ∧ (⟪y v, v⟫_ℂ).re ≤ (3 / 4 : ℝ) * ‖v‖ ^ 2 := by
  intro r y; have hr : 0 < r := by positivity
  have hz_norm : |(⟪z v, v⟫_ℂ).re| ≤ (‖z‖ + 1) * ‖v‖ ^ 2 :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (by nlinarith [z.le_opNorm v, norm_nonneg v, sq_nonneg ‖v‖]))
  have hv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
  have h2 : starRingEnd ℂ (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_inv, Complex.conj_ofReal]
  have hre_y : (⟪y v, v⟫_ℂ).re = (1 / 2 : ℝ) * ‖v‖ ^ 2 + r⁻¹ * (⟪z v, v⟫_ℂ).re := by
    simp only [y, add_apply, smul_apply, one_apply_eq_self]
    rw [inner_add_left, inner_smul_left, inner_smul_left, h2]
    simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hv]; ring
  have hstep : |r⁻¹ * (⟪z v, v⟫_ℂ).re| ≤ (1 / 4 : ℝ) * ‖v‖ ^ 2 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hr)]
    have hmul := mul_le_mul_of_nonneg_left hz_norm (inv_nonneg.mpr hr.le)
    have hr_eq : r⁻¹ * (‖z‖ + 1) = 1 / 4 := by
      have : ‖z‖ + 1 ≠ 0 := by positivity
      simp only [r]; field_simp
    nlinarith
  rcases abs_le.mp hstep with ⟨h1, h2⟩; constructor <;> linarith

/-- For a self-adjoint operator `z`, `y = (1/2) • 1 + (4 (‖z‖ + 1))⁻¹ • z` and `1 - y` are
both positive. -/
private theorem isPositive_half_add_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {z : H →L[ℂ] H} (hz : IsSelfAdjoint z) :
    let y : H →L[ℂ] H := (2⁻¹ : ℂ) • 1 + (((4 * (‖z‖ + 1))⁻¹ : ℝ) : ℂ) • z
    y.IsPositive ∧ (1 - y).IsPositive := by
  intro y
  have hy_sa : IsSelfAdjoint y :=
    (IsSelfAdjoint.smul (by simp : IsSelfAdjoint (2⁻¹ : ℂ)) (IsSelfAdjoint.one _)).add
      (IsSelfAdjoint.smul (Complex.conj_ofReal _) hz)
  refine ⟨isPositive_def'.mpr ⟨hy_sa, fun v =>
      (by positivity : (0 : ℝ) ≤ (1 / 4) * ‖v‖ ^ 2).trans (re_inner_half_add_smul_bounds z v).1⟩,
    isPositive_def'.mpr ⟨(IsSelfAdjoint.one _).sub hy_sa, fun v => ?_⟩⟩
  have hle := (re_inner_half_add_smul_bounds z v).2; dsimp only [y]
  simp only [reApplyInnerSelf, sub_apply, one_apply_eq_self, inner_sub_left, map_sub,
    RCLike.re_to_complex, sub_nonneg,
    show (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 by rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]]
  linarith [hle, sq_nonneg ‖v‖]

/-- A central operator in the GNS representation of a β-KMS state is uniquely determined by its
vector functional on `Ω`. -/
private theorem IsKMSState.eq_smul_one_of_gnsVectorFunctional_eq (hω : α.IsKMSState β ω)
    {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hT : T ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)))
    {c : ℂ} (hval : ∀ a : A, ω.toPositiveLinearMap.gnsVectorFunctional T a = c * ω a) :
    T = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) := by
  let f := ω.toPositiveLinearMap; let π := f.gnsStarAlgHom
  have hsub := (mem_center_gnsStarAlgHom_iff f).mp <| sub_mem
    ((mem_center_gnsStarAlgHom_iff f).mpr hT) (SMulMemClass.smul_mem c (one_mem _))
  have hvan : f.gnsVectorFunctional (T - c • (1 : f.GNS →L[ℂ] f.GNS)) = 0 := by
    ext a; simp [gnsVectorFunctional_sub, gnsVectorFunctional_smul,
      show f.gnsVectorFunctional T a = c * f a from hval a]
  exact sub_eq_zero.mp (hω.eq_zero_of_apply_toPreGNS_one_eq_zero
    ((VonNeumannAlgebra.mem_adjoin_range_iff π).mpr hsub.2)
    (by
      rw [← gnsVector_def]
      exact apply_gnsVector_eq_zero_of_gnsVectorFunctional_eq_zero f hsub.1 hvan))

/-- Self-adjoint operators in the GNS centre of an extreme β-KMS state are scalar multiples of
the identity. -/
private theorem eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint (hω : α.IsKMSState β ω)
    (hext : StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β))
    {z : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hz : z ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)))
    (hz_sa : IsSelfAdjoint z) :
    ∃ c : ℂ, z = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) := by
  let f := ω.toPositiveLinearMap; let π := f.gnsStarAlgHom
  let Z : VonNeumannAlgebra f.GNS :=
    (VonNeumannAlgebra.adjoin (Set.range π)).commutant ⊓ VonNeumannAlgebra.adjoin (Set.range π)
  set r : ℝ := 4 * (‖z‖ + 1); have hr : 0 < r := by positivity
  let y : f.GNS →L[ℂ] f.GNS := (2⁻¹ : ℂ) • 1 + ((r⁻¹ : ℝ) : ℂ) • z
  have hyZ : y ∈ Z := add_mem (SMulMemClass.smul_mem _ (one_mem Z))
    (SMulMemClass.smul_mem _ ((mem_center_gnsStarAlgHom_iff f).mpr hz))
  have hyZ' := (mem_center_gnsStarAlgHom_iff f).mp hyZ
  have h1yZ' := (mem_center_gnsStarAlgHom_iff f).mp (sub_mem (one_mem Z) hyZ)
  obtain ⟨hy_pos, h1y_pos⟩ := isPositive_half_add_smul hz_sa
  have hΩ_norm : ‖f.gnsVector‖ = 1 := f.norm_gnsVector (by
    simpa [f] using (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω).symm.trans
      (by rw [hω.norm_eq_one, Complex.ofReal_one]))
  set t : ℝ := (⟪y f.gnsVector, f.gnsVector⟫_ℂ).re
  have ht_bounds : (1 / 4 : ℝ) ≤ t ∧ t ≤ 3 / 4 := by
    simpa only [t, y, r, hΩ_norm, one_pow, mul_one] using
      re_inner_half_add_smul_bounds z f.gnsVector
  have ht_pos : 0 < t := by linarith
  have h1t_pos : 0 < 1 - t := by linarith
  have hyΩ : ⟪f.gnsVector, y f.gnsVector⟫_ℂ = (t : ℂ) := by
    rw [← hy_pos.inner_left_eq_inner_right f.gnsVector f.gnsVector]
    exact Complex.ext rfl (Complex.le_def.mp (hy_pos.inner_nonneg_left f.gnsVector)).2.symm
  have h1yΩ : ⟪f.gnsVector, ((1 : f.GNS →L[ℂ] f.GNS) - y) f.gnsVector⟫_ℂ =
      ((1 - t : ℝ) : ℂ) := by
    rw [sub_apply, one_apply_eq_self, inner_sub_right, hyΩ, inner_self_eq_norm_sq_to_K, hΩ_norm]
    simp
  have hseg : StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈
      openSegment ℝ
        (StrongDual.toWeakDual (kmsStateOfCentralPositive hyZ'.1 hy_pos ht_pos : A →L[ℂ] ℂ))
        (StrongDual.toWeakDual (kmsStateOfCentralPositive h1yZ'.1 h1y_pos h1t_pos :
          A →L[ℂ] ℂ)) := by
    refine ⟨t, 1 - t, ht_pos, h1t_pos, add_sub_cancel t 1, DFunLike.ext _ _ fun a => ?_⟩
    simp only [_root_.add_apply, _root_.smul_apply, StrongDual.toWeakDual_apply,
      PositiveContinuousLinearMap.coe_toContinuousLinearMap, Complex.real_smul,
      kmsStateOfCentralPositive_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht_pos.ne', Complex.ofReal_one,
      one_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h1t_pos.ne', Complex.ofReal_one,
      one_mul, gnsVectorFunctional_sub, sub_apply, gnsVectorFunctional_one, add_sub_cancel]; rfl
  have hω₁_eq := (mem_extremePoints_iff_left.mp hext).2 _ (toWeakDual_mem_kmsStates_iff.mpr
      (isKMSState_kmsStateOfCentralPositive hω hyZ' hy_pos ht_pos hyΩ)) _
    (toWeakDual_mem_kmsStates_iff.mpr
      (isKMSState_kmsStateOfCentralPositive hω h1yZ' h1y_pos h1t_pos h1yΩ)) hseg
  have hy_eq : y = (t : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) :=
    hω.eq_smul_one_of_gnsVectorFunctional_eq hyZ' fun a => by
      have heval := DFunLike.congr_fun hω₁_eq a
      simp only [StrongDual.toWeakDual_apply, PositiveContinuousLinearMap.coe_toContinuousLinearMap,
        kmsStateOfCentralPositive_apply] at heval
      simpa [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht_pos.ne'), f] using
        congrArg (fun w => (t : ℂ) * w) heval
  refine ⟨(r : ℂ) * ((t : ℂ) - 2⁻¹), ?_⟩
  have hrz : ((r⁻¹ : ℝ) : ℂ) • z = ((t : ℂ) - 2⁻¹) • (1 : f.GNS →L[ℂ] f.GNS) := by
    rw [sub_smul]; exact eq_sub_of_add_eq' hy_eq
  simpa [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')] using
    congrArg (fun S : f.GNS →L[ℂ] f.GNS => (r : ℂ) • S) hrz

/-- A β-KMS factor state is an extreme point of `α.kmsStates β`. -/
private theorem mem_extremePoints_kmsStates_of_trivial_center (hω : α.IsKMSState β ω)
    (hfactor : ∀ T ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
        Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)),
      ∃ c : ℂ, T = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)) :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β) := by
  let f := ω.toPositiveLinearMap
  refine mem_extremePoints_iff_left.mpr ⟨toWeakDual_mem_kmsStates_iff.mpr hω, ?_⟩
  rintro φ₁ hφ₁ φ₂ hφ₂ ⟨s, t, hs, ht, _, hcomb⟩
  obtain ⟨ω₁, hω₁, rfl⟩ := mem_kmsStates_iff.mp hφ₁
  obtain ⟨ω₂, _, rfl⟩ := mem_kmsStates_iff.mp hφ₂
  let φ : A →ₚ[ℂ] ℂ := .mk₀ ((s : ℂ) • ω₁.toPositiveLinearMap.toLinearMap) fun _ ha =>
    mul_nonneg (Complex.le_def.mpr ⟨hs.le, by simp⟩) (ω₁.map_nonneg ha)
  have hφ_apply (a : A) : φ a = (s : ℂ) * ω₁ a := rfl
  have hcomb_apply (a : A) : (s : ℂ) * ω₁ a + (t : ℂ) * ω₂ a = ω a := by
    simpa only [_root_.add_apply, _root_.smul_apply, StrongDual.toWeakDual_apply,
      PositiveContinuousLinearMap.coe_toContinuousLinearMap, Complex.real_smul] using
      DFunLike.congr_fun hcomb a
  have hdom : ∀ a, 0 ≤ a → φ a ≤ (1 : ℂ) * ω a := fun a ha => by
    rw [one_mul, hφ_apply, ← hcomb_apply a, le_add_iff_nonneg_right]
    exact mul_nonneg (Complex.le_def.mpr ⟨ht.le, by simp⟩) (ω₂.map_nonneg ha)
  obtain ⟨c, hc⟩ := hfactor (f.gnsRadonNikodym φ) (hω.gnsRadonNikodym_mem_center hdom
    fun a _ b hb => by simp only [hφ_apply, hω₁.apply_mul_entireExtension_mul_I a hb])
  have hval (a : A) : (s : ℂ) * ω₁ a = c * ω a := by
    simpa [f, hc, gnsVectorFunctional_smul, gnsVectorFunctional_one, hφ_apply] using
      (gnsVectorFunctional_gnsRadonNikodym (f := f) (g := φ) hdom a).symm
  have hcs : c = (s : ℂ) := by
    have h1 := hval 1
    rw [← PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω₁,
      ← PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω,
      hω₁.norm_eq_one, hω.norm_eq_one, Complex.ofReal_one, mul_one, mul_one] at h1; exact h1.symm
  refine DFunLike.ext _ _ fun a => ?_
  simp only [StrongDual.toWeakDual_apply, PositiveContinuousLinearMap.coe_toContinuousLinearMap]
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hs.ne') (by rw [hval a, hcs])

/-- **Extreme KMS states are factor states (Bratteli–Robinson 2, Theorem 5.3.30).** For a unital
C⋆-dynamical system `(A, α)` and any real `β` (including `β = 0`), a β-KMS state `ω` is an
extreme point of `α.kmsStates β` in the weak-* dual if and only if the centre
`π_ω(A)' ∩ π_ω(A)''` of its GNS von Neumann algebra consists of scalar multiples of the
identity. -/
theorem mem_extremePoints_kmsStates_iff (α : CStarAction (Multiplicative ℝ) A) (β : ℝ)
    (ω : A →P[ℂ] ℂ) (hω : α.IsKMSState β ω) :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β) ↔
      ∀ T ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
          Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)),
        ∃ c : ℂ,
          T = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) := by
  refine ⟨fun hext z hz => ?_, mem_extremePoints_kmsStates_of_trivial_center hω⟩
  let f := ω.toPositiveLinearMap
  let Z : VonNeumannAlgebra f.GNS :=
    (VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom)).commutant ⊓
      VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom)
  have hzZ : z ∈ Z := (mem_center_gnsStarAlgHom_iff f).mpr hz
  let x : f.GNS →L[ℂ] f.GNS := (2⁻¹ : ℂ) • (z + star z)
  let y : f.GNS →L[ℂ] f.GNS := (-I / 2 : ℂ) • (z - star z)
  have hx_sa : IsSelfAdjoint x :=
    IsSelfAdjoint.smul (by simp : IsSelfAdjoint (2⁻¹ : ℂ)) (IsSelfAdjoint.add_star_self z)
  have hy_sa : IsSelfAdjoint y := by
    rw [IsSelfAdjoint, star_smul, star_sub, star_star,
      show star (-I / 2 : ℂ) = -(-I / 2 : ℂ) by simp [RCLike.star_def, neg_div],
      neg_smul, ← smul_neg, neg_sub]
  obtain ⟨c₁, hc₁⟩ := eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint hω hext
    ((mem_center_gnsStarAlgHom_iff f).mp (SMulMemClass.smul_mem _ (add_mem hzZ (star_mem hzZ))))
    hx_sa
  obtain ⟨c₂, hc₂⟩ := eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint hω hext
    ((mem_center_gnsStarAlgHom_iff f).mp (SMulMemClass.smul_mem _ (sub_mem hzZ (star_mem hzZ))))
    hy_sa
  refine ⟨c₁ + I * c₂, ?_⟩
  have hI : I * (-I / 2) = (2⁻¹ : ℂ) := by ring_nf; rw [I_sq]; norm_num
  have hdecomp : z = x + I • y := by
    simp only [x, y, smul_add, smul_sub, smul_smul, hI]
    rw [show (2⁻¹ : ℂ) • z + (2⁻¹ : ℂ) • star z + ((2⁻¹ : ℂ) • z - (2⁻¹ : ℂ) • star z) =
        ((2⁻¹ : ℂ) + 2⁻¹) • z by rw [add_smul]; abel]; norm_num
  rw [hdecomp]; dsimp only [x, y]; rw [hc₁, hc₂, smul_smul, ← add_smul]

end TauCeti.CStarAction
