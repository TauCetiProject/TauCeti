/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import TauCeti.Analysis.CStarAlgebra.Action.KMS.StateSpace
public import TauCeti.Analysis.CStarAlgebra.GNS.RadonNikodym
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
public import TauCeti.Analysis.VonNeumannAlgebra.Factor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import TauCeti.Analysis.CStarAlgebra.Action.GaussianSmearing
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Dense
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Separating
import TauCeti.Analysis.CStarAlgebra.Action.KMS.TomitaCommutation
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Extreme KMS states and factor states

Let `α` be a point-norm continuous real action on a unital C⋆-algebra `A`, let `β : ℝ`, and let
`ω` be a β-KMS state of `α` with GNS representation `π_ω` and GNS von Neumann algebra
`M = ω.toPositiveLinearMap.gnsVonNeumannAlgebra`, whose centre is `Z = M ⊓ M.commutant`.

This file proves Bratteli–Robinson's characterization of the extreme points of `α.kmsStates β` in
the weak-* dual: `ω` is extreme if and only if `M` is a factor (`M.IsFactor`), i.e., `1 ≠ 0` and
`Z = ℂ · 1` (for every `β : ℝ`, including `β = 0`). Central operators produce KMS vector
functionals via the separating KMS identity on `M`; conversely, Tomita commutation
(`TomitaCommutation`) forces the GNS Radon–Nikodym operator of any dominated β-KMS functional to lie
in `Z`.

## Main statements

* `TauCeti.CStarAction.IsKMSState.gnsVectorFunctional_mul_entireExtension_mul_I`: vector functionals
  of central operators satisfy the analytic β-KMS identity.
* `TauCeti.CStarAction.IsKMSState.gnsRadonNikodym_mem_center`: the GNS Radon–Nikodym operator of a
  dominated β-KMS functional lies in `M ⊓ M.commutant`.
* `TauCeti.CStarAction.mem_extremePoints_kmsStates_iff`: a β-KMS state is an extreme point of
  `α.kmsStates β` if and only if its GNS von Neumann algebra `M` is a factor.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*,
  second edition, Theorem 5.3.30.
-/

public section

noncomputable section

open Complex ContinuousLinearMap PositiveLinearMap Set
open scoped ComplexOrder ComplexStarModule CStarAlgebra InnerProductSpace NNReal Pointwise

namespace TauCeti.CStarAction

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {α : CStarAction (Multiplicative ℝ) A} {β : ℝ} {ω : A →P[ℂ] ℂ}

/-- **Central operators preserve the analytic KMS identity.** For a β-KMS state `ω` and an
operator `z` in the centre `M_ω ⊓ M_ω'`, the vector functional `a ↦ ⟪Ω, z π_ω(a) Ω⟫`
satisfies `φ (a α_{iβ}(b)) = φ (b a)` for every `a : A` and entire analytic `b : A`. -/
theorem IsKMSState.gnsVectorFunctional_mul_entireExtension_mul_I (hω : α.IsKMSState β ω)
    {z : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hz : z ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra ⊓
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant)
    (a : A) {b : A} (hb : α.IsEntireAnalytic b) :
    ω.toPositiveLinearMap.gnsVectorFunctional z (a * α.entireExtension b (β * I)) =
      ω.toPositiveLinearMap.gnsVectorFunctional z (b * a) := by
  let f := ω.toPositiveLinearMap; let π := f.gnsNonUnitalStarAlgHom
  obtain ⟨hzM, hzM'⟩ := VonNeumannAlgebra.mem_inf.mp hz
  have hcomm (x : A) (v : f.GNS) : z (π x v) = π x (z v) := by
    simpa [mul_apply_eq_comp] using
      congrArg (fun T => T v) (f.mem_gnsVonNeumannAlgebra_commutant_iff.mp hzM' x).symm
  have hz_adj : z ∈ VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) := by
    rwa [← gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom]
  calc f.gnsVectorFunctional z (a * α.entireExtension b (β * I))
      = ⟪f.gnsVector, π a (z (π (α.entireExtension b (β * I)) f.gnsVector))⟫_ℂ := by
        rw [gnsVectorFunctional_apply, map_mul, mul_apply_eq_comp]
        exact congrArg (⟪f.gnsVector, ·⟫_ℂ) (hcomm a (π (α.entireExtension b (β * I)) f.gnsVector))
    _ = ⟪(f.toPreGNS (star a) : f.GNS),
          z (f.toPreGNS (α.entireExtension b (β * I)) : f.GNS)⟫_ℂ := by
        rw [show π a = star (π (star a)) by rw [map_star, star_star], star_eq_adjoint,
          adjoint_inner_right]; simp [π, gnsVector_def, gnsNonUnitalStarAlgHom_apply_coe]
    _ = ⟪(f.toPreGNS (star a * star b) : f.GNS), z (f.toPreGNS 1 : f.GNS)⟫_ℂ :=
        hω.inner_apply_toPreGNS_entireExtension_mul_I hz_adj (star a) hb
    _ = ⟪π (star (b * a)) f.gnsVector, z f.gnsVector⟫_ℂ := by
        simp [π, star_mul, gnsVector_def, gnsNonUnitalStarAlgHom_apply_coe]
    _ = f.gnsVectorFunctional z (b * a) := by
        rw [map_star, star_eq_adjoint, adjoint_inner_left, ← hcomm, gnsVectorFunctional_apply]
        simp [π, gnsStarAlgHom_apply]

/-- Scaling a positive continuous functional by `t⁻¹` for `t > 0`. -/
private def normalizePos (ψ : A →P[ℂ] ℂ) (t : ℝ) : A →P[ℂ] ℂ :=
  Real.toNNReal t⁻¹ • ψ

@[simp]
private theorem normalizePos_apply (ψ : A →P[ℂ] ℂ) {t : ℝ} (ht : 0 < t) (a : A) :
    normalizePos ψ t a = ((t⁻¹ : ℝ) : ℂ) * ψ a := by
  simp [normalizePos, NNReal.smul_def, Complex.real_smul,
    Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)]

private theorem normalizePos_map_one (ψ : A →P[ℂ] ℂ) {t : ℝ} (ht : 0 < t)
    (h1 : ψ 1 = (t : ℂ)) : normalizePos ψ t 1 = 1 := by
  simp [normalizePos_apply ψ ht, h1, Complex.ofReal_ne_zero.mpr ht.ne']

private theorem isKMSState_normalizePos (α : CStarAction (Multiplicative ℝ) A) (β : ℝ)
    (ψ : A →P[ℂ] ℂ) {t : ℝ} (ht : 0 < t) (h1 : ψ 1 = (t : ℂ))
    (hkms : ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      ψ (a * α.entireExtension b (β * I)) = ψ (b * a)) :
    α.IsKMSState β (normalizePos ψ t) := by
  refine isKMSState_iff_forall_isEntireAnalytic.mpr ⟨?_, fun x hx y hy => ?_⟩
  · exact Complex.ofReal_injective (by
      simpa [normalizePos_map_one ψ ht h1] using
        PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one (normalizePos ψ t))
  · simp only [normalizePos_apply ψ ht, hkms x hx y hy]

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
    have hφ1 : φc 1 = (r : ℂ) := Complex.ext rfl hpos1.2.symm
    have hψ_kms : α.IsKMSState β (normalizePos φc r) :=
      isKMSState_normalizePos α β φc hr_pos hφ1 hkms
    have hinv := hψ_kms.apply_action hβ t a
    simp only [normalizePos_apply φc hr_pos, φc, PositiveContinuousLinearMap.coe_ofClass] at hinv
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hr_pos.ne')) hinv

/-- If `T := f.gnsRadonNikodym φ` satisfies `B := J₀ T J₀ ∈ M_ω` and `B Ω = T Ω`, then `B`
commutes with `π_ω(α_{iβ}(b))` for every entire analytic `b`. -/
private theorem comm_entireExtension_mul_I_of_gnsRadonNikodym (hω : α.IsKMSState β ω)
    {φ : A →ₚ[ℂ] ℂ} {C : ℝ} (hφ : ∀ a, 0 ≤ a → φ a ≤ (C : ℂ) * ω a)
    (hkms : ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      φ (a * α.entireExtension b (β * I)) = φ (b * a))
    (hB_vN : hω.modularConjugation.conjOperator (ω.toPositiveLinearMap.gnsRadonNikodym φ) ∈
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra)
    (hBΩ : hω.modularConjugation.conjOperator (ω.toPositiveLinearMap.gnsRadonNikodym φ)
        ω.toPositiveLinearMap.gnsVector =
      ω.toPositiveLinearMap.gnsRadonNikodym φ ω.toPositiveLinearMap.gnsVector)
    {b : A} (hb : α.IsEntireAnalytic b) :
    hω.modularConjugation.conjOperator (ω.toPositiveLinearMap.gnsRadonNikodym φ) *
        ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom (α.entireExtension b (β * I)) =
      ω.toPositiveLinearMap.gnsNonUnitalStarAlgHom (α.entireExtension b (β * I)) *
        hω.modularConjugation.conjOperator (ω.toPositiveLinearMap.gnsRadonNikodym φ) := by
  let f := ω.toPositiveLinearMap; let π := f.gnsNonUnitalStarAlgHom
  let T := f.gnsRadonNikodym φ; let B := hω.modularConjugation.conjOperator T
  let c := α.entireExtension b (β * I)
  have hT_comm : T ∈ Set.centralizer (Set.range π) := gnsRadonNikodym_mem_centralizer hφ
  have hB_adj : B ∈ VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) := by
    rwa [← gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom]
  have hc_adj : π c ∈ VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) := by
    rw [← gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom]
    exact f.gnsNonUnitalStarAlgHom_mem_gnsVonNeumannAlgebra c
  suffices hkill : (B * π c - π c * B) (f.toPreGNS 1) = 0 from sub_eq_zero.mp
    (hω.eq_zero_of_apply_toPreGNS_one_eq_zero (sub_mem (mul_mem hB_adj hc_adj)
      (mul_mem hc_adj hB_adj)) hkill)
  rw [sub_apply, sub_eq_zero]
  refine ext_inner_left ℂ fun u => (denseRange_toGNS_entireAnalytic α f).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
  have ha := mem_entireAnalytic.mp a.property
  calc ⟪f.toGNS (a : A), (B * π c) (f.toPreGNS 1)⟫_ℂ
      = ⟪(f.toPreGNS (a : A) : f.GNS), B (f.toPreGNS c)⟫_ℂ := by
        simp [π, mul_apply_eq_comp, toGNS_apply, gnsNonUnitalStarAlgHom_apply_coe]
    _ = ⟪(f.toPreGNS ((a : A) * star b) : f.GNS), B (f.toPreGNS 1)⟫_ℂ :=
        hω.inner_apply_toPreGNS_entireExtension_mul_I hB_adj (a : A) hb
    _ = φ (b * star (a : A)) := by
        rw [← gnsVector_def, hBΩ, gnsVector_def, ← toGNS_apply, ← toGNS_apply,
          inner_gnsRadonNikodym_toGNS hφ]; simp [star_mul]
    _ = φ (star (a : A) * c) := (hkms (star (a : A)) ha.star b hb).symm
    _ = ⟪f.toGNS (a : A), (T * π c) f.gnsVector⟫_ℂ := by
        simpa [f, π, mul_apply_eq_comp, toGNS_apply, gnsVector_def,
          gnsNonUnitalStarAlgHom_apply_coe] using (inner_gnsRadonNikodym_toGNS hφ (a : A) c).symm
    _ = ⟪f.toGNS (a : A), (π c * B) (f.toPreGNS 1)⟫_ℂ := by
        rw [← hT_comm _ ⟨c, rfl⟩, mul_apply_eq_comp, mul_apply_eq_comp, ← gnsVector_def, hBΩ]

/-- **Dominated KMS functionals have central Radon–Nikodym operators.** If `ω` is a β-KMS state
and `φ` is a positive linear functional dominated by a scalar multiple of `ω` that satisfies the
analytic β-KMS identity, then its GNS Radon–Nikodym operator lies in the centre `M_ω ⊓ M_ω'`. -/
theorem IsKMSState.gnsRadonNikodym_mem_center (hω : α.IsKMSState β ω) {φ : A →ₚ[ℂ] ℂ}
    {C : ℝ} (hφ : ∀ a, 0 ≤ a → φ a ≤ (C : ℂ) * ω a)
    (hkms : ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      φ (a * α.entireExtension b (β * I)) = φ (b * a)) :
    ω.toPositiveLinearMap.gnsRadonNikodym φ ∈
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra ⊓
        ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant := by
  let f := ω.toPositiveLinearMap; let π := f.gnsNonUnitalStarAlgHom; let T := f.gnsRadonNikodym φ
  have hT_comm : T ∈ f.gnsVonNeumannAlgebra.commutant :=
    f.mem_gnsVonNeumannAlgebra_commutant_iff.mpr fun a =>
      gnsRadonNikodym_mem_centralizer (f := f) hφ (π a) ⟨a, rfl⟩
  have hT_sa : IsSelfAdjoint T := f.isSelfAdjoint_gnsRadonNikodym φ
  -- 1. Show `J₀ T Ω = T Ω`.
  have hJTΩ : hω.modularConjugation (T f.gnsVector) = T f.gnsVector := by
    rcases eq_or_ne β 0 with rfl | hβ
    · rw [hω.modularConjugation_apply_gnsVector_of_zero hT_comm, hT_sa.star_eq]
    · have hinv_ω : ∀ s a, f (α s a) = f a := fun s a => hω.apply_action hβ s a
      have hUcomm (s : Multiplicative ℝ) :=
        (α.gnsImplementingGroup_commute_gnsRadonNikodym hinv_ω hφ
          (apply_action_of_analytic_kms hβ hkms) s).eq
      rw [hω.modularConjugation_apply_gnsVector_of_commute hβ hT_comm hUcomm, hT_sa.star_eq]
  -- 2. Set `B := J₀ T J₀ ∈ M_ω`, which satisfies `B Ω = T Ω`.
  let B := hω.modularConjugation.conjOperator T
  have hB_vN : B ∈ f.gnsVonNeumannAlgebra :=
    hω.conjOperator_modularConjugation_mem_gnsVonNeumannAlgebra hT_comm
  have hBΩ : B f.gnsVector = T f.gnsVector := by
    simp [B, f, LinearIsometryEquiv.conjOperator_apply, hω.modularConjugation_symm, hJTΩ]
  -- 3. Show `B` commutes with `π(A)`.
  have hB_comm : B ∈ f.gnsVonNeumannAlgebra.commutant := by
    refine f.mem_gnsVonNeumannAlgebra_commutant_iff.mpr fun a => ?_
    refine congrFun (Continuous.ext_on α.dense_entireAnalytic
      ((map_continuous π).mul continuous_const) (continuous_const.mul (map_continuous π))
      fun c hc => ?_) a
    simpa [entireExtension_entireExtension, (mem_entireAnalytic.mp hc).entireExtension_apply_zero]
      using (comm_entireExtension_mul_I_of_gnsRadonNikodym hω hφ hkms hB_vN hBΩ
        (isEntireAnalytic_entireExtension α c (-(β * I)))).symm
  -- 4. Conclude `B = T` using cyclicity of `Ω`, hence `T ∈ M_ω ⊓ M_ω'`.
  have hBT : B = T := by
    ext v; refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop))
      fun a => ?_
    calc B (f.toGNS a) = (B * π a) f.gnsVector := by
          simp [π, mul_apply_eq_comp, toGNS_apply, gnsVector_def, gnsNonUnitalStarAlgHom_apply_coe]
      _ = (T * π a) f.gnsVector := by
          rw [← f.mem_gnsVonNeumannAlgebra_commutant_iff.mp hB_comm a, mul_apply_eq_comp, hBΩ,
            ← mul_apply_eq_comp, f.mem_gnsVonNeumannAlgebra_commutant_iff.mp hT_comm a]
      _ = T (f.toGNS a) := by
          simp [π, mul_apply_eq_comp, toGNS_apply, gnsVector_def, gnsNonUnitalStarAlgHom_apply_coe]
  exact VonNeumannAlgebra.mem_inf.mpr ⟨by simpa only [f, T, ← hBT] using hB_vN, hT_comm⟩

/-- Normalizing the vector functional of a positive commutant operator by `t > 0` yields a positive
continuous linear functional. -/
private def kmsStateOfCentralPositive {f : A →ₚ[ℂ] ℂ} {y : f.GNS →L[ℂ] f.GNS}
    (hy : y ∈ f.gnsVonNeumannAlgebra.commutant) (hy_pos : y.IsPositive) (t : ℝ) : A →P[ℂ] ℂ :=
  normalizePos (.mk₀ (f.gnsVectorFunctional y) fun _ ha =>
    gnsVectorFunctional_nonneg f
      (by simpa only [← SetLike.mem_coe, coe_commutant_gnsVonNeumannAlgebra] using hy) hy_pos ha) t

@[simp]
private theorem kmsStateOfCentralPositive_apply {f : A →ₚ[ℂ] ℂ} {y : f.GNS →L[ℂ] f.GNS}
    (hy : y ∈ f.gnsVonNeumannAlgebra.commutant) (hy_pos : y.IsPositive)
    {t : ℝ} (ht_pos : 0 < t) (a : A) :
    kmsStateOfCentralPositive hy hy_pos t a = ((t⁻¹ : ℝ) : ℂ) * f.gnsVectorFunctional y a :=
  normalizePos_apply _ ht_pos a

private theorem isKMSState_kmsStateOfCentralPositive (hω : α.IsKMSState β ω)
    {y : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hyZ : y ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra ⊓
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant)
    (hy_pos : y.IsPositive) {t : ℝ} (ht_pos : 0 < t)
    (hyΩ : ⟪ω.toPositiveLinearMap.gnsVector, y ω.toPositiveLinearMap.gnsVector⟫_ℂ = t) :
    α.IsKMSState β
      (kmsStateOfCentralPositive (VonNeumannAlgebra.mem_inf.mp hyZ).2 hy_pos t) :=
  isKMSState_normalizePos α β _ ht_pos
    (by simpa [PositiveContinuousLinearMap.mk₀_apply, gnsVectorFunctional_apply, ← gnsVector_def]
      using hyΩ)
    fun a _ b hb => hω.gnsVectorFunctional_mul_entireExtension_mul_I hyZ a hb

/-- Operator order bounds `(1/4) • 1 ≤ y ≤ (3/4) • 1` for
`y = (1/2) • 1 + (4 (‖z‖ + 1))⁻¹ • z` when `z` is self-adjoint. -/
private theorem half_add_smul_bounds {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {z : H →L[ℂ] H} (hz : IsSelfAdjoint z) :
    let r : ℝ := 4 * (‖z‖ + 1)
    let y : H →L[ℂ] H := (2⁻¹ : ℂ) • 1 + ((r⁻¹ : ℝ) : ℂ) • z
    algebraMap ℝ (H →L[ℂ] H) (1 / 4) ≤ y ∧ y ≤ algebraMap ℝ (H →L[ℂ] H) (3 / 4) := by
  intro r y
  have hr : 0 < r := by positivity
  have h1 : (0 : H →L[ℂ] H) ≤ 1 := ContinuousLinearMap.nonneg_iff_isPositive.mpr isPositive_one
  have hr_norm : r⁻¹ * ‖z‖ ≤ 1 / 4 := by
    have : 4 * ‖z‖ ≤ r := by simp only [r]; linarith
    rw [inv_mul_le_iff₀ hr]; linarith
  have hlo : algebraMap ℝ (H →L[ℂ] H) (-(1 / 4)) ≤ (r⁻¹ : ℝ) • z := by
    refine (smul_le_smul_of_nonneg_right (neg_le_neg hr_norm) h1).trans ?_
    calc (-(r⁻¹ * ‖z‖)) • (1 : H →L[ℂ] H)
        = r⁻¹ • (-algebraMap ℝ (H →L[ℂ] H) ‖z‖) := by
          rw [Algebra.algebraMap_eq_smul_one, neg_smul, smul_neg, smul_smul]
      _ ≤ r⁻¹ • z :=
        smul_le_smul_of_nonneg_left hz.neg_algebraMap_norm_le_self (inv_nonneg.mpr hr.le)
  have hhi : (r⁻¹ : ℝ) • z ≤ algebraMap ℝ (H →L[ℂ] H) (1 / 4) := by
    refine (smul_le_smul_of_nonneg_left hz.le_algebraMap_norm_self (inv_nonneg.mpr hr.le)).trans ?_
    calc r⁻¹ • algebraMap ℝ (H →L[ℂ] H) ‖z‖
        = (r⁻¹ * ‖z‖) • (1 : H →L[ℂ] H) := by rw [Algebra.algebraMap_eq_smul_one, smul_smul]
      _ ≤ algebraMap ℝ (H →L[ℂ] H) (1 / 4) := by
          rw [Algebra.algebraMap_eq_smul_one]; exact smul_le_smul_of_nonneg_right hr_norm h1
  have hy_eq : y = algebraMap ℝ (H →L[ℂ] H) (1 / 2) + (r⁻¹ : ℝ) • z := by
    simp only [y, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, one_div,
      Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [hy_eq]
  refine ⟨?_, ?_⟩
  · calc algebraMap ℝ (H →L[ℂ] H) (1 / 4)
        = algebraMap ℝ (H →L[ℂ] H) (1 / 2) + algebraMap ℝ (H →L[ℂ] H) (-(1 / 4)) := by
          rw [← map_add]; norm_num
      _ ≤ algebraMap ℝ (H →L[ℂ] H) (1 / 2) + (r⁻¹ : ℝ) • z := add_le_add_right hlo _
  · calc algebraMap ℝ (H →L[ℂ] H) (1 / 2) + (r⁻¹ : ℝ) • z
        ≤ algebraMap ℝ (H →L[ℂ] H) (1 / 2) + algebraMap ℝ (H →L[ℂ] H) (1 / 4) :=
          add_le_add_right hhi _
      _ = algebraMap ℝ (H →L[ℂ] H) (3 / 4) := by rw [← map_add]; norm_num

/-- Quadratic-form bounds `(1/4)‖v‖² ≤ Re ⟪y v, v⟫ ≤ (3/4)‖v‖²` for the perturbation
`y = (1/2) • 1 + (4 (‖z‖ + 1))⁻¹ • z` when `z` is self-adjoint. -/
private theorem re_inner_half_add_smul_bounds {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {z : H →L[ℂ] H} (hz : IsSelfAdjoint z) (v : H) :
    let r : ℝ := 4 * (‖z‖ + 1)
    let y : H →L[ℂ] H := (2⁻¹ : ℂ) • 1 + ((r⁻¹ : ℝ) : ℂ) • z
    (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (⟪y v, v⟫_ℂ).re ∧ (⟪y v, v⟫_ℂ).re ≤ (3 / 4 : ℝ) * ‖v‖ ^ 2 := by
  intro r y
  obtain ⟨hlo, hhi⟩ := half_add_smul_bounds hz
  have h1 := (Complex.le_def.mp ((ContinuousLinearMap.le_def.mp hlo).inner_nonneg_left v)).1
  have h2 := (Complex.le_def.mp ((ContinuousLinearMap.le_def.mp hhi).inner_nonneg_left v)).1
  have hv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self,
    inner_sub_left, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re,
    hv, sub_nonneg] at h1 h2
  exact ⟨h1, h2⟩

/-- For a self-adjoint operator `z`, `y = (1/2) • 1 + (4 (‖z‖ + 1))⁻¹ • z` and `1 - y` are
both positive. -/
private theorem isPositive_half_add_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {z : H →L[ℂ] H} (hz : IsSelfAdjoint z) :
    let y : H →L[ℂ] H := (2⁻¹ : ℂ) • 1 + (((4 * (‖z‖ + 1))⁻¹ : ℝ) : ℂ) • z
    y.IsPositive ∧ (1 - y).IsPositive := by
  intro y
  obtain ⟨hlo, hhi⟩ := half_add_smul_bounds hz
  have h1 : (0 : H →L[ℂ] H) ≤ 1 := ContinuousLinearMap.nonneg_iff_isPositive.mpr isPositive_one
  have h0 : (0 : H →L[ℂ] H) ≤ algebraMap ℝ (H →L[ℂ] H) (1 / 4) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_nonneg (by norm_num) h1
  have h34 : algebraMap ℝ (H →L[ℂ] H) (3 / 4) ≤ 1 := by
    rw [Algebra.algebraMap_eq_smul_one]
    simpa using smul_le_smul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ 1) h1
  have h1y : (0 : H →L[ℂ] H) ≤ 1 - y := sub_nonneg.mpr (hhi.trans h34)
  exact ⟨ContinuousLinearMap.nonneg_iff_isPositive.mp (h0.trans hlo),
    ContinuousLinearMap.nonneg_iff_isPositive.mp h1y⟩

/-- The canonical GNS vector of a KMS state has norm one. -/
private theorem IsKMSState.norm_gnsVector (hω : α.IsKMSState β ω) :
    ‖ω.toPositiveLinearMap.gnsVector‖ = 1 :=
  ω.toPositiveLinearMap.norm_gnsVector (by
    simpa using (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω).symm.trans
      (by rw [hω.norm_eq_one, Complex.ofReal_one]))

/-- A central operator in the GNS representation of a β-KMS state is uniquely determined by its
vector functional on `Ω`. -/
private theorem IsKMSState.eq_smul_one_of_gnsVectorFunctional_eq (hω : α.IsKMSState β ω)
    {T : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hT : T ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra ⊓
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant)
    {c : ℂ} (hval : ∀ a : A, ω.toPositiveLinearMap.gnsVectorFunctional T a = c * ω a) :
    T = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) := by
  let f := ω.toPositiveLinearMap
  obtain ⟨hsubM, hsubM'⟩ := VonNeumannAlgebra.mem_inf.mp
    (sub_mem hT (SMulMemClass.smul_mem c (one_mem _)))
  have hvan : f.gnsVectorFunctional (T - c • (1 : f.GNS →L[ℂ] f.GNS)) = 0 := by
    ext a; simp [gnsVectorFunctional_sub, gnsVectorFunctional_smul,
      show f.gnsVectorFunctional T a = c * f a from hval a]
  have hsubM_adj : T - c • (1 : f.GNS →L[ℂ] f.GNS) ∈
      VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) := by
    rwa [← gnsVonNeumannAlgebra_eq_adjoin_range_gnsStarAlgHom]
  have hsubM'_cent : T - c • (1 : f.GNS →L[ℂ] f.GNS) ∈
      Set.centralizer (Set.range f.gnsNonUnitalStarAlgHom) := by
    simpa only [← SetLike.mem_coe, coe_commutant_gnsVonNeumannAlgebra] using hsubM'
  exact sub_eq_zero.mp (hω.eq_zero_of_apply_toPreGNS_one_eq_zero hsubM_adj (by
    rw [← gnsVector_def]
    exact apply_gnsVector_eq_zero_of_gnsVectorFunctional_eq_zero f hsubM'_cent hvan))

/-- Self-adjoint operators in the GNS centre of an extreme β-KMS state are scalar multiples of
the identity. -/
private theorem eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint (hω : α.IsKMSState β ω)
    (hext : StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β))
    {z : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hz : z ∈ ω.toPositiveLinearMap.gnsVonNeumannAlgebra ⊓
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.commutant)
    (hz_sa : IsSelfAdjoint z) :
    ∃ c : ℂ, z = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) := by
  -- Shift and scale `z` into `[1/4, 3/4]` via `y = (1/2) • 1 + (4 (‖z‖ + 1))⁻¹ • z` so that
  -- `ω = t ω₁ + (1 - t) ω₂` is a proper convex combination of KMS vector states `ω₁, ω₂` of `y`
  -- and `1 - y`; extremality forces `ω₁ = ω`, hence `y = t • 1` by uniqueness on the centre.
  let f := ω.toPositiveLinearMap
  let Z : VonNeumannAlgebra f.GNS := f.gnsVonNeumannAlgebra ⊓ f.gnsVonNeumannAlgebra.commutant
  set r : ℝ := 4 * (‖z‖ + 1); have hr : 0 < r := by positivity
  let y : f.GNS →L[ℂ] f.GNS := (2⁻¹ : ℂ) • 1 + ((r⁻¹ : ℝ) : ℂ) • z
  have hyZ : y ∈ Z := add_mem (SMulMemClass.smul_mem _ (one_mem Z)) (SMulMemClass.smul_mem _ hz)
  have h1yZ : (1 : f.GNS →L[ℂ] f.GNS) - y ∈ Z := sub_mem (one_mem Z) hyZ
  obtain ⟨hy_pos, h1y_pos⟩ := isPositive_half_add_smul hz_sa
  have hΩ_norm : ‖f.gnsVector‖ = 1 := hω.norm_gnsVector
  set t : ℝ := (⟪y f.gnsVector, f.gnsVector⟫_ℂ).re
  have ht_bounds : (1 / 4 : ℝ) ≤ t ∧ t ≤ 3 / 4 := by
    simpa only [t, y, r, hΩ_norm, one_pow, mul_one] using
      re_inner_half_add_smul_bounds hz_sa f.gnsVector
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
        (StrongDual.toWeakDual
          (kmsStateOfCentralPositive (VonNeumannAlgebra.mem_inf.mp hyZ).2 hy_pos t :
            A →L[ℂ] ℂ))
        (StrongDual.toWeakDual
          (kmsStateOfCentralPositive (VonNeumannAlgebra.mem_inf.mp h1yZ).2 h1y_pos (1 - t) :
            A →L[ℂ] ℂ)) := by
    refine ⟨t, 1 - t, ht_pos, h1t_pos, add_sub_cancel t 1, DFunLike.ext _ _ fun a => ?_⟩
    simp only [_root_.add_apply, _root_.smul_apply, StrongDual.toWeakDual_apply,
      PositiveContinuousLinearMap.coe_toContinuousLinearMap, Complex.real_smul,
      kmsStateOfCentralPositive_apply _ _ ht_pos, kmsStateOfCentralPositive_apply _ _ h1t_pos]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht_pos.ne', Complex.ofReal_one,
      one_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h1t_pos.ne', Complex.ofReal_one,
      one_mul, gnsVectorFunctional_sub, sub_apply, gnsVectorFunctional_one, add_sub_cancel]
    simp [f]
  have hω₁_eq := (mem_extremePoints_iff_left.mp hext).2 _ (toWeakDual_mem_kmsStates_iff.mpr
      (isKMSState_kmsStateOfCentralPositive hω hyZ hy_pos ht_pos hyΩ)) _
    (toWeakDual_mem_kmsStates_iff.mpr
      (isKMSState_kmsStateOfCentralPositive hω h1yZ h1y_pos h1t_pos h1yΩ)) hseg
  have hy_eq : y = (t : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) :=
    hω.eq_smul_one_of_gnsVectorFunctional_eq hyZ fun a => by
      have heval := DFunLike.congr_fun hω₁_eq a
      simp only [StrongDual.toWeakDual_apply, PositiveContinuousLinearMap.coe_toContinuousLinearMap,
        kmsStateOfCentralPositive_apply _ _ ht_pos] at heval
      simpa [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht_pos.ne'), f] using
        congrArg (fun w => (t : ℂ) * w) heval
  refine ⟨(r : ℂ) * ((t : ℂ) - 2⁻¹), ?_⟩
  have hrz : ((r⁻¹ : ℝ) : ℂ) • z = ((t : ℂ) - 2⁻¹) • (1 : f.GNS →L[ℂ] f.GNS) := by
    rw [sub_smul]; exact eq_sub_of_add_eq' hy_eq
  simpa [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')] using
    congrArg (fun S : f.GNS →L[ℂ] f.GNS => (r : ℂ) • S) hrz

/-- A β-KMS factor state is an extreme point of `α.kmsStates β`. -/
private theorem mem_extremePoints_kmsStates_of_isFactor (hω : α.IsKMSState β ω)
    (hfactor : ω.toPositiveLinearMap.gnsVonNeumannAlgebra.IsFactor) :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β) := by
  let f := ω.toPositiveLinearMap
  refine mem_extremePoints_iff_left.mpr ⟨toWeakDual_mem_kmsStates_iff.mpr hω, ?_⟩
  rintro φ₁ hφ₁ φ₂ hφ₂ ⟨s, t, hs, ht, _, hcomb⟩
  obtain ⟨ω₁, hω₁, rfl⟩ := mem_kmsStates_iff.mp hφ₁
  obtain ⟨ω₂, _, rfl⟩ := mem_kmsStates_iff.mp hφ₂
  let φc : A →P[ℂ] ℂ := Real.toNNReal s • ω₁
  let φ : A →ₚ[ℂ] ℂ := φc.toPositiveLinearMap
  have hφ_apply (a : A) : φ a = (s : ℂ) * ω₁ a := by
    simp [φ, φc, NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _ hs.le]
  have hcomb_apply (a : A) : (s : ℂ) * ω₁ a + (t : ℂ) * ω₂ a = ω a := by
    simpa only [_root_.add_apply, _root_.smul_apply, StrongDual.toWeakDual_apply,
      PositiveContinuousLinearMap.coe_toContinuousLinearMap, Complex.real_smul] using
      DFunLike.congr_fun hcomb a
  have hdom : ∀ a, 0 ≤ a → φ a ≤ (1 : ℂ) * ω a := fun a ha => by
    rw [one_mul, hφ_apply, ← hcomb_apply a, le_add_iff_nonneg_right]
    exact mul_nonneg (Complex.le_def.mpr ⟨ht.le, by simp⟩) (ω₂.map_nonneg ha)
  have hT_center := VonNeumannAlgebra.mem_inf.mp (hω.gnsRadonNikodym_mem_center hdom
    fun a _ b hb => by simp only [hφ_apply, hω₁.apply_mul_entireExtension_mul_I a hb])
  obtain ⟨c, hc⟩ := hfactor.exists_eq_smul_one hT_center.1 hT_center.2
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
extreme point of `α.kmsStates β` in the weak-* dual if and only if its GNS von Neumann algebra
`ω.toPositiveLinearMap.gnsVonNeumannAlgebra` is a factor. -/
theorem mem_extremePoints_kmsStates_iff (α : CStarAction (Multiplicative ℝ) A) (β : ℝ)
    (ω : A →P[ℂ] ℂ) (hω : α.IsKMSState β ω) :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β) ↔
      ω.toPositiveLinearMap.gnsVonNeumannAlgebra.IsFactor := by
  refine ⟨fun hext => ?_, mem_extremePoints_kmsStates_of_isFactor hω⟩
  rw [VonNeumannAlgebra.isFactor_def]
  refine ⟨fun h10 => ?_, fun z hzM hzM' => ?_⟩
  · let f := ω.toPositiveLinearMap
    have hΩ : ‖f.gnsVector‖ = 1 := hω.norm_gnsVector
    have h0 : f.gnsVector = 0 := by
      simpa using congrArg (fun T : f.GNS →L[ℂ] f.GNS => T f.gnsVector) h10
    rw [h0, norm_zero] at hΩ
    exact one_ne_zero hΩ.symm
  · let f := ω.toPositiveLinearMap
    let Z : VonNeumannAlgebra f.GNS := f.gnsVonNeumannAlgebra ⊓ f.gnsVonNeumannAlgebra.commutant
    have hzZ : z ∈ Z := VonNeumannAlgebra.mem_inf.mpr ⟨hzM, hzM'⟩
    have hxZ : (ℜ z : f.GNS →L[ℂ] f.GNS) ∈ Z := by
      rw [realPart_apply_coe, ← Complex.coe_smul]
      exact SMulMemClass.smul_mem _ (add_mem hzZ (star_mem hzZ))
    have hyZ : (ℑ z : f.GNS →L[ℂ] f.GNS) ∈ Z := by
      rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
      exact SMulMemClass.smul_mem _ (SMulMemClass.smul_mem _ (sub_mem hzZ (star_mem hzZ)))
    obtain ⟨c₁, hc₁⟩ := eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint hω hext hxZ (ℜ z).property
    obtain ⟨c₂, hc₂⟩ := eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint hω hext hyZ (ℑ z).property
    refine ⟨c₁ + I * c₂, ?_⟩
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart z]
    rw [hc₁, hc₂, smul_smul, ← add_smul]

end TauCeti.CStarAction
