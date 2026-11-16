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
import TauCeti.Analysis.CStarAlgebra.Action.KMS.ModularConjugation
import TauCeti.Analysis.CStarAlgebra.Action.KMS.Separating
import TauCeti.Analysis.VonNeumannAlgebra.Lattice
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Extreme KMS states and factor states

Let `α` be a point-norm continuous real action on a unital C⋆-algebra `A`, let `β : ℝ`, and let
`ω` be a β-KMS state of `α` with GNS representation `π_ω = ω.toPositiveLinearMap.gnsStarAlgHom`
and GNS von Neumann algebra `M = π_ω(A)''`. Its centre is `Z = π_ω(A)' ∩ π_ω(A)''`.

This file proves Bratteli–Robinson's characterization of the extreme points of the KMS simplex
`K_β = α.kmsStates β` in the weak-* dual: a β-KMS state `ω` is an extreme point of `K_β` if and
only if it is a factor state, meaning that the centre `Z` consists of scalar multiples of the
identity (`TauCeti.CStarAction.mem_extremePoints_kmsStates_iff`). The theorem holds for every real
`β`, including `β = 0`, where `K_0` is the set of tracial states.

The proof establishes the two halves of the correspondence between dominated β-KMS functionals and
positive central operators:

* `TauCeti.CStarAction.IsKMSState.gnsVectorFunctional_mul_entireExtension_mul_I`: every central
  operator `z ∈ Z` induces a vector functional `a ↦ ⟪Ω, z π_ω(a) Ω⟫` satisfying the analytic β-KMS
  identity, by the separating-vector KMS identity on `M`. Any non-scalar self-adjoint `z ∈ Z`
  therefore splits `ω` into a nontrivial convex combination in `K_β`.
* `TauCeti.CStarAction.IsKMSState.gnsRadonNikodym_mem_center`: conversely, if a positive functional
  `φ` is dominated by a scalar multiple of `ω` and satisfies the analytic β-KMS identity, then its
  GNS Radon–Nikodym operator `T ∈ M'` actually lies in the centre `Z`. The proof uses the modular
  conjugation `J₀` and Tomita commutation `J₀ M' J₀ ⊆ M` from
  `TauCeti.Analysis.CStarAlgebra.Action.KMS.ModularConjugation`, together with the separating
  property of `Ω`, to show `J₀ T J₀ = T`.

## Main statements

* `TauCeti.CStarAction.IsKMSState.gnsVectorFunctional_mul_entireExtension_mul_I`: vector functionals
  of central operators satisfy the analytic β-KMS identity.
* `TauCeti.CStarAction.IsKMSState.gnsRadonNikodym_mem_center`: the GNS Radon–Nikodym operator of a
  dominated β-KMS functional lies in the centre `π_ω(A)' ∩ π_ω(A)''`.
* `TauCeti.CStarAction.mem_extremePoints_kmsStates_iff`: a β-KMS state is an extreme point of
  `α.kmsStates β` if and only if the centre `π_ω(A)' ∩ π_ω(A)''` consists of scalar multiples of
  the identity.

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

/-- The von Neumann algebra `VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom)` has carrier
`Set.centralizer (Set.centralizer (Set.range f.gnsStarAlgHom))`. -/
private theorem mem_adjoin_gnsStarAlgHom_iff (f : A →ₚ[ℂ] ℂ) {x : f.GNS →L[ℂ] f.GNS} :
    x ∈ VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) ↔
      x ∈ Set.centralizer (Set.centralizer (Set.range f.gnsStarAlgHom)) := by
  have hrange : (f.gnsNonUnitalStarAlgHom.range : Set _) = Set.range f.gnsStarAlgHom :=
    NonUnitalStarAlgHom.coe_range f.gnsNonUnitalStarAlgHom
  rw [← SetLike.mem_coe, ← hrange,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset, hrange]

/-- The centre of the GNS von Neumann algebra `M = π_ω(A)''` as a von Neumann algebra
`M.commutant ⊓ M`, whose carrier is `π_ω(A)' ∩ π_ω(A)''`. -/
private theorem mem_center_gnsStarAlgHom_iff (f : A →ₚ[ℂ] ℂ) {x : f.GNS →L[ℂ] f.GNS} :
    x ∈ (VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom)).commutant ⊓
        VonNeumannAlgebra.adjoin (Set.range f.gnsStarAlgHom) ↔
      x ∈ Set.centralizer (Set.range f.gnsStarAlgHom) ∩
        Set.centralizer (Set.centralizer (Set.range f.gnsStarAlgHom)) := by
  have hrange : (f.gnsNonUnitalStarAlgHom.range : Set _) = Set.range f.gnsStarAlgHom :=
    NonUnitalStarAlgHom.coe_range f.gnsNonUnitalStarAlgHom
  rw [VonNeumannAlgebra.mem_inf, ← SetLike.mem_coe, ← SetLike.mem_coe, ← hrange,
    VonNeumannAlgebra.coe_commutant_adjoin,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset,
    Set.union_eq_left.mpr (StarMemClass.star_coe_eq _).subset, hrange]
  rfl

/-- **Central operators preserve the analytic KMS identity.** For a β-KMS state `ω` and an operator
`z` in the centre `π_ω(A)' ∩ π_ω(A)''`, the vector functional `a ↦ ⟪Ω, z π_ω(a) Ω⟫` satisfies
`φ (a α_{iβ}(b)) = φ (b a)` for every `a : A` and entire analytic `b : A`. -/
theorem IsKMSState.gnsVectorFunctional_mul_entireExtension_mul_I (hω : α.IsKMSState β ω)
    {z : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hz : z ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)))
    (a : A) {b : A} (hb : α.IsEntireAnalytic b) :
    ω.toPositiveLinearMap.gnsVectorFunctional z (a * α.entireExtension b (β * I)) =
      ω.toPositiveLinearMap.gnsVectorFunctional z (b * a) := by
  let f := ω.toPositiveLinearMap
  let π := f.gnsStarAlgHom
  have hzvN : z ∈ VonNeumannAlgebra.adjoin (Set.range π) :=
    (mem_adjoin_gnsStarAlgHom_iff f).mpr hz.2
  have hcomm (x : A) : π x * z = z * π x := hz.1 _ ⟨x, rfl⟩
  have hcomm_apply (x : A) (v : f.GNS) : z (π x v) = π x (z v) := by
    simpa [mul_apply_eq_comp] using congrArg (fun T => T v) (hcomm x).symm
  calc
    f.gnsVectorFunctional z (a * α.entireExtension b (β * I))
        = ⟪f.gnsVector, π a (z (π (α.entireExtension b (β * I)) f.gnsVector))⟫_ℂ := by
          rw [gnsVectorFunctional_apply, map_mul, mul_apply_eq_comp, hcomm_apply]
    _ = ⟪(f.toPreGNS (star a) : f.GNS),
          z (f.toPreGNS (α.entireExtension b (β * I)) : f.GNS)⟫_ℂ := by
          have hπa : π a = star (π (star a)) := by rw [map_star, star_star]
          rw [hπa, star_eq_adjoint, adjoint_inner_right]
          simp [π, gnsVector_def]
    _ = ⟪(f.toPreGNS (star a * star b) : f.GNS), z (f.toPreGNS 1 : f.GNS)⟫_ℂ :=
          hω.inner_apply_toPreGNS_entireExtension_mul_I hzvN (star a) hb
    _ = ⟪π (star (b * a)) f.gnsVector, z f.gnsVector⟫_ℂ := by
          simp [π, star_mul, gnsVector_def]
    _ = ⟪f.gnsVector, π (b * a) (z f.gnsVector)⟫_ℂ := by
          rw [map_star, star_eq_adjoint, adjoint_inner_left]
    _ = f.gnsVectorFunctional z (b * a) := by
          rw [← hcomm_apply, gnsVectorFunctional_apply]

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
  · have hzero : (φc : A →L[ℂ] ℂ) = 0 := by
      rw [h1, Complex.ofReal_eq_zero, norm_eq_zero] at hnorm_eq
      exact hnorm_eq
    have hφ0 (x : A) : φ x = 0 := by
      simpa [φc] using DFunLike.congr_fun hzero x
    rw [hφ0, hφ0]
  · have hpos1 : 0 ≤ φ 1 := φ.map_nonneg zero_le_one
    have hr_pos : 0 < (φ 1).re := by
      have hre_nonneg : 0 ≤ (φ 1).re := (Complex.le_def.mp hpos1).1
      have him : (φ 1).im = 0 := (Complex.le_def.mp hpos1).2.symm
      refine lt_of_le_of_ne hre_nonneg fun h => h1 ?_
      exact Complex.ext h.symm him
    have hr_eq : ((φ 1).re : ℂ) = φ 1 :=
      Complex.ext rfl (Complex.le_def.mp hpos1).2
    let r : ℝ := (φ 1).re
    have hr_inv_nonneg : (0 : ℂ) ≤ ((r⁻¹ : ℝ) : ℂ) := by
      rw [Complex.le_def]
      exact ⟨inv_nonneg.mpr hr_pos.le, by simp⟩
    let ψ : A →P[ℂ] ℂ := .mk₀ (((r⁻¹ : ℝ) : ℂ) • (φc : A →L[ℂ] ℂ)) fun x hx =>
      mul_nonneg hr_inv_nonneg (φ.map_nonneg hx)
    have hψ_apply (x : A) : ψ x = ((r⁻¹ : ℝ) : ℂ) * φ x := by
      simp [ψ, φc]
    have hψ1 : ψ 1 = 1 := by
      rw [hψ_apply, ← hr_eq, ← Complex.ofReal_mul, inv_mul_cancel₀ hr_pos.ne', Complex.ofReal_one]
    have hψ_norm : ‖(ψ : A →L[ℂ] ℂ)‖ = 1 := by
      have h := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ψ
      rw [hψ1] at h
      exact Complex.ofReal_injective (by simpa using h)
    have hψ_kms : α.IsKMSState β ψ := by
      refine isKMSState_iff_forall_isEntireAnalytic.mpr ⟨hψ_norm, fun x hx y hy => ?_⟩
      rw [hψ_apply, hψ_apply, hkms x hx y hy]
    have hψ_inv := hψ_kms.apply_action hβ t a
    rw [hψ_apply, hψ_apply] at hψ_inv
    have hne : ((r⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hr_pos.ne')
    exact mul_left_cancel₀ hne hψ_inv

/-- **Dominated KMS functionals have central Radon–Nikodym operators.** If `ω` is a β-KMS state
and `φ` is a positive linear functional dominated by a scalar multiple of `ω` that satisfies the
analytic β-KMS identity, then its GNS Radon–Nikodym operator lies in the centre
`π_ω(A)' ∩ π_ω(A)''`. -/
theorem IsKMSState.gnsRadonNikodym_mem_center (hω : α.IsKMSState β ω) {φ : A →ₚ[ℂ] ℂ} {C : ℝ}
    (hφ : ∀ a, 0 ≤ a → φ a ≤ (C : ℂ) * ω a)
    (hkms : ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      φ (a * α.entireExtension b (β * I)) = φ (b * a)) :
    ω.toPositiveLinearMap.gnsRadonNikodym φ ∈
      Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
        Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)) := by
  let f := ω.toPositiveLinearMap
  let π := f.gnsStarAlgHom
  let T := f.gnsRadonNikodym φ
  have hT_comm : T ∈ Set.centralizer (Set.range π) :=
    gnsRadonNikodym_mem_centralizer_gnsStarAlgHom hφ
  have hT_sa : IsSelfAdjoint T := f.isSelfAdjoint_gnsRadonNikodym φ
  -- Step 1: `J₀ (T Ω) = T Ω`.
  have hJTΩ : hω.modularConjugation (T f.gnsVector) = T f.gnsVector := by
    rcases eq_or_ne β 0 with rfl | hβ
    · rw [hω.modularConjugation_apply_gnsVector_of_zero hT_comm, hT_sa.star_eq]
    · have hinv_ω : ∀ s a, f (α s a) = f a := fun s a => hω.apply_action hβ s a
      have hinv_φ : ∀ s a, φ (α s a) = φ a := fun s a =>
        apply_action_of_analytic_kms hβ hkms s a
      let U := α.gnsImplementingGroup hinv_ω
      have hU := α.isUnitary_gnsImplementingGroup hinv_ω
      have hUcomm (t : Multiplicative ℝ) : U t * T = T * U t := by
        ext v
        refine ext_inner_left ℂ fun u => ?_
        refine f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop))
          fun a => ?_
        refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop))
          fun b => ?_
        simp only [mul_apply_eq_comp]
        have h1 : ⟪f.toGNS a, U t (T (f.toGNS b))⟫_ℂ =
            ⟪U t⁻¹ (f.toGNS a), T (f.toGNS b)⟫_ℂ := by
          rw [← hU.adjoint_eq_inv t, adjoint_inner_left]
        have hUa (x : A) (g : Multiplicative ℝ) : U g (f.toGNS x) = f.toGNS (α g x) := by
          simp [U, toGNS_apply]
        rw [h1, hUa, hUa, inner_gnsRadonNikodym_toGNS hφ, inner_gnsRadonNikodym_toGNS hφ]
        have hstar : star (α t⁻¹ a) * b = α t⁻¹ (star a * α t b) := by
          rw [map_mul, map_star, ← CStarAction.mul_apply, inv_mul_cancel, CStarAction.one_apply]
        rw [hstar, hinv_φ]
      rw [hω.modularConjugation_apply_gnsVector_of_commute hβ hT_comm hUcomm, hT_sa.star_eq]
  -- Step 2: `B := J₀ T J₀ ∈ M` satisfies `B Ω = T Ω` and commutes with `π(A)`.
  let B := hω.conjModularConjugation T
  have hB_vN : B ∈ VonNeumannAlgebra.adjoin (Set.range π) :=
    hω.conjModularConjugation_mem_adjoin hT_comm
  have hBΩ : B f.gnsVector = T f.gnsVector := by
    simp [B, f, hJTΩ]
  have hB_comm_entire_shift {b : A} (hb : α.IsEntireAnalytic b) :
      B * π (α.entireExtension b (β * I)) = π (α.entireExtension b (β * I)) * B := by
    let c := α.entireExtension b (β * I)
    have hmem : B * π c - π c * B ∈ VonNeumannAlgebra.adjoin (Set.range π) := by
      have hc : π c ∈ VonNeumannAlgebra.adjoin (Set.range π) :=
        VonNeumannAlgebra.subset_adjoin _ ⟨c, rfl⟩
      exact sub_mem (mul_mem hB_vN hc) (mul_mem hc hB_vN)
    suffices hkill : (B * π c - π c * B) (f.toPreGNS 1) = 0 from
      sub_eq_zero.mp (hω.eq_zero_of_apply_toPreGNS_one_eq_zero hmem hkill)
    rw [sub_apply, sub_eq_zero]
    refine ext_inner_left ℂ fun u => ?_
    refine (denseRange_toGNS_entireAnalytic α f).induction_on u
      (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
    have ha := mem_entireAnalytic.mp a.2
    have hTcomm_c : π c * T = T * π c := hT_comm _ ⟨c, rfl⟩
    calc
      ⟪f.toGNS (a : A), (B * π c) (f.toPreGNS 1)⟫_ℂ
          = ⟪(f.toPreGNS (a : A) : f.GNS), B (f.toPreGNS c)⟫_ℂ := by
            simp [π, mul_apply_eq_comp, toGNS_apply, ← gnsVector_def]
      _ = ⟪(f.toPreGNS ((a : A) * star b) : f.GNS), B (f.toPreGNS 1)⟫_ℂ :=
            hω.inner_apply_toPreGNS_entireExtension_mul_I hB_vN (a : A) hb
      _ = ⟪f.toGNS ((a : A) * star b), T (f.toGNS 1)⟫_ℂ := by
            rw [← gnsVector_def, hBΩ, gnsVector_def, ← toGNS_apply, ← toGNS_apply]
      _ = φ (b * star (a : A)) := by
            rw [inner_gnsRadonNikodym_toGNS hφ]
            simp [star_mul]
      _ = φ (star (a : A) * c) := (hkms (star (a : A)) ha.star b hb).symm
      _ = ⟪f.toGNS (a : A), T (f.toGNS c)⟫_ℂ :=
            (inner_gnsRadonNikodym_toGNS hφ (a : A) c).symm
      _ = ⟪f.toGNS (a : A), (T * π c) f.gnsVector⟫_ℂ := by
            simp [π, mul_apply_eq_comp, toGNS_apply]
      _ = ⟪f.toGNS (a : A), (π c * B) (f.toPreGNS 1)⟫_ℂ := by
            rw [← hTcomm_c, mul_apply_eq_comp, mul_apply_eq_comp, ← gnsVector_def, hBΩ]
  have hB_comm : B ∈ Set.centralizer (Set.range π) := by
    rintro _ ⟨a, rfl⟩
    refine congrFun (Continuous.ext_on α.dense_entireAnalytic
      ((map_continuous π).mul continuous_const)
      (continuous_const.mul (map_continuous π)) fun c hc => ?_) a
    have hc' := mem_entireAnalytic.mp hc
    have hshift := hB_comm_entire_shift (isEntireAnalytic_entireExtension α c (-(β * I)))
    rw [entireExtension_entireExtension, neg_add_cancel, hc'.entireExtension_apply_zero] at hshift
    exact hshift.symm
  -- Step 3: `B` and `T` both lie in `M'` and agree on the cyclic vector `Ω`, so `B = T`.
  have hBT : B = T := by
    ext v
    refine f.denseRange_toGNS.induction_on v (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
    have hBa : B * π a = π a * B := (hB_comm _ ⟨a, rfl⟩).symm
    have hTa : T * π a = π a * T := (hT_comm _ ⟨a, rfl⟩).symm
    calc
      B (f.toGNS a) = (B * π a) f.gnsVector := by simp [π, mul_apply_eq_comp, toGNS_apply]
      _ = π a (B f.gnsVector) := by rw [hBa, mul_apply_eq_comp]
      _ = π a (T f.gnsVector) := by rw [hBΩ]
      _ = (T * π a) f.gnsVector := by rw [hTa, mul_apply_eq_comp]
      _ = T (f.toGNS a) := by simp [π, mul_apply_eq_comp, toGNS_apply]
  have hT_vN : T ∈ VonNeumannAlgebra.adjoin (Set.range π) := hBT ▸ hB_vN
  exact ⟨hT_comm, (mem_adjoin_gnsStarAlgHom_iff f).mp hT_vN⟩

/-- Normalizing the vector functional of a positive commutant operator by a positive scalar
`t > 0` yields a positive continuous linear functional. -/
private def kmsStateOfCentralPositive {f : A →ₚ[ℂ] ℂ} {y : f.GNS →L[ℂ] f.GNS}
    (hy : y ∈ Set.centralizer (Set.range f.gnsStarAlgHom)) (hy_pos : y.IsPositive)
    {t : ℝ} (ht_pos : 0 < t) : A →P[ℂ] ℂ :=
  .mk₀ (((t⁻¹ : ℝ) : ℂ) • f.gnsVectorFunctional y) fun _ ha =>
    mul_nonneg (Complex.le_def.mpr ⟨inv_nonneg.mpr ht_pos.le, by simp⟩)
      (gnsVectorFunctional_nonneg f hy hy_pos ha)

private theorem kmsStateOfCentralPositive_apply {f : A →ₚ[ℂ] ℂ} {y : f.GNS →L[ℂ] f.GNS}
    (hy : y ∈ Set.centralizer (Set.range f.gnsStarAlgHom)) (hy_pos : y.IsPositive)
    {t : ℝ} (ht_pos : 0 < t) (a : A) :
    kmsStateOfCentralPositive hy hy_pos ht_pos a =
      ((t⁻¹ : ℝ) : ℂ) * f.gnsVectorFunctional y a := by
  simp [kmsStateOfCentralPositive]

/-- When `y` is positive and central with `⟪Ω, y Ω⟫ = t > 0`, the normalized vector functional
`kmsStateOfCentralPositive` is a β-KMS state. -/
private theorem isKMSState_kmsStateOfCentralPositive (hω : α.IsKMSState β ω)
    {y : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hyZ : y ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)))
    (hy_pos : y.IsPositive) {t : ℝ} (ht_pos : 0 < t)
    (hyΩ : ⟪ω.toPositiveLinearMap.gnsVector, y ω.toPositiveLinearMap.gnsVector⟫_ℂ = (t : ℂ)) :
    α.IsKMSState β (kmsStateOfCentralPositive hyZ.1 hy_pos ht_pos) := by
  refine isKMSState_iff_forall_isEntireAnalytic.mpr ⟨?_, fun a _ b hb => ?_⟩
  · have h1 : kmsStateOfCentralPositive hyZ.1 hy_pos ht_pos 1 = 1 := by
      rw [kmsStateOfCentralPositive_apply]
      simp only [gnsVectorFunctional_apply, map_one, one_apply_eq_self, hyΩ]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht_pos.ne', Complex.ofReal_one]
    have h := PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one
      (kmsStateOfCentralPositive hyZ.1 hy_pos ht_pos)
    rw [h1] at h
    exact Complex.ofReal_injective (by simpa using h)
  · rw [kmsStateOfCentralPositive_apply, kmsStateOfCentralPositive_apply,
      hω.gnsVectorFunctional_mul_entireExtension_mul_I hyZ a hb]

/-- Self-adjoint operators in the GNS centre of an extreme β-KMS state are scalar multiples of
the identity. -/
private theorem eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint
    (hω : α.IsKMSState β ω)
    (hext : StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β))
    {z : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS}
    (hz : z ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)))
    (hz_sa : IsSelfAdjoint z) :
    ∃ c : ℂ, z = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS) := by
  let f := ω.toPositiveLinearMap
  let π := f.gnsStarAlgHom
  let Z : VonNeumannAlgebra f.GNS :=
    (VonNeumannAlgebra.adjoin (Set.range π)).commutant ⊓ VonNeumannAlgebra.adjoin (Set.range π)
  have hzZ : z ∈ Z := (mem_center_gnsStarAlgHom_iff f).mpr hz
  set r : ℝ := 4 * (‖z‖ + 1)
  have hr : 0 < r := by positivity
  let y : f.GNS →L[ℂ] f.GNS := (2⁻¹ : ℂ) • 1 + ((r⁻¹ : ℝ) : ℂ) • z
  have hyZ : y ∈ Z :=
    add_mem (SMulMemClass.smul_mem _ (one_mem Z)) (SMulMemClass.smul_mem _ hzZ)
  have h1yZ : (1 : f.GNS →L[ℂ] f.GNS) - y ∈ Z := sub_mem (one_mem Z) hyZ
  have hyZ' := (mem_center_gnsStarAlgHom_iff f).mp hyZ
  have h1yZ' := (mem_center_gnsStarAlgHom_iff f).mp h1yZ
  have hy_sa : IsSelfAdjoint y :=
    (IsSelfAdjoint.smul (by simp : IsSelfAdjoint (2⁻¹ : ℂ)) (IsSelfAdjoint.one _)).add
      (IsSelfAdjoint.smul (Complex.conj_ofReal r⁻¹) hz_sa)
  -- Bound `⟪v, y v⟫` between `(1/4) ‖v‖²` and `(3/4) ‖v‖²`.
  have hre_bound (v : f.GNS) :
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (⟪y v, v⟫_ℂ).re ∧
        (⟪y v, v⟫_ℂ).re ≤ (3 / 4 : ℝ) * ‖v‖ ^ 2 := by
    have hz_norm : |(⟪z v, v⟫_ℂ).re| ≤ (‖z‖ + 1) * ‖v‖ ^ 2 := by
      calc
        |(⟪z v, v⟫_ℂ).re| ≤ ‖⟪z v, v⟫_ℂ‖ := Complex.abs_re_le_norm _
        _ ≤ ‖z v‖ * ‖v‖ := norm_inner_le_norm _ _
        _ ≤ (‖z‖ * ‖v‖) * ‖v‖ := by gcongr; exact z.le_opNorm v
        _ = ‖z‖ * ‖v‖ ^ 2 := by ring
        _ ≤ (‖z‖ + 1) * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
    have hre_y :
        (⟪y v, v⟫_ℂ).re = (1 / 2 : ℝ) * ‖v‖ ^ 2 + r⁻¹ * (⟪z v, v⟫_ℂ).re := by
      have hv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
        rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
      have h2 : starRingEnd ℂ (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_ofNat, ← Complex.ofReal_inv, Complex.conj_ofReal]
      simp only [y, add_apply, smul_apply, one_apply_eq_self, inner_add_left,
        inner_smul_left, h2, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hv]
      ring
    have hr_eq : r⁻¹ * (‖z‖ + 1) = 1 / 4 := by
      have hz1 : ‖z‖ + 1 ≠ 0 := by positivity
      simp only [r]
      field_simp
    have hstep : r⁻¹ * |(⟪z v, v⟫_ℂ).re| ≤ (1 / 4 : ℝ) * ‖v‖ ^ 2 := by
      calc
        r⁻¹ * |(⟪z v, v⟫_ℂ).re| ≤ r⁻¹ * ((‖z‖ + 1) * ‖v‖ ^ 2) := by gcongr
        _ = (r⁻¹ * (‖z‖ + 1)) * ‖v‖ ^ 2 := by ring
        _ = (1 / 4 : ℝ) * ‖v‖ ^ 2 := by rw [hr_eq]
    rw [abs_le] at hz_norm
    have h1 : -((1 / 4 : ℝ) * ‖v‖ ^ 2) ≤ r⁻¹ * (⟪z v, v⟫_ℂ).re := by
      have := mul_le_mul_of_nonneg_left hz_norm.1 (inv_nonneg.mpr hr.le)
      nlinarith
    have h2 : r⁻¹ * (⟪z v, v⟫_ℂ).re ≤ (1 / 4 : ℝ) * ‖v‖ ^ 2 :=
      (le_abs_self _).trans (by
        simpa only [abs_mul, abs_of_pos (inv_pos.mpr hr)] using hstep)
    constructor <;> linarith
  have hy_pos : y.IsPositive :=
    isPositive_def'.mpr ⟨hy_sa, fun v =>
      (by positivity : (0 : ℝ) ≤ (1 / 4) * ‖v‖ ^ 2).trans (hre_bound v).1⟩
  have h1y_pos : ((1 : f.GNS →L[ℂ] f.GNS) - y).IsPositive := by
    refine isPositive_def'.mpr ⟨(IsSelfAdjoint.one _).sub hy_sa, fun v => ?_⟩
    simp only [reApplyInnerSelf, sub_apply, one_apply_eq_self, inner_sub_left, map_sub,
      RCLike.re_to_complex, sub_nonneg]
    have hv : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
      rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
    rw [hv]
    linarith [(hre_bound v).2, sq_nonneg ‖v‖]
  -- Construct the convex decomposition `ω = t • ω₁ + (1 - t) • ω₂` in `K_β`.
  have hω1 : f 1 = 1 := by
    simpa [f] using
      (PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω).symm.trans
        (by rw [hω.norm_eq_one, Complex.ofReal_one])
  have hΩ_norm : ‖f.gnsVector‖ = 1 := f.norm_gnsVector hω1
  set t : ℝ := (⟪y f.gnsVector, f.gnsVector⟫_ℂ).re
  have ht_bounds : (1 / 4 : ℝ) ≤ t ∧ t ≤ 3 / 4 := by
    simpa [t, hΩ_norm] using hre_bound f.gnsVector
  have ht_pos : 0 < t := by linarith
  have h1t_pos : 0 < 1 - t := by linarith
  have hyΩ : ⟪f.gnsVector, y f.gnsVector⟫_ℂ = (t : ℂ) := by
    have h0 := hy_pos.inner_nonneg_left f.gnsVector
    have hsym := hy_pos.inner_left_eq_inner_right f.gnsVector f.gnsVector
    rw [← hsym]
    exact Complex.ext rfl (Complex.le_def.mp h0).2.symm
  have h1yΩ : ⟪f.gnsVector, ((1 : f.GNS →L[ℂ] f.GNS) - y) f.gnsVector⟫_ℂ =
      ((1 - t : ℝ) : ℂ) := by
    rw [sub_apply, one_apply_eq_self, inner_sub_right, hyΩ,
      inner_self_eq_norm_sq_to_K, hΩ_norm]
    simp
  let ω₁ : A →P[ℂ] ℂ :=
    kmsStateOfCentralPositive ((Set.mem_inter_iff _ _ _).mp hyZ').1 hy_pos ht_pos
  let ω₂ : A →P[ℂ] ℂ :=
    kmsStateOfCentralPositive ((Set.mem_inter_iff _ _ _).mp h1yZ').1 h1y_pos h1t_pos
  have hω₁_kms : α.IsKMSState β ω₁ :=
    isKMSState_kmsStateOfCentralPositive hω hyZ' hy_pos ht_pos hyΩ
  have hω₂_kms : α.IsKMSState β ω₂ :=
    isKMSState_kmsStateOfCentralPositive hω h1yZ' h1y_pos h1t_pos h1yΩ
  have hseg : StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈
      openSegment ℝ (StrongDual.toWeakDual (ω₁ : A →L[ℂ] ℂ))
        (StrongDual.toWeakDual (ω₂ : A →L[ℂ] ℂ)) := by
    refine ⟨t, 1 - t, ht_pos, h1t_pos, add_sub_cancel t 1, ?_⟩
    refine DFunLike.ext _ _ fun a => ?_
    simp only [_root_.add_apply, _root_.smul_apply, StrongDual.toWeakDual_apply,
      PositiveContinuousLinearMap.coe_toContinuousLinearMap, Complex.real_smul]
    dsimp only [ω₁, ω₂]
    rw [kmsStateOfCentralPositive_apply, kmsStateOfCentralPositive_apply,
      ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht_pos.ne', Complex.ofReal_one,
      one_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h1t_pos.ne',
      Complex.ofReal_one, one_mul, gnsVectorFunctional_sub, sub_apply,
      gnsVectorFunctional_one, add_sub_cancel]
    rfl
  have hω₁_eq : StrongDual.toWeakDual (ω₁ : A →L[ℂ] ℂ) =
      StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) :=
    (mem_extremePoints_iff_left.mp hext).2 _ (toWeakDual_mem_kmsStates_iff.mpr hω₁_kms)
      _ (toWeakDual_mem_kmsStates_iff.mpr hω₂_kms) hseg
  -- Therefore `(y - t • 1) Ω = 0`, and since `Ω` is separating for `M`, `y = t • 1`.
  have hsubZ : y - (t : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) ∈ Z :=
    sub_mem hyZ (SMulMemClass.smul_mem _ (one_mem Z))
  have hsubZ' := (mem_center_gnsStarAlgHom_iff f).mp hsubZ
  have hkill : (y - (t : ℂ) • (1 : f.GNS →L[ℂ] f.GNS)) (f.toPreGNS 1) = 0 := by
    refine ext_inner_left ℂ fun u => ?_
    refine f.denseRange_toGNS.induction_on u (isClosed_eq (by fun_prop) (by fun_prop))
      fun a => ?_
    have heval := DFunLike.congr_fun hω₁_eq (star a)
    simp only [StrongDual.toWeakDual_apply, PositiveContinuousLinearMap.coe_toContinuousLinearMap,
      ω₁, kmsStateOfCentralPositive_apply] at heval
    have hy_eval : f.gnsVectorFunctional y (star a) = (t : ℂ) * f (star a) := by
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
      have h := congrArg (fun w => (t : ℂ) * w) heval
      simpa [← mul_assoc, mul_inv_cancel₀ ht_ne, f] using h
    have hcomm : π (star a) * (y - (t : ℂ) • 1) = (y - (t : ℂ) • 1) * π (star a) :=
      hsubZ'.1 _ ⟨star a, rfl⟩
    calc
      ⟪f.toGNS a, (y - (t : ℂ) • (1 : f.GNS →L[ℂ] f.GNS)) (f.toPreGNS 1)⟫_ℂ
          = ⟪π a f.gnsVector, (y - (t : ℂ) • 1) f.gnsVector⟫_ℂ := by
            simp [π, toGNS_apply, gnsVector_def]
      _ = ⟪f.gnsVector, (π (star a) * (y - (t : ℂ) • 1)) f.gnsVector⟫_ℂ := by
            rw [mul_apply_eq_comp, map_star, star_eq_adjoint, adjoint_inner_right]
      _ = ⟪f.gnsVector, ((y - (t : ℂ) • 1) * π (star a)) f.gnsVector⟫_ℂ := by
            rw [hcomm]
      _ = f.gnsVectorFunctional (y - (t : ℂ) • 1) (star a) := by
            rw [mul_apply_eq_comp, gnsVectorFunctional_apply]
      _ = 0 := by
            rw [gnsVectorFunctional_sub, sub_apply, gnsVectorFunctional_smul, smul_apply,
              gnsVectorFunctional_one, hy_eval, smul_eq_mul, sub_self]
      _ = ⟪f.toGNS a, 0⟫_ℂ := (inner_zero_right _).symm
  have hy_eq : y = (t : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) :=
    sub_eq_zero.mp (hω.eq_zero_of_apply_toPreGNS_one_eq_zero
      ((mem_adjoin_gnsStarAlgHom_iff f).mpr hsubZ'.2) hkill)
  refine ⟨(r : ℂ) * ((t : ℂ) - 2⁻¹), ?_⟩
  have hrz :
      ((r⁻¹ : ℝ) : ℂ) • z = ((t : ℂ) - 2⁻¹) • (1 : f.GNS →L[ℂ] f.GNS) := by
    have h :
        (2⁻¹ : ℂ) • (1 : f.GNS →L[ℂ] f.GNS) + ((r⁻¹ : ℝ) : ℂ) • z = (t : ℂ) • 1 :=
      hy_eq
    rw [sub_smul]
    exact eq_sub_of_add_eq' h
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hmul := congrArg (fun S : f.GNS →L[ℂ] f.GNS => (r : ℂ) • S) hrz
  simpa [smul_smul, mul_inv_cancel₀ hr_ne] using hmul

/-- A β-KMS factor state is an extreme point of `α.kmsStates β`. -/
private theorem mem_extremePoints_kmsStates_of_trivial_center
    (hω : α.IsKMSState β ω)
    (hfactor : ∀ T ∈ Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom) ∩
        Set.centralizer (Set.centralizer (Set.range ω.toPositiveLinearMap.gnsStarAlgHom)),
      ∃ c : ℂ,
        T = c • (1 : ω.toPositiveLinearMap.GNS →L[ℂ] ω.toPositiveLinearMap.GNS)) :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ Set.extremePoints ℝ (α.kmsStates β) := by
  let f := ω.toPositiveLinearMap
  refine mem_extremePoints_iff_left.mpr ⟨toWeakDual_mem_kmsStates_iff.mpr hω, ?_⟩
  rintro φ₁ hφ₁ φ₂ hφ₂ ⟨s, t, hs, ht, _, hcomb⟩
  obtain ⟨ω₁, hω₁, rfl⟩ := mem_kmsStates_iff.mp hφ₁
  obtain ⟨ω₂, _, rfl⟩ := mem_kmsStates_iff.mp hφ₂
  have hs_nonneg : (0 : ℂ) ≤ (s : ℂ) := Complex.le_def.mpr ⟨hs.le, by simp⟩
  have ht_nonneg : (0 : ℂ) ≤ (t : ℂ) := Complex.le_def.mpr ⟨ht.le, by simp⟩
  let φ : A →ₚ[ℂ] ℂ :=
    .mk₀ ((s : ℂ) • ω₁.toPositiveLinearMap.toLinearMap) fun a ha =>
      mul_nonneg hs_nonneg (ω₁.map_nonneg ha)
  have hφ_apply (a : A) : φ a = (s : ℂ) * ω₁ a := rfl
  have hcomb_apply (a : A) : (s : ℂ) * ω₁ a + (t : ℂ) * ω₂ a = ω a := by
    simpa only [_root_.add_apply, _root_.smul_apply, StrongDual.toWeakDual_apply,
      PositiveContinuousLinearMap.coe_toContinuousLinearMap, Complex.real_smul] using
      DFunLike.congr_fun hcomb a
  have hdom : ∀ a, 0 ≤ a → φ a ≤ (1 : ℂ) * ω a := by
    intro a ha
    rw [one_mul, hφ_apply, ← hcomb_apply a, le_add_iff_nonneg_right]
    exact mul_nonneg ht_nonneg (ω₂.map_nonneg ha)
  have hkms_φ : ∀ a, α.IsEntireAnalytic a → ∀ b, α.IsEntireAnalytic b →
      φ (a * α.entireExtension b (β * I)) = φ (b * a) := fun a _ b hb => by
    simp only [hφ_apply, hω₁.apply_mul_entireExtension_mul_I a hb]
  obtain ⟨c, hc⟩ :=
    hfactor (f.gnsRadonNikodym φ) (hω.gnsRadonNikodym_mem_center hdom hkms_φ)
  have hval (a : A) : (s : ℂ) * ω₁ a = c * ω a := by
    have h := gnsVectorFunctional_gnsRadonNikodym (f := f) (g := φ) hdom a
    rw [hc, gnsVectorFunctional_smul, smul_apply, gnsVectorFunctional_one,
      smul_eq_mul, hφ_apply] at h
    exact h.symm
  have hcs : c = (s : ℂ) := by
    have h1 := hval 1
    rw [← PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω₁,
      ← PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one ω,
      hω₁.norm_eq_one, hω.norm_eq_one, Complex.ofReal_one, mul_one, mul_one] at h1
    exact h1.symm
  have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  refine DFunLike.ext _ _ fun a => ?_
  simp only [StrongDual.toWeakDual_apply, PositiveContinuousLinearMap.coe_toContinuousLinearMap]
  exact mul_left_cancel₀ hs_ne (by rw [hval a, hcs])

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
  let π := f.gnsStarAlgHom
  let Z : VonNeumannAlgebra f.GNS :=
    (VonNeumannAlgebra.adjoin (Set.range π)).commutant ⊓ VonNeumannAlgebra.adjoin (Set.range π)
  have hzZ : z ∈ Z := (mem_center_gnsStarAlgHom_iff f).mpr hz
  let x : f.GNS →L[ℂ] f.GNS := (2⁻¹ : ℂ) • (z + star z)
  let y : f.GNS →L[ℂ] f.GNS := (-I / 2 : ℂ) • (z - star z)
  have hxZ : x ∈ Set.centralizer (Set.range f.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range f.gnsStarAlgHom)) :=
    (mem_center_gnsStarAlgHom_iff f).mp
      (SMulMemClass.smul_mem (2⁻¹ : ℂ) (add_mem hzZ (star_mem hzZ)))
  have hyZ : y ∈ Set.centralizer (Set.range f.gnsStarAlgHom) ∩
      Set.centralizer (Set.centralizer (Set.range f.gnsStarAlgHom)) :=
    (mem_center_gnsStarAlgHom_iff f).mp
      (SMulMemClass.smul_mem (-I / 2 : ℂ) (sub_mem hzZ (star_mem hzZ)))
  have hx_sa : IsSelfAdjoint x :=
    IsSelfAdjoint.smul (by simp : IsSelfAdjoint (2⁻¹ : ℂ)) (IsSelfAdjoint.add_star_self z)
  have hy_sa : IsSelfAdjoint y := by
    rw [IsSelfAdjoint, star_smul, star_sub, star_star]
    have hc : star (-I / 2 : ℂ) = -(-I / 2 : ℂ) := by
      simp [RCLike.star_def, neg_div]
    rw [hc, neg_smul, ← smul_neg, neg_sub]
  obtain ⟨c₁, hc₁⟩ := eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint hω hext hxZ hx_sa
  obtain ⟨c₂, hc₂⟩ := eq_smul_one_of_mem_extremePoints_of_isSelfAdjoint hω hext hyZ hy_sa
  refine ⟨c₁ + I * c₂, ?_⟩
  have hdecomp : z = x + I • y := by
    simp only [x, y, smul_add, smul_sub, smul_smul]
    have h1 : (2⁻¹ : ℂ) + I * (-I / 2) = 1 := by
      ring_nf
      rw [I_sq]
      norm_num
    have h2 : (2⁻¹ : ℂ) - I * (-I / 2) = 0 := by
      ring_nf
      rw [I_sq]
      norm_num
    calc
      z = (1 : ℂ) • z + (0 : ℂ) • star z := by simp
      _ = ((2⁻¹ : ℂ) + I * (-I / 2)) • z + ((2⁻¹ : ℂ) - I * (-I / 2)) • star z := by
            rw [h1, h2]
      _ = (2⁻¹ : ℂ) • z + (2⁻¹ : ℂ) • star z +
            ((I * (-I / 2)) • z - (I * (-I / 2)) • star z) := by
          rw [add_smul, sub_smul]
          abel
  rw [hdecomp, hc₁, hc₂, smul_smul, ← add_smul]

end TauCeti.CStarAction
