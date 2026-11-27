/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Domain
import Mathlib.Algebra.Module.Torsion.Basic
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# One-step lifting over compact principal ideal domains

Over a compact principal ideal domain `O`, any `O`-linear functional `φ : M →ₗ[O] O ⧸ I` (`I ≠ ⊥`)
with open kernel on a profinite flat `O`-module `M` lifts along `O ⧸ (ϖ) * I → O ⧸ I` for any
nonzero `ϖ : O` (`TauCeti.IsProfiniteFlat.exists_lift_mul`). Specializing to `I = (ϖ ^ (n + 1))`
gives the one-step lift along `(ϖ ^ (n + 2)) → (ϖ ^ (n + 1))`
(`TauCeti.IsProfiniteFlat.exists_lift_span_pow_succ`).
-/

public section

namespace TauCeti.IsProfiniteFlat

section PrincipalIdealRing

variable {O M : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  [TopologicalSpace O] [CompactSpace O] [AddCommGroup M] [Module O M] [TopologicalSpace M]
  (hM : IsProfiniteFlat O M)

include hM in
/-- One-step lifting of `O`-linear maps `M →ₗ[O] O ⧸ I` with open kernel (for `I ≠ ⊥`) along
`(ϖ) * I → I` over a compact principal ideal domain `O`. -/
theorem exists_lift_mul {I : Ideal O} (hI : I ≠ ⊥) {ϖ : O} (hϖ : ϖ ≠ 0)
    (φ : M →ₗ[O] O ⧸ I) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ φ' : M →ₗ[O] O ⧸ (Ideal.span {ϖ} * I), IsOpen (LinearMap.ker φ' : Set M) ∧
      ∀ m : M, Ideal.Quotient.factor Ideal.mul_le_right (φ' m) = φ m := by
  have := hM.isTopologicalAddGroup
  let J₂ : Ideal O := Ideal.span {ϖ} * I
  obtain ⟨V, hV_open, hJ₂_le, hV_le_ker, hV_ker⟩ := hM.exists_open_submodule_ker_of_mul hϖ φ hker
  have hJ₂_ne : J₂ ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact (Submodule.ne_bot_iff J₂).mpr
      ⟨ϖ * a, Ideal.mul_mem_mul (Ideal.mem_span_singleton_self ϖ) ha, mul_ne_zero hϖ ha0⟩
  have htor : Module.IsTorsionBySet O (M ⧸ V) J₂ := (Module.isTorsionBySet_quotient_iff V J₂).mpr
    fun _ _ hr ↦ hJ₂_le (Submodule.smul_mem_smul hr Submodule.mem_top)
  let := htor.module; have : IsScalarTower O (O ⧸ J₂) (M ⧸ V) := htor.isScalarTower
  let β : M →ₗ[O] (O ⧸ J₂) := (Ideal.Quotient.mulLeft ϖ le_rfl).comp φ
  let βbar : (M ⧸ V) →ₗ[O ⧸ J₂] (O ⧸ J₂) :=
    (V.liftQ β (hV_le_ker.trans (LinearMap.ker_le_ker_comp φ _))).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let μ : (M ⧸ V) →ₗ[O ⧸ J₂] (M ⧸ V) := LinearMap.lsmul (O ⧸ J₂) (M ⧸ V) (Ideal.Quotient.mk J₂ ϖ)
  have hker_μ : LinearMap.ker μ.rangeRestrict ≤ LinearMap.ker βbar := fun x hx ↦ by
    obtain ⟨m, rfl⟩ := V.mkQ_surjective x
    have hμ0 : V.mkQ (ϖ • m) = 0 := by
      simpa [μ, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] using
        congr_arg Subtype.val (LinearMap.mem_ker.mp hx)
    simp [LinearMap.mem_ker, βbar, β,
      LinearMap.mem_ker.mp (hV_ker ((Submodule.Quotient.mk_eq_zero V).mp hμ0))]
  let ψ₀ : LinearMap.range μ →ₗ[O ⧸ J₂] (O ⧸ J₂) :=
    (μ.rangeRestrict.liftOfSurjective μ.surjective_rangeRestrict) ⟨βbar, hker_μ⟩
  obtain ⟨ψ, hψ⟩ := (Module.Baer.quotient_self hJ₂_ne).extension_property _
    (LinearMap.range μ).injective_subtype ψ₀
  let φ' : M →ₗ[O] (O ⧸ J₂) := (ψ.restrictScalars O).comp V.mkQ
  refine ⟨φ', Submodule.isOpen_mono
    (fun m hm ↦ by simp [φ', (Submodule.Quotient.mk_eq_zero V).mpr hm]) hV_open, fun m ↦ ?_⟩
  apply Ideal.Quotient.mulLeft_injective le_rfl le_rfl (mul_right_injective₀ hϖ)
  rw [Ideal.Quotient.mulLeft_factor, ← map_smul]
  calc φ' (ϖ • m) = (ψ.comp (LinearMap.range μ).subtype) (μ.rangeRestrict (V.mkQ m)) := by
        simp [φ', μ, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    _ = ψ₀ (μ.rangeRestrict (V.mkQ m)) := by rw [hψ]
    _ = Ideal.Quotient.mulLeft ϖ le_rfl (φ m) := by simp [ψ₀, βbar, β]

include hM in
/-- One-step lifting of `O`-linear maps `M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}` with open kernel
along `(ϖ ^ (n + 2)) → (ϖ ^ (n + 1))` over a compact principal ideal domain `O`. -/
theorem exists_lift_span_pow_succ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ)
    (φ : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ φ' : M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 2)}, IsOpen (LinearMap.ker φ' : Set M) ∧
      ∀ m : M, Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))
        (φ' m) = φ m := by
  have heq : Ideal.span {ϖ} * Ideal.span {ϖ ^ (n + 1)} = Ideal.span {ϖ ^ (n + 2)} := by
    rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ']
  obtain ⟨φ₀, hopen, hcomp⟩ :=
    hM.exists_lift_mul (mt Ideal.span_singleton_eq_bot.mp (pow_ne_zero (n + 1) hϖ)) hϖ φ hker
  let e : (O ⧸ (Ideal.span {ϖ} * Ideal.span {ϖ ^ (n + 1)})) ≃ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 2)}) :=
    Submodule.quotEquivOfEq _ _ heq
  refine ⟨e.toLinearMap.comp φ₀, ?_, fun m ↦ ?_⟩
  · rw [LinearMap.ker_comp_of_ker_eq_bot φ₀ (LinearEquiv.ker e)]
    exact hopen
  · obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (φ₀ m)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hr, e, Submodule.quotEquivOfEq_ideal_mk]
    simpa [← hr] using hcomp m

end PrincipalIdealRing

end TauCeti.IsProfiniteFlat
