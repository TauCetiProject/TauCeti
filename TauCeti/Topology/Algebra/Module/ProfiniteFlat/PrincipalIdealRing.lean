/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.ProfiniteFlat.Domain
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
import TauCeti.LinearAlgebra.Quotient.Basic
import TauCeti.RingTheory.Ideal.Colon
import TauCeti.RingTheory.Ideal.Quotient.Colon

/-!
# One-step lifting over compact principal ideal domains

Over a compact principal ideal domain `O`, any `O`-linear functional `φ : M →ₗ[O] O ⧸ I` (`I ≠ ⊥`)
with open kernel on a profinite flat `O`-module `M` lifts along the quotient projection
`O ⧸ Ideal.span {ϖ} * I → O ⧸ I` for any nonzero `ϖ : O` to a map with open kernel
(`TauCeti.IsProfiniteFlat.exists_lift_mul`). Specializing to `I = Ideal.span {ϖ ^ (n + 1)}` gives
the one-step lift with open kernel along the quotient projection
`O ⧸ Ideal.span {ϖ ^ (n + 2)} → O ⧸ Ideal.span {ϖ ^ (n + 1)}`
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
the quotient projection `O ⧸ Ideal.span {ϖ} * I → O ⧸ I` for nonzero `ϖ : O` over a compact
principal ideal domain `O`, producing a lift with open kernel. -/
theorem exists_lift_mul {I : Ideal O} (hI : I ≠ ⊥) {ϖ : O} (hϖ : ϖ ≠ 0)
    (φ : M →ₗ[O] O ⧸ I) (hker : IsOpen (LinearMap.ker φ : Set M)) :
    ∃ φ' : M →ₗ[O] O ⧸ (Ideal.span {ϖ} * I), IsOpen (LinearMap.ker φ' : Set M) ∧
      ∀ m : M, Ideal.Quotient.factor Ideal.mul_le_right (φ' m) = φ m := by
  have := hM.isTopologicalAddGroup
  let J₂ : Ideal O := Ideal.span {ϖ} * I
  obtain ⟨V, hV_open, hJ₂_le, hV_le_ker, hV_ker⟩ := hM.exists_open_submodule_ker_of_mul hϖ φ hker
  have hJ₂_ne : J₂ ≠ ⊥ := by
    rw [ne_eq, Ideal.mul_eq_bot, Ideal.span_singleton_eq_bot]
    exact not_or.mpr ⟨hϖ, hI⟩
  have hcolon : J₂.colon {ϖ} = I :=
    Ideal.span_singleton_mul_colon_singleton (mul_right_injective₀ hϖ) I
  let mulQ : (O ⧸ I) →ₗ[O] (O ⧸ J₂) :=
    TauCeti.ColonQuotient.mulColon O J₂ ϖ ∘ₗ (Submodule.quotEquivOfEq _ _ hcolon.symm).toLinearMap
  have hmulQ_inj : Function.Injective mulQ :=
    (TauCeti.ColonQuotient.mulColon_injective O J₂ ϖ).comp
      (Submodule.quotEquivOfEq _ _ hcolon.symm).injective
  have hmulQ_factor : ∀ q : O ⧸ J₂,
      mulQ (Ideal.Quotient.factor Ideal.mul_le_right q) = ϖ • q := fun q ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Ideal.Quotient.factor_mk,
      ← Ideal.Quotient.mk_eq_mk, Submodule.quotEquivOfEq_mk, Ideal.Quotient.mk_eq_mk,
      TauCeti.ColonQuotient.mulColon_mk, ← smul_eq_mul, ← Ideal.Quotient.mk_eq_mk,
      Submodule.Quotient.mk_smul, Ideal.Quotient.mk_eq_mk]
  have htor : Module.IsTorsionBySet O (M ⧸ V) J₂ := (Module.isTorsionBySet_quotient_iff V J₂).mpr
    fun _ _ hr ↦ hJ₂_le (Submodule.smul_mem_smul hr Submodule.mem_top)
  let := htor.module; have : IsScalarTower O (O ⧸ J₂) (M ⧸ V) := htor.isScalarTower
  let β : M →ₗ[O] (O ⧸ J₂) := mulQ.comp φ
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
  apply hmulQ_inj
  rw [hmulQ_factor, ← map_smul]
  calc φ' (ϖ • m) = (ψ.comp (LinearMap.range μ).subtype) (μ.rangeRestrict (V.mkQ m)) := by
        simp [φ', μ, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    _ = ψ₀ (μ.rangeRestrict (V.mkQ m)) := by rw [hψ]
    _ = mulQ (φ m) := by simp [ψ₀, βbar, β]

include hM in
/-- One-step lifting of `O`-linear maps `M →ₗ[O] O ⧸ Ideal.span {ϖ ^ (n + 1)}` with open kernel
along the quotient projection `O ⧸ Ideal.span {ϖ ^ (n + 2)} → O ⧸ Ideal.span {ϖ ^ (n + 1)}` for
nonzero `ϖ : O` over a compact principal ideal domain `O`, producing a lift with open kernel. -/
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
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← Submodule.factor_eq_factor,
      Submodule.factor_quotEquivOfEq heq rfl Ideal.mul_le_right,
      Submodule.factor_eq_factor, hcomp m]
    obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (φ m)
    rw [← hr, Submodule.quotEquivOfEq_mk]

end PrincipalIdealRing

end TauCeti.IsProfiniteFlat
