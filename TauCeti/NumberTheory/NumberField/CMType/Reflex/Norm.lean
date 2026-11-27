/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.SMul
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Representation
import Mathlib.RingTheory.Unramified.Field

/-!
# The reflex norm on rational points

Let `Φ` be a CM type on a number field `E` and `k ⊆ ℂ` a subfield containing the reflex field
`E*`. By Milne, *Complex Multiplication*, Proposition 1.21, `E` has a representation `V` on a
finite-dimensional `k`-vector space with trace the type trace, `Tr_k(a | V) = typeTrace_Φ(a)`,
unique up to isomorphism (`TauCeti.CMType.exists_trace_eq_typeTrace`,
`TauCeti.CMType.exists_linearEquiv_of_trace_eq_typeTrace`). The actions of `E` and `k` on `V`
commute, so `k` acts on `V` by `E`-linear maps, and the **reflex norm**
`N_{k,Φ}(a) = det_E(a | V)` is a multiplicative map `k → E` (Milne, *Complex Multiplication*,
p.16). Milne defines `N_{k,Φ} : (k ⊗_ℚ R)ˣ → (E ⊗_ℚ R)ˣ` for every `ℚ`-algebra `R`; this file
treats `R = ℚ`.

* `TauCeti.CMType.smulDet_eq_smulDet_of_trace_eq`: any two finite-dimensional representations
  with the type trace have the same determinant of the scalar action `TauCeti.smulDet`.
* `TauCeti.CMType.reflexNorm Φ hk`: `N_{k,Φ}`, the determinant on the representation with the type
  trace chosen by `TauCeti.CMType.exists_trace_eq_typeTrace`.
* `TauCeti.CMType.reflexNorm_eq_smulDet`: `N_{k,Φ}` is the determinant on any finite-dimensional
  representation with the type trace, so it does not depend on the choice of `V`.
* `TauCeti.CMType.reflexNorm_apply_of_coe_eq_singleton`: for a one-element type `Φ = {φ}`,
  `N_Φ(φ c) = c`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Proposition 1.21, p.15, and p.16.
-/

public section

namespace TauCeti.CMType

variable {E : Type*} [Field E] {k : IntermediateField ℚ ℂ}

/-- The `E`-module structure on `kⁿ` given by a representation `ρ : E → End_k(kⁿ)`. -/
private noncomputable abbrev repModule {n : ℕ} (ρ : E →+* Module.End k (Fin n → k)) :
    Module E (Fin n → k) :=
  Module.compHom _ ρ

private theorem smulCommClass_repModule {n : ℕ} (ρ : E →+* Module.End k (Fin n → k)) :
    letI := repModule ρ
    SMulCommClass E k (Fin n → k) :=
  letI := repModule ρ
  ⟨fun c a v ↦ ((ρ c).map_smul a v)⟩

/-- Under `repModule ρ`, `c ∈ E` acts on `kⁿ` as `ρ c`. -/
private theorem toLinearMap_repModule {n : ℕ} (ρ : E →+* Module.End k (Fin n → k)) (c : E) :
    letI := repModule ρ
    haveI := smulCommClass_repModule ρ
    DistribSMul.toLinearMap k (Fin n → k) c = ρ c :=
  -- `Module.compHom` defines `c • v` as `ρ c v`.
  rfl

variable [NumberField E]

/-- **Uniqueness of the determinant.** Any two finite-dimensional representations of `E` over
`k ⊆ ℂ` with the type trace of `Φ` have the same determinant of the scalar action. -/
theorem smulDet_eq_smulDet_of_trace_eq (Φ : CMType E)
    {V W : Type*} [AddCommGroup V] [Module E V] [Module k V] [SMulCommClass E k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module E W] [Module k W] [SMulCommClass E k W]
    [FiniteDimensional k W]
    (hV : ∀ c : E, (LinearMap.trace k V (DistribSMul.toLinearMap k V c) : ℂ) =
      Φ.typeTrace c)
    (hW : ∀ c : E, (LinearMap.trace k W (DistribSMul.toLinearMap k W c) : ℂ) =
      Φ.typeTrace c) :
    smulDet E k V = smulDet E k W := by
  have := Algebra.FormallyUnramified.of_isSeparable ℚ E
  obtain ⟨e, he⟩ := exists_linearEquiv_of_trace_eq_typeTrace Φ k (Module.toModuleEnd k V)
    (Module.toModuleEnd k W) hV hW
  exact smulDet_congr e he

/-- **The reflex norm** `N_{k,Φ} : k → E` of a CM type `Φ` on a number field `E`, for a subfield
`k ⊆ ℂ` containing the reflex field: `a ↦ det_E(a | V)` on the representation `V` of `E` over `k`
with the type trace chosen by `TauCeti.CMType.exists_trace_eq_typeTrace`. It is the determinant
on every such representation (`TauCeti.CMType.reflexNorm_eq_smulDet`). -/
noncomputable def reflexNorm (Φ : CMType E) (hk : Φ.reflexField ≤ k) : k →* E :=
  have := Algebra.FormallyUnramified.of_isSeparable ℚ E
  letI := repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  haveI := smulCommClass_repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  smulDet E k (Fin (Φ.exists_trace_eq_typeTrace hk).choose → k)

/-- **The reflex norm is the determinant on any representation with the type trace.** For every
finite-dimensional representation `V` of `E` over `k` with `Tr_k(c | V) = typeTrace_Φ(c)`,
`N_{k,Φ}(a) = det_E(a | V)`. -/
theorem reflexNorm_eq_smulDet (Φ : CMType E) (hk : Φ.reflexField ≤ k)
    (V : Type*) [AddCommGroup V] [Module E V] [Module k V] [SMulCommClass E k V]
    [FiniteDimensional k V]
    (hV : ∀ c : E, (LinearMap.trace k V (DistribSMul.toLinearMap k V c) : ℂ) =
      Φ.typeTrace c) :
    Φ.reflexNorm hk = smulDet E k V := by
  have := Algebra.FormallyUnramified.of_isSeparable ℚ E
  have hρ := (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose_spec
  let := repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  have := smulCommClass_repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  refine smulDet_eq_smulDet_of_trace_eq Φ (fun c ↦ ?_) hV
  rw [toLinearMap_repModule]
  exact hρ c

/-- **The reflex norm of a one-element CM type.** If `Φ = {φ}`, as for an imaginary quadratic
field, then `N_Φ = N_{E*,Φ}` inverts `φ`: `N_Φ(φ c) = c`. The representation with the type trace
is `E*` itself, on which `E` acts through `φ`, and `E* = φ(E)`. -/
theorem reflexNorm_apply_of_coe_eq_singleton {Φ : CMType E} {φ : E →+* ℂ}
    (hΦ : (Φ : Set (E →+* ℂ)) = {φ}) {a : Φ.reflexField} {c : E} (ha : (a : ℂ) = φ c) :
    Φ.reflexNorm le_rfl a = c := by
  have hmem (c : E) : φ c ∈ Φ.reflexField :=
    typeTrace_eq_of_coe_eq_singleton hΦ c ▸ Φ.typeTrace_mem_reflexField c
  -- `E` acts on `E*` through `φ`.
  let ψ : E →+* Φ.reflexField := φ.codRestrict Φ.reflexField.toSubalgebra hmem
  let := Module.compHom Φ.reflexField ψ
  -- `Module.compHom` defines `c • v` as `ψ c * v`.
  have hψ (c : E) (v : Φ.reflexField) : c • v = ψ c * v := rfl
  have : SMulCommClass E Φ.reflexField Φ.reflexField :=
    ⟨fun c a v ↦ by simp only [hψ, smul_eq_mul, mul_left_comm (ψ c) a v]⟩
  -- `E* = φ(E)`, so `E*` is one-dimensional over `E`.
  have hrange : Φ.reflexField ≤ φ.toRatAlgHom.fieldRange := reflexField_le_iff.mpr fun c ↦ by
    rw [typeTrace_eq_of_coe_eq_singleton hΦ c]
    exact ⟨c, rfl⟩
  have hdim : Module.finrank E Φ.reflexField = 1 := by
    refine (finrank_eq_one_iff_of_ne_zero' (1 : Φ.reflexField) one_ne_zero).mpr fun w ↦ ?_
    obtain ⟨c', hc'⟩ := hrange w.prop
    refine ⟨c', Subtype.ext ?_⟩
    rw [hψ, mul_one]
    exact hc'
  have htrace (c : E) : (LinearMap.trace Φ.reflexField Φ.reflexField
      (DistribSMul.toLinearMap Φ.reflexField Φ.reflexField c) : ℂ) = Φ.typeTrace c := by
    have h : DistribSMul.toLinearMap Φ.reflexField Φ.reflexField c = ψ c • LinearMap.id :=
      LinearMap.ext fun v ↦ hψ c v
    rw [h, map_smul, LinearMap.trace_id, Module.finrank_self, typeTrace_eq_of_coe_eq_singleton hΦ]
    simp [ψ]
  have hsmul (v : Φ.reflexField) : a • v = c • v := by
    rw [hψ, smul_eq_mul, show ψ c = a from Subtype.ext ha.symm]
  rw [reflexNorm_eq_smulDet Φ le_rfl Φ.reflexField htrace, smulDet_eq_pow_of_smul_eq hsmul, hdim,
    pow_one]

end TauCeti.CMType
