/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
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
p.16). This file defines it on rational points, the case `R = ℚ` of the roadmap's
`N_{k,Φ} : (k ⊗ R)ˣ → (E ⊗ R)ˣ`.

* `TauCeti.CMType.typeDet E k V`: for an `E`-module `V` with a commuting `k`-action, the
  determinant over `E` of the action of `k`, `a ↦ det_E(a | V)`, a monoid homomorphism `k →* E`.
  It depends only on the isomorphism class of `V` (`TauCeti.CMType.typeDet_congr`). If `a` acts as
  `c ∈ E`, then `det_E(a | V) = c ^ dim_E V` (`TauCeti.CMType.typeDet_eq_pow_of_smul_eq`).
* `TauCeti.CMType.reflexNorm Φ hk`: `N_{k,Φ}`, the determinant on the representation with the type
  trace chosen by `TauCeti.CMType.exists_trace_eq_typeTrace`.
* `TauCeti.CMType.reflexNorm_eq_typeDet`: `N_{k,Φ}` is the determinant on any finite-dimensional
  representation with the type trace, so it does not depend on the choice of `V`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Proposition 1.21, p.15, and p.16.
-/

public section

namespace TauCeti.CMType

section TypeDet

variable (E : Type*) [Field E] (k : Type*) [Semiring k] (V : Type*) [AddCommGroup V] [Module E V]
  [Module k V] [SMulCommClass E k V]

/-- **The determinant of the scalar action.** For an `E`-module `V` with a commuting action of a
semiring `k`, the map `a ↦ det_E(a | V)`. When `V` is the representation with the type trace of a CM
type, this is the reflex norm (`TauCeti.CMType.reflexNorm_eq_typeDet`). -/
noncomputable def typeDet : k →* E :=
  haveI : SMulCommClass k E V := .symm E k V
  LinearMap.det.comp (DistribMulAction.toModuleEnd E V)

theorem typeDet_apply (a : k) :
    haveI : SMulCommClass k E V := .symm E k V
    typeDet E k V a = LinearMap.det (DistribSMul.toLinearMap E V a) :=
  (rfl)

variable {E k V}

/-- If `a ∈ k` acts on `V` as `c ∈ E`, then `det_E(a | V) = c ^ dim_E V`. -/
theorem typeDet_eq_pow_of_smul_eq {a : k} {c : E} (h : ∀ v : V, a • v = c • v) :
    typeDet E k V a = c ^ Module.finrank E V := by
  have : SMulCommClass k E V := .symm E k V
  have hc : DistribSMul.toLinearMap E V a = c • LinearMap.id := LinearMap.ext h
  rw [typeDet_apply, hc, LinearMap.det_smul, LinearMap.det_id, mul_one]

/-- **Independence of the module.** Isomorphic `E`-modules with commuting `k`-actions have the same
determinant of the scalar action: a `k`-linear isomorphism `V ≃ W` intertwining the actions of `E`
gives `det_E(a | V) = det_E(a | W)`. -/
theorem typeDet_congr {W : Type*} [AddCommGroup W] [Module E W] [Module k W]
    [SMulCommClass E k W] (e : V ≃ₗ[k] W) (he : ∀ (c : E) (v : V), e (c • v) = c • e v) :
    typeDet E k V = typeDet E k W := by
  have : SMulCommClass k E V := .symm E k V
  have : SMulCommClass k E W := .symm E k W
  -- `e` is also `E`-linear.
  let eE : V ≃ₗ[E] W := { e.toAddEquiv with map_smul' := he }
  ext a
  rw [typeDet_apply, typeDet_apply, ← LinearMap.det_conj _ eE]
  congr 1
  ext w
  simp [eE, e.map_smul]

end TypeDet

section ReflexNorm

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

variable [NumberField E]

/-- **Uniqueness of the determinant.** Any two finite-dimensional representations of `E` over
`k ⊆ ℂ` with the type trace of `Φ` have the same determinant of the scalar action. -/
theorem typeDet_eq_typeDet_of_trace_eq (Φ : CMType E)
    {V W : Type*} [AddCommGroup V] [Module E V] [Module k V] [SMulCommClass E k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module E W] [Module k W] [SMulCommClass E k W]
    [FiniteDimensional k W]
    (hV : ∀ c : E, (LinearMap.trace k V (DistribSMul.toLinearMap k V c) : ℂ) =
      Φ.typeTrace c)
    (hW : ∀ c : E, (LinearMap.trace k W (DistribSMul.toLinearMap k W c) : ℂ) =
      Φ.typeTrace c) :
    typeDet E k V = typeDet E k W := by
  have := Algebra.FormallyUnramified.of_isSeparable ℚ E
  obtain ⟨e, he⟩ := exists_linearEquiv_of_trace_eq_typeTrace Φ k (Module.toModuleEnd k V)
    (Module.toModuleEnd k W) hV hW
  exact typeDet_congr e he

/-- **The reflex norm** `N_{k,Φ} : k → E` of a CM type `Φ` on a number field `E`, for a subfield
`k ⊆ ℂ` containing the reflex field: `a ↦ det_E(a | V)` on the representation `V` of `E` over `k`
with the type trace chosen by `TauCeti.CMType.exists_trace_eq_typeTrace`. It is the determinant
on every such representation (`TauCeti.CMType.reflexNorm_eq_typeDet`). -/
noncomputable def reflexNorm (Φ : CMType E) (hk : Φ.reflexField ≤ k) : k →* E :=
  have := Algebra.FormallyUnramified.of_isSeparable ℚ E
  letI := repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  haveI := smulCommClass_repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  typeDet E k (Fin (Φ.exists_trace_eq_typeTrace hk).choose → k)

/-- **The reflex norm is the determinant on any representation with the type trace.** For every
finite-dimensional representation `V` of `E` over `k` with `Tr_k(c | V) = typeTrace_Φ(c)`,
`N_{k,Φ}(a) = det_E(a | V)`. -/
theorem reflexNorm_eq_typeDet (Φ : CMType E) (hk : Φ.reflexField ≤ k)
    (V : Type*) [AddCommGroup V] [Module E V] [Module k V] [SMulCommClass E k V]
    [FiniteDimensional k V]
    (hV : ∀ c : E, (LinearMap.trace k V (DistribSMul.toLinearMap k V c) : ℂ) =
      Φ.typeTrace c) :
    Φ.reflexNorm hk = typeDet E k V := by
  have := Algebra.FormallyUnramified.of_isSeparable ℚ E
  have hρ := (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose_spec
  let := repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  have := smulCommClass_repModule (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  exact typeDet_eq_typeDet_of_trace_eq Φ (fun c ↦ hρ c) hV

/-- For a CM type consisting of the single embedding `φ`, the type trace is `φ`. -/
theorem typeTrace_eq_of_coe_eq_singleton {Φ : CMType E} {φ : E →+* ℂ}
    (hΦ : (Φ : Set (E →+* ℂ)) = {φ}) (c : E) : Φ.typeTrace c = φ c := by
  rw [typeTrace_apply, hΦ, finsum_mem_singleton]

/-- **The reflex norm of a one-element CM type.** If `Φ = {φ}`, as for an imaginary quadratic
field, then `N_Φ = N_{E*,Φ}` inverts `φ`: `N_Φ(φ c) = c`. The representation with the type trace
is `E*` itself, on which `E` acts through `φ`, and `E* = φ(E)`. -/
theorem reflexNorm_apply_of_coe_eq_singleton {Φ : CMType E} {φ : E →+* ℂ}
    (hΦ : (Φ : Set (E →+* ℂ)) = {φ}) (c : E) :
    Φ.reflexNorm le_rfl ⟨φ c, typeTrace_eq_of_coe_eq_singleton hΦ c ▸
      Φ.typeTrace_mem_reflexField c⟩ = c := by
  have hmem (c : E) : φ c ∈ Φ.reflexField :=
    typeTrace_eq_of_coe_eq_singleton hΦ c ▸ Φ.typeTrace_mem_reflexField c
  -- `E` acts on `E*` through `φ`.
  let ψ : E →+* Φ.reflexField := φ.codRestrict Φ.reflexField.toSubalgebra hmem
  let := Module.compHom Φ.reflexField ψ
  have : SMulCommClass E Φ.reflexField Φ.reflexField :=
    ⟨fun c a v ↦ mul_left_comm (ψ c) a v⟩
  -- `E* = φ(E)`, so `E*` is one-dimensional over `E`.
  have hrange : Φ.reflexField ≤ φ.toRatAlgHom.fieldRange := reflexField_le_iff.mpr fun c ↦ by
    rw [typeTrace_eq_of_coe_eq_singleton hΦ c]
    exact ⟨c, rfl⟩
  have hdim : Module.finrank E Φ.reflexField = 1 := by
    refine (finrank_eq_one_iff_of_ne_zero' (1 : Φ.reflexField) one_ne_zero).mpr fun w ↦ ?_
    obtain ⟨c', hc'⟩ := hrange w.prop
    refine ⟨c', Subtype.ext ?_⟩
    change φ c' * 1 = w
    rw [mul_one]
    exact hc'
  have htrace (c : E) : (LinearMap.trace Φ.reflexField Φ.reflexField
      (DistribSMul.toLinearMap Φ.reflexField Φ.reflexField c) : ℂ) = Φ.typeTrace c := by
    have h : DistribSMul.toLinearMap Φ.reflexField Φ.reflexField c = ψ c • LinearMap.id :=
      LinearMap.ext fun v ↦ rfl
    rw [h, map_smul, LinearMap.trace_id, Module.finrank_self, typeTrace_eq_of_coe_eq_singleton hΦ]
    simp [ψ]
  have hsmul : ∀ v : Φ.reflexField, (⟨φ c, hmem c⟩ : Φ.reflexField) • v = c • v := fun _ ↦ rfl
  exact (DFunLike.congr_fun (reflexNorm_eq_typeDet Φ le_rfl Φ.reflexField htrace) _).trans
    ((typeDet_eq_pow_of_smul_eq hsmul).trans (by rw [hdim, pow_one]))

end ReflexNorm

end TauCeti.CMType
