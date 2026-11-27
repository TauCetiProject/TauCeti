/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Field
public import TauCeti.Algebra.Module.LinearMap.CompHom
public import TauCeti.LinearAlgebra.Determinant.SMul
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Representation

/-!
# The reflex norm on rational points

Let `E` be a finite-dimensional formally unramified `ℚ`-algebra, such as a number field or a
finite product of CM fields, `Φ` a CM type on `E`, and `k ⊆ ℂ` a subfield containing the reflex
field `E*`. By Milne, *Complex Multiplication*, Proposition 1.21, `E` has a representation `V` on a
finite-dimensional `k`-vector space with trace the type trace, `Tr_k(a | V) = typeTrace_Φ(a)`,
unique up to isomorphism (`TauCeti.CMType.exists_trace_eq_typeTrace`,
`TauCeti.CMType.exists_linearEquiv_of_trace_eq_typeTrace`). The actions of `E` and `k` on `V`
commute, so `k` acts on `V` by `E`-linear maps, and the **reflex norm**
`N_{k,Φ}(a) = det_E(a | V)` is a multiplicative map `k → E` (Milne, *Complex Multiplication*,
p.16). Milne defines `N_{k,Φ} : (k ⊗_ℚ R)ˣ → (E ⊗_ℚ R)ˣ` for a number field `k` and every
`ℚ`-algebra `R`; this file treats `R = ℚ`. The definition accepts any `k`, but if `[k : ℚ]` is
infinite then `V` is not finitely generated over `E` and the determinant is the junk value `1`.

* `TauCeti.CMType.smulDet_eq_smulDet_of_trace_eq`: any two finite-dimensional representations
  with the type trace have the same determinant of the scalar action `TauCeti.smulDet`.
* `TauCeti.CMType.reflexNorm Φ hk`: `N_{k,Φ}`, the determinant on the representation with the type
  trace chosen by `TauCeti.CMType.exists_trace_eq_typeTrace`.
* `TauCeti.CMType.reflexNorm_eq_smulDet`: `N_{k,Φ}` is the determinant on any finite-dimensional
  representation with the type trace, so it does not depend on the choice of `V`.
* `TauCeti.CMType.reflexNorm_apply_of_coe_eq_singleton`: for a one-element type `Φ = {φ}` on a
  number field, `N_Φ(φ c) = c`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Proposition 1.21, p.15, and p.16.
-/

public section

namespace TauCeti.CMType

section FormallyUnramified

variable {E : Type*} [CommRing E] [Finite (E →+* ℂ)] [Algebra ℚ E] [Module.Finite ℚ E]
  [Algebra.FormallyUnramified ℚ E] {k : IntermediateField ℚ ℂ}

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
  obtain ⟨e, he⟩ := exists_linearEquiv_of_trace_eq_typeTrace Φ k (Module.toModuleEnd k V)
    (Module.toModuleEnd k W) hV hW
  exact smulDet_congr e he

/-- **The reflex norm** `N_{k,Φ} : k → E` of a CM type `Φ` on `E`, for a subfield `k ⊆ ℂ`
containing the reflex field: `a ↦ det_E(a | V)` on the representation `V` of `E` over `k`
with the type trace chosen by `TauCeti.CMType.exists_trace_eq_typeTrace`. It is the determinant
on every such representation (`TauCeti.CMType.reflexNorm_eq_smulDet`).

Milne defines `N_{k,Φ}` for a number field `k`. If `k` has infinite degree over `ℚ`, then `V` is not
finitely generated over `E`, so `LinearMap.det` and hence `reflexNorm Φ hk` take the junk value
`1`. -/
noncomputable def reflexNorm (Φ : CMType E) (hk : Φ.reflexField ≤ k) : k →* E :=
  let n := (Φ.exists_trace_eq_typeTrace hk).choose
  let ρ : E →+* Module.End k (Fin n → k) := (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  letI := Module.compHom (Fin n → k) ρ
  haveI := SMul.comp.smulCommClass (α := Fin n → k) (β := k) ρ
  smulDet E k (Fin n → k)

/-- **The reflex norm is the determinant on any representation with the type trace.** For every
finite-dimensional representation `V` of `E` over `k` with `Tr_k(c | V) = typeTrace_Φ(c)`,
`N_{k,Φ}(a) = det_E(a | V)`. -/
theorem reflexNorm_eq_smulDet (Φ : CMType E) (hk : Φ.reflexField ≤ k)
    (V : Type*) [AddCommGroup V] [Module E V] [Module k V] [SMulCommClass E k V]
    [FiniteDimensional k V]
    (hV : ∀ c : E, (LinearMap.trace k V (DistribSMul.toLinearMap k V c) : ℂ) =
      Φ.typeTrace c) :
    Φ.reflexNorm hk = smulDet E k V := by
  -- The choices made in the definition of `reflexNorm`: `E` acts on `Fin n → k` through `ρ`,
  -- whose trace is the type trace.
  let n := (Φ.exists_trace_eq_typeTrace hk).choose
  let ρ : E →+* Module.End k (Fin n → k) := (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose
  have hρ : ∀ c, (LinearMap.trace k (Fin n → k) (ρ c) : ℂ) = Φ.typeTrace c :=
    (Φ.exists_trace_eq_typeTrace hk).choose_spec.choose_spec
  let := Module.compHom (Fin n → k) ρ
  have := SMul.comp.smulCommClass (α := Fin n → k) (β := k) ρ
  -- With these instances, `reflexNorm Φ hk` unfolds by definition to `smulDet E k (Fin n → k)`,
  -- which `smulDet_eq_smulDet_of_trace_eq` compares with `smulDet E k V`.
  refine smulDet_eq_smulDet_of_trace_eq Φ (fun c ↦ ?_) hV
  rw [DistribSMul.toLinearMap_compHom]
  exact hρ c

end FormallyUnramified

section Field

variable {E : Type*} [Field E] [NumberField E]

-- A number field is formally unramified over `ℚ`, so its reflex norm is defined.
attribute [local instance] Algebra.FormallyUnramified.of_isSeparable

/-- **The reflex norm of a one-element CM type.** If `Φ = {φ}` is a CM type on a number field, as
for an imaginary quadratic field, then `N_Φ = N_{E*,Φ}` inverts `φ`: `N_Φ(φ c) = c`. The
representation with the type trace is `E*` itself, on which `E` acts through `φ`, and
`E* = φ(E)`. -/
theorem reflexNorm_apply_of_coe_eq_singleton {Φ : CMType E} {φ : E →+* ℂ}
    (hΦ : (Φ : Set (E →+* ℂ)) = {φ}) {a : Φ.reflexField} {c : E} (ha : (a : ℂ) = φ c) :
    Φ.reflexNorm le_rfl a = c := by
  -- `E* = φ(E)`.
  have hrange := reflexField_eq_fieldRange_of_coe_eq_singleton hΦ
  have hmem (c : E) : φ c ∈ Φ.reflexField :=
    hrange ▸ AlgHom.mem_fieldRange.2 ⟨c, φ.toRatAlgHom_apply c⟩
  -- `E` acts on `E*` through `φ`.
  let ψ : E →+* Φ.reflexField := φ.codRestrict Φ.reflexField.toSubalgebra hmem
  have hψφ (c : E) : (ψ c : ℂ) = φ c := RingHom.codRestrict_apply _ _ hmem c
  let := Module.compHom Φ.reflexField ψ
  -- `Module.compHom` defines `c • v` as `ψ c * v`.
  have hψ (c : E) (v : Φ.reflexField) : c • v = ψ c * v := rfl
  have : SMulCommClass E Φ.reflexField Φ.reflexField :=
    ⟨fun c a v ↦ by simp only [hψ, smul_eq_mul, mul_left_comm (ψ c) a v]⟩
  -- Since `E* = φ(E)`, `E*` is one-dimensional over `E`.
  have hdim : Module.finrank E Φ.reflexField = 1 := by
    refine (finrank_eq_one_iff_of_ne_zero' (1 : Φ.reflexField) one_ne_zero).mpr fun w ↦ ?_
    obtain ⟨c', hc'⟩ := hrange.le w.prop
    refine ⟨c', Subtype.ext ?_⟩
    rw [hψ, mul_one, hψφ, ← hc', AlgHom.toRingHom_eq_coe, RingHom.toRatAlgHom_toRingHom]
  have htrace (c : E) : (LinearMap.trace Φ.reflexField Φ.reflexField
      (DistribSMul.toLinearMap Φ.reflexField Φ.reflexField c) : ℂ) = Φ.typeTrace c := by
    have h : DistribSMul.toLinearMap Φ.reflexField Φ.reflexField c = ψ c • LinearMap.id :=
      LinearMap.ext fun v ↦ hψ c v
    rw [h, map_smul, LinearMap.trace_id, Module.finrank_self, typeTrace_eq_of_coe_eq_singleton hΦ]
    simp [ψ]
  have hsmul (v : Φ.reflexField) : a • v = c • v := by
    rw [hψ, smul_eq_mul, show ψ c = a from Subtype.ext ((hψφ c).trans ha.symm)]
  rw [reflexNorm_eq_smulDet Φ le_rfl Φ.reflexField htrace, smulDet_eq_pow_of_smul_eq hsmul, hdim,
    pow_one]

end Field

end TauCeti.CMType
