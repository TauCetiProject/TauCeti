/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Norm
import TauCeti.Algebra.Algebra.Tower
import TauCeti.LinearAlgebra.Determinant.SMul.TensorProduct
import TauCeti.RingTheory.NormTrace.BaseChange
import TauCeti.RingTheory.Unramified.TraceRepresentation

/-!
# The reflex norms of a CM type and of its complementary type

Let `Φ` be a CM type on a number field `E`, `ιΦ` its complementary type, and `k ⊆ ℂ` a subfield of
finite degree containing the reflex field `E* = (ιΦ)*`. The reflex norms satisfy

`N_{k,Φ}(a) · N_{k,ιΦ}(a) = Nm_{k/ℚ}(a)`

(`TauCeti.CMType.reflexNorm_mul_reflexNorm_star`). The direct sum `V ⊕ V'` of the representations
with the type traces of `Φ` and `ιΦ` has trace `Tr_{E/ℚ}`, as does `k ⊗_ℚ E`, so the two are
isomorphic (`TauCeti.exists_linearEquiv_of_trace_eq`). The determinant over `E` of `a ∈ k` on
`V ⊕ V'` is the product of the reflex norms (`TauCeti.smulDet_prod`), and on `k ⊗_ℚ E` it is
`Nm_{k/ℚ}(a)` (`TauCeti.smulDet_tensorProduct`).

With `N_{k,ιΦ} = ι_E ∘ N_{k,Φ}` this is Milne's identity `N_{k,Φ}(a) · ι_E(N_{k,Φ}(a)) =
Nm_{k/ℚ}(a)` on rational points (Milne, *Complex Multiplication*, Remark 1.24(b), p.16).

## Main results

* `TauCeti.CMType.reflexNorm_mul_reflexNorm_star`: `N_{k,Φ}(a) · N_{k,ιΦ}(a) = Nm_{k/ℚ}(a)`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Remark 1.24(b), p.16.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace CMType

section Field

variable {E : Type*} [Field E] [NumberField E] {k : IntermediateField ℚ ℂ}

-- A number field is formally unramified over `ℚ`, so its reflex norm is defined.
attribute [local instance] Algebra.FormallyUnramified.of_isSeparable
  Algebra.TensorProduct.rightAlgebra

/-- **The reflex norms of a CM type and of its complementary type multiply to the norm.** For a
CM type `Φ` on a number field `E` and a subfield `k ⊆ ℂ` containing the reflex field,
`N_{k,Φ}(a) · N_{k,ιΦ}(a) = Nm_{k/ℚ}(a)`. If `k` has infinite degree, both sides are the junk
value `1`. -/
theorem reflexNorm_mul_reflexNorm_star (Φ : CMType E) (hk : Φ.reflexField ≤ k) (a : k) :
    Φ.reflexNorm hk a * (star Φ).reflexNorm (reflexField_star Φ ▸ hk) a =
      algebraMap ℚ E (Algebra.norm ℚ a) := by
  by_cases hfin : FiniteDimensional ℚ k
  swap
  · rw [reflexNorm_eq_one_of_not_finiteDimensional hfin,
      reflexNorm_eq_one_of_not_finiteDimensional hfin,
      Algebra.norm_eq_one_of_not_module_finite hfin, mul_one, map_one]
  -- The representations `V` and `V'` with the type traces of `Φ` and `ιΦ`.
  obtain ⟨n, ρ, hρ⟩ := Φ.exists_trace_eq_typeTrace hk
  obtain ⟨n', ρ', hρ'⟩ := (star Φ).exists_trace_eq_typeTrace (reflexField_star Φ ▸ hk)
  let V := Fin n → k
  let V' := Fin n' → k
  let := Module.compHom V ρ
  have := SMul.comp.smulCommClass (α := V) (β := k) ρ
  let := Module.compHom V' ρ'
  have := SMul.comp.smulCommClass (α := V') (β := k) ρ'
  -- `V ⊕ V'` and `k ⊗_ℚ E` have the same trace `Tr_{E/ℚ}`, so they are isomorphic.
  have htr (c : E) : LinearMap.trace k (V × V') (DistribSMul.toLinearMap k (V × V') c) =
      LinearMap.trace k (k ⊗[ℚ] E) (DistribSMul.toLinearMap k (k ⊗[ℚ] E) c) := by
    -- `c` acts on `k ⊗_ℚ E` as multiplication by `1 ⊗ c`, whose trace is `Tr_{E/ℚ}(c)`.
    have hmul : DistribSMul.toLinearMap k (k ⊗[ℚ] E) c = Algebra.lmul k (k ⊗[ℚ] E) (1 ⊗ₜ c) :=
      LinearMap.ext fun z ↦ by
        rw [DistribSMul.toLinearMap_apply, Algebra.smul_def,
          Algebra.TensorProduct.right_algebraMap_apply, Algebra.coe_lmul_eq_mul,
          LinearMap.mul_apply']
    apply Subtype.ext
    rw [DistribSMul.toLinearMap_prod, hmul, LinearMap.trace_prodMap',
      ← Algebra.trace_apply (R := k) (S := k ⊗[ℚ] E) (1 ⊗ₜ c),
      Algebra.trace_baseChange_tmul, IntermediateField.coe_add, DistribSMul.toLinearMap_compHom,
      DistribSMul.toLinearMap_compHom, hρ, hρ', typeTrace_add_typeTrace_star_eq_trace,
      IntermediateField.coe_algebraMap_apply]
  obtain ⟨e, he⟩ := exists_linearEquiv_of_trace_eq (R := ℚ) (V := V × V') (W := k ⊗[ℚ] E)
    (Module.toModuleEnd k (S := E) (V × V')).toRatAlgHom
    (Module.toModuleEnd k (S := E) (k ⊗[ℚ] E)).toRatAlgHom fun c ↦ by
      rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply]
      exact htr c
  -- Compare determinants: the product of the reflex norms on `V ⊕ V'`, the norm on `k ⊗_ℚ E`.
  have : Module.Finite ℚ V := Module.Finite.trans k V
  have : Module.Finite ℚ V' := Module.Finite.trans k V'
  have : IsScalarTower ℚ E V := ρ.toRatAlgHom.isScalarTower_compHom
  have : IsScalarTower ℚ E V' := ρ'.toRatAlgHom.isScalarTower_compHom
  have : Module.Finite E V := Module.Finite.of_restrictScalars_finite ℚ E V
  have : Module.Finite E V' := Module.Finite.of_restrictScalars_finite ℚ E V'
  have he' (c : E) (v : V × V') : e (c • v) = c • e v := by
    simpa only [RingHom.toRatAlgHom_apply, Module.toModuleEnd_apply,
      DistribSMul.toLinearMap_apply] using he c v
  rw [reflexNorm_eq_smulDet Φ hk V hρ, reflexNorm_eq_smulDet (star Φ) _ V' hρ', ← smulDet_prod,
    smulDet_congr e he', smulDet_tensorProduct]

end Field

end CMType

end TauCeti
