/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Norm
import TauCeti.Algebra.Algebra.Tower
import TauCeti.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.Unramified.TraceRepresentation

/-!
# The reflex norms of a CM type and of its complementary type

Let `Φ` be a CM type on a number field `E`, `ιΦ` its complementary type, and `k ⊆ ℂ` a subfield of
finite degree containing the reflex field `E* = (ιΦ)*`. The reflex norms satisfy

`N_{k,Φ}(a) · N_{k,ιΦ}(a) = Nm_{k/ℚ}(a)`

(`TauCeti.CMType.reflexNorm_mul_reflexNorm_star`). The direct sum `V ⊕ V'` of the representations
with the type traces of `Φ` and `ιΦ` has trace `Tr_{E/ℚ}`, as does `k ⊗_ℚ E`, so the two are
isomorphic (`TauCeti.exists_linearEquiv_of_trace_eq`). The determinant over `E` of `a ∈ k` on
`V ⊕ V'` is the product of the reflex norms, and on `k ⊗_ℚ E ≅ E ⊗_ℚ k` it is the base change of
multiplication by `a` on `k`, whose determinant is `Nm_{k/ℚ}(a)`.

With `N_{k,ιΦ} = ι_E ∘ N_{k,Φ}` this is Milne's identity `N_{k,Φ}(a) · ι_E(N_{k,Φ}(a)) =
Nm_{k/ℚ}(a)` on rational points (Milne, *Complex Multiplication*, Remark 1.24(b), p.16).

## Main results

* `TauCeti.CMType.smulDet_tensorProduct`: the determinant over `E` of `a ∈ k` acting on `k ⊗_ℚ E`
  is `Nm_{k/ℚ}(a)`.
* `TauCeti.CMType.reflexNorm_mul_reflexNorm_star`: `N_{k,Φ}(a) · N_{k,ιΦ}(a) = Nm_{k/ℚ}(a)`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Remark 1.24(b), p.16.
-/

public section

open scoped TensorProduct

namespace TauCeti

section Prod

variable {E k V W : Type*} [CommRing E] [Semiring k] [AddCommGroup V] [Module E V] [Module k V]
  [SMulCommClass E k V] [AddCommGroup W] [Module E W] [Module k W] [SMulCommClass E k W]
  [Module.Free E V] [Module.Finite E V] [Module.Free E W] [Module.Finite E W]

/-- The determinant of the scalar action on a product is the product of the determinants. -/
theorem smulDet_prod (a : k) : smulDet E k (V × W) a = smulDet E k V a * smulDet E k W a := by
  have : SMulCommClass k E V := .symm E k V
  have : SMulCommClass k E W := .symm E k W
  rw [smulDet_apply, smulDet_apply, smulDet_apply, ← LinearMap.det_prodMap]
  rfl

end Prod

namespace CMType

section TensorProduct

variable (E : Type*) [Field E] [Algebra ℚ E] (k : Type*) [Field k] [Algebra ℚ k]

-- `E` acts on `k ⊗_ℚ E` through the right factor, commuting with the action of `k`.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The determinant over `E` of the action of `k` on `k ⊗_ℚ E` is the norm.** Here `E` acts
through the right factor (`Algebra.TensorProduct.rightAlgebra`). If `k` has infinite degree, both
sides are the junk value `1`. -/
theorem smulDet_tensorProduct (a : k) :
    smulDet E k (k ⊗[ℚ] E) a = algebraMap ℚ E (Algebra.norm ℚ a) := by
  by_cases hfin : Module.Finite ℚ k
  swap
  · rw [smulDet_apply, Algebra.norm_eq_one_of_not_module_finite hfin, map_one,
      LinearMap.det_eq_one_of_not_module_finite]
    exact fun h ↦ hfin (Module.Finite.of_baseChange (S := E)
      (Module.Finite.equiv (Algebra.TensorProduct.commRight ℚ E k).symm.toLinearEquiv))
  rw [smulDet_apply, Algebra.norm_apply, ← LinearMap.det_baseChange,
    ← LinearMap.det_conj _ (Algebra.TensorProduct.commRight ℚ E k).symm.toLinearEquiv]
  congr 1
  refine LinearMap.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul c x => rfl

end TensorProduct

section Field

variable {E : Type*} [Field E] [NumberField E] {k : IntermediateField ℚ ℂ}

-- A number field is formally unramified over `ℚ`, so its reflex norm is defined.
attribute [local instance] Algebra.FormallyUnramified.of_isSeparable
  Algebra.TensorProduct.rightAlgebra

/-- If `k` has infinite degree, the reflex norm is the junk value `1`: the representation with
the type trace is nonzero, so it is not finitely generated over `E`. -/
private theorem reflexNorm_eq_one (hfin : ¬FiniteDimensional ℚ k) (Φ : CMType E)
    (hk : Φ.reflexField ≤ k) (a : k) : Φ.reflexNorm hk a = 1 := by
  obtain ⟨n, ρ, hρ⟩ := Φ.exists_trace_eq_typeTrace hk
  let V := Fin n → k
  let := Module.compHom V ρ
  have := SMul.comp.smulCommClass (α := V) (β := k) ρ
  have : SMulCommClass k E V := .symm E k V
  -- `c ∈ E` acts on `V` as `ρ c` by definition, so `hρ` says that `V` has the type trace.
  rw [reflexNorm_eq_smulDet Φ hk V hρ, smulDet_apply, LinearMap.det_eq_one_of_not_module_finite]
  intro hE
  have : IsScalarTower ℚ E V := ρ.toRatAlgHom.isScalarTower_compHom
  have : Module.Finite ℚ V := Module.Finite.trans E V
  -- `V ≠ 0`: the type traces of `Φ` and `ιΦ` at `1` add up to `[E : ℚ] ≠ 0`.
  obtain ⟨i⟩ : Nonempty (Fin n) := by
    refine Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero fun hn ↦ ?_)
    subst hn
    have h := Φ.typeTrace_add_typeTrace_star_eq_trace 1
    rw [typeTrace_star, ← hρ, map_one, LinearMap.trace_one, Module.finrank_fin_fun] at h
    rw [← map_one (algebraMap ℚ E), Algebra.trace_algebraMap] at h
    have h' : (Module.finrank ℚ E : ℂ) = 0 := by simpa [eq_comm] using h
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne' (by exact_mod_cast h')
  exact hfin (Module.Finite.of_injective (LinearMap.single ℚ (fun _ : Fin n ↦ k) i)
    (Pi.single_injective (M := fun _ : Fin n ↦ k) i))

/-- **The reflex norms of a CM type and of its complementary type multiply to the norm.** For a
CM type `Φ` on a number field `E` and a subfield `k ⊆ ℂ` containing the reflex field,
`N_{k,Φ}(a) · N_{k,ιΦ}(a) = Nm_{k/ℚ}(a)`. If `k` has infinite degree, both sides are the junk
value `1`. -/
theorem reflexNorm_mul_reflexNorm_star (Φ : CMType E) (hk : Φ.reflexField ≤ k) (a : k) :
    Φ.reflexNorm hk a * (star Φ).reflexNorm (reflexField_star Φ ▸ hk) a =
      algebraMap ℚ E (Algebra.norm ℚ a) := by
  by_cases hfin : FiniteDimensional ℚ k
  swap
  · rw [reflexNorm_eq_one hfin, reflexNorm_eq_one hfin,
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
    have h1 : DistribSMul.toLinearMap k (V × V') c =
        (DistribSMul.toLinearMap k V c).prodMap (DistribSMul.toLinearMap k V' c) := rfl
    have h2 : DistribSMul.toLinearMap k (k ⊗[ℚ] E) c =
        (Algebra.lmul ℚ E c).baseChange k := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul x e => exact (Algebra.TensorProduct.tmul_mul_tmul (1 : k) x c e).trans (by simp)
    apply Subtype.ext
    rw [h1, h2, LinearMap.trace_prodMap', LinearMap.trace_baseChange, IntermediateField.coe_add,
      DistribSMul.toLinearMap_compHom, DistribSMul.toLinearMap_compHom, hρ, hρ',
      typeTrace_add_typeTrace_star_eq_trace, IntermediateField.coe_algebraMap_apply]
    rfl
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
