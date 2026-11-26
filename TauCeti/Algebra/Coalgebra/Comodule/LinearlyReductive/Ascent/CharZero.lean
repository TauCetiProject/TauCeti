/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.RingTheory.Semisimple.BaseChange
public import TauCeti.RingTheory.SimpleModule.Subalgebra
import TauCeti.Algebra.Coalgebra.Comodule.Convolution.BaseChange
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Complete reducibility of a comodule ascends in characteristic zero

Let `C` be a coalgebra over a field `k` of characteristic zero and let `M` be a completely
reducible `C`-comodule. For every field extension `K` of `k`, the base-changed comodule
`K ⊗[k] M` over `K ⊗[k] C` is completely reducible.

A completely reducible comodule is the sum of its simple subcomodules, which are
finite-dimensional, so it suffices to treat finite-dimensional `M`. Then the convolution algebra
`C^∨` acts on `M` through a finite-dimensional subalgebra `B` of `End_k(M)`. Complete
reducibility makes `M` a semisimple `B`-module, and `B` embeds in a finite power of `M`, so `B`
is a semisimple algebra (`Subalgebra.isSemisimpleRing_of_isSemisimpleModule`). In characteristic
zero, as over any perfect field, `K ⊗[k] B` is again semisimple
(`TauCeti.isSemisimpleRing_tensorProduct_of_perfectField`), so `K ⊗[k] M` is a
semisimple `K ⊗[k] B`-module. Its `K ⊗[k] B`-submodules are exactly its subcomodules: a
subcomodule is stable under the base changes of the `C^∨`-action, and conversely a subspace stable
under them is stable under every `K`-linear functional on `K ⊗[k] C`, because the base changes of
the `k`-linear functionals on `C` separate the points of `K ⊗[k] C` and a functional acts through
the matrix coefficients (`TauCeti.Comodule.convolutionAction_mem_of_forall_baseChangeDual`). The
two lattices of submodules are therefore order isomorphic, and complements transfer.

Characteristic zero is used only for the semisimplicity of `K ⊗[k] B`. Over an imperfect field
the statement fails: a purely inseparable extension field `B` of `k`, as a comodule over the dual
coalgebra of `B`, is simple, while `K ⊗[k] B` has nonzero nilpotent radical for `K = B`.

The descent direction, for any nonzero commutative algebra, is
`TauCeti.Comodule.IsCompletelyReducible.of_baseChange`.

## Main results

* `TauCeti.Comodule.IsCompletelyReducible.baseChange`: complete reducibility of a comodule
  ascends along field extensions in characteristic zero.

## References

* N. Bourbaki, *Algebra, Chapter 8*, §12, no. 7.
* J. S. Milne, *Algebraic Groups* (2017), §4.a and Theorem 22.42.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

variable {k : Type u} {C : Type v} {M : Type w} (K : Type x)
variable [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]
variable [Field K] [Algebra k K]

section CharZero

variable (k C M) in
/-- The subalgebra of `End_k(M)` through which the convolution algebra of `C` acts on `M`. -/
private noncomputable abbrev actionRange : Subalgebra k (Module.End k M) :=
  (convolutionAction (R := k) (C := C) (M := M)).range

/-- A completely reducible comodule is a semisimple module over the image of the convolution
algebra. -/
private theorem isSemisimpleModule_actionRange (h : IsCompletelyReducible k C M) :
    IsSemisimpleModule (actionRange k C M) M := by
  let _ := convolutionModule (R := k) (C := C) (M := M)
  have hD := (isCompletelyReducible_iff_isSemisimpleModule (R := k) (C := C) (V := M)).1 h
  let σ := (convolutionAction (R := k) (C := C) (M := M)).rangeRestrict.toRingHom
  have : RingHomSurjective σ := ⟨AlgHom.rangeRestrict_surjective _⟩
  -- `σ f` is `convolutionAction f` as an element of the range, and both scalar actions are
  -- `Module.compHom` actions evaluating that endomorphism, so they agree by definition.
  let l : M →ₛₗ[σ] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact (l.isSemisimpleModule_iff_of_bijective Function.bijective_id).1 hD

variable (k C M) in
/-- The action of `K ⊗[k] B` on `K ⊗[k] M`, for `B` the image of the convolution algebra. -/
private noncomputable def baseChangeAction :
    K ⊗[k] actionRange k C M →ₐ[K] Module.End K (K ⊗[k] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _)
    ((Module.End.baseChangeHom k K M).comp (actionRange k C M).val)
    fun a _ ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left a _

/-- The pure tensor `a ⊗ s` acts as `a` times the base change of `s`. -/
private theorem baseChangeAction_tmul (a : K) (s : actionRange k C M) :
    baseChangeAction k C M K (a ⊗ₜ[k] s) = a • (s : Module.End k M).baseChange K := by
  rw [baseChangeAction, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, ← Algebra.smul_def]
  -- `Module.End.baseChangeHom` is `LinearMap.baseChange` bundled as an algebra map, and Mathlib has
  -- no application lemma for it in those terms (its `simps` lemma unfolds to
  -- `TensorProduct.liftAux`), so `baseChangeHom s = s.baseChange K` is used by definition.
  rfl

/-- An additive submonoid of `K ⊗[k] M` is stable under the convolution algebra of
`K ⊗[k] C`, that is, it is a subcomodule, if and only if it is stable under the action of
`K ⊗[k] B`. -/
private theorem forall_convolutionAction_mem_iff (P : AddSubmonoid (K ⊗[k] M)) :
    letI := Comodule.baseChange (R := k) (H := C) (M := M) K
    (∀ (g : WithConv (K ⊗[k] C →ₗ[K] K)) {v}, v ∈ P →
        convolutionAction (R := K) (C := K ⊗[k] C) (M := K ⊗[k] M) g v ∈ P) ↔
      ∀ (r : K ⊗[k] actionRange k C M) {v}, v ∈ P → baseChangeAction k C M K r v ∈ P := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := M) K
  refine ⟨fun hP r v hv ↦ ?_, fun hP g v hv ↦ ?_⟩
  · induction r with
    | add r s hr hs => rw [map_add, LinearMap.add_apply]; exact P.add_mem hr hs
    | tmul a s =>
      obtain ⟨_, f, rfl⟩ := s
      rw [baseChangeAction_tmul]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← convolutionAction_baseChangeDual, ← map_smul]
      exact hP _ hv
  · -- `P` is a `K`-subspace, stable under the base changes of the `C^∨`-action.
    let PK : Submodule K (K ⊗[k] M) :=
      { P with
        smul_mem' := fun a v hv ↦ by
          simpa [baseChangeAction_tmul] using hP (a ⊗ₜ[k] 1) hv }
    refine convolutionAction_mem_of_forall_baseChangeDual K PK (fun f v hv ↦ ?_) g hv
    have := hP (1 ⊗ₜ[k] ⟨_, AlgHom.mem_range_self _ f⟩) hv
    rwa [baseChangeAction_tmul, one_smul] at this

variable [CharZero k]

/-- The finite-dimensional case of `TauCeti.Comodule.IsCompletelyReducible.baseChange`. -/
private theorem IsCompletelyReducible.baseChange_of_finite [Module.Finite k M]
    (h : IsCompletelyReducible k C M) :
    letI := Comodule.baseChange (R := k) (H := C) (M := M) K
    IsCompletelyReducible K (K ⊗[k] C) (K ⊗[k] M) := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := M) K
  let _ := convolutionModule (R := K) (C := K ⊗[k] C) (M := K ⊗[k] M)
  let B := actionRange k C M
  have := isSemisimpleModule_actionRange h
  have := B.isSemisimpleRing_of_isSemisimpleModule
  let _ : Module (K ⊗[k] B) (K ⊗[k] M) :=
    Module.compHom _ (baseChangeAction k C M K).toRingHom
  -- Both scalar actions are `Module.compHom` actions, evaluating `convolutionAction` and
  -- `baseChangeAction` respectively, so their `smul_mem'` conditions are those of
  -- `forall_convolutionAction_mem_iff`.
  let e : Submodule (K ⊗[k] B) (K ⊗[k] M) ≃o
      Submodule (WithConv (K ⊗[k] C →ₗ[K] K)) (K ⊗[k] M) :=
    { toFun P :=
        { P.toAddSubmonoid with
          smul_mem' :=
            (forall_convolutionAction_mem_iff K P.toAddSubmonoid).2 fun r _ ↦ P.smul_mem r }
      invFun W :=
        { W.toAddSubmonoid with
          smul_mem' :=
            (forall_convolutionAction_mem_iff K W.toAddSubmonoid).1 fun g _ ↦ W.smul_mem g }
      left_inv _ := rfl
      right_inv _ := rfl
      map_rel_iff' := Iff.rfl }
  rw [isCompletelyReducible_iff_isSemisimpleModule, isSemisimpleModule_iff]
  exact e.complementedLattice

/-- **Complete reducibility of a comodule ascends along field extensions in characteristic
zero.** If `M` is a completely reducible comodule over a coalgebra `C` over a field `k` of
characteristic zero, then `K ⊗[k] M` is a completely reducible comodule over `K ⊗[k] C` for every
field extension `K` of `k`.

`M` is the sum of its simple subcomodules, which are finite-dimensional, and the base change of
each of them is completely reducible. -/
theorem IsCompletelyReducible.baseChange (h : IsCompletelyReducible k C M) :
    letI := Comodule.baseChange (R := k) (H := C) (M := M) K
    IsCompletelyReducible K (K ⊗[k] C) (K ⊗[k] M) := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := M) K
  let _ := convolutionModule (R := K) (C := K ⊗[k] C) (M := K ⊗[k] M)
  -- The image in `K ⊗[k] M` of the base change of a simple subcomodule.
  let p (S : {S : Subcomodule k C M // IsAtom S}) :
      Submodule (WithConv (K ⊗[k] C →ₗ[K] K)) (K ⊗[k] M) :=
    letI := Comodule.baseChange (R := k) (H := C) (M := S.val) K
    letI := convolutionModule (R := K) (C := K ⊗[k] C) (M := K ⊗[k] S.val)
    LinearMap.range (Hom.baseChange K (Subcomodule.subtype S.val)).toConvolutionLinearMap
  have hp (S : {S : Subcomodule k C M // IsAtom S}) :
      IsSemisimpleModule (WithConv (K ⊗[k] C →ₗ[K] K)) (p S) := by
    let _ := Comodule.baseChange (R := k) (H := C) (M := S.val) K
    let _ := convolutionModule (R := K) (C := K ⊗[k] C) (M := K ⊗[k] S.val)
    have : Module.Finite k S.val := Subcomodule.finite_of_isAtom S.property
    have hS : IsCompletelyReducible k C S.val := by
      let _ := convolutionModule (R := k) (C := C) (M := S.val)
      have := (Subcomodule.isSimpleModule_convolution_iff_isAtom S.val).2 S.property
      exact (isCompletelyReducible_iff_isSemisimpleModule (R := k)).2 inferInstance
    have := (isCompletelyReducible_iff_isSemisimpleModule (R := K)).1 (hS.baseChange_of_finite K)
    exact IsSemisimpleModule.range _
  rw [isCompletelyReducible_iff_isSemisimpleModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hp (Submodule.eq_top_iff'.2 fun x ↦ ?_)
  -- Every pure tensor `a ⊗ m` lies in the sum, because `M` is the sum of its simple
  -- subcomodules.
  let P : Submodule k M :=
    { carrier := {m | ∀ a : K, a ⊗ₜ[k] m ∈ ⨆ S, p S}
      add_mem' := fun hm hn a ↦ by rw [TensorProduct.tmul_add]; exact add_mem (hm a) (hn a)
      zero_mem' := fun a ↦ by rw [TensorProduct.tmul_zero]; exact zero_mem _
      smul_mem' := fun c m hm a ↦ by rw [← TensorProduct.smul_tmul]; exact hm _ }
  have hP : (⊤ : Submodule k M) ≤ P := by
    rw [← Subcomodule.top_toSubmodule (R := k) (C := C) (M := M),
      ← (isCompletelyReducible_iff_sSup_atoms_eq_top (R := k)).1 h,
      Subcomodule.sSup_toSubmodule, iSup_le_iff]
    intro S m hm a
    let _ := Comodule.baseChange (R := k) (H := C) (M := S.val) K
    let _ := convolutionModule (R := K) (C := K ⊗[k] C) (M := K ⊗[k] S.val)
    refine le_iSup p ⟨S.val, S.property⟩ (LinearMap.mem_range.2 ⟨a ⊗ₜ[k] ⟨m, hm⟩, ?_⟩)
    simp
  induction x with
  | add x y hx hy => exact add_mem hx hy
  | tmul a m => exact hP Submodule.mem_top a

end CharZero

end TauCeti.Comodule
