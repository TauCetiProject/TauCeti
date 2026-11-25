/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Basic
public import Mathlib.LinearAlgebra.Dual.BaseChange
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
import TauCeti.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The convolution action after base change

Let `C` be a coalgebra over a commutative semiring `k`, let `M` be a `C`-comodule and let `K` be
a commutative `k`-algebra. The base change of a `k`-linear functional on `C` is an element of the
convolution algebra of `K ⊗[k] C`, and it acts on the base-changed comodule `K ⊗[k] M` as the base
change of its action on `M`.

When `C` is projective over `k` and `K` is a field, the base changes of the functionals on `C`
separate the points of `K ⊗[k] C` (`TauCeti.Module.Dual.eq_of_baseChange_eq`). Since a functional
acts through the matrix coefficients, a subspace of `K ⊗[k] M` stable under the base-changed
actions is then stable under the whole convolution algebra of `K ⊗[k] C`.

## Main results

* `TauCeti.Comodule.baseChangeDual`: the base change of a functional on `C`, in the convolution
  algebra of `K ⊗[k] C`; its underlying functional is `Module.Dual.baseChange`
  (`TauCeti.Comodule.ofConv_baseChangeDual`).
* `TauCeti.Comodule.convolutionAction_baseChangeDual`: the base change of a functional acts on
  `K ⊗[k] M` as the base change of its action on `M`.
* `TauCeti.Comodule.convolutionAction_mem_of_forall_baseChangeDual`: a subspace of `K ⊗[k] M`
  stable under these base-changed actions is stable under every functional on `K ⊗[k] C`.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

variable {k : Type u} {C : Type v} {M : Type w} (K : Type x)

section CommSemiring

variable [CommSemiring k] [AddCommMonoid C] [Module k C]
variable [CommSemiring K] [Algebra k K]

/-- The base change of a `k`-linear functional on a coalgebra, as an element of the convolution
algebra of the base-changed coalgebra. -/
noncomputable def baseChangeDual (f : WithConv (C →ₗ[k] k)) :
    WithConv (K ⊗[k] C →ₗ[K] K) :=
  WithConv.toConv (Module.Dual.baseChange K f.ofConv)

/-- The underlying functional of `baseChangeDual K f` is `Module.Dual.baseChange K f`. -/
@[simp]
theorem ofConv_baseChangeDual (f : WithConv (C →ₗ[k] k)) :
    (baseChangeDual K f).ofConv = Module.Dual.baseChange K f.ofConv :=
  (rfl)

/-- The base change of a functional evaluates on a pure tensor `a ⊗ c` to `f c • a`. -/
theorem baseChangeDual_tmul (f : WithConv (C →ₗ[k] k)) (a : K) (c : C) :
    (baseChangeDual K f).ofConv (a ⊗ₜ[k] c) = f.ofConv c • a := by
  simp

variable [Coalgebra k C] [AddCommMonoid M] [Module k M] [Comodule k C M]

/-- The base change of a functional acts on the base-changed comodule as the base change of its
action on the original comodule. -/
theorem convolutionAction_baseChangeDual (f : WithConv (C →ₗ[k] k)) :
    letI := Comodule.baseChange (R := k) (H := C) (M := M) K
    convolutionAction (R := K) (C := K ⊗[k] C) (M := K ⊗[k] M) (baseChangeDual K f) =
      (convolutionAction (R := k) (C := C) (M := M) f).baseChange K := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := M) K
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  rw [convolutionAction_apply, LinearMap.baseChange_tmul, convolutionAction_apply,
    baseChange_coact, baseChangeCoact_tmul]
  induction coact (R := k) (C := C) m with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul n c =>
    simp [LinearMap.tensorComponent_def, TensorProduct.smul_tmul']

end CommSemiring

variable [CommRing k] [AddCommMonoid C] [Module k C] [Module.Projective k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]
variable [Field K] [Algebra k K]

/-- If `C` is projective, a subspace of `K ⊗[k] M` which is stable under the base changes of the
`k`-linear functionals on `C` is stable under every `K`-linear functional on `K ⊗[k] C`. -/
theorem convolutionAction_mem_of_forall_baseChangeDual (P : Submodule K (K ⊗[k] M))
    (hP : ∀ f : WithConv (C →ₗ[k] k), ∀ v ∈ P,
      (convolutionAction (R := k) (C := C) (M := M) f).baseChange K v ∈ P)
    (g : WithConv (K ⊗[k] C →ₗ[K] K)) {v : K ⊗[k] M} (hv : v ∈ P) :
    letI := Comodule.baseChange (R := k) (H := C) (M := M) K
    convolutionAction (R := K) (C := K ⊗[k] C) (M := K ⊗[k] M) g v ∈ P := by
  let _ := Comodule.baseChange (R := k) (H := C) (M := M) K
  by_contra hg
  obtain ⟨φ, hφ, hφP⟩ := P.exists_dual_map_eq_bot_of_notMem hg inferInstance
  apply hφ
  have hf (f : WithConv (C →ₗ[k] k)) :
      (baseChangeDual K f).ofConv (matrixCoefficient (R := K) (C := K ⊗[k] C) φ v) = 0 := by
    rw [LinearMap.apply_matrixCoefficient, coactComponent_apply, ← convolutionAction_apply,
      convolutionAction_baseChangeDual]
    rw [← LinearMap.le_ker_iff_map] at hφP
    exact hφP (hP f v hv)
  have hc : matrixCoefficient (R := K) (C := K ⊗[k] C) φ v = 0 :=
    Module.Dual.eq_of_baseChange_eq fun f ↦ by simpa using hf (.toConv f)
  have := LinearMap.apply_matrixCoefficient (R := K) (C := K ⊗[k] C) g.ofConv φ v
  rw [hc, map_zero, coactComponent_apply, ← convolutionAction_apply] at this
  exact this.symm

end TauCeti.Comodule
