/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic

/-!
# Linear forms over a separable extension, through the trace

Let `L / K` be a finite separable field extension and `V` a vector space over `L`.  Composing an
`L`-linear form on `V` with the trace `Tr_{L/K} : L → K` gives a `K`-linear form on `V`, and every
`K`-linear form on `V` arises this way from exactly one `L`-linear form.  This is the
nondegeneracy of the trace form, `traceForm_nondegenerate`, applied pointwise: the `L`-linear
form attached to `μ` sends `v` to the element of `L` which the trace form pairs with
`b ↦ μ (b • v)`.

This is how Weil differentials of a function field are transported along an extension of the
constant field: they are linear forms over the constant field, and the trace form of the
constant-field extension converts linear forms over the larger constant field to linear forms over
the smaller one.

## Main definitions

* `Module.Dual.traceCompEquiv`: the `K`-linear equivalence
  `Module.Dual L V ≃ₗ[K] Module.Dual K V`, `φ ↦ Tr_{L/K} ∘ φ`.

## Main results

* `Module.Dual.traceCompEquiv_apply`: the equivalence composes with the trace.
* `Module.Dual.apply_eq_zero_iff_forall_trace_eq_zero`: an `L`-linear form vanishes at `v`
  exactly when the traces of its values on the `L`-line through `v` all vanish.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  proof of Theorem 3.4.6, where this identification converts the trace of a Weil differential
  into a Weil differential over the larger constant field.
-/

public section

namespace Module.Dual

variable {K L V : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-- The value at `v` of the `L`-linear form attached to a `K`-linear form `μ`: the element of `L`
whose trace pairing is the `K`-linear form `b ↦ μ (b • v)` on `L`. -/
private noncomputable def traceCompInvAux (μ : Module.Dual K V) (v : V) : L :=
  ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm
    (μ ∘ₗ (LinearMap.toSpanSingleton L V v).restrictScalars K)

private theorem trace_mul_traceCompInvAux (μ : Module.Dual K V) (v : V) (b : L) :
    Algebra.trace K L (traceCompInvAux (L := L) μ v * b) = μ (b • v) := by
  rw [← Algebra.traceForm_apply, traceCompInvAux, LinearMap.BilinForm.apply_toDual_symm_apply]
  simp

/-- `traceCompInvAux μ v` is the only element of `L` with the trace pairing `b ↦ μ (b • v)`. -/
private theorem eq_traceCompInvAux {μ : Module.Dual K V} {v : V} {x : L}
    (h : ∀ b : L, Algebra.trace K L (x * b) = μ (b • v)) : x = traceCompInvAux μ v :=
  sub_eq_zero.mp <| (traceForm_nondegenerate K L).1 _ fun b ↦ by
    rw [Algebra.traceForm_apply, sub_mul, map_sub, h, trace_mul_traceCompInvAux, sub_self]

variable (K L V) in
/-- The `L`-linear form attached to a `K`-linear form. -/
private noncomputable def traceCompInvFun (μ : Module.Dual K V) : Module.Dual L V where
  toFun := traceCompInvAux μ
  map_add' v w := (eq_traceCompInvAux fun b ↦ by
    rw [add_mul, map_add, trace_mul_traceCompInvAux, trace_mul_traceCompInvAux, smul_add,
      map_add]).symm
  map_smul' a v := (eq_traceCompInvAux fun b ↦ by
    rw [RingHom.id_apply, smul_eq_mul, mul_comm a, mul_assoc, trace_mul_traceCompInvAux, mul_comm,
      mul_smul]).symm

private theorem traceCompInvFun_apply (μ : Module.Dual K V) (v : V) :
    traceCompInvFun K L V μ v = traceCompInvAux μ v :=
  (rfl)

variable (K L V) in
/-- **Linear forms over a finite separable extension, through the trace**: composition with
`Tr_{L/K}` identifies the `L`-linear forms on an `L`-vector space with its `K`-linear forms. -/
noncomputable def traceCompEquiv : Module.Dual L V ≃ₗ[K] Module.Dual K V where
  toFun φ := Algebra.trace K L ∘ₗ φ.restrictScalars K
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp
  invFun := traceCompInvFun K L V
  left_inv φ := LinearMap.ext fun v ↦ by
    refine (traceCompInvFun_apply _ v).trans (eq_traceCompInvAux fun b ↦ ?_).symm
    simp [mul_comm (φ v) b]
  right_inv μ := LinearMap.ext fun v ↦ by
    simpa [traceCompInvFun_apply] using trace_mul_traceCompInvAux (L := L) μ v 1

/-- The equivalence `traceCompEquiv` composes a linear form with the trace. -/
@[simp]
theorem traceCompEquiv_apply (φ : Module.Dual L V) (v : V) :
    traceCompEquiv K L V φ v = Algebra.trace K L (φ v) :=
  (rfl)

/-- The `L`-linear form attached to a `K`-linear form `μ` has trace `μ`. -/
@[simp]
theorem trace_traceCompEquiv_symm_apply (μ : Module.Dual K V) (v : V) :
    Algebra.trace K L ((traceCompEquiv K L V).symm μ v) = μ v := by
  rw [← traceCompEquiv_apply, LinearEquiv.apply_symm_apply]

omit [Module K V] [IsScalarTower K L V] in
/-- An `L`-linear form vanishes at `v` exactly when the traces of its values at the multiples
`b • v` all vanish. -/
theorem apply_eq_zero_iff_forall_trace_eq_zero (φ : Module.Dual L V) (v : V) :
    φ v = 0 ↔ ∀ b : L, Algebra.trace K L (φ (b • v)) = 0 := by
  refine ⟨fun h b ↦ by simp [h], fun h ↦ ?_⟩
  refine (traceForm_nondegenerate K L).1 (φ v) fun b ↦ ?_
  rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul]
  exact h b

end Module.Dual
