/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Derivative

/-!
# Restricting fields to stable submodules

If every mode `A₍ₙ₎` of a field `A(z)` on `V` maps a submodule `p` into itself, the restricted
modes are again the modes of a field on `p` (`VertexOperator.restrict`): lower truncation on a
vector of `p` is lower truncation in `V`. Restriction commutes with the formal derivative and
preserves mutual locality of every order. These are the facts needed to give a submodule closed
under all modes, such as a vertex subalgebra, its own fields.

## Main definitions

* `VertexOperator.restrict`: the restriction of a field to a submodule stable under its modes.

## Main results

* `VertexOperator.coe_ncoeff_restrict_apply`: the modes of the restriction act as the original
  modes.
* `VertexOperator.derivative_restrict`: restriction commutes with differentiation.
* `VertexOperator.IsLocalOfOrder.restrict`: restriction preserves locality.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset

namespace VertexOperator

variable {R V S : Type*} [CommRing R] [AddCommGroup V] [Module R V] [SetLike S V]
  [AddSubgroupClass S V] [SMulMemClass S R V] {p : S}

/-- The restriction of a field `A(z)` on `V` to a submodule `p` stable under every mode `A₍ₙ₎`.
The submodule may be given by any `SetLike` type of submodules, such as `Submodule R V`. -/
def restrict (A : VertexOperator R V) (hA : ∀ n : ℤ, ∀ v ∈ p, (A[[n]]) v ∈ p) :
    VertexOperator R p :=
  of_coeff
    (fun m ↦
      { toFun v := ⟨(A[[-m - 1]]) v, hA _ _ v.property⟩
        map_add' _ _ := Subtype.ext (map_add _ _ _)
        map_smul' _ _ := Subtype.ext (map_smul _ _ _) })
    fun v ↦ by
      obtain ⟨N, hN⟩ := exists_forall_ncoeff_apply_eq_zero A v
      refine ⟨-(N : ℤ) - 1, fun m hm ↦ not_lt.1 fun h ↦ hm ?_⟩
      ext
      simpa using hN (-m - 1) (by omega)

/-- The modes of a restricted field act on `p` as the original modes. -/
@[simp]
theorem coe_ncoeff_restrict_apply (A : VertexOperator R V)
    (hA : ∀ n : ℤ, ∀ v ∈ p, (A[[n]]) v ∈ p) (n : ℤ) (v : p) :
    (((A.restrict hA)[[n]]) v : V) = (A[[n]]) v := by
  simp [restrict]

omit [SMulMemClass S R V] in
/-- A submodule stable under every mode of `A` is stable under every mode of `∂A`. -/
theorem ncoeff_derivative_apply_mem {A : VertexOperator R V}
    (hA : ∀ n : ℤ, ∀ v ∈ p, (A[[n]]) v ∈ p) (n : ℤ) (v : V) (hv : v ∈ p) :
    ((derivative A)[[n]]) v ∈ p := by
  simpa using zsmul_mem (hA (n - 1) v hv) (-n)

/-- Restriction commutes with the formal derivative. -/
theorem derivative_restrict (A : VertexOperator R V) (hA : ∀ n : ℤ, ∀ v ∈ p, (A[[n]]) v ∈ p) :
    derivative (A.restrict hA) = (derivative A).restrict (ncoeff_derivative_apply_mem hA) := by
  refine ext_ncoeff fun n ↦ LinearMap.ext fun v ↦ Subtype.ext ?_
  simp

/-- Restriction to a submodule stable under both fields preserves mutual locality. -/
theorem IsLocalOfOrder.restrict {A B : VertexOperator R V} {N : ℕ} (h : A.IsLocalOfOrder B N)
    (hA : ∀ n : ℤ, ∀ v ∈ p, (A[[n]]) v ∈ p) (hB : ∀ n : ℤ, ∀ v ∈ p, (B[[n]]) v ∈ p) :
    (A.restrict hA).IsLocalOfOrder (B.restrict hB) N := by
  refine isLocalOfOrder_iff.2 fun m n ↦ LinearMap.ext fun v ↦ Subtype.ext ?_
  have h' := LinearMap.congr_fun (isLocalOfOrder_iff.1 h m n) (v : V)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply] at h' ⊢
  simpa using h'

end VertexOperator
