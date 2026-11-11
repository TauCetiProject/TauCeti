/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# The norm modulo an ideal

Let `S` be a free `R`-algebra and `I` an ideal of `R`. The norm of `S ⧸ IS` over `R ⧸ I`
of the class of `x` is the class of the norm of `x`. This is the norm counterpart of
`TauCeti.Algebra.trace_quotient_map_mk`. It lets a norm equation over `R` be solved first over the
quotient: taking `I` to be the maximal ideal of a local ring, it supplies the residual norm input
for lifting norm equations with Hensel's lemma (`TauCeti.Algebra.exists_norm_eq_of_norm_sub_mem`).

## Main results

* `TauCeti.Algebra.norm_quotient_mk`: the norm of `S ⧸ IS` over `R ⧸ I` of the class of `x` is
  the class of the norm of `x`.
-/

public section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]

/-- **The norm commutes with reduction modulo an ideal.** For a free algebra `S` over `R`
and an ideal `I` of `R`, the norm of `S ⧸ IS` over `R ⧸ I` of the class of `x` is the class of the
norm of `x`. -/
@[simp]
theorem Algebra.norm_quotient_mk (I : Ideal R) (x : S) :
    Algebra.norm (R ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap R S)) x) =
      Ideal.Quotient.mk I (Algebra.norm R x) := by
  by_cases hfin : Module.Finite R S
  · -- `S ⧸ IS` is the base change `(R ⧸ I) ⊗[R] S`, on which multiplication by `1 ⊗ x` is the
    -- base change of multiplication by `x`; the determinant commutes with base change.
    rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I),
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.norm_apply, Algebra.norm_apply,
      ← Ideal.Quotient.algebraMap_eq, ← LinearMap.det_baseChange, Algebra.baseChange_lmul]
  · -- If `S` is not finite, both norms are `1`, since the base change of an infinite basis stays
    -- infinite.
    rw [Algebra.norm_eq_one_of_not_module_finite hfin, map_one]
    rcases subsingleton_or_nontrivial (R ⧸ I) with h | h
    · exact Subsingleton.elim _ _
    rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I)]
    refine Algebra.norm_eq_one_of_not_module_finite (fun hf ↦ hfin ?_) _
    have := Module.Finite.finite_basis
      ((Module.Free.chooseBasis R S).baseChange (R ⧸ I))
    exact Module.Finite.of_basis (Module.Free.chooseBasis R S)

end TauCeti
