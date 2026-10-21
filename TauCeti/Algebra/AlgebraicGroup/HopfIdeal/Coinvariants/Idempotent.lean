/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
import Mathlib.RingTheory.FiniteStability
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Detecting invariant idempotents on algebraically closed points

For an idempotent function on an affine group of finite type over a field, invariance under a
closed subgroup can be tested on points valued in an algebraically closed extension. Neither the
group nor the subgroup needs to be reduced. This permits descent of unions of connected
components along faithfully flat group homomorphisms.

The argument uses the idempotent point-separation theorem in
`TauCeti.RingTheory.FiniteType.PointSeparation`, applied to the subgroup coaction.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6.7 and 16.3.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.HopfIdeal

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
  {H : CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]

/-- An idempotent function is invariant under a closed subgroup exactly when its values on
points valued in an algebraically closed extension are invariant. The subgroup and the ambient
group may be nonreduced. -/
theorem mem_coinvariants_iff_forall_mul_of_isIdempotentElem
    (I : HopfIdeal k H) {e : H} (he : IsIdempotentElem e) :
    e ∈ I.coinvariants ↔
      ∀ (g n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k K)),
        n ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K) →
          (g * n).ofConv e = g.ofConv e := by
  refine ⟨fun h g n hn ↦ ofConv_mul_apply_of_mem_coinvariants h g hn, fun h ↦ ?_⟩
  let coact := (Algebra.TensorProduct.map (AlgHom.id k H)
    (Ideal.Quotient.mkₐ k I.toIdeal)).comp (Bialgebra.comulAlgHom k H)
  let inc : H →ₐ[k] H ⊗[k] (H ⧸ I.toIdeal) := Algebra.TensorProduct.includeLeft
  let _ : Algebra.FiniteType k (H ⊗[k] (H ⧸ I.toIdeal)) :=
    Algebra.FiniteType.trans (R := k) (S := H) (A := H ⊗[k] (H ⧸ I.toIdeal))
      inferInstance inferInstance
  apply mem_coinvariants_iff.mpr
  apply eq_of_isIdempotentElem_of_forall_algHom_apply_eq
    (k := k) (K := K) (he.map coact) (he.map inc)
  intro p
  let g := p.comp inc
  let n := (p.comp Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ k I.toIdeal)
  have hn : toConv n ∈ CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K) := by
    apply (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H I _ _).mpr
    intro x hx
    simp [n, Ideal.Quotient.eq_zero_iff_mem.mpr (mem_toIdeal.mpr hx)]
  have hlift : (Algebra.TensorProduct.lift g n (fun _ _ ↦ .all _ _)) =
      p.comp (Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I.toIdeal)) := by
    ext <;> simp [g, n, inc]
  simpa only [AlgHom.convMul_apply, ofConv_toConv, hlift, AlgHom.comp_apply, coact, g,
    Bialgebra.comulAlgHom_apply]
    using h (toConv g) (toConv n) hn

end TauCeti.HopfIdeal
