/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import Mathlib.RingTheory.FiniteStability
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.FiniteType.Tensor.Product

/-!
# Normality of reduced closed subgroups from rational points

Over an algebraically closed field `k`, let `H` be a reduced finite-type commutative Hopf algebra
and `I` a Hopf ideal with reduced quotient. Then the closed subgroup cut out by `I` is normal as
soon as conjugation by every rational point preserves it.

Normality asks that the coordinate conjugation `c♯ : H → H ⊗ H` send `I` into `H ⊗ I`, the
kernel of `H ⊗ H → H ⊗ (H ⧸ I)`. The algebra `H ⊗ (H ⧸ I)` is reduced and of finite type, so an
element of it vanishes once it vanishes at every rational point. A rational point of
`H ⊗ (H ⧸ I)` is a pair `(g, h)` with `h` a point of the subgroup, and evaluating `c♯ x` at it
gives `x (g h g⁻¹)`. That value is zero for `x ∈ I` when conjugation by `g` preserves `I`.

Without reducedness the criterion fails: rational points do not see infinitesimal structure.

## Main declarations

* `TauCeti.HopfIdeal.isNormal_of_forall_le_conjugate`: stability under conjugation by rational
  points gives normality.
* `TauCeti.HopfIdeal.isNormal_iff_forall_le_conjugate`: the resulting characterization of
  normal reduced closed subgroups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.d, for the rational points of reduced algebraic
  schemes, and §3.5, for normal closed subgroups.
-/

public section

open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]

/-- **Normality from rational points.** Over an algebraically closed field, a reduced closed
subgroup of a reduced finite-type affine group is normal when conjugation by every rational
point maps it into itself. -/
theorem isNormal_of_forall_le_conjugate (I : HopfIdeal k H) [IsReduced (H ⧸ I.toIdeal)]
    (hI : ∀ g : WithConv (H →ₐ[k] k), I ≤ I.conjugate g) : I.IsNormal := by
  rw [isNormal_iff_conjugation_mem]
  intro x hx
  let q : H →ₐ[k] H ⧸ I.toIdeal := Ideal.Quotient.mkₐ k I.toIdeal
  let F : H ⊗[k] H →ₐ[k] H ⊗[k] (H ⧸ I.toIdeal) :=
    Algebra.TensorProduct.map (AlgHom.id k H) q
  let _ : Algebra.FiniteType k (H ⊗[k] (H ⧸ I.toIdeal)) :=
    Algebra.FiniteType.trans (R := k) (S := H) (A := H ⊗[k] (H ⧸ I.toIdeal))
      inferInstance inferInstance
  rw [← ker_tensorProduct_map_id_quotient, RingHom.mem_ker]
  apply eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro φ
  let g : WithConv (H →ₐ[k] k) :=
    WithConv.toConv ((φ.comp F).comp Algebra.TensorProduct.includeLeft)
  let h : WithConv (H →ₐ[k] k) :=
    WithConv.toConv ((φ.comp F).comp Algebra.TensorProduct.includeRight)
  have hh : ∀ y ∈ I, h.ofConv y = 0 := by
    intro y hy
    simp [h, F, q, Ideal.Quotient.eq_zero_iff_mem.mpr (mem_toIdeal.mpr hy)]
  have hconj := AlgHom.congr_fun (HopfAlgebra.comp_conjugationAlgHom (φ.comp F)) x
  have hpoint := HopfAlgebra.comp_pointConjugationAlgHom g h
  rw [Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply] at hpoint
  rw [map_zero]
  calc φ (F (HopfAlgebra.conjugationAlgHom x))
      = (g * h * g⁻¹).ofConv x := hconj
    _ = h.ofConv (HopfAlgebra.pointConjugationAlgHom g x) := by
      rw [← hpoint, WithConv.ofConv_toConv, AlgHom.comp_apply]
    _ = 0 := hh _ (mem_conjugate.mp (hI g hx))

/-- Over an algebraically closed field, a reduced closed subgroup of a reduced finite-type affine
group is normal exactly when conjugation by every rational point maps it into itself. -/
theorem isNormal_iff_forall_le_conjugate (I : HopfIdeal k H) [IsReduced (H ⧸ I.toIdeal)] :
    I.IsNormal ↔ ∀ g : WithConv (H →ₐ[k] k), I ≤ I.conjugate g :=
  ⟨IsNormal.le_conjugate, isNormal_of_forall_le_conjugate I⟩

end TauCeti.HopfIdeal
