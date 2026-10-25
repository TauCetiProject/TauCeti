/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Abelianization
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Perfect affine groups and commutative images

For a geometrically reduced affine group of finite type over a field, the derived closed
subgroup is the whole group exactly when every homomorphism to a commutative affine group
is trivial. The target group need not be of finite type. This concerns the scheme-theoretic
derived subgroup, not perfectness of the group of rational points.

The converse uses the affine abelianization: its coordinate map is trivial, so its kernel
is the whole group. The exact-kernel theorem for coinvariant projections identifies this
kernel with the derived subgroup, including its scheme structure.

A separate criterion needs only reducedness: a finite-type affine group with reduced coordinate
ring equals its derived closed subgroup as soon as its group of points with values in one
algebraically closed extension field is perfect, because such points separate functions. This is
how scheme-theoretic perfectness of concrete matrix groups is deduced from perfectness of their
abstract groups of geometric points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open CategoryTheory

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] (H : _root_.CommHopfAlgCat.{v} k) [Algebra.FiniteType k H]

section GeometricallyReduced

variable [Algebra.IsGeometricallyReduced k H]

/-- A geometrically reduced finite-type affine group equals its derived closed subgroup
exactly when all its homomorphisms to commutative affine groups are trivial.
The target coordinate algebra may be infinite-dimensional. -/
theorem derivedDefiningIdeal_eq_bot_iff_forall_hom_eq_unit_comp_counit :
    derivedDefiningIdeal (R := k) H = ⊥ ↔
      ∀ (C : _root_.CommHopfAlgCat.{v} k) [Coalgebra.IsCocomm k C] (f : C ⟶ H),
        f = _root_.CommHopfAlgCat.ofHom
          ((Bialgebra.unitBialgHom k H).comp (Bialgebra.counitBialgHom k C)) := by
  constructor
  · intro hD C _ f
    simpa only [Category.comp_id] using
      (comp_eq_unit_comp_counit_iff f (𝟙 H)).mpr (by
        have hker := f.kernelHopfIdeal_le_derivedDefiningIdeal
        rw [hD] at hker
        rw [le_bot_iff.mp hker, HopfIdeal.bot_toIdeal]
        exact bot_le)
  · intro h
    have htriv := h (coinvariants (isNormal_derivedDefiningIdeal H))
      (coinvariantsι (isNormal_derivedDefiningIdeal H))
    have hker := (comp_eq_unit_comp_counit_iff
      (coinvariantsι (isNormal_derivedDefiningIdeal H)) (𝟙 H)).mp
        (by simpa only [Category.comp_id] using htriv)
    rw [kernelHopfIdeal_coinvariantsι_eq,
      (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id] at hker
    apply le_antisymm _ bot_le
    rw [← HopfIdeal.toIdeal_le_toIdeal, HopfIdeal.bot_toIdeal]
    exact hker

end GeometricallyReduced

section Reduced

variable {H} [IsReduced H]

/-- A reduced finite-type affine group equals its derived closed subgroup if its group of points
with values in some algebraically closed extension field is perfect. The derived defining ideal
is then zero, so the equality retains the full scheme structure. -/
theorem derivedDefiningIdeal_eq_bot_of_commutator_eq_top
    {K : Type*} [Field K] [Algebra k K] [IsAlgClosed K]
    (hK : commutator (WithConv (H →ₐ[k] K)) = ⊤) :
    derivedDefiningIdeal (R := k) H = ⊥ := by
  apply le_bot_iff.mp
  rw [← HopfIdeal.toIdeal_le_toIdeal, HopfIdeal.bot_toIdeal]
  intro x hx
  rw [Ideal.mem_bot]
  apply eq_of_forall_algHom_apply_eq (k := k) (K := K)
  intro f
  rw [map_zero]
  have hf : WithConv.toConv f ∈ commutator (WithConv (H →ₐ[k] K)) := by
    rw [hK]
    trivial
  exact (mem_quotientPointsSubgroup_iff _ _ _ _).mp
    (commutator_le_quotientPointsSubgroup_of_le_derivedDefiningIdeal H _ le_rfl
      (CommAlgCat.of k K) hf) x hx

end Reduced

end CommHopfAlgCat
