/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Invariants
import Mathlib.RingTheory.Jacobson.Ring
import TauCeti.RingTheory.Invariant.Free

/-!
# Finiteness of descended group algebras

Let `L/k` be a field extension with finite automorphism group and let an abelian group `M` carry
an integral representation of `Aut(L/k)`. The simultaneous semilinear action on
`L[Multiplicative M]` has an invariant `k`-subalgebra. This file proves that the split group
algebra is finite as a module over that invariant algebra: the automorphism group acts freely on
it, since every nontrivial automorphism already moves a scalar of `L`, so the free-action
finiteness theorem `TauCeti.MulSemiringAction.moduleFinite` applies. When `L/k` is finite type and
`M` is finitely generated, the Artin--Tate lemma then shows that the invariant algebra is finite
type over `k`.

Finite type is necessary before the invariant algebra can serve as the coordinate algebra of the
torus descended from the split torus `D(M)`. Its scalar extension to `L` is identified with
`L[Multiplicative M]` in `TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.BaseChange`.

## Main declarations

* `TauCeti.GaloisDescent.instModuleFiniteGroupAlgebraGroupAlgebraInvariants`: the split group
  algebra is module-finite, hence integral, over its invariant algebra.
* `TauCeti.GaloisDescent.instFiniteTypeGroupAlgebraInvariants`: the invariant algebra is finite
  type over the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 7.8
  (Artin--Tate).

This supplies the finite-type part of the inverse Galois-descent construction from an integral
Galois lattice.
-/

public section

open scoped TauCeti.GaloisDescent

namespace TauCeti.GaloisDescent

universe u_k u_L u_M

variable {k : Type u_k} {L : Type u_L} {M : Type u_M}
variable [Field k] [Field L] [Algebra k L] [AddCommGroup M]

/-- The split group algebra is finite as a module over its invariant algebra when the
automorphism group of `L/k` is finite. Neither `L/k` nor the exponent group needs to be finitely
generated. -/
instance instModuleFiniteGroupAlgebraGroupAlgebraInvariants
    [Finite (L ≃ₐ[k] L)] (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Module.Finite (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) := by
  let _ : SMul (L ≃ₐ[k] L) (MonoidAlgebra L (Multiplicative M)) :=
    ⟨fun σ x ↦ groupAlgebraAction rho σ x⟩
  let _ : MulSemiringAction (L ≃ₐ[k] L) (MonoidAlgebra L (Multiplicative M)) :=
    MulSemiringAction.compHom _ (groupAlgebraAction rho)
  have action_apply (σ : L ≃ₐ[k] L) (x : MonoidAlgebra L (Multiplicative M)) :
      σ • x = groupAlgebraAction rho σ x := rfl
  have : Algebra.IsInvariant (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) (L ≃ₐ[k] L) :=
    ⟨fun x hx ↦ ⟨⟨x, (mem_groupAlgebraInvariants_iff rho x).mpr fun σ ↦ by
      simpa only [action_apply] using hx σ⟩, rfl⟩⟩
  -- The action is free: a nontrivial automorphism moves some scalar `a`, and the displacement
  -- `σ a - a` of that scalar is a unit of the group algebra.
  refine TauCeti.MulSemiringAction.moduleFinite (G := L ≃ₐ[k] L) fun σ hσ ↦ ?_
  obtain ⟨a, ha⟩ : ∃ a : L, σ a ≠ a := by
    by_contra! h
    exact hσ (AlgEquiv.ext h)
  have hsub : σ • algebraMap L (MonoidAlgebra L (Multiplicative M)) a - algebraMap L _ a =
      algebraMap L _ (σ a - a) := by
    rw [action_apply, Algebra.algebraMap_eq_smul_one, groupAlgebraAction_smul, map_one,
      ← sub_smul, ← Algebra.algebraMap_eq_smul_one]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, hsub⟩)
    ((sub_ne_zero.mpr ha).isUnit.map _)

/-- For a finite-type field extension, the invariant algebra of the automorphism action on the
group algebra of a finitely generated abelian group is finite type over the ground field. -/
noncomputable instance instFiniteTypeGroupAlgebraInvariants
    [Algebra.FiniteType k L] [Module.Finite ℤ M]
    (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Algebra.FiniteType k (groupAlgebraInvariants rho) := by
  -- By Zariski's lemma `L/k` is finite, so its automorphism group is finite.
  have : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  let _ : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  let _ : Group.FG (Multiplicative M) := AddGroup.fg_iff_mul_fg.mp inferInstance
  let _ : Algebra.FiniteType k (MonoidAlgebra L (Multiplicative M)) :=
    Algebra.FiniteType.trans (R := k) (S := L) inferInstance inferInstance
  exact ⟨fg_of_fg_of_fg (A := k) (B := groupAlgebraInvariants rho)
    (C := MonoidAlgebra L (Multiplicative M))
      Algebra.FiniteType.out Module.Finite.fg_top (fun _ _ h ↦ Subtype.ext h)⟩

end TauCeti.GaloisDescent
