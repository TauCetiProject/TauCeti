/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Invariants
import Mathlib.RingTheory.Jacobson.Ring
import TauCeti.RingTheory.Invariant.Free
import TauCeti.RingTheory.Invariant.FiniteType

/-!
# Finiteness of descended group algebras

Let `L/k` be a field extension with finite automorphism group and let an abelian group `M` carry
an integral representation of `Aut(L/k)`. The simultaneous semilinear action on
`L[Multiplicative M]` has an invariant `k`-subalgebra, the fixed-point subalgebra of that action
(`TauCeti.GaloisDescent.groupAlgebraInvariants_eq_fixedPoints`). This file proves that the split
group algebra is finite as a module over that invariant algebra. The automorphism group acts
freely on its spectrum: for every nontrivial automorphism `σ` the displacements `σ • x - x`
generate the unit ideal, because `σ` moves some scalar `a` of `L` and the displacement `σ a - a`
is a unit. So the free-action finiteness theorem of Chase, Harrison and Rosenberg
(`TauCeti.MulSemiringAction.moduleFinite`) applies. When `L/k` is finite type and `M` is finitely
generated, Noether's finiteness theorem for the invariants of a finite group
(`TauCeti.FixedPoints.finiteType_subalgebra`, by the Artin--Tate lemma) shows that the invariant
algebra is finite type over `k`.

Finite type is necessary before the invariant algebra can serve as the coordinate algebra of the
torus descended from the split torus `D(M)`. When `L/k` is finite Galois, the scalar extension of
the invariant algebra to `L` is identified with `L[Multiplicative M]` in
`TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.BaseChange`; for a finite automorphism group
alone, the scalar-extension map is only shown to be surjective there. The descended torus of
`TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Torus` also needs `M` to be finitely
generated and torsion-free.

## Main declarations

* `TauCeti.GaloisDescent.instModuleFiniteGroupAlgebraInvariantsMonoidAlgebra`: the split group
  algebra is module-finite, hence integral, over its invariant algebra.
* `TauCeti.GaloisDescent.instFiniteTypeGroupAlgebraInvariants`: the invariant algebra is finite
  type over the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Proposition 7.8
  (Artin--Tate).
* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, Theorem 1.3 (finiteness for a
  free action, `TauCeti.MulSemiringAction.moduleFinite`).

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
instance instModuleFiniteGroupAlgebraInvariantsMonoidAlgebra
    [Finite (L ≃ₐ[k] L)] (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Module.Finite (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) := by
  let _ := groupAlgebraSMul rho
  let _ := groupAlgebraMulSemiringAction rho
  have := smulCommClass_groupAlgebraSMul rho
  rw [groupAlgebraInvariants_eq_fixedPoints]
  -- The action is free on the spectrum: a nontrivial automorphism moves some scalar `a`, and the
  -- displacement `σ a - a` of that scalar is a unit of the group algebra.
  refine TauCeti.MulSemiringAction.moduleFinite (G := L ≃ₐ[k] L) fun σ hσ ↦ ?_
  obtain ⟨a, ha⟩ : ∃ a : L, σ a ≠ a := by
    by_contra! h
    exact hσ (AlgEquiv.ext h)
  have halg (b : L) :
      groupAlgebraAction rho σ (algebraMap L (MonoidAlgebra L (Multiplicative M)) b) =
        algebraMap L _ (σ b) := by
    simp only [Algebra.algebraMap_eq_smul_one, groupAlgebraAction_smul, map_one]
  have hsub : σ • algebraMap L (MonoidAlgebra L (Multiplicative M)) a - algebraMap L _ a =
      algebraMap L _ (σ a - a) := by
    rw [groupAlgebraSMul_smul, halg, map_sub]
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
  let _ := groupAlgebraSMul rho
  let _ := groupAlgebraMulSemiringAction rho
  have := smulCommClass_groupAlgebraSMul rho
  rw [groupAlgebraInvariants_eq_fixedPoints]
  -- Noether's finiteness theorem for the invariants of a finite group (Artin--Tate).
  exact TauCeti.FixedPoints.finiteType_subalgebra k _ (L ≃ₐ[k] L)

end TauCeti.GaloisDescent
