/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Invariants
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Jacobson.Ring
import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.BaseChange

/-!
# Finiteness of descended group algebras

Let `L/k` be a field extension with finite automorphism group and let an abelian group `M` carry
an integral representation of `Aut(L/k)`. The simultaneous semilinear action on
`L[Multiplicative M]` has an invariant `k`-subalgebra. This file proves that the split group
algebra is finite as a module over that invariant algebra: by Galois descent the invariant
elements span it over `L`, and `L` is finite over the fixed field of its automorphism group.
When `L/k` is finite type and `M` is finitely generated, the Artin--Tate lemma then shows that the
invariant algebra is finite type over `k`.

Finite type is necessary before the invariant algebra can serve as the coordinate algebra of the
torus descended from the split torus `D(M)`. Its scalar extension to `L` is identified with
`L[Multiplicative M]` in `TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.BaseChange`, whose
surjectivity half is the descent step used here.

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
automorphism group of `L/k` is finite. By Galois descent the invariant elements span the group
algebra over `L`, and `L` is finite over the fixed field of its automorphism group, which lies in
the invariant algebra. Neither `L/k` nor the exponent group needs to be finitely generated. -/
instance instModuleFiniteGroupAlgebraGroupAlgebraInvariants
    [Finite (L ≃ₐ[k] L)] (rho : Representation ℤ (L ≃ₐ[k] L) M) :
    Module.Finite (groupAlgebraInvariants rho)
      (MonoidAlgebra L (Multiplicative M)) := by
  obtain ⟨n, s, hs⟩ :=
    Module.Finite.exists_fin (R := FixedPoints.subfield (L ≃ₐ[k] L) L) (M := L)
  let N : Submodule (groupAlgebraInvariants rho) (MonoidAlgebra L (Multiplicative M)) :=
    Submodule.span _ (Set.range fun i ↦ algebraMap L (MonoidAlgebra L (Multiplicative M)) (s i))
  -- Every `L`-multiple of an invariant element lies in `N`, spanned by a generating family of `L`
  -- over the fixed field.
  have hmem (a : L) (x : groupAlgebraInvariants rho) :
      a • (x : MonoidAlgebra L (Multiplicative M)) ∈ N := by
    have ha : a ∈ Submodule.span (FixedPoints.subfield (L ≃ₐ[k] L) L) (Set.range s) :=
      hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction generalizing x with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      rw [Algebra.smul_def, mul_comm]
      exact N.smul_mem x (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_smul]
      exact N.add_mem (ha x) (hb x)
    | smul c a _ ha =>
      have hc : algebraMap L (MonoidAlgebra L (Multiplicative M)) c ∈ groupAlgebraInvariants rho :=
        algebraMap_mem_groupAlgebraInvariants rho c fun σ ↦ c.2 σ
      have := ha (⟨_, hc⟩ * x)
      rwa [Subalgebra.coe_mul, ← Algebra.smul_def, smul_smul, mul_comm] at this
  suffices hN : N = ⊤ from ⟨Submodule.fg_def.mpr ⟨_, Set.finite_range _, hN⟩⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := liftEquiv_groupAlgebraInvariants_surjective rho y
  induction t using TensorProduct.inductionOn with
  | tmul a x => simpa using hmem a x
  | add t u ht hu => simpa only [map_add] using N.add_mem ht hu

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
