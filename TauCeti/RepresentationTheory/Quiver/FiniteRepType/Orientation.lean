/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Reorient
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Embedding
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Reflection
public import TauCeti.RepresentationTheory.Quiver.Reflection.Forest

/-!
# Finite representation type of a forest does not depend on the orientation

Whether a quiver has finite representation type is unchanged by reflecting it at a sink
(`TauCeti.isFiniteRepType_reflectList_iff`), and any two orientations of a finite forest are
related by such reflections (`Quiver.exists_isSinkAdmissible_reflectList_equiv`). So for a
quiver whose underlying graph is a forest, with at most one arrow between any two vertices, finite
representation type is a property of the underlying graph alone: every quiver with the same
underlying multigraph has finite representation type exactly when the original one does
(`TauCeti.isFiniteRepType_iff_of_isAcyclic_underlyingGraph`), and in particular so does every
reorientation `TauCeti.Reorient Q σ` (`TauCeti.isFiniteRepType_reorient_iff`).

This is how Gabriel's dichotomy is reduced to the underlying graph: for a tree, such as a Dynkin
or an extended Dynkin diagram other than a cycle, it suffices to treat a single orientation.

## Main results

* `TauCeti.isFiniteRepType_iff_of_isAcyclic_underlyingGraph`: two orientations of the same finite
  forest have finite representation type together.
* `TauCeti.isFiniteRepType_reorient_iff`: reorienting the arrows of a finite forest does not change
  whether it has finite representation type.

## References

* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys **28** (1973), 17--32.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} [Field k]

/-- **Finite representation type of a forest does not depend on the orientation.** Let `q` be a
quiver on a finite vertex type with at most one arrow between any two vertices, counted in both
directions, whose underlying graph is acyclic. A quiver `q'` with the same arrows joining any two
vertices, in either direction, has finite representation type exactly when `q` does. -/
theorem isFiniteRepType_iff_of_isAcyclic_underlyingGraph {V : Type v} [Finite V]
    (q q' : _root_.Quiver.{w} V)
    (hsub : ∀ a b : V,
      Subsingleton (@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a))
    (hG : (@underlyingGraph V q).IsAcyclic)
    (h : ∀ a b : V, Nonempty ((@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a) ≃
      (@_root_.Quiver.Hom V q' a b ⊕ @_root_.Quiver.Hom V q' b a))) :
    @IsFiniteRepType.{u, v, w, max v w x} k V _ q' ↔
      @IsFiniteRepType.{u, v, w, max v w x} k V _ q := by
  obtain ⟨l, hl, he⟩ := q.exists_isSinkAdmissible_reflectList_equiv q' hsub hG h
  have hfin (a b : V) : Finite (@_root_.Quiver.Hom V q a b) :=
    have : Subsingleton (@_root_.Quiver.Hom V q a b) :=
      ⟨fun y z ↦ Sum.inl_injective ((hsub a b).elim (Sum.inl y) (Sum.inl z))⟩
    inferInstance
  rw [← isFiniteRepType_reflectList_iff l q hfin hl]
  exact (isFiniteRepType_iff_of_homEquiv.{u, v, w, max w x} fun a b ↦ (he a b).some).symm

/-- **Reorienting a forest does not change whether it has finite representation type.** If a
finite quiver `Q` has at most one arrow between any two vertices, counted in both directions, and
its underlying graph is acyclic, then turning around any of its arrows gives a quiver
`TauCeti.Reorient Q σ` with finite representation type exactly when `Q` has it. -/
theorem isFiniteRepType_reorient_iff {Q : Type v} [q : _root_.Quiver.{w} Q] [Finite Q]
    (hsub : ∀ a b : Q, Subsingleton ((a ⟶ b) ⊕ (b ⟶ a)))
    (hG : (underlyingGraph Q).IsAcyclic) (σ : ∀ ⦃i j : Q⦄, (i ⟶ j) → Bool) :
    IsFiniteRepType.{u, v, w, max v w x} k (Reorient Q σ) ↔
      IsFiniteRepType.{u, v, w, max v w x} k Q := by
  classical
  refine isFiniteRepType_iff_of_isAcyclic_underlyingGraph _ (reorientQuiver σ) hsub hG
    fun a b ↦ ⟨?_⟩
  -- split the arrows `a ⟶ b` and `b ⟶ a` according to whether `σ` turns them around
  refine (Equiv.sumCongr (Equiv.sumCompl fun f : @_root_.Quiver.Hom Q q a b ↦ σ f = true).symm
    (Equiv.sumCompl fun f : @_root_.Quiver.Hom Q q b a ↦ σ f = true).symm).trans ?_
  refine ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans
    (Equiv.sumSumSumComm _ _ _ _)).trans ?_
  exact (Equiv.sumCongr (reorientHomEquiv σ a b).symm
    ((Equiv.sumComm _ _).trans (reorientHomEquiv σ b a).symm))

end TauCeti
