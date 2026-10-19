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

Combined with the passage of finite representation type to subquivers, this frees the forest from
the arrows of the ambient quiver as well: if the underlying graph of a forest quiver `P` has a copy
in the underlying graph of a quiver `Q` of finite representation type, then `P` has finite
representation type (`TauCeti.IsFiniteRepType.of_copy_underlyingGraph`). The arrows of `Q` over the
edges of the copy orient the forest in some way, giving a subquiver of `Q`, and that orientation has
finite representation type together with `P`.

This is how Gabriel's dichotomy is reduced to the underlying graph: for a tree, such as a Dynkin
or an extended Dynkin diagram other than a cycle, it suffices to treat a single orientation.

## Main results

* `TauCeti.isFiniteRepType_iff_of_isAcyclic_underlyingGraph`: two orientations of the same finite
  forest have finite representation type together.
* `TauCeti.isFiniteRepType_reorient_iff`: reorienting the arrows of a finite forest does not change
  whether it has finite representation type.
* `TauCeti.IsFiniteRepType.of_copy_underlyingGraph`: a finite forest quiver whose underlying graph
  has a copy in the underlying graph of a quiver of finite representation type has finite
  representation type.

## References

* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys **28** (1973), 17--32.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
-/

public section

namespace TauCeti

open _root_.TauCeti.Quiver

universe u v w x v' w'

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

section Copy

variable {Q : Type v} [Quiver.{w} Q] {W : Type v'} [Quiver.{w'} W] {n : ℕ}
  (f : (underlyingGraph W).Copy (underlyingGraph Q)) (σ : W ≃ Fin n)

/-- The edges of the copy `f` that the orientation `TauCeti.copyQuiver` directs from `a` to `b`:
those carrying an arrow `f a ⟶ f b` of `Q`, and, when `Q` also has an arrow back, with `a` the
`σ`-smaller end. -/
private def CopyRel (a b : W) : Prop :=
  (underlyingGraph W).Adj a b ∧ Nonempty (f a ⟶ f b) ∧ (Nonempty (f b ⟶ f a) → σ a < σ b)

/-- The orientation of a forest `W` by the arrows of `Q` along a copy `f` of its underlying graph,
with the vertex order `σ` breaking ties: one arrow over each edge of the copy, directed as in
`TauCeti.CopyRel`. -/
@[instance_reducible]
private def copyQuiver : _root_.Quiver.{w'} W :=
  ⟨fun a b ↦ ULift.{w'} (PLift (CopyRel f σ a b))⟩

/-- The arrows of `TauCeti.copyQuiver` from `a` to `b` are the proofs of `TauCeti.CopyRel`. -/
private def copyQuiverHomEquiv (a b : W) :
    @Quiver.Hom W (copyQuiver f σ) a b ≃ PLift (CopyRel f σ a b) :=
  Equiv.ulift

/-- `TauCeti.CopyRel` never holds in both directions. -/
private theorem CopyRel.asymm {a b : W} (hab : CopyRel f σ a b) (hba : CopyRel f σ b a) : False :=
  (hab.2.2 hba.2.1).asymm (hba.2.2 hab.2.1)

/-- Over every edge of the copy, `TauCeti.CopyRel` holds in one direction. -/
private theorem CopyRel.of_adj {a b : W} (hab : (underlyingGraph W).Adj a b) :
    CopyRel f σ a b ∨ CopyRel f σ b a := by
  obtain ⟨-, hf⟩ := underlyingGraph_adj.mp (f.toHom.map_adj hab)
  by_cases hr : Nonempty (f a ⟶ f b) ∧ (Nonempty (f b ⟶ f a) → σ a < σ b)
  · exact .inl ⟨hab, hr⟩
  simp only [not_and, not_imp] at hr
  refine .inr ⟨hab.symm, hf.elim (fun h ↦ (hr h).1) id, fun h ↦ ?_⟩
  exact lt_of_le_of_ne (not_lt.mp (hr h).2) (σ.injective.ne hab.ne).symm

/-- The quiver `TauCeti.copyQuiver` has at most one arrow between any two vertices, counted in
both directions. -/
private theorem subsingleton_copyQuiver_hom_sum (a b : W) :
    Subsingleton (@Quiver.Hom W (copyQuiver f σ) a b ⊕ @Quiver.Hom W (copyQuiver f σ) b a) := by
  refine ⟨?_⟩
  rintro (x | x) (y | y)
  · exact congrArg Sum.inl ((copyQuiverHomEquiv f σ a b).injective (Subsingleton.elim _ _))
  · exact (CopyRel.asymm f σ (copyQuiverHomEquiv f σ a b x).down
      (copyQuiverHomEquiv f σ b a y).down).elim
  · exact (CopyRel.asymm f σ (copyQuiverHomEquiv f σ a b y).down
      (copyQuiverHomEquiv f σ b a x).down).elim
  · exact congrArg Sum.inr ((copyQuiverHomEquiv f σ b a).injective (Subsingleton.elim _ _))

/-- The quiver `TauCeti.copyQuiver` joins two vertices by an arrow exactly when they are adjacent in
the forest. -/
private theorem nonempty_copyQuiver_hom_sum_iff (a b : W) :
    Nonempty (@Quiver.Hom W (copyQuiver f σ) a b ⊕ @Quiver.Hom W (copyQuiver f σ) b a) ↔
      (underlyingGraph W).Adj a b := by
  refine ⟨?_, fun hab ↦ ?_⟩
  · rintro ⟨x | x⟩
    · exact ((copyQuiverHomEquiv f σ a b) x).down.1
    · exact ((copyQuiverHomEquiv f σ b a) x).down.1.symm
  · rcases CopyRel.of_adj f σ hab with h | h
    · exact ⟨.inl ((copyQuiverHomEquiv f σ a b).symm ⟨h⟩)⟩
    · exact ⟨.inr ((copyQuiverHomEquiv f σ b a).symm ⟨h⟩)⟩

/-- The chosen arrows of `Q` embed `TauCeti.copyQuiver` in `Q`. -/
private noncomputable def copyQuiverEmbedding : @QuiverEmbedding W (copyQuiver f σ) Q _ :=
  @QuiverEmbedding.mk W (copyQuiver f σ) Q _
    (@Prefunctor.mk W (copyQuiver f σ) Q _ f fun {a b} e ↦
      ((copyQuiverHomEquiv f σ a b) e).down.2.1.some)
    f.injective fun {a b} _ _ _ ↦
      (copyQuiverHomEquiv f σ a b).injective (Subsingleton.elim _ _)

end Copy

/-- **Finite representation type passes to forests in the underlying graph.** Let `W` be a finite
quiver with at most one arrow between any two vertices, counted in both directions, whose underlying
graph is acyclic. If the underlying graph of `W` has a copy in the underlying graph of a quiver `Q`
of finite representation type, then `W` has finite representation type, whatever the directions of
the arrows of `Q` along the copy.

The copy need not be induced, and `Q` may have several arrows, in either direction, over an edge of
the copy: choosing one of them over each edge orients the forest as a subquiver of `Q`, and that
orientation has finite representation type together with `W`. -/
theorem IsFiniteRepType.of_copy_underlyingGraph {Q : Type v} [Quiver.{w} Q] {W : Type v'}
    [Finite W] [p : Quiver.{w'} W] (h : IsFiniteRepType.{u, v, w, max v' w' x} k Q)
    (hsub : ∀ a b : W, Subsingleton ((a ⟶ b) ⊕ (b ⟶ a)))
    (hG : (underlyingGraph W).IsAcyclic) (f : (underlyingGraph W).Copy (underlyingGraph Q)) :
    IsFiniteRepType.{u, v', w', max v' w' x} k W := by
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin W
  -- Both quivers join `a` and `b` by an arrow exactly when they are adjacent in the forest.
  have hiff (a b : W) : Nonempty ((a ⟶ b) ⊕ (b ⟶ a)) ↔
      Nonempty (@Quiver.Hom W (copyQuiver f σ) a b ⊕ @Quiver.Hom W (copyQuiver f σ) b a) := by
    refine Iff.trans ?_ (nonempty_copyQuiver_hom_sum_iff f σ a b).symm
    rw [nonempty_sum, underlyingGraph_adj, iff_and_self]
    rintro (he | he) rfl <;> obtain ⟨e⟩ := he <;>
      exact Sum.inl_ne_inr (Subsingleton.elim (h := hsub a a) (Sum.inl e) (Sum.inr e))
  -- Both have at most one arrow between `a` and `b`, so their arrows correspond.
  refine (isFiniteRepType_iff_of_isAcyclic_underlyingGraph p (copyQuiver f σ) hsub hG fun a b ↦
    ⟨@equivOfSubsingletonOfSubsingleton _ _ (hsub a b) (subsingleton_copyQuiver_hom_sum f σ a b)
      (fun x ↦ ((hiff a b).mp ⟨x⟩).some) fun y ↦ ((hiff a b).mpr ⟨y⟩).some⟩).mp
    (@IsFiniteRepType.of_quiverEmbedding _ _ _ (copyQuiver f σ) _ _ h (copyQuiverEmbedding f σ))

end TauCeti
