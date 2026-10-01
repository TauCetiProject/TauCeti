/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Finitely generated adic rings are Huber rings

Let `A` be a commutative topological ring whose topology is `I`-adic.  If `I` is finitely
generated, then `(A, I)` is a pair of definition: the ring of definition is all of `A`, and the
ideal of definition is `I`, transported to the top subring.  Consequently `A` is a Huber ring.
Such a ring is a Tate ring only in the degenerate case `I = ⊤`: a power of a topologically
nilpotent element lies in `I`.

This is the bridge from algebraic adic completeness to Huber theory.  In particular, Mathlib's
`IsAdic.isAdicComplete_iff` can be applied to an adically complete ring equipped with its adic
topology, while `isHuberRing_adicTopology` supplies its Huber structure.  The construction is used
for Witt-vector rings with their `(p, [ϖ])`-adic topology.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.adic`: the pair of definition `(A, I)` associated to a finitely
  generated ideal defining the topology.

## Main results

* `TauCeti.Huber.PairOfDefinition.adic_extendedIdealOfDefinition`: the ideal of definition of this
  pair, extended to `A`, is `I`.
* `TauCeti.Huber.PairOfDefinition.adic_idealImage`: the neighbourhood subgroup furnished by this
  pair in degree `n` is exactly `I ^ n`.
* `TauCeti.Huber.isHuberRing_of_isAdic`: a ring with a finitely generated ideal defining its
  topology is Huber.
* `TauCeti.Huber.isHuberRing_adicTopology`: a commutative ring equipped with the adic topology of
  a finitely generated ideal is Huber.
* `TauCeti.Huber.IsTateRing.eq_top_of_isAdic` and `TauCeti.Huber.isTateRing_iff_eq_top_of_isAdic`:
  an adic ring is Tate only in the degenerate case `I = ⊤`, where the topology is indiscrete.
  So `ℤ_[p]` and `W(𝒪_F)` with its `(p, [ϖ])`-adic topology are Huber rings that are not Tate.

## References

* T. Wedhorn, *Adic Spaces*, the definition of an f-adic ring in §6.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-- The pair of definition `(A, I)` attached to a finitely generated ideal `I` defining the
topology of `A`.

The ideal is transported to the top subring because a `PairOfDefinition` stores its ideal in its
ring of definition, even when that ring of definition is all of `A`. -/
noncomputable def adic (I : Ideal A) (hI : IsAdic I) (hfg : I.FG) : PairOfDefinition A where
  ringOfDefinition := ⊤
  isOpen_ringOfDefinition := by simp
  idealOfDefinition := I.comap (Subring.topEquiv : (⊤ : Subring A) ≃+* A)
  fg_idealOfDefinition := by
    rw [← Ideal.map_symm]
    exact hfg.map (Subring.topEquiv : (⊤ : Subring A) ≃+* A).symm.toRingHom
  isAdic_idealOfDefinition := by
    -- An adic topology is a ring topology, so `IsAdic.comap` applies without assuming it.
    have : IsTopologicalRing A := hI ▸ I.nonarchimedean.toIsTopologicalRing
    exact IsAdic.comap _ Topology.IsInducing.subtypeVal hI

@[simp]
theorem adic_ringOfDefinition (I : Ideal A) (hI : IsAdic I) (hfg : I.FG) :
    (adic I hI hfg).ringOfDefinition = ⊤ :=
  (rfl)

/-- Membership in the ideal of definition of `adic I hI hfg` is membership in `I`. -/
@[simp]
theorem mem_adic_idealOfDefinition (I : Ideal A) (hI : IsAdic I) (hfg : I.FG)
    {x : (adic I hI hfg).ringOfDefinition} :
    x ∈ (adic I hI hfg).idealOfDefinition ↔ (x : A) ∈ I :=
  Ideal.mem_comap

/-- The ring of definition of `adic I hI hfg` is all of `A`, so its inclusion is surjective. -/
private theorem surjective_subtype_adic (I : Ideal A) (hI : IsAdic I) (hfg : I.FG) :
    Function.Surjective (adic I hI hfg).ringOfDefinition.subtype :=
  fun x ↦ ⟨⟨x, Subring.mem_top x⟩, rfl⟩

/-- The ideal of definition of `adic I hI hfg`, extended to `A`, is `I`. -/
@[simp]
theorem adic_extendedIdealOfDefinition (I : Ideal A) (hI : IsAdic I) (hfg : I.FG) :
    (adic I hI hfg).extendedIdealOfDefinition = I := by
  have hideal : (adic I hI hfg).idealOfDefinition =
      I.comap (adic I hI hfg).ringOfDefinition.subtype := by
    ext x
    exact mem_adic_idealOfDefinition I hI hfg
  rw [extendedIdealOfDefinition_def, hideal]
  exact Ideal.map_comap_of_surjective _ (surjective_subtype_adic I hI hfg) I

/-- The `n`-th neighbourhood subgroup supplied by the adic pair is `I ^ n` itself. -/
@[simp]
theorem adic_idealImage (I : Ideal A) (hI : IsAdic I) (hfg : I.FG) (n : ℕ) :
    (adic I hI hfg).idealImage n = (I ^ n).toAddSubgroup := by
  ext x
  let P := adic I hI hfg
  have hsurj : Function.Surjective P.ringOfDefinition.subtype := surjective_subtype_adic I hI hfg
  rw [P.mem_idealImage]
  calc
    (∃ y ∈ P.idealOfDefinition ^ n, (y : A) = x) ↔
        x ∈ (P.idealOfDefinition ^ n).map P.ringOfDefinition.subtype := by
      simpa using (Ideal.mem_map_iff_of_surjective _ hsurj).symm
    _ ↔ x ∈ I ^ n := by
      rw [Ideal.map_pow, ← extendedIdealOfDefinition_def, adic_extendedIdealOfDefinition]
    _ ↔ x ∈ (I ^ n).toAddSubgroup := Iff.rfl

end PairOfDefinition

variable [IsTopologicalRing A]

/-- A commutative topological ring is Huber when its topology is defined by a finitely generated
ideal. -/
theorem isHuberRing_of_isAdic (I : Ideal A) (hI : IsAdic I) (hfg : I.FG) : IsHuberRing A :=
  ⟨⟨PairOfDefinition.adic I hI hfg⟩⟩

/-- A commutative ring equipped with the adic topology of a finitely generated ideal is a Huber
ring.  This form lets callers install the topology and Huber structure together without first
naming the tautological proof `IsAdic I`. -/
theorem isHuberRing_adicTopology {A : Type*} [CommRing A] (I : Ideal A) (hfg : I.FG) :
    letI := I.adicTopology
    IsHuberRing A := by
  let _ := I.adicTopology
  exact isHuberRing_of_isAdic I rfl hfg

/-- **An adic ring is Tate only for the unit ideal.** If the topology of `A` is `I`-adic and `A`
has a pseudouniformiser `a`, then some power of `a` lies in the open ideal `I`, and that power is a
unit. -/
theorem IsTateRing.eq_top_of_isAdic [IsTateRing A] {I : Ideal A} (hI : IsAdic I) : I = ⊤ := by
  obtain ⟨a, ha⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  rw [← Ideal.radical_eq_top]
  exact Ideal.eq_top_of_isUnit_mem _ (hI.isTopologicallyNilpotent_iff_mem_radical.mp
    ha.isTopologicallyNilpotent) ha.isUnit

/-- **A finitely generated adic ring is Tate exactly when its ideal is the unit ideal.** For
`I = ⊤` the topology is indiscrete and `1` is a pseudouniformiser; otherwise
`TauCeti.Huber.IsTateRing.eq_top_of_isAdic` applies. -/
theorem isTateRing_iff_eq_top_of_isAdic {I : Ideal A} (hI : IsAdic I) (hfg : I.FG) :
    IsTateRing A ↔ I = ⊤ := by
  refine ⟨fun _ ↦ IsTateRing.eq_top_of_isAdic hI, fun h ↦ ?_⟩
  have := isHuberRing_of_isAdic I hI hfg
  refine ⟨⟨1, isPseudoUniformizer_iff.mpr ⟨isUnit_one, ?_⟩⟩⟩
  rw [hI.isTopologicallyNilpotent_iff_mem_radical, h, Ideal.radical_top]
  exact Submodule.mem_top

end TauCeti.Huber
