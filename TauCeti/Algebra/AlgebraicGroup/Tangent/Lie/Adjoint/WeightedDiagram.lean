/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Exponential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone
public import TauCeti.Algebra.Lie.AdjointAction.Regular
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Uniqueness
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.Principal
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.Lie.Sl2.RangeKer
import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant

/-!
# Classification and finiteness of nilpotent orbits via weighted Dynkin diagrams

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero whose Lie algebra `𝔤 = (𝔪 / 𝔪²)*` has nondegenerate Killing form. Fix a Cartan
subalgebra `𝔥` of `𝔤` and a base `b` of its root system.

Combining dominant-chamber normalization under `Int(𝔤)` with the integration of `Int(𝔤)` into
any closed subgroup with full Lie algebra
(`TauCeti.exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_smul_of_mem_intLieAlgebra`)
and into `G°(k)` (`TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`), every
`sl₂` triple in `𝔤` is conjugate into `RootPairing.Base.dominantNeutralElements b` under any
closed subgroup with full Lie algebra via
`IsSl2Triple.exists_mem_quotientPointsSubgroup_basePointsRepresentation_mem_dominantNeutralElements`
and in particular under `G°(k)`
(`IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements`).
Applying the Jacobson–Morozov theorem therefore carries every nonzero `ad`-nilpotent element of `𝔤`
to the nilpositive element of a dominant `sl₂` triple under any closed subgroup with full Lie
algebra, under `G°(k)`
(`TauCeti.exists_mem_identityComponent_isSl2Triple_basePointsRepresentation_of_isNilpotent_ad`), and
under `G(k)`
(`TauCeti.exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad`). Together with
Malcev–Kostant conjugacy at a shared neutral element
(`IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq`),
every `h ∈ b.dominantNeutralElements` determines a well-defined nonzero rational adjoint orbit
`b.dominantVectorOrbit h` (`RootPairing.Base.dominantVectorOrbit`), exhausting the nonzero
nilpotent `G(k)`-orbits. Consequently `G(k)` has only finitely many nilpotent orbits in `𝔤`
(`TauCeti.Comodule.VectorOrbit.finite_setOf_isNilpotentAd`), with bounds
`3 ^ finrank k 𝔥 - 1` and `3 ^ finrank k 𝔥`
(`TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_and_ne_mk_zero_le`,
`TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_le`), without assuming `G` is connected.

A nonzero `ad`-nilpotent element with minimal centralizer dimension is conjugate to the
nilpositive element of a triple whose dominant neutral element is `2ρ^∨`
(`IsSl2Triple.isCentralizerRegular_e_iff`), and two triples with a shared neutral element are
conjugate. So the regular nilpotent elements form a single `G(k)`-orbit
(`TauCeti.Comodule.VectorOrbit.mk_eq_mk_of_isCentralizerRegular`), again without assuming
connectedness.

When `G` is connected, `O(𝔤)^G = S(𝔤*)^𝔤` (`TauCeti.adjointInvariantPolynomials_eq_lieInvariants`),
so `b.dominantVectorOrbit` is injective (`RootPairing.Base.dominantVectorOrbit_injective`), two
dominant `sl₂` triples have `G(k)`-conjugate nilpositive elements—and identical topological adjoint
orbit images in `P(𝔤 × k)`—if and only if their weighted Dynkin diagrams coincide
(`IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`,
`IsSl2Triple.range_projectiveOrbitMap_adjoint_eq_iff_weightedDynkinDiagram_eq`), and we obtain the
explicit equivalence `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentOrbit`, the
injective invariant `RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram`, the exact nilpotent
orbit counts (`TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_and_ne_mk_zero_eq`,
`TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_eq`), and the identification of the
rational orbits on the nilpotent cone
(`TauCeti.image_vectorOrbit_mk_setOf_nilpotentConeIdeal_le_ker_lift_eval`).

## Main declarations

* `RootPairing.Base.dominantVectorOrbit`, `RootPairing.Base.dominantVectorOrbit_eq_mk`,
  `RootPairing.Base.exists_isSl2Triple_and_dominantVectorOrbit_eq_mk`, and
  `RootPairing.Base.dominantVectorOrbit_eq_mk_iff`: the rational adjoint `G`-orbit attached to a
  dominant neutral element, and its characterization.
* Dominant-chamber conjugacy for `sl₂` triples (closed subgroups with full Lie algebra and
  `G°(k)`):
`IsSl2Triple.exists_mem_quotientPointsSubgroup_basePointsRepresentation_mem_dominantNeutralElements`
  and `IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements`.
* Dominant-chamber conjugacy for nonzero `ad`-nilpotent elements (closed subgroups, `G°(k)`,
  `G(k)`):
`TauCeti.exists_mem_quotientPointsSubgroup_isSl2Triple_basePointsRepresentation_of_isNilpotent_ad`,
  `TauCeti.exists_mem_identityComponent_isSl2Triple_basePointsRepresentation_of_isNilpotent_ad`, and
  `TauCeti.exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad`.
* `TauCeti.Comodule.VectorOrbit.finite_setOf_isNilpotentAd`,
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_and_ne_mk_zero_le` and
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_le`: finiteness and `3 ^ rank` bounds for
  nilpotent `G(k)`-orbits without assuming connectedness.
* `TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd` and
  `TauCeti.Comodule.VectorOrbit.finite_setOf_lt_of_isNilpotentAd`: finiteness of orbits below a
  nilpotent orbit in the closure order, making the decomposition of the `k`-rational vectors
  `{y : 𝔤 | mk y ≤ O}` in
  `TauCeti.Comodule.VectorOrbit.setOf_mk_le_eq_union_biUnion_of_isNilpotentAd`
  a finite union.
* `TauCeti.Comodule.VectorOrbit.mk_eq_mk_of_isCentralizerRegular`: any two regular `ad`-nilpotent
  elements are `G(k)`-conjugate.
* `RootPairing.Base.dominantVectorOrbit_injective`,
  `IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`,
  `IsSl2Triple.range_projectiveOrbitMap_adjoint_eq_iff_weightedDynkinDiagram_eq`,
  `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentOrbit`,
  `RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram`,
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_and_ne_mk_zero_eq`,
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_eq`, and
  `TauCeti.image_vectorOrbit_mk_setOf_nilpotentConeIdeal_le_ker_lift_eval`: complete
  weighted-Dynkin-diagram classification, exact orbit counts, and nilpotent-cone orbit
  identification for connected `G`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Theorems 3.2.10, 3.5.4, and §6.2.
* E. B. Dynkin, *Semisimple subalgebras of semisimple Lie algebras*, Mat. Sb. **30** (1952),
  349–462; Amer. Math. Soc. Transl. (2) **6** (1957), 111–244.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §4.
-/

public section

open CategoryTheory TauCeti WithConv

universe u

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial
attribute [local instance 100] LieRing.ofAssociativeRing

namespace RootPairing.Base

section FiniteType

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

/-- **The rational nilpotent `G`-orbit attached to a dominant neutral element.** Because any two
`sl₂` triples sharing `h` are `C_G(h)`-conjugate (`IsSl2Triple.vectorOrbit_mk_eq`), the rational
orbit of `e` depends only on `h`. -/
noncomputable def dominantVectorOrbit (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (h : b.dominantNeutralElements) :
    Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
  Comodule.VectorOrbit.mk (((b.mem_dominantNeutralElements_iff h.val).mp h.property).1.choose)

/-- For any `sl₂` triple `(h, e, f)` with `h ∈ b.dominantNeutralElements`, `b.dominantVectorOrbit`
is the rational adjoint orbit of `e`. -/
theorem dominantVectorOrbit_eq_mk (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h : b.dominantNeutralElements} {e f : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t : IsSl2Triple (h : Module.Dual k (Bialgebra.CotangentSpace k H)) e f) :
    b.dominantVectorOrbit h = Comodule.VectorOrbit.mk (k := k) (H := H) e := by
  have hex := ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1
  exact hex.choose_spec.choose_spec.vectorOrbit_mk_eq t

/-- Every dominant neutral element `h` belongs to an `sl₂` triple `(h, e, f)` whose nilpositive
element represents `b.dominantVectorOrbit h`. -/
theorem exists_isSl2Triple_and_dominantVectorOrbit_eq_mk
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) :
    ∃ e f : Module.Dual k (Bialgebra.CotangentSpace k H),
      IsSl2Triple (h : Module.Dual k (Bialgebra.CotangentSpace k H)) e f ∧
        b.dominantVectorOrbit h = Comodule.VectorOrbit.mk (k := k) (H := H) e := by
  obtain ⟨e, f, t⟩ := ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1
  exact ⟨e, f, t, b.dominantVectorOrbit_eq_mk t⟩

/-- A vector `x ∈ 𝔤` lies in `b.dominantVectorOrbit h` if and only if some rational point of `G`
conjugates `x` to the nilpositive element of an `sl₂` triple with neutral element `h`. -/
theorem dominantVectorOrbit_eq_mk_iff (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h : b.dominantNeutralElements} {x : Module.Dual k (Bialgebra.CotangentSpace k H)} :
    b.dominantVectorOrbit h = Comodule.VectorOrbit.mk (k := k) (H := H) x ↔
      ∃ g : WithConv (H →ₐ[k] k), ∃ f : Module.Dual k (Bialgebra.CotangentSpace k H),
        IsSl2Triple (h : Module.Dual k (Bialgebra.CotangentSpace k H))
          (Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g x) f := by
  constructor
  · intro horb
    obtain ⟨e, f, t, he⟩ := b.exists_isSl2Triple_and_dominantVectorOrbit_eq_mk h
    rw [he, Comodule.VectorOrbit.mk_eq_mk_iff] at horb
    obtain ⟨g, rfl⟩ := horb
    refine ⟨g⁻¹, f, ?_⟩
    rwa [Representation.inv_self_apply]
  · rintro ⟨g, f', t'⟩
    rw [b.dominantVectorOrbit_eq_mk t', Comodule.VectorOrbit.mk_basePointsRepresentation]

/-- A dominant nilpotent orbit is never the zero orbit. -/
@[simp]
theorem dominantVectorOrbit_ne_mk_zero (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (h : b.dominantNeutralElements) :
    b.dominantVectorOrbit h ≠ Comodule.VectorOrbit.mk (k := k) (H := H) 0 := by
  obtain ⟨e, f, t, he⟩ := b.exists_isSl2Triple_and_dominantVectorOrbit_eq_mk h
  rw [he]
  intro h0
  obtain ⟨g, hg⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp h0.symm
  rw [map_zero] at hg
  exact t.e_ne_zero hg.symm

end FiniteType

end RootPairing.Base

namespace IsSl2Triple

section Subgroup

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : Type u} [CommRing H] [HopfAlgebra k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

/-- **Every `sl₂` triple is conjugate into the dominant chamber by any closed subgroup with full
Lie algebra.** -/
theorem exists_mem_quotientPointsSubgroup_basePointsRepresentation_mem_dominantNeutralElements
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {J : HopfIdeal k H}
    (hJ : J.lieSubalgebra (B := k) = ⊤)
    {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)} (t : IsSl2Triple h e f) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k),
      ∃ h₀ ∈ b.dominantNeutralElements,
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h =
          (h₀ : Module.Dual k (Bialgebra.CotangentSpace k H)) ∧
          IsSl2Triple (h₀ : Module.Dual k (Bialgebra.CotangentSpace k H))
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e)
            (Comodule.basePointsRepresentation
              (Module.Dual k (Bialgebra.CotangentSpace k H)) g f) := by
  let := ratLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))
  obtain ⟨γ, hγ, h₀, hh₀, hγh, t'⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  obtain ⟨g, hg, hgγ⟩ :=
    exists_mem_quotientPointsSubgroup_basePointsRepresentation_eq_smul_of_mem_intLieAlgebra hJ hγ
  refine ⟨g, hg, h₀, hh₀, (hgγ h).trans hγh, ?_⟩
  rwa [hgγ e, hgγ f]

end Subgroup

/-- **Every `sl₂` triple is `G°(k)`-conjugate to one with dominant neutral element.** -/
theorem exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)} (t : IsSl2Triple h e f) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h' ∈ b.dominantNeutralElements,
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h =
            h' ∧
          IsSl2Triple (h' : Module.Dual k (Bialgebra.CotangentSpace k H))
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e)
            (Comodule.basePointsRepresentation
              (Module.Dual k (Bialgebra.CotangentSpace k H)) g f) :=
  t.exists_mem_quotientPointsSubgroup_basePointsRepresentation_mem_dominantNeutralElements b
    (HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top (k := k) (H := H))

end IsSl2Triple

namespace RootPairing.Base

section Surjective

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

/-- **Dominant neutral elements surject onto nonzero nilpotent `G`-orbits.** No connectedness
assumption on `G` is needed: `G⁰(k)` already conjugates every triple into the dominant chamber. -/
theorem range_dominantVectorOrbit (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range b.dominantVectorOrbit =
      {O : Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H)) |
        O.IsNilpotentAd ∧ O ≠ Comodule.VectorOrbit.mk 0} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, rfl⟩
    refine ⟨?_, b.dominantVectorOrbit_ne_mk_zero h⟩
    obtain ⟨e, f, t, he⟩ := b.exists_isSl2Triple_and_dominantVectorOrbit_eq_mk h
    rw [he, Comodule.VectorOrbit.isNilpotentAd_mk_iff]
    exact t.isNilpotent_toEnd_e (K := k) (M := Module.Dual k (Bialgebra.CotangentSpace k H))
  · rintro O ⟨hO, h0⟩
    obtain ⟨e, rfl⟩ := Comodule.VectorOrbit.mk_surjective O
    have he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e) :=
      Comodule.VectorOrbit.isNilpotentAd_mk_iff.mp hO
    have he0 : e ≠ 0 := by rintro rfl; exact h0 rfl
    obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
    obtain ⟨g, -, h₀, hh₀, -, t'⟩ :=
      t.exists_mem_quotientPointsSubgroup_basePointsRepresentation_mem_dominantNeutralElements b
        (J := ⊥) HopfIdeal.lieSubalgebra_bot
    refine ⟨⟨h₀, hh₀⟩, ?_⟩
    rw [b.dominantVectorOrbit_eq_mk t', Comodule.VectorOrbit.mk_basePointsRepresentation]

/-- **All nilpotent `G`-orbits are the zero orbit together with the dominant nilpotent orbits.** -/
theorem insert_mk_zero_range_dominantVectorOrbit (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    insert (Comodule.VectorOrbit.mk (k := k) (H := H) 0) (Set.range b.dominantVectorOrbit) =
      {O : Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H)) |
        O.IsNilpotentAd} := by
  rw [b.range_dominantVectorOrbit]
  ext O
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
  exact ⟨by rintro (rfl | ⟨hO, -⟩); exacts [Comodule.VectorOrbit.isNilpotentAd_mk_zero, hO],
    fun hO ↦ (em (O = Comodule.VectorOrbit.mk 0)).imp_right (⟨hO, ·⟩)⟩

end Surjective

end RootPairing.Base

namespace TauCeti

section Subgroup

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : Type u} [CommRing H] [HopfAlgebra k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **Every nonzero `ad`-nilpotent element is conjugate by any closed subgroup with full Lie
algebra to the nilpositive element of a dominant `sl₂` triple.** -/
theorem exists_mem_quotientPointsSubgroup_isSl2Triple_basePointsRepresentation_of_isNilpotent_ad
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {J : HopfIdeal k H}
    (hJ : J.lieSubalgebra (B := k) = ⊤)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k),
      ∃ h₀ ∈ b.dominantNeutralElements, ∃ f : Module.Dual k (Bialgebra.CotangentSpace k H),
        IsSl2Triple (h₀ : Module.Dual k (Bialgebra.CotangentSpace k H))
          (Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g e) f := by
  obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
  obtain ⟨g, hg, h₀, hh₀, -, t'⟩ :=
    t.exists_mem_quotientPointsSubgroup_basePointsRepresentation_mem_dominantNeutralElements b hJ
  exact ⟨g, hg, h₀, hh₀, _, t'⟩

end Subgroup

section IdentityComponent

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **Every nonzero `ad`-nilpotent element is `G⁰(k)`-conjugate to the nilpositive element of a
dominant `sl₂` triple.** -/
theorem exists_mem_identityComponent_isSl2Triple_basePointsRepresentation_of_isNilpotent_ad
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h₀ ∈ b.dominantNeutralElements, ∃ f : Module.Dual k (Bialgebra.CotangentSpace k H),
        IsSl2Triple (h₀ : Module.Dual k (Bialgebra.CotangentSpace k H))
          (Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g e) f :=
  exists_mem_quotientPointsSubgroup_isSl2Triple_basePointsRepresentation_of_isNilpotent_ad b
    (HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top (k := k) (H := H)) he he0

end IdentityComponent

section Finiteness

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

/-- **Every nonzero `ad`-nilpotent element is `G(k)`-conjugate to the nilpositive element of a
dominant `sl₂` triple.** -/
theorem exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad
    {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {e : 𝔤}
    (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (he0 : e ≠ 0) :
    ∃ (g : WithConv (H →ₐ[k] k)), ∃ h ∈ b.dominantNeutralElements, ∃ f : 𝔤,
      IsSl2Triple (h : 𝔤) (Comodule.basePointsRepresentation 𝔤 g e) f := by
  obtain ⟨g, -, h, hh, f, t⟩ :=
    exists_mem_quotientPointsSubgroup_isSl2Triple_basePointsRepresentation_of_isNilpotent_ad b
      (J := ⊥) HopfIdeal.lieSubalgebra_bot he he0
  exact ⟨g, h, hh, f, t⟩

namespace Comodule.VectorOrbit

/-- **Bound on nonzero nilpotent orbits.** Over an algebraically closed field of characteristic
zero, `G(k)` has at most `3 ^ finrank k 𝔥 - 1` nonzero nilpotent adjoint orbits in `𝔤`, for any
Cartan subalgebra `𝔥` of `𝔤`. No connectedness hypothesis on `G` is needed. -/
theorem ncard_setOf_isNilpotentAd_and_ne_mk_zero_le (𝔥 : LieSubalgebra k 𝔤)
    [𝔥.IsCartanSubalgebra] :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0}.ncard ≤ 3 ^ Module.finrank k 𝔥 - 1 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  have hle : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0}.ncard ≤
      b.dominantNeutralElements.ncard := by
    rw [← b.range_dominantVectorOrbit, ← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    rw [Set.ncard_univ, Nat.card_coe_set_eq]
  have hbound := b.ncard_dominantNeutralElements_add_one_le
  omega

/-- **Finiteness of nilpotent orbits.** Over an algebraically closed field of characteristic zero,
an affine group of finite type whose Lie algebra has nondegenerate Killing form has only finitely
many nilpotent rational adjoint orbits. No connectedness hypothesis is needed. -/
theorem finite_setOf_isNilpotentAd : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.Finite := by
  obtain ⟨x, _⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k 𝔤
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  rw [← b.insert_mk_zero_range_dominantVectorOrbit]
  exact (Set.finite_range _).insert _

/-- The subtype of nilpotent rational adjoint orbits is finite. -/
instance : Finite {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  finite_setOf_isNilpotentAd.to_subtype

/-- **Bound on all nilpotent orbits.** Including the zero orbit, `G(k)` has at most
`3 ^ finrank k 𝔥` nilpotent adjoint orbits in `𝔤`. -/
theorem ncard_setOf_isNilpotentAd_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  have heq : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd} =
      insert (mk 0) {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0} := by
    ext O
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    exact ⟨fun hO ↦ (em (O = mk 0)).imp_right (⟨hO, ·⟩),
      by rintro (rfl | ⟨hO, -⟩); exacts [isNilpotentAd_mk_zero, hO]⟩
  have hpos : 1 ≤ 3 ^ Module.finrank k 𝔥 := Nat.one_le_pow _ _ (by decide)
  have h1 := ncard_setOf_isNilpotentAd_and_ne_mk_zero_le (H := H) 𝔥
  have h2 := Set.ncard_insert_le (mk (0 : 𝔤)) {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0}
  rw [heq]
  omega

/-- **A nilpotent orbit closure contains only finitely many orbits.** No connectedness hypothesis
on `G` is needed. -/
theorem finite_setOf_le_of_isNilpotentAd {O : VectorOrbit k H 𝔤} (hO : O.IsNilpotentAd) :
    {O' : VectorOrbit k H 𝔤 | O' ≤ O}.Finite :=
  finite_setOf_isNilpotentAd.subset fun _ hle ↦ hO.of_le hle

/-- **A nilpotent orbit boundary contains only finitely many orbits.** No connectedness hypothesis
on `G` is needed. -/
theorem finite_setOf_lt_of_isNilpotentAd {O : VectorOrbit k H 𝔤} (hO : O.IsNilpotentAd) :
    {O' : VectorOrbit k H 𝔤 | O' < O}.Finite :=
  (finite_setOf_le_of_isNilpotentAd hO).subset fun (_ : VectorOrbit k H 𝔤) (hlt : _ < O) ↦
    hlt.le

/-- **The regular nilpotent orbit is unique.** Over an algebraically closed field of characteristic
zero, two `ad`-nilpotent elements of `𝔤` with minimal centralizer dimension lie in the same
`G(k)`-orbit. No connectedness hypothesis on `G` is needed. -/
theorem mk_eq_mk_of_isCentralizerRegular {e₁ e₂ : 𝔤} (he₁ : IsNilpotent (LieAlgebra.ad k 𝔤 e₁))
    (he₂ : IsNilpotent (LieAlgebra.ad k 𝔤 e₂)) (hr₁ : LieAlgebra.IsCentralizerRegular k e₁)
    (hr₂ : LieAlgebra.IsCentralizerRegular k e₂) :
    (mk e₁ : VectorOrbit k H 𝔤) = mk e₂ := by
  obtain ⟨𝔥, _, ⟨b⟩⟩ := exists_isCartanSubalgebra_base k 𝔤
  -- if `0` is regular then `𝔤` is abelian, hence zero since its Killing form is nondegenerate
  by_cases h0 : e₁ = 0 ∨ e₂ = 0
  · have : IsLieAbelian 𝔤 := by
      rcases h0 with rfl | rfl
      exacts [LieAlgebra.isCentralizerRegular_zero_iff.mp hr₁,
        LieAlgebra.isCentralizerRegular_zero_iff.mp hr₂]
    have := LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian (R := k) (L := 𝔤)
    rw [Subsingleton.elim e₁ e₂]
  -- a nonzero regular nilpotent element is conjugate to a principal nilpositive element
  have key {e : 𝔤} (he : IsNilpotent (LieAlgebra.ad k 𝔤 e))
      (hr : LieAlgebra.IsCentralizerRegular k e) (he0 : e ≠ 0) :
      ∃ (g : WithConv (H →ₐ[k] k)) (f : 𝔤), IsSl2Triple
        ((twoWeylVector (LieAlgebra.IsKilling.rootSystem 𝔥).flip b.flip : 𝔥) : 𝔤)
        (basePointsRepresentation 𝔤 g e) f := by
    obtain ⟨g, h, hh, f, t⟩ :=
      exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad b he he0
    have hr' : LieAlgebra.IsCentralizerRegular k (basePointsRepresentation 𝔤 g e) := by
      rwa [← Derivation.basePointsAdjointLieEquiv_apply, LieEquiv.isCentralizerRegular_apply_iff]
    obtain rfl :=
      (t.isCentralizerRegular_e_iff ((b.mem_dominantNeutralElements_iff h).mp hh).2).mp hr'
    exact ⟨g, f, t⟩
  push Not at h0
  obtain ⟨g₁, f₁, t₁⟩ := key he₁ hr₁ h0.1
  obtain ⟨g₂, f₂, t₂⟩ := key he₂ hr₂ h0.2
  obtain ⟨g, -, -, hge, -⟩ :=
    t₁.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t₂
  rw [← mk_basePointsRepresentation g₁ e₁, ← mk_basePointsRepresentation g₂ e₂, ← hge]
  exact mk_eq_mk_iff.mpr ⟨g, rfl⟩

end Comodule.VectorOrbit

end Finiteness

end TauCeti

section Connected

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

namespace IsSl2Triple

/-- **Uniqueness of dominant neutral elements under `G(k)`-conjugacy for connected `G`.** -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤}
    (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : WithConv (H →ₐ[k] k)} (hge : Comodule.basePointsRepresentation 𝔤 g e₁ = e₂) :
    h₁ = h₂ :=
  t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂
    (Derivation.basePointsAdjointLieEquiv g)
    (by rwa [Derivation.basePointsAdjointLieEquiv_apply]) fun _ hp z ↦ by
      rw [Derivation.basePointsAdjointLieEquiv_apply]
      exact lift_eval_basePointsRepresentation_of_mem_lieInvariants hp g z

/-- **Classification of nilpositive elements by weighted Dynkin diagrams.** For a connected affine
group `G` over an algebraically closed field of characteristic zero with Killing Lie algebra `𝔤`,
two `sl₂` triples `(h₁, e₁, f₁)` and `(h₂, e₂, f₂)` with dominant neutral elements in the same Weyl
chamber have `G(k)`-conjugate nilpositive elements if and only if their weighted Dynkin diagrams
coincide. -/
theorem exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤}
    (t₁ : IsSl2Triple (h₁ : 𝔤) e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements) :
    (∃ g : WithConv (H →ₐ[k] k), Comodule.basePointsRepresentation 𝔤 g e₁ = e₂) ↔
      b.weightedDynkinDiagram ⟨h₁, hh₁⟩ = b.weightedDynkinDiagram ⟨h₂, hh₂⟩ := by
  constructor
  · rintro ⟨g, hge⟩
    congr 1
    exact Subtype.ext
      (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq b t₂ hh₁ hh₂ hge)
  · intro hdiag
    obtain ⟨g, -, -, hge, -⟩ :=
      t₁.exists_mem_quotientPointsSubgroup_identityComponent_of_weightedDynkinDiagram_eq
        (H := FiniteTypeCommHopfAlgCat.of k H) (h₁ := ⟨h₁, hh₁⟩) (h₂ := ⟨h₂, hh₂⟩) t₂ hdiag
    exact ⟨g, hge⟩

/-- **Geometric adjoint orbit classification by weighted Dynkin diagrams.** For a connected Killing
affine group `G`, two `sl₂` triples with dominant neutral elements have identical topological
adjoint `G`-orbit images in `P(𝔤 × k)` (including nonclosed points) if and only if their weighted
Dynkin diagrams coincide. -/
theorem range_projectiveOrbitMap_adjoint_eq_iff_weightedDynkinDiagram_eq
    {b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base} {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t₁ : IsSl2Triple (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₂ f₂) :
    Set.range (Comodule.projectiveOrbitMap (H := H)
        ((e₁, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one e₁)) =
      Set.range (Comodule.projectiveOrbitMap (H := H)
        ((e₂, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one e₂)) ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ := by
  rw [← Comodule.VectorOrbit.image_mk, ← Comodule.VectorOrbit.image_mk,
    Comodule.VectorOrbit.image_injective.eq_iff, Comodule.VectorOrbit.mk_eq_mk_iff]
  exact t₁.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq b t₂
    h₁.property h₂.property

end IsSl2Triple

namespace RootPairing.Base

/-- **Distinct dominant neutral elements give distinct nilpotent `G`-orbits when `G` is
connected.** -/
theorem dominantVectorOrbit_injective (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective b.dominantVectorOrbit := by
  intro h₁ h₂ horb
  obtain ⟨e₁, f₁, t₁, he₁⟩ := b.exists_isSl2Triple_and_dominantVectorOrbit_eq_mk h₁
  obtain ⟨e₂, f₂, t₂, he₂⟩ := b.exists_isSl2Triple_and_dominantVectorOrbit_eq_mk h₂
  rw [he₁, he₂] at horb
  obtain ⟨g, hge⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp horb
  exact Subtype.ext
    (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq b t₂
      h₁.property h₂.property hge)

/-- Distinct dominant neutral elements determine distinct rational nilpotent `G`-orbits when `G` is
connected. -/
@[simp]
theorem dominantVectorOrbit_inj (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h₁ h₂ : b.dominantNeutralElements} :
    b.dominantVectorOrbit h₁ = b.dominantVectorOrbit h₂ ↔ h₁ = h₂ :=
  b.dominantVectorOrbit_injective.eq_iff

/-- **Every nonzero nilpotent element of a connected Killing group lies in the orbit of a unique
dominant neutral element.** -/
theorem existsUnique_dominantVectorOrbit_eq_of_isNilpotent_ad
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃! h : b.dominantNeutralElements,
      b.dominantVectorOrbit h = Comodule.VectorOrbit.mk (k := k) (H := H) e := by
  rw [b.dominantVectorOrbit_injective.existsUnique_iff_exists, ← Set.mem_range,
    b.range_dominantVectorOrbit]
  exact ⟨Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr he,
    mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mp he0⟩

/-- Auxiliary map sending `none` to the zero nilpotent orbit and `some h` to
`b.dominantVectorOrbit h`. -/
private noncomputable def optionDominantToNilpotentOrbit
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Option b.dominantNeutralElements → {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}
  | none => ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩
  | some h =>
    ⟨b.dominantVectorOrbit h, by
      obtain ⟨e, f, t, he⟩ := b.exists_isSl2Triple_and_dominantVectorOrbit_eq_mk (H := H) h
      rw [he, Comodule.VectorOrbit.isNilpotentAd_mk_iff]
      exact t.isNilpotent_toEnd_e (K := k) (M := 𝔤)⟩

private theorem optionDominantToNilpotentOrbit_bijective
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Bijective (b.optionDominantToNilpotentOrbit (H := H)) := by
  constructor
  · rintro (_ | h₁) (_ | h₂) heq
    · rfl
    · exact absurd (congrArg Subtype.val heq).symm (b.dominantVectorOrbit_ne_mk_zero (H := H) h₂)
    · exact absurd (congrArg Subtype.val heq) (b.dominantVectorOrbit_ne_mk_zero (H := H) h₁)
    · exact congrArg some (b.dominantVectorOrbit_injective (H := H) (congrArg Subtype.val heq))
  · rintro ⟨O, hO⟩
    by_cases h0 : O = Comodule.VectorOrbit.mk 0
    · exact ⟨none, Subtype.ext h0.symm⟩
    · have hmem : O ∈ Set.range (b.dominantVectorOrbit (H := H)) := by
        rw [b.range_dominantVectorOrbit]
        exact ⟨hO, h0⟩
      obtain ⟨h, hh⟩ := hmem
      exact ⟨some h, Subtype.ext hh⟩

/-- **Bijection between `Option b.dominantNeutralElements` and nilpotent orbits.** For connected
`G`, `none` corresponds to the zero orbit and `some h` corresponds to the nilpotent `G(k)`-orbit of
any nilpositive partner of `h`. -/
noncomputable def optionDominantNeutralElementsEquivNilpotentOrbit
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Option b.dominantNeutralElements ≃ {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  Equiv.ofBijective (b.optionDominantToNilpotentOrbit (H := H))
    (b.optionDominantToNilpotentOrbit_bijective (H := H))

/-- `none` maps to the zero nilpotent orbit. -/
@[simp]
theorem optionDominantNeutralElementsEquivNilpotentOrbit_none
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H) none =
      ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩ := by
  simp [optionDominantNeutralElementsEquivNilpotentOrbit, optionDominantToNilpotentOrbit]

/-- `some h` maps to the nilpotent orbit of any nilpositive partner `e` of `(h : 𝔤)`. -/
theorem optionDominantNeutralElementsEquivNilpotentOrbit_some_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) {e f : 𝔤}
    (t : IsSl2Triple (h : 𝔤) e f) :
    b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H) (some h) =
      ⟨Comodule.VectorOrbit.mk e,
        Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr
          (t.isNilpotent_toEnd_e (K := k) (M := 𝔤))⟩ := by
  apply Subtype.ext
  simpa [optionDominantNeutralElementsEquivNilpotentOrbit, optionDominantToNilpotentOrbit] using
    b.dominantVectorOrbit_eq_mk (H := H) t

/-- The inverse equivalence sends the zero nilpotent orbit to `none`. -/
@[simp]
theorem optionDominantNeutralElementsEquivNilpotentOrbit_symm_mk_zero
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm
        ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩ = none :=
  (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm_apply_eq.mpr
    (b.optionDominantNeutralElementsEquivNilpotentOrbit_none (H := H)).symm

/-- The inverse equivalence sends the orbit of the nilpositive element of a dominant `sl₂` triple
`(h, e, f)` to `some ⟨h, hh⟩`. -/
theorem optionDominantNeutralElementsEquivNilpotentOrbit_symm_mk_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h : 𝔥} {e f : 𝔤}
    (t : IsSl2Triple (h : 𝔤) e f) (hh : h ∈ b.dominantNeutralElements) :
    (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm
        ⟨Comodule.VectorOrbit.mk e,
          Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr
            (t.isNilpotent_toEnd_e (K := k) (M := 𝔤))⟩ = some ⟨h, hh⟩ :=
  (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm_apply_eq.mpr
    (b.optionDominantNeutralElementsEquivNilpotentOrbit_some_of_isSl2Triple
      (H := H) ⟨h, hh⟩ t).symm

/-- **The weighted Dynkin diagram of a nilpotent orbit.** Sends the zero orbit to the all-zero
diagram `0 : b.support → Fin 3` and every nonzero nilpotent orbit to the `{0, 1, 2}` simple-root
labeling of its unique dominant neutral element. -/
noncomputable def nilpotentOrbitWeightedDynkinDiagram
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (O : {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    b.support → Fin 3 :=
  ((b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm O).elim 0
    b.weightedDynkinDiagram

/-- Unfolding lemma for `RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram`. -/
theorem nilpotentOrbitWeightedDynkinDiagram_def
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (O : {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H) O =
      ((b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm O).elim 0
        b.weightedDynkinDiagram :=
  (rfl)

/-- The weighted Dynkin diagram of the orbit indexed by `x : Option b.dominantNeutralElements` is
`0` for `none` and `b.weightedDynkinDiagram h` for `some h`. -/
@[simp]
theorem nilpotentOrbitWeightedDynkinDiagram_optionDominantNeutralElementsEquivNilpotentOrbit
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (x : Option b.dominantNeutralElements) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H)
        (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H) x) =
      x.elim 0 b.weightedDynkinDiagram := by
  simp [nilpotentOrbitWeightedDynkinDiagram_def]

/-- The zero nilpotent orbit has the all-zero weighted Dynkin diagram `0`. -/
@[simp]
theorem nilpotentOrbitWeightedDynkinDiagram_mk_zero
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H)
        ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩ = 0 := by
  simp [nilpotentOrbitWeightedDynkinDiagram_def]

/-- On the orbit of the nilpositive element of a dominant `sl₂` triple `(h, e, f)`, the orbit-level
weighted Dynkin diagram is `b.weightedDynkinDiagram ⟨h, hh⟩`. -/
theorem nilpotentOrbitWeightedDynkinDiagram_mk_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h : 𝔥} {e f : 𝔤}
    (t : IsSl2Triple (h : 𝔤) e f) (hh : h ∈ b.dominantNeutralElements) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H)
        ⟨Comodule.VectorOrbit.mk e,
          Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr
            (t.isNilpotent_toEnd_e (K := k) (M := 𝔤))⟩ =
      b.weightedDynkinDiagram ⟨h, hh⟩ := by
  rw [nilpotentOrbitWeightedDynkinDiagram_def,
    b.optionDominantNeutralElementsEquivNilpotentOrbit_symm_mk_of_isSl2Triple (H := H) t hh]
  rfl

/-- **Weighted Dynkin diagrams classify nilpotent orbits of a connected group.** -/
theorem nilpotentOrbitWeightedDynkinDiagram_injective
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective (b.nilpotentOrbitWeightedDynkinDiagram (H := H)) := by
  have hcomp : b.nilpotentOrbitWeightedDynkinDiagram (H := H) =
      (fun x : Option b.dominantNeutralElements ↦ x.elim 0 b.weightedDynkinDiagram) ∘
        (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm :=
    funext (b.nilpotentOrbitWeightedDynkinDiagram_def (H := H))
  rw [hcomp]
  refine Function.Injective.comp ?_
    (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm.injective
  rintro (_ | h₁) (_ | h₂) h
  · rfl
  · exact absurd h.symm (b.weightedDynkinDiagram_ne_zero h₂)
  · exact absurd h (b.weightedDynkinDiagram_ne_zero h₁)
  · exact congrArg some (b.weightedDynkinDiagram_injective h)

/-- Two nilpotent orbits have the same weighted Dynkin diagram if and only if they are equal. -/
@[simp]
theorem nilpotentOrbitWeightedDynkinDiagram_eq_iff
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (O₁ O₂ : {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H) O₁ =
        b.nilpotentOrbitWeightedDynkinDiagram (H := H) O₂ ↔ O₁ = O₂ :=
  (b.nilpotentOrbitWeightedDynkinDiagram_injective (H := H)).eq_iff

/-- A nilpotent orbit has the all-zero weighted Dynkin diagram if and only if it is the zero orbit.
-/
@[simp]
theorem nilpotentOrbitWeightedDynkinDiagram_eq_zero_iff
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (O : {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    b.nilpotentOrbitWeightedDynkinDiagram (H := H) O = 0 ↔
      O = ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩ := by
  rw [← b.nilpotentOrbitWeightedDynkinDiagram_mk_zero (H := H),
    b.nilpotentOrbitWeightedDynkinDiagram_eq_iff]

end RootPairing.Base

namespace TauCeti.Comodule.VectorOrbit

/-- **Exact count of nonzero nilpotent `G`-orbits for a connected Killing group.** -/
theorem ncard_setOf_isNilpotentAd_and_ne_mk_zero_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0}.ncard =
      b.dominantNeutralElements.ncard := by
  rw [← b.range_dominantVectorOrbit,
    Set.ncard_range_of_injective b.dominantVectorOrbit_injective, Nat.card_coe_set_eq]

/-- **Exact count of nilpotent `G`-orbits for a connected Killing group.** Together with the zero
orbit, the nilpotent `G`-orbits are in bijection with `Option b.dominantNeutralElements`. -/
theorem ncard_setOf_isNilpotentAd_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.ncard =
      b.dominantNeutralElements.ncard + 1 := by
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H))).symm.trans
    (by rw [Finite.card_option, Nat.card_coe_set_eq])

end TauCeti.Comodule.VectorOrbit

end Connected

namespace TauCeti

section NilpotentCone

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  (H : Type u) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **Rational `G`-orbits on the nilpotent cone.** For a connected Killing group, the rational
orbits of `k`-points of the nilpotent cone are the nilpotent `G`-orbits. -/
theorem image_vectorOrbit_mk_setOf_nilpotentConeIdeal_le_ker_lift_eval :
    Comodule.VectorOrbit.mk (k := k) (H := H) ''
        {x : Module.Dual k (Bialgebra.CotangentSpace k H) |
          nilpotentConeIdeal k H ≤
            RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k _ x))} =
      {O : Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H)) |
        O.IsNilpotentAd} := by
  rw [← Set.image_preimage_eq
    {O : Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H)) | O.IsNilpotentAd}
    Comodule.VectorOrbit.mk_surjective]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Comodule.VectorOrbit.isNilpotentAd_mk_iff]
  exact nilpotentConeIdeal_le_ker_lift_eval_iff (H := FiniteTypeCommHopfAlgCat.of k H)

end NilpotentCone

end TauCeti
