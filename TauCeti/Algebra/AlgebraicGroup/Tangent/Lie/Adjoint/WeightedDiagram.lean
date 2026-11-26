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
import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.Principal
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.Lie.Sl2.RangeKer

/-!
# Classification and finiteness of nilpotent orbits via weighted Dynkin diagrams

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero whose Lie algebra `𝔤 = (𝔪 / 𝔪²)*` has nondegenerate Killing form. Fix a Cartan
subalgebra `𝔥` of `𝔤` and a base `b` of its root system.

Combining dominant-chamber normalization under `Int(𝔤)` with the integration of `Int(𝔤)` into
`G°(k)` (`TauCeti.intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent`), every `sl₂`
triple in `𝔤` is `G°(k)`-conjugate to one whose neutral element lies in
`RootPairing.Base.dominantNeutralElements b`
(`IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements`).
Applying the Jacobson–Morozov theorem therefore carries every nonzero `ad`-nilpotent element of `𝔤`
by `G(k)` to the nilpositive element of a dominant `sl₂` triple
(`TauCeti.exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad`). Together with
Malcev–Kostant conjugacy at a shared neutral element
(`IsSl2Triple.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq`),
the nonzero nilpotent `G(k)`-orbits are exhausted by `b.dominantNeutralElements`. Since every
dominant neutral element has a nonzero weighted Dynkin diagram
(`RootPairing.Base.weightedDynkinDiagram_ne_zero`), `G(k)` has only finitely many nilpotent orbits
in `𝔤` (`TauCeti.Comodule.VectorOrbit.finite_setOf_isNilpotentAd`), at most `3 ^ finrank k 𝔥 - 1`
nonzero ones (`TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_and_ne_mk_zero_le`) and at
most `3 ^ finrank k 𝔥` in total (`TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_le`),
without assuming `G` is connected. In particular, for any nilpotent orbit `O`, only finitely many
orbits lie below `O` in the closure order
(`TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd`,
`TauCeti.Comodule.VectorOrbit.finite_setOf_lt_of_isNilpotentAd`).

A nonzero `ad`-nilpotent element with minimal centralizer dimension is conjugate to the
nilpositive element of a triple whose dominant neutral element is `2ρ^∨`
(`IsSl2Triple.isCentralizerRegular_e_iff`), and two triples with a shared neutral element are
conjugate. So the regular nilpotent elements form a single `G(k)`-orbit
(`TauCeti.Comodule.VectorOrbit.mk_eq_mk_of_isCentralizerRegular`), again without assuming
connectedness.

When `G` is connected, `O(𝔤)^G = S(𝔤*)^𝔤` (`TauCeti.adjointInvariantPolynomials_eq_lieInvariants`),
so two dominant `sl₂` triples have `G(k)`-conjugate nilpositive elements if and only if their
weighted Dynkin diagrams coincide
(`IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`). This gives an
explicit equivalence `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentOrbit` between
`Option b.dominantNeutralElements` and the subtype of nilpotent `G(k)`-orbits, and an injective
orbit-level weighted Dynkin diagram invariant
`RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram` valued in `b.support → Fin 3`, assigning the
all-zero diagram `0` to the zero orbit and `b.weightedDynkinDiagram h` to each nonzero orbit.

For any `sl₂` triple `(h, e, f)`, every nonzero scalar multiple of the nilpositive element `e` lies
in its rational `G(k)`-orbit (`IsSl2Triple.mk_smul_eq`), placing the zero orbit in the closure of
every nilpotent orbit (`TauCeti.Comodule.VectorOrbit.IsNilpotentAd.mk_zero_le`). In addition,
`TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd` supplies the lower-set finiteness
hypothesis needed to apply the generic representation orbit-closure and boundary decompositions
`TauCeti.Comodule.VectorOrbit.closure_image_inter_basicOpen_snd_eq_biUnion` and
`TauCeti.Comodule.VectorOrbit.closure_image_sdiff_image_inter_basicOpen_snd_eq_biUnion`.

Finally, when `𝔤` is reductive (`[LieAlgebra.HasCentralRadical k 𝔤]`), `⁅𝔤, 𝔤⁆` has nondegenerate
Killing form (`TauCeti.isKilling_derivedSeries`) and `Int(⁅𝔤, 𝔤⁆)` integrates on `⁅𝔤, 𝔤⁆` into
`G°(k)` (`TauCeti.exists_mem_quotientPointsSubgroup_forall_derivedSeries_eq_of_mem_intLieAlgebra`).
Exhaustion by dominant `sl₂` triples in `⁅𝔤, 𝔤⁆` gives finiteness and `3 ^ finrank k 𝔥` bounds on
the `G(k)`-orbits of `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆` (and hence, for connected `G`, on
`TauCeti.nilpotentConeOrbits k H` together with lower-set finiteness
`TauCeti.finite_setOf_le_of_mem_nilpotentConeOrbits`). Pulling Lie invariants on `⁅𝔤, 𝔤⁆` back
along `TauCeti.derivedSeriesLieProj k 𝔤` then establishes uniqueness of the dominant neutral
element under `G(k)`-conjugacy
(`IsSl2Triple.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_coe_eq`), yielding the
bijection `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentConeOrbits`, the exact count
`RootPairing.Base.ncard_nilpotentConeOrbits_eq`, and the injective weighted Dynkin diagram
invariant `RootPairing.Base.nilpotentConeOrbitWeightedDynkinDiagram` for any Cartan subalgebra `𝔥`
of `⁅𝔤, 𝔤⁆`.

## Main declarations

* `IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements`: every
  `sl₂` triple is `G°(k)`-conjugate to one with dominant neutral element.
* `IsSl2Triple.mk_smul_eq`, `TauCeti.Comodule.VectorOrbit.mk_smul_eq_of_isNilpotent_ad`, and
  `TauCeti.Comodule.VectorOrbit.IsNilpotentAd.mk_zero_le`: scaling invariance of nilpotent orbits
  and minimality of the zero orbit in the closure order.
* `TauCeti.exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad`: every nonzero
  `ad`-nilpotent element is `G(k)`-conjugate to the nilpositive element of a dominant `sl₂` triple.
* `TauCeti.Comodule.VectorOrbit.finite_setOf_isNilpotentAd`,
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_and_ne_mk_zero_le`, and
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_le`: finiteness and `3 ^ rank` bounds for
  nilpotent `G(k)`-orbits without assuming connectedness.
* `TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd` and
  `TauCeti.Comodule.VectorOrbit.finite_setOf_lt_of_isNilpotentAd`: finiteness of orbits below a
  nilpotent orbit in the closure order.
* `TauCeti.Comodule.VectorOrbit.mk_eq_mk_of_isCentralizerRegular`: any two regular `ad`-nilpotent
  elements are `G(k)`-conjugate.
* `IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`,
  `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentOrbit`,
  `RootPairing.Base.ncard_setOf_isNilpotentAd_eq`, and
  `RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram`: weighted Dynkin diagram classification and
  exact count of nilpotent orbits of connected `G` when `𝔤` is Killing.
* `TauCeti.finite_nilpotentConeOrbits`,
  `TauCeti.ncard_nilpotentConeOrbits_le`,
  `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentConeOrbits`,
  `RootPairing.Base.ncard_nilpotentConeOrbits_eq`, and
  `RootPairing.Base.nilpotentConeOrbitWeightedDynkinDiagram`: finiteness, bounds, exact count, and
  weighted Dynkin diagram classification of `TauCeti.nilpotentConeOrbits k H` when `𝔤` is reductive.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §§3.5 and 6.2.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032.
-/

public section

open CategoryTheory WithConv

namespace IsSl2Triple

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

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
              (Module.Dual k (Bialgebra.CotangentSpace k H)) g f) := by
  let _ := ratLieAlgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))
  obtain ⟨u, hu, h', hh', huh, tu⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  obtain ⟨g, hg, hgu⟩ :=
    intLieAlgebra_le_map_quotientPointsSubgroup_identityComponent (H := H) hu
  have hact (z : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g z =
        u • z := by
    have := LinearMap.congr_fun (congrArg Units.val hgu) z
    rwa [MonoidHom.coe_toHomUnits] at this
  exact ⟨g, hg, h', hh', (hact h).trans huh, by rwa [hact e, hact f]⟩

/-- **Scaling invariance of the adjoint orbit of a nilpositive element.** Every nonzero scalar
multiple of `e` lies in the same rational `G(k)`-orbit as `e`. -/
theorem mk_smul_eq {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)} (t : IsSl2Triple h e f) (c : kˣ) :
    (Comodule.VectorOrbit.mk ((c : k) • e) :
        Comodule.VectorOrbit k H (Module.Dual k (Bialgebra.CotangentSpace k H))) =
      Comodule.VectorOrbit.mk e := by
  obtain ⟨g, -, -, hge, -⟩ :=
    t.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq
      (t.rescale c)
  exact (Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hge⟩).symm

end IsSl2Triple

/-! ### Shared dominant-orbit, finiteness, and `Option`-equivalence construction -/

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

section SharedMachinery

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

private theorem mk_smul_map_eq_of_isNilpotent_ad {L : Type u} [LieRing L] [LieAlgebra k L]
    [LieAlgebra.IsKilling k L] (ι : L →ₗ⁅k⁆ 𝔤) (hι : Function.Injective ι)
    {e₀ : L} (he₀ : IsNilpotent (LieAlgebra.ad k L e₀)) (c : kˣ) :
    (Comodule.VectorOrbit.mk ((c : k) • ι e₀) : Comodule.VectorOrbit k H 𝔤) =
      Comodule.VectorOrbit.mk (ι e₀) := by
  rcases eq_or_ne e₀ 0 with rfl | he0
  · simp
  · obtain ⟨h₀, f₀, t₀⟩ := exists_isSl2Triple_of_isNilpotent_ad he₀ he0
    exact (t₀.map ι (mt (map_eq_zero_iff ι hι).mp t₀.h_ne_zero)).mk_smul_eq c

/-- Shared map sending each dominant neutral element of a Cartan subalgebra `𝔥` of a Killing Lie
algebra `L` (embedded in `𝔤` via `ι : L →ₗ⁅k⁆ 𝔤`) to the `G(k)`-orbit of its nilpositive partner's
image in `𝔤`. -/
private noncomputable def dominantNilpotentOrbitOfLieHom {L : Type u} [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [LieAlgebra.IsKilling k L] (ι : L →ₗ⁅k⁆ 𝔤)
    {𝔥 : LieSubalgebra k L} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) :
    Comodule.VectorOrbit k H 𝔤 :=
  Comodule.VectorOrbit.mk
    (ι (Classical.choose ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1))

private theorem dominantNilpotentOrbitOfLieHom_eq_mk_of_isSl2Triple {L : Type u} [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] [LieAlgebra.IsKilling k L] (ι : L →ₗ⁅k⁆ 𝔤)
    (hι : Function.Injective ι) {𝔥 : LieSubalgebra k L} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements)
    {e f : 𝔤} (t : IsSl2Triple (ι h.val) e f) :
    dominantNilpotentOrbitOfLieHom (H := H) ι b h = Comodule.VectorOrbit.mk e := by
  obtain ⟨f₀, t₀⟩ :=
    Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1
  have t₀' : IsSl2Triple (ι h.val) _ (ι f₀) := t₀.map ι (mt (map_eq_zero_iff ι hι).mp t₀.h_ne_zero)
  obtain ⟨g, -, -, hge, -⟩ :=
    t₀'.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t
  exact Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hge⟩

private theorem dominantNilpotentOrbitOfLieHom_injective {L : Type u} [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [LieAlgebra.IsKilling k L] (ι : L →ₗ⁅k⁆ 𝔤)
    {𝔥 : LieSubalgebra k L} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (huniq : ∀ {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : L},
      IsSl2Triple (h₁ : L) e₁ f₁ → IsSl2Triple (h₂ : L) e₂ f₂ →
        h₁ ∈ b.dominantNeutralElements → h₂ ∈ b.dominantNeutralElements →
        ∀ {g : WithConv (H →ₐ[k] k)},
          Comodule.basePointsRepresentation 𝔤 g (ι e₁) = ι e₂ → h₁ = h₂) :
    Function.Injective (dominantNilpotentOrbitOfLieHom (H := H) ι b) := by
  intro h₁ h₂ heq
  obtain ⟨f₁, t₁⟩ :=
    Classical.choose_spec ((b.mem_dominantNeutralElements_iff h₁.val).mp h₁.property).1
  obtain ⟨f₂, t₂⟩ :=
    Classical.choose_spec ((b.mem_dominantNeutralElements_iff h₂.val).mp h₂.property).1
  obtain ⟨g, hge⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp heq
  exact Subtype.ext (huniq t₁ t₂ h₁.property h₂.property hge)

private theorem ncard_sdiff_singleton_mk_zero_le_of_range {L : Type u} [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [LieAlgebra.IsKilling k L] {𝔥 : LieSubalgebra k L}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {S : Set (Comodule.VectorOrbit k H 𝔤)}
    {D : b.dominantNeutralElements → Comodule.VectorOrbit k H 𝔤}
    (hrange : Set.range D = S \ {Comodule.VectorOrbit.mk 0}) :
    (S \ {Comodule.VectorOrbit.mk 0}).ncard ≤ 3 ^ Module.finrank k 𝔥 - 1 := by
  have hle : (S \ {Comodule.VectorOrbit.mk 0}).ncard ≤ b.dominantNeutralElements.ncard := by
    rw [← hrange, ← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    rw [Set.ncard_univ, Nat.card_coe_set_eq]
  have hbound := b.ncard_dominantNeutralElements_add_one_le
  omega

private theorem ncard_le_of_range {L : Type u} [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    [LieAlgebra.IsKilling k L] {𝔥 : LieSubalgebra k L} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {S : Set (Comodule.VectorOrbit k H 𝔤)}
    (h0 : Comodule.VectorOrbit.mk 0 ∈ S)
    {D : b.dominantNeutralElements → Comodule.VectorOrbit k H 𝔤}
    (hrange : Set.range D = S \ {Comodule.VectorOrbit.mk 0}) :
    S.ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  have hpos : 1 ≤ 3 ^ Module.finrank k 𝔥 := Nat.one_le_pow _ _ (by decide)
  have h1 := ncard_sdiff_singleton_mk_zero_le_of_range b hrange
  have h2 := Set.ncard_insert_le (Comodule.VectorOrbit.mk (0 : 𝔤)) (S \ {Comodule.VectorOrbit.mk 0})
  rw [← Set.insert_sdiff_self_of_mem h0]
  omega

private noncomputable def optionDominantNeutralElementsEquivOfLieHom {L : Type u} [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] [LieAlgebra.IsKilling k L] (ι : L →ₗ⁅k⁆ 𝔤)
    {𝔥 : LieSubalgebra k L} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {S : Set (Comodule.VectorOrbit k H 𝔤)} (h0 : Comodule.VectorOrbit.mk 0 ∈ S)
    (hrange : Set.range (dominantNilpotentOrbitOfLieHom (H := H) ι b) =
      S \ {Comodule.VectorOrbit.mk 0})
    (hinj : Function.Injective (dominantNilpotentOrbitOfLieHom (H := H) ι b)) :
    Option b.dominantNeutralElements ≃ S :=
  open Classical in
  (Equiv.optionCongr <|
      (Equiv.ofInjective (dominantNilpotentOrbitOfLieHom (H := H) ι b) hinj).trans <|
        (Set.equivOfEq hrange).trans <|
          (Equiv.subtypeEquivRight fun _ ↦ by simp).trans <|
            (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ S)
                (· ≠ Comodule.VectorOrbit.mk 0)).symm.trans
              (Equiv.subtypeEquivRight fun _ ↦ by simp [Subtype.ext_iff])).trans
    (Equiv.optionSubtypeNe ⟨Comodule.VectorOrbit.mk 0, h0⟩)

private theorem optionDominantNeutralElementsEquivOfLieHom_none {L : Type u} [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] [LieAlgebra.IsKilling k L] (ι : L →ₗ⁅k⁆ 𝔤)
    {𝔥 : LieSubalgebra k L} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {S : Set (Comodule.VectorOrbit k H 𝔤)} (h0 : Comodule.VectorOrbit.mk 0 ∈ S)
    (hrange : Set.range (dominantNilpotentOrbitOfLieHom (H := H) ι b) =
      S \ {Comodule.VectorOrbit.mk 0})
    (hinj : Function.Injective (dominantNilpotentOrbitOfLieHom (H := H) ι b)) :
    optionDominantNeutralElementsEquivOfLieHom (H := H) ι b h0 hrange hinj none =
      ⟨Comodule.VectorOrbit.mk 0, h0⟩ := by
  classical
  rw [optionDominantNeutralElementsEquivOfLieHom, Equiv.trans_apply, Equiv.optionCongr_apply,
    Option.map_none, Equiv.optionSubtypeNe_none]

private theorem optionDominantNeutralElementsEquivOfLieHom_some_of_isSl2Triple {L : Type u}
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] [LieAlgebra.IsKilling k L]
    (ι : L →ₗ⁅k⁆ 𝔤) (hι : Function.Injective ι)
    {𝔥 : LieSubalgebra k L} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {S : Set (Comodule.VectorOrbit k H 𝔤)} (h0 : Comodule.VectorOrbit.mk 0 ∈ S)
    (hrange : Set.range (dominantNilpotentOrbitOfLieHom (H := H) ι b) =
      S \ {Comodule.VectorOrbit.mk 0})
    (hinj : Function.Injective (dominantNilpotentOrbitOfLieHom (H := H) ι b))
    (h : b.dominantNeutralElements) {e f : 𝔤} (t : IsSl2Triple (ι h.val) e f) :
    ((optionDominantNeutralElementsEquivOfLieHom (H := H) ι b h0 hrange hinj (some h) : S) :
        Comodule.VectorOrbit k H 𝔤) =
      Comodule.VectorOrbit.mk e := by
  classical
  rw [optionDominantNeutralElementsEquivOfLieHom, Equiv.trans_apply, Equiv.optionCongr_apply,
    Option.map_some, Equiv.optionSubtypeNe_some]
  simp [dominantNilpotentOrbitOfLieHom_eq_mk_of_isSl2Triple (H := H) ι hι b h t]

private theorem ncard_eq_of_equiv_option {L : Type u} [LieRing L] [LieAlgebra k L]
    [FiniteDimensional k L] [LieAlgebra.IsKilling k L] {𝔥 : LieSubalgebra k L}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {S : Set (Comodule.VectorOrbit k H 𝔤)} (e : Option b.dominantNeutralElements ≃ S) :
    S.ncard = b.dominantNeutralElements.ncard + 1 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr e, Finite.card_option, Nat.card_coe_set_eq]

end SharedMachinery

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
  obtain ⟨h₀, f₀, t₀⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
  obtain ⟨g, -, h, hh, -, t⟩ :=
    t₀.exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements
      (H := FiniteTypeCommHopfAlgCat.of k H) b
  exact ⟨g, h, hh, _, t⟩

private theorem range_dominantNilpotentOrbit_eq {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range (dominantNilpotentOrbitOfLieHom (H := H) (LieHom.id : 𝔤 →ₗ⁅k⁆ 𝔤) b) =
      {O : Comodule.VectorOrbit k H 𝔤 | O.IsNilpotentAd} \ {Comodule.VectorOrbit.mk 0} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, rfl⟩
    obtain ⟨f₀, t₀⟩ :=
      Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1
    exact ⟨Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr (t₀.isNilpotent_toEnd_e (K := k) (M := 𝔤)),
      mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mp t₀.e_ne_zero⟩
  · intro O ⟨hO, hne⟩
    induction O using Comodule.VectorOrbit.ind with | h e =>
    obtain ⟨g, h, hh, f, t⟩ :=
      exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad b
        (Comodule.VectorOrbit.isNilpotentAd_mk_iff.mp hO)
        (mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mpr hne)
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [dominantNilpotentOrbitOfLieHom_eq_mk_of_isSl2Triple (LieHom.id : 𝔤 →ₗ⁅k⁆ 𝔤)
      Function.injective_id b ⟨h, hh⟩ t, Comodule.VectorOrbit.mk_basePointsRepresentation]

namespace Comodule.VectorOrbit

/-- **Scaling invariance of nilpotent orbits.** Every nonzero scalar multiple of an `ad`-nilpotent
element lies in the same rational `G(k)`-orbit. -/
theorem mk_smul_eq_of_isNilpotent_ad {e : 𝔤} (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (c : kˣ) :
    (mk ((c : k) • e) : VectorOrbit k H 𝔤) = mk e :=
  mk_smul_map_eq_of_isNilpotent_ad (LieHom.id : 𝔤 →ₗ⁅k⁆ 𝔤) Function.injective_id he c

/-- **The zero orbit is the minimum nilpotent orbit in the closure order.** -/
theorem IsNilpotentAd.mk_zero_le {O : VectorOrbit k H 𝔤} (hO : O.IsNilpotentAd) :
    (mk (0 : 𝔤) : VectorOrbit k H 𝔤) ≤ O := by
  induction O using VectorOrbit.ind with | h e =>
  exact mk_zero_le_mk_of_forall_smul
    (mk_smul_eq_of_isNilpotent_ad (isNilpotentAd_mk_iff.mp hO))

/-- **Bound on nonzero nilpotent orbits.** Over an algebraically closed field of characteristic
zero, `G(k)` has at most `3 ^ finrank k 𝔥 - 1` nonzero nilpotent adjoint orbits in `𝔤`, for any
Cartan subalgebra `𝔥` of `𝔤`. No connectedness hypothesis on `G` is needed. -/
theorem ncard_setOf_isNilpotentAd_and_ne_mk_zero_le (𝔥 : LieSubalgebra k 𝔤)
    [𝔥.IsCartanSubalgebra] :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ mk 0}.ncard ≤ 3 ^ Module.finrank k 𝔥 - 1 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  exact ncard_sdiff_singleton_mk_zero_le_of_range b (range_dominantNilpotentOrbit_eq (H := H) b)

/-- **Finiteness of nilpotent orbits.** Over an algebraically closed field of characteristic zero,
an affine group of finite type whose Lie algebra has nondegenerate Killing form has only finitely
many nilpotent rational adjoint orbits. No connectedness hypothesis on `G` is needed. -/
theorem finite_setOf_isNilpotentAd : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.Finite := by
  obtain ⟨x, _⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k 𝔤
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  rw [← Set.insert_sdiff_self_of_mem (s := {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd})
    isNilpotentAd_mk_zero, ← range_dominantNilpotentOrbit_eq (H := H) b]
  exact (Set.finite_range _).insert _

/-- The subtype of nilpotent rational adjoint orbits is finite. -/
instance : Finite {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  finite_setOf_isNilpotentAd.to_subtype

/-- **Bound on all nilpotent orbits.** Including the zero orbit, `G(k)` has at most
`3 ^ finrank k 𝔥` nilpotent adjoint orbits in `𝔤`. -/
theorem ncard_setOf_isNilpotentAd_le (𝔥 : LieSubalgebra k 𝔤) [𝔥.IsCartanSubalgebra] :
    {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  exact ncard_le_of_range b isNilpotentAd_mk_zero (range_dominantNilpotentOrbit_eq (H := H) b)

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

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

namespace IsSl2Triple

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

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
      exact lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials g z
        ((adjointInvariantPolynomials_eq_lieInvariants
          (H := FiniteTypeCommHopfAlgCat.of k H)).symm ▸ hp)

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

end IsSl2Triple

namespace RootPairing.Base

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)

private theorem dominantNilpotentOrbit_injective (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective
      (TauCeti.dominantNilpotentOrbitOfLieHom (H := H) (LieHom.id : 𝔤 →ₗ⁅k⁆ 𝔤) b) :=
  TauCeti.dominantNilpotentOrbitOfLieHom_injective (LieHom.id : 𝔤 →ₗ⁅k⁆ 𝔤) b
    fun {_ _ _ _ _ _} t₁ t₂ hh₁ hh₂ {_} hge ↦
      t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq (H := H) b t₂ hh₁ hh₂ hge

/-- **Bijection between `Option b.dominantNeutralElements` and nilpotent orbits.** For connected
`G`, `none` corresponds to the zero orbit and `some h` corresponds to the nilpotent `G(k)`-orbit of
any nilpositive partner of `h`. -/
noncomputable def optionDominantNeutralElementsEquivNilpotentOrbit
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Option b.dominantNeutralElements ≃ {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd} :=
  (TauCeti.optionDominantNeutralElementsEquivOfLieHom (H := H) (LieHom.id : 𝔤 →ₗ⁅k⁆ 𝔤) b
      (S := {O : Comodule.VectorOrbit k H 𝔤 | O.IsNilpotentAd})
      Comodule.VectorOrbit.isNilpotentAd_mk_zero
      (TauCeti.range_dominantNilpotentOrbit_eq (H := H) b)
      (b.dominantNilpotentOrbit_injective (H := H))).trans
    (Equiv.subtypeEquivRight fun _ ↦ Iff.rfl)

/-- `none` maps to the zero nilpotent orbit. -/
@[simp]
theorem optionDominantNeutralElementsEquivNilpotentOrbit_none
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H) none =
      ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩ :=
  Subtype.ext <| by
    simp [optionDominantNeutralElementsEquivNilpotentOrbit,
      TauCeti.optionDominantNeutralElementsEquivOfLieHom_none]

/-- `some h` maps to the nilpotent orbit of any nilpositive partner `e` of `(h : 𝔤)`. -/
theorem optionDominantNeutralElementsEquivNilpotentOrbit_some_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) {e f : 𝔤}
    (t : IsSl2Triple (h : 𝔤) e f) :
    b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H) (some h) =
      ⟨Comodule.VectorOrbit.mk e,
        Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr
          (t.isNilpotent_toEnd_e (K := k) (M := 𝔤))⟩ :=
  Subtype.ext <| by
    simp [optionDominantNeutralElementsEquivNilpotentOrbit,
      TauCeti.optionDominantNeutralElementsEquivOfLieHom_some_of_isSl2Triple (H := H)
        (LieHom.id : 𝔤 →ₗ⁅k⁆ 𝔤) Function.injective_id b
        Comodule.VectorOrbit.isNilpotentAd_mk_zero
        (TauCeti.range_dominantNilpotentOrbit_eq (H := H) b)
        (b.dominantNilpotentOrbit_injective (H := H)) h t]

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
    Function.Injective (b.nilpotentOrbitWeightedDynkinDiagram (H := H)) :=
  b.injective_optionElim_weightedDynkinDiagram.comp
    (b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).symm.injective

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

/-- **Exact count of nilpotent orbits of a connected group with Killing Lie algebra.** The number of
nilpotent `G(k)`-orbits equals `b.dominantNeutralElements.ncard + 1`. -/
theorem ncard_setOf_isNilpotentAd_eq (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    {O : Comodule.VectorOrbit k H 𝔤 | O.IsNilpotentAd}.ncard =
      b.dominantNeutralElements.ncard + 1 :=
  TauCeti.ncard_eq_of_equiv_option b
    ((b.optionDominantNeutralElementsEquivNilpotentOrbit (H := H)).trans
      (Equiv.subtypeEquivRight fun _ ↦ Iff.rfl))

end RootPairing.Base

end Connected

/-! ### Reductive Lie algebras and nilpotent-cone orbits -/

section Reductive

open TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

namespace IsSl2Triple

/-- **Every `sl₂` triple in `⁅𝔤, 𝔤⁆` is `G°(k)`-conjugate to a dominant one** when `𝔤` is
reductive. -/
theorem exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements_coe_eq
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {𝔥 : LieSubalgebra k
      (LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1)}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h e f : LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1}
    (t : IsSl2Triple h e f) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∃ h' ∈ b.dominantNeutralElements, ∃ e' f' :
          LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1,
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g
            (h : Module.Dual k (Bialgebra.CotangentSpace k H)) =
              ((h' : LieAlgebra.derivedSeries k
                (Module.Dual k (Bialgebra.CotangentSpace k H)) 1) :
                Module.Dual k (Bialgebra.CotangentSpace k H)) ∧
          Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g
            (e : Module.Dual k (Bialgebra.CotangentSpace k H)) = e' ∧
          Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g
            (f : Module.Dual k (Bialgebra.CotangentSpace k H)) = f' ∧
          IsSl2Triple
            (h' : LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1)
            e' f' := by
  let _ := ratLieAlgebra k
    (LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1)
  obtain ⟨u, hu, h', hh', huh, tu⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  obtain ⟨g, hg, hgu⟩ :=
    exists_mem_quotientPointsSubgroup_forall_derivedSeries_eq_of_mem_intLieAlgebra
      (H := H.obj) (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
      (HopfIdeal.lieSubalgebra_identityComponentHopfIdeal_eq_top.ge.trans' le_top) hu
  exact ⟨g, hg, h', hh', u • e, u • f, (hgu h).trans (congrArg Subtype.val huh), hgu e, hgu f, tu⟩

end IsSl2Triple

namespace TauCeti

section ReductiveFiniteness

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]
  [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "𝔤'" => LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1

/-- **Every nonzero `ad`-nilpotent element of `⁅𝔤, 𝔤⁆` is `G(k)`-conjugate to the nilpositive
element of a dominant `sl₂` triple in `⁅𝔤, 𝔤⁆`.** -/
theorem exists_basePointsRepresentation_isSl2Triple_of_mem_derivedSeries_of_isNilpotent_ad
    {𝔥 : LieSubalgebra k 𝔤'} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {e : 𝔤}
    (he_mem : e ∈ 𝔤') (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (he0 : e ≠ 0) :
    ∃ (g : WithConv (H →ₐ[k] k)), ∃ h ∈ b.dominantNeutralElements, ∃ e' f' : 𝔤',
      Comodule.basePointsRepresentation 𝔤 g e = (e' : 𝔤) ∧ IsSl2Triple (h : 𝔤') e' f' := by
  have he' : IsNilpotent (LieAlgebra.ad k 𝔤' ⟨e, he_mem⟩) := (LieIdeal.isNilpotent_ad_iff 𝔤').mpr he
  have he'0 : (⟨e, he_mem⟩ : 𝔤') ≠ 0 := fun h ↦ he0 (congrArg Subtype.val h)
  obtain ⟨h₀, f₀, t₀⟩ := exists_isSl2Triple_of_isNilpotent_ad he' he'0
  obtain ⟨g, -, h, hh, e', f', -, hge, -, t⟩ :=
    t₀.exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements_coe_eq
      (H := FiniteTypeCommHopfAlgCat.of k H) b
  exact ⟨g, h, hh, e', f', hge, t⟩

/-- **Scaling invariance of `ad`-nilpotent orbits in `⁅𝔤, 𝔤⁆`** for reductive `𝔤`. -/
theorem mk_smul_eq_of_mem_derivedSeries_of_isNilpotent_ad {e : 𝔤} (he_mem : e ∈ 𝔤')
    (he : IsNilpotent (LieAlgebra.ad k 𝔤 e)) (c : kˣ) :
    (Comodule.VectorOrbit.mk ((c : k) • e) : Comodule.VectorOrbit k H 𝔤) =
      Comodule.VectorOrbit.mk e :=
  mk_smul_map_eq_of_isNilpotent_ad (𝔤').incl (𝔤').incl_injective (e₀ := (⟨e, he_mem⟩ : 𝔤'))
    ((LieIdeal.isNilpotent_ad_iff 𝔤').mpr he) c

private theorem range_dominantDerivedNilpotentOrbit_eq {𝔥 : LieSubalgebra k 𝔤'}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range (dominantNilpotentOrbitOfLieHom (H := H) (𝔤').incl b) =
      {O : Comodule.VectorOrbit k H 𝔤 |
        ∃ x ∈ 𝔤', IsNilpotent (LieAlgebra.ad k 𝔤 x) ∧ Comodule.VectorOrbit.mk x = O} \
        {Comodule.VectorOrbit.mk 0} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, rfl⟩
    obtain ⟨f₀, t₀⟩ :=
      Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1
    have t₀' := t₀.map (𝔤').incl (by simpa using t₀.h_ne_zero)
    exact ⟨⟨_, Subtype.prop _, t₀'.isNilpotent_toEnd_e (K := k) (M := 𝔤), rfl⟩,
      mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mp t₀'.e_ne_zero⟩
  · rintro O ⟨⟨x, hx_mem, hx_nil, rfl⟩, hne⟩
    obtain ⟨g, h, hh, e', f', hge, t⟩ :=
      exists_basePointsRepresentation_isSl2Triple_of_mem_derivedSeries_of_isNilpotent_ad
        b hx_mem hx_nil (mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mpr hne)
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [dominantNilpotentOrbitOfLieHom_eq_mk_of_isSl2Triple (𝔤').incl (𝔤').incl_injective b ⟨h, hh⟩
      (t.map (𝔤').incl (by simpa using t.h_ne_zero)), (𝔤').incl_apply, ← hge,
      Comodule.VectorOrbit.mk_basePointsRepresentation]

variable (k H) in
/-- **Bound on nonzero `ad`-nilpotent orbits of `⁅𝔤, 𝔤⁆`** (no connectedness needed). -/
theorem ncard_setOf_exists_mem_derivedSeries_and_isNilpotent_ad_and_ne_mk_zero_le
    (𝔥 : LieSubalgebra k 𝔤') [𝔥.IsCartanSubalgebra] :
    {O : Comodule.VectorOrbit k H 𝔤 |
      (∃ x ∈ 𝔤', IsNilpotent (LieAlgebra.ad k 𝔤 x) ∧ Comodule.VectorOrbit.mk x = O) ∧
        O ≠ Comodule.VectorOrbit.mk 0}.ncard ≤ 3 ^ Module.finrank k 𝔥 - 1 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  exact ncard_sdiff_singleton_mk_zero_le_of_range b (range_dominantDerivedNilpotentOrbit_eq b)

/-- **Finiteness of `G(k)`-orbits of `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆`** (no connectedness
needed). -/
theorem finite_setOf_exists_mem_derivedSeries_and_isNilpotent_ad :
    {O : Comodule.VectorOrbit k H 𝔤 |
      ∃ x ∈ 𝔤', IsNilpotent (LieAlgebra.ad k 𝔤 x) ∧ Comodule.VectorOrbit.mk x = O}.Finite := by
  obtain ⟨x, _⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k 𝔤'
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  rw [← Set.insert_sdiff_self_of_mem
    (s := {O : Comodule.VectorOrbit k H 𝔤 |
      ∃ x ∈ 𝔤', IsNilpotent (LieAlgebra.ad k 𝔤 x) ∧ Comodule.VectorOrbit.mk x = O})
    ⟨0, zero_mem _, by simp, rfl⟩, ← range_dominantDerivedNilpotentOrbit_eq b]
  exact (Set.finite_range _).insert _

variable (k H) in
/-- **Bound on all `G(k)`-orbits of `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆`** (no connectedness
needed). -/
theorem ncard_setOf_exists_mem_derivedSeries_and_isNilpotent_ad_le
    (𝔥 : LieSubalgebra k 𝔤') [𝔥.IsCartanSubalgebra] :
    {O : Comodule.VectorOrbit k H 𝔤 |
      ∃ x ∈ 𝔤', IsNilpotent (LieAlgebra.ad k 𝔤 x) ∧ Comodule.VectorOrbit.mk x = O}.ncard ≤
        3 ^ Module.finrank k 𝔥 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  exact ncard_le_of_range b ⟨0, zero_mem _, by simp, rfl⟩
    (range_dominantDerivedNilpotentOrbit_eq b)

end ReductiveFiniteness

section ReductiveConnected

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "𝔤'" => LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1

/-- For connected `G` with reductive Lie algebra `𝔤`, `nilpotentConeOrbits k H` is the set of
orbits of `ad`-nilpotent elements of `⁅𝔤, 𝔤⁆`. -/
theorem nilpotentConeOrbits_eq_setOf_exists_mem_derivedSeries_and_isNilpotent_ad :
    nilpotentConeOrbits k H =
      {O : Comodule.VectorOrbit k H 𝔤 |
        ∃ x ∈ 𝔤', IsNilpotent (LieAlgebra.ad k 𝔤 x) ∧ Comodule.VectorOrbit.mk x = O} := by
  ext O
  induction O using Comodule.VectorOrbit.ind with | h x =>
  simp only [mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad,
    Set.mem_ofPred_eq]
  refine ⟨fun ⟨hx, hnil⟩ ↦ ⟨x, hx, hnil, rfl⟩, fun ⟨y, hy, hnil, heq⟩ ↦ ?_⟩
  obtain ⟨g, rfl⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp heq
  refine ⟨(Derivation.basePointsRepresentation_adjointComodule_mem_derivedSeries_iff g 1 y).mpr hy,
    ?_⟩
  rw [← Derivation.basePointsAdjointLieEquiv_apply,
    (Derivation.basePointsAdjointLieEquiv g).isNilpotent_ad_apply_iff]
  exact hnil

/-- **Finiteness of rational orbits in the nilpotent cone** for connected `G` with reductive Lie
algebra `𝔤`. -/
theorem finite_nilpotentConeOrbits : (nilpotentConeOrbits k H).Finite := by
  rw [nilpotentConeOrbits_eq_setOf_exists_mem_derivedSeries_and_isNilpotent_ad]
  exact finite_setOf_exists_mem_derivedSeries_and_isNilpotent_ad

/-- The subtype `nilpotentConeOrbits k H` is finite for connected `G` with reductive Lie algebra. -/
instance : Finite (nilpotentConeOrbits k H) :=
  finite_nilpotentConeOrbits.to_subtype

variable (k H) in
/-- **Bound on nonzero orbits in `nilpotentConeOrbits k H`:** at most `3 ^ finrank k 𝔥 - 1` for any
Cartan subalgebra `𝔥` of `⁅𝔤, 𝔤⁆`. -/
theorem ncard_nilpotentConeOrbits_sdiff_singleton_mk_zero_le
    (𝔥 : LieSubalgebra k 𝔤') [𝔥.IsCartanSubalgebra] :
    (nilpotentConeOrbits k H \ {Comodule.VectorOrbit.mk 0}).ncard ≤
      3 ^ Module.finrank k 𝔥 - 1 := by
  rw [nilpotentConeOrbits_eq_setOf_exists_mem_derivedSeries_and_isNilpotent_ad]
  exact ncard_setOf_exists_mem_derivedSeries_and_isNilpotent_ad_and_ne_mk_zero_le k H 𝔥

variable (k H) in
/-- **Bound on all orbits in `nilpotentConeOrbits k H`:** at most `3 ^ finrank k 𝔥` for any Cartan
subalgebra `𝔥` of `⁅𝔤, 𝔤⁆`. -/
theorem ncard_nilpotentConeOrbits_le (𝔥 : LieSubalgebra k 𝔤') [𝔥.IsCartanSubalgebra] :
    (nilpotentConeOrbits k H).ncard ≤ 3 ^ Module.finrank k 𝔥 := by
  rw [nilpotentConeOrbits_eq_setOf_exists_mem_derivedSeries_and_isNilpotent_ad]
  exact ncard_setOf_exists_mem_derivedSeries_and_isNilpotent_ad_le k H 𝔥

/-- **Minimality of the zero orbit in `nilpotentConeOrbits k H`.** -/
theorem mk_zero_le_of_mem_nilpotentConeOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentConeOrbits k H) :
    (Comodule.VectorOrbit.mk (0 : 𝔤) : Comodule.VectorOrbit k H 𝔤) ≤ O := by
  induction O using Comodule.VectorOrbit.ind with | h e =>
  obtain ⟨he_mem, he_nil⟩ :=
    mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad.mp hO
  exact Comodule.VectorOrbit.mk_zero_le_mk_of_forall_smul
    (mk_smul_eq_of_mem_derivedSeries_of_isNilpotent_ad he_mem he_nil)

/-- **Finiteness of the lower set of an orbit in `nilpotentConeOrbits k H`.** -/
theorem finite_setOf_le_of_mem_nilpotentConeOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentConeOrbits k H) :
    {O' : Comodule.VectorOrbit k H 𝔤 | O' ≤ O}.Finite :=
  finite_nilpotentConeOrbits.subset fun _ hle ↦ mem_nilpotentConeOrbits_of_le hle hO

/-- **Finiteness of the strict lower set of an orbit in `nilpotentConeOrbits k H`.** -/
theorem finite_setOf_lt_of_mem_nilpotentConeOrbits {O : Comodule.VectorOrbit k H 𝔤}
    (hO : O ∈ nilpotentConeOrbits k H) :
    {O' : Comodule.VectorOrbit k H 𝔤 | O' < O}.Finite :=
  (finite_setOf_le_of_mem_nilpotentConeOrbits hO).subset
    fun (_ : Comodule.VectorOrbit k H 𝔤) (hlt : _ < O) ↦ hlt.le

end ReductiveConnected

end TauCeti

namespace IsSl2Triple

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k
    (LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1)}
  [𝔥.IsCartanSubalgebra]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "𝔤'" => LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1

/-- **Uniqueness of dominant neutral elements in `⁅𝔤, 𝔤⁆` under `G(k)`-conjugacy** for connected
`G` with reductive Lie algebra `𝔤`. -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_coe_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤'}
    (t₁ : IsSl2Triple (h₁ : 𝔤') e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤') e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : WithConv (H →ₐ[k] k)}
    (hge : Comodule.basePointsRepresentation 𝔤 g (e₁ : 𝔤) = (e₂ : 𝔤)) :
    h₁ = h₂ := by
  let ψ : 𝔤 ≃ₗ⁅k⁆ 𝔤 := Derivation.basePointsAdjointLieEquiv g
  let φ : 𝔤' ≃ₗ⁅k⁆ 𝔤' := ψ.ofSubalgebras (𝔤').toLieSubalgebra (𝔤').toLieSubalgebra
    (Derivation.map_basePointsAdjointLieEquiv_derivedSeries g 1)
  have hφe : φ e₁ = e₂ := Subtype.ext <|
    (ψ.ofSubalgebras_apply (𝔤').toLieSubalgebra (𝔤').toLieSubalgebra
      (Derivation.map_basePointsAdjointLieEquiv_derivedSeries g 1) e₁).trans
      (by rwa [Derivation.basePointsAdjointLieEquiv_apply])
  refine t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂ φ hφe
    fun p hp z ↦ ?_
  let π : 𝔤 →ₗ⁅k⁆ 𝔤' := derivedSeriesLieProj k 𝔤
  let q := _root_.SymmetricAlgebra.map k π.toLinearMap.dualMap p
  have hq : q ∈ adjointInvariantPolynomials k H :=
    (adjointInvariantPolynomials_eq_lieInvariants
      (H := FiniteTypeCommHopfAlgCat.of k H)).symm ▸ π.map_dualMap_mem_lieInvariants hp
  have heval (w : 𝔤') :
      _root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (w : 𝔤)) q =
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤' w) p := by
    have hhom : (_root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤 (w : 𝔤))).comp
          (_root_.SymmetricAlgebra.map k π.toLinearMap.dualMap) =
        _root_.SymmetricAlgebra.lift (Module.Dual.eval k 𝔤' w) :=
      _root_.SymmetricAlgebra.algHom_ext <| LinearMap.ext fun _ ↦ by
        simp [π, derivedSeriesLieProj_coe]
    exact AlgHom.congr_fun hhom p
  rw [← heval (φ z), ← heval z]
  have hφz : ((φ z : 𝔤') : 𝔤) = Comodule.basePointsRepresentation 𝔤 g (z : 𝔤) :=
    (ψ.ofSubalgebras_apply (𝔤').toLieSubalgebra (𝔤').toLieSubalgebra
      (Derivation.map_basePointsAdjointLieEquiv_derivedSeries g 1) z).trans
      (Derivation.basePointsAdjointLieEquiv_apply g (z : 𝔤))
  rw [hφz]
  exact lift_eval_basePointsRepresentation_of_mem_adjointInvariantPolynomials g (z : 𝔤) hq

/-- **Classification of nilpositive elements in `⁅𝔤, 𝔤⁆` by weighted Dynkin diagrams** for
connected `G` with reductive Lie algebra `𝔤`. -/
theorem exists_basePointsRepresentation_coe_eq_iff_weightedDynkinDiagram_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥} {e₁ f₁ e₂ f₂ : 𝔤'}
    (t₁ : IsSl2Triple (h₁ : 𝔤') e₁ f₁) (t₂ : IsSl2Triple (h₂ : 𝔤') e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements) :
    (∃ g : WithConv (H →ₐ[k] k), Comodule.basePointsRepresentation 𝔤 g (e₁ : 𝔤) = (e₂ : 𝔤)) ↔
      b.weightedDynkinDiagram ⟨h₁, hh₁⟩ = b.weightedDynkinDiagram ⟨h₂, hh₂⟩ := by
  constructor
  · rintro ⟨g, hge⟩
    congr 1
    exact Subtype.ext
      (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_coe_eq
        b t₂ hh₁ hh₂ hge)
  · intro hdiag
    obtain rfl : h₁ = h₂ := congrArg Subtype.val (b.weightedDynkinDiagram_injective hdiag)
    obtain ⟨g, -, -, hge, -⟩ :=
      (t₁.map (𝔤').incl (by simpa using t₁.h_ne_zero)
        ).exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq
        (t₂.map (𝔤').incl (by simpa using t₂.h_ne_zero))
    exact ⟨g, hge⟩

end IsSl2Triple

namespace RootPairing.Base

variable {k H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.HasCentralRadical k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k
    (LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1)}
  [𝔥.IsCartanSubalgebra]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "𝔤'" => LieAlgebra.derivedSeries k (Module.Dual k (Bialgebra.CotangentSpace k H)) 1

private theorem range_dominantNilpotentConeOrbit_eq (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range (TauCeti.dominantNilpotentOrbitOfLieHom (H := H) (𝔤').incl b) =
      nilpotentConeOrbits k H \ {Comodule.VectorOrbit.mk 0} := by
  rw [nilpotentConeOrbits_eq_setOf_exists_mem_derivedSeries_and_isNilpotent_ad]
  exact TauCeti.range_dominantDerivedNilpotentOrbit_eq (H := H) b

private theorem dominantNilpotentConeOrbit_injective
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective (TauCeti.dominantNilpotentOrbitOfLieHom (H := H) (𝔤').incl b) :=
  TauCeti.dominantNilpotentOrbitOfLieHom_injective (𝔤').incl b
    fun {_ _ _ _ _ _} t₁ t₂ hh₁ hh₂ {_} hge ↦
      t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_coe_eq
        (H := H) b t₂ hh₁ hh₂ hge

/-- **Bijection between `Option b.dominantNeutralElements` and `nilpotentConeOrbits k H`** for
connected `G` with reductive Lie algebra `𝔤` and Cartan subalgebra `𝔥` of `⁅𝔤, 𝔤⁆`. -/
noncomputable def optionDominantNeutralElementsEquivNilpotentConeOrbits
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Option b.dominantNeutralElements ≃ nilpotentConeOrbits k H :=
  TauCeti.optionDominantNeutralElementsEquivOfLieHom (H := H) (𝔤').incl b
    mk_zero_mem_nilpotentConeOrbits
    (b.range_dominantNilpotentConeOrbit_eq (H := H))
    (b.dominantNilpotentConeOrbit_injective (H := H))

/-- `none` maps to the zero orbit in `nilpotentConeOrbits k H`. -/
@[simp]
theorem optionDominantNeutralElementsEquivNilpotentConeOrbits_none
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H) none =
      ⟨Comodule.VectorOrbit.mk 0, mk_zero_mem_nilpotentConeOrbits⟩ :=
  TauCeti.optionDominantNeutralElementsEquivOfLieHom_none (H := H) (𝔤').incl b
    mk_zero_mem_nilpotentConeOrbits
    (b.range_dominantNilpotentConeOrbit_eq (H := H))
    (b.dominantNilpotentConeOrbit_injective (H := H))

/-- `some h` maps to the orbit of `(e : 𝔤)` for any `sl₂` triple `(h, e, f)` in `⁅𝔤, 𝔤⁆`. -/
theorem optionDominantNeutralElementsEquivNilpotentConeOrbits_some_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) {e f : 𝔤'}
    (t : IsSl2Triple (h : 𝔤') e f) :
    b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H) (some h) =
      ⟨Comodule.VectorOrbit.mk (e : 𝔤),
        mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad.mpr
          ⟨e.property, (LieIdeal.isNilpotent_ad_iff 𝔤').mp
            (t.isNilpotent_toEnd_e (K := k) (M := 𝔤'))⟩⟩ :=
  Subtype.ext <|
    TauCeti.optionDominantNeutralElementsEquivOfLieHom_some_of_isSl2Triple (H := H)
      (𝔤').incl (𝔤').incl_injective b mk_zero_mem_nilpotentConeOrbits
      (b.range_dominantNilpotentConeOrbit_eq (H := H))
      (b.dominantNilpotentConeOrbit_injective (H := H)) h
      (t.map (𝔤').incl (by simpa using t.h_ne_zero))

/-- The inverse equivalence sends the zero orbit in `nilpotentConeOrbits k H` to `none`. -/
@[simp]
theorem optionDominantNeutralElementsEquivNilpotentConeOrbits_symm_mk_zero
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H)).symm
        ⟨Comodule.VectorOrbit.mk 0, mk_zero_mem_nilpotentConeOrbits⟩ = none :=
  (b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H)).symm_apply_eq.mpr
    (b.optionDominantNeutralElementsEquivNilpotentConeOrbits_none (H := H)).symm

/-- The inverse equivalence sends the orbit of `(e : 𝔤)` of a dominant `sl₂` triple `(h, e, f)` in
`⁅𝔤, 𝔤⁆` to `some ⟨h, hh⟩`. -/
theorem optionDominantNeutralElementsEquivNilpotentConeOrbits_symm_mk_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h : 𝔥} {e f : 𝔤'}
    (t : IsSl2Triple (h : 𝔤') e f) (hh : h ∈ b.dominantNeutralElements) :
    (b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H)).symm
        ⟨Comodule.VectorOrbit.mk (e : 𝔤),
          mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad.mpr
            ⟨e.property, (LieIdeal.isNilpotent_ad_iff 𝔤').mp
              (t.isNilpotent_toEnd_e (K := k) (M := 𝔤'))⟩⟩ =
      some ⟨h, hh⟩ :=
  (b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H)).symm_apply_eq.mpr
    (b.optionDominantNeutralElementsEquivNilpotentConeOrbits_some_of_isSl2Triple
      (H := H) ⟨h, hh⟩ t).symm

/-- **Exact count of orbits in `nilpotentConeOrbits k H`** for connected `G` with reductive Lie
algebra `𝔤`: `(nilpotentConeOrbits k H).ncard = b.dominantNeutralElements.ncard + 1`. -/
theorem ncard_nilpotentConeOrbits_eq (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (nilpotentConeOrbits k H).ncard = b.dominantNeutralElements.ncard + 1 :=
  TauCeti.ncard_eq_of_equiv_option b
    (b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H))

/-- **The weighted Dynkin diagram of an orbit in `nilpotentConeOrbits k H`** for connected `G` with
reductive Lie algebra `𝔤`, sending the zero orbit to `0 : b.support → Fin 3` and every nonzero orbit
to the `{0, 1, 2}` simple-root labeling of its unique dominant neutral element in `𝔥 ⊆ ⁅𝔤, 𝔤⁆`. -/
noncomputable def nilpotentConeOrbitWeightedDynkinDiagram
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (O : nilpotentConeOrbits k H) :
    b.support → Fin 3 :=
  ((b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H)).symm O).elim 0
    b.weightedDynkinDiagram

/-- Unfolding lemma for `RootPairing.Base.nilpotentConeOrbitWeightedDynkinDiagram`. -/
theorem nilpotentConeOrbitWeightedDynkinDiagram_def
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (O : nilpotentConeOrbits k H) :
    b.nilpotentConeOrbitWeightedDynkinDiagram (H := H) O =
      ((b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H)).symm O).elim 0
        b.weightedDynkinDiagram :=
  (rfl)

/-- On `optionDominantNeutralElementsEquivNilpotentConeOrbits x`, the diagram is `0` for `none` and
`b.weightedDynkinDiagram h` for `some h`. -/
@[simp]
theorem
    nilpotentConeOrbitWeightedDynkinDiagram_optionDominantNeutralElementsEquivNilpotentConeOrbits
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (x : Option b.dominantNeutralElements) :
    b.nilpotentConeOrbitWeightedDynkinDiagram (H := H)
        (b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H) x) =
      x.elim 0 b.weightedDynkinDiagram := by
  simp [nilpotentConeOrbitWeightedDynkinDiagram_def]

/-- The zero orbit in `nilpotentConeOrbits k H` has the all-zero weighted Dynkin diagram `0`. -/
@[simp]
theorem nilpotentConeOrbitWeightedDynkinDiagram_mk_zero
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    b.nilpotentConeOrbitWeightedDynkinDiagram (H := H)
        ⟨Comodule.VectorOrbit.mk 0, mk_zero_mem_nilpotentConeOrbits⟩ = 0 := by
  simp [nilpotentConeOrbitWeightedDynkinDiagram_def]

/-- On the orbit of `(e : 𝔤)` of a dominant `sl₂` triple `(h, e, f)` in `⁅𝔤, 𝔤⁆`, the diagram is
`b.weightedDynkinDiagram ⟨h, hh⟩`. -/
theorem nilpotentConeOrbitWeightedDynkinDiagram_mk_of_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h : 𝔥} {e f : 𝔤'}
    (t : IsSl2Triple (h : 𝔤') e f) (hh : h ∈ b.dominantNeutralElements) :
    b.nilpotentConeOrbitWeightedDynkinDiagram (H := H)
        ⟨Comodule.VectorOrbit.mk (e : 𝔤),
          mk_mem_nilpotentConeOrbits_iff_mem_derivedSeries_and_isNilpotent_ad.mpr
            ⟨e.property, (LieIdeal.isNilpotent_ad_iff 𝔤').mp
              (t.isNilpotent_toEnd_e (K := k) (M := 𝔤'))⟩⟩ =
      b.weightedDynkinDiagram ⟨h, hh⟩ := by
  rw [nilpotentConeOrbitWeightedDynkinDiagram_def,
    b.optionDominantNeutralElementsEquivNilpotentConeOrbits_symm_mk_of_isSl2Triple (H := H) t hh]
  rfl

/-- **Weighted Dynkin diagrams classify `nilpotentConeOrbits k H`** for connected `G` with reductive
Lie algebra `𝔤`. -/
theorem nilpotentConeOrbitWeightedDynkinDiagram_injective
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective (b.nilpotentConeOrbitWeightedDynkinDiagram (H := H)) :=
  b.injective_optionElim_weightedDynkinDiagram.comp
    (b.optionDominantNeutralElementsEquivNilpotentConeOrbits (H := H)).symm.injective

/-- Two orbits in `nilpotentConeOrbits k H` have the same weighted Dynkin diagram iff they are
equal. -/
@[simp]
theorem nilpotentConeOrbitWeightedDynkinDiagram_eq_iff
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (O₁ O₂ : nilpotentConeOrbits k H) :
    b.nilpotentConeOrbitWeightedDynkinDiagram (H := H) O₁ =
        b.nilpotentConeOrbitWeightedDynkinDiagram (H := H) O₂ ↔ O₁ = O₂ :=
  (b.nilpotentConeOrbitWeightedDynkinDiagram_injective (H := H)).eq_iff

/-- An orbit in `nilpotentConeOrbits k H` has the all-zero diagram iff it is the zero orbit. -/
@[simp]
theorem nilpotentConeOrbitWeightedDynkinDiagram_eq_zero_iff
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (O : nilpotentConeOrbits k H) :
    b.nilpotentConeOrbitWeightedDynkinDiagram (H := H) O = 0 ↔
      O = ⟨Comodule.VectorOrbit.mk 0, mk_zero_mem_nilpotentConeOrbits⟩ := by
  rw [← b.nilpotentConeOrbitWeightedDynkinDiagram_mk_zero (H := H),
    b.nilpotentConeOrbitWeightedDynkinDiagram_eq_iff]

end RootPairing.Base

end Reductive
