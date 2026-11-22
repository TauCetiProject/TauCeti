/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Exponential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Nilpotent.Cone
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Uniqueness
import Mathlib.Data.Set.Card
import TauCeti.Algebra.Lie.CartanExists
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
without assuming `G` is connected. Consequently, for any nilpotent orbit `O`, only finitely many
orbits lie below `O` in the closure order
(`TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd`,
`TauCeti.Comodule.VectorOrbit.finite_setOf_lt_of_isNilpotentAd`), so the generic scheme-point
decompositions of `closure O` and `closure O \ O` inside the affine chart `𝔤 = {t ≠ 0}` of
`P(𝔤 × k)` specialize to decompositions in `TauCeti.Comodule.VectorOrbit` indexed by the
subtype of nilpotent orbits (`closure_image_inter_basicOpen_snd_eq_biUnion_le_nilpotentOrbit` and
`closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_nilpotentOrbit`).

When `G` is connected, `O(𝔤)^G = S(𝔤*)^𝔤` (`TauCeti.adjointInvariantPolynomials_eq_lieInvariants`),
so two dominant `sl₂` triples have `G(k)`-conjugate nilpositive elements if and only if their
weighted Dynkin diagrams coincide
(`IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`). This gives an
explicit equivalence `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentOrbit` between
`Option b.dominantNeutralElements` and the subtype of nilpotent `G(k)`-orbits, and an injective
orbit-level weighted Dynkin diagram invariant
`RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram` valued in `b.support → Fin 3`, assigning the
all-zero diagram `0` to the zero orbit and `b.weightedDynkinDiagram h` to each nonzero orbit.

## Main declarations

* `IsSl2Triple.exists_mem_quotientPointsSubgroup_identityComponent_dominantNeutralElements`: every
  `sl₂` triple is `G°(k)`-conjugate to one with dominant neutral element.
* `TauCeti.exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad`: every nonzero
  `ad`-nilpotent element is `G(k)`-conjugate to the nilpositive element of a dominant `sl₂` triple.
* `TauCeti.Comodule.VectorOrbit.finite_setOf_isNilpotentAd`,
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_and_ne_mk_zero_le`, and
  `TauCeti.Comodule.VectorOrbit.ncard_setOf_isNilpotentAd_le`: finiteness and `3 ^ rank` bounds for
  nilpotent `G(k)`-orbits without assuming connectedness.
* `TauCeti.Comodule.VectorOrbit.finite_setOf_le_of_isNilpotentAd` and
  `TauCeti.Comodule.VectorOrbit.finite_setOf_lt_of_isNilpotentAd`: finiteness of orbits below a
  nilpotent orbit in the closure order, making the decomposition of the `k`-rational vectors
  `{y : 𝔤 | mk y ≤ O}` in
  `TauCeti.Comodule.VectorOrbit.setOf_mk_le_eq_union_biUnion_of_isNilpotentAd` a finite union.
* `closure_image_inter_basicOpen_snd_eq_biUnion_le_nilpotentOrbit` and
  `closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_nilpotentOrbit` in
  `TauCeti.Comodule.VectorOrbit`: exact decompositions of `closure O` and `closure O \ O` in the
  affine chart `𝔤` of `P(𝔤 × k)` into finite unions indexed by the nilpotent orbit subtype.
* `IsSl2Triple.exists_basePointsRepresentation_eq_iff_weightedDynkinDiagram_eq`: for connected `G`,
  nilpositive elements of dominant `sl₂` triples are `G(k)`-conjugate iff their weighted Dynkin
  diagrams agree.
* `RootPairing.Base.optionDominantNeutralElementsEquivNilpotentOrbit` and
  `RootPairing.Base.nilpotentOrbitWeightedDynkinDiagram`: bijection with
  `Option b.dominantNeutralElements` and injective `{0, 1, 2}` weighted Dynkin diagram
  classification of nilpotent orbits of connected `G`.

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

end IsSl2Triple

namespace TauCeti

universe u

attribute [local instance] Derivation.adjointComodule

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

/-- Map sending each dominant neutral element to the rational adjoint orbit of its nilpositive
partner; by Malcev–Kostant conjugacy at fixed `h`, this orbit is independent of the partner. -/
private noncomputable def dominantNilpotentOrbit {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) (h : b.dominantNeutralElements) :
    Comodule.VectorOrbit k H 𝔤 :=
  Comodule.VectorOrbit.mk (Classical.choose ((b.mem_dominantNeutralElements_iff h.val).mp
      h.property).1)

private theorem dominantNilpotentOrbit_eq_mk_of_isSl2Triple {𝔥 : LieSubalgebra k 𝔤}
    [𝔥.IsCartanSubalgebra] (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (h : b.dominantNeutralElements) {e f : 𝔤} (t : IsSl2Triple (h : 𝔤) e f) :
    dominantNilpotentOrbit (H := H) b h = Comodule.VectorOrbit.mk e := by
  obtain ⟨f₀, t₀⟩ :=
    Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1
  obtain ⟨g, -, -, hge, -⟩ :=
    t₀.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t
  exact Comodule.VectorOrbit.mk_eq_mk_iff.mpr ⟨g, hge⟩

private theorem range_dominantNilpotentOrbit_eq {𝔥 : LieSubalgebra k 𝔤} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range (dominantNilpotentOrbit (H := H) b) =
      {O : Comodule.VectorOrbit k H 𝔤 | O.IsNilpotentAd ∧ O ≠ Comodule.VectorOrbit.mk 0} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, rfl⟩
    obtain ⟨f₀, t₀⟩ :=
      Classical.choose_spec ((b.mem_dominantNeutralElements_iff h.val).mp h.property).1
    exact ⟨Comodule.VectorOrbit.isNilpotentAd_mk_iff.mpr (t₀.isNilpotent_toEnd_e (K := k) (M := 𝔤)),
      mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mp t₀.e_ne_zero⟩
  · intro O ⟨hO, hne⟩
    induction O using Comodule.VectorOrbit.ind with | h e =>
    have he0 : e ≠ 0 := mt Comodule.VectorOrbit.mk_eq_mk_zero_iff.mpr hne
    obtain ⟨g, h, hh, f, t⟩ :=
      exists_basePointsRepresentation_isSl2Triple_of_isNilpotent_ad b
        (Comodule.VectorOrbit.isNilpotentAd_mk_iff.mp hO) he0
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [dominantNilpotentOrbit_eq_mk_of_isSl2Triple b ⟨h, hh⟩ t,
      Comodule.VectorOrbit.mk_basePointsRepresentation]

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
    rw [← range_dominantNilpotentOrbit_eq (H := H) b, ← Set.image_univ]
    refine (Set.ncard_image_le Set.finite_univ).trans ?_
    rw [Set.ncard_univ, Nat.card_coe_set_eq]
  have hbound := b.ncard_dominantNeutralElements_add_one_le
  omega

/-- **Finiteness of nilpotent orbits.** Over an algebraically closed field of characteristic zero,
an affine group of finite type whose Lie algebra has nondegenerate Killing form has only finitely
many nilpotent rational adjoint orbits. No connectedness hypothesis on `G` is needed. -/
theorem finite_setOf_isNilpotentAd : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd}.Finite := by
  obtain ⟨x, _⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k 𝔤
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  have hsub : {O : VectorOrbit k H 𝔤 | O.IsNilpotentAd} ⊆
      insert (mk 0) (Set.range (dominantNilpotentOrbit (H := H) b)) := by
    intro O hO
    rw [range_dominantNilpotentOrbit_eq]
    rcases eq_or_ne O (mk 0) with rfl | h0
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨hO, h0⟩
  exact ((Set.finite_range _).insert (mk 0)).subset hsub

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

/-- **Orbit closure decomposition for nilpotent orbits.** Inside the affine chart `𝔤 = {t ≠ 0}` of
`P(𝔤 × k)`, the closure of a nilpotent adjoint orbit `O` is the finite union of the scheme-point
orbit images of all nilpotent orbits `O' ≤ O`, indexed by the nilpotent orbit subtype. No
connectedness of `G` is assumed. -/
theorem closure_image_inter_basicOpen_snd_eq_biUnion_le_nilpotentOrbit
    (O : {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    closure O.val.image ∩
        (AlgebraicGeometry.Proj.basicOpen
          (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : {O' : VectorOrbit k H 𝔤 // O'.IsNilpotentAd} | O' ≤ O}, O'.val.image := by
  rw [closure_image_inter_basicOpen_snd_eq_biUnion_le (finite_setOf_le_of_isNilpotentAd O.property)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Subtype.exists, exists_prop]
  exact ⟨fun ⟨O', hle, hx⟩ ↦ ⟨O', O.property.of_le hle, hle, hx⟩,
    fun ⟨O', _, hle, hx⟩ ↦ ⟨O', hle, hx⟩⟩

/-- **Orbit boundary decomposition for nilpotent orbits.** Inside the affine chart `𝔤 = {t ≠ 0}` of
`P(𝔤 × k)`, the boundary `closure O \ O` of a nilpotent adjoint orbit `O` is the finite union of
the scheme-point orbit images of all strictly smaller nilpotent orbits `O' < O`, indexed by the
nilpotent orbit subtype. No connectedness of `G` is assumed. -/
theorem closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt_nilpotentOrbit
    (O : {O : VectorOrbit k H 𝔤 // O.IsNilpotentAd}) :
    (closure O.val.image \ O.val.image) ∩
        (AlgebraicGeometry.Proj.basicOpen
          (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k (𝔤 × k)))
          (SymmetricAlgebra.ι k (Module.Dual k (𝔤 × k)) (LinearMap.snd k 𝔤 k)) : Set _) =
      ⋃ O' ∈ {O' : {O' : VectorOrbit k H 𝔤 // O'.IsNilpotentAd} | O' < O}, O'.val.image := by
  rw [closure_image_sdiff_inter_basicOpen_snd_eq_biUnion_lt
    (finite_setOf_le_of_isNilpotentAd O.property)]
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Subtype.exists, exists_prop]
  exact ⟨fun ⟨O', hlt, hx⟩ ↦ ⟨O', O.property.of_le hlt.le, hlt, hx⟩,
    fun ⟨O', _, hlt, hx⟩ ↦ ⟨O', hlt, hx⟩⟩

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

/-- Auxiliary map sending `none` to the zero nilpotent orbit and `some h` to the nilpotent orbit of
a nilpositive partner of `h ∈ b.dominantNeutralElements`. -/
private noncomputable def optionDominantToNilpotentOrbit
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Option b.dominantNeutralElements → {O : Comodule.VectorOrbit k H 𝔤 // O.IsNilpotentAd}
  | none => ⟨Comodule.VectorOrbit.mk 0, Comodule.VectorOrbit.isNilpotentAd_mk_zero⟩
  | some h =>
    ⟨TauCeti.dominantNilpotentOrbit (H := H) b h,
      ((TauCeti.range_dominantNilpotentOrbit_eq (H := H) b).subset
        (Set.mem_range_self h)).1⟩

private theorem optionDominantToNilpotentOrbit_bijective
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Bijective (b.optionDominantToNilpotentOrbit (H := H)) := by
  constructor
  · rintro (_ | h₁) (_ | h₂) heq
    · rfl
    · exfalso
      exact ((TauCeti.range_dominantNilpotentOrbit_eq (H := H) b).subset
        (Set.mem_range_self h₂)).2 (congrArg Subtype.val heq).symm
    · exfalso
      exact ((TauCeti.range_dominantNilpotentOrbit_eq (H := H) b).subset
        (Set.mem_range_self h₁)).2 (congrArg Subtype.val heq)
    · congr 1
      obtain ⟨f₁, t₁⟩ :=
        Classical.choose_spec ((b.mem_dominantNeutralElements_iff h₁.val).mp h₁.property).1
      obtain ⟨f₂, t₂⟩ :=
        Classical.choose_spec ((b.mem_dominantNeutralElements_iff h₂.val).mp h₂.property).1
      obtain ⟨g, hge⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp (congrArg Subtype.val heq)
      exact Subtype.ext
        (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
          (H := H) b t₂ h₁.property h₂.property hge)
  · rintro ⟨O, hO⟩
    by_cases h0 : O = Comodule.VectorOrbit.mk 0
    · exact ⟨none, Subtype.ext h0.symm⟩
    · obtain ⟨h, hh⟩ : O ∈ Set.range (TauCeti.dominantNilpotentOrbit (H := H) b) := by
        rw [TauCeti.range_dominantNilpotentOrbit_eq]
        exact ⟨hO, h0⟩
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
    TauCeti.dominantNilpotentOrbit_eq_mk_of_isSl2Triple (H := H) b h t

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

end Connected
