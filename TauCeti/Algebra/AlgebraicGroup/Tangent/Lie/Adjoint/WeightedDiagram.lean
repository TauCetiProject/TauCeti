/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone
public import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Finite
import Mathlib.Data.Set.Card
import TauCeti.Algebra.AlgebraicGroup.Representation.Orbit.ClosureOrder
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Exponential
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Dominant
import TauCeti.Algebra.Lie.Sl2.WeightedDiagram.Uniqueness

/-!
# Classification and finiteness of nilpotent orbits by weighted Dynkin diagrams

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero, with Killing Lie algebra `𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)`,
Cartan subalgebra `𝔥`, and root-system base `b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base`.

Combining the grade-two centralizer openness (`IsSl2Triple.range_projectiveOrbitMap_adjoint_eq`),
the exponential subgroup realization of `Int(𝔤)` inside `G⁰(k)`
(`TauCeti.exists_mem_quotientPointsSubgroup_bot_identityComponent_of_mem_intLieAlgebra`), and the
uniqueness of dominant neutral elements under invariant-preserving Lie automorphisms
(`IsSl2Triple.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq`) yields the Dynkin–Kostant
parametrization of nilpotent `G`-orbits:

1. **Without connectedness of `G`:** Every dominant neutral element `h ∈ b.dominantNeutralElements`
   determines a well-defined nonzero rational adjoint orbit `b.dominantVectorOrbit h`
   (`RootPairing.Base.dominantVectorOrbit`), independent of the choice of nilpositive partner `e`.
   Every `sl₂` triple in `𝔤` is conjugate under `G⁰(k)` to one with neutral element in
   `b.dominantNeutralElements`
   (`IsSl2Triple.exists_mem_quotientPointsSubgroup_bot_identityComponent_dominantNeutralElements`),
   so `b.dominantVectorOrbit` surjects onto the nonzero nilpotent `G`-orbits. Consequently `G`
   has only finitely many nilpotent orbits in `𝔤`
   (`TauCeti.finite_image_vectorOrbit_mk_setOf_isNilpotent_ad`), at most `3 ^ finrank k 𝔥` nonzero
   ones and at most `3 ^ finrank k 𝔥 + 1` in total.
2. **For connected `G`:** Group invariants and Lie invariants in `Sym(𝔤*)` coincide
   (`TauCeti.lift_eval_basePointsRepresentation_of_mem_lieInvariants`), so every rational point of
   `G` preserves values of `S(𝔤*)^𝔤`. Hence `b.dominantVectorOrbit` is injective
   (`RootPairing.Base.dominantVectorOrbit_injective`): two `sl₂` triples with dominant neutral
   elements have `G(k)`-conjugate nilpositive elements—and identical geometric orbit images in
   `P(𝔤 × k)`—if and only if their weighted Dynkin diagrams agree
   (`IsSl2Triple.vectorOrbit_mk_eq_iff_weightedDynkinDiagram_eq`,
   `IsSl2Triple.range_projectiveOrbitMap_adjoint_eq_iff_weightedDynkinDiagram_eq`). Every nonzero
   `ad`-nilpotent element determines a unique dominant neutral element, and the number of nilpotent
   `G`-orbits (equivalently, rational `G`-orbits on the nilpotent cone) is
   `b.dominantNeutralElements.ncard + 1`.

## Main declarations

* `RootPairing.Base.dominantVectorOrbit` and `RootPairing.Base.dominantVectorOrbit_eq_mk`: the
  rational adjoint `G`-orbit attached to a dominant neutral element.
* `IsSl2Triple.exists_mem_quotientPointsSubgroup_bot_identityComponent_dominantNeutralElements` and
  `TauCeti.exists_mem_quotientPointsSubgroup_bot_identityComponent_isSl2Triple_of_isNilpotent_ad`:
  `G⁰(k)`-conjugacy of `sl₂` triples and nonzero nilpotent elements into the dominant chamber.
* `RootPairing.Base.range_dominantVectorOrbit`,
  `TauCeti.finite_image_vectorOrbit_mk_setOf_isNilpotent_ad`, and
  `TauCeti.ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_le`: finiteness and rank-exponential
  bound on nilpotent `G`-orbits (without assuming `G` connected).
* `RootPairing.Base.dominantVectorOrbit_injective`,
  `IsSl2Triple.vectorOrbit_mk_eq_iff_weightedDynkinDiagram_eq`,
  `IsSl2Triple.range_projectiveOrbitMap_adjoint_eq_iff_weightedDynkinDiagram_eq`,
  `TauCeti.existsUnique_mem_dominantNeutralElements_exists_basePointsRepresentation_isSl2Triple`,
  `TauCeti.ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_eq`, and
  `TauCeti.ncard_image_vectorOrbit_mk_nilpotentCone_eq`: complete weighted-Dynkin-diagram
  classification and exact orbit count when `G` is connected.

## References

* E. B. Dynkin, *Semisimple subalgebras of semisimple Lie algebras*, Mat. Sb. **30** (1952),
  349–462; Amer. Math. Soc. Transl. (2) **6** (1957), 111–244.
* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §4.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Theorems 3.2.10 and 3.5.4.
-/

public section

open CategoryTheory TauCeti WithConv

universe u

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial
attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

section FiniteType

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

/-- Two `sl₂` triples in `Lie(G)` sharing their neutral element have nilpositive elements in the
same rational adjoint `G`-orbit. -/
theorem vectorOrbit_mk_eq {h e f e' f' : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') :
    Comodule.VectorOrbit.mk (k := k) (H := H) e =
      Comodule.VectorOrbit.mk (k := k) (H := H) e' := by
  obtain ⟨g, -, -, rfl, -⟩ :=
    t.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t'
  exact (Comodule.VectorOrbit.mk_basePointsRepresentation g e).symm

/-- Two `sl₂` triples with dominant neutral elements and equal weighted Dynkin diagrams have
nilpositive elements in the same rational adjoint `G`-orbit. -/
theorem vectorOrbit_mk_eq_of_weightedDynkinDiagram_eq
    [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    {b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base} {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t₁ : IsSl2Triple (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₂ f₂)
    (hdiag : b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂) :
    Comodule.VectorOrbit.mk (k := k) (H := H) e₁ =
      Comodule.VectorOrbit.mk (k := k) (H := H) e₂ := by
  obtain rfl := b.weightedDynkinDiagram_injective hdiag
  exact t₁.vectorOrbit_mk_eq t₂

end FiniteType

end IsSl2Triple

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
  Comodule.VectorOrbit.mk (((b.mem_dominantNeutralElements_iff h.1).mp h.2).1.choose)

/-- For any `sl₂` triple `(h, e, f)` with `h ∈ b.dominantNeutralElements`, `b.dominantVectorOrbit`
is the rational adjoint orbit of `e`. -/
theorem dominantVectorOrbit_eq_mk (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h : b.dominantNeutralElements} {e f : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t : IsSl2Triple (h : Module.Dual k (Bialgebra.CotangentSpace k H)) e f) :
    b.dominantVectorOrbit h = Comodule.VectorOrbit.mk (k := k) (H := H) e := by
  have hex := ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  exact hex.choose_spec.choose_spec.vectorOrbit_mk_eq t

/-- A dominant nilpotent orbit is never the zero orbit. -/
theorem dominantVectorOrbit_ne_mk_zero (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    (h : b.dominantNeutralElements) :
    b.dominantVectorOrbit h ≠ Comodule.VectorOrbit.mk (k := k) (H := H) 0 := by
  obtain ⟨e, f, t⟩ := ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
  rw [b.dominantVectorOrbit_eq_mk t]
  intro h0
  obtain ⟨g, hg⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp h0.symm
  rw [map_zero] at hg
  exact t.e_ne_zero hg.symm

end FiniteType

end RootPairing.Base

namespace IsSl2Triple

section IdentityComponent

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

/-- **Every `sl₂` triple is `G⁰(k)`-conjugate to one with dominant neutral element.** -/
theorem exists_mem_quotientPointsSubgroup_bot_identityComponent_dominantNeutralElements
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {h e f : Module.Dual k (Bialgebra.CotangentSpace k H)} (t : IsSl2Triple h e f) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj (⊥ : HopfIdeal k H).identityComponent
        (CommAlgCat.of k k),
      ∃ h₀ ∈ b.dominantNeutralElements,
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h =
          (h₀ : Module.Dual k (Bialgebra.CotangentSpace k H)) ∧
          IsSl2Triple (h₀ : Module.Dual k (Bialgebra.CotangentSpace k H))
            (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e)
            (Comodule.basePointsRepresentation
              (Module.Dual k (Bialgebra.CotangentSpace k H)) g f) := by
  let _ : LieAlgebra ℚ (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    { lie_smul := fun q x y ↦ map_rat_smul (LieAlgebra.ad k _ x) q y }
  obtain ⟨γ, hγ, h₀, hh₀, hγh, t'⟩ :=
    t.exists_mem_intLieAlgebra_smul_mem_dominantNeutralElements_of_isAlgClosed b
  obtain ⟨g, hg, hgγ⟩ :=
    exists_mem_quotientPointsSubgroup_bot_identityComponent_of_mem_intLieAlgebra hγ
  refine ⟨g, hg, h₀, hh₀, (hgγ h).trans hγh, ?_⟩
  rwa [hgγ e, hgγ f]

end IdentityComponent

end IsSl2Triple

namespace RootPairing.Base

section Surjective

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

/-- **Dominant neutral elements surject onto nonzero nilpotent `G`-orbits.** No connectedness
assumption on `G` is needed: `G⁰(k)` already conjugates every triple into the dominant chamber. -/
theorem range_dominantVectorOrbit (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Set.range b.dominantVectorOrbit =
      Comodule.VectorOrbit.mk (k := k) (H := H) ''
        {e : Module.Dual k (Bialgebra.CotangentSpace k H) | ∃ h f, IsSl2Triple h e f} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨h, rfl⟩
    obtain ⟨e, f, t⟩ := ((b.mem_dominantNeutralElements_iff h.1).mp h.2).1
    exact ⟨e, ⟨h, f, t⟩, (b.dominantVectorOrbit_eq_mk t).symm⟩
  · rintro _ ⟨e, ⟨h, f, t⟩, rfl⟩
    obtain ⟨g, -, h₀, hh₀, -, t'⟩ :=
      t.exists_mem_quotientPointsSubgroup_bot_identityComponent_dominantNeutralElements b
    refine ⟨⟨h₀, hh₀⟩, ?_⟩
    rw [b.dominantVectorOrbit_eq_mk t', Comodule.VectorOrbit.mk_basePointsRepresentation]

/-- **All nilpotent `G`-orbits are the zero orbit together with the dominant nilpotent orbits.** -/
theorem insert_mk_zero_range_dominantVectorOrbit (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    insert (Comodule.VectorOrbit.mk (k := k) (H := H) 0) (Set.range b.dominantVectorOrbit) =
      Comodule.VectorOrbit.mk (k := k) (H := H) ''
        {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
          IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)} := by
  rw [b.range_dominantVectorOrbit, ← Set.image_insert_eq]
  congr 1
  ext e
  rcases eq_or_ne e 0 with rfl | he0
  · simp [exists_isSl2Triple_iff (K := k), IsNilpotent.zero]
  · simp [exists_isSl2Triple_iff (K := k), he0]

end Surjective

end RootPairing.Base

namespace TauCeti

section FiniteOrbits

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **Every nonzero `ad`-nilpotent element is `G⁰(k)`-conjugate to the nilpositive element of a
dominant `sl₂` triple.** -/
theorem exists_mem_quotientPointsSubgroup_bot_identityComponent_isSl2Triple_of_isNilpotent_ad
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj (⊥ : HopfIdeal k H).identityComponent
        (CommAlgCat.of k k),
      ∃ h₀ ∈ b.dominantNeutralElements, ∃ f : Module.Dual k (Bialgebra.CotangentSpace k H),
        IsSl2Triple (h₀ : Module.Dual k (Bialgebra.CotangentSpace k H))
          (Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g e) f := by
  obtain ⟨h, f, t⟩ := exists_isSl2Triple_of_isNilpotent_ad he he0
  obtain ⟨g, hg, h₀, hh₀, -, t'⟩ :=
    t.exists_mem_quotientPointsSubgroup_bot_identityComponent_dominantNeutralElements b
  exact ⟨g, hg, h₀, hh₀, _, t'⟩

variable (H) in
/-- **Finiteness of nonzero nilpotent `G`-orbits.** -/
theorem finite_image_vectorOrbit_mk_setOf_exists_isSl2Triple :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) | ∃ h f, IsSl2Triple h e f}).Finite := by
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k
    (Module.Dual k (Bialgebra.CotangentSpace k H))
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  rw [← b.range_dominantVectorOrbit]
  exact Set.finite_range _

variable (H) in
/-- **Finiteness of nilpotent `G`-orbits.** An affine group of finite type with Killing Lie
algebra over an algebraically closed field of characteristic zero has only finitely many rational
nilpotent orbits in its Lie algebra (no connectedness hypothesis is required). -/
theorem finite_image_vectorOrbit_mk_setOf_isNilpotent_ad :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).Finite := by
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel k
    (Module.Dual k (Bialgebra.CotangentSpace k H))
  let b := (LieAlgebra.IsKilling.rootSystem (LieSubalgebra.engel k x)).nonempty_base.some
  rw [← b.insert_mk_zero_range_dominantVectorOrbit]
  exact (Set.finite_range _).insert _

/-- **Bound on the number of nonzero nilpotent `G`-orbits.** There are at most `3 ^ finrank k 𝔥`
nonzero nilpotent `G`-orbits, for any Cartan subalgebra `𝔥`. -/
theorem ncard_image_vectorOrbit_mk_setOf_exists_isSl2Triple_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) | ∃ h f, IsSl2Triple h e f}).ncard ≤
      3 ^ Module.finrank k 𝔥 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  rw [← b.range_dominantVectorOrbit, ← Set.image_univ]
  refine (Set.ncard_image_le Set.finite_univ).trans ?_
  rw [Set.ncard_univ, Nat.card_coe_set_eq]
  exact b.ncard_dominantNeutralElements_le

/-- **Bound on the total number of nilpotent `G`-orbits.** Including the zero orbit, there are at
most `3 ^ finrank k 𝔥 + 1` nilpotent `G`-orbits. -/
theorem ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_le
    (𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))) [𝔥.IsCartanSubalgebra] :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).ncard ≤
      3 ^ Module.finrank k 𝔥 + 1 := by
  let b := (LieAlgebra.IsKilling.rootSystem 𝔥).nonempty_base.some
  rw [← b.insert_mk_zero_range_dominantVectorOrbit]
  refine (Set.ncard_insert_le _ _).trans ?_
  rw [b.range_dominantVectorOrbit]
  exact Nat.add_le_add_right (ncard_image_vectorOrbit_mk_setOf_exists_isSl2Triple_le 𝔥) 1

end FiniteOrbits

end TauCeti

section Connected

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]
  {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]

namespace IsSl2Triple

/-- **Uniqueness of the dominant neutral element on a connected group's adjoint orbit.** If `G` is
connected and a rational point `g ∈ G(k)` carries `e₁` to `e₂` for two `sl₂` triples with dominant
neutral elements `h₁, h₂ ∈ b.dominantNeutralElements`, then `h₁ = h₂`. -/
theorem eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) {h₁ h₂ : 𝔥}
    {e₁ f₁ e₂ f₂ : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t₁ : IsSl2Triple (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₂ f₂)
    (hh₁ : h₁ ∈ b.dominantNeutralElements) (hh₂ : h₂ ∈ b.dominantNeutralElements)
    {g : WithConv (H →ₐ[k] k)}
    (hge : Comodule.basePointsRepresentation
      (Module.Dual k (Bialgebra.CotangentSpace k H)) g e₁ = e₂) :
    h₁ = h₂ :=
  t₁.eq_of_mem_dominantNeutralElements_of_lieEquiv_apply_eq b t₂ hh₁ hh₂
    (Derivation.basePointsAdjointLieEquiv (R := k) (H := H) g) (by simpa using hge)
    (fun _ hp ↦ by simpa using lift_eval_basePointsRepresentation_of_mem_lieInvariants hp g _)

/-- **Two dominant `sl₂` triples of a connected group have the same nilpotent `G`-orbit if and only
if their neutral elements coincide.** -/
theorem vectorOrbit_mk_eq_iff_eq {b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base}
    {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t₁ : IsSl2Triple (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₂ f₂) :
    Comodule.VectorOrbit.mk (k := k) (H := H) e₁ =
      Comodule.VectorOrbit.mk (k := k) (H := H) e₂ ↔ h₁ = h₂ := by
  refine ⟨fun horb ↦ ?_, ?_⟩
  · obtain ⟨g, hge⟩ := Comodule.VectorOrbit.mk_eq_mk_iff.mp horb
    exact Subtype.ext
      (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq b t₂ h₁.2 h₂.2 hge)
  · rintro rfl
    exact t₁.vectorOrbit_mk_eq t₂

/-- **Weighted Dynkin diagram classification of nilpotent `G`-orbits.** For a connected Killing
affine group `G`, two `sl₂` triples with dominant neutral elements have nilpositive elements in the
same rational `G`-orbit if and only if their weighted Dynkin diagrams coincide. -/
theorem vectorOrbit_mk_eq_iff_weightedDynkinDiagram_eq
    {b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base} {h₁ h₂ : b.dominantNeutralElements}
    {e₁ f₁ e₂ f₂ : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (t₁ : IsSl2Triple (h₁ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₁ f₁)
    (t₂ : IsSl2Triple (h₂ : Module.Dual k (Bialgebra.CotangentSpace k H)) e₂ f₂) :
    Comodule.VectorOrbit.mk (k := k) (H := H) e₁ =
      Comodule.VectorOrbit.mk (k := k) (H := H) e₂ ↔
      b.weightedDynkinDiagram h₁ = b.weightedDynkinDiagram h₂ :=
  (t₁.vectorOrbit_mk_eq_iff_eq t₂).trans b.weightedDynkinDiagram_injective.eq_iff.symm

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
    Comodule.VectorOrbit.image_injective.eq_iff]
  exact t₁.vectorOrbit_mk_eq_iff_weightedDynkinDiagram_eq t₂

end IsSl2Triple

namespace RootPairing.Base

/-- **Distinct dominant neutral elements give distinct nilpotent `G`-orbits when `G` is
connected.** -/
theorem dominantVectorOrbit_injective (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    Function.Injective b.dominantVectorOrbit := by
  intro h₁ h₂ horb
  obtain ⟨e₁, f₁, t₁⟩ := ((b.mem_dominantNeutralElements_iff h₁.1).mp h₁.2).1
  obtain ⟨e₂, f₂, t₂⟩ := ((b.mem_dominantNeutralElements_iff h₂.1).mp h₂.2).1
  rw [b.dominantVectorOrbit_eq_mk t₁, b.dominantVectorOrbit_eq_mk t₂] at horb
  exact (t₁.vectorOrbit_mk_eq_iff_eq t₂).mp horb

/-- **Every nonzero nilpotent element of a connected Killing group lies in the orbit of a unique
dominant neutral element.** -/
theorem existsUnique_dominantVectorOrbit_eq_of_isNilpotent_ad
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃! h : b.dominantNeutralElements,
      b.dominantVectorOrbit h = Comodule.VectorOrbit.mk (k := k) (H := H) e := by
  obtain ⟨g, -, h₀, hh₀, f, t⟩ :=
    exists_mem_quotientPointsSubgroup_bot_identityComponent_isSl2Triple_of_isNilpotent_ad b he he0
  refine ⟨⟨h₀, hh₀⟩, ?_, fun h' hh' ↦ ?_⟩
  · dsimp only
    rw [b.dominantVectorOrbit_eq_mk (h := ⟨h₀, hh₀⟩) t,
      Comodule.VectorOrbit.mk_basePointsRepresentation]
  · refine b.dominantVectorOrbit_injective (hh'.trans ?_)
    rw [b.dominantVectorOrbit_eq_mk (h := ⟨h₀, hh₀⟩) t,
      Comodule.VectorOrbit.mk_basePointsRepresentation]

end RootPairing.Base

namespace TauCeti

/-- **Uniqueness of the dominant neutral element attached to a nonzero nilpotent element under
`G(k)`-conjugacy.** -/
theorem existsUnique_mem_dominantNeutralElements_exists_basePointsRepresentation_isSl2Triple
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base)
    {e : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (he : IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e))
    (he0 : e ≠ 0) :
    ∃! h : 𝔥, h ∈ b.dominantNeutralElements ∧
      ∃ g : WithConv (H →ₐ[k] k), ∃ f : Module.Dual k (Bialgebra.CotangentSpace k H),
        IsSl2Triple (h : Module.Dual k (Bialgebra.CotangentSpace k H))
          (Comodule.basePointsRepresentation
            (Module.Dual k (Bialgebra.CotangentSpace k H)) g e) f := by
  obtain ⟨g₁, -, h₁, hh₁, f₁, t₁⟩ :=
    exists_mem_quotientPointsSubgroup_bot_identityComponent_isSl2Triple_of_isNilpotent_ad b he he0
  refine ⟨h₁, ⟨hh₁, g₁, f₁, t₁⟩, ?_⟩
  rintro h₂ ⟨hh₂, g₂, f₂, t₂⟩
  refine (t₁.eq_of_mem_dominantNeutralElements_of_basePointsRepresentation_eq b t₂ hh₁ hh₂
    (g := g₂ * g₁⁻¹) ?_).symm
  rw [map_mul, mul_apply_eq_comp, Representation.inv_self_apply]

/-- **Exact count of nonzero nilpotent `G`-orbits for a connected Killing group.** -/
theorem ncard_image_vectorOrbit_mk_setOf_exists_isSl2Triple_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) | ∃ h f, IsSl2Triple h e f}).ncard =
      b.dominantNeutralElements.ncard := by
  rw [← b.range_dominantVectorOrbit,
    Set.ncard_range_of_injective b.dominantVectorOrbit_injective, Nat.card_coe_set_eq]

/-- **Exact count of nilpotent `G`-orbits for a connected Killing group.** Together with the zero
orbit, the nilpotent `G`-orbits are in bijection with `Option b.dominantNeutralElements`. -/
theorem ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_eq
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
        IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)}).ncard =
      b.dominantNeutralElements.ncard + 1 := by
  have hnotMem : Comodule.VectorOrbit.mk (k := k) (H := H)
      (0 : Module.Dual k (Bialgebra.CotangentSpace k H)) ∉ Set.range b.dominantVectorOrbit := by
    rintro ⟨h, hh⟩
    exact b.dominantVectorOrbit_ne_mk_zero h hh
  rw [← b.insert_mk_zero_range_dominantVectorOrbit,
    Set.ncard_insert_of_notMem hnotMem (Set.finite_range _),
    Set.ncard_range_of_injective b.dominantVectorOrbit_injective, Nat.card_coe_set_eq]

end TauCeti

end Connected

namespace TauCeti

section NilpotentCone

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  (H : FiniteTypeCommHopfAlgCat.{u, u} k) [ConnectedSpace (PrimeSpectrum H)]
  [LieAlgebra.IsKilling k (Module.Dual k (Bialgebra.CotangentSpace k H))]

/-- **Rational `G`-orbits on the nilpotent cone.** For a connected Killing group, the rational
orbits of `k`-points of the nilpotent cone are the nilpotent `G`-orbits. -/
theorem image_vectorOrbit_mk_nilpotentCone :
    Comodule.VectorOrbit.mk (k := k) (H := H) ''
        {x : Module.Dual k (Bialgebra.CotangentSpace k H) |
          nilpotentConeIdeal k H ≤
            RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k _ x))} =
      Comodule.VectorOrbit.mk (k := k) (H := H) ''
        {e : Module.Dual k (Bialgebra.CotangentSpace k H) |
          IsNilpotent (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) e)} := by
  congr 1
  ext x
  exact nilpotentConeIdeal_le_ker_lift_eval_iff

/-- **Finiteness of rational `G`-orbits on the nilpotent cone.** -/
theorem finite_image_vectorOrbit_mk_nilpotentCone :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {x : Module.Dual k (Bialgebra.CotangentSpace k H) |
        nilpotentConeIdeal k H ≤
          RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k _ x))}).Finite := by
  rw [image_vectorOrbit_mk_nilpotentCone H]
  exact finite_image_vectorOrbit_mk_setOf_isNilpotent_ad H

variable {H}

/-- **Exact count of rational `G`-orbits on the nilpotent cone.** -/
theorem ncard_image_vectorOrbit_mk_nilpotentCone_eq
    {𝔥 : LieSubalgebra k (Module.Dual k (Bialgebra.CotangentSpace k H))} [𝔥.IsCartanSubalgebra]
    (b : (LieAlgebra.IsKilling.rootSystem 𝔥).Base) :
    (Comodule.VectorOrbit.mk (k := k) (H := H) ''
      {x : Module.Dual k (Bialgebra.CotangentSpace k H) |
        nilpotentConeIdeal k H ≤
          RingHom.ker (SymmetricAlgebra.lift (Module.Dual.eval k _ x))}).ncard =
      b.dominantNeutralElements.ncard + 1 := by
  rw [image_vectorOrbit_mk_nilpotentCone H]
  exact ncard_image_vectorOrbit_mk_setOf_isNilpotent_ad_eq b

end NilpotentCone

end TauCeti
