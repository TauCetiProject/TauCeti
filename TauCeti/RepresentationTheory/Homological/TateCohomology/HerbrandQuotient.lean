/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Periodic
public import TauCeti.LinearAlgebra.LinearMap.Cardinality
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import TauCeti.RepresentationTheory.Invariants

/-!
# Herbrand quotients of finite cyclic group representations

For a representation `M` of a finite cyclic group, its Herbrand quotient is the quotient of the
orders of `H-hat^0(G, M)` and `H-hat^(-1)(G, M)`. This file defines it directly on Mathlib's
Tate-cohomology carrier, on top of the low-degree descriptions

`H-hat^0(G, M) = M^G / N M` and `H-hat^(-1)(G, M) = ker(N) / I_G M`,

and proves its two base calculations: the quotient is `1` for a finite module, and it is `|G|`
for the trivial integral representation.

It then proves that the Herbrand quotient is **multiplicative in a short exact sequence**. The
argument is the classical exact hexagon: the periodic chain complex of
`TauCeti.RepresentationTheory.Homological.TateCohomology.Periodic` is a functor of the
coefficients, so a short exact sequence of representations gives a short exact sequence of
complexes and hence a long exact sequence of homology groups, which alternates between the
degree-`0` and the degree-`-1` Tate groups; naturality of the periodicity in odd degrees splices
that sequence into a cycle of six maps. Counting each of the six groups against the image of the
map leaving it and the image of the map entering it gives the identity
`|Ĥ⁰(X₁)| |Ĥ⁰(X₃)| |Ĥ⁻¹(X₂)| = |Ĥ⁻¹(X₁)| |Ĥ⁻¹(X₃)| |Ĥ⁰(X₂)|`, which is multiplicativity once the
degree-`-1` orders are known to be nonzero.

The proofs are adapted to Mathlib's current Tate complex from the corresponding calculations in
`ClassFieldTheory/Cohomology/FiniteCyclic/HerbrandQuotient/{Defs,Finite,Trivial}.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`. The trivial
integral calculation reads off the low-degree evaluations
`natCard_tateCohomology_zero_trivial_int_eq_card` and
`subsingleton_tateCohomology_negOne_trivial_int`.

## Main definitions

* `TauCeti.TateCohomology.herbrandQuotient` is the Herbrand quotient.
* `TauCeti.TateCohomology.herbrandQuotient_eq_one_of_finite` computes it for a finite module.
* `TauCeti.TateCohomology.herbrandQuotient_trivial_int_eq_card` computes it for trivial integral
  coefficients.

## Main results

* `TauCeti.TateCohomology.natCard_tateCohomology_mul_of_shortExact`: the exact hexagon of a short
  exact sequence, in the form of an identity between two products of three orders. It assumes no
  finiteness.
* `TauCeti.TateCohomology.natCard_tateCohomology_negOne_dvd_of_shortExact`: the order of the
  middle degree-`-1` Tate group divides the product of the two outer ones.
* `TauCeti.TateCohomology.herbrandQuotient_eq_mul_of_shortExact`: **multiplicativity of the
  Herbrand quotient** in a short exact sequence whose outer terms have finite degree-`-1` Tate
  cohomology.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, section 4.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IX, section 4.
-/

public noncomputable section

universe u

open CategoryTheory groupCohomology groupHomology LinearMap Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The Herbrand quotient, the order of degree-zero Tate cohomology divided by the order of
degree `-1` Tate cohomology. Classically the invariant is only defined when both Tate groups are
finite; this definition is totalized by `Nat.card`, which is `0` on an infinite type, so together
with division by zero it returns `0` as soon as either group is infinite. The definition makes
sense for any finite group; periodicity makes it useful for cyclic groups. -/
def herbrandQuotient (M : Rep R G) : ℚ :=
  Nat.card (tateCohomology M 0) / Nat.card (tateCohomology M (-1))

/-- The Herbrand quotient is the ratio of the orders of degree zero and degree `-1` Tate
cohomology. This unfolding equation is deliberately not `@[simp]`: the terminating evaluations
below keep `herbrandQuotient` as their left-hand side, and unfolding it first would make each of
them non-simp-normal. -/
theorem herbrandQuotient_def (M : Rep R G) :
    herbrandQuotient M =
      Nat.card (tateCohomology M 0) / Nat.card (tateCohomology M (-1)) := by
  simp [herbrandQuotient]

/-- The Herbrand quotient vanishes exactly when one of its two defining Tate groups is infinite. -/
@[simp]
theorem herbrandQuotient_eq_zero_iff {M : Rep R G} :
    herbrandQuotient M = 0 ↔
      Infinite (tateCohomology M 0) ∨ Infinite (tateCohomology M (-1)) := by
  simp [herbrandQuotient_def, Nat.card_eq_zero]

/-- The Herbrand quotient of a finite representation of a finite cyclic group is one. -/
@[simp]
theorem herbrandQuotient_eq_one_of_finite [IsCyclic G] (M : Rep R G) [Finite M] :
    herbrandQuotient M = 1 := by
  let hgen := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  let g := hgen.choose
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x ↦
    hgen.choose_spec.ge (Subgroup.mem_top x)
  let D : Module.End R M := M.ρ g - LinearMap.id
  have hinv : M.ρ.invariants = ker D := by
    simpa [D, sub_hom, applyAsHom] using
      Rep.FiniteCyclicGroup.invariants_eq_ker_apply_sub M g hg
  have hcoinv : Representation.Coinvariants.ker M.ρ = range D := by
    simpa only [D] using Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg
  have hnorm_le : range M.ρ.norm ≤ M.ρ.invariants := by
    rintro _ ⟨x, rfl⟩
    exact fun a ↦ M.ρ.self_norm_apply a x
  have hzero :
      Nat.card M.ρ.invariants =
        Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
    calc
      Nat.card M.ρ.invariants =
          Nat.card ((range M.ρ.norm).submoduleOf M.ρ.invariants) *
            Nat.card (M.ρ.invariants ⧸
              (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe hnorm_le).toEquiv,
          ← Nat.card_congr (H0IsoNormQuotient M).toLinearEquiv.toEquiv]
  have hnegone :
      Nat.card (ker M.ρ.norm) =
        Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
    calc
      Nat.card (ker M.ρ.norm) =
          Nat.card ((Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) *
            Nat.card (ker M.ρ.norm ⧸
              (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe (by
          rw [← range_d₁₀_eq_coinvariantsKer]
          exact LinearMap.range_le_ker_iff.mpr
            (ModuleCat.hom_ext_iff.mp (Rep.comp_eq_zero M)))).toEquiv,
          ← Nat.card_congr (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv]
  have hcard (f : Module.End R M) :
      Nat.card M = Nat.card (ker f) * Nat.card (range f) := by
    rw [card_eq_card_range_mul_card_ker f, Nat.mul_comm]
  have hnorm := hcard M.ρ.norm
  have hdiff := hcard D
  have hrangeNorm : 0 < Nat.card (range M.ρ.norm) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hrangeDiff : 0 < Nat.card (range D) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hcard : Nat.card (tateCohomology M 0) = Nat.card (tateCohomology M (-1)) := by
    apply Nat.mul_right_cancel (Nat.mul_pos hrangeNorm hrangeDiff)
    calc
      Nat.card (tateCohomology M 0) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) =
          (Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0)) *
            Nat.card (range D) := by ac_rfl
      _ = Nat.card (ker D) * Nat.card (range D) := by rw [← hzero, hinv]
      _ = Nat.card M := hdiff.symm
      _ = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := hnorm
      _ = (Nat.card (range D) * Nat.card (tateCohomology M (-1))) *
          Nat.card (range M.ρ.norm) := by rw [hnegone, hcoinv]
      _ = Nat.card (tateCohomology M (-1)) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) := by ac_rfl
  have hfiniteQuotient : Finite (ker M.ρ.norm ⧸
      (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
    Finite.of_surjective (Submodule.mkQ _ ) (Submodule.mkQ_surjective _)
  have hfiniteNegOne : Finite (tateCohomology M (-1)) :=
    (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv.finite_iff.mpr hfiniteQuotient
  rw [herbrandQuotient_def, hcard]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨0⟩, hfiniteNegOne⟩))

section TrivialInt

variable (H : Type) [Group H] [Fintype H]

/-- The Herbrand quotient of the trivial integral representation is the order of the finite
group. -/
@[simp]
theorem herbrandQuotient_trivial_int_eq_card :
    herbrandQuotient (Rep.trivial ℤ H ℤ) = Nat.card H := by
  let hsub := subsingleton_tateCohomology_negOne_trivial_int H
  rw [herbrandQuotient_def, natCard_tateCohomology_zero_trivial_int_eq_card]
  rw [@Nat.card_of_subsingleton _ 0 hsub]
  simp

end TrivialInt

section ShortExact

open Rep.FiniteCyclicGroup

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The six cardinalities produced by the exact hexagon of a short exact sequence of
representations of a finite cyclic group.

Splicing the long exact sequence of the periodic chain complex against its two-periodicity turns
it into a cycle of six maps through the Tate groups of degrees `0` and `-1` of the three
representations. Writing `rᵢ`, `sᵢ` and `tᵢ` for the cardinalities of the images of those six
maps, each of the six Tate groups is an extension of the image of the map leaving it by the image
of the map entering it. The six equations below are exactly that statement, and they are all this
file uses about the hexagon. -/
private theorem exists_hexagon_natCard {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ r₁ r₂ s₁ s₂ t₁ t₂ : ℕ,
      Nat.card (tateCohomology S.X₁ 0) = r₁ * t₁ ∧
        Nat.card (tateCohomology S.X₁ (-1)) = r₂ * t₂ ∧
        Nat.card (tateCohomology S.X₃ 0) = t₂ * s₁ ∧
        Nat.card (tateCohomology S.X₃ (-1)) = t₁ * s₂ ∧
        Nat.card (tateCohomology S.X₂ 0) = s₁ * r₁ ∧
        Nat.card (tateCohomology S.X₂ (-1)) = s₂ * r₂ := by
  have hT := map_periodicFunctor_shortExact g hS
  -- the left-hand term of the sequence is an extension of the image of the connecting map
  have ha : ∀ (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j),
      Nat.card (((periodicFunctor R g).obj S.X₁).homology j) =
        Nat.card (range (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).f j))) *
          Nat.card (range (ModuleCat.Hom.hom (hT.δ i j hij))) := by
    intro i j hij
    have h := card_eq_card_range_mul_card_ker (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).f j))
    rw [← (hT.homology_exact₁ i j hij).moduleCat_range_eq_ker] at h
    exact h
  -- the middle term is an extension of the image of the first map
  have hb : ∀ j : ℕ, Nat.card (((periodicFunctor R g).obj S.X₂).homology j) =
      Nat.card (range (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).g j))) *
        Nat.card (range (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).f j))) := by
    intro j
    have h := card_eq_card_range_mul_card_ker (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).g j))
    rw [← (hT.homology_exact₂ j).moduleCat_range_eq_ker] at h
    exact h
  -- the right-hand term is an extension of the image of the second map
  have hc : ∀ (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j),
      Nat.card (((periodicFunctor R g).obj S.X₃).homology i) =
        Nat.card (range (ModuleCat.Hom.hom (hT.δ i j hij))) *
          Nat.card (range (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).g i))) := by
    intro i j hij
    have h := card_eq_card_range_mul_card_ker (ModuleCat.Hom.hom (hT.δ i j hij))
    rw [← (hT.homology_exact₃ i j hij).moduleCat_range_eq_ker] at h
    exact h
  -- naturality of the periodicity closes the sequence into a hexagon: degrees `1` and `3` give
  -- the same image
  have hs13 : Nat.card (range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).g 3))) =
      Nat.card (range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).g 1))) := by
    have hstep : ∀ {j : ℕ}, Odd j →
        Nat.card (range (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (S.map (periodicFunctor R g)).g j))) =
          Nat.card (range (ModuleCat.Hom.hom
            (ShortComplex.homologyMap (normHomCompSubMap g S.g)))) := by
      intro j hj
      refine card_range_eq_card_range_of_comp_eq _ _
        (periodicHomologyIsoOdd S.X₂ g hj).toLinearEquiv
        (periodicHomologyIsoOdd S.X₃ g hj).toLinearEquiv ?_
      have h := congrArg ModuleCat.Hom.hom (homologyMap_comp_periodicHomologyIsoOdd g S.g hj)
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
      exact h
    exact (hstep (by decide)).trans (hstep (by decide)).symm
  exact ⟨_, _, _, _, _, _,
    (natCard_periodicHomology_odd S.X₁ g hg (j := 1) (by decide)).symm.trans (ha 2 1 rfl),
    (natCard_periodicHomology_even S.X₁ g hg (j := 2) (by decide) (by decide)).symm.trans
      (ha 3 2 rfl),
    (natCard_periodicHomology_odd S.X₃ g hg (j := 3) (by decide)).symm.trans
      ((hc 3 2 rfl).trans (congrArg _ hs13)),
    (natCard_periodicHomology_even S.X₃ g hg (j := 2) (by decide) (by decide)).symm.trans
      (hc 2 1 rfl),
    (natCard_periodicHomology_odd S.X₂ g hg (j := 1) (by decide)).symm.trans (hb 1),
    (natCard_periodicHomology_even S.X₂ g hg (j := 2) (by decide) (by decide)).symm.trans
      (hb 2)⟩

end ShortExact

section Multiplicativity

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] [IsCyclic G]

/-- The hexagon of `exists_hexagon_natCard`, with a generator produced from cyclicity. -/
private theorem exists_hexagon_natCard_of_isCyclic {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) :
    ∃ r₁ r₂ s₁ s₂ t₁ t₂ : ℕ,
      Nat.card (tateCohomology S.X₁ 0) = r₁ * t₁ ∧
        Nat.card (tateCohomology S.X₁ (-1)) = r₂ * t₂ ∧
        Nat.card (tateCohomology S.X₃ 0) = t₂ * s₁ ∧
        Nat.card (tateCohomology S.X₃ (-1)) = t₁ * s₂ ∧
        Nat.card (tateCohomology S.X₂ 0) = s₁ * r₁ ∧
        Nat.card (tateCohomology S.X₂ (-1)) = s₂ * r₂ := by
  obtain ⟨g, hgtop⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x ↦ hgtop.ge (Subgroup.mem_top x)
  let _inst : CommGroup G := IsCyclic.commGroup
  exact exists_hexagon_natCard hS g hg

/-- **The exact hexagon in cardinality form.** For a short exact sequence of representations of a
finite cyclic group, the product of the orders of the Tate groups at three alternate corners of
the hexagon equals the product at the other three. No finiteness is assumed: an infinite Tate
group makes both sides zero. -/
theorem natCard_tateCohomology_mul_of_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) :
    Nat.card (tateCohomology S.X₁ 0) * Nat.card (tateCohomology S.X₃ 0) *
        Nat.card (tateCohomology S.X₂ (-1)) =
      Nat.card (tateCohomology S.X₁ (-1)) * Nat.card (tateCohomology S.X₃ (-1)) *
        Nat.card (tateCohomology S.X₂ 0) := by
  obtain ⟨r₁, r₂, s₁, s₂, t₁, t₂, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_hexagon_natCard_of_isCyclic hS
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  ring

/-- In the hexagon, the middle degree `-1` Tate group is squeezed between the two outer ones: its
order divides their product. In particular it is finite as soon as they are. -/
theorem natCard_tateCohomology_negOne_dvd_of_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) :
    Nat.card (tateCohomology S.X₂ (-1)) ∣
      Nat.card (tateCohomology S.X₁ (-1)) * Nat.card (tateCohomology S.X₃ (-1)) := by
  obtain ⟨r₁, r₂, s₁, s₂, t₁, t₂, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_hexagon_natCard_of_isCyclic hS
  exact ⟨t₂ * t₁, by rw [h₂, h₄, h₆]; ring⟩

/-- **The Herbrand quotient is multiplicative in a short exact sequence.** For a short exact
sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations of a finite cyclic group whose outer terms
have finite Tate cohomology in degree `-1`, the Herbrand quotient of the middle term is the
product of the Herbrand quotients of the outer ones. The degree-zero groups are unconstrained:
if one of them is infinite both sides are zero. -/
theorem herbrandQuotient_eq_mul_of_shortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    [Finite (tateCohomology S.X₁ (-1))] [Finite (tateCohomology S.X₃ (-1))] :
    herbrandQuotient S.X₂ = herbrandQuotient S.X₁ * herbrandQuotient S.X₃ := by
  have h1 : Nat.card (tateCohomology S.X₁ (-1)) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩
  have h3 : Nat.card (tateCohomology S.X₃ (-1)) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩
  have h2 : Nat.card (tateCohomology S.X₂ (-1)) ≠ 0 := fun h ↦
    mul_ne_zero h1 h3 (Nat.eq_zero_of_zero_dvd
      (h ▸ natCard_tateCohomology_negOne_dvd_of_shortExact hS))
  have keyQ : (Nat.card (tateCohomology S.X₁ 0) : ℚ) * Nat.card (tateCohomology S.X₃ 0) *
      Nat.card (tateCohomology S.X₂ (-1)) =
      (Nat.card (tateCohomology S.X₁ (-1)) : ℚ) * Nat.card (tateCohomology S.X₃ (-1)) *
        Nat.card (tateCohomology S.X₂ 0) := by
    exact_mod_cast natCard_tateCohomology_mul_of_shortExact hS
  have q1 : (Nat.card (tateCohomology S.X₁ (-1)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h1
  have q2 : (Nat.card (tateCohomology S.X₂ (-1)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h2
  have q3 : (Nat.card (tateCohomology S.X₃ (-1)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h3
  rw [herbrandQuotient_def, herbrandQuotient_def, herbrandQuotient_def]
  field_simp
  linear_combination -keyQ

end Multiplicativity

end TauCeti.TateCohomology
