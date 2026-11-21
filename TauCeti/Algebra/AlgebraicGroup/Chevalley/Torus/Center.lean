/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Quotient
import TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct

/-!
# The toral part of the centre of a Chevalley group

For every Chevalley datum `D`, every root parametrization is injective over every commutative
ring (`ChevalleyDatum.rootSubgroupPoints_injective`), so a torus point centralizes the
root-and-torus-generated subgroup exactly when every root character is one. The converse to
the pinning equation can be tested at parameter one, so this assertion holds over arbitrary
commutative rings, including nonreduced rings and rings of bad characteristic.

For every datum `D`, its toral centralizer is the group of unit-valued characters of
`Λ(D) / Q`, expressed in the chosen basis `D.weightLatticeBasis`: the denominator is the span
of `D.coordinateRoot`, not the roots read in the full weight lattice. For the simply connected
datum, this quotient is `P / Q`, where `P` is the full weight lattice. The equivalences land in
actual datum points, not merely in torus parameters, and retain their evaluation equations.
`ChevalleyDatum.torusInfCentralizerRootTorusSubgroupEquiv` treats arbitrary Chevalley data;
`scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv` reads the simply connected quotient
directly in fundamental-weight coordinates.

This identifies only the intersection of the torus with the centralizer of the generated
subgroup. It does not assert that all central elements lie in the torus or that the generated
subgroup contains every point of the group scheme.

The construction uses `ChevalleyDatum.torusPoints_conj_rootSubgroupPoints`,
`ChevalleyDatum.rootSubgroupPoints_injective`, and the lattice-duality equivalence
`TauCeti.torusAnnihilatorEquiv`. The converse argument and equivalence construction adapt
`TauCeti.UniversalEnvelopingAlgebra.torusCharacter_eq_one_of_commute_kostantRootSubgroupParam`
from `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic` and
`TauCeti.UniversalEnvelopingAlgebra.kostantCentralTorusEquiv` from
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Center` to actual datum points.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 28(d).
* R. W. Carter, *Simple Groups of Lie Type*, §7.1.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

variable {t : DynkinType} {ht : t.Valid} {A : Type*} [CommRing A]

namespace ChevalleyDatum

variable (D : ChevalleyDatum t ht)

/-- A root subgroup detects whether its root character is trivial on a torus point: it suffices to
commute with the root element of parameter one. -/
theorem commute_torusPoints_rootSubgroupPoints_ofAdd_one_iff (γ : Fin t.numRoots)
    (s : Fin t.rank → Aˣ) :
    Commute (D.torusPoints A s) (D.rootSubgroupPoints γ A (Multiplicative.ofAdd 1)) ↔
      torusCharacter s (D.coordinateRoot γ) = 1 := by
  constructor
  · intro h
    have heq := D.torusPoints_conj_rootSubgroupPoints γ A s 1
    rw [h.eq, mul_inv_cancel_right, mul_one] at heq
    have hval := congrArg Multiplicative.toAdd (D.rootSubgroupPoints_injective γ A heq)
    exact Units.ext hval.symm
  · intro h
    have heq := D.torusPoints_conj_rootSubgroupPoints γ A s 1
    rw [h, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at heq
    exact heq

/-- A torus point of any Chevalley datum centralizes the generated group if and only if all root
characters are trivial on it. No point-generation theorem is assumed. -/
theorem torusPoints_mem_centralizer_rootTorusSubgroup_iff (s : Fin t.rank → Aˣ) :
    D.torusPoints A s ∈ Subgroup.centralizer (D.rootTorusSubgroup A : Set (D.points A)) ↔
      ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  constructor
  · intro hs γ
    apply (D.commute_torusPoints_rootSubgroupPoints_ofAdd_one_iff γ s).mp
    exact (Subgroup.mem_centralizer_iff.mp hs _
      (D.rootSubgroupPoints_mem_rootTorusSubgroup γ A (Multiplicative.ofAdd 1))).symm
  · exact D.torusPoints_mem_centralizer_rootTorusSubgroup_of_root_eq_one s

/-- In actual character-lattice coordinates, the toral part of the centralizer of the generated
group is exactly the image of the annihilator of the root lattice. -/
theorem map_torusAnnihilator_eq_range_inf_centralizer_rootTorusSubgroup :
    (torusAnnihilator (R := A) (Submodule.span ℤ (Set.range D.coordinateRoot))).map
        (D.torusPoints A) =
      (D.torusPoints A).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup A : Set (D.points A)) := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff s).2
      ((mem_torusAnnihilator_span_iff D.coordinateRoot s).1 hs)⟩
  · rintro ⟨⟨s, rfl⟩, hs⟩
    exact ⟨s, (mem_torusAnnihilator_span_iff D.coordinateRoot s).2
      ((D.torusPoints_mem_centralizer_rootTorusSubgroup_iff s).1 hs), rfl⟩

variable (A)

/-- Characters of the actual weight lattice modulo the root lattice, in the chosen lattice
basis, identify with the torus points centralizing the generated group. The denominator is the
span of the coordinate roots, so this applies also to proper sublattices of the full weight
lattice. -/
def torusInfCentralizerRootTorusSubgroupEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Aˣ ≃*
      ↥((D.torusPoints A).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup A : Set (D.points A))) :=
  (torusAnnihilatorEquiv _).trans
    (((torusAnnihilator (R := A)
      (Submodule.span ℤ (Set.range D.coordinateRoot))).equivMapOfInjective
        (D.torusPoints A) (D.torusPoints_injective A)).trans
      (MulEquiv.subgroupCongr
        D.map_torusAnnihilator_eq_range_inf_centralizer_rootTorusSubgroup))

/-- The forward equivalence evaluates the quotient character on the classes of the chosen
basis of the actual weight lattice to obtain the torus coordinates. -/
@[simp]
theorem coe_torusInfCentralizerRootTorusSubgroupEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ Submodule.span ℤ (Set.range D.coordinateRoot)) Aˣ) :
    (D.torusInfCentralizerRootTorusSubgroupEquiv A χ : D.points A) =
      D.torusPoints A (quotientCharTorusPoint _ χ) := by
  simp [torusInfCentralizerRootTorusSubgroupEquiv]

/-- The inverse equivalence evaluates a quotient class by the character of the given torus
parameter. -/
@[simp]
theorem torusInfCentralizerRootTorusSubgroupEquiv_symm_apply_mk
    (s : Fin t.rank → Aˣ)
    (hg : D.torusPoints A s ∈ (D.torusPoints A).range ⊓
      Subgroup.centralizer (D.rootTorusSubgroup A : Set (D.points A)))
    (μ : Fin t.rank → ℤ) :
    (D.torusInfCentralizerRootTorusSubgroupEquiv A).symm ⟨D.torusPoints A s, hg⟩
      (Submodule.Quotient.mk μ) = torusCharacter s μ := by
  have hcoord : quotientCharTorusPoint _
      ((D.torusInfCentralizerRootTorusSubgroupEquiv A).symm
        ⟨D.torusPoints A s, hg⟩) = s := by
    apply D.torusPoints_injective A
    rw [← D.coe_torusInfCentralizerRootTorusSubgroupEquiv A,
      MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

end ChevalleyDatum

variable (t ht)

/-- For the simply connected datum over any commutative ring, a torus point centralizes the
root-and-torus-generated group exactly when all root characters are trivial. -/
@[simp]
theorem scChevalleyDatum_torusPoints_mem_centralizer_rootTorusSubgroup_iff
    (s : Fin t.rank → Aˣ) :
    (t.scChevalleyDatum ht).torusPoints A s ∈
        Subgroup.centralizer ((t.scChevalleyDatum ht).rootTorusSubgroup A :
          Set ((t.scChevalleyDatum ht).points A)) ↔
      ∀ γ, torusCharacter s ((t.simplyConnectedRootDatum ht).root γ) = 1 := by
  simpa only [scChevalleyDatum_coordinateRoot] using
    (t.scChevalleyDatum ht).torusPoints_mem_centralizer_rootTorusSubgroup_iff s

variable (A)

/-- Unit-valued characters of `P / Q` identify with the simply connected torus points
centralizing the root-and-torus-generated group, over any commutative ring. Here `P` and `Q`
are the weight and root lattices in fundamental-weight coordinates. -/
def scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Aˣ ≃*
      ↥(((t.scChevalleyDatum ht).torusPoints A).range ⊓
        Subgroup.centralizer ((t.scChevalleyDatum ht).rootTorusSubgroup A :
          Set ((t.scChevalleyDatum ht).points A))) :=
  (torusAnnihilatorEquiv _).trans
    (((torusAnnihilator (R := A)
      ((t.simplyConnectedRootDatum ht).rootSpan ℤ)).equivMapOfInjective
        ((t.scChevalleyDatum ht).torusPoints A)
        ((t.scChevalleyDatum ht).torusPoints_injective A)).trans
      (MulEquiv.subgroupCongr (by
        simpa only [funext (t.scChevalleyDatum_coordinateRoot ht)] using
          (t.scChevalleyDatum ht).map_torusAnnihilator_eq_range_inf_centralizer_rootTorusSubgroup)))

/-- The simply connected equivalence obtains the torus coordinates by evaluating the
quotient character on the fundamental-weight classes. -/
@[simp]
theorem coe_scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸ (t.simplyConnectedRootDatum ht).rootSpan ℤ) Aˣ) :
    (t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht A χ :
        (t.scChevalleyDatum ht).points A) =
      (t.scChevalleyDatum ht).torusPoints A (quotientCharTorusPoint _ χ) := by
  simp [scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv]

/-- The inverse simply connected equivalence evaluates a weight class by the character of
the given torus parameter. -/
@[simp]
theorem scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv_symm_apply_mk
    (s : Fin t.rank → Aˣ)
    (hg : (t.scChevalleyDatum ht).torusPoints A s ∈
      ((t.scChevalleyDatum ht).torusPoints A).range ⊓
        Subgroup.centralizer ((t.scChevalleyDatum ht).rootTorusSubgroup A :
          Set ((t.scChevalleyDatum ht).points A)))
    (μ : Fin t.rank → ℤ) :
    (t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht A).symm
      ⟨(t.scChevalleyDatum ht).torusPoints A s, hg⟩ (Submodule.Quotient.mk μ) =
        torusCharacter s μ := by
  have hcoord : quotientCharTorusPoint _
      ((t.scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv ht A).symm
        ⟨(t.scChevalleyDatum ht).torusPoints A s, hg⟩) = s := by
    apply (t.scChevalleyDatum ht).torusPoints_injective A
    rw [← coe_scChevalleyDatumTorusInfCentralizerRootTorusSubgroupEquiv,
      MulEquiv.apply_symm_apply]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

end

end TauCeti.DynkinType
