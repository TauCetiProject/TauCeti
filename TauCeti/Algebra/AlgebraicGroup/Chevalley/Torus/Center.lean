/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Quotient

/-!
# The toral part of the centre of a Chevalley group

For a Chevalley datum with injective root parametrizations, a torus point centralizes the
root-and-torus-generated subgroup exactly when every root character is one. The converse to
the pinning equation can be tested at parameter one, so this assertion holds over arbitrary
commutative rings, including nonreduced rings and rings of bad characteristic.

For the simply connected datum, the root parametrizations are injective over every ring.
Its toral centralizer is therefore the group of unit-valued characters of `P / Q`, where `P`
is the full weight lattice and `Q` is the span of the roots. The equivalence lands in actual
datum points, not merely in torus parameters, and retains its evaluation equation.

This identifies only the intersection of the torus with the centralizer of the generated
subgroup. It does not assert that all central elements lie in the torus or that the generated
subgroup contains every point of the group scheme.

The construction uses `ChevalleyDatum.torusPoints_conj_rootSubgroupPoints`,
`scChevalleyDatum_rootSubgroupPoints_injective`, and the lattice-duality equivalence
`TauCeti.torusAnnihilatorEquiv`.

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

/-- An injectively parametrized root subgroup detects whether its root character is trivial
on a torus point: it suffices to commute with the root element of parameter one. -/
theorem commute_torusPoints_rootSubgroupPoints_one_iff (γ : Fin t.numRoots)
    (hinj : Function.Injective (D.rootSubgroupPoints γ A)) (s : Fin t.rank → Aˣ) :
    Commute (D.torusPoints A s) (D.rootSubgroupPoints γ A (Multiplicative.ofAdd 1)) ↔
      torusCharacter s (D.coordinateRoot γ) = 1 := by
  constructor
  · intro h
    have heq := D.torusPoints_conj_rootSubgroupPoints γ A s 1
    rw [h.eq, mul_inv_cancel_right, mul_one] at heq
    have hval := congrArg Multiplicative.toAdd (hinj heq)
    exact Units.ext hval.symm
  · intro h
    have heq := D.torusPoints_conj_rootSubgroupPoints γ A s 1
    rw [h, Units.val_one, one_mul, mul_inv_eq_iff_eq_mul] at heq
    exact heq

/-- With injective root parametrizations, a torus point centralizes the generated group if
and only if all root characters are trivial on it. No point-generation theorem is assumed. -/
theorem torusPoints_mem_centralizer_rootTorusSubgroup_iff
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ A)) (s : Fin t.rank → Aˣ) :
    D.torusPoints A s ∈ Subgroup.centralizer (D.rootTorusSubgroup A : Set (D.points A)) ↔
      ∀ γ, torusCharacter s (D.coordinateRoot γ) = 1 := by
  constructor
  · intro hs γ
    apply (D.commute_torusPoints_rootSubgroupPoints_one_iff γ (hinj γ) s).mp
    exact (Subgroup.mem_centralizer_iff.mp hs _
      (D.rootSubgroupPoints_mem_rootTorusSubgroup γ A (Multiplicative.ofAdd 1))).symm
  · exact D.torusPoints_mem_centralizer_rootTorusSubgroup_of_root_eq_one s

/-- In actual character-lattice coordinates, the toral part of the centralizer of the
generated group is exactly the image of the annihilator of the root lattice. -/
theorem map_torusAnnihilator_eq_range_inf_centralizer_rootTorusSubgroup
    (hinj : ∀ γ, Function.Injective (D.rootSubgroupPoints γ A)) :
    (torusAnnihilator (R := A) (Submodule.span ℤ (Set.range D.coordinateRoot))).map
        (D.torusPoints A) =
      (D.torusPoints A).range ⊓
        Subgroup.centralizer (D.rootTorusSubgroup A : Set (D.points A)) := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, (D.torusPoints_mem_centralizer_rootTorusSubgroup_iff hinj s).2
      ((mem_torusAnnihilator_span_iff D.coordinateRoot s).1 hs)⟩
  · rintro ⟨⟨s, rfl⟩, hs⟩
    exact ⟨s, (mem_torusAnnihilator_span_iff D.coordinateRoot s).2
      ((D.torusPoints_mem_centralizer_rootTorusSubgroup_iff hinj s).1 hs), rfl⟩

end ChevalleyDatum

variable (t ht A)

/-- The unit-valued characters of the weight lattice modulo the root lattice are precisely
the points of the simply connected torus centralizing the root-and-torus-generated group.
This concerns the toral part of the centre, not containment of the entire centre in the torus. -/
def scToralCenterEquiv :
    AddChar ((Fin t.rank → ℤ) ⧸
      Submodule.span ℤ (Set.range (t.simplyConnectedRootDatum ht).root)) Aˣ ≃*
      ↥(((t.scChevalleyDatum ht).torusPoints A).range ⊓
        Subgroup.centralizer ((t.scChevalleyDatum ht).rootTorusSubgroup A :
          Set ((t.scChevalleyDatum ht).points A))) :=
  (torusAnnihilatorEquiv _).trans
    (((torusAnnihilator (R := A)
      (Submodule.span ℤ (Set.range (t.simplyConnectedRootDatum ht).root))).equivMapOfInjective
        ((t.scChevalleyDatum ht).torusPoints A)
        ((t.scChevalleyDatum ht).torusPoints_injective A)).trans
      (MulEquiv.subgroupCongr (by
        have hroot : (t.scChevalleyDatum ht).coordinateRoot =
            (t.simplyConnectedRootDatum ht).root :=
          funext (t.scChevalleyDatum_coordinateRoot ht)
        simpa only [hroot] using
          (t.scChevalleyDatum ht).map_torusAnnihilator_eq_range_inf_centralizer_rootTorusSubgroup
            (fun γ => t.scChevalleyDatum_rootSubgroupPoints_injective ht γ A))))

/-- The toral-centre equivalence sends a quotient character to the torus point whose
coordinates are its values on the classes of the fundamental weights. -/
@[simp]
theorem coe_scToralCenterEquiv
    (χ : AddChar ((Fin t.rank → ℤ) ⧸
      Submodule.span ℤ (Set.range (t.simplyConnectedRootDatum ht).root)) Aˣ) :
    (t.scToralCenterEquiv ht A χ : (t.scChevalleyDatum ht).points A) =
      (t.scChevalleyDatum ht).torusPoints A (quotientCharTorusPoint _ χ) := by
  simp [scToralCenterEquiv]

/-- The inverse equivalence evaluates a quotient class by the character of any torus
parameter representing the given point. Injectivity of the torus makes this independent of
the chosen representation. -/
theorem scToralCenterEquiv_symm_apply_mk
    (g : ↥(((t.scChevalleyDatum ht).torusPoints A).range ⊓
      Subgroup.centralizer ((t.scChevalleyDatum ht).rootTorusSubgroup A :
        Set ((t.scChevalleyDatum ht).points A))))
    (s : Fin t.rank → Aˣ) (hs : (t.scChevalleyDatum ht).torusPoints A s = g)
    (μ : Fin t.rank → ℤ) :
    (t.scToralCenterEquiv ht A).symm g (Submodule.Quotient.mk μ) = torusCharacter s μ := by
  have hcoord : quotientCharTorusPoint _ ((t.scToralCenterEquiv ht A).symm g) = s := by
    apply (t.scChevalleyDatum ht).torusPoints_injective A
    rw [← coe_scToralCenterEquiv, MulEquiv.apply_symm_apply, hs]
  rw [← Submodule.mkQ_apply, ← torusCharacter_quotientCharTorusPoint, hcoord]

end

end TauCeti.DynkinType
