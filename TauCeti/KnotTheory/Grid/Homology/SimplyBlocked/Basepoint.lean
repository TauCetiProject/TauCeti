/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
public import TauCeti.KnotTheory.Grid.XHomotopy.Grading
import TauCeti.Algebra.Homology.SquareZero.Quotient

/-!
# Independence of bigraded simply blocked grid homology from the blocked marking

Setting `V_i = 0` on the unblocked grid complex `GC⁻` presents `GC^_i` as the quotient of `GC⁻` by
the injective chain map `V_i • id`, so its homology is canonically identified over the coefficient
ring `R` with the homology of the mapping cone of `V_i • id` on `GC⁻`. In characteristic two, given
any polynomial-linear map `H` on `GC⁻` satisfying `∂⁻ ∘ H + H ∘ ∂⁻ = (V_i + V_j) • id`, the
shearing automorphism `(a, b) ↦ (a, H a + b)` intertwines the mapping cones of `V_i` and `V_j`
(`LinearMap.homologyEquivOfHomotopicInjective`) and therefore induces an `R`-linear equivalence
between the homologies of `GC^_i` and `GC^_j`.

On an odd-component grid diagram, if `H` lowers the `(O-Maslov, Alexander)` bidegree by `(1, 1)` —
as the sum of `X`-marking homotopies along a link component does
(`OddComponentGridDiagram.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle`) — then a
homogeneous cycle of bidegree `g` in `GC^_i` lifts to `b ∈ GC⁻_g` with `∂⁻ b = -V_i • a`. Because
`∂⁻` has bidegree `(-1, 0)` and multiplication by `V_i` reflects homogeneity while lowering bidegree
by `(2, 1)`, the primitive `a` has bidegree `g + (1, 1)`, so `H a + b` again has bidegree `g`. Thus
the induced `R`-linear equivalence on homology is homogeneous of bidegree `(0, 0)`.

For a knot grid all `O`-markings lie on one component, so `G-hat` as a bigraded `R`-module — and,
over a field of characteristic two, its bigraded Poincaré series and Alexander-graded Euler
characteristic — is independent of the choice of blocked column.

## Main definitions

* `TauCeti.GridDiagram.oneVariableSpecializationHomologyEquivOfHomotopy`: the `R`-linear equivalence
  between the homologies of the specializations `V_i = 0` and `V_j = 0` induced by a homotopy `H`
  between `V_i` and `V_j` on `GC⁻`.
* `TauCeti.OddComponentGridDiagram.oneVariableSpecializationHomologySameCycleEquiv`: the resulting
  bidegree-preserving `R`-linear equivalence when `i` and `j` lie on the same link component.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyBasepointEquiv` and
  `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyBasepointPieceEquiv`: for a knot grid, the
  bidegree-preserving `R`-linear equivalence comparing `G-hat` across any two choices of blocked
  column, and its restriction to each homogeneous piece.

## Main results

* `TauCeti.GridDiagram.oneVariableSpecializationHomologyEquivOfHomotopy_class`: explicit evaluation
  of the cone comparison on a lifted cycle `b` with `V_i • a + ∂⁻ b = 0`.
* `TauCeti.GridDiagram.IsKnot.isHomogeneous_simplyBlockedHomologyBasepointEquiv`: the basepoint
  comparison on `G-hat` is homogeneous of bidegree `(0, 0)`.
* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_eq` and
  `TauCeti.GridDiagram.IsKnot.gradedSimplyBlockedHomologyEulerChar_eq`: the bigraded Poincaré series
  and Alexander-graded Euler characteristic of `G-hat` do not depend on the blocked column.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Proposition 4.6.15.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

section ConcreteModel

private abbrev dMinus : GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  (G.unblockedDifferential R).restrictScalars R

private abbrev dHat (i : Fin n) : GridChainHat R n i →ₗ[R] GridChainHat R n i :=
  (G.simplyBlockedDifferential R i).restrictScalars R

private def xSmulEnd (i : Fin n) : GridChainMinus R n →ₗ[R] GridChainMinus R n :=
  ((MvPolynomial.X i : MvPolynomial (Fin n) R) •
    (LinearMap.id : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
      ).restrictScalars R

private theorem xSmulEnd_comp_dMinus (i : Fin n) :
    xSmulEnd R i ∘ₗ dMinus G R = dMinus G R ∘ₗ xSmulEnd R i :=
  LinearMap.ext fun c => (map_smul (G.unblockedDifferential R) (MvPolynomial.X i) c).symm

private theorem xSmulEnd_injective (i : Fin n) : Function.Injective (xSmulEnd R i) :=
  X_smul_gridChainMinus_injective R i

private def specLinearMap (i : Fin n) : GridChainMinus R n →ₗ[R] GridChainHat R n i where
  toFun := simplyBlockedSpecialization R i
  map_add' := map_add _
  map_smul' r c := by
    apply Finsupp.ext
    intro x
    simp only [simplyBlockedSpecialization_apply, Finsupp.smul_apply, RingHom.id_apply]
    exact (MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective).toLinearMap.map_smul r _

private theorem specLinearMap_comp_dMinus (i : Fin n) :
    specLinearMap R i ∘ₗ dMinus G R = dHat G R i ∘ₗ specLinearMap R i :=
  LinearMap.ext (G.simplyBlockedSpecialization_unblockedDifferential R i)

private theorem specLinearMap_surjective (i : Fin n) : Function.Surjective (specLinearMap R i) :=
  simplyBlockedSpecialization_surjective R i

private theorem exact_xSmulEnd_specLinearMap (i : Fin n) :
    Function.Exact (xSmulEnd R i) (specLinearMap R i) :=
  exact_X_smul_simplyBlockedSpecialization R i

variable [CharP R 2]

private theorem dMinus_comp_self : dMinus G R ∘ₗ dMinus G R = 0 :=
  LinearMap.ext fun c => congr($(G.unblockedDifferential_comp_self_eq_zero R) c)

private theorem dHat_comp_self (i : Fin n) : dHat G R i ∘ₗ dHat G R i = 0 :=
  LinearMap.ext fun c => congr($(G.simplyBlockedDifferential_comp_self_eq_zero R i) c)

private theorem mem_ker_simplyBlockedComplex_d_of_mem_ker_dHat (i : Fin n)
    (w : LinearMap.ker (dHat G R i)) :
    (G.simplyBlockedChainEquiv R i).symm w.1 ∈
      LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom := by
  rw [G.mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
  exact w.2

/-- The concrete `R`-linear cycle-to-homology map from `ker (simplyBlockedDifferential R i)` onto
the restricted-scalar categorical homology of `G.simplyBlockedComplex R i`. -/
private def kerDHatToHomology (i : Fin n) :
    LinearMap.ker (dHat G R i) →ₗ[R]
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
          ((G.simplyBlockedComplex R i).homology ()) where
  toFun w :=
    (G.oneVariableSpecializationHomologyClass R i
      ⟨(G.simplyBlockedChainEquiv R i).symm w.1,
        mem_ker_simplyBlockedComplex_d_of_mem_ker_dHat G R i w⟩ :
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
          ((G.simplyBlockedComplex R i).homology ()))
  map_add' w₁ w₂ := by
    refine Eq.trans ?_ (map_add (G.oneVariableSpecializationHomologyClass R i) _ _)
    congr 1
    exact Subtype.ext (map_add (G.simplyBlockedChainEquiv R i).symm w₁.1 w₂.1)
  map_smul' r w := by
    have hsmul : (r • w.1 : GridChainHat R n i) =
        (MvPolynomial.C r : MvPolynomial {c : Fin n // c ≠ i} R) • w.1 := by
      rw [MvPolynomial.C_eq_algebraMap, algebraMap_smul]
    have hclass := (G.oneVariableSpecializationHomologyClass R i).map_smul
      (MvPolynomial.C r) ⟨(G.simplyBlockedChainEquiv R i).symm w.1,
        mem_ker_simplyBlockedComplex_d_of_mem_ker_dHat G R i w⟩
    refine Eq.trans ?_ hclass
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, hsmul, map_smul]

private theorem kerDHatToHomology_apply (i : Fin n) (w : LinearMap.ker (dHat G R i)) :
    kerDHatToHomology G R i w =
      G.oneVariableSpecializationHomologyClass R i
        ⟨(G.simplyBlockedChainEquiv R i).symm w.1,
          mem_ker_simplyBlockedComplex_d_of_mem_ker_dHat G R i w⟩ :=
  (rfl)

private theorem kerDHatToHomology_eq_zero_iff (i : Fin n) (w : LinearMap.ker (dHat G R i)) :
    kerDHatToHomology G R i w = 0 ↔ w ∈ (dHat G R i).boundariesInKer := by
  refine Iff.trans (Iff.rfl : _ ↔ G.oneVariableSpecializationHomologyClass R i
    ⟨(G.simplyBlockedChainEquiv R i).symm w.1,
      mem_ker_simplyBlockedComplex_d_of_mem_ker_dHat G R i w⟩ = 0) ?_
  rw [G.oneVariableSpecializationHomologyClass_eq_zero_iff,
    G.mem_range_moduleCatToCycles_simplyBlockedComplex_iff, LinearEquiv.apply_symm_apply,
    LinearMap.mem_boundariesInKer]
  rfl

private theorem ker_kerDHatToHomology (i : Fin n) :
    LinearMap.ker (kerDHatToHomology G R i) = (dHat G R i).boundariesInKer :=
  Submodule.ext (kerDHatToHomology_eq_zero_iff G R i)

private theorem surjective_kerDHatToHomology (i : Fin n) :
    Function.Surjective (kerDHatToHomology G R i) := fun y => by
  obtain ⟨z, rfl⟩ := G.oneVariableSpecializationHomologyClass_surjective R i y
  refine ⟨⟨G.simplyBlockedChainEquiv R i z.1,
    (G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2⟩, ?_⟩
  rw [kerDHatToHomology_apply]
  simp only [LinearEquiv.symm_apply_apply, Subtype.coe_eta]
  rfl

/-- The `R`-linear identification between the concrete quotient homology of
`simplyBlockedDifferential` and the restricted-scalar categorical homology of
`simplyBlockedComplex`. -/
private def concreteHatHomologyEquiv (i : Fin n) :
    (dHat G R i).homology (dHat_comp_self G R i) ≃ₗ[R]
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
          ((G.simplyBlockedComplex R i).homology ()) :=
  (Submodule.quotEquivOfEq _ _ (ker_kerDHatToHomology G R i).symm).trans
    ((kerDHatToHomology G R i).quotKerEquivOfSurjective (surjective_kerDHatToHomology G R i))

private theorem concreteHatHomologyEquiv_mk (i : Fin n) (w : LinearMap.ker (dHat G R i)) :
    concreteHatHomologyEquiv G R i (Submodule.Quotient.mk w) =
      G.oneVariableSpecializationHomologyClass R i
        ⟨(G.simplyBlockedChainEquiv R i).symm w.1,
          mem_ker_simplyBlockedComplex_d_of_mem_ker_dHat G R i w⟩ :=
  (rfl)

private theorem concreteHatHomologyEquiv_symm_class (i : Fin n)
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    (concreteHatHomologyEquiv G R i).symm
        (G.oneVariableSpecializationHomologyClass R i z :
          (ModuleCat.restrictScalars
            (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
              ((G.simplyBlockedComplex R i).homology ())) =
      Submodule.Quotient.mk ⟨G.simplyBlockedChainEquiv R i z.1,
        (G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2⟩ :=
  (concreteHatHomologyEquiv G R i).symm_apply_eq.mpr <| by
    rw [concreteHatHomologyEquiv_mk]
    simp only [LinearEquiv.symm_apply_apply, Subtype.coe_eta]
    rfl

private theorem homotopy_restrictScalars {i j : Fin n}
    (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id) :
    dMinus G R ∘ₗ H.restrictScalars R + H.restrictScalars R ∘ₗ dMinus G R =
      xSmulEnd R i - xSmulEnd R j := by
  refine LinearMap.ext fun c => ?_
  have hc := congr($hH c)
  simp only [dMinus, xSmulEnd, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hc ⊢
  rw [hc, ← sub_smul, CharTwo.sub_eq_add]

/-- **Comparing two one-variable specializations along a variable homotopy.** Given a
polynomial-linear map `H` on `GC⁻` with `∂⁻ ∘ H + H ∘ ∂⁻ = (V_i + V_j) • id` in characteristic two,
comparing the mapping cones of `V_i` and `V_j` yields an `R`-linear equivalence between the
homologies of the specializations `V_i = 0` and `V_j = 0`. -/
def oneVariableSpecializationHomologyEquivOfHomotopy {i j : Fin n}
    (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id) :
    (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
          ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ j} R)).obj
          ((G.simplyBlockedComplex R j).homology ()) :=
  (concreteHatHomologyEquiv G R i).symm.trans <|
    (LinearMap.homologyEquivOfHomotopicInjective
      (π₁ := specLinearMap R i) (π₂ := specLinearMap R j)
      (dMinus_comp_self G R) (dHat_comp_self G R i) (dHat_comp_self G R j)
      (xSmulEnd_comp_dMinus G R i) (xSmulEnd_comp_dMinus G R j)
      (xSmulEnd_injective R i) (xSmulEnd_injective R j)
      (homotopy_restrictScalars G R H hH)
      (specLinearMap_surjective R i) (specLinearMap_surjective R j)
      (exact_xSmulEnd_specLinearMap R i) (exact_xSmulEnd_specLinearMap R j)
      (specLinearMap_comp_dMinus G R i) (specLinearMap_comp_dMinus G R j)).trans
        (concreteHatHomologyEquiv G R j)

/-- If `V_i • a + ∂⁻ b = 0` on `GC⁻`, then `simplyBlockedSpecialization R j (H a + b)` is killed by
`simplyBlockedDifferential R j`. -/
theorem simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero {i j : Fin n}
    (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id)
    {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X i : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0) :
    G.simplyBlockedDifferential R j (simplyBlockedSpecialization R j (H a + b)) = 0 :=
  LinearMap.mem_ker.mp
    (LinearMap.map_add_mem_ker_of_homotopy (π₂ := specLinearMap R j) (dMinus_comp_self G R)
      (xSmulEnd_comp_dMinus G R i) (xSmulEnd_injective R i)
      (homotopy_restrictScalars G R H hH)
      (exact_xSmulEnd_specLinearMap R j) (specLinearMap_comp_dMinus G R j) hab)

/-- Explicit cycle-level formula for `oneVariableSpecializationHomologyEquivOfHomotopy`: if a cycle
`z` in the specialization `V_i = 0` lifts to `b` in `GC⁻` with `V_i • a + ∂⁻ b = 0`, then its class
maps to the class of `simplyBlockedSpecialization R j (H a + b)` in the specialization
`V_j = 0`. -/
theorem oneVariableSpecializationHomologyEquivOfHomotopy_class {i j : Fin n}
    (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id)
    {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X i : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0)
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom)
    (hz : G.simplyBlockedChainEquiv R i z = simplyBlockedSpecialization R i b) :
    G.oneVariableSpecializationHomologyEquivOfHomotopy R H hH
        (G.oneVariableSpecializationHomologyClass R i z) =
      G.oneVariableSpecializationHomologyClass R j
        ⟨(G.simplyBlockedChainEquiv R j).symm (simplyBlockedSpecialization R j (H a + b)), by
          rw [G.mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
          exact G.simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero
            R H hH hab⟩ := by
  have hz₁ : specLinearMap R i b ∈ LinearMap.ker (dHat G R i) := by
    have hdz := (G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2
    rw [hz] at hdz
    exact hdz
  have hsub : (⟨G.simplyBlockedChainEquiv R i z.1,
      (G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2⟩ : LinearMap.ker (dHat G R i)) =
      ⟨specLinearMap R i b, hz₁⟩ :=
    Subtype.ext hz
  have hcone :=
    ((congrArg _ ((concreteHatHomologyEquiv_symm_class G R i z).trans
        (congrArg Submodule.Quotient.mk hsub))).trans
      (LinearMap.homologyEquivOfHomotopicInjective_mk
        (π₁ := specLinearMap R i) (π₂ := specLinearMap R j)
        (dMinus_comp_self G R) (dHat_comp_self G R i) (dHat_comp_self G R j)
        (xSmulEnd_comp_dMinus G R i) (xSmulEnd_comp_dMinus G R j)
        (xSmulEnd_injective R i) (xSmulEnd_injective R j)
        (homotopy_restrictScalars G R H hH)
        (specLinearMap_surjective R i) (specLinearMap_surjective R j)
        (exact_xSmulEnd_specLinearMap R i) (exact_xSmulEnd_specLinearMap R j)
        (specLinearMap_comp_dMinus G R i) (specLinearMap_comp_dMinus G R j) hab hz₁))
  exact congrArg (concreteHatHomologyEquiv G R j) hcone

end ConcreteModel

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

section Homotopy

variable {i j : Fin n}
  (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
  (hH : G.1.unblockedDifferential R ∘ₗ H + H ∘ₗ G.1.unblockedDifferential R =
    (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id)
  (hdeg : ∀ ⦃g : ℤ × ℤ⦄ ⦃c : GridChainMinus R n⦄,
    c ∈ G.bigradedChainMinusPiece R g → H c ∈ G.bigradedChainMinusPiece R (g - (1, 1)))

include hdeg in
/-- If the homotopy `H` lowers chain bidegrees by `(1, 1)`, the induced mapping-cone comparison
between the homologies of `V_i = 0` and `V_j = 0` preserves bidegrees. -/
theorem oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece
    {g : ℤ × ℤ}
    {y : (ModuleCat.restrictScalars
      (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
        ((G.1.simplyBlockedComplex R i).homology ())}
    (hy : y ∈ G.bigradedHatHomologyPiece R i g) :
    G.1.oneVariableSpecializationHomologyEquivOfHomotopy R H hH y ∈
      G.bigradedHatHomologyPiece R j g := by
  obtain ⟨z, hz, rfl⟩ := (G.mem_bigradedHatHomologyPiece_iff R i).mp hy
  obtain ⟨b, hb, hbz⟩ := G.mem_bigradedChainHatPiece_iff_exists.mp hz
  have hspec : simplyBlockedSpecialization R i (G.1.unblockedDifferential R b) = 0 := by
    rw [GridDiagram.simplyBlockedSpecialization_unblockedDifferential, hbz]
    exact (G.1.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2
  obtain ⟨a', ha'⟩ := (exact_X_smul_simplyBlockedSpecialization R i _).mp hspec
  dsimp only at ha'
  have hab : (MvPolynomial.X i : MvPolynomial (Fin n) R) • (-a') +
      G.1.unblockedDifferential R b = 0 := by
    rw [smul_neg, ha', neg_add_cancel]
  have ha_mem : -a' ∈ G.bigradedChainMinusPiece R (g + (1, 1)) := by
    rw [← G.X_smul_mem_bigradedChainMinusPiece_iff i]
    have hg : g + (1, 1) - (2, 1) = g - (1, 0) := Prod.ext (by simp; omega) (by simp)
    rw [hg, smul_neg, ha']
    exact Submodule.neg_mem _ (G.unblockedDifferential_mem_bigradedChainMinusPiece hb)
  have hHab : H (-a') + b ∈ G.bigradedChainMinusPiece R g := by
    have hHa := hdeg ha_mem
    rw [add_sub_cancel_right] at hHa
    exact Submodule.add_mem _ hHa hb
  rw [G.1.oneVariableSpecializationHomologyEquivOfHomotopy_class R H hH hab z hbz.symm]
  refine G.oneVariableSpecializationHomologyClass_mem_bigradedHatHomologyPiece R j ?_
  rw [LinearEquiv.apply_symm_apply]
  exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece j hHab

include hdeg in
/-- When `H` lowers bidegrees by `(1, 1)`, `oneVariableSpecializationHomologyEquivOfHomotopy` is
homogeneous of bidegree `(0, 0)`. -/
theorem isHomogeneous_oneVariableSpecializationHomologyEquivOfHomotopy :
    LinearMap.IsHomogeneous
      (G.1.oneVariableSpecializationHomologyEquivOfHomotopy R H hH).toLinearMap
      (G.bigradedHatHomologyGrading R i).piece
      (G.bigradedHatHomologyGrading R j).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro g y hy
  rw [bigradedHatHomologyGrading_piece] at hy
  rw [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe]
  exact G.oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece R H hH
    hdeg hy

include hdeg in
/-- When `H` lowers bidegrees by `(1, 1)`, `oneVariableSpecializationHomologyEquivOfHomotopy`
preserves and reflects homology bidegrees. -/
@[simp]
theorem oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ}
    {y : (ModuleCat.restrictScalars
      (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
        ((G.1.simplyBlockedComplex R i).homology ())} :
    G.1.oneVariableSpecializationHomologyEquivOfHomotopy R H hH y ∈
        G.bigradedHatHomologyPiece R j g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  refine ⟨fun hy => ?_,
    G.oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece R H hH hdeg⟩
  have hinv :=
    (G.isHomogeneous_oneVariableSpecializationHomologyEquivOfHomotopy R H hH hdeg).linearEquiv_symm
  rw [← bigradedHatHomologyGrading_piece] at hy
  simpa only [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hinv.map_mem hy

/-- Restriction of `oneVariableSpecializationHomologyEquivOfHomotopy` to each homogeneous bidegree
piece. -/
def oneVariableSpecializationHomologyPieceEquivOfHomotopy (g : ℤ × ℤ) :
    G.bigradedHatHomologyPiece R i g ≃ₗ[R] G.bigradedHatHomologyPiece R j g :=
  (G.1.oneVariableSpecializationHomologyEquivOfHomotopy R H hH).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv,
      ← G.oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece_iff R H hH
        hdeg,
      LinearEquiv.apply_symm_apply])

/-- Evaluating `oneVariableSpecializationHomologyPieceEquivOfHomotopy` on underlying classes. -/
@[simp]
theorem coe_oneVariableSpecializationHomologyPieceEquivOfHomotopy (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    (G.oneVariableSpecializationHomologyPieceEquivOfHomotopy R H hH hdeg g y :
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ j} R)).obj
          ((G.1.simplyBlockedComplex R j).homology ())) =
      G.1.oneVariableSpecializationHomologyEquivOfHomotopy R H hH y :=
  (rfl)

end Homotopy

section SameCycle

variable {i j : Fin n} (hc : G.1.componentPerm.SameCycle i j)

/-- For two columns `i` and `j` on the same link component of an odd-component grid diagram, an
`R`-linear equivalence between the homologies of the specializations `V_i = 0` and `V_j = 0`. -/
def oneVariableSpecializationHomologySameCycleEquiv :
    (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
          ((G.1.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ j} R)).obj
          ((G.1.simplyBlockedComplex R j).homology ()) :=
  G.1.oneVariableSpecializationHomologyEquivOfHomotopy R
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose_spec.1

/-- `oneVariableSpecializationHomologySameCycleEquiv` is homogeneous of bidegree `(0, 0)`. -/
theorem isHomogeneous_oneVariableSpecializationHomologySameCycleEquiv :
    LinearMap.IsHomogeneous
      (G.oneVariableSpecializationHomologySameCycleEquiv R hc).toLinearMap
      (G.bigradedHatHomologyGrading R i).piece
      (G.bigradedHatHomologyGrading R j).piece 0 :=
  G.isHomogeneous_oneVariableSpecializationHomologyEquivOfHomotopy R _
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose_spec.1
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose_spec.2

/-- `oneVariableSpecializationHomologySameCycleEquiv` preserves and reflects homology bidegrees. -/
@[simp]
theorem oneVariableSpecializationHomologySameCycleEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ}
    {y : (ModuleCat.restrictScalars
      (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
        ((G.1.simplyBlockedComplex R i).homology ())} :
    G.oneVariableSpecializationHomologySameCycleEquiv R hc y ∈
        G.bigradedHatHomologyPiece R j g ↔
      y ∈ G.bigradedHatHomologyPiece R i g :=
  G.oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece_iff R _
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose_spec.1
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose_spec.2

/-- Restriction of `oneVariableSpecializationHomologySameCycleEquiv` to a homogeneous bidegree
piece. -/
def oneVariableSpecializationHomologySameCyclePieceEquiv (g : ℤ × ℤ) :
    G.bigradedHatHomologyPiece R i g ≃ₗ[R] G.bigradedHatHomologyPiece R j g :=
  G.oneVariableSpecializationHomologyPieceEquivOfHomotopy R _
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose_spec.1
    (G.exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle R hc).choose_spec.2 g

/-- Evaluating `oneVariableSpecializationHomologySameCyclePieceEquiv` on underlying classes. -/
@[simp]
theorem coe_oneVariableSpecializationHomologySameCyclePieceEquiv (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    (G.oneVariableSpecializationHomologySameCyclePieceEquiv R hc g y :
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ j} R)).obj
          ((G.1.simplyBlockedComplex R j).homology ())) =
      G.oneVariableSpecializationHomologySameCycleEquiv R hc y :=
  (rfl)

end SameCycle

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

include hG in
private theorem sameCycle_of_isKnot (i j : Fin n) : G.componentPerm.SameCycle i j :=
  ((G.isKnot_iff_componentPerm_isCycle).mp hG).sameCycle
    (G.componentPerm_apply_ne_self i) (G.componentPerm_apply_ne_self j)

section Ring

variable (R : Type*) [CommRing R] [CharP R 2] (i j : Fin n)

/-- **Independence of `G-hat` from the choice of blocked `O`-marking.** For a knot grid `G` and any
two columns `i` and `j`, an `R`-linear equivalence between the simply blocked homologies blocking
`i` and blocking `j` that preserves and reflects the `(O-Maslov, Alexander)` bigrading. -/
def simplyBlockedHomologyBasepointEquiv :
    (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
          (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ j} R)).obj
          (hG.simplyBlockedHomology R j) :=
  hG.toOddComponentGridDiagram.oneVariableSpecializationHomologySameCycleEquiv R
    (sameCycle_of_isKnot hG i j)

/-- `simplyBlockedHomologyBasepointEquiv` is homogeneous of bidegree `(0, 0)`. -/
theorem isHomogeneous_simplyBlockedHomologyBasepointEquiv :
    LinearMap.IsHomogeneous
      (hG.simplyBlockedHomologyBasepointEquiv R i j).toLinearMap
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R j).piece 0 :=
  hG.toOddComponentGridDiagram.isHomogeneous_oneVariableSpecializationHomologySameCycleEquiv R
    (sameCycle_of_isKnot hG i j)

/-- `simplyBlockedHomologyBasepointEquiv` preserves and reflects both homology degrees of
`G-hat`. -/
@[simp]
theorem simplyBlockedHomologyBasepointEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ}
    {y : (ModuleCat.restrictScalars
      (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
        (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyBasepointEquiv R i j y ∈
        hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  open OddComponentGridDiagram in
  oneVariableSpecializationHomologySameCycleEquiv_mem_bigradedHatHomologyPiece_iff
    hG.toOddComponentGridDiagram R (sameCycle_of_isKnot hG i j)

/-- Restriction of `simplyBlockedHomologyBasepointEquiv` to a homogeneous bidegree piece of
`G-hat`. -/
def simplyBlockedHomologyBasepointPieceEquiv (g : ℤ × ℤ) :
    hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g :=
  hG.toOddComponentGridDiagram.oneVariableSpecializationHomologySameCyclePieceEquiv R
    (sameCycle_of_isKnot hG i j) g

/-- Evaluating `simplyBlockedHomologyBasepointPieceEquiv` agrees with
`simplyBlockedHomologyBasepointEquiv` on underlying classes. -/
@[simp]
theorem coe_simplyBlockedHomologyBasepointPieceEquiv (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyBasepointPieceEquiv R i j g y :
      (ModuleCat.restrictScalars
        (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ j} R)).obj
          (hG.simplyBlockedHomology R j)) =
      hG.simplyBlockedHomologyBasepointEquiv R i j y :=
  hG.toOddComponentGridDiagram.coe_oneVariableSpecializationHomologySameCyclePieceEquiv R
    (sameCycle_of_isKnot hG i j) g y

end Ring

section Field

variable (K : Type*) [Field K] [CharP K 2] (i j : Fin n)

/-- **The bigraded Poincaré series of `G-hat` is independent of the blocked column.** -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_eq :
    hG.bigradedSimplyBlockedHomologyPoincareSeries K i =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K j := by
  ext g
  simp only [coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact (hG.simplyBlockedHomologyBasepointPieceEquiv K i j g).finrank_eq

/-- **The Alexander-graded Euler characteristic of `G-hat` is independent of the blocked
column.** -/
theorem gradedSimplyBlockedHomologyEulerChar_eq :
    hG.gradedSimplyBlockedHomologyEulerChar K i =
      hG.gradedSimplyBlockedHomologyEulerChar K j := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_eq K i j]

end Field

end TauCeti.GridDiagram.IsKnot
