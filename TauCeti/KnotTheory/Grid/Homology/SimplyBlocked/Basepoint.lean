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

Setting `V_i = 0` on `GC⁻` presents `GC^_i` as the quotient of `GC⁻` by the injective chain map
`V_i • id`, identifying its `R`-module homology with the mapping-cone homology of `V_i • id` on
`GC⁻`. In characteristic two, any polynomial-linear `H` on `GC⁻` with
`∂⁻ ∘ H + H ∘ ∂⁻ = (V_i + V_j) • id` shears `(a, b) ↦ (a, H a + b)` between the cones of `V_i` and
`V_j` (`LinearMap.homologyEquivOfHomotopicInjective`), inducing an `R`-linear equivalence between
the homologies of `GC^_i` and `GC^_j`.

On an odd-component grid diagram, if `H` lowers the `(O-Maslov, Alexander)` bidegree by `(1, 1)`
(`OddComponentGridDiagram.componentPathXHomotopy_mem_bigradedChainMinusPiece`), a cycle of
bidegree `g` in `GC^_i` lifts to `b ∈ GC⁻_g` with `∂⁻ b = -V_i • a`; since `∂⁻` has bidegree
`(-1, 0)` and `V_i` has bidegree `(-2, -1)`, `a` has bidegree `g + (1, 1)` and `H a + b` has
bidegree `g`, making the homology equivalence homogeneous of bidegree `(0, 0)`. For a knot grid all
`O`-markings lie on one component, so bigraded `G-hat` and (over a field of characteristic two) its
Poincaré series and Euler characteristic do not depend on the blocked column.

## Main definitions and results

* `TauCeti.GridDiagram.oneVariableSpecializationHomologyEquivOfHomotopy` and
  `oneVariableSpecializationHomologyEquivOfHomotopy_class`: the `R`-linear homology comparison from
  a homotopy between `V_i` and `V_j` on `GC⁻`, and its explicit formula on lifted cycles.
* `TauCeti.GridDiagram.oneVariableSpecializationHomologySameCycleEquiv`: the `R`-linear equivalence
  between the homologies of `V_i = 0` and `V_j = 0` when `i` and `j` lie on the same link
  component, homogeneous of bidegree `(0, 0)` on odd-component grid diagrams.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyBasepointEquiv`,
  `simplyBlockedHomologyBasepointPieceEquiv`, `bigradedSimplyBlockedHomologyPoincareSeries_eq`, and
  `gradedSimplyBlockedHomologyEulerChar_eq`: basepoint independence of bigraded `G-hat`, its
  homogeneous pieces, its Poincaré series, and its Euler characteristic.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Proposition 4.6.15.
-/

public section

noncomputable section

open CategoryTheory

local notation "Base(" R ", " n ", " i ")" =>
  ModuleCat.restrictScalars (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)

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

private theorem xSmulEnd_apply (i : Fin n) (c : GridChainMinus R n) :
    xSmulEnd R i c = (MvPolynomial.X i : MvPolynomial (Fin n) R) • c :=
  (rfl)

private theorem xSmulEnd_injective (i : Fin n) : Function.Injective (xSmulEnd R i) :=
  X_smul_gridChainMinus_injective R i

private theorem xSmulEnd_comp_dMinus (i : Fin n) :
    xSmulEnd R i ∘ₗ dMinus G R = dMinus G R ∘ₗ xSmulEnd R i :=
  LinearMap.ext fun c => (map_smul (G.unblockedDifferential R) (MvPolynomial.X i) c).symm

private def specLinearMap (i : Fin n) : GridChainMinus R n →ₗ[R] GridChainHat R n i where
  toFun := simplyBlockedSpecialization R i
  map_add' := map_add _
  map_smul' r c := Finsupp.ext fun x => by
    simp only [simplyBlockedSpecialization_apply, Finsupp.smul_apply, RingHom.id_apply]
    exact (MvPolynomial.killCompl (f := Subtype.val) Subtype.val_injective).toLinearMap.map_smul r _

private theorem specLinearMap_apply (i : Fin n) (c : GridChainMinus R n) :
    specLinearMap R i c = simplyBlockedSpecialization R i c :=
  (rfl)

private theorem specLinearMap_surjective (i : Fin n) : Function.Surjective (specLinearMap R i) :=
  simplyBlockedSpecialization_surjective R i

private theorem exact_xSmulEnd_specLinearMap (i : Fin n) :
    Function.Exact (xSmulEnd R i) (specLinearMap R i) :=
  exact_X_smul_simplyBlockedSpecialization R i

private theorem specLinearMap_comp_dMinus (i : Fin n) :
    specLinearMap R i ∘ₗ dMinus G R = dHat G R i ∘ₗ specLinearMap R i :=
  LinearMap.ext (G.simplyBlockedSpecialization_unblockedDifferential R i)

variable [CharP R 2]

private theorem dMinus_comp_self : dMinus G R ∘ₗ dMinus G R = 0 :=
  LinearMap.ext fun c => congr($(G.unblockedDifferential_comp_self_eq_zero R) c)

private theorem dHat_comp_self (i : Fin n) : dHat G R i ∘ₗ dHat G R i = 0 :=
  LinearMap.ext fun c => congr($(G.simplyBlockedDifferential_comp_self_eq_zero R i) c)

private theorem homotopy_restrictScalars {i j : Fin n}
    (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id) :
    dMinus G R ∘ₗ H.restrictScalars R + H.restrictScalars R ∘ₗ dMinus G R =
      xSmulEnd R i - xSmulEnd R j :=
  LinearMap.ext fun c => by
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
    (Base(R, n, i)).obj ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (Base(R, n, j)).obj ((G.simplyBlockedComplex R j).homology ()) :=
  (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv R i).symm.trans <|
    (LinearMap.homologyEquivOfHomotopicInjective
      (π₁ := specLinearMap R i) (π₂ := specLinearMap R j)
      (dMinus_comp_self G R) (dMinus_comp_self G R)
      (dHat_comp_self G R i) (dHat_comp_self G R j)
      (xSmulEnd_comp_dMinus G R i) (xSmulEnd_comp_dMinus G R j)
      (xSmulEnd_injective R i) (xSmulEnd_injective R j)
      (homotopy_restrictScalars G R H hH)
      (specLinearMap_surjective R i) (specLinearMap_surjective R j)
      (exact_xSmulEnd_specLinearMap R i) (exact_xSmulEnd_specLinearMap R j)
      (specLinearMap_comp_dMinus G R i) (specLinearMap_comp_dMinus G R j)).trans
        (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv R j)

/-- If `V_i • a + ∂⁻ b = 0` on `GC⁻`, then `simplyBlockedSpecialization R j (H a + b)` is killed by
`simplyBlockedDifferential R j`. -/
theorem simplyBlockedDifferential_simplyBlockedSpecialization_add_eq_zero {i j : Fin n}
    (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (hH : G.unblockedDifferential R ∘ₗ H + H ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id)
    {a b : GridChainMinus R n}
    (hab : (MvPolynomial.X i : MvPolynomial (Fin n) R) • a + G.unblockedDifferential R b = 0) :
    G.simplyBlockedDifferential R j (simplyBlockedSpecialization R j (H a + b)) = 0 := by
  have hab' : xSmulEnd R i a + dMinus G R b = 0 := by
    rw [xSmulEnd_apply, dMinus, LinearMap.restrictScalars_apply]
    exact hab
  have hmem := LinearMap.map_add_mem_ker_of_homotopy (π₂ := specLinearMap R j)
    (dMinus_comp_self G R) (xSmulEnd_comp_dMinus G R i) (xSmulEnd_injective R i)
    (homotopy_restrictScalars G R H hH)
    (exact_xSmulEnd_specLinearMap R j) (specLinearMap_comp_dMinus G R j) hab'
  simpa only [LinearMap.mem_ker, dHat, specLinearMap_apply, LinearMap.restrictScalars_apply]
    using hmem

/-- Explicit cycle-level formula for `oneVariableSpecializationHomologyEquivOfHomotopy`: if a cycle
`z` in the specialization `V_i = 0` lifts to `b` in `GC⁻` with `V_i • a + ∂⁻ b = 0`, then its class
maps to the class of `simplyBlockedSpecialization R j (H a + b)` in `V_j = 0`. -/
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
  have hab' : xSmulEnd R i a + dMinus G R b = 0 := by
    rw [xSmulEnd_apply, dMinus, LinearMap.restrictScalars_apply]
    exact hab
  have hz₁ : specLinearMap R i b ∈ LinearMap.ker (dHat G R i) := by
    rw [specLinearMap_apply, ← hz, LinearMap.mem_ker, dHat, LinearMap.restrictScalars_apply]
    exact (G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2
  have hsub : (⟨G.simplyBlockedChainEquiv R i z.1,
      (G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2⟩ : LinearMap.ker (dHat G R i)) =
      ⟨specLinearMap R i b, hz₁⟩ :=
    Subtype.ext (hz.trans (specLinearMap_apply R i b).symm)
  let e := LinearMap.homologyEquivOfHomotopicInjective
    (π₁ := specLinearMap R i) (π₂ := specLinearMap R j)
    (dMinus_comp_self G R) (dMinus_comp_self G R)
    (dHat_comp_self G R i) (dHat_comp_self G R j)
    (xSmulEnd_comp_dMinus G R i) (xSmulEnd_comp_dMinus G R j)
    (xSmulEnd_injective R i) (xSmulEnd_injective R j)
    (homotopy_restrictScalars G R H hH)
    (specLinearMap_surjective R i) (specLinearMap_surjective R j)
    (exact_xSmulEnd_specLinearMap R i) (exact_xSmulEnd_specLinearMap R j)
    (specLinearMap_comp_dMinus G R i) (specLinearMap_comp_dMinus G R j)
  have h1 : (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv R i).symm
      (G.oneVariableSpecializationHomologyClass R i z :
        (Base(R, n, i)).obj ((G.simplyBlockedComplex R i).homology ())) =
      Submodule.Quotient.mk ⟨specLinearMap R i b, hz₁⟩ :=
    (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv_symm_class R i z).trans
      (congrArg Submodule.Quotient.mk hsub)
  have h2 := LinearMap.homologyEquivOfHomotopicInjective_mk
    (π₁ := specLinearMap R i) (π₂ := specLinearMap R j)
    (dMinus_comp_self G R) (dMinus_comp_self G R)
    (dHat_comp_self G R i) (dHat_comp_self G R j)
    (xSmulEnd_comp_dMinus G R i) (xSmulEnd_comp_dMinus G R j)
    (xSmulEnd_injective R i) (xSmulEnd_injective R j)
    (homotopy_restrictScalars G R H hH)
    (specLinearMap_surjective R i) (specLinearMap_surjective R j)
    (exact_xSmulEnd_specLinearMap R i) (exact_xSmulEnd_specLinearMap R j)
    (specLinearMap_comp_dMinus G R i) (specLinearMap_comp_dMinus G R j) hab' hz₁
  exact (LinearEquiv.trans_apply
      (e₁₂ := (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv R i).symm)
      (e₂₃ := e.trans (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv R j)) _).trans <|
    (LinearEquiv.trans_apply
      (e₁₂ := e)
      (e₂₃ := G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv R j) _).trans <|
    (congrArg (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv R j)
      ((congrArg e h1).trans h2)).trans <|
    (G.simplyBlockedDifferentialRestrictScalarsHomologyEquiv_mk R j _).trans <|
      congrArg (G.oneVariableSpecializationHomologyClass R j)
        (Subtype.ext (congrArg (G.simplyBlockedChainEquiv R j).symm
          (by simp only [specLinearMap_apply, LinearMap.restrictScalars_apply])))

private theorem componentPathXHomotopy_homotopy_of_sameCycle {i j : Fin n}
    (hc : G.componentPerm.SameCycle i j) :
    G.unblockedDifferential R ∘ₗ G.componentPathXHomotopy R i hc.exists_nat_pow_eq.choose +
        G.componentPathXHomotopy R i hc.exists_nat_pow_eq.choose ∘ₗ G.unblockedDifferential R =
      (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id := by
  simpa only [hc.exists_nat_pow_eq.choose_spec] using
    G.unblockedDifferential_comp_componentPathXHomotopy_add_componentPathXHomotopy_comp
      R i hc.exists_nat_pow_eq.choose

/-- For two columns `i` and `j` on the same link component of a grid diagram, an `R`-linear
equivalence between the homologies of the specializations `V_i = 0` and `V_j = 0`. -/
def oneVariableSpecializationHomologySameCycleEquiv {i j : Fin n}
    (hc : G.componentPerm.SameCycle i j) :
    (Base(R, n, i)).obj ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (Base(R, n, j)).obj ((G.simplyBlockedComplex R j).homology ()) :=
  G.oneVariableSpecializationHomologyEquivOfHomotopy R
    (G.componentPathXHomotopy R i hc.exists_nat_pow_eq.choose)
    (componentPathXHomotopy_homotopy_of_sameCycle G R hc)

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
/-- If `H` lowers chain bidegrees by `(1, 1)`, the induced mapping-cone comparison between the
homologies of `V_i = 0` and `V_j = 0` preserves bidegrees. -/
theorem oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece
    {g : ℤ × ℤ} {y : (Base(R, n, i)).obj ((G.1.simplyBlockedComplex R i).homology ())}
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
      G.1.unblockedDifferential R b = 0 := by rw [smul_neg, ha', neg_add_cancel]
  have ha_mem : -a' ∈ G.bigradedChainMinusPiece R (g + (1, 1)) := by
    rw [← G.X_smul_mem_bigradedChainMinusPiece_iff i]
    have hg : g + (1, 1) - (2, 1) = g - (1, 0) := Prod.ext (by simp; omega) (by simp)
    rw [hg, smul_neg, ha']
    exact Submodule.neg_mem _ (G.unblockedDifferential_mem_bigradedChainMinusPiece hb)
  have hHab : H (-a') + b ∈ G.bigradedChainMinusPiece R g :=
    Submodule.add_mem _ (by simpa only [add_sub_cancel_right] using hdeg ha_mem) hb
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
      (G.bigradedHatHomologyGrading R j).piece 0 :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hy => by
    rw [bigradedHatHomologyGrading_piece] at hy
    rw [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe]
    exact G.oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece R H hH
      hdeg hy

include hdeg in
/-- When `H` lowers bidegrees by `(1, 1)`, `oneVariableSpecializationHomologyEquivOfHomotopy`
preserves and reflects homology bidegrees. -/
@[simp]
theorem oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base(R, n, i)).obj ((G.1.simplyBlockedComplex R i).homology ())} :
    G.1.oneVariableSpecializationHomologyEquivOfHomotopy R H hH y ∈
        G.bigradedHatHomologyPiece R j g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  refine ⟨fun hy => ?_,
    G.oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece R H hH hdeg⟩
  rw [← bigradedHatHomologyGrading_piece] at hy
  simpa only [add_zero, bigradedHatHomologyGrading_piece, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using
    (G.isHomogeneous_oneVariableSpecializationHomologyEquivOfHomotopy
      R H hH hdeg).linearEquiv_symm.map_mem hy

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
      (Base(R, n, j)).obj ((G.1.simplyBlockedComplex R j).homology ())) =
      G.1.oneVariableSpecializationHomologyEquivOfHomotopy R H hH y :=
  (rfl)

end Homotopy

section SameCycle

variable {i j : Fin n} (hc : G.1.componentPerm.SameCycle i j)

/-- `oneVariableSpecializationHomologySameCycleEquiv` is homogeneous of bidegree `(0, 0)`. -/
theorem isHomogeneous_oneVariableSpecializationHomologySameCycleEquiv :
    LinearMap.IsHomogeneous
      (G.1.oneVariableSpecializationHomologySameCycleEquiv R hc).toLinearMap
      (G.bigradedHatHomologyGrading R i).piece (G.bigradedHatHomologyGrading R j).piece 0 :=
  G.isHomogeneous_oneVariableSpecializationHomologyEquivOfHomotopy R _ _
    fun _ _ => G.componentPathXHomotopy_mem_bigradedChainMinusPiece i _

/-- `oneVariableSpecializationHomologySameCycleEquiv` preserves and reflects homology bidegrees. -/
@[simp]
theorem oneVariableSpecializationHomologySameCycleEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base(R, n, i)).obj ((G.1.simplyBlockedComplex R i).homology ())} :
    G.1.oneVariableSpecializationHomologySameCycleEquiv R hc y ∈
        G.bigradedHatHomologyPiece R j g ↔
      y ∈ G.bigradedHatHomologyPiece R i g :=
  G.oneVariableSpecializationHomologyEquivOfHomotopy_mem_bigradedHatHomologyPiece_iff R _ _
    fun _ _ => G.componentPathXHomotopy_mem_bigradedChainMinusPiece i _

/-- Restriction of `oneVariableSpecializationHomologySameCycleEquiv` to a homogeneous piece. -/
def oneVariableSpecializationHomologySameCyclePieceEquiv (g : ℤ × ℤ) :
    G.bigradedHatHomologyPiece R i g ≃ₗ[R] G.bigradedHatHomologyPiece R j g :=
  G.oneVariableSpecializationHomologyPieceEquivOfHomotopy R
    (G.1.componentPathXHomotopy R i hc.exists_nat_pow_eq.choose)
    (GridDiagram.componentPathXHomotopy_homotopy_of_sameCycle G.1 R hc)
    (fun _ _ => G.componentPathXHomotopy_mem_bigradedChainMinusPiece i _) g

/-- Evaluating `oneVariableSpecializationHomologySameCyclePieceEquiv` on underlying classes. -/
@[simp]
theorem coe_oneVariableSpecializationHomologySameCyclePieceEquiv (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    (G.oneVariableSpecializationHomologySameCyclePieceEquiv R hc g y :
      (Base(R, n, j)).obj ((G.1.simplyBlockedComplex R j).homology ())) =
      G.1.oneVariableSpecializationHomologySameCycleEquiv R hc y :=
  (rfl)

end SameCycle

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

section Ring

variable (R : Type*) [CommRing R] [CharP R 2] (i j : Fin n)

/-- **Independence of `G-hat` from the choice of blocked `O`-marking.** For a knot grid `G` and any
two columns `i` and `j`, a bidegree-preserving `R`-linear equivalence between the simply blocked
homologies blocking `i` and blocking `j`. -/
def simplyBlockedHomologyBasepointEquiv :
    (Base(R, n, i)).obj (hG.simplyBlockedHomology R i) ≃ₗ[R]
      (Base(R, n, j)).obj (hG.simplyBlockedHomology R j) :=
  G.oneVariableSpecializationHomologySameCycleEquiv R (hG.sameCycle_componentPerm i j)

/-- `simplyBlockedHomologyBasepointEquiv` is homogeneous of bidegree `(0, 0)`. -/
theorem isHomogeneous_simplyBlockedHomologyBasepointEquiv :
    LinearMap.IsHomogeneous (hG.simplyBlockedHomologyBasepointEquiv R i j).toLinearMap
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).piece
      (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R j).piece 0 :=
  hG.toOddComponentGridDiagram.isHomogeneous_oneVariableSpecializationHomologySameCycleEquiv R
    (hG.sameCycle_componentPerm i j)

/-- `simplyBlockedHomologyBasepointEquiv` preserves and reflects both homology degrees of
`G-hat`. -/
@[simp]
theorem simplyBlockedHomologyBasepointEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyBasepointEquiv R i j y ∈
        hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  open OddComponentGridDiagram in
  oneVariableSpecializationHomologySameCycleEquiv_mem_bigradedHatHomologyPiece_iff
    hG.toOddComponentGridDiagram R (hG.sameCycle_componentPerm i j)

/-- Restriction of `simplyBlockedHomologyBasepointEquiv` to a homogeneous piece of `G-hat`. -/
def simplyBlockedHomologyBasepointPieceEquiv (g : ℤ × ℤ) :
    hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R j g :=
  hG.toOddComponentGridDiagram.oneVariableSpecializationHomologySameCyclePieceEquiv R
    (hG.sameCycle_componentPerm i j) g

/-- Evaluating `simplyBlockedHomologyBasepointPieceEquiv` agrees with
`simplyBlockedHomologyBasepointEquiv` on underlying classes. -/
@[simp]
theorem coe_simplyBlockedHomologyBasepointPieceEquiv (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyBasepointPieceEquiv R i j g y :
      (Base(R, n, j)).obj (hG.simplyBlockedHomology R j)) =
      hG.simplyBlockedHomologyBasepointEquiv R i j y :=
  hG.toOddComponentGridDiagram.coe_oneVariableSpecializationHomologySameCyclePieceEquiv R
    (hG.sameCycle_componentPerm i j) g y

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
