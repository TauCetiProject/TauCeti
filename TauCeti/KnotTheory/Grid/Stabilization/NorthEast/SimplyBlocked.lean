/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SimplyBlocked.Basic
import TauCeti.KnotTheory.Grid.Homology.ExactSequence
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading
public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# North-east stabilization of one-variable-specialization homology

The north-east corner `X`-stabilization inserts a column after the split column `s` and a row
after its `X`-marking. The old `O`-marking of column `i` then lies in column
`s.succ.succAbove i`. Blocking that marking gives one-variable-specialization homology in the
same absolute `(O-Maslov, Alexander)` bidegrees as the original diagram whenever its component
count is odd. For knots this specialization is simply blocked homology.

This file specializes the existing unblocked north-east comparison to a semilinear map over
the surviving polynomial variables. It descends to a bijective semilinear homology map and,
after restricting scalars, a coefficient-linear equivalence on total homology and every
homogeneous piece. The cycle-class and chain-evaluation equations hide all carrier transport.
The underlying unblocked comparison conjugates the south-west comparison by half-turns,
retaining the grading normalization and blocked marking. For knots over a field of
characteristic two, the bigraded Poincaré series and Alexander-graded Euler characteristic
are unchanged.

The specialization construction and exact-sequence argument adapt the south-west comparison
in `Stabilization/SimplyBlocked/Basic.lean` and `Stabilization/SimplyBlocked/Homology.lean`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
-/

public section

open CategoryTheory

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (s i : Fin n) (R : Type*)

section Semiring

variable [CommSemiring R]

local notation "j" => s.succ.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The coefficient homomorphism of stabilization after blocking the transported old marking.
Merge the stabilization columns using `s.predAbove`, then kill the variable of column `i`. -/
noncomputable def simplyBlockedStabilizeXSuccRingHom : S →+* A :=
  (simplyBlockedRingHom R i).comp
    ((rename (R := R) s.predAbove).toRingHom.comp (rename Subtype.val).toRingHom)

/-- A surviving source variable is merged and then specialized in the old grid. In particular,
when `i = s`, the other variable of the stabilization block also maps to zero. -/
@[simp]
theorem simplyBlockedStabilizeXSuccRingHom_X (c : {c : Fin (n + 1) // c ≠ j}) :
    simplyBlockedStabilizeXSuccRingHom s i R (MvPolynomial.X c) =
      simplyBlockedRingHom R i (MvPolynomial.X (s.predAbove c)) := by
  simp [simplyBlockedStabilizeXSuccRingHom]

/-- Stabilization leaves ground-ring coefficients unchanged after blocking. -/
@[simp]
theorem simplyBlockedStabilizeXSuccRingHom_C (r : R) :
    simplyBlockedStabilizeXSuccRingHom s i R (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [simplyBlockedStabilizeXSuccRingHom]

/-- Merging columns commutes with blocking the transported old marking. -/
theorem simplyBlockedStabilizeXSuccRingHom_specialization (p : MvPolynomial (Fin (n + 1)) R) :
    simplyBlockedStabilizeXSuccRingHom s i R (simplyBlockedRingHom R j p) =
      simplyBlockedRingHom R i (rename s.predAbove p) := by
  have h : ((killCompl (R := R) (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
      Subtype.val_injective).comp ((rename s.predAbove).comp (rename Subtype.val))).comp
        (killCompl (f := (Subtype.val : {c : Fin (n + 1) // c ≠ j} → Fin (n + 1)))
          Subtype.val_injective) =
      (killCompl (f := (Subtype.val : {c : Fin n // c ≠ i} → Fin n))
        Subtype.val_injective).comp (rename s.predAbove) := by
    ext c
    by_cases hc : c = j
    · subst c
      simp [Fin.predAbove_succ_succAbove]
    · have hX : MvPolynomial.X c = rename Subtype.val
          (MvPolynomial.X (R := R) (⟨c, hc⟩ : {c : Fin (n + 1) // c ≠ j})) := by simp
      simp only [AlgHom.comp_apply]
      rw [hX, killCompl_rename_app]
  exact DFunLike.congr_fun h p

end Semiring

variable (G : GridDiagram n) [CommRing R]

local notation "j" => s.succ.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The stabilization comparison with the transported old `O`-marking blocked. Its image on a
generator is the specialization of the unblocked stabilization comparison. -/
noncomputable def simplyBlockedStabilizeXSuccMap :
    GridChainHat R (n + 1) j →ₛₗ[simplyBlockedStabilizeXSuccRingHom s i R]
      GridChainHat R n i :=
  (Finsupp.linearCombination A fun x : GridState (n + 1) =>
    simplyBlockedSpecialization R i (G.stabilizeXSuccChainMap s R (Finsupp.single x 1))).comp
      (Finsupp.mapRange.linearMap (simplyBlockedStabilizeXSuccRingHom s i R).toSemilinearMap)

/-- The specialized stabilization map on a single supported coefficient. -/
theorem simplyBlockedStabilizeXSuccMap_single (x : GridState (n + 1)) (p : S) :
    G.simplyBlockedStabilizeXSuccMap s i R (Finsupp.single x p) =
      simplyBlockedStabilizeXSuccRingHom s i R p •
        simplyBlockedSpecialization R i (G.stabilizeXSuccChainMap s R (Finsupp.single x 1)) := by
  simp [simplyBlockedStabilizeXSuccMap]

/-- The matrix formula for the specialized stabilization comparison. -/
@[simp]
theorem simplyBlockedStabilizeXSuccMap_apply_apply (c : GridChainHat R (n + 1) j)
    (y : GridState n) :
    G.simplyBlockedStabilizeXSuccMap s i R c y = c.sum fun x p =>
      simplyBlockedStabilizeXSuccRingHom s i R p *
        simplyBlockedRingHom R i (G.stabilizeXSuccChainMap s R (Finsupp.single x 1) y) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.zero_apply, Finsupp.sum_zero_index]
  | add c d hc hd =>
    rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.sum_add_index'] <;> simp [add_mul]
  | single x p =>
    rw [simplyBlockedStabilizeXSuccMap_single, Finsupp.smul_apply, smul_eq_mul,
      simplyBlockedSpecialization_apply, ← simplyBlockedRingHom_apply,
      Finsupp.sum_single_index (by simp)]

/-- The simply blocked comparison is the descent of the unblocked stabilization map through
coefficient specialization. -/
@[simp↓]
theorem simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization (c : GridChainMinus R (n + 1)) :
    G.simplyBlockedStabilizeXSuccMap s i R (simplyBlockedSpecialization R j c) =
      simplyBlockedSpecialization R i (G.stabilizeXSuccChainMap s R c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x p =>
    rw [simplyBlockedSpecialization_single, simplyBlockedStabilizeXSuccMap_single,
      ← simplyBlockedRingHom_apply, simplyBlockedStabilizeXSuccRingHom_specialization,
      ← Finsupp.smul_single_one x p, map_smulₛₗ, map_smulₛₗ]
    rfl

variable [CharP R 2]

/-- Stabilization commutes with the simply blocked differentials. -/
theorem simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential (c : GridChainHat R (n + 1) j) :
    G.simplyBlockedStabilizeXSuccMap s i R
        ((G.stabilizeX s.succ (G.X s).succ s).simplyBlockedDifferential R j c) =
      G.simplyBlockedDifferential R i (G.simplyBlockedStabilizeXSuccMap s i R c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R j c
  rw [← simplyBlockedSpecialization_unblockedDifferential,
    simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization,
    simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization,
    ← simplyBlockedSpecialization_unblockedDifferential,
    stabilizeXSuccChainMap_unblockedDifferential]

/-! ### Quasi-isomorphism after blocking -/

local notation "G'" => GridDiagram.stabilizeX G (Fin.succ s)
  (Fin.succ (GridDiagram.X G s)) s

omit [CharP R 2] in
/-- Stabilization carries multiplication by the variable of the transported marking to
multiplication by `V_i`. -/
private theorem stabilizeXSuccChainMap_X_smul (c : GridChainMinus R (n + 1)) :
    G.stabilizeXSuccChainMap s R ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) • c) =
      (MvPolynomial.X i : MvPolynomial (Fin n) R) • G.stabilizeXSuccChainMap s R c := by
  rw [map_smulₛₗ]
  simp [Fin.predAbove_succ_succAbove]

private theorem exists_sub_stabilizeXSuccChainMap_mem_range {c : GridChainMinus R n}
    (hc : c ∈ LinearMap.ker (G.unblockedDifferential R)) :
    ∃ m ∈ LinearMap.ker ((G').unblockedDifferential R),
      c - G.stabilizeXSuccChainMap s R m ∈ LinearMap.range (G.unblockedDifferential R) := by
  obtain ⟨y, hy⟩ := (G.stabilizeXSuccHomologyMap_bijective s R).2
    (G.unblockedHomologyClass R ⟨c, hc⟩)
  obtain ⟨z, rfl⟩ := (G').unblockedHomologyClass_surjective R y
  refine ⟨z, z.2, ?_⟩
  rw [stabilizeXSuccHomologyMap_unblockedHomologyClass] at hy
  have he : G.unblockedHomologyClass R
      (⟨c, hc⟩ - ⟨G.stabilizeXSuccChainMap s R z,
        G.stabilizeXSuccChainMap_mem_ker s R z.2⟩) = 0 := by
    calc
      _ = G.unblockedHomologyClass R ⟨c, hc⟩ -
          G.unblockedHomologyClass R ⟨G.stabilizeXSuccChainMap s R z,
            G.stabilizeXSuccChainMap_mem_ker s R z.2⟩ := map_sub _ _ _
      _ = 0 := sub_eq_zero.mpr hy.symm
  exact (G.unblockedHomologyClass_eq_zero_iff R _).1 he

private theorem mem_range_of_stabilizeXSuccChainMap_mem_range {m : GridChainMinus R (n + 1)}
    (hm : m ∈ LinearMap.ker ((G').unblockedDifferential R))
    (h : G.stabilizeXSuccChainMap s R m ∈ LinearMap.range (G.unblockedDifferential R)) :
    m ∈ LinearMap.range ((G').unblockedDifferential R) := by
  apply ((G').unblockedHomologyClass_eq_zero_iff R ⟨m, hm⟩).1
  apply (G.stabilizeXSuccHomologyMap_bijective s R).1
  rw [map_zero, stabilizeXSuccHomologyMap_unblockedHomologyClass,
    unblockedHomologyClass_eq_zero_iff]
  exact h

/-- `exists_sub_stabilizeXSuccChainMap_mem_range` for the underlying additive maps. -/
private theorem exists_sub_stabilizeXSuccChainMap_mem_addRange (c : GridChainMinus R n)
    (hc : c ∈ (G.unblockedDifferential R).toAddMonoidHom.ker) :
    ∃ m ∈ ((G').unblockedDifferential R).toAddMonoidHom.ker,
      c - (G.stabilizeXSuccChainMap s R).toAddMonoidHom m ∈
        (G.unblockedDifferential R).toAddMonoidHom.range := by
  simpa using G.exists_sub_stabilizeXSuccChainMap_mem_range s R (by simpa using hc)

/-- `mem_range_of_stabilizeXSuccChainMap_mem_range` for the underlying additive maps. -/
private theorem mem_addRange_of_stabilizeXSuccChainMap_mem_addRange (m : GridChainMinus R (n + 1))
    (hm : m ∈ ((G').unblockedDifferential R).toAddMonoidHom.ker)
    (h : (G.stabilizeXSuccChainMap s R).toAddMonoidHom m ∈
      (G.unblockedDifferential R).toAddMonoidHom.range) :
    m ∈ ((G').unblockedDifferential R).toAddMonoidHom.range := by
  simpa using G.mem_range_of_stabilizeXSuccChainMap_mem_range s R (by simpa using hm)
    (by simpa using h)

/-- Every simply blocked cycle of `G` differs from the image of a simply blocked cycle of the
stabilized diagram by a boundary. -/
private theorem exists_sub_simplyBlockedStabilizeXSuccMap_mem_range {y : GridChainHat R n i}
    (hy : y ∈ LinearMap.ker (G.simplyBlockedDifferential R i)) :
    ∃ x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j),
      y - G.simplyBlockedStabilizeXSuccMap s i R x ∈
        LinearMap.range (G.simplyBlockedDifferential R i) := by
  -- Specialization at the blocked variable is a morphism from the short exact sequence
  -- `0 → GC⁻ --V_j--> GC⁻ → GC^ → 0` of the stabilized diagram to that of `G`.
  -- The unblocked stabilization map is a quasi-isomorphism.
  simpa using AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact
    (G.simplyBlockedStabilizeXSuccMap s i R).toAddMonoidHom
    (f₁ := (G.stabilizeXSuccChainMap s R).toAddMonoidHom)
    (f := (G.stabilizeXSuccChainMap s R).toAddMonoidHom)
    ((G').isShortExactDifferential_X_smul_simplyBlockedSpecialization R j)
    (G.isShortExactDifferential_X_smul_simplyBlockedSpecialization R i)
    (G.stabilizeXSuccChainMap_unblockedDifferential s R)
    (G.stabilizeXSuccChainMap_X_smul s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization s i R)
    (G.exists_sub_stabilizeXSuccChainMap_mem_addRange s R)
    (G.exists_sub_stabilizeXSuccChainMap_mem_addRange s R)
    (G.mem_addRange_of_stabilizeXSuccChainMap_mem_addRange s R) (by simpa using hy)

/-- A simply blocked cycle of the stabilized diagram whose image in `G` is a boundary is itself a
boundary. -/
private theorem mem_range_of_simplyBlockedStabilizeXSuccMap_mem_range {x : GridChainHat R (n + 1) j}
    (hx : x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j))
    (h : G.simplyBlockedStabilizeXSuccMap s i R x ∈
      LinearMap.range (G.simplyBlockedDifferential R i)) :
    x ∈ LinearMap.range ((G').simplyBlockedDifferential R j) := by
  -- The same morphism of short exact sequences as in
  -- `exists_sub_simplyBlockedStabilizeXSuccMap_mem_range`.
  simpa using AddMonoidHom.mem_range_of_map_mem_range_of_exact
    (G.simplyBlockedStabilizeXSuccMap s i R).toAddMonoidHom
    (f₁ := (G.stabilizeXSuccChainMap s R).toAddMonoidHom)
    (f := (G.stabilizeXSuccChainMap s R).toAddMonoidHom)
    ((G').isShortExactDifferential_X_smul_simplyBlockedSpecialization R j)
    (G.isShortExactDifferential_X_smul_simplyBlockedSpecialization R i)
    (G.stabilizeXSuccChainMap_unblockedDifferential s R)
    (G.stabilizeXSuccChainMap_unblockedDifferential s R)
    (G.stabilizeXSuccChainMap_X_smul s i R)
    (G.simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization s i R)
    (G.exists_sub_stabilizeXSuccChainMap_mem_addRange s R)
    (G.mem_addRange_of_stabilizeXSuccChainMap_mem_addRange s R)
    (G.mem_addRange_of_stabilizeXSuccChainMap_mem_addRange s R)
    (by simpa using hx) (by simpa using h)

end TauCeti.GridDiagram

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "G'" => GridDiagram.stabilizeX G (Fin.succ s)
  (Fin.succ (GridDiagram.X G s)) s
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The specialized stabilization map between the categorical chain carriers. -/
private noncomputable def oneVariableSpecializationStabilizeXSuccChainMap :
    ((G').simplyBlockedComplex R j).X () →ₛₗ[simplyBlockedStabilizeXSuccRingHom s i R]
      (G.simplyBlockedComplex R i).X () :=
  (G.simplyBlockedChainEquiv R i).symm.toLinearMap.comp
    ((G.simplyBlockedStabilizeXSuccMap s i R).comp
      ((G').simplyBlockedChainEquiv R j).toLinearMap)

private theorem oneVariableSpecializationStabilizeXSuccChainMap_d
    (z : ((G').simplyBlockedComplex R j).X ()) :
    oneVariableSpecializationStabilizeXSuccChainMap G s i R
        (((G').simplyBlockedComplex R j).d () () z) =
      (G.simplyBlockedComplex R i).d () ()
        (oneVariableSpecializationStabilizeXSuccChainMap G s i R z) := by
  apply (G.simplyBlockedChainEquiv R i).injective
  simp only [oneVariableSpecializationStabilizeXSuccChainMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, simplyBlockedChainEquiv_d]
  exact G.simplyBlockedStabilizeXSuccMap_simplyBlockedDifferential s i R _

/-- Stabilization on cycles of the one-variable specialization, with the chosen old `O`-marking
blocked in each diagram. -/
noncomputable def oneVariableSpecializationStabilizeXSuccCyclesMap :
    LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom
      →ₛₗ[simplyBlockedStabilizeXSuccRingHom s i R]
      LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom :=
  (oneVariableSpecializationStabilizeXSuccChainMap G s i R).restrict fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    rw [← oneVariableSpecializationStabilizeXSuccChainMap_d, hz, map_zero]

/-- Under the explicit chain identifications, the map on cycles of the one-variable specialization
is `simplyBlockedStabilizeXSuccMap`. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXSuccCyclesMap
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.simplyBlockedChainEquiv R i (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) =
      G.simplyBlockedStabilizeXSuccMap s i R ((G').simplyBlockedChainEquiv R j z) := by
  simp only [oneVariableSpecializationStabilizeXSuccCyclesMap, LinearMap.coe_restrict_apply,
    oneVariableSpecializationStabilizeXSuccChainMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

private theorem oneVariableSpecializationStabilizeXSuccCyclesMap_mem_boundariesInKer
    {z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom}
    (hz : z ∈ (((G').simplyBlockedComplex R j).d () ()).hom.boundariesInKer) :
    G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z ∈
      ((G.simplyBlockedComplex R i).d () ()).hom.boundariesInKer := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨oneVariableSpecializationStabilizeXSuccChainMap G s i R w, ?_⟩
  simp only [Submodule.subtype_apply, oneVariableSpecializationStabilizeXSuccCyclesMap,
    LinearMap.coe_restrict_apply] at hw ⊢
  rw [← hw, oneVariableSpecializationStabilizeXSuccChainMap_d]

/-- The specified semilinear stabilization comparison on the homology of the one-variable
specialization, from the stabilized grid to the original grid. -/
noncomputable def oneVariableSpecializationStabilizeXSuccHomologyMap :
    ((G').simplyBlockedComplex R j).homology () →ₛₗ[simplyBlockedStabilizeXSuccRingHom s i R]
      (G.simplyBlockedComplex R i).homology () :=
  (G.simplyBlockedComplex R i).moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
    ((Submodule.mapQ
      (((G').simplyBlockedComplex R j).d () ()).hom.boundariesInKer
      ((G.simplyBlockedComplex R i).d () ()).hom.boundariesInKer
      (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R)
      (fun _ hz =>
        G.oneVariableSpecializationStabilizeXSuccCyclesMap_mem_boundariesInKer s i R hz)).comp
          ((G').simplyBlockedComplex R j).moduleCatHomologyIso.toLinearEquiv.toLinearMap)

/-- The stabilization comparison on the one-variable specialization sends a cycle class to the class
of its stabilization image. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyMap_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R
        ((G').oneVariableSpecializationHomologyClass R j z) =
      G.oneVariableSpecializationHomologyClass R i
        (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) := by
  simp only [oneVariableSpecializationStabilizeXSuccHomologyMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    HomologicalComplex.moduleCatHomologyIso_hom_moduleCatKerHomologyClass,
    HomologicalComplex.moduleCatHomologyIso_hom_moduleCatKerHomologyClass,
    LinearMap.homologyπ_apply, LinearMap.homologyπ_apply, Submodule.mapQ_apply]

/-- **Stabilization invariance for the one-variable specialization.** For any grid diagram `G`, the
stabilization map from the homology of the specialization `V_{s.succ.succAbove i} = 0` of `G'`
to the homology of the specialization `V_i = 0` of `G` is bijective. -/
theorem oneVariableSpecializationStabilizeXSuccHomologyMap_bijective :
    Function.Bijective (G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun y => ?_⟩
  · -- A cycle whose stabilization image is a boundary is a boundary.
    obtain ⟨z, rfl⟩ := (G').oneVariableSpecializationHomologyClass_surjective R j y
    rw [oneVariableSpecializationStabilizeXSuccHomologyMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff,
      simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXSuccCyclesMap] at hy
    rw [oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff]
    exact G.mem_range_of_simplyBlockedStabilizeXSuccMap_mem_range s i R
      (((G').mem_ker_simplyBlockedComplex_d_iff R j z.1).mp z.2) hy
  · -- Every cycle differs from the stabilization image of a cycle by a boundary.
    obtain ⟨y, rfl⟩ := G.oneVariableSpecializationHomologyClass_surjective R i y
    obtain ⟨x, hx, hxy⟩ := G.exists_sub_simplyBlockedStabilizeXSuccMap_mem_range s i R
      ((G.mem_ker_simplyBlockedComplex_d_iff R i y.1).mp y.2)
    let z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom :=
      ⟨((G').simplyBlockedChainEquiv R j).symm x, by
        rw [mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
        exact hx⟩
    refine ⟨(G').oneVariableSpecializationHomologyClass R j z, ?_⟩
    rw [oneVariableSpecializationStabilizeXSuccHomologyMap_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff, Submodule.coe_sub, map_sub,
      simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXSuccCyclesMap,
      LinearEquiv.apply_symm_apply, ← neg_sub]
    exact neg_mem hxy

/-- The stabilization comparison on the homology of the one-variable specialization, packaged as an
`R`-linear equivalence by restricting scalars along `MvPolynomial.C`. -/
noncomputable def oneVariableSpecializationStabilizeXSuccHomologyEquiv :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
        (((G').simplyBlockedComplex R j).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)).obj
        ((G.simplyBlockedComplex R i).homology ()) :=
  LinearEquiv.ofBijective
    ({ toFun := G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R
       map_add' := map_add _
       map_smul' := fun r y => by
         have h := (G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R).map_smulₛₗ
           (MvPolynomial.C r) y
         rwa [simplyBlockedStabilizeXSuccRingHom_C] at h } :
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
          (((G').simplyBlockedComplex R j).homology ()) →ₗ[R]
        (ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)).obj
          ((G.simplyBlockedComplex R i).homology ()))
    (G.oneVariableSpecializationStabilizeXSuccHomologyMap_bijective s i R)

/-- On elements, the coefficient-linear equivalence is the semilinear stabilization map. -/
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_apply
    (y : (ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)).obj
      (((G').simplyBlockedComplex R j).homology ())) :
    G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y =
      G.oneVariableSpecializationStabilizeXSuccHomologyMap s i R y :=
  (rfl)

/-- The total north-east comparison sends a cycle class to the class of its cycle image. -/
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R
        ((G').oneVariableSpecializationHomologyClass R j z) :
          (G.simplyBlockedComplex R i).homology ()) =
      G.oneVariableSpecializationHomologyClass R i
        (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z) :=
  G.oneVariableSpecializationStabilizeXSuccHomologyMap_oneVariableSpecializationHomologyClass
    s i R z

/-- The inverse total comparison recovers a cycle class from the class of its north-east image. -/
theorem
    oneVariableSpecializationStabilizeXSuccHomologyEquiv_symm_homologyClass_cyclesMap
    (z : LinearMap.ker (((G').simplyBlockedComplex R j).d () ()).hom) :
    ((G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm
        (G.oneVariableSpecializationHomologyClass R i
          (G.oneVariableSpecializationStabilizeXSuccCyclesMap s i R z)) :
              ((G').simplyBlockedComplex R j).homology ()) =
      (G').oneVariableSpecializationHomologyClass R j z := by
  rw [←
    oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
      G s i R z]
  exact (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm_apply_apply _

end TauCeti.GridDiagram

namespace TauCeti.OddComponentGridDiagram

open GridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R
local notation "BaseA" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* A)
local notation "BaseS" => ModuleCat.restrictScalars (MvPolynomial.C : R →+* S)

omit [CharP R 2] in
/-- The specialized north-east chain comparison preserves absolute bidegrees. -/
theorem simplyBlockedStabilizeXSuccMap_mem_bigradedChainHatPiece {g : ℤ × ℤ}
    {c : GridChainHat R (n + 1) j}
    (hc : c ∈ (G.stabilizeXSucc s).bigradedChainHatPiece R j g) :
    G.1.simplyBlockedStabilizeXSuccMap s i R c ∈ G.bigradedChainHatPiece R i g := by
  obtain ⟨b, hb, rfl⟩ := (G.stabilizeXSucc s).mem_bigradedChainHatPiece_iff_exists.mp hc
  rw [GridDiagram.simplyBlockedStabilizeXSuccMap_simplyBlockedSpecialization]
  exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i
    (G.stabilizeXSuccChainMap_mem_bigradedChainMinusPiece s R hb)

/-- The north-east total homology comparison is homogeneous of bidegree zero. -/
theorem isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv :
    LinearMap.IsHomogeneous
      (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).toLinearMap
      ((G.stabilizeXSucc s).bigradedHatHomologyGrading R j).piece
      (G.bigradedHatHomologyGrading R i).piece 0 := by
  refine (G.stabilizeXSucc s).isHomogeneous_oneVariableSpecializationHomologyMap R j G i
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).toLinearMap
    (G.1.oneVariableSpecializationStabilizeXSuccCyclesMap s i R) ?_ ?_
  · intro z
    exact
      oneVariableSpecializationStabilizeXSuccHomologyEquiv_oneVariableSpecializationHomologyClass
        G.1 s i R z
  · intro g z hz
    rw [GridDiagram.simplyBlockedChainEquiv_oneVariableSpecializationStabilizeXSuccCyclesMap]
    exact G.simplyBlockedStabilizeXSuccMap_mem_bigradedChainHatPiece s i R hz

/-- The north-east comparison preserves and reflects the absolute homology bidegree. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ)
    (y : (BaseS).obj (((G.stabilizeXSucc s).1.simplyBlockedComplex R j).homology ())) :
    G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y ∈
        G.bigradedHatHomologyPiece R i g ↔
      y ∈ (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g := by
  simpa only [bigradedHatHomologyGrading_piece] using
    LinearMap.IsHomogeneous.linearEquiv_mem_piece_iff
      (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g y

/-- The inverse north-east comparison preserves and reflects the absolute homology bidegree. -/
@[simp]
theorem oneVariableSpecializationStabilizeXSuccHomologyEquiv_symm_mem_bigradedHatHomologyPiece_iff
    (g : ℤ × ℤ) (y : (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) :
    (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y ∈
        (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g ↔
      y ∈ G.bigradedHatHomologyPiece R i g := by
  simpa only [LinearEquiv.apply_symm_apply] using
    (G.oneVariableSpecializationStabilizeXSuccHomologyEquiv_mem_bigradedHatHomologyPiece_iff s i R g
      ((G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y)).symm

/-- North-east `X`-stabilization identifies each homogeneous piece, blocking the transported old
`O`-marking and preserving absolute `O`-Maslov and Alexander bidegrees. -/
noncomputable def oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv (g : ℤ × ℤ) :
    (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g ≃ₗ[R]
      G.bigradedHatHomologyPiece R i g :=
  ((LinearEquiv.ofEq _ _ ((G.stabilizeXSucc s).bigradedHatHomologyGrading_piece R j g).symm).trans
    (LinearMap.IsHomogeneous.pieceEquiv
      (G.isHomogeneous_oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R) g)).trans
      (LinearEquiv.ofEq _ _ (G.bigradedHatHomologyGrading_piece R i g))

/-- The piece comparison is the restriction of the total homology comparison. -/
@[simp↓]
theorem coe_oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv_apply (g : ℤ × ℤ)
    (y : (G.stabilizeXSucc s).bigradedHatHomologyPiece R j g) :
    (G.oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv s i R g y :
        (BaseA).obj ((G.1.simplyBlockedComplex R i).homology ())) =
      G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R y := by
  simp only [oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.IsHomogeneous.coe_pieceEquiv_apply]

/-- The inverse piece comparison is the restriction of the inverse total comparison. -/
@[simp↓]
theorem coe_oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv_symm_apply (g : ℤ × ℤ)
    (y : G.bigradedHatHomologyPiece R i g) :
    ((G.oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv s i R g).symm y :
        (BaseS).obj (((G.stabilizeXSucc s).1.simplyBlockedComplex R j).homology ())) =
      (G.1.oneVariableSpecializationStabilizeXSuccHomologyEquiv s i R).symm y := by
  simp only [oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    LinearMap.IsHomogeneous.coe_pieceEquiv_symm_apply]

/-- North-east `X`-stabilization preserves the coefficient-ring rank in every bidegree. -/
theorem finrank_bigradedHatHomologyPiece_stabilizeXSucc (g : ℤ × ℤ) :
    Module.finrank R ((G.stabilizeXSucc s).bigradedHatHomologyPiece R j g) =
      Module.finrank R (G.bigradedHatHomologyPiece R i g) :=
  (G.oneVariableSpecializationStabilizeXSuccHomologyPieceEquiv s i R g).finrank_eq

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s i : Fin n)
  (K : Type*) [Field K] [CharP K 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "hG'" => Iff.mpr
  (GridDiagram.isKnot_stabilizeX G (Fin.succ s) (Fin.succ (GridDiagram.X G s)) s) hG

/-- North-east corner `X`-stabilization preserves the bigraded Poincaré series of simply
blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX_succ :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries K j =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  have hstab : (hG').toOddComponentGridDiagram = hG.toOddComponentGridDiagram.stabilizeXSucc s :=
    Subtype.ext rfl
  ext g
  rw [coeff_bigradedSimplyBlockedHomologyPoincareSeries,
    coeff_bigradedSimplyBlockedHomologyPoincareSeries, hstab]
  exact hG.toOddComponentGridDiagram.finrank_bigradedHatHomologyPiece_stabilizeXSucc s i K g

/-- North-east corner `X`-stabilization preserves the Alexander-graded Euler characteristic of
simply blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem gradedSimplyBlockedHomologyEulerChar_stabilizeX_succ :
    (hG').gradedSimplyBlockedHomologyEulerChar K j =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeX_succ s i K]

end TauCeti.GridDiagram.IsKnot
