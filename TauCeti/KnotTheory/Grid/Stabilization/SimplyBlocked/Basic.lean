/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Homology
public import TauCeti.KnotTheory.Grid.SimplyBlocked.Basic
import TauCeti.Algebra.Homology.SquareZero.ShortExact

/-!
# The simply blocked stabilization chain map

An `X`-stabilization inserts a new `O`-marking and carries each old `O`-marking to its
inserted column. Blocking one of those old markings specializes the unblocked stabilization
map to a semilinear chain map. Its scalar homomorphism first merges the two stabilization
variables and then kills the chosen old variable; it need not be a renaming of variables.

The specialization identity characterizes the map on all chains and proves that it commutes
with the differentials. These constructions apply to arbitrary grid diagrams. For knots,
blocking one `O`-marking gives the simply blocked theory.

The specialized map is again a quasi-isomorphism. Specialization at a variable `V` is the
quotient of `GC⁻` by multiplication by `V`, which is injective, and the unblocked stabilization
map carries the variable of the transported marking to that of the original marking. So the
unblocked and specialized maps form a morphism of short exact sequences of complexes, and the
five lemma for their long exact homology sequences
(`AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact` and
`AddMonoidHom.mem_range_of_map_mem_range_of_exact`) transfers stabilization invariance of `GH⁻`
to the specialized complexes.

## Main results

* `TauCeti.GridDiagram.simplyBlockedStabilizeXMap_simplyBlockedSpecialization`: the specialized
  map is the descent of the unblocked stabilization map through specialization.
* `TauCeti.GridDiagram.simplyBlockedStabilizeXMap_simplyBlockedDifferential`: it is a chain map.
* `TauCeti.GridDiagram.exists_sub_simplyBlockedStabilizeXMap_mem_range` and
  `TauCeti.GridDiagram.mem_range_of_simplyBlockedStabilizeXMap_mem_range`: it induces a bijection
  on homology, in elementwise form.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2;
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.2 (arXiv:math/0610559).
-/

public section

open MvPolynomial

namespace TauCeti.GridDiagram

variable {n : ℕ} (s i : Fin n) (R : Type*)

section Semiring

variable [CommSemiring R]

local notation "j" => s.castSucc.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The coefficient homomorphism of stabilization after blocking the transported old marking.
Merge the stabilization columns using `s.predAbove`, then kill the variable of column `i`. -/
noncomputable def simplyBlockedStabilizeXRingHom : S →+* A :=
  (simplyBlockedRingHom R i).comp
    ((rename (R := R) s.predAbove).toRingHom.comp (rename Subtype.val).toRingHom)

/-- A surviving source variable is merged and then specialized in the old grid. In particular,
when `i = s`, the other variable of the stabilization block also maps to zero. -/
@[simp]
theorem simplyBlockedStabilizeXRingHom_X (c : {c : Fin (n + 1) // c ≠ j}) :
    simplyBlockedStabilizeXRingHom s i R (MvPolynomial.X c) =
      simplyBlockedRingHom R i (MvPolynomial.X (s.predAbove c)) := by
  simp [simplyBlockedStabilizeXRingHom]

/-- Stabilization leaves ground-ring coefficients unchanged after blocking. -/
@[simp]
theorem simplyBlockedStabilizeXRingHom_C (r : R) :
    simplyBlockedStabilizeXRingHom s i R (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [simplyBlockedStabilizeXRingHom]

/-- Merging columns commutes with blocking the transported old marking. -/
theorem simplyBlockedStabilizeXRingHom_specialization (p : MvPolynomial (Fin (n + 1)) R) :
    simplyBlockedStabilizeXRingHom s i R (simplyBlockedRingHom R j p) =
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
      simp [Fin.predAbove_succAbove]
    · have hX : MvPolynomial.X c = rename Subtype.val
          (MvPolynomial.X (R := R) (⟨c, hc⟩ : {c : Fin (n + 1) // c ≠ j})) := by simp
      simp only [AlgHom.comp_apply]
      rw [hX, killCompl_rename_app]
  exact DFunLike.congr_fun h p

end Semiring

variable (G : GridDiagram n) [CommRing R]

local notation "j" => s.castSucc.succAbove i
local notation "A" => MvPolynomial {c : Fin n // c ≠ i} R
local notation "S" => MvPolynomial {c : Fin (n + 1) // c ≠ j} R

/-- The stabilization comparison with the transported old `O`-marking blocked. Its image on a
generator is the specialization of the unblocked stabilization comparison. -/
noncomputable def simplyBlockedStabilizeXMap :
    GridChainHat R (n + 1) j →ₛₗ[simplyBlockedStabilizeXRingHom s i R] GridChainHat R n i :=
  (Finsupp.linearCombination A fun x : GridState (n + 1) =>
    simplyBlockedSpecialization R i (G.stabilizeXChainMap s R (Finsupp.single x 1))).comp
      (Finsupp.mapRange.linearMap (simplyBlockedStabilizeXRingHom s i R).toSemilinearMap)

/-- The specialized stabilization map on a single supported coefficient. -/
theorem simplyBlockedStabilizeXMap_single (x : GridState (n + 1)) (p : S) :
    G.simplyBlockedStabilizeXMap s i R (Finsupp.single x p) =
      simplyBlockedStabilizeXRingHom s i R p •
        simplyBlockedSpecialization R i (G.stabilizeXChainMap s R (Finsupp.single x 1)) := by
  simp [simplyBlockedStabilizeXMap]

/-- The matrix formula for the specialized stabilization comparison. -/
@[simp]
theorem simplyBlockedStabilizeXMap_apply_apply (c : GridChainHat R (n + 1) j)
    (y : GridState n) :
    G.simplyBlockedStabilizeXMap s i R c y = c.sum fun x p =>
      simplyBlockedStabilizeXRingHom s i R p *
        simplyBlockedRingHom R i (G.stabilizeXChainMap s R (Finsupp.single x 1) y) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.zero_apply, Finsupp.sum_zero_index]
  | add c d hc hd =>
    rw [map_add, Finsupp.add_apply, hc, hd, Finsupp.sum_add_index'] <;> simp [add_mul]
  | single x p =>
    rw [simplyBlockedStabilizeXMap_single, Finsupp.smul_apply, smul_eq_mul,
      simplyBlockedSpecialization_apply, ← simplyBlockedRingHom_apply,
      Finsupp.sum_single_index (by simp)]

/-- The simply blocked comparison is the descent of the unblocked stabilization map through
coefficient specialization. -/
@[simp]
theorem simplyBlockedStabilizeXMap_simplyBlockedSpecialization (c : GridChainMinus R (n + 1)) :
    G.simplyBlockedStabilizeXMap s i R (simplyBlockedSpecialization R j c) =
      simplyBlockedSpecialization R i (G.stabilizeXChainMap s R c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x p =>
    rw [simplyBlockedSpecialization_single, simplyBlockedStabilizeXMap_single,
      ← simplyBlockedRingHom_apply, simplyBlockedStabilizeXRingHom_specialization,
      ← Finsupp.smul_single_one x p, map_smulₛₗ, map_smulₛₗ]
    rfl

variable [CharP R 2]

/-- Stabilization commutes with the simply blocked differentials. -/
theorem simplyBlockedStabilizeXMap_simplyBlockedDifferential (c : GridChainHat R (n + 1) j) :
    G.simplyBlockedStabilizeXMap s i R
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).simplyBlockedDifferential R j c) =
      G.simplyBlockedDifferential R i (G.simplyBlockedStabilizeXMap s i R c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R j c
  rw [← simplyBlockedSpecialization_unblockedDifferential,
    simplyBlockedStabilizeXMap_simplyBlockedSpecialization,
    simplyBlockedStabilizeXMap_simplyBlockedSpecialization,
    ← simplyBlockedSpecialization_unblockedDifferential,
    stabilizeXChainMap_unblockedDifferential]

/-! ### Quasi-isomorphism after blocking -/

local notation "G'" => GridDiagram.stabilizeX G (Fin.castSucc s)
  (Fin.castSucc (GridDiagram.X G s)) s

omit [CharP R 2] in
/-- Stabilization carries multiplication by the variable of the transported marking to
multiplication by `V_i`. -/
private theorem stabilizeXChainMap_X_smul (c : GridChainMinus R (n + 1)) :
    G.stabilizeXChainMap s R ((MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) • c) =
      (MvPolynomial.X i : MvPolynomial (Fin n) R) • G.stabilizeXChainMap s R c := by
  rw [map_smulₛₗ]
  simp [Fin.predAbove_succAbove]

/-- `exists_sub_stabilizeXChainMap_mem_range` for the underlying additive maps. -/
private theorem exists_sub_stabilizeXChainMap_mem_addRange (c : GridChainMinus R n)
    (hc : c ∈ (G.unblockedDifferential R).toAddMonoidHom.ker) :
    ∃ m ∈ ((G').unblockedDifferential R).toAddMonoidHom.ker,
      c - (G.stabilizeXChainMap s R).toAddMonoidHom m ∈
        (G.unblockedDifferential R).toAddMonoidHom.range := by
  simpa using G.exists_sub_stabilizeXChainMap_mem_range s R (by simpa using hc)

/-- `mem_range_of_stabilizeXChainMap_mem_range` for the underlying additive maps. -/
private theorem mem_addRange_of_stabilizeXChainMap_mem_addRange (m : GridChainMinus R (n + 1))
    (hm : m ∈ ((G').unblockedDifferential R).toAddMonoidHom.ker)
    (h : (G.stabilizeXChainMap s R).toAddMonoidHom m ∈
      (G.unblockedDifferential R).toAddMonoidHom.range) :
    m ∈ ((G').unblockedDifferential R).toAddMonoidHom.range := by
  simpa using G.mem_range_of_stabilizeXChainMap_mem_range s R (by simpa using hm)
    (by simpa using h)

/-- Every simply blocked cycle of `G` differs from the image of a simply blocked cycle of the
stabilized diagram by a boundary. -/
theorem exists_sub_simplyBlockedStabilizeXMap_mem_range {y : GridChainHat R n i}
    (hy : y ∈ LinearMap.ker (G.simplyBlockedDifferential R i)) :
    ∃ x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j),
      y - G.simplyBlockedStabilizeXMap s i R x ∈
        LinearMap.range (G.simplyBlockedDifferential R i) := by
  -- Specialization at the blocked variable is a morphism from the short exact sequence
  -- `0 → GC⁻ --V_j--> GC⁻ → GC^ → 0` of the stabilized diagram to that of `G`, and the unblocked
  -- stabilization map is a quasi-isomorphism.
  simpa using AddMonoidHom.exists_mem_ker_sub_mem_range_of_exact
    (G.simplyBlockedStabilizeXMap s i R).toAddMonoidHom
    (d := ((G').unblockedDifferential R).toAddMonoidHom)
    (e := (G.unblockedDifferential R).toAddMonoidHom)
    (f := (G.stabilizeXChainMap s R).toAddMonoidHom)
    (u := DistribSMul.toAddMonoidHom _ (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))
    (v := DistribSMul.toAddMonoidHom _ (MvPolynomial.X i : MvPolynomial (Fin n) R))
    (dP := ((G').simplyBlockedDifferential R j).toAddMonoidHom)
    (eQ := (G.simplyBlockedDifferential R i).toAddMonoidHom)
    (p := (simplyBlockedSpecialization R j).toAddMonoidHom)
    (q := (simplyBlockedSpecialization R i).toAddMonoidHom)
    (fun c => LinearMap.congr_fun (G.unblockedDifferential_comp_self_eq_zero R) c)
    (fun c => map_smul ((G').unblockedDifferential R) _ c)
    (fun c => map_smul (G.unblockedDifferential R) _ c) (X_smul_gridChainMinus_injective R i)
    (exact_X_smul_simplyBlockedSpecialization R j) (exact_X_smul_simplyBlockedSpecialization R i)
    (simplyBlockedSpecialization_surjective R i)
    (fun c => simplyBlockedSpecialization_unblockedDifferential _ R j c)
    (fun c => simplyBlockedSpecialization_unblockedDifferential _ R i c)
    (fun c => G.stabilizeXChainMap_unblockedDifferential s R c)
    (fun c => G.stabilizeXChainMap_X_smul s i R c)
    (fun c => G.simplyBlockedStabilizeXMap_simplyBlockedSpecialization s i R c)
    (G.exists_sub_stabilizeXChainMap_mem_addRange s R)
    (G.mem_addRange_of_stabilizeXChainMap_mem_addRange s R) (y := y) (by simpa using hy)

/-- A simply blocked cycle of the stabilized diagram whose image in `G` is a boundary is itself a
boundary. -/
theorem mem_range_of_simplyBlockedStabilizeXMap_mem_range {x : GridChainHat R (n + 1) j}
    (hx : x ∈ LinearMap.ker ((G').simplyBlockedDifferential R j))
    (h : G.simplyBlockedStabilizeXMap s i R x ∈
      LinearMap.range (G.simplyBlockedDifferential R i)) :
    x ∈ LinearMap.range ((G').simplyBlockedDifferential R j) := by
  -- The same morphism of short exact sequences as in
  -- `exists_sub_simplyBlockedStabilizeXMap_mem_range`.
  simpa using AddMonoidHom.mem_range_of_map_mem_range_of_exact
    (G.simplyBlockedStabilizeXMap s i R).toAddMonoidHom
    (d := ((G').unblockedDifferential R).toAddMonoidHom)
    (e := (G.unblockedDifferential R).toAddMonoidHom)
    (f := (G.stabilizeXChainMap s R).toAddMonoidHom)
    (u := DistribSMul.toAddMonoidHom _ (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))
    (v := DistribSMul.toAddMonoidHom _ (MvPolynomial.X i : MvPolynomial (Fin n) R))
    (dP := ((G').simplyBlockedDifferential R j).toAddMonoidHom)
    (eQ := (G.simplyBlockedDifferential R i).toAddMonoidHom)
    (p := (simplyBlockedSpecialization R j).toAddMonoidHom)
    (q := (simplyBlockedSpecialization R i).toAddMonoidHom)
    (fun c => LinearMap.congr_fun (unblockedDifferential_comp_self_eq_zero (G') R) c)
    (fun c => LinearMap.congr_fun (G.unblockedDifferential_comp_self_eq_zero R) c)
    (fun c => map_smul ((G').unblockedDifferential R) _ c)
    (fun c => map_smul (G.unblockedDifferential R) _ c)
    (X_smul_gridChainMinus_injective R j) (X_smul_gridChainMinus_injective R i)
    (exact_X_smul_simplyBlockedSpecialization R j) (simplyBlockedSpecialization_surjective R j)
    (exact_X_smul_simplyBlockedSpecialization R i) (simplyBlockedSpecialization_surjective R i)
    (fun c => simplyBlockedSpecialization_unblockedDifferential _ R j c)
    (fun c => simplyBlockedSpecialization_unblockedDifferential _ R i c)
    (fun c => G.stabilizeXChainMap_unblockedDifferential s R c)
    (fun c => G.stabilizeXChainMap_X_smul s i R c)
    (fun c => G.simplyBlockedStabilizeXMap_simplyBlockedSpecialization s i R c)
    (G.exists_sub_stabilizeXChainMap_mem_addRange s R)
    (G.mem_addRange_of_stabilizeXChainMap_mem_addRange s R) (x := x) (by simpa using hx)
    (by simpa using h)

end TauCeti.GridDiagram
