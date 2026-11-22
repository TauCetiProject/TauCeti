/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.Algebra.MonoidAlgebra.SubgroupCharSum
import Mathlib.RingTheory.IntegralDomain
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Evaluation of a group ring at characters

Let `O` be a commutative semiring (or commutative ring) and `G` a commutative group. A *character*
of `G` is a group homomorphism `ψ : G →* Oˣ`, and evaluation at `ψ` is the `O`-algebra
homomorphism `ψ : O[G] → O`, `∑ a_g g ↦ ∑ a_g ψ(g)` (`MonoidHom.charEval`).

This file provides the lightweight character-evaluation API for ordinary group rings `O[G]`:
its functoriality under `MonoidAlgebra.mapDomain`, its agreement with `MonoidAlgebra.augmentation`
at the trivial character, and row orthogonality on character sums `TauCeti.subgroupCharSum`.

## Main definitions

* `MonoidHom.charEval`: evaluation `O[G] →ₐ[O] O` at a character, the `O[G]`-point
  `TauCeti.DiagonalizableGroup.point` of the diagonalizable group with values in `O`.

## Main results

* `MonoidAlgebra.charEval_one_apply` and `MonoidHom.charEval_one`: the trivial character
  evaluates by the augmentation.
* `MonoidHom.charEval_mapDomain`: functoriality of character evaluation under
  `MonoidAlgebra.mapDomain`.
* `MonoidHom.charEval_subgroupCharSum_of_le_ker` and
  `MonoidHom.charEval_subgroupCharSum_eq_zero`: the evaluation of a character sum over a finite
  subgroup `H`, which is `#H` or `0` (row orthogonality); the norm element `∑_{h ∈ H} h` is the
  case of the trivial character.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023), §2.2.
-/

public section

section CommSemiring

variable {O G : Type*} [CommSemiring O] [CommGroup G]

/-- Evaluation of the group ring `O[G]` at a character `ψ : G →* Oˣ`: the `O`-algebra
homomorphism `∑ a_g g ↦ ∑ a_g ψ(g)`. It is the `O[G]`-point of the diagonalizable group
`D(G)` with values in `O` attached to `ψ`, and following Dasgupta–Kakde it is written `ψ(x)`
for `x ∈ O[G]`. Being reducible, it inherits the value lemmas of
`TauCeti.DiagonalizableGroup.point`: `TauCeti.DiagonalizableGroup.point_single` sends
`single g a` to `a • ψ g`, and `TauCeti.DiagonalizableGroup.point_single_one` sends `single g 1`
to `ψ g`. -/
noncomputable abbrev MonoidHom.charEval (ψ : G →* Oˣ) : MonoidAlgebra O G →ₐ[O] O :=
  TauCeti.DiagonalizableGroup.point ψ

/-- The trivial character evaluates by the coefficient-sum augmentation. -/
@[simp]
theorem MonoidAlgebra.charEval_one_apply (x : MonoidAlgebra O G) :
    (1 : G →* Oˣ).charEval x = MonoidAlgebra.augmentation O G x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single g a => simp

namespace MonoidHom

/-- As a ring homomorphism, evaluation at the trivial character is the coefficient-sum
augmentation. -/
theorem charEval_one :
    ((1 : G →* Oˣ).charEval : MonoidAlgebra O G →+* O) =
      MonoidAlgebra.augmentation O G :=
  RingHom.ext MonoidAlgebra.charEval_one_apply

/-- Evaluating at `ψ : G →* Oˣ` after mapping the group along `f : H →* G` agrees with evaluating
at the restricted character `ψ.comp f`. -/
@[simp]
theorem charEval_mapDomain {H : Type*} [CommGroup H] (ψ : G →* Oˣ) (f : H →* G)
    (y : MonoidAlgebra O H) :
    ψ.charEval (MonoidAlgebra.mapDomain f y) = (ψ.comp f).charEval y := by
  simpa only [MonoidHom.charEval, TauCeti.DiagonalizableGroup.point, MonoidHom.comp_assoc] using
    MonoidAlgebra.lift_mapDomain ((Units.coeHom O).comp ψ) f y

/-- The value of a character `ψ` on the character sum `∑_{h ∈ H} χ(h) h` over a finite subgroup
`H` is `#H` when `χ ψ` is trivial on `H`. -/
theorem charEval_subgroupCharSum_of_le_ker (χ ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : H ≤ (χ * ψ).ker) :
    ψ.charEval (TauCeti.subgroupCharSum ((Units.coeHom O).comp χ) H) = Nat.card H := by
  have h (h : H) : ((χ h : Oˣ) : O) * ψ h = 1 := by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, hH h.property, Units.val_one]
  simp [TauCeti.subgroupCharSum_def, map_sum, h, Nat.card_eq_fintype_card]

/-- The norm element `∑_{h ∈ H} h` of a finite subgroup `H` on which `ψ` is trivial evaluates
to `#H` at `ψ`. -/
theorem charEval_subgroupCharSum_one_of_le_ker (ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : H ≤ ψ.ker) :
    ψ.charEval (TauCeti.subgroupCharSum (1 : G →* O) H) = Nat.card H := by
  simpa using charEval_subgroupCharSum_of_le_ker 1 ψ H
    fun g hg ↦ by simpa [MonoidHom.mem_ker] using hH hg

end MonoidHom

end CommSemiring

section Domain

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G]

namespace MonoidHom

/-- Row orthogonality: the value of a character `ψ` on the character sum `∑_{h ∈ H} χ(h) h` over
a finite subgroup `H` vanishes when `χ ψ` is nontrivial on `H` and `O` is a domain. -/
theorem charEval_subgroupCharSum_eq_zero (χ ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : ¬ H ≤ (χ * ψ).ker) :
    ψ.charEval (TauCeti.subgroupCharSum ((Units.coeHom O).comp χ) H) = 0 := by
  have hne : (Units.coeHom O).comp ((χ * ψ).comp H.subtype) ≠ 1 := by
    intro h
    refine hH fun g hg ↦ Units.val_eq_one.mp ?_
    simpa using DFunLike.congr_fun h ⟨g, hg⟩
  simpa [TauCeti.subgroupCharSum_def, map_sum] using sum_hom_units_eq_zero _ hne

variable [Fintype (⊤ : Subgroup G)] in
/-- The integral character sum associated to `χ` evaluates to the group order at `χ` and to
zero at each other character. It is the scaled character idempotent, with no division in `O`. -/
@[simp]
theorem charEval_subgroupCharSum_inv_top [DecidableEq (G →* Oˣ)] (χ ψ : G →* Oˣ) :
    ψ.charEval (TauCeti.subgroupCharSum ((Units.coeHom O).comp χ⁻¹) ⊤) =
      if χ = ψ then (Nat.card G : O) else 0 := by
  have hker : ⊤ ≤ (χ⁻¹ * ψ).ker ↔ χ = ψ := by
    rw [top_le_iff, MonoidHom.ker_eq_top_iff]
    exact inv_mul_eq_one (a := χ) (b := ψ)
  by_cases h : χ = ψ
  · rw [ite_eq_left h]
    simpa using charEval_subgroupCharSum_of_le_ker χ⁻¹ ψ ⊤ (hker.mpr h)
  · rw [ite_eq_right h]
    exact charEval_subgroupCharSum_eq_zero χ⁻¹ ψ ⊤ fun hle ↦ h (hker.mp hle)

/-- The norm element `∑_{h ∈ H} h` of a finite subgroup `H` on which `ψ` is nontrivial evaluates
to `0` at `ψ` when `O` is a domain. For `H = G` this is the vanishing of a nontrivial character
on the group sum. -/
theorem charEval_subgroupCharSum_one_eq_zero (ψ : G →* Oˣ) (H : Subgroup G) [Fintype H]
    (hH : ¬ H ≤ ψ.ker) :
    ψ.charEval (TauCeti.subgroupCharSum (1 : G →* O) H) = 0 := by
  simpa using charEval_subgroupCharSum_eq_zero 1 ψ H
    fun h ↦ hH fun g hg ↦ by simpa [MonoidHom.mem_ker] using h hg

end MonoidHom

end Domain
