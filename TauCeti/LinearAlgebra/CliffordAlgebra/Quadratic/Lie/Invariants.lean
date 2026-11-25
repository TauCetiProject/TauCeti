/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.EnvelopingImage
public import TauCeti.LinearAlgebra.ExteriorAlgebra.LieInvariants
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.LinearAlgebra.ExteriorAlgebra.AlgebraMapInv
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The invariant exterior algebra of a Lie algebra with nondegenerate Killing form

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form `κ`, acting on its
exterior algebra `⋀ L` by the derivations extending the adjoint representation. Kostant's
decomposition of the Clifford algebra `Cl(L, κ)` starts from the subalgebra of invariants
`E = (⋀ L)^L` (`TauCeti.ExteriorAlgebra.lieInvariants`), its positive-degree augmentation ideal `I`
(`TauCeti.ExteriorAlgebra.lieInvariantsAugmentation`), and the square `I * I`: the primitive
invariants form a complement of `I * I` in `I`.

This file relates `E` to the Clifford algebra and computes it in dimension three.

* The quantization map `σ = (CliffordAlgebra.equivExterior κ).symm : ⋀ L ≃ Cl(L, κ)` carries `E`
  onto the commutant of the image `A` of the enveloping algebra
  (`CliffordAlgebra.adjointEnvelopingImage`). This is the equivariance of `σ` for the commutator
  action `⁅x, c⁆ = ⁅q x, c⁆` of the quadratic lift `q`, whose invariants are that commutant.
* A Lie algebra with nondegenerate Killing form is perfect, so it acts on itself with trace zero
  and its top exterior power is invariant.
* In dimension three, for instance for `𝔰𝔩₂`, `E` is spanned by `1` and the top exterior power
  `⋀³ L`. So `I = ⋀³ L` and `I * I = 0`, and the primitive invariants are the line `⋀³ L`, of
  dimension one, the rank of `L`. The upper bound on `E` comes from the decomposition
  `1 ⊕ L ⊕ L ⊕ 1` of the commutator module
  (`CliffordAlgebra.exists_lieModuleEquiv_commutator_of_finrank_eq_three`): its invariants are the
  two trivial lines, since `L` has trivial centre.

## Main results

* `CliffordAlgebra.equivExterior_mem_lieInvariants_iff` and
  `CliffordAlgebra.map_equivExterior_symm_lieInvariants`: the quantization map identifies
  `(⋀ L)^L` with the commutant of the image of the enveloping algebra.
* `CliffordAlgebra.toSubmodule_lieInvariants_of_finrank_eq_three`: in dimension three,
  `(⋀ L)^L = K ⊕ ⋀³ L`; `CliffordAlgebra.finrank_lieInvariants_of_finrank_eq_three` and
  `CliffordAlgebra.finrank_lieInvariants_sl_fin_two`: it has dimension two.
* `CliffordAlgebra.lieInvariantsAugmentation_of_finrank_eq_three` and
  `CliffordAlgebra.lieInvariantsAugmentation_mul_self_eq_bot_of_finrank_eq_three`: in dimension
  three, `I = ⋀³ L` and `I * I = 0`.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem, the ρ-decomposition
  `C(𝔤) = End V_ρ ⊗ C(P)`, and the `𝔤`-module structure of `⋀𝔤`*, Adv. Math. 125 (1997), 275--350.
* Y. Bazlov, *The Harish-Chandra isomorphism for Clifford algebras*, arXiv:0812.2059, §§3.2--3.5.
-/

public section

universe u v

open TauCeti TauCeti.LieAlgebra LieModule Module
open TauCeti.ExteriorAlgebra (lieInvariants lieInvariantsAugmentation mem_lieInvariants
  mem_lieInvariantsAugmentation)

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {L : Type v} [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L]

section Commutant

open scoped CliffordAlgebra.Commutator

/-- **The invariants of `⋀ L` correspond to the commutant of the image of the enveloping
algebra**: a Clifford element `c` commutes with the image of `U(L)` exactly when
`CliffordAlgebra.equivExterior c` is invariant under the derivations extending the adjoint
action. -/
theorem equivExterior_mem_lieInvariants_iff {c : CliffordAlgebra (killingQuadraticForm K L)} :
    equivExterior (killingQuadraticForm K L) c ∈ lieInvariants K L L ↔
      c ∈ Subalgebra.centralizer K
        (adjointEnvelopingImage K L : Set (CliffordAlgebra (killingQuadraticForm K L))) := by
  rw [mem_centralizer_adjointEnvelopingImage_iff_mem_maxTrivSubmodule, mem_maxTrivSubmodule,
    mem_lieInvariants]
  refine forall_congr' fun x ↦ ?_
  have hx : toEnd K L L x = _root_.LieAlgebra.ad K L x :=
    LinearMap.ext fun y ↦ by rw [toEnd_apply_apply, _root_.LieAlgebra.ad_apply]
  rw [hx, ← equivExterior_commutator_lie, LinearEquiv.map_eq_zero_iff]

/-- **The quantization map carries the invariants of `⋀ L` onto the commutant of the image of
the enveloping algebra.** -/
theorem map_equivExterior_symm_lieInvariants :
    (Subalgebra.toSubmodule (lieInvariants K L L)).map
        (equivExterior (killingQuadraticForm K L)).symm.toLinearMap =
      Subalgebra.toSubmodule (Subalgebra.centralizer K
        (adjointEnvelopingImage K L : Set (CliffordAlgebra (killingQuadraticForm K L)))) := by
  ext c
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_toSubmodule, equivExterior_mem_lieInvariants_iff]

end Commutant

section Dimension

/-- In dimension three, the commutant of the image of the enveloping algebra has dimension at most
two. Its elements are the invariants of the commutator module, and these lie in the span of `1` and
of the odd central element `ω` of
`CliffordAlgebra.exists_lieModuleEquiv_commutator_of_finrank_eq_three`: the adjoint summands
contribute nothing, because the centre of `L` is trivial. -/
private theorem finrank_centralizer_adjointEnvelopingImage_le_of_finrank_eq_three
    (h : finrank K L = 3) :
    finrank K (Subalgebra.toSubmodule (Subalgebra.centralizer K
      (adjointEnvelopingImage K L : Set (CliffordAlgebra (killingQuadraticForm K L))))) ≤ 2 := by
  open scoped CliffordAlgebra.Commutator in
  obtain ⟨ω, -, -, e, he⟩ := exists_lieModuleEquiv_commutator_of_finrank_eq_three h
  have hle : Subalgebra.toSubmodule (Subalgebra.centralizer K
      (adjointEnvelopingImage K L : Set (CliffordAlgebra (killingQuadraticForm K L)))) ≤
      Submodule.span K (Set.range ![1, ω]) := by
    intro c hc
    rw [Subalgebra.mem_toSubmodule, mem_centralizer_adjointEnvelopingImage_iff_mem_maxTrivSubmodule,
      mem_maxTrivSubmodule] at hc
    -- The preimage `p` of `c` is invariant, so its two adjoint components are central.
    set p := e.symm c with hp
    have hinv (x : L) : ⁅x, p⁆ = 0 := by
      have hmap : e.symm ⁅x, c⁆ = ⁅x, e.symm c⁆ := e.symm.map_lie'
      rw [hp, ← hmap, hc x, map_zero]
    have hcen (y : L) (hy : ∀ x : L, ⁅x, y⁆ = 0) : y = 0 := by
      have hy' : y ∈ _root_.LieAlgebra.center K L := by
        rw [_root_.LieAlgebra.center, mem_maxTrivSubmodule]
        exact hy
      rwa [_root_.LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at hy'
    have h₁ : p.2.1 = 0 := hcen _ fun x ↦ congrArg (·.2.1) (hinv x)
    have h₂ : p.2.2.1 = 0 := hcen _ fun x ↦ congrArg (·.2.2.1) (hinv x)
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![TrivialLieModule.equiv K L K p.1, TrivialLieModule.equiv K L K p.2.2.2], ?_⟩
    rw [← e.apply_symm_apply c, ← hp, he, h₁, h₂]
    simp [Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]
  exact (Submodule.finrank_mono hle).trans ((finrank_range_le_card _).trans (by simp))

omit [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L] in
/-- In dimension three, the scalars and `⋀³ L` are lines in different exterior degrees, so their
sum is a plane. -/
private theorem finrank_one_sup_exteriorPower_three (h : finrank K L = 3) :
    finrank K ↥(1 ⊔ ⋀[K]^3 L) = 2 := by
  have hdisj : Disjoint (⋀[K]^0 L) (⋀[K]^3 L) :=
    (DirectSum.Decomposition.isInternal (fun i : ℕ ↦ ⋀[K]^i L)).submodule_iSupIndep.pairwiseDisjoint
      (show (0 : ℕ) ≠ 3 by decide)
  have := Submodule.finrank_sup_add_finrank_inf_eq (⋀[K]^0 L) (⋀[K]^3 L)
  rw [hdisj.eq_bot, finrank_bot, add_zero, exteriorPower.finrank_eq, exteriorPower.finrank_eq,
    h] at this
  have hone : (1 : Submodule K (ExteriorAlgebra K L)) = ⋀[K]^0 L := (pow_zero _).symm
  rw [hone, this, Nat.choose_zero_right, Nat.choose_self]

variable (K L) in
/-- **The invariants of `⋀ L` in dimension three**: for a three-dimensional Lie algebra with
nondegenerate Killing form, such as `𝔰𝔩₂`, they are the scalars and the top exterior power. -/
theorem toSubmodule_lieInvariants_of_finrank_eq_three (h : finrank K L = 3) :
    Subalgebra.toSubmodule (lieInvariants K L L) = 1 ⊔ ⋀[K]^3 L := by
  have hle : 1 ⊔ ⋀[K]^3 L ≤ Subalgebra.toSubmodule (lieInvariants K L L) :=
    sup_le (Submodule.one_le.mpr (lieInvariants K L L).one_mem) <| h ▸
      TauCeti.ExteriorAlgebra.exteriorPower_finrank_le_lieInvariants_of_derivedSeries_eq_top
        (derivedSeries_one_eq_top_of_isKilling K L)
  -- The invariants have dimension at most two, as the commutant does.
  have hE : finrank K (Subalgebra.toSubmodule (lieInvariants K L L)) ≤ 2 := by
    rw [← (equivExterior (killingQuadraticForm K L)).symm.finrank_map_eq,
      map_equivExterior_symm_lieInvariants]
    exact finrank_centralizer_adjointEnvelopingImage_le_of_finrank_eq_three h
  exact (Submodule.eq_of_le_of_finrank_le hle
    (hE.trans (finrank_one_sup_exteriorPower_three h).ge)).symm

variable (K L) in
/-- **In dimension three the invariants of `⋀ L` form a plane.** -/
theorem finrank_lieInvariants_of_finrank_eq_three (h : finrank K L = 3) :
    finrank K (lieInvariants K L L) = 2 := by
  rw [← Subalgebra.finrank_toSubmodule, toSubmodule_lieInvariants_of_finrank_eq_three K L h,
    finrank_one_sup_exteriorPower_three h]

variable (K L) in
/-- **In dimension three the augmentation ideal of `(⋀ L)^L` is the top exterior power**
`⋀³ L`. -/
theorem lieInvariantsAugmentation_of_finrank_eq_three (h : finrank K L = 3) :
    lieInvariantsAugmentation K L L = ⋀[K]^3 L := by
  have hE := toSubmodule_lieInvariants_of_finrank_eq_three K L h
  refine le_antisymm (fun y hy ↦ ?_) fun y hy ↦ ?_
  · obtain ⟨hyE, hy0⟩ := mem_lieInvariantsAugmentation.mp hy
    rw [← Subalgebra.mem_toSubmodule, hE] at hyE
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hyE
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hu
    rw [map_add, ExteriorAlgebra.algebraMap_leftInverse L r,
      ExteriorAlgebra.algebraMapInv_eq_zero_of_mem_exteriorPower (by decide) hz, add_zero] at hy0
    rwa [hy0, map_zero, zero_add]
  · refine TauCeti.ExteriorAlgebra.toSubmodule_lieInvariants_inf_exteriorPower_le (by decide)
      ⟨?_, hy⟩
    rw [hE]
    exact Submodule.mem_sup_right hy

variable (K L) in
/-- **In dimension three the square of the augmentation ideal vanishes**: `I * I` lies in
`⋀⁶ L = 0`. So the primitive invariants, a complement of `I * I` in `I`, are the line `⋀³ L`. -/
theorem lieInvariantsAugmentation_mul_self_eq_bot_of_finrank_eq_three (h : finrank K L = 3) :
    lieInvariantsAugmentation K L L * lieInvariantsAugmentation K L L = ⊥ := by
  rw [lieInvariantsAugmentation_of_finrank_eq_three K L h, ExteriorAlgebra.exteriorPower, ← pow_add,
    Submodule.eq_bot_iff]
  intro y hy
  exact congrArg Subtype.val (exteriorPower.eq_zero_of_finrank_lt (3 + 3) (by omega) ⟨y, hy⟩)

open _root_.LieAlgebra.SpecialLinear in
/-- **The invariants of `⋀ 𝔰𝔩₂` form a plane**, spanned by `1` and the top exterior power
(`CliffordAlgebra.toSubmodule_lieInvariants_of_finrank_eq_three`). -/
theorem finrank_lieInvariants_sl_fin_two [CharZero K] :
    finrank K (lieInvariants K (sl (Fin 2) K) (sl (Fin 2) K)) = 2 :=
  finrank_lieInvariants_of_finrank_eq_three K _ (by simp [finrank_sl])

end Dimension

end CliffordAlgebra
