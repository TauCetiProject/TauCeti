/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.EnvelopingImage
public import TauCeti.LinearAlgebra.ExteriorAlgebra.LieInvariants
import TauCeti.Algebra.Lie.Killing.Perfect
import TauCeti.LinearAlgebra.ExteriorAlgebra.AlgebraMapInv
import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The invariant exterior algebra of a Lie algebra with nondegenerate Killing form

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form `κ`, acting on its
exterior algebra `⋀ L` by the derivations extending the adjoint representation. Kostant's
decomposition of the Clifford algebra `Cl(L, κ)` starts from the subalgebra of invariants
`E = (⋀ L)^L` (`TauCeti.ExteriorAlgebra.lieInvariants`), its positive-degree augmentation ideal `I`
(`TauCeti.ExteriorAlgebra.lieInvariantsAugmentation`), and the square `I * I`: the space `P` of
primitive invariants is the orthogonal complement of `I * I` in `I` for the form on `⋀ L` induced by
the Killing form.

This file relates `E` to the Clifford algebra and computes it in dimension three.

* The quantization map `σ = (CliffordAlgebra.equivExterior κ).symm : ⋀ L ≃ Cl(L, κ)` carries `E`
  onto the commutant of the image `A` of the enveloping algebra
  (`CliffordAlgebra.adjointEnvelopingImage`). This is the equivariance of `σ` for the commutator
  action `⁅x, c⁆ = ⁅q x, c⁆` of the quadratic lift `q`, whose invariants are that commutant.
* A Lie algebra with nondegenerate Killing form is perfect, so it acts on itself with trace zero
  and its top exterior power is invariant.
* In dimension three, for instance for `𝔰𝔩₂`, `E` is spanned by `1` and the top exterior power
  `⋀³ L`. So `I = ⋀³ L` and `I * I = 0`; hence `P = I` is the line `⋀³ L`, of dimension one, the
  rank of `L`. The upper bound on `E` is the bound on the commutant of `A`
  (`CliffordAlgebra.finrank_centralizer_adjointEnvelopingImage_le_of_finrank_eq_three`).

## Main results

* `CliffordAlgebra.equivExterior_mem_lieInvariants_iff` and
  `CliffordAlgebra.map_equivExterior_symm_lieInvariants`: the quantization map identifies
  `(⋀ L)^L` with the commutant of the image of the enveloping algebra.
* `TauCeti.ExteriorAlgebra.toSubmodule_lieInvariants_of_finrank_eq_three`: in dimension three,
  `(⋀ L)^L = K ⊕ ⋀³ L`; `TauCeti.ExteriorAlgebra.finrank_lieInvariants_of_finrank_eq_three` and
  `TauCeti.ExteriorAlgebra.finrank_lieInvariants_sl_fin_two`: it has dimension two, and so has the
  commutant of the image of the enveloping algebra
  (`CliffordAlgebra.finrank_centralizer_adjointEnvelopingImage_of_finrank_eq_three`).
* `TauCeti.ExteriorAlgebra.lieInvariantsAugmentation_of_finrank_eq_three` and
  `TauCeti.ExteriorAlgebra.lieInvariantsAugmentation_mul_self_eq_bot_of_finrank_eq_three`: in
  dimension three, `I = ⋀³ L` and `I * I = 0`.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem, the ρ-decomposition
  `C(𝔤) = End V_ρ ⊗ C(P)`, and the `𝔤`-module structure of `⋀𝔤`*, Adv. Math. 125 (1997), 275--350.
* Y. Bazlov, *The Harish-Chandra isomorphism for Clifford algebras*, arXiv:0812.2059, §§3.2--3.5.
-/

public section

universe u v

open TauCeti TauCeti.LieAlgebra LieModule Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace CliffordAlgebra

open TauCeti.ExteriorAlgebra (lieInvariants mem_lieInvariants)

variable {K : Type u} [Field K] {L : Type v} [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L]

/-- **The invariants of `⋀ L` correspond to the commutant of the image of the enveloping
algebra**: a Clifford element `c` commutes with the image of `U(L)` exactly when
`CliffordAlgebra.equivExterior c` is invariant under the derivations extending the adjoint
action. -/
theorem equivExterior_mem_lieInvariants_iff {c : CliffordAlgebra (killingQuadraticForm K L)} :
    equivExterior (killingQuadraticForm K L) c ∈ lieInvariants K L L ↔
      c ∈ Subalgebra.centralizer K
        (adjointEnvelopingImage K L : Set (CliffordAlgebra (killingQuadraticForm K L))) := by
  open scoped CliffordAlgebra.Commutator in
  rw [mem_centralizer_adjointEnvelopingImage_iff_mem_maxTrivSubmodule, mem_maxTrivSubmodule,
    mem_lieInvariants]
  refine forall_congr' fun x ↦ ?_
  -- `LieAlgebra.ad K L` is by definition `LieModule.toEnd K L L`.
  have hx : toEnd K L L x = _root_.LieAlgebra.ad K L x := rfl
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

end CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

open CliffordAlgebra

variable (K : Type u) [Field K] (L : Type v) [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L]

/-- **The invariants of `⋀ L` in dimension three**: for a three-dimensional Lie algebra with
nondegenerate Killing form, such as `𝔰𝔩₂`, they are the scalars and the top exterior power. -/
theorem toSubmodule_lieInvariants_of_finrank_eq_three (h : finrank K L = 3) :
    Subalgebra.toSubmodule (lieInvariants K L L) = 1 ⊔ ⋀[K]^3 L := by
  have hle : 1 ⊔ ⋀[K]^3 L ≤ Subalgebra.toSubmodule (lieInvariants K L L) :=
    sup_le (Submodule.one_le.mpr (lieInvariants K L L).one_mem) <| h ▸
      exteriorPower_finrank_le_lieInvariants_of_derivedSeries_eq_top
        (derivedSeries_one_eq_top_of_isKilling K L)
  -- The invariants have dimension at most two, as the commutant does.
  have hE : finrank K (Subalgebra.toSubmodule (lieInvariants K L L)) ≤ 2 := by
    rw [← (equivExterior (killingQuadraticForm K L)).symm.finrank_map_eq,
      map_equivExterior_symm_lieInvariants]
    exact finrank_centralizer_adjointEnvelopingImage_le_of_finrank_eq_three h
  have h2 : finrank K ↥(1 ⊔ ⋀[K]^3 L) = 2 := h ▸ finrank_one_sup_exteriorPower_finrank (by omega)
  exact (Submodule.eq_of_le_of_finrank_le hle (hE.trans h2.ge)).symm

/-- **In dimension three the invariants of `⋀ L` form a plane.** -/
theorem finrank_lieInvariants_of_finrank_eq_three (h : finrank K L = 3) :
    finrank K (lieInvariants K L L) = 2 := by
  rw [← Subalgebra.finrank_toSubmodule, toSubmodule_lieInvariants_of_finrank_eq_three K L h, ← h,
    finrank_one_sup_exteriorPower_finrank (by omega)]

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
    rw [map_add, _root_.ExteriorAlgebra.algebraMap_leftInverse L r,
      _root_.ExteriorAlgebra.algebraMapInv_eq_zero_of_mem_exteriorPower three_ne_zero hz,
      add_zero] at hy0
    rwa [hy0, map_zero, zero_add]
  · refine toSubmodule_lieInvariants_inf_exteriorPower_le three_ne_zero ⟨?_, hy⟩
    rw [hE]
    exact Submodule.mem_sup_right hy

/-- **In dimension three the square of the augmentation ideal vanishes**: `I * I` lies in
`⋀⁶ L = 0`. So the space of primitive invariants, the orthogonal complement of `I * I` in `I`, is
all of `I`, the line `⋀³ L`. -/
theorem lieInvariantsAugmentation_mul_self_eq_bot_of_finrank_eq_three (h : finrank K L = 3) :
    lieInvariantsAugmentation K L L * lieInvariantsAugmentation K L L = ⊥ := by
  rw [lieInvariantsAugmentation_of_finrank_eq_three K L h, _root_.ExteriorAlgebra.exteriorPower,
    ← pow_add, Submodule.eq_bot_iff]
  intro y hy
  exact congrArg Subtype.val (exteriorPower.eq_zero_of_finrank_lt (3 + 3) (by omega) ⟨y, hy⟩)

omit [Invertible (2 : K)] in
open _root_.LieAlgebra.SpecialLinear in
/-- **The invariants of `⋀ 𝔰𝔩₂` form a plane**, spanned by `1` and the top exterior power
(`TauCeti.ExteriorAlgebra.toSubmodule_lieInvariants_of_finrank_eq_three`). -/
theorem finrank_lieInvariants_sl_fin_two [CharZero K] :
    finrank K (lieInvariants K (sl (Fin 2) K) (sl (Fin 2) K)) = 2 :=
  finrank_lieInvariants_of_finrank_eq_three K _ (by simp [finrank_sl])

end TauCeti.ExteriorAlgebra

namespace CliffordAlgebra

variable {K : Type u} [Field K] {L : Type v} [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [_root_.LieAlgebra.IsKilling K L]

/-- **In dimension three the commutant of the image of the enveloping algebra is a plane**: it is
the image of the invariants of `⋀ L` under the quantization map. -/
theorem finrank_centralizer_adjointEnvelopingImage_of_finrank_eq_three (h : finrank K L = 3) :
    finrank K (Subalgebra.toSubmodule (Subalgebra.centralizer K
      (adjointEnvelopingImage K L : Set (CliffordAlgebra (killingQuadraticForm K L))))) = 2 := by
  rw [← map_equivExterior_symm_lieInvariants, LinearEquiv.finrank_map_eq,
    Subalgebra.finrank_toSubmodule,
    TauCeti.ExteriorAlgebra.finrank_lieInvariants_of_finrank_eq_three K L h]

end CliffordAlgebra
