/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Root.CorootSpan
public import TauCeti.Algebra.Lie.Weights.Root.KostantStability
public import TauCeti.LinearAlgebra.RootSystem.EquivInvariance
public import TauCeti.RingTheory.DividedPowers.Associative
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.RootString
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.RootSystem

/-!
# Exact low-degree Chevalley action in type F₄

This file transports the pinned forty-eight-root indexing to the rational Killing root system and
records the exact degree-one and degree-two adjoint actions needed for the characteristic-two
short-root submodule.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.

-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule

noncomputable section

/-- Identify the fixed forty-eight F₄ root labels with the root index of `DynkinType.F4`. -/
abbrev f4RootIndex (i : Fin 48) : Fin F4.numRoots :=
  Fin.cast numRoots_F4.symm i

/-- The Killing-root label belonging to a pinned integral root index. -/
abbrev f4KillingRootLabel (i : Fin 48) :
    (F4.cartanSubalgebra valid_F4).root :=
  (F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex i)

/-- The Killing weight indexed by the corresponding root of the pinned F₄ root datum. -/
abbrev f4KillingRoot (i : Fin 48) :
    Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4) :=
  (f4KillingRootLabel i : (F4.cartanSubalgebra valid_F4).root)

/-- A chosen F₄ root-vector system compatible with the pinned Chevalley involution. -/
noncomputable def f4ChevalleyRootVector :
    Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4) →
      F4.lieAlgebra valid_F4 :=
  Classical.choose (F4.exists_isChevalleySystem valid_F4)

/-- The chosen F₄ root vectors form a Chevalley system for the pinned involution. -/
theorem f4ChevalleyRootVector_isChevalleySystem :
    IsChevalleySystem (F4.chevalleyInvolution valid_F4) f4ChevalleyRootVector :=
  Classical.choose_spec (F4.exists_isChevalleySystem valid_F4)

/-- The rational root-system equivalence carries a pinned root to its Killing root. -/
theorem f4KillingRoot_weightEquiv (i : Fin 48) :
    (F4.rationalRootSystemEquiv valid_F4).weightEquiv
        ((F4.rationalRootSystem valid_F4).root (f4RootIndex i)) =
      (rootSystem (F4.cartanSubalgebra valid_F4)).root (f4KillingRootLabel i) :=
  RootPairing.Hom.root_weightMap_apply _ _ (f4RootIndex i)
    (F4.rationalRootSystemEquiv valid_F4).toHom

/-- Integral root relations are equivalent to the corresponding relations among Killing weights. -/
theorem f4KillingRoot_eq_add_zsmul_iff (α β γ : Fin 48) (n : ℤ) :
    (f4KillingRoot γ : (F4.cartanSubalgebra valid_F4) → ℚ) =
        (f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ) +
          (n : ℚ) • (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ) ↔
      f4SimplyConnectedRootDatum.root γ =
        f4SimplyConnectedRootDatum.root β + n • f4SimplyConnectedRootDatum.root α := by
  let E := F4.rationalRootSystemEquiv valid_F4
  have hmap (i : Fin 48) :
      E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex i)) =
        (rootSystem (F4.cartanSubalgebra valid_F4)).root
          (E.indexEquiv (f4RootIndex i)) := f4KillingRoot_weightEquiv i
  -- First transport through the linear equivalence, then forget that Killing roots are
  -- linear forms. Injectivity of each map reflects as well as preserves the relation.
  have hrat : (F4.rationalRootSystem valid_F4).root (f4RootIndex γ) =
        (F4.rationalRootSystem valid_F4).root (f4RootIndex β) +
          (n : ℚ) • (F4.rationalRootSystem valid_F4).root (f4RootIndex α) ↔
      (f4KillingRoot γ : (F4.cartanSubalgebra valid_F4) → ℚ) =
        (f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ) +
          (n : ℚ) • (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ) := by
    calc
      _ ↔ E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex γ)) =
          E.weightEquiv ((F4.rationalRootSystem valid_F4).root (f4RootIndex β) +
            (n : ℚ) • (F4.rationalRootSystem valid_F4).root (f4RootIndex α)) :=
        E.weightEquiv.injective.eq_iff.symm
      _ ↔ _ := by
        simp only [map_add, map_smul, hmap]
        exact DFunLike.coe_injective.eq_iff.symm
  -- The assembled F4 datum uses the same root table, with only rank/index casts.
  have hint : (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex γ) =
        (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex β) +
          n • (F4.simplyConnectedRootDatum valid_F4).root (f4RootIndex α) ↔
      f4SimplyConnectedRootDatum.root γ =
        f4SimplyConnectedRootDatum.root β + n • f4SimplyConnectedRootDatum.root α := by
    rw [simplyConnectedRootDatum_F4]
    simp only [rank_F4]
    constructor <;> intro h <;> convert h using 1 <;> congr
  -- Finally descend the rational relation using the general base-change theorem.
  rw [← hrat, ← hint]
  exact root_rationalRootSystem_eq_add_zsmul_iff F4 valid_F4 _ _ _ n

/-- The rational Killing-root identification preserves the root-string coefficient inherited from
the integral pinned F₄ datum. -/
theorem f4KillingRootSystem_chainBotCoeff (α β : Fin 48) :
    (rootSystem (F4.cartanSubalgebra valid_F4)).chainBotCoeff
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex α))
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex β)) =
      f4SimplyConnectedRootDatum.chainBotCoeff α β := by
  calc
    _ = (F4.rationalRootSystem valid_F4).chainBotCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      chainBotCoeff_indexEquiv (F4.rationalRootSystemEquiv valid_F4)
        (f4RootIndex α) (f4RootIndex β)
    _ = (F4.simplyConnectedRootDatum valid_F4).chainBotCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      chainBotCoeff_rationalRootSystem F4 valid_F4 _ _
    _ = _ := by
      rw [simplyConnectedRootDatum_F4]
      congr

/-- The rational Killing-root identification preserves the ascending root-string coefficient
inherited from the integral pinned F₄ datum. -/
theorem f4KillingRootSystem_chainTopCoeff (α β : Fin 48) :
    (rootSystem (F4.cartanSubalgebra valid_F4)).chainTopCoeff
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex α))
        ((F4.rationalRootSystemEquiv valid_F4).indexEquiv (f4RootIndex β)) =
      f4SimplyConnectedRootDatum.chainTopCoeff α β := by
  calc
    _ = (F4.rationalRootSystem valid_F4).chainTopCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      chainTopCoeff_indexEquiv (F4.rationalRootSystemEquiv valid_F4)
        (f4RootIndex α) (f4RootIndex β)
    _ = (F4.simplyConnectedRootDatum valid_F4).chainTopCoeff
        (f4RootIndex α) (f4RootIndex β) :=
      chainTopCoeff_rationalRootSystem F4 valid_F4 _ _
    _ = _ := by
      rw [simplyConnectedRootDatum_F4]
      congr

/-- The two root-string lengths agree for the Killing weights and the pinned integral roots. -/
theorem f4_chainCoeffs_eq (α β : Fin 48)
    (hlin : LinearIndependent ℚ
      ![(f4KillingRoot α : Module.Dual ℚ (F4.cartanSubalgebra valid_F4)),
        (f4KillingRoot β : Module.Dual ℚ (F4.cartanSubalgebra valid_F4))]) :
    chainTopCoeff (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ)
        (f4KillingRoot β) = f4SimplyConnectedRootDatum.chainTopCoeff α β ∧
      chainBotCoeff (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ)
        (f4KillingRoot β) = f4SimplyConnectedRootDatum.chainBotCoeff α β := by
  have h := rootSystem_chainCoeffs_eq hlin
  exact ⟨h.1.symm.trans (f4KillingRootSystem_chainTopCoeff α β),
    h.2.symm.trans (f4KillingRootSystem_chainBotCoeff α β)⟩

/-- Every Killing coroot expands in the simple Killing coroots with the coordinates of the
corresponding pinned integral F₄ coroot. -/
theorem f4KillingCoroot_eq_sum_simple (β : Fin 48) :
    (rootSystem (F4.cartanSubalgebra valid_F4)).coroot (f4KillingRootLabel β) =
      ∑ i : Fin F4.rank,
        ((F4.rationalRootSystem valid_F4).coroot (f4RootIndex β) i) •
          (rootSystem (F4.cartanSubalgebra valid_F4)).coroot
            ((F4.lieBasis valid_F4).baseSupportEquiv i) := by
  -- Expand in the rational simple-coroot basis, then transport through the coweight equivalence.
  let E := F4.rationalRootSystemEquiv valid_F4
  let k := f4RootIndex β
  have hsimple (i : Fin F4.rank) :
      (F4.rationalRootSystem valid_F4).coroot (F4.simpleSupportEquiv valid_F4 i) =
        Pi.single i 1 := by
    ext j
    simp only [coroot_rationalRootSystem, coe_simpleSupportEquiv, coroot_simpleIndex]
    by_cases hij : i = j
    · subst j
      rw [Pi.single_eq_same, Pi.single_eq_same]
      norm_num
    · rw [Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne (Ne.symm hij)]
      norm_num
  have hsource : (F4.rationalRootSystem valid_F4).coroot k =
      ∑ i : Fin F4.rank, ((F4.rationalRootSystem valid_F4).coroot k i) •
        (F4.rationalRootSystem valid_F4).coroot
          (F4.simpleSupportEquiv valid_F4 i) := by
    calc
      _ = ∑ i, ((F4.rationalRootSystem valid_F4).coroot k i) • Pi.single i 1 :=
        pi_eq_sum_univ' ((F4.rationalRootSystem valid_F4).coroot k)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (((F4.rationalRootSystem valid_F4).coroot k i) • ·)
          (hsimple i).symm
  calc
    _ = E.coweightEquiv.symm ((F4.rationalRootSystem valid_F4).coroot k) :=
      by
      apply E.coweightEquiv.injective
      rw [LinearEquiv.apply_symm_apply, RootPairing.Equiv.coweightEquiv_apply]
      simpa only [f4KillingRootLabel, E, k, Equiv.symm_apply_apply] using
        RootPairing.Hom.coroot_coweightMap_apply _ _ (E.indexEquiv k) E.toHom
    _ = E.coweightEquiv.symm (∑ i : Fin F4.rank,
        ((F4.rationalRootSystem valid_F4).coroot k i) •
          (F4.rationalRootSystem valid_F4).coroot
            (F4.simpleSupportEquiv valid_F4 i)) := congrArg E.coweightEquiv.symm hsource
    _ = ∑ i : Fin F4.rank, ((F4.rationalRootSystem valid_F4).coroot k i) •
        E.coweightEquiv.symm ((F4.rationalRootSystem valid_F4).coroot
          (F4.simpleSupportEquiv valid_F4 i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (((F4.rationalRootSystem valid_F4).coroot k i) • ·)
      simpa only [coe_simpleSupportEquiv] using
        F4.rationalRootSystemEquiv_coweightEquiv_symm_coroot_simpleIndex valid_F4 i

/-- The Cartan integer of a pinned Killing root against a simple Killing coroot is the
corresponding integral pairing in the pinned F₄ datum. -/
theorem f4RootCartanWeight_simple (α : Fin 48) (i : Fin F4.rank) :
    rootCartanWeight (f4KillingRoot α)
        (((F4.lieBasis valid_F4).baseSupportEquiv i :
          (F4.cartanSubalgebra valid_F4).root) :
            Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4)) =
      f4SimplyConnectedRootDatum.pairing α
        (Fin.castAdd 44 (Fin.cast rank_F4 i)) := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
  rw [intCast_rootCartanWeight_apply]
  rw [← rootSystem_pairing_apply (F4.cartanSubalgebra valid_F4)
    ((F4.lieBasis valid_F4).baseSupportEquiv i) (f4KillingRootLabel α)]
  rw [← F4.rationalRootSystemEquiv_indexEquiv_simpleIndex valid_F4 i,
    (F4.rationalRootSystemEquiv valid_F4).toHom.pairing,
    F4.pairing_rationalRootSystem, simplyConnectedRootDatum_F4]
  norm_cast
  have hs : F4.simpleIndex valid_F4 i =
      Fin.castAdd 44 (Fin.cast rank_F4 i) := by
    -- These casts identify the rank-four node type without changing its underlying numeral.
    have hi : i = Fin.cast rank_F4 i := by
      apply Fin.ext
      rfl
    rw [hi]
    exact simpleIndex_F4 valid_F4 (Fin.cast rank_F4 i)
  rw [hs]
  congr 1

/-- The bracket along any nondegenerate F₄ root edge has the integral Chevalley coefficient
prescribed by the descending root string. -/
theorem exists_f4_lie_rootVector_eq_smul_of_add (α β γ : Fin 48)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    ∃ z : ℤ, z.natAbs = f4SimplyConnectedRootDatum.chainBotCoeff α β + 1 ∧
      ⁅f4ChevalleyRootVector (f4KillingRoot α),
          f4ChevalleyRootVector (f4KillingRoot β)⁆ =
        (z : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  let H := F4.cartanSubalgebra valid_F4
  let L := F4.lieAlgebra valid_F4
  let E := F4.rationalRootSystemEquiv valid_F4
  let P := rootSystem H
  let a : Weight ℚ H L := f4KillingRoot α
  let b : Weight ℚ H L := f4KillingRoot β
  let g : Weight ℚ H L := f4KillingRoot γ
  let x := f4ChevalleyRootVector
  have hx : IsChevalleySystem (F4.chevalleyInvolution valid_F4) x :=
    f4ChevalleyRootVector_isChevalleySystem
  have ha : a.IsNonZero := by
    simpa only [a, f4KillingRoot] using
      LieSubalgebra.isNonZero_coe_root (E.indexEquiv (f4RootIndex α))
  have hb : b.IsNonZero := by
    simpa only [b, f4KillingRoot] using
      LieSubalgebra.isNonZero_coe_root (E.indexEquiv (f4RootIndex β))
  have hg : g.IsNonZero := by
    simpa only [g, f4KillingRoot] using
      LieSubalgebra.isNonZero_coe_root (E.indexEquiv (f4RootIndex γ))
  have hgab : (g : H → ℚ) = (a : H → ℚ) + b := by
    have hmap := (f4KillingRoot_eq_add_zsmul_iff α β γ 1).mpr (by
      simpa only [one_zsmul] using h)
    have hmap' : (g : H → ℚ) = (b : H → ℚ) + a := by
      simpa only [H, a, b, g, Int.cast_one, one_smul] using hmap
    exact hmap'.trans (add_comm _ _)
  let ia := E.indexEquiv (f4RootIndex α)
  let ib := E.indexEquiv (f4RootIndex β)
  let ig := E.indexEquiv (f4RootIndex γ)
  have hroot : P.root ig = P.root ia + P.root ib := by
    ext y
    simpa only [P, ia, ib, ig, a, b, g, rootSystem_root_apply,
      Weight.toLinear_apply, LinearMap.add_apply, Pi.add_apply] using congrFun hgab y
  have hlin := P.linearIndependent_of_add_mem_range_root' ⟨ig, hroot⟩
  have hLieBot := (f4_chainCoeffs_eq α β (by
    simpa only [P, ia, ib, a, b, rootSystem_root_apply, Weight.toLinear_apply] using hlin)).2
  let N := hx.intStructureConstant a b g hg hgab
  have hN := hx.intStructureConstant_eq_natCast_or_eq_neg_natCast a b g ha hb hg hgab
  have hlie := hx.lie_eq_intStructureConstant_zsmul a b g hg hgab
  refine ⟨N, ?_, ?_⟩
  · rcases hN with hN | hN
    · dsimp only [N]
      rw [hN, Int.natAbs_natCast, hLieBot]
    · dsimp only [N]
      rw [hN, Int.natAbs_neg, Int.natAbs_natCast, hLieBot]
  · simpa only [N, Int.cast_smul_eq_zsmul] using hlie

/-- A root edge whose descending string has length zero carries a unit Chevalley coefficient. -/
theorem exists_f4_lie_rootVector_eq_smul_of_add_of_chainBotCoeff_eq_zero (α β γ : Fin 48)
    (hbot : f4SimplyConnectedRootDatum.chainBotCoeff α β = 0)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    ∃ ε : ℤ, ε.natAbs = 1 ∧
      ⁅f4ChevalleyRootVector (f4KillingRoot α),
          f4ChevalleyRootVector (f4KillingRoot β)⁆ =
        (ε : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  obtain ⟨ε, hε, hlie⟩ := exists_f4_lie_rootVector_eq_smul_of_add α β γ h
  refine ⟨ε, ?_, hlie⟩
  simpa only [hbot, zero_add] using hε

/-- Along a two-step F₄ string from a long root in a short-root direction, the square of the
adjoint root-vector action has coefficient of absolute value two. Dividing by `2!` therefore has
unit coefficient, which becomes exactly one after reduction modulo two. -/
theorem exists_f4_ad_sq_rootVector_eq_smul_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    ∃ z : ℤ, z.natAbs = 2 ∧
      ((ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) ^ 2)
          (f4ChevalleyRootVector (f4KillingRoot β)) =
        (z : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  let L := F4.lieAlgebra valid_F4
  let a := f4KillingRoot α
  let b := f4KillingRoot β
  let g := f4KillingRoot γ
  let x := f4ChevalleyRootVector
  obtain ⟨δ, hδ, -, hbotab, -, hbotad, -⟩ :=
    exists_f4_short_midpoint_of_long_add_two_short α β γ hα hβ h
  have hγδ : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root δ + f4SimplyConnectedRootDatum.root α := by
    rw [h, hδ]
    module
  obtain ⟨N₁, hN₁, hlie₁⟩ := exists_f4_lie_rootVector_eq_smul_of_add α β δ hδ
  obtain ⟨N₂, hN₂, hlie₂⟩ := exists_f4_lie_rootVector_eq_smul_of_add α δ γ hγδ
  have hN₁' : N₁.natAbs = 1 := by simpa only [hbotab, zero_add] using hN₁
  have hN₂' : N₂.natAbs = 2 := by simpa only [hbotad, one_add_one_eq_two] using hN₂
  refine ⟨N₁ * N₂, ?_, ?_⟩
  · rw [Int.natAbs_mul, hN₁', hN₂']
  · -- Fold the local names for the Lie algebra, root vectors and weights.
    change ((ad ℚ L (x a)) ^ 2) (x b) = ((N₁ * N₂ : ℤ) : ℚ) • x g
    rw [pow_two, Module.End.mul_apply, ad_apply, ad_apply, hlie₁, lie_smul, hlie₂,
      smul_smul, Int.cast_mul]

/-- The second divided adjoint power along a long--short--long F₄ string has unit coefficient.
It sends the initial root vector to plus or minus the final root vector and therefore preserves
the integral lattice on this root string. -/
theorem exists_f4_dividedAd_sq_rootVector_eq_smul_of_long_add_two_short (α β γ : Fin 48)
    (hα : f4Length α = 1) (hβ : f4Length β = 2)
    (h : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    ∃ ε : ℤ, ε.natAbs = 1 ∧
      ((Nat.factorial 2 : ℚ)⁻¹ •
          ((ad ℚ (F4.lieAlgebra valid_F4)
            (f4ChevalleyRootVector (f4KillingRoot α))) ^ 2)
            (f4ChevalleyRootVector (f4KillingRoot β))) =
        (ε : ℚ) • f4ChevalleyRootVector (f4KillingRoot γ) := by
  obtain ⟨z, hzabs, hz⟩ := exists_f4_ad_sq_rootVector_eq_smul_of_long_add_two_short α β γ hα hβ h
  have hzsign : z = 2 ∨ z = -2 := by omega
  rcases hzsign with rfl | rfl
  · refine ⟨1, by norm_num, ?_⟩
    rw [hz]
    rw [smul_smul]
    norm_num
  · refine ⟨-1, by norm_num, ?_⟩
    rw [hz]
    rw [smul_smul]
    norm_num

/-- The pinned opposite-root index has the negative rational Killing-root label. -/
theorem f4KillingRootLabel_f4OppositeRootIndex (α : Fin 48) :
    f4KillingRootLabel (f4OppositeRootIndex α) = -f4KillingRootLabel α := by
  have hsource : (F4.rationalRootSystem valid_F4).reflectionPerm
      (f4RootIndex α) (f4RootIndex α) = f4RootIndex (f4OppositeRootIndex α) := by
    rw [reflectionPerm_rationalRootSystem, simplyConnectedRootDatum_F4,
      f4OppositeRootIndex_eq_reflectionPerm]; rfl
  calc
    _ = (F4.rationalRootSystemEquiv valid_F4).indexEquiv
        ((F4.rationalRootSystem valid_F4).reflectionPerm (f4RootIndex α) (f4RootIndex α)) :=
      congrArg (F4.rationalRootSystemEquiv valid_F4).indexEquiv hsource.symm
    _ = (rootSystem (F4.cartanSubalgebra valid_F4)).reflectionPerm
        (f4KillingRootLabel α) (f4KillingRootLabel α) :=
      indexEquiv_reflectionPerm (F4.rationalRootSystemEquiv valid_F4).toHom _ _
    _ = _ := rootSystem_reflectionPerm_self_eq_neg _

/-- Distinct pinned indices define distinct rational Killing roots. -/
theorem f4KillingRoot_injective : Function.Injective f4KillingRoot := by
  intro α β h
  have hlabel : f4KillingRootLabel α = f4KillingRootLabel β := by
    apply Subtype.ext
    exact h
  have hi := (F4.rationalRootSystemEquiv valid_F4).indexEquiv.injective hlabel
  apply Fin.ext
  exact congrArg Fin.val hi

/-- The Killing root at the opposite pinned index is the negative root. -/
@[simp] theorem f4KillingRoot_f4OppositeRootIndex (α : Fin 48) :
    f4KillingRoot (f4OppositeRootIndex α) = -f4KillingRoot α := by
  exact congrArg
    (fun r : (F4.cartanSubalgebra valid_F4).root =>
      (r : Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4)))
    (f4KillingRootLabel_f4OppositeRootIndex α)

/-- Two indexed rational Killing roots do not sum to zero unless their pinned labels are
opposite. -/
theorem f4KillingRoot_add_ne_zero_of_ne_opposite (α β : Fin 48)
    (hopp : α ≠ f4OppositeRootIndex β) :
    (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ) + f4KillingRoot β ≠ 0 := by
  intro hz
  apply hopp
  apply f4KillingRoot_injective
  rw [f4KillingRoot_f4OppositeRootIndex]
  apply Weight.ext
  intro x
  have hx := congrFun hz x
  simp only [Pi.add_apply, Pi.zero_apply] at hx ⊢
  exact eq_neg_of_add_eq_zero_left hx

/-- Every rational Killing root label is one of the pinned forty-eight indices. -/
theorem f4KillingRootLabel_surjective : Function.Surjective f4KillingRootLabel := by
  intro γ
  refine ⟨Fin.cast numRoots_F4
    ((F4.rationalRootSystemEquiv valid_F4).indexEquiv.symm γ), ?_⟩
  simp only [f4KillingRootLabel, f4RootIndex, Fin.cast_cast, Fin.cast_eq_self]
  exact Equiv.apply_symm_apply (F4.rationalRootSystemEquiv valid_F4).indexEquiv γ

/-- A nonzero weight whose root space is present has a pinned index, including when it is
presented as an endpoint of a root string. -/
theorem exists_f4Root_eq_add_zsmul_of_rootSpace_ne_bot
    (α β : Fin 48) (n : ℕ)
    (hsum : (f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ) +
      n • f4KillingRoot α ≠ 0)
    (hbot : rootSpace (F4.cartanSubalgebra valid_F4)
      ((f4KillingRoot β : (F4.cartanSubalgebra valid_F4) → ℚ) +
        n • f4KillingRoot α) ≠ ⊥) :
    ∃ γ : Fin 48, f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α := by
  let H := F4.cartanSubalgebra valid_F4
  let γweight : Weight ℚ H (F4.lieAlgebra valid_F4) :=
    ⟨(f4KillingRoot β : H → ℚ) + n • f4KillingRoot α, hbot⟩
  have hγnz : γweight.IsNonZero := by
    rw [Weight.IsNonZero, Weight.IsZero]
    exact hsum
  let γroot : H.root := ⟨γweight, by simpa only [LieSubalgebra.root,
    Finset.mem_filter, Finset.mem_univ, true_and] using hγnz⟩
  obtain ⟨γ, hγlabel⟩ := f4KillingRootLabel_surjective γroot
  refine ⟨γ, ?_⟩
  apply (f4KillingRoot_eq_add_zsmul_iff α β γ n).mp
  have hγweight : f4KillingRoot γ = γweight := congrArg Subtype.val hγlabel
  rw [hγweight]
  rfl

/-- A missing endpoint in the pinned root string forces the corresponding adjoint power to
vanish. The only excluded case is the string through the opposite root. -/
theorem f4_ad_pow_rootVector_eq_zero_of_no_endpoint (α β : Fin 48) (n : ℕ)
    (hopp : β ≠ f4OppositeRootIndex α)
    (hno : ∀ δ : Fin 48, f4SimplyConnectedRootDatum.root δ ≠
      f4SimplyConnectedRootDatum.root β +
        (n : ℤ) • f4SimplyConnectedRootDatum.root α) :
    ((ad ℚ (F4.lieAlgebra valid_F4)
      (f4ChevalleyRootVector (f4KillingRoot α))) ^ n)
        (f4ChevalleyRootVector (f4KillingRoot β)) = 0 := by
  let H := F4.cartanSubalgebra valid_F4
  have hαnz : (f4KillingRoot α).IsNonZero := H.isNonZero_coe_root (f4KillingRootLabel α)
  have hβnz : (f4KillingRoot β).IsNonZero := H.isNonZero_coe_root (f4KillingRootLabel β)
  have hopp' : α ≠ f4OppositeRootIndex β :=
    (ne_f4OppositeRootIndex_comm α β).mp hopp
  have hsum := f4KillingRoot_add_ne_zero_of_ne_opposite α β hopp'
  rcases f4ChevalleyRootVector_isChevalleySystem.ad_pow_rootVector_eq_zero_or_exists
      hαnz hβnz hsum n with hzero | hnonzero
  · exact hzero
  · obtain ⟨γ, hγcoe, -, -⟩ := hnonzero
    have hweight : (f4KillingRoot β : H → ℚ) + n • f4KillingRoot α ≠ 0 :=
      coe_add_natCast_smul_ne_zero hαnz hβnz hsum n
    have hspace : rootSpace H
        ((f4KillingRoot β : H → ℚ) + n • f4KillingRoot α) ≠ ⊥ := by
      have hspace' : rootSpace H
          ((f4KillingRoot β : H → ℚ) + (n : ℚ) • f4KillingRoot α) ≠ ⊥ := by
        rw [← hγcoe]
        exact γ.genWeightSpace_ne_bot'
      simpa only [Nat.cast_smul_eq_nsmul] using hspace'
    obtain ⟨δ, hδ⟩ :=
      exists_f4Root_eq_add_zsmul_of_rootSpace_ne_bot α β n hweight hspace
    exact (hno δ hδ).elim

/-- In characteristic zero, the second divided adjoint power vanishes exactly when the
ordinary second adjoint power does. -/
theorem f4_dividedPower_two_ad_smul_eq_zero_iff (α : Fin 48)
    (y : F4.lieAlgebra valid_F4) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) • y = 0 ↔
      ((ad ℚ (F4.lieAlgebra valid_F4)
        (f4ChevalleyRootVector (f4KillingRoot α))) ^ 2) y = 0 := by
  rw [Associative.dividedPower_def, Module.End.smul_def, LinearMap.smul_apply]
  constructor
  · intro h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    rw [h, smul_zero]

/-- A missing second root-string endpoint makes the second adjoint divided power vanish. -/
theorem f4_dividedPower_two_ad_rootVector_eq_zero_of_no_endpoint
    (α β : Fin 48) (hopp : β ≠ f4OppositeRootIndex α)
    (hno : ∀ γ : Fin 48, f4SimplyConnectedRootDatum.root γ ≠
      f4SimplyConnectedRootDatum.root β +
        (2 : ℤ) • f4SimplyConnectedRootDatum.root α) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) •
        f4ChevalleyRootVector (f4KillingRoot β) = 0 := by
  exact (f4_dividedPower_two_ad_smul_eq_zero_iff α _).2
    (f4_ad_pow_rootVector_eq_zero_of_no_endpoint α β 2 hopp hno)

/-- The second divided adjoint power sends the opposite root vector to the negative root vector. -/
theorem f4_dividedPower_two_ad_rootVector_opposite (α : Fin 48) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) •
        f4ChevalleyRootVector (f4KillingRoot (f4OppositeRootIndex α)) =
      -f4ChevalleyRootVector (f4KillingRoot α) := by
  let a := f4KillingRoot α
  let x := f4ChevalleyRootVector
  have ha : a.IsNonZero :=
    (F4.cartanSubalgebra valid_F4).isNonZero_coe_root (f4KillingRootLabel α)
  have hop : f4KillingRoot (f4OppositeRootIndex α) = -a := by
    simpa only [a] using f4KillingRoot_f4OppositeRootIndex α
  have h1 : (ad ℚ (F4.lieAlgebra valid_F4) (x a)) (x (-a)) =
      ((coroot a : F4.cartanSubalgebra valid_F4) : F4.lieAlgebra valid_F4) :=
    f4ChevalleyRootVector_isChevalleySystem.toIsSl2System.lie_neg a ha
  have h2 : (ad ℚ (F4.lieAlgebra valid_F4) (x a))
      ((coroot a : F4.cartanSubalgebra valid_F4) : F4.lieAlgebra valid_F4) =
        (-2 : ℚ) • x a := by
    rw [ad_apply, ← lie_skew,
      f4ChevalleyRootVector_isChevalleySystem.toIsSl2System.lie_coroot a a,
      root_apply_coroot ha]
    module
  rw [hop, Associative.dividedPower_def, Module.End.smul_def, LinearMap.smul_apply, pow_two,
    Module.End.mul_apply, h1, h2, smul_smul]
  norm_num
  rfl

/-- Away from the opposite-root string, the second divided adjoint power annihilates every
short-root vector. -/
theorem f4_dividedPower_two_ad_rootVector_eq_zero_of_short (α β : Fin 48)
    (hβ : f4Length β = 1) (hopp : β ≠ f4OppositeRootIndex α) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) •
        f4ChevalleyRootVector (f4KillingRoot β) = 0 := by
  apply f4_dividedPower_two_ad_rootVector_eq_zero_of_no_endpoint α β hopp
  intro δ hpinned
  rcases f4Length_eq_one_or_eq_two α with hα | hα
  · have hneg : f4SimplyConnectedRootDatum.root β ≠
        -f4SimplyConnectedRootDatum.root α := by
      intro h
      apply hopp
      simpa only [f4OppositeRootIndex_eq_reflectionPerm] using
        (f4SimplyConnectedRootDatum.root_eq_neg_iff.mp h)
    exact (f4_not_root_eq_short_add_nsmul_short_of_two_le α β δ 2 hα hβ hneg
      (by omega) hpinned).elim
  · have hn :=
      f4_n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
        α β δ 2 hα hβ (by omega) hpinned
    omega

/-- Away from the opposite string, the second divided adjoint power annihilates a long root
vector when both roots have long length. -/
theorem f4_dividedPower_two_ad_rootVector_eq_zero_of_long
    (α β : Fin 48) (hα : f4Length α = 2) (hβ : f4Length β = 2)
    (hopp : β ≠ f4OppositeRootIndex α) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) •
        f4ChevalleyRootVector (f4KillingRoot β) = 0 := by
  apply f4_dividedPower_two_ad_rootVector_eq_zero_of_no_endpoint α β hopp
  intro γ hγ
  have hpairLower := f4_pairing_ge_neg_one_of_long_ne_opposite α β hα hβ hopp
  rw [f4SimplyConnectedRootDatum_pairing] at hpairLower
  have hlen := f4Length_of_root_eq_add_zsmul α β γ 2 hγ
  rcases f4Length_eq_one_or_eq_two γ with hlenγ | hlenγ
  · rw [hα, hβ, hlenγ] at hlen
    norm_num at hlen
    omega
  · rw [hα, hβ, hlenγ] at hlen
    norm_num at hlen
    omega

/-- The second divided adjoint power annihilates every Cartan element. -/
theorem f4_dividedPower_two_ad_cartan_eq_zero (α : Fin 48)
    (h : F4.cartanSubalgebra valid_F4) :
    Associative.dividedPower 2
        (ad ℚ (F4.lieAlgebra valid_F4)
          (f4ChevalleyRootVector (f4KillingRoot α))) •
        (h : F4.lieAlgebra valid_F4) = 0 := by
  have hfirst : ⁅f4ChevalleyRootVector (f4KillingRoot α),
      (h : F4.lieAlgebra valid_F4)⁆ =
      -(f4KillingRoot α h) • f4ChevalleyRootVector (f4KillingRoot α) := by
    rw [← lie_skew, ← LieSubalgebra.coe_bracket_of_module,
      LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace
      (f4ChevalleyRootVector_isChevalleySystem.toIsSl2System.mem_rootSpace _), neg_smul]
  rw [Associative.dividedPower_def, Module.End.smul_def, LinearMap.smul_apply, pow_two,
    Module.End.mul_apply, ad_apply, ad_apply, hfirst, lie_smul, lie_self, smul_zero,
    smul_zero]

/-- Three adjoint applications annihilate every F4 root vector, regardless of root length. -/
theorem f4_ad_pow_three_rootVector_eq_zero (α β : Fin 48) :
    ((ad ℚ (F4.lieAlgebra valid_F4)
      (f4ChevalleyRootVector (f4KillingRoot α))) ^ 3)
        (f4ChevalleyRootVector (f4KillingRoot β)) = 0 := by
  have hthree : (3 : ℕ) = 2 + 1 := by omega
  by_cases hopp : β = f4OppositeRootIndex α
  · subst β
    have hdiv := f4_dividedPower_two_ad_rootVector_opposite α
    rw [Associative.dividedPower_def, Module.End.smul_def, LinearMap.smul_apply] at hdiv
    have hpow : ((ad ℚ (F4.lieAlgebra valid_F4)
        (f4ChevalleyRootVector (f4KillingRoot α))) ^ 2)
          (f4ChevalleyRootVector (f4KillingRoot (f4OppositeRootIndex α))) =
            (-2 : ℚ) • f4ChevalleyRootVector (f4KillingRoot α) := by
      rw [f4KillingRoot_f4OppositeRootIndex]
      have h := congrArg (fun x : F4.lieAlgebra valid_F4 => (2 : ℚ) • x) hdiv
      simpa [smul_smul] using h
    rw [hthree, pow_succ', Module.End.mul_apply, hpow, map_smul, ad_apply,
      lie_self, smul_zero]
  · rcases f4Length_eq_one_or_eq_two β with hβ | hβ
    · have hdiv := f4_dividedPower_two_ad_rootVector_eq_zero_of_short α β hβ hopp
      have hpow := (f4_dividedPower_two_ad_smul_eq_zero_iff α _).1 hdiv
      rw [hthree, pow_succ', Module.End.mul_apply, hpow, map_zero]
    · rcases f4Length_eq_one_or_eq_two α with hα | hα
      · apply f4_ad_pow_rootVector_eq_zero_of_no_endpoint α β 3 hopp
        intro δ hpinned
        have hlen := f4Length_of_root_eq_add_zsmul α β δ 3 hpinned
        have hpair := abs_pairing_f4SimplyConnectedRootDatum_le_two β α
        have hpairLower : -2 ≤ f4SimplyConnectedRootDatum.pairing β α :=
          (abs_le.mp hpair).1
        rw [f4SimplyConnectedRootDatum_pairing] at hpairLower
        rcases f4Length_eq_one_or_eq_two δ with hδ | hδ
        all_goals rw [hα, hβ, hδ] at hlen
        all_goals norm_num at hlen
        all_goals omega
      · have hdiv := f4_dividedPower_two_ad_rootVector_eq_zero_of_long α β hα hβ hopp
        have hpow := (f4_dividedPower_two_ad_smul_eq_zero_iff α _).1 hdiv
        rw [hthree, pow_succ', Module.End.mul_apply, hpow, map_zero]

/-- The third adjoint power annihilates every Cartan element. -/
theorem f4_ad_pow_three_cartan_eq_zero (α : Fin 48)
    (h : F4.cartanSubalgebra valid_F4) :
    ((ad ℚ (F4.lieAlgebra valid_F4)
      (f4ChevalleyRootVector (f4KillingRoot α))) ^ 3)
        (h : F4.lieAlgebra valid_F4) = 0 := by
  have hdiv := f4_dividedPower_two_ad_cartan_eq_zero α h
  have hpow := (f4_dividedPower_two_ad_smul_eq_zero_iff α _).1 hdiv
  have hthree : (3 : ℕ) = 2 + 1 := by omega
  rw [hthree, pow_succ', Module.End.mul_apply, hpow, map_zero]


end

end TauCeti.DynkinType
