/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Lattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.RootString
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.CartanDetector

/-!
# Centralizers of the short-root vectors in modular type F₄

This file detects the coordinates of an element of the modular Chevalley lattice from its
brackets with the short-root vectors. Long-root coordinates are detected by a structurally
chosen short neighbor, and the remaining Cartan coordinates are detected by the integral span
of the short-root weights.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module Set

noncomputable section

private theorem f4ModularChevalleyBasis_repr_lie_eq_sum
    (X Y : f4ModularChevalleyLieAlgebra) (k : f4ChevalleyIndex) :
    f4ModularChevalleyBasis.repr ⁅X, Y⁆ k =
      ∑ i : f4ChevalleyIndex,
        f4ModularChevalleyBasis.repr X i *
          f4ModularChevalleyBasis.repr ⁅f4ModularChevalleyBasis i, Y⁆ k := by
  conv_lhs => rw [← f4ModularChevalleyBasis.sum_repr X]
  rw [sum_lie]
  simp only [smul_lie, map_sum, LinearEquiv.map_smul]
  simp only [Fintype.sum_sum_type, Finset.univ_eq_attach, Finsupp.coe_add,
    Finsupp.coe_finsetSum, Finsupp.coe_smul, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

private theorem eq_zero_of_f4Root_smul_eq_zero_on_short
    (c : Fin 4 → ZMod 2)
    (hc : ∀ β : Fin 48, f4Length β = 1 → ∑ i, f4Root β i • c i = 0) :
    c = 0 := by
  apply eq_zero_of_f4ShortRootWeight_smul_eq_zero
  intro a
  by_cases ha : f4ShortRootWeight a = 0
  · simp only [ha, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  · obtain ⟨β, hβ, hroot⟩ :=
      (f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha
    simpa only [← hroot] using hc β hβ

private theorem f4ModularChevalleyBasis_repr_simpleCoroot_inl
    (i : Fin F4.rank) (γ : Fin 48) :
    f4ModularChevalleyBasis.repr (f4ModularSimpleCoroot i)
      (Sum.inl (f4KillingRootLabel γ)) = 0 := by
  classical
  rw [f4ModularSimpleCoroot_eq_basis, f4ModularChevalleyBasis.repr_self,
    Finsupp.single_apply]
  split
  · rename_i h
    exact (Sum.inr_ne_inl h).elim
  · rfl

private theorem f4ModularChevalleyBasis_repr_coroot_inl
    (β γ : Fin 48) :
    f4ModularChevalleyBasis.repr (f4ModularCoroot β)
      (Sum.inl (f4KillingRootLabel γ)) = 0 := by
  classical
  rw [f4ModularCoroot_eq_sum_simple, map_sum]
  -- Evaluate the sum of finitely supported coordinate vectors at this root label.
  change (∑ i : Fin F4.rank,
    f4ModularChevalleyBasis.repr
      ((f4Coroot β (Fin.cast rank_F4 i) : ZMod 2) • f4ModularSimpleCoroot i)
        (Sum.inl (f4KillingRootLabel γ))) = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, Finsupp.smul_apply,
    f4ModularChevalleyBasis_repr_simpleCoroot_inl, smul_zero]

private theorem f4ModularChevalleyBasis_repr_smul_rootVector_inl_eq_zero
    (c : ZMod 2) (ε γ : Fin 48) (hεγ : f4KillingRootLabel ε ≠ f4KillingRootLabel γ) :
    f4ModularChevalleyBasis.repr (c • f4ModularRootVector ε)
      (Sum.inl (f4KillingRootLabel γ)) = 0 := by
  classical
  rw [map_smul, f4ModularRootVector_eq_basis,
    f4ModularChevalleyBasis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  split
  · rename_i h
    exact (hεγ (Sum.inl.inj h)).elim
  · exact smul_zero _

private theorem f4ModularChevalleyBasis_repr_smul_rootVector_self
    (c : ZMod 2) (β : Fin 48) :
    f4ModularChevalleyBasis.repr (c • f4ModularRootVector β)
      (Sum.inl (f4KillingRootLabel β)) = c := by
  rw [map_smul, f4ModularRootVector_eq_basis,
    f4ModularChevalleyBasis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- A nonzero, present sum of two Killing roots has the corresponding pinned integral root
label. -/
theorem exists_f4Root_eq_add_of_rootSpace_ne_bot
    (δ β : Fin 48)
    (hsum : (f4KillingRoot δ : (F4.cartanSubalgebra valid_F4) → ℚ) +
      f4KillingRoot β ≠ 0)
    (hbot : rootSpace (F4.cartanSubalgebra valid_F4)
      ((f4KillingRoot δ : (F4.cartanSubalgebra valid_F4) → ℚ) +
        f4KillingRoot β) ≠ ⊥) :
    ∃ ε : Fin 48, f4SimplyConnectedRootDatum.root ε =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root δ := by
  let H := F4.cartanSubalgebra valid_F4
  have hadd : (f4KillingRoot β : H → ℚ) + (f4KillingRoot δ : H → ℚ) =
      (f4KillingRoot δ : H → ℚ) + (f4KillingRoot β : H → ℚ) := add_comm _ _
  have hroot : rootSpace H
      ((f4KillingRoot β : H → ℚ) + (f4KillingRoot δ : H → ℚ)) ≠ ⊥ := by
    rw [hadd]
    exact hbot
  let εweight : Weight ℚ H (F4.lieAlgebra valid_F4) :=
    ⟨(f4KillingRoot β : H → ℚ) + (f4KillingRoot δ : H → ℚ), hroot⟩
  have hεnz : εweight.IsNonZero := by
    intro hz
    apply hsum
    -- Read vanishing of the constructed weight as equality of its underlying functions.
    change (f4KillingRoot β : H → ℚ) + (f4KillingRoot δ : H → ℚ) = 0 at hz
    exact hadd.symm.trans hz
  let εroot : H.root := ⟨εweight, by simpa only [LieSubalgebra.root,
    Finset.mem_filter, Finset.mem_univ, true_and] using hεnz⟩
  let ε : Fin 48 := f4PinnedRootIndex εroot
  have hεweight : f4KillingRoot ε = εweight := by
    exact congrArg
      (fun s : H.root => (s : Weight ℚ H (F4.lieAlgebra valid_F4)))
      (f4KillingRootLabel_f4PinnedRootIndex εroot)
  refine ⟨ε, ?_⟩
  have h := (f4KillingRoot_eq_add_zsmul_iff δ β ε 1).mp
  simp only [Int.cast_one, one_smul] at h
  apply h
  exact congrArg DFunLike.coe hεweight

/-- A nonzero root coordinate in a modular root-vector bracket has the expected integral root
label, even though the bracket itself is reduced modulo two. -/
theorem f4Root_eq_add_of_repr_lie_rootVector_ne_zero
    (δ β γ : Fin 48)
    (hne : f4ModularChevalleyBasis.repr
      ⁅f4ModularRootVector δ, f4ModularRootVector β⁆
        (Sum.inl (f4KillingRootLabel γ)) ≠ 0) :
    f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root δ := by
  classical
  let H := F4.cartanSubalgebra valid_F4
  by_cases hsum :
      (f4KillingRoot δ : H → ℚ) + (f4KillingRoot β : H → ℚ) = 0
  · have hindex : δ = f4OppositeRootIndex β := by
      by_contra hopp
      exact f4KillingRoot_add_ne_zero_of_ne_opposite δ β hopp hsum
    rw [hindex, ← lie_skew, f4Modular_lie_rootVector_opposite, map_neg] at hne
    -- Negation in the coordinate Finsupp is pointwise.
    change -f4ModularChevalleyBasis.repr (f4ModularCoroot β)
      (Sum.inl (f4KillingRootLabel γ)) ≠ 0 at hne
    rw [f4ModularChevalleyBasis_repr_coroot_inl, neg_zero] at hne
    exact (hne rfl).elim
  by_cases hbot : rootSpace H
      ((f4KillingRoot δ : H → ℚ) + (f4KillingRoot β : H → ℚ)) = ⊥
  · have hlie : ⁅f4ModularRootVector δ, f4ModularRootVector β⁆ = 0 :=
      f4Modular_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot δ β hbot
    have hz : f4ModularChevalleyBasis.repr
        ⁅f4ModularRootVector δ, f4ModularRootVector β⁆
          (Sum.inl (f4KillingRootLabel γ)) = 0 := by
      exact congrArg
        (fun Y => f4ModularChevalleyBasis.repr Y
          (Sum.inl (f4KillingRootLabel γ))) hlie |>.trans
            (congrArg (fun f => f (Sum.inl (f4KillingRootLabel γ)))
              (map_zero f4ModularChevalleyBasis.repr))
    exact (hne hz).elim
  · obtain ⟨ε, hε⟩ := exists_f4Root_eq_add_of_rootSpace_ne_bot δ β hsum hbot
    obtain ⟨z, _, hlie⟩ := exists_f4Modular_lie_rootVector_eq_smul_of_add δ β ε hε
    by_cases heq : f4KillingRootLabel ε = f4KillingRootLabel γ
    · have hεγ : ε = γ := by
        simpa only [f4PinnedRootIndex_f4KillingRootLabel] using
          congrArg f4PinnedRootIndex heq
      have hγε : γ = ε := hεγ.symm
      exact hγε ▸ hε
    · have hz : f4ModularChevalleyBasis.repr
          ⁅f4ModularRootVector δ, f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel γ)) = 0 :=
        congrArg
          (fun Y => f4ModularChevalleyBasis.repr Y
            (Sum.inl (f4KillingRootLabel γ))) hlie |>.trans
              (f4ModularChevalleyBasis_repr_smul_rootVector_inl_eq_zero
                (z : ZMod 2) ε γ heq)
      exact (hne hz).elim

private theorem f4ModularChevalleyBasis_repr_lie_rootVector_eq_zero
    (δ β γ : Fin 48)
    (h : f4SimplyConnectedRootDatum.root γ ≠
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root δ) :
    f4ModularChevalleyBasis.repr
      ⁅f4ModularRootVector δ, f4ModularRootVector β⁆
        (Sum.inl (f4KillingRootLabel γ)) = 0 := by
  by_contra hne
  exact h (f4Root_eq_add_of_repr_lie_rootVector_ne_zero δ β γ hne)

private theorem f4ModularChevalleyBasis_repr_lie_simpleCoroot_rootVector_eq_zero
    (i : Fin F4.rank) (β γ : Fin 48) (hβγ : f4KillingRootLabel β ≠ f4KillingRootLabel γ) :
    f4ModularChevalleyBasis.repr
      ⁅f4ModularSimpleCoroot i, f4ModularRootVector β⁆
        (Sum.inl (f4KillingRootLabel γ)) = 0 := by
  rw [f4Modular_lie_simpleCoroot_rootVector]
  exact f4ModularChevalleyBasis_repr_smul_rootVector_inl_eq_zero _ β γ hβγ

private theorem f4KillingRootLabel_ne_of_root_eq_add (α β γ : Fin 48)
    (hγ : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α) :
    f4KillingRootLabel β ≠ f4KillingRootLabel γ := by
  intro heq
  have hindex : β = γ := by
    simpa only [f4PinnedRootIndex_f4KillingRootLabel] using
      congrArg f4PinnedRootIndex heq
  have hzero : f4SimplyConnectedRootDatum.root α = 0 := by
    apply add_left_cancel (a := f4SimplyConnectedRootDatum.root β)
    simpa only [add_zero, hindex] using hγ.symm
  exact f4SimplyConnectedRootDatum.ne_zero α hzero

private theorem f4ModularChevalleyBasis_repr_lie_summand_eq_zero_of_ne_long
    (X : f4ModularChevalleyLieAlgebra) (α β γ : Fin 48)
    (hγ : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α)
    (i : f4ChevalleyIndex) (hi : i ≠ Sum.inl (f4KillingRootLabel α)) :
    f4ModularChevalleyBasis.repr X i *
      f4ModularChevalleyBasis.repr
        ⁅f4ModularChevalleyBasis i, f4ModularRootVector β⁆
          (Sum.inl (f4KillingRootLabel γ)) = 0 := by
  cases i with
  | inl r =>
      let δ : Fin 48 := f4PinnedRootIndex r
      have hne : f4SimplyConnectedRootDatum.root γ ≠
          f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root δ := by
        intro heq
        have hδα : δ = α := f4SimplyConnectedRootDatum.root.injective
          (add_left_cancel (heq.symm.trans hγ))
        have hr : r = f4KillingRootLabel α := by
          calc
            r = f4KillingRootLabel (f4PinnedRootIndex r) :=
              (f4KillingRootLabel_f4PinnedRootIndex r).symm
            _ = f4KillingRootLabel δ := rfl
            _ = f4KillingRootLabel α := congrArg f4KillingRootLabel hδα
        exact hi (congrArg Sum.inl hr)
      have hz := f4ModularChevalleyBasis_repr_lie_rootVector_eq_zero δ β γ hne
      rw [f4ModularChevalleyBasis_inl_eq_rootVector]
      exact mul_eq_zero_of_right _ hz
  | inr r =>
      let j : Fin F4.rank := (F4.lieBasis valid_F4).baseSupportEquiv.symm r
      have hbasis : f4ModularChevalleyBasis (Sum.inr r) =
          f4ModularSimpleCoroot j :=
        f4ModularChevalleyBasis_inr_eq_simpleCoroot r
      have hz := f4ModularChevalleyBasis_repr_lie_simpleCoroot_rootVector_eq_zero
        j β γ (f4KillingRootLabel_ne_of_root_eq_add α β γ hγ)
      have hlie := congrArg (fun Y => ⁅Y, f4ModularRootVector β⁆) hbasis
      have hcoord : f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inr r), f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel γ)) = 0 :=
        congrArg
          (fun Y => f4ModularChevalleyBasis.repr Y
            (Sum.inl (f4KillingRootLabel γ))) hlie |>.trans hz
      exact mul_eq_zero_of_right _ hcoord

private theorem f4ModularChevalleyBasis_repr_lie_distinguished_eq_one
    (α β γ : Fin 48)
    (hbracket : ⁅f4ModularRootVector α, f4ModularRootVector β⁆ =
      f4ModularRootVector γ) :
    f4ModularChevalleyBasis.repr
      ⁅f4ModularChevalleyBasis (Sum.inl (f4KillingRootLabel α)),
        f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel γ)) = 1 := by
  have hbasis : f4ModularChevalleyBasis (Sum.inl (f4KillingRootLabel α)) =
      f4ModularRootVector α := by
    rw [f4ModularChevalleyBasis_inl_eq_rootVector,
      f4PinnedRootIndex_f4KillingRootLabel]
  have hlie : ⁅f4ModularChevalleyBasis (Sum.inl (f4KillingRootLabel α)),
      f4ModularRootVector β⁆ = f4ModularRootVector γ :=
    congrArg (fun Y => ⁅Y, f4ModularRootVector β⁆) hbasis |>.trans hbracket
  exact congrArg
    (fun Y => f4ModularChevalleyBasis.repr Y
      (Sum.inl (f4KillingRootLabel γ))) hlie |>.trans (by
        rw [f4ModularRootVector_eq_basis, f4ModularChevalleyBasis.repr_self,
          Finsupp.single_eq_same])

private theorem f4ModularChevalleyBasis_sum_lie_eq_long_coordinate
    (X : f4ModularChevalleyLieAlgebra) (α β γ : Fin 48)
    (hγ : f4SimplyConnectedRootDatum.root γ =
      f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α)
    (hbracket : ⁅f4ModularRootVector α, f4ModularRootVector β⁆ =
      f4ModularRootVector γ) :
    (∑ i : f4ChevalleyIndex,
      f4ModularChevalleyBasis.repr X i *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis i, f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel γ))) =
      f4ModularChevalleyBasis.repr X (Sum.inl (f4KillingRootLabel α)) := by
  classical
  calc
    _ = f4ModularChevalleyBasis.repr X (Sum.inl (f4KillingRootLabel α)) *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inl (f4KillingRootLabel α)),
            f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel γ)) := by
      apply Finset.sum_eq_single (Sum.inl (f4KillingRootLabel α))
      · intro i _ hi
        exact f4ModularChevalleyBasis_repr_lie_summand_eq_zero_of_ne_long
          X α β γ hγ i hi
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = _ := by
      rw [f4ModularChevalleyBasis_repr_lie_distinguished_eq_one α β γ hbracket,
        mul_one]

private theorem f4ModularChevalleyBasis_repr_lie_rootVector_self_eq_zero
    (δ β : Fin 48) :
    f4ModularChevalleyBasis.repr
      ⁅f4ModularRootVector δ, f4ModularRootVector β⁆
        (Sum.inl (f4KillingRootLabel β)) = 0 := by
  apply f4ModularChevalleyBasis_repr_lie_rootVector_eq_zero
  intro h
  have hzero : f4SimplyConnectedRootDatum.root δ = 0 := by
    apply add_left_cancel (a := f4SimplyConnectedRootDatum.root β)
    simpa only [add_zero] using h.symm
  exact f4SimplyConnectedRootDatum.ne_zero δ hzero

private theorem f4ModularChevalleyBasis_repr_lie_simpleCoroot_rootVector_self
    (i : Fin F4.rank) (β : Fin 48) :
    f4ModularChevalleyBasis.repr
      ⁅f4ModularSimpleCoroot i, f4ModularRootVector β⁆
      (Sum.inl (f4KillingRootLabel β)) =
      (f4Root β (Fin.cast rank_F4 i) : ZMod 2) := by
  let c : ZMod 2 := f4SimplyConnectedRootDatum.pairing β
    (Fin.castAdd 44 (Fin.cast rank_F4 i))
  have hlie : ⁅f4ModularSimpleCoroot i, f4ModularRootVector β⁆ =
      c • f4ModularRootVector β := f4Modular_lie_simpleCoroot_rootVector i β
  have hrepr := congrArg
    (fun Y => f4ModularChevalleyBasis.repr Y
      (Sum.inl (f4KillingRootLabel β))) hlie
  have hcoeff : f4SimplyConnectedRootDatum.pairing β
      (Fin.castAdd 44 (Fin.cast rank_F4 i)) = f4Root β (Fin.cast rank_F4 i) := by
    rw [f4SimplyConnectedRootDatum_pairing, f4Coroot_castAdd,
      dotProduct_single_one]
  exact hrepr.trans <| (f4ModularChevalleyBasis_repr_smul_rootVector_self c β).trans <|
    congrArg (fun z : ℤ => (z : ZMod 2)) hcoeff

private noncomputable def f4CartanCoordinates
    (X : f4ModularChevalleyLieAlgebra) : Fin 4 → ZMod 2 := fun i =>
  f4ModularChevalleyBasis.repr X (Sum.inr (f4PinnedSimpleIndexEquiv.symm i))

private theorem f4CartanCoordinates_apply
    (X : f4ModularChevalleyLieAlgebra) (i : Fin 4) :
    f4CartanCoordinates X i =
      f4ModularChevalleyBasis.repr X
        (Sum.inr (f4PinnedSimpleIndexEquiv.symm i)) := rfl

private theorem f4ModularChevalleyBasis_repr_lie_inr_summand
    (X : f4ModularChevalleyLieAlgebra) (β : Fin 48) (k : Fin 4) :
    f4ModularChevalleyBasis.repr X (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) *
      f4ModularChevalleyBasis.repr
        ⁅f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)),
          f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β)) =
      (f4Root β k : ZMod 2) * f4ModularChevalleyBasis.repr X
        (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) := by
  let i : Fin F4.rank := finCongr rank_F4.symm k
  have hbasis : f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) =
      f4ModularSimpleCoroot i := by
    calc
      _ = f4ModularSimpleCoroot
          ((F4.lieBasis valid_F4).baseSupportEquiv.symm
            (f4PinnedSimpleIndexEquiv.symm k)) :=
        f4ModularChevalleyBasis_inr_eq_simpleCoroot _
      _ = f4ModularSimpleCoroot i := by
        congr 1
        calc
          _ = (finCongr rank_F4).symm k := by
            simp only [f4PinnedSimpleIndexEquiv, Equiv.symm_trans_apply,
              Equiv.symm_symm, Equiv.symm_apply_apply]
          _ = i := rfl
  have hlie := congrArg (fun Y => ⁅Y, f4ModularRootVector β⁆) hbasis
  have hcoord : f4ModularChevalleyBasis.repr
      ⁅f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)),
        f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β)) =
      (f4Root β k : ZMod 2) := by
    refine congrArg
      (fun Y => f4ModularChevalleyBasis.repr Y
        (Sum.inl (f4KillingRootLabel β))) hlie |>.trans ?_
    have hi : Fin.cast rank_F4 i = k := by
      apply Fin.ext
      rfl
    have h := f4ModularChevalleyBasis_repr_lie_simpleCoroot_rootVector_self i β
    rw [hi] at h
    exact h
  calc
    _ = f4ModularChevalleyBasis.repr X
        (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) * (f4Root β k : ZMod 2) :=
      congrArg
        (fun z => f4ModularChevalleyBasis.repr X
          (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) * z) hcoord
    _ = (f4Root β k : ZMod 2) * f4ModularChevalleyBasis.repr X
        (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) := mul_comm _ _

private theorem f4ModularChevalleyBasis_sum_inl_lie_self_eq_zero
    (X : f4ModularChevalleyLieAlgebra) (β : Fin 48) :
    ∑ r : (F4.cartanSubalgebra valid_F4).root,
      f4ModularChevalleyBasis.repr X (Sum.inl r) *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inl r), f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel β)) = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  let δ : Fin 48 := f4PinnedRootIndex r
  have hz := f4ModularChevalleyBasis_repr_lie_rootVector_self_eq_zero δ β
  rw [f4ModularChevalleyBasis_inl_eq_rootVector]
  exact mul_eq_zero_of_right _ hz

private theorem f4CartanDetectorSummand_eq_bracketSummand
    (X : f4ModularChevalleyLieAlgebra) (β : Fin 48) (k : Fin 4) :
    f4Root β k • f4CartanCoordinates X k =
      f4ModularChevalleyBasis.repr X
          (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)),
          f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β)) := by
  calc
    f4Root β k • f4CartanCoordinates X k =
        (f4Root β k : ZMod 2) • f4CartanCoordinates X k :=
      (Int.cast_smul_eq_zsmul (ZMod 2) (f4Root β k) (f4CartanCoordinates X k)).symm
    _ = (f4Root β k : ZMod 2) • f4ModularChevalleyBasis.repr X
        (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) :=
      congrArg ((f4Root β k : ZMod 2) • ·) (f4CartanCoordinates_apply X k)
    _ = (f4Root β k : ZMod 2) * f4ModularChevalleyBasis.repr X
        (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) := by
      exact smul_eq_mul _ _
    _ = _ := (f4ModularChevalleyBasis_repr_lie_inr_summand X β k).symm

private noncomputable def f4CartanBracketSum
    (X : f4ModularChevalleyLieAlgebra) (β : Fin 48) : ZMod 2 :=
  ∑ k : Fin 4,
    f4ModularChevalleyBasis.repr X
        (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) *
      f4ModularChevalleyBasis.repr
        ⁅f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)),
          f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β))

private theorem f4CartanDetectorSum_eq_bracketSum
    (X : f4ModularChevalleyLieAlgebra) (β : Fin 48) :
    (∑ k : Fin 4, f4Root β k • f4CartanCoordinates X k) =
      f4CartanBracketSum X β := by
  rw [f4CartanBracketSum]
  apply Finset.sum_congr rfl
  intro k _
  exact f4CartanDetectorSummand_eq_bracketSummand X β k

private theorem f4CartanCoordinates_eq_zero
    (X : f4ModularChevalleyLieAlgebra)
    (hcentral : ∀ β : Fin 48, f4Length β = 1 →
      ⁅X, f4ModularRootVector β⁆ = 0) :
    f4CartanCoordinates X = 0 := by
  apply eq_zero_of_f4Root_smul_eq_zero_on_short
  intro β hβ
  let f : f4ChevalleyIndex → ZMod 2 := fun i =>
    f4ModularChevalleyBasis.repr X i *
      f4ModularChevalleyBasis.repr
        ⁅f4ModularChevalleyBasis i, f4ModularRootVector β⁆
          (Sum.inl (f4KillingRootLabel β))
  have hsum := f4ModularChevalleyBasis_repr_lie_eq_sum X
    (f4ModularRootVector β) (Sum.inl (f4KillingRootLabel β))
  have hzero : f4ModularChevalleyBasis.repr
      ⁅X, f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β)) = 0 := by
    exact congrArg
      (fun Y => f4ModularChevalleyBasis.repr Y
        (Sum.inl (f4KillingRootLabel β))) (hcentral β hβ) |>.trans
          (congrArg (fun g => g (Sum.inl (f4KillingRootLabel β)))
            (map_zero f4ModularChevalleyBasis.repr))
  have htotal : ∑ i : f4ChevalleyIndex, f i = 0 := hsum.symm.trans hzero
  have hsplit : (∑ r : (F4.cartanSubalgebra valid_F4).root, f (Sum.inl r)) +
      ∑ r : f4KillingBase.support,
        f4ModularChevalleyBasis.repr X (Sum.inr r) *
          f4ModularChevalleyBasis.repr
            ⁅f4ModularChevalleyBasis (Sum.inr r), f4ModularRootVector β⁆
              (Sum.inl (f4KillingRootLabel β)) = 0 := by
    exact (Fintype.sum_sum_type f).symm.trans htotal
  have hroot : ∑ r : (F4.cartanSubalgebra valid_F4).root, f (Sum.inl r) = 0 := by
    -- Expand the local summand f on the root part of the Chevalley basis.
    change ∑ r : (F4.cartanSubalgebra valid_F4).root,
      f4ModularChevalleyBasis.repr X (Sum.inl r) *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inl r), f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel β)) = 0
    exact f4ModularChevalleyBasis_sum_inl_lie_self_eq_zero X β
  have hcartan : ∑ r : f4KillingBase.support,
      f4ModularChevalleyBasis.repr X (Sum.inr r) *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inr r), f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel β)) = 0 := by
    simpa only [hroot, zero_add] using hsplit
  have hindexed : f4CartanBracketSum X β = 0 := by
    rw [f4CartanBracketSum]
    exact (f4PinnedSimpleIndexEquiv.symm.sum_comp (fun r =>
      f4ModularChevalleyBasis.repr X (Sum.inr r) *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inr r), f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel β)))).trans hcartan
  exact (f4CartanDetectorSum_eq_bracketSum X β).trans hindexed

private theorem f4ModularChevalleyBasis_repr_eq_zero_of_long
    (X : f4ModularChevalleyLieAlgebra)
    (hcentral : ∀ β : Fin 48, f4Length β = 1 →
      ⁅X, f4ModularRootVector β⁆ = 0)
    (α : Fin 48) (hα : f4Length α = 2) :
    f4ModularChevalleyBasis.repr X (Sum.inl (f4KillingRootLabel α)) = 0 := by
  classical
  obtain ⟨β, γ, hβ, _, hγ, _, hbot⟩ := exists_f4_short_neighbor_of_long α hα
  have hbracket : ⁅f4ModularRootVector α, f4ModularRootVector β⁆ =
      f4ModularRootVector γ :=
    f4Modular_lie_rootVector_of_add_of_chainBotCoeff_eq_zero α β γ hγ hbot
  have hsum := f4ModularChevalleyBasis_repr_lie_eq_sum X
    (f4ModularRootVector β) (Sum.inl (f4KillingRootLabel γ))
  have hzero : f4ModularChevalleyBasis.repr
      ⁅X, f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel γ)) = 0 := by
    exact congrArg
      (fun Y => f4ModularChevalleyBasis.repr Y
        (Sum.inl (f4KillingRootLabel γ))) (hcentral β hβ) |>.trans
          (congrArg (fun f => f (Sum.inl (f4KillingRootLabel γ)))
            (map_zero f4ModularChevalleyBasis.repr))
  have hsingle := f4ModularChevalleyBasis_sum_lie_eq_long_coordinate
    X α β γ hγ hbracket
  exact hsingle ▸ hsum.symm.trans hzero

/-- A modular Chevalley vector whose coordinates outside the distinguished short labels vanish
belongs to the short-root coordinate subspace. -/
theorem mem_f4ShortRootSubspace_of_repr_eq_zero
    (X : f4ModularChevalleyLieAlgebra)
    (hX : ∀ i : f4ChevalleyIndex, ¬ F4ChevalleyIndexIsShort i →
      f4ModularChevalleyBasis.repr X i = 0) :
    X ∈ f4ShortRootSubspace := by
  rw [← f4ModularChevalleyBasis.sum_repr X]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : F4ChevalleyIndexIsShort i
  · exact Submodule.smul_mem _ _ (f4ModularChevalleyBasis_mem_shortRootSubspace hi)
  · rw [hX i hi, zero_smul]
    exact Submodule.zero_mem _

/-- A modular Chevalley vector that centralizes every short root vector belongs to the
short-root coordinate subspace. -/
theorem mem_f4ShortRootSubspace_of_forall_lie_rootVector_eq_zero
    (X : f4ModularChevalleyLieAlgebra)
    (hcentral : ∀ β : Fin 48, f4Length β = 1 →
      ⁅X, f4ModularRootVector β⁆ = 0) :
    X ∈ f4ShortRootSubspace := by
  apply mem_f4ShortRootSubspace_of_repr_eq_zero X
  intro i hi
  rcases i with r | j
  · have hnot : f4Length (f4PinnedRootIndex r) ≠ 1 := by
      simpa only [f4ChevalleyIndexIsShort_inl_iff] using hi
    rcases f4Length_eq_one_or_eq_two (f4PinnedRootIndex r) with hshort | hlong
    · exact (hnot hshort).elim
    · simpa only [f4KillingRootLabel_f4PinnedRootIndex] using
        f4ModularChevalleyBasis_repr_eq_zero_of_long X hcentral
          (f4PinnedRootIndex r) hlong
  · have hcoord := congrFun (f4CartanCoordinates_eq_zero X hcentral)
      (f4PinnedSimpleIndexEquiv j)
    simpa only [f4CartanCoordinates_apply, Equiv.symm_apply_apply, Pi.zero_apply] using hcoord

end

end TauCeti.DynkinType
