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

The main result, `mem_f4ShortRootSubspace_of_forall_lie_rootVector_eq_zero`, shows that an
element of the modular Chevalley algebra bracketing to zero with every short-root vector lies
in the short-root subspace. Thus the kernel of the adjoint action on the short-root ideal is
contained in the ideal, as needed for the quotient construction.

The proof detects long-root coordinates with a structurally chosen short neighbor, then detects
the remaining Cartan coordinates using the integral span of the short-root weights.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module Set

noncomputable section

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
  calc
    _ = f4ModularChevalleyBasis.repr (f4ModularRootVector γ)
        (Sum.inl (f4KillingRootLabel γ)) :=
      congrArg (fun Y => f4ModularChevalleyBasis.repr Y
        (Sum.inl (f4KillingRootLabel γ))) hlie
    _ = 1 := f4ModularChevalleyBasis_repr_rootVector_self γ

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
  have hbasis : f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm k) :=
    f4ModularChevalleyBasis_inr_f4PinnedSimpleIndexEquiv_symm k
  have hlie := congrArg (fun Y => ⁅Y, f4ModularRootVector β⁆) hbasis
  have hcoord : f4ModularChevalleyBasis.repr
      ⁅f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)),
        f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β)) =
      (f4Root β k : ZMod 2) := by
    refine congrArg
      (fun Y => f4ModularChevalleyBasis.repr Y
        (Sum.inl (f4KillingRootLabel β))) hlie |>.trans ?_
    simpa only [Fin.cast_cast, Fin.cast_eq_self] using
      f4ModularChevalleyBasis_repr_lie_simpleCoroot_rootVector_self
        (Fin.cast rank_F4.symm k) β
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

private theorem f4CartanCoordinates_eq_zero
    (X : f4ModularChevalleyLieAlgebra)
    (hcentral : ∀ β : Fin 48, f4Length β = 1 →
      ⁅X, f4ModularRootVector β⁆ = 0) :
    f4CartanCoordinates X = 0 := by
  apply eq_zero_of_f4Root_smul_eq_zero_on_short
  intro β hβ
  have hsum := Module.Basis.repr_lie_eq_sum f4ModularChevalleyBasis X
    (f4ModularRootVector β) (Sum.inl (f4KillingRootLabel β))
  have hzero : f4ModularChevalleyBasis.repr
      ⁅X, f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β)) = 0 := by
    exact f4ModularChevalleyBasis_repr_eq_zero_of_eq_zero (hcentral β hβ) _
  have htotal : (∑ i : f4ChevalleyIndex,
      f4ModularChevalleyBasis.repr X i *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis i, f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel β))) = 0 := hsum.symm.trans hzero
  rw [Fintype.sum_sum_type] at htotal
  have hroot := f4ModularChevalleyBasis_sum_inl_lie_self_eq_zero X β
  have hcartan : ∑ r : f4KillingBase.support,
      f4ModularChevalleyBasis.repr X (Sum.inr r) *
        f4ModularChevalleyBasis.repr
          ⁅f4ModularChevalleyBasis (Sum.inr r), f4ModularRootVector β⁆
            (Sum.inl (f4KillingRootLabel β)) = 0 := by
    simpa only [hroot, zero_add] using htotal
  calc
    (∑ k : Fin 4, f4Root β k • f4CartanCoordinates X k) =
        ∑ k : Fin 4,
          f4ModularChevalleyBasis.repr X
            (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)) *
          f4ModularChevalleyBasis.repr
            ⁅f4ModularChevalleyBasis (Sum.inr (f4PinnedSimpleIndexEquiv.symm k)),
              f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel β)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact f4CartanDetectorSummand_eq_bracketSummand X β k
    _ = ∑ r : f4KillingBase.support,
          f4ModularChevalleyBasis.repr X (Sum.inr r) *
          f4ModularChevalleyBasis.repr
            ⁅f4ModularChevalleyBasis (Sum.inr r), f4ModularRootVector β⁆
              (Sum.inl (f4KillingRootLabel β)) := by
      exact f4PinnedSimpleIndexEquiv.symm.sum_comp (fun r =>
        f4ModularChevalleyBasis.repr X (Sum.inr r) *
          f4ModularChevalleyBasis.repr
            ⁅f4ModularChevalleyBasis (Sum.inr r), f4ModularRootVector β⁆
              (Sum.inl (f4KillingRootLabel β)))
    _ = 0 := hcartan

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
  have hsum := Module.Basis.repr_lie_eq_sum f4ModularChevalleyBasis X
    (f4ModularRootVector β) (Sum.inl (f4KillingRootLabel γ))
  have hzero : f4ModularChevalleyBasis.repr
      ⁅X, f4ModularRootVector β⁆ (Sum.inl (f4KillingRootLabel γ)) = 0 := by
    exact f4ModularChevalleyBasis_repr_eq_zero_of_eq_zero (hcentral β hβ) _
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
