/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Lattice
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.Index

/-!
# A basis of the modular F4 short-root subspace

The modular short-root subspace has the twenty-four short-root vectors and the two short simple
coroots as a basis. The coordinate equivalence from the short-root weight table fixes the two
zero-weight coordinates as the simple coroots at zero-based Lean indices `2` and `3`.

## Main declarations

* `TauCeti.DynkinType.f4ShortRootBasisCoordinate`: the corresponding full Chevalley-basis label
  of each of the twenty-six short-root coordinates.
* `TauCeti.DynkinType.f4ShortRootBasis`: the resulting basis of `f4ShortRootSubspace`.
* `TauCeti.DynkinType.f4ShortRootLieIdealBasis`: the same basis, carried by the Lie ideal
  `f4ShortRootLieIdeal`; `f4ShortRootLieIdealBasis_repr_apply` identifies its coordinates with the
  ambient Chevalley coordinates.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module Set

noncomputable section

/-- The two short simple nodes in Bourbaki order. -/
def f4ShortSimpleIndex (k : Fin 2) : Fin F4.rank :=
  Fin.cast rank_F4.symm ⟨k + 2, by omega⟩

@[simp] theorem f4ShortSimpleIndex_zero :
    f4ShortSimpleIndex 0 = Fin.cast rank_F4.symm (2 : Fin 4) := by rfl

@[simp] theorem f4ShortSimpleIndex_one :
    f4ShortSimpleIndex 1 = Fin.cast rank_F4.symm (3 : Fin 4) := by rfl

private theorem f4ShortSimpleIndex_injective : Function.Injective f4ShortSimpleIndex := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [f4ShortSimpleIndex, Fin.val_cast] at this
  omega

/-- The full Chevalley-basis coordinate assigned to a short-root-representation coordinate.
Nonzero weights use their unique short-root label; coordinates `12` and `13` use the short
simple-coroot labels `2` and `3`. -/
def f4ShortRootBasisCoordinate (a : Fin 26) : f4ChevalleyIndex :=
  match f4ShortRootWeightIndexEquiv a with
  | Sum.inl i => Sum.inl (f4KillingRootLabel i)
  | Sum.inr k => Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv (f4ShortSimpleIndex k))

@[simp] theorem f4ShortRootBasisCoordinate_symm_inl (i : F4ShortRootIndex) :
    f4ShortRootBasisCoordinate
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
      Sum.inl (f4KillingRootLabel i) := by
  simp only [f4ShortRootBasisCoordinate, Equiv.apply_symm_apply]

@[simp] theorem f4ShortRootBasisCoordinate_symm_inr (k : Fin 2) :
    f4ShortRootBasisCoordinate (f4ShortRootWeightIndexEquiv.symm (Sum.inr k)) =
      Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv (f4ShortSimpleIndex k)) := by
  simp only [f4ShortRootBasisCoordinate, Equiv.apply_symm_apply]

theorem f4ShortRootBasisCoordinate_injective :
    Function.Injective f4ShortRootBasisCoordinate := by
  intro a b hab
  apply f4ShortRootWeightIndexEquiv.injective
  rcases ha : f4ShortRootWeightIndexEquiv a with i | k <;>
    rcases hb : f4ShortRootWeightIndexEquiv b with j | l
  · apply congrArg Sum.inl
    have hab' := hab
    simp only [f4ShortRootBasisCoordinate, ha, hb] at hab'
    apply Subtype.ext
    apply Fin.cast_injective numRoots_F4.symm
    apply (F4.rationalRootSystemEquiv valid_F4).indexEquiv.injective
    exact Sum.inl.inj hab'
  · have hab' := hab
    simp only [f4ShortRootBasisCoordinate, ha, hb] at hab'
    cases hab'
  · have hab' := hab
    simp only [f4ShortRootBasisCoordinate, ha, hb] at hab'
    cases hab'
  · apply congrArg Sum.inr
    have hab' := hab
    simp only [f4ShortRootBasisCoordinate, ha, hb] at hab'
    apply f4ShortSimpleIndex_injective
    apply (F4.lieBasis valid_F4).baseSupportEquiv.injective
    exact Sum.inr.inj hab'

@[simp] theorem range_f4ShortRootBasisCoordinate :
    Set.range f4ShortRootBasisCoordinate = f4ShortChevalleyIndices := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases h : f4ShortRootWeightIndexEquiv a with i | k
    · simp only [f4ShortRootBasisCoordinate, h, mem_f4ShortChevalleyIndices_iff,
        f4ChevalleyIndexIsShort_inl_iff]
      rw [f4PinnedRootIndex_f4KillingRootLabel]
      exact i.property
    · simp only [f4ShortRootBasisCoordinate, h, mem_f4ShortChevalleyIndices_iff,
        f4ChevalleyIndexIsShort_inr_iff]
      rw [f4PinnedSimpleIndexEquiv_baseSupportEquiv]
      fin_cases k <;> simp [f4ShortSimpleIndex]
  · intro hx
    rcases x with α | j
    · have hx' : f4Length (f4PinnedRootIndex α) = 1 :=
        f4ChevalleyIndexIsShort_inl_iff α |>.mp
          (mem_f4ShortChevalleyIndices_iff (Sum.inl α) |>.mp hx)
      let i : F4ShortRootIndex := ⟨f4PinnedRootIndex α, hx'⟩
      refine ⟨f4ShortRootWeightIndexEquiv.symm (Sum.inl i), ?_⟩
      simp only [f4ShortRootBasisCoordinate, Equiv.apply_symm_apply]
      exact congrArg Sum.inl (f4KillingRootLabel_f4PinnedRootIndex α)
    · have hx' : f4PinnedSimpleIndexEquiv j = 2 ∨ f4PinnedSimpleIndexEquiv j = 3 :=
        f4ChevalleyIndexIsShort_inr_iff j |>.mp
          (mem_f4ShortChevalleyIndices_iff (Sum.inr j) |>.mp hx)
      rcases hx' with h2 | h3
      · refine ⟨f4ShortRootWeightIndexEquiv.symm (Sum.inr 0), ?_⟩
        simp only [f4ShortRootBasisCoordinate, Equiv.apply_symm_apply]
        apply congrArg Sum.inr
        have hu : (F4.lieBasis valid_F4).baseSupportEquiv.symm j =
            f4ShortSimpleIndex 0 := by
          apply Fin.ext
          have hv := congrArg Fin.val h2
          simp only [f4PinnedSimpleIndexEquiv_apply, Fin.val_cast] at hv
          simp only [f4ShortSimpleIndex, Fin.val_cast]
          omega
        exact (congrArg (F4.lieBasis valid_F4).baseSupportEquiv hu.symm).trans
          ((F4.lieBasis valid_F4).baseSupportEquiv.apply_symm_apply j)
      · refine ⟨f4ShortRootWeightIndexEquiv.symm (Sum.inr 1), ?_⟩
        simp only [f4ShortRootBasisCoordinate, Equiv.apply_symm_apply]
        apply congrArg Sum.inr
        have hu : (F4.lieBasis valid_F4).baseSupportEquiv.symm j =
            f4ShortSimpleIndex 1 := by
          apply Fin.ext
          have hv := congrArg Fin.val h3
          simp only [f4PinnedSimpleIndexEquiv_apply, Fin.val_cast] at hv
          simp only [f4ShortSimpleIndex, Fin.val_cast]
          omega
        exact (congrArg (F4.lieBasis valid_F4).baseSupportEquiv hu.symm).trans
          ((F4.lieBasis valid_F4).baseSupportEquiv.apply_symm_apply j)

private theorem span_range_f4ShortRootBasisCoordinate_eq :
    Submodule.span (ZMod 2)
        (Set.range (f4ModularChevalleyBasis ∘ f4ShortRootBasisCoordinate)) =
      f4ShortRootSubspace := by
  rw [Set.range_comp, range_f4ShortRootBasisCoordinate]
  exact f4ShortRootSubspace_eq_span.symm

private theorem f4ShortRootBasisCoordinate_linearIndependent :
    LinearIndependent (ZMod 2)
      (f4ModularChevalleyBasis ∘ f4ShortRootBasisCoordinate) :=
  f4ModularChevalleyBasis.linearIndependent.comp _ f4ShortRootBasisCoordinate_injective

/-- **The coordinate basis of the modular short-root subspace.** The directions other than
`12` and `13` are short-root vectors; those two zero-weight directions are the short simple
coroots at zero-based Lean indices `2` and `3`. -/
noncomputable def f4ShortRootBasis :
    Basis (Fin 26) (ZMod 2) f4ShortRootSubspace :=
  (Basis.span f4ShortRootBasisCoordinate_linearIndependent).map
    (LinearEquiv.ofEq _ _ span_range_f4ShortRootBasisCoordinate_eq)

/-- Coercing a short-root basis vector gives the ambient Chevalley basis vector selected
by `f4ShortRootBasisCoordinate`. -/
theorem coe_f4ShortRootBasis (a : Fin 26) :
    (f4ShortRootBasis a : f4ModularChevalleyLieAlgebra) =
      f4ModularChevalleyBasis (f4ShortRootBasisCoordinate a) := by
  simp [f4ShortRootBasis, Basis.map_apply, Basis.span_apply]

@[simp] theorem coe_f4ShortRootBasis_symm_inl (i : F4ShortRootIndex) :
    (f4ShortRootBasis (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) :
      f4ModularChevalleyLieAlgebra) = f4ModularRootVector i := by
  rw [coe_f4ShortRootBasis]
  simp only [f4ShortRootBasisCoordinate, Equiv.apply_symm_apply]
  rw [f4ModularRootVector_eq_basis]

/-- The two zero-weight basis coordinates are the corresponding short simple coroots. -/
@[simp] theorem coe_f4ShortRootBasis_symm_inr (k : Fin 2) :
    (f4ShortRootBasis (f4ShortRootWeightIndexEquiv.symm (Sum.inr k)) :
      f4ModularChevalleyLieAlgebra) = f4ModularSimpleCoroot (f4ShortSimpleIndex k) := by
  simp only [coe_f4ShortRootBasis, f4ShortRootBasisCoordinate_symm_inr,
    f4ModularChevalleyBasis_inr_eq_simpleCoroot, Equiv.symm_apply_apply]

@[simp] theorem coe_f4ShortRootBasis_twelve :
    (f4ShortRootBasis 12 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (2 : Fin 4)) := by
  simpa only [f4ShortRootWeightIndexEquiv_symm_apply_inr_zero,
    f4ShortSimpleIndex_zero] using coe_f4ShortRootBasis_symm_inr 0

@[simp] theorem coe_f4ShortRootBasis_thirteen :
    (f4ShortRootBasis 13 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (3 : Fin 4)) := by
  simpa only [f4ShortRootWeightIndexEquiv_symm_apply_inr_one,
    f4ShortSimpleIndex_one] using coe_f4ShortRootBasis_symm_inr 1

/-- The coordinate basis of the modular short-root Lie ideal. -/
noncomputable def f4ShortRootLieIdealBasis :
    Basis (Fin 26) (ZMod 2) f4ShortRootLieIdeal :=
  f4ShortRootBasis.map (LinearEquiv.ofEq _ _ f4ShortRootLieIdeal_toSubmodule.symm)

/-- The ideal basis has the same ambient Chevalley coordinates as the short-root subspace basis. -/
@[simp] theorem coe_f4ShortRootLieIdealBasis (a : Fin 26) :
    (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) =
      f4ModularChevalleyBasis (f4ShortRootBasisCoordinate a) := by
  exact (LinearEquiv.coe_ofEq_apply f4ShortRootLieIdeal_toSubmodule.symm
    (f4ShortRootBasis a)).trans (coe_f4ShortRootBasis a)

/-- A nonzero-weight ideal basis vector is the corresponding modular short-root vector. -/
theorem coe_f4ShortRootLieIdealBasis_symm_inl (i : F4ShortRootIndex) :
    (f4ShortRootLieIdealBasis (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) :
      f4ModularChevalleyLieAlgebra) = f4ModularRootVector i := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_symm_inl i

/-- The two zero-weight ideal basis vectors are the corresponding short simple coroots. -/
theorem coe_f4ShortRootLieIdealBasis_symm_inr (k : Fin 2) :
    (f4ShortRootLieIdealBasis (f4ShortRootWeightIndexEquiv.symm (Sum.inr k)) :
      f4ModularChevalleyLieAlgebra) = f4ModularSimpleCoroot (f4ShortSimpleIndex k) := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_symm_inr k

/-- A basis coordinate whose short-root weight is the root `i` has the modular root vector of
`i` as its underlying element. -/
theorem coe_f4ShortRootLieIdealBasis_of_weight_eq_root (b : Fin 26) (i : Fin 48)
    (hi : f4Length i = 1) (h : f4ShortRootWeight b = f4Root i) :
    (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra) =
      f4ModularRootVector i := by
  have hb : b = f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨i, hi⟩) := by
    apply f4ShortRootWeightIndexEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (f4ShortRootWeightIndexEquiv_apply_eq_inl_iff _ _).2 h
  rw [hb]
  exact coe_f4ShortRootLieIdealBasis_symm_inl ⟨i, hi⟩

/-- Ideal coordinate twelve is the short simple coroot at index two. -/
theorem coe_f4ShortRootLieIdealBasis_twelve :
    (f4ShortRootLieIdealBasis 12 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (2 : Fin 4)) := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_twelve

/-- Ideal coordinate thirteen is the short simple coroot at index three. -/
theorem coe_f4ShortRootLieIdealBasis_thirteen :
    (f4ShortRootLieIdealBasis 13 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (3 : Fin 4)) := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_thirteen

/-- Coordinates in the ideal basis agree with the corresponding ambient Chevalley coordinates. -/
@[simp] theorem f4ShortRootLieIdealBasis_repr_apply (y : f4ShortRootLieIdeal) (i : Fin 26) :
    f4ShortRootLieIdealBasis.repr y i =
      f4ModularChevalleyBasis.repr (y : f4ModularChevalleyLieAlgebra)
        (f4ShortRootBasisCoordinate i) := by
  -- The ambient coordinate map is linear and sends the ideal basis to the standard coordinates.
  refine f4ShortRootLieIdealBasis.repr_apply_eq
    (fun y a => f4ModularChevalleyBasis.repr (y : f4ModularChevalleyLieAlgebra)
      (f4ShortRootBasisCoordinate a)) ?_ ?_ ?_ y i
  · intro y z
    ext a
    simp [LieSubmodule.coe_add]
  · intro c y
    ext a
    simp
  · intro j
    ext a
    simp [Finsupp.single_apply_left f4ShortRootBasisCoordinate_injective]

end

end TauCeti.DynkinType
