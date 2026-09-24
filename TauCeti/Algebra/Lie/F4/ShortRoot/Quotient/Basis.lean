/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Basis
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.SpecialMap

/-!
# A basis of the modular F4 quotient by the short-root subspace

The complement of the short-root coordinates consists of the twenty-four long-root vectors and
simple coroots at zero-based Lean indices `0` and `1`. The special F4 root permutation indexes
these coordinates by the same `Fin 26` labels as the short-root basis. Their images in the quotient
form a basis with the normalization required by the special isogeny.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11, for the
  special isogeny of type `F₄` in characteristic two.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII, for the root
  coordinates and the simple-root numbering.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module Set

noncomputable section

/-- The long simple nodes, in the order exchanged with the two short nodes by the isogeny. -/
def f4LongSimpleIndex (k : Fin 2) : Fin F4.rank :=
  Fin.cast rank_F4.symm (![1, 0] k : Fin 4)

private theorem f4LongSimpleIndex_injective : Function.Injective f4LongSimpleIndex := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [f4LongSimpleIndex]

/-- The first complementary simple-coroot coordinate is numbered one. -/
@[simp] theorem f4LongSimpleIndex_zero :
    f4LongSimpleIndex 0 = Fin.cast rank_F4.symm (1 : Fin 4) := by
  rfl

/-- The second complementary simple-coroot coordinate is numbered zero. -/
@[simp] theorem f4LongSimpleIndex_one :
    f4LongSimpleIndex 1 = Fin.cast rank_F4.symm (0 : Fin 4) := by
  rfl

/-- The full Chevalley-basis coordinate complementary to a short-root-representation coordinate.
A short-root label is sent through the special root permutation to its long-root partner; zero
coordinates `12`, `13` are sent to simple-coroot labels `1`, `0`, respectively. -/
def f4LongRootBasisCoordinate (a : Fin 26) : f4ChevalleyIndex :=
  match f4ShortRootWeightIndexEquiv a with
  | Sum.inl i => Sum.inl (f4KillingRootLabel (f4SpecialIsogenyIndexEquiv i))
  | Sum.inr k => Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv (f4LongSimpleIndex k))

/-- A nonzero short-root coordinate is sent to the Chevalley coordinate of its long-root partner
under the special root permutation. -/
@[simp] theorem f4LongRootBasisCoordinate_symm_inl (i : F4ShortRootIndex) :
    f4LongRootBasisCoordinate (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
      Sum.inl (f4KillingRootLabel (f4SpecialIsogenyIndexEquiv i)) := by
  simp [f4LongRootBasisCoordinate]

/-- The zero-weight quotient coordinates are the two long simple-coroot coordinates. -/
@[simp] theorem f4LongRootBasisCoordinate_symm_inr (j : Fin 2) :
    f4LongRootBasisCoordinate (f4ShortRootWeightIndexEquiv.symm (Sum.inr j)) =
      Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv (f4LongSimpleIndex j)) := by
  simp only [f4LongRootBasisCoordinate, Equiv.apply_symm_apply]

/-- Distinct short-root labels name distinct complementary Chevalley coordinates. -/
theorem f4LongRootBasisCoordinate_injective :
    Function.Injective f4LongRootBasisCoordinate := by
  intro a b hab
  apply f4ShortRootWeightIndexEquiv.injective
  rcases ha : f4ShortRootWeightIndexEquiv a with i | k <;>
    rcases hb : f4ShortRootWeightIndexEquiv b with j | l
  · apply congrArg Sum.inl
    have hab' := hab
    simp only [f4LongRootBasisCoordinate, ha, hb] at hab'
    apply Subtype.ext
    apply f4SpecialIsogenyIndexEquiv.injective
    have hroot := congrArg f4PinnedRootIndex (Sum.inl.inj hab')
    simpa only [f4PinnedRootIndex_f4KillingRootLabel] using hroot
  · have hab' := hab
    simp only [f4LongRootBasisCoordinate, ha, hb] at hab'
    cases hab'
  · have hab' := hab
    simp only [f4LongRootBasisCoordinate, ha, hb] at hab'
    cases hab'
  · apply congrArg Sum.inr
    have hab' := hab
    simp only [f4LongRootBasisCoordinate, ha, hb] at hab'
    apply f4LongSimpleIndex_injective
    apply (F4.lieBasis valid_F4).baseSupportEquiv.injective
    exact Sum.inr.inj hab'

/-- The complementary coordinates exhaust exactly the Chevalley coordinates that are not short:
the twenty-four long roots and the two long simple coroots. -/
@[simp] theorem range_f4LongRootBasisCoordinate :
    Set.range f4LongRootBasisCoordinate = f4ShortChevalleyIndicesᶜ := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases h : f4ShortRootWeightIndexEquiv a with i | k
    · simp only [f4LongRootBasisCoordinate, h, Set.mem_compl_iff,
        mem_f4ShortChevalleyIndices_iff, f4ChevalleyIndexIsShort_inl_iff,
        f4PinnedRootIndex_f4KillingRootLabel, f4SpecialIsogenyIndexEquiv_apply]
      rw [f4Length_specialIsogenyIndex_eq_one_iff]
      omega
    · simp only [f4LongRootBasisCoordinate, h, Set.mem_compl_iff,
        mem_f4ShortChevalleyIndices_iff, f4ChevalleyIndexIsShort_inr_iff]
      rw [f4PinnedSimpleIndex, Equiv.symm_apply_apply]
      fin_cases k <;> simp [f4LongSimpleIndex]
  · intro hx
    rcases x with α | j
    · have hne : f4Length (f4PinnedRootIndex α) ≠ 1 := by
        simpa only [Set.mem_compl_iff, mem_f4ShortChevalleyIndices_iff,
          f4ChevalleyIndexIsShort_inl_iff] using hx
      have hlong : f4Length (f4PinnedRootIndex α) = 2 :=
        (f4Length_eq_one_or_eq_two _).resolve_left hne
      have hshort : f4Length (f4SpecialIsogenyIndexEquiv (f4PinnedRootIndex α)) = 1 := by
        rw [f4SpecialIsogenyIndexEquiv_apply,
          f4Length_specialIsogenyIndex_eq_one_iff]
        exact hlong
      let i : F4ShortRootIndex :=
        ⟨f4SpecialIsogenyIndexEquiv (f4PinnedRootIndex α), hshort⟩
      refine ⟨f4ShortRootWeightIndexEquiv.symm (Sum.inl i), ?_⟩
      simp only [f4LongRootBasisCoordinate, Equiv.apply_symm_apply]
      apply congrArg Sum.inl
      dsimp only [i]
      simp only [f4SpecialIsogenyIndexEquiv_apply]
      rw [f4SpecialIsogenyIndex_involutive]
      exact f4KillingRootLabel_f4PinnedRootIndex α
    · have hne : ¬(f4PinnedSimpleIndex j = 2 ∨ f4PinnedSimpleIndex j = 3) := by
        simpa only [Set.mem_compl_iff, mem_f4ShortChevalleyIndices_iff,
          f4ChevalleyIndexIsShort_inr_iff] using hx
      have hj : f4PinnedSimpleIndex j = 0 ∨ f4PinnedSimpleIndex j = 1 := by
        omega
      rcases hj with h0 | h1
      · refine ⟨f4ShortRootWeightIndexEquiv.symm (Sum.inr 1), ?_⟩
        simp only [f4LongRootBasisCoordinate, Equiv.apply_symm_apply]
        apply congrArg Sum.inr
        rw [← (F4.lieBasis valid_F4).baseSupportEquiv.apply_symm_apply j]
        apply congrArg (F4.lieBasis valid_F4).baseSupportEquiv
        apply Fin.ext
        have := congrArg Fin.val h0
        simp only [f4PinnedSimpleIndex, Fin.val_cast] at this
        simpa [f4LongSimpleIndex] using this.symm
      · refine ⟨f4ShortRootWeightIndexEquiv.symm (Sum.inr 0), ?_⟩
        simp only [f4LongRootBasisCoordinate, Equiv.apply_symm_apply]
        apply congrArg Sum.inr
        rw [← (F4.lieBasis valid_F4).baseSupportEquiv.apply_symm_apply j]
        apply congrArg (F4.lieBasis valid_F4).baseSupportEquiv
        apply Fin.ext
        have := congrArg Fin.val h1
        simp only [f4PinnedSimpleIndex, Fin.val_cast] at this
        simpa [f4LongSimpleIndex] using this.symm

/-- The coordinate complement to the modular short-root subspace. -/
def f4LongRootComplement : Submodule (ZMod 2) f4ModularChevalleyLieAlgebra :=
  Submodule.span (ZMod 2) (f4ModularChevalleyBasis '' f4ShortChevalleyIndicesᶜ)

/-- **The short-root subspace and its coordinate complement decompose the reduced Chevalley Lie
algebra.**  This is what makes the complementary coordinates a basis of the quotient. -/
theorem isCompl_f4ShortRootSubspace_f4LongRootComplement :
    IsCompl f4ShortRootSubspace f4LongRootComplement := by
  rw [f4ShortRootSubspace_eq_span, f4LongRootComplement]
  exact f4ModularChevalleyBasis.linearIndependent.isCompl_span_image
    f4ModularChevalleyBasis.span_eq isCompl_compl

private theorem span_range_f4LongRootBasisCoordinate_eq :
    Submodule.span (ZMod 2)
        (Set.range (f4ModularChevalleyBasis ∘ f4LongRootBasisCoordinate)) =
      f4LongRootComplement := by
  rw [Set.range_comp, range_f4LongRootBasisCoordinate]
  rfl

private theorem f4LongRootBasisCoordinate_linearIndependent :
    LinearIndependent (ZMod 2)
      (f4ModularChevalleyBasis ∘ f4LongRootBasisCoordinate) :=
  f4ModularChevalleyBasis.linearIndependent.comp _ f4LongRootBasisCoordinate_injective

/-- The long-root and long-simple-coroot coordinate basis complementary to
`f4ShortRootSubspace`. -/
noncomputable def f4LongRootComplementBasis :
    Basis (Fin 26) (ZMod 2) f4LongRootComplement :=
  (Basis.span f4LongRootBasisCoordinate_linearIndependent).map
    (LinearEquiv.ofEq _ _ span_range_f4LongRootBasisCoordinate_eq)

/-- The complement basis vector embeds as its matching modular Chevalley vector. -/
@[simp] theorem coe_f4LongRootComplementBasis (a : Fin 26) :
    (f4LongRootComplementBasis a : f4ModularChevalleyLieAlgebra) =
      f4ModularChevalleyBasis (f4LongRootBasisCoordinate a) := by
  simp [f4LongRootComplementBasis, Basis.map_apply, Basis.span_apply]

/-- Complement coordinate twelve is the surviving simple coroot at index one. -/
@[simp] theorem f4ModularChevalleyBasis_longRootBasisCoordinate_twelve :
    f4ModularChevalleyBasis (f4LongRootBasisCoordinate 12) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (1 : Fin 4)) := by
  simp only [f4LongRootBasisCoordinate, f4ShortRootWeightIndexEquiv_apply_twelve]
  exact (congrArg
    (fun i ↦ f4ModularChevalleyBasis
      (Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv i)))
    f4LongSimpleIndex_zero).trans (f4ModularSimpleCoroot_eq_basis _).symm

/-- Complement coordinate thirteen is the surviving simple coroot at index zero. -/
@[simp] theorem f4ModularChevalleyBasis_longRootBasisCoordinate_thirteen :
    f4ModularChevalleyBasis (f4LongRootBasisCoordinate 13) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (0 : Fin 4)) := by
  simp only [f4LongRootBasisCoordinate, f4ShortRootWeightIndexEquiv_apply_thirteen]
  exact (congrArg
    (fun i ↦ f4ModularChevalleyBasis
      (Sum.inr ((F4.lieBasis valid_F4).baseSupportEquiv i)))
    f4LongSimpleIndex_one).trans (f4ModularSimpleCoroot_eq_basis _).symm

/-- **The special-isogeny-indexed basis of the modular quotient by the short-root subspace.** -/
noncomputable def f4ShortRootQuotientBasis :
    Basis (Fin 26) (ZMod 2) (f4ModularChevalleyLieAlgebra ⧸ f4ShortRootSubspace) :=
  f4LongRootComplementBasis.map
    (f4ShortRootSubspace.quotientEquivOfIsCompl f4LongRootComplement
      isCompl_f4ShortRootSubspace_f4LongRootComplement).symm

/-- Each quotient basis vector is the class of its complementary Chevalley basis vector. -/
@[simp] theorem f4ShortRootQuotientBasis_apply (a : Fin 26) :
    f4ShortRootQuotientBasis a =
      Submodule.Quotient.mk (f4ModularChevalleyBasis (f4LongRootBasisCoordinate a)) := by
  rw [f4ShortRootQuotientBasis, Basis.map_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply]
  congr 1
  exact coe_f4LongRootComplementBasis a

/-- A nonzero-weight quotient coordinate is the corresponding special-map long-root class. -/
theorem f4ShortRootQuotientBasis_symm_inl (i : F4ShortRootIndex) :
    f4ShortRootQuotientBasis (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) =
      Submodule.Quotient.mk
        (f4ModularRootVector (f4SpecialIsogenyIndexEquiv i)) := by
  rw [f4ShortRootQuotientBasis_apply]
  simp only [f4LongRootBasisCoordinate, Equiv.apply_symm_apply,
    f4ModularChevalleyBasis_inl_eq_rootVector,
    f4PinnedRootIndex_f4KillingRootLabel]

/-- Quotient coordinate twelve is the class of the first surviving simple coroot. -/
theorem f4ShortRootQuotientBasis_twelve :
    f4ShortRootQuotientBasis 12 =
      Submodule.Quotient.mk
        (f4ModularSimpleCoroot (Fin.cast rank_F4.symm (1 : Fin 4))) := by
  rw [f4ShortRootQuotientBasis_apply,
    f4ModularChevalleyBasis_longRootBasisCoordinate_twelve]

/-- Quotient coordinate thirteen is the class of the other surviving simple coroot. -/
theorem f4ShortRootQuotientBasis_thirteen :
    f4ShortRootQuotientBasis 13 =
      Submodule.Quotient.mk
        (f4ModularSimpleCoroot (Fin.cast rank_F4.symm (0 : Fin 4))) := by
  rw [f4ShortRootQuotientBasis_apply,
    f4ModularChevalleyBasis_longRootBasisCoordinate_thirteen]

end

end TauCeti.DynkinType
