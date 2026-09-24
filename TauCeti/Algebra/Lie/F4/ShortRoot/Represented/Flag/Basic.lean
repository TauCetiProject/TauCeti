/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Comodule
public import TauCeti.Algebra.Lie.F4.ShortRoot.Quotient.Basis
public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Quotient
public import TauCeti.LinearAlgebra.ExtensionBasis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod

/-!
# The represented split flag for modular F4

The adjoint action on the modular short-root ideal gives subspaces
`J = ρ(I) ⊆ M = ρ(L) ⊆ End(I)`. This file chooses an ambient basis adapted to that flag.
The middle block is prescribed: modulo `J`, it is the special-isogeny-indexed basis of `L / I`
transported through the represented-quotient equivalence. The bases of `J` and `End(I) / M` are
arbitrary, so no dimensions of `J` or `M` need to be computed.

The ambient endomorphism space is then identified with the fixed cotangent dual of `GL₂₆`, where
the existing adjoint comodule acts. Weights `2`, `1`, and `0` record the three blocks.
-/

public section

namespace TauCeti.DynkinType

open Module

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- Keep the range and quotient instances abstract while assembling the adapted basis.  At the
concrete represented subtypes, asking elaboration to infer both structures at once is prohibitively
expensive. -/
private noncomputable def representedRangeBasis
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {m n : ℕ}
    (f : V →ₗ[k] W) (I : Submodule k V) (hker : LinearMap.ker f ≤ I)
    (bImage : Basis (Fin m) k (I.map f.rangeRestrict))
    (bQuot : Basis (Fin n) k (V ⧸ I)) :
    Basis (Fin (m + n)) k f.range :=
  TauCeti.extensionBasis (I.map f.rangeRestrict) bImage
    (bQuot.map (LinearMap.quotientEquivRangeQuotientMap f I hker))

private theorem representedRangeBasis_natAdd_mkQ
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {m n : ℕ}
    (f : V →ₗ[k] W) (I : Submodule k V) (hker : LinearMap.ker f ≤ I)
    (bImage : Basis (Fin m) k (I.map f.rangeRestrict))
    (bQuot : Basis (Fin n) k (V ⧸ I)) (j : Fin n) :
    Submodule.Quotient.mk
        (representedRangeBasis f I hker bImage bQuot (Fin.natAdd m j)) =
      LinearMap.quotientEquivRangeQuotientMap f I hker (bQuot j) := by
  rw [representedRangeBasis, TauCeti.extensionBasis_natAdd_mkQ,
    Module.Basis.map_apply]

private theorem representedRangeBasis_castAdd
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] {m n : ℕ}
    (f : V →ₗ[k] W) (I : Submodule k V) (hker : LinearMap.ker f ≤ I)
    (bImage : Basis (Fin m) k (I.map f.rangeRestrict))
    (bQuot : Basis (Fin n) k (V ⧸ I)) (i : Fin m) :
    representedRangeBasis f I hker bImage bQuot (Fin.castAdd n i) = bImage i := by
  rw [representedRangeBasis, TauCeti.extensionBasis_castAdd]

private noncomputable local instance : AddCommGroup f4ShortRootRepresentedIdeal :=
  Module.addCommMonoidToAddCommGroup 𝔽₂

/-- The dimension of the represented image of the short-root ideal. -/
abbrev f4ShortRootRepresentedIdealRank :=
  finrank 𝔽₂ f4ShortRootRepresentedIdeal

/-- The dimension of the quotient of the ambient endomorphism space by the represented range. -/
abbrev f4ShortRootRepresentedComplementRank :=
  finrank 𝔽₂
    (Module.End 𝔽₂ f4ShortRootLieIdeal ⧸ f4ShortRootRepresentedRange)

/-- An arbitrary basis of the represented image of the short-root ideal. -/
noncomputable def f4ShortRootRepresentedIdealBasis :
    Basis (Fin f4ShortRootRepresentedIdealRank) 𝔽₂ f4ShortRootRepresentedIdeal :=
  Module.finBasis 𝔽₂ f4ShortRootRepresentedIdeal

/-- The prescribed basis of `M / J`, obtained from the special-isogeny-indexed basis of `L / I`. -/
noncomputable def f4ShortRootRepresentedQuotientBasis :=
  f4ShortRootQuotientBasis.map
    (LinearMap.quotientEquivRangeQuotientMap f4ShortRootAdjointLinearMap
      f4ShortRootSubspace ker_f4ShortRootAdjoint_le_f4ShortRootSubspace)

/-- A basis of the represented range `M` adapted to `J ⊆ M`, with prescribed quotient block. -/
noncomputable def f4ShortRootRepresentedRangeBasis :
    Basis (Fin (f4ShortRootRepresentedIdealRank + 26)) 𝔽₂
      f4ShortRootRepresentedRange :=
  representedRangeBasis f4ShortRootAdjointLinearMap f4ShortRootSubspace
    ker_f4ShortRootAdjoint_le_f4ShortRootSubspace
    f4ShortRootRepresentedIdealBasis f4ShortRootQuotientBasis

/-- An arbitrary basis of `End(I) / M`. -/
noncomputable def f4ShortRootRepresentedComplementBasis :
    Basis (Fin f4ShortRootRepresentedComplementRank) 𝔽₂
      (Module.End 𝔽₂ f4ShortRootLieIdeal ⧸ f4ShortRootRepresentedRange) :=
  Module.finBasis 𝔽₂
    (Module.End 𝔽₂ f4ShortRootLieIdeal ⧸ f4ShortRootRepresentedRange)

/-- A basis of `End(I)` adapted to `J ⊆ M ⊆ End(I)`. -/
noncomputable def f4ShortRootEndBasis :
    Basis
      (Fin ((f4ShortRootRepresentedIdealRank + 26) +
        f4ShortRootRepresentedComplementRank)) 𝔽₂
      (Module.End 𝔽₂ f4ShortRootLieIdeal) :=
  TauCeti.extensionBasis f4ShortRootRepresentedRange
    f4ShortRootRepresentedRangeBasis f4ShortRootRepresentedComplementBasis

/-- Identify endomorphisms of the based short-root ideal with the cotangent dual of `GL₂₆`. -/
@[expose] noncomputable def f4ShortRootEndEquivCotangentDual :
    Module.End 𝔽₂ f4ShortRootLieIdeal ≃ₗ[𝔽₂]
      Module.Dual 𝔽₂
        (Bialgebra.CotangentSpace 𝔽₂
          (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)) :=
  (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis).trans
    (GeneralLinear.cotangentDualMatrixEquiv (k := 𝔽₂) (n := 26)).symm

private theorem linearEquiv_apply_trans_symm
    {R U V W : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (f : U ≃ₗ[R] V) (e : W ≃ₗ[R] V) (x : U) :
    e (f.trans e.symm x) = f x := by
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- Matrix coordinates undo the endomorphism-to-cotangent identification. -/
@[simp]
theorem cotangentDualMatrixEquiv_f4ShortRootEndEquivCotangentDual
    (T : Module.End 𝔽₂ f4ShortRootLieIdeal) :
    GeneralLinear.cotangentDualMatrixEquiv (f4ShortRootEndEquivCotangentDual T) =
      (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis) T := by
  exact linearEquiv_apply_trans_symm
    (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis)
    (GeneralLinear.cotangentDualMatrixEquiv (k := 𝔽₂) (n := 26)) T

/-- The cotangent-dual basis carrying the represented flag `J ⊆ M ⊆ End(I)`. -/
@[expose] noncomputable def f4ShortRootCotangentFlagBasis :
    Basis
      (Fin ((f4ShortRootRepresentedIdealRank + 26) +
        f4ShortRootRepresentedComplementRank)) 𝔽₂
      (Module.Dual 𝔽₂
        (Bialgebra.CotangentSpace 𝔽₂
          (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26))) :=
  f4ShortRootEndBasis.map f4ShortRootEndEquivCotangentDual

@[simp] theorem f4ShortRootCotangentFlagBasis_apply (i) :
    f4ShortRootCotangentFlagBasis i =
      f4ShortRootEndEquivCotangentDual (f4ShortRootEndBasis i) :=
  Module.Basis.map_apply f4ShortRootEndBasis f4ShortRootEndEquivCotangentDual i

/-- Weights `2`, `1`, and `0` on the `J`, `M/J`, and `End(I)/M` blocks. -/
@[expose] def f4ShortRootCotangentFlagWeight
    (i : Fin ((f4ShortRootRepresentedIdealRank + 26) +
      f4ShortRootRepresentedComplementRank)) : ℤ :=
  if i.val < f4ShortRootRepresentedIdealRank then 2
  else if i.val < f4ShortRootRepresentedIdealRank + 26 then 1
  else 0

/-- The first block of the represented-range basis is the represented-ideal basis. -/
@[simp]
theorem f4ShortRootRepresentedRangeBasis_ideal
    (i : Fin f4ShortRootRepresentedIdealRank) :
    f4ShortRootRepresentedRangeBasis (Fin.castAdd 26 i) =
      f4ShortRootRepresentedIdealBasis i :=
  representedRangeBasis_castAdd f4ShortRootAdjointLinearMap f4ShortRootSubspace
    ker_f4ShortRootAdjoint_le_f4ShortRootSubspace
    f4ShortRootRepresentedIdealBasis f4ShortRootQuotientBasis i

/-- The second block of the represented-range basis projects to the modular quotient basis. -/
@[simp]
theorem f4ShortRootRepresentedRangeBasis_quotient (a : Fin 26) :
    Submodule.Quotient.mk
        (f4ShortRootRepresentedRangeBasis
          (Fin.natAdd f4ShortRootRepresentedIdealRank a)) =
      LinearMap.quotientEquivRangeQuotientMap f4ShortRootAdjointLinearMap
        f4ShortRootSubspace ker_f4ShortRootAdjoint_le_f4ShortRootSubspace
        (f4ShortRootQuotientBasis a) :=
  representedRangeBasis_natAdd_mkQ f4ShortRootAdjointLinearMap f4ShortRootSubspace
    ker_f4ShortRootAdjoint_le_f4ShortRootSubspace
    f4ShortRootRepresentedIdealBasis f4ShortRootQuotientBasis a

/-- The first two blocks of the adapted endomorphism basis equal the represented-range basis. -/
@[simp]
theorem f4ShortRootEndBasis_range (i : Fin (f4ShortRootRepresentedIdealRank + 26)) :
    f4ShortRootEndBasis (Fin.castAdd f4ShortRootRepresentedComplementRank i) =
      f4ShortRootRepresentedRangeBasis i :=
  TauCeti.extensionBasis_castAdd f4ShortRootRepresentedRange
    f4ShortRootRepresentedRangeBasis f4ShortRootRepresentedComplementBasis i

/-- The first two cotangent-flag blocks are the image of the represented-range basis. -/
theorem f4ShortRootCotangentFlagBasis_range
    (i : Fin (f4ShortRootRepresentedIdealRank + 26)) :
    f4ShortRootCotangentFlagBasis
        (Fin.castAdd f4ShortRootRepresentedComplementRank i) =
      f4ShortRootEndEquivCotangentDual (f4ShortRootRepresentedRangeBasis i) := by
  calc
    _ = f4ShortRootEndEquivCotangentDual
        (f4ShortRootEndBasis (Fin.castAdd f4ShortRootRepresentedComplementRank i)) :=
      f4ShortRootCotangentFlagBasis_apply _
    _ = _ := congrArg f4ShortRootEndEquivCotangentDual (f4ShortRootEndBasis_range i)

/-- The first cotangent-flag block is the image of the represented-ideal basis. -/
theorem f4ShortRootCotangentFlagBasis_ideal
    (i : Fin f4ShortRootRepresentedIdealRank) :
    f4ShortRootCotangentFlagBasis
        (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)) =
      f4ShortRootEndEquivCotangentDual
        (f4ShortRootRepresentedRange.subtype (f4ShortRootRepresentedIdealBasis i)) := by
  calc
    _ = f4ShortRootEndEquivCotangentDual
        (f4ShortRootRepresentedRangeBasis (Fin.castAdd 26 i)) :=
      f4ShortRootCotangentFlagBasis_range _
    _ = _ := congrArg
      (fun x : f4ShortRootRepresentedRange =>
        f4ShortRootEndEquivCotangentDual (x : Module.End 𝔽₂ f4ShortRootLieIdeal))
      (f4ShortRootRepresentedRangeBasis_ideal i)

@[simp]
theorem f4ShortRootCotangentFlagWeight_ideal
    (i : Fin f4ShortRootRepresentedIdealRank) :
    f4ShortRootCotangentFlagWeight
        (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)) = 2 := by
  simp [f4ShortRootCotangentFlagWeight]

@[simp]
theorem f4ShortRootCotangentFlagWeight_quotient (a : Fin 26) :
    f4ShortRootCotangentFlagWeight
        (Fin.castAdd f4ShortRootRepresentedComplementRank
          (Fin.natAdd f4ShortRootRepresentedIdealRank a)) = 1 := by
  simp [f4ShortRootCotangentFlagWeight]

@[simp]
theorem f4ShortRootCotangentFlagWeight_complement
    (i : Fin f4ShortRootRepresentedComplementRank) :
    f4ShortRootCotangentFlagWeight
        (Fin.natAdd (f4ShortRootRepresentedIdealRank + 26) i) = 0 := by
  simp [f4ShortRootCotangentFlagWeight]
  omega

end


end TauCeti.DynkinType
