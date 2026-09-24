/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Flag.Basic
public import TauCeti.Algebra.Lie.F4.ShortRoot.TorusAction

/-!
# Scalar-extended coordinate spans of the represented modular F4 flag

This file identifies the first two blocks of the adapted represented basis with the concrete
matrix-coordinate scalar extensions preserved by the F4 generators.  The statements work over
an arbitrary value algebra over `ZMod 2`; no injectivity or flatness hypothesis is used.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

/-- Entrywise scalar extension of an endomorphism of the modular short-root ideal, in its
distinguished matrix coordinates. -/
noncomputable def f4ShortRootEndMatrixBaseChangeLinearMap :
    Module.End 𝔽₂ f4ShortRootLieIdeal →ₗ[𝔽₂] Matrix (Fin 26) (Fin 26) A :=
  (Algebra.linearMap 𝔽₂ A).mapMatrix.comp
    (LinearMap.toMatrix f4ShortRootLieIdealBasis
      f4ShortRootLieIdealBasis).toLinearMap

/-- Scalar extension of the adjoint endomorphism agrees with its named matrix. -/
@[simp] theorem f4ShortRootEndMatrixBaseChangeLinearMap_adjoint
    (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootEndMatrixBaseChangeLinearMap (A := A) (f4ShortRootAdjointLinearMap X) =
      f4ShortRootAdjointMatrixBaseChange (A := A) X := by
  ext i j
  simp [f4ShortRootEndMatrixBaseChangeLinearMap, f4ShortRootAdjointMatrixBaseChange,
    f4ShortRootAdjointLinearMap, LinearMap.toMatrix_apply]

/-- The scalar-extended span of the first, represented-ideal block of the adapted endomorphism
basis. -/
noncomputable def f4ShortRootRepresentedIdealBasisMatrixBaseChange :
    Submodule A (Matrix (Fin 26) (Fin 26) A) :=
  Submodule.span A <| Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
    f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
      (f4ShortRootEndBasis
        (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)))

/-- The scalar-extended span of the first two blocks of the adapted endomorphism basis. -/
noncomputable def f4ShortRootRepresentedRangeBasisMatrixBaseChange :
    Submodule A (Matrix (Fin 26) (Fin 26) A) :=
  Submodule.span A <| Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
    f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
      (f4ShortRootEndBasis (Fin.castAdd f4ShortRootRepresentedComplementRank i))

private theorem range_comp_rangeRestrict
    {R V W N : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid N] [Module R N]
    (f : V →ₗ[R] W) (g : W →ₗ[R] N) :
    Set.range (g.comp f) = Set.range (g.comp f.range.subtype) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨f x, LinearMap.mem_range_self f x⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, by
      simp only [LinearMap.comp_apply]
      rw [hx]
      rfl⟩

private theorem range_comp_map_subtype
    {R V W N : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid N] [Module R N]
    (f : V →ₗ[R] W) (I : Submodule R V) (g : W →ₗ[R] N) :
    Set.range (g.comp (f.comp I.subtype)) =
      Set.range ((g.comp f.range.subtype).comp (I.map f.rangeRestrict).subtype) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    let y : I.map f.rangeRestrict := ⟨f.rangeRestrict x, Submodule.mem_map_of_mem x.2⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, by
      simp only [LinearMap.comp_apply]
      exact congrArg g (congrArg Subtype.val hxy)⟩

/-- The first two adapted basis blocks span exactly the represented range after scalar extension. -/
theorem f4ShortRootRepresentedRangeBasisMatrixBaseChange_eq :
    f4ShortRootRepresentedRangeBasisMatrixBaseChange (A := A) =
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  let g := f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
  calc
    f4ShortRootRepresentedRangeBasisMatrixBaseChange (A := A) =
        Submodule.span A (Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
          g (f4ShortRootEndBasis (Fin.castAdd f4ShortRootRepresentedComplementRank i))) := rfl
    _ = Submodule.span A (Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
          g (f4ShortRootRepresentedRangeBasis i)) := by
      apply congrArg (Submodule.span A)
      apply congrArg Set.range
      funext i
      exact congrArg g (f4ShortRootEndBasis_range i)
    _ = Submodule.span A (Set.range
          ((g.comp f4ShortRootRepresentedRange.subtype) ∘
            f4ShortRootRepresentedRangeBasis)) := rfl
    _ = Submodule.span A (Set.range (g.comp f4ShortRootRepresentedRange.subtype)) :=
      (span_range_eq_span_range_basis (S := A) f4ShortRootRepresentedRangeBasis
        (g.comp f4ShortRootRepresentedRange.subtype)).symm
    _ = Submodule.span A (Set.range (g.comp f4ShortRootAdjointLinearMap)) :=
      congrArg (Submodule.span A) (range_comp_rangeRestrict
        f4ShortRootAdjointLinearMap g).symm
    _ = Submodule.span A (Set.range fun X : f4ModularChevalleyLieAlgebra =>
          f4ShortRootAdjointMatrixBaseChange (A := A) X) := by
      congr 2
      funext X
      exact f4ShortRootEndMatrixBaseChangeLinearMap_adjoint X
    _ = f4ShortRootRepresentedRangeMatrixSpan (A := A) :=
      f4ShortRootRepresentedRangeMatrixSpan_eq_span_range.symm
    _ = f4ShortRootRepresentedRangeMatrixBaseChange (A := A) :=
      f4ShortRootRepresentedRangeMatrixBaseChange_eq_span.symm

/-- The first adapted basis block spans exactly the represented ideal after scalar extension. -/
theorem f4ShortRootRepresentedIdealBasisMatrixBaseChange_eq :
    f4ShortRootRepresentedIdealBasisMatrixBaseChange (A := A) =
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  let g := f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
  calc
    f4ShortRootRepresentedIdealBasisMatrixBaseChange (A := A) =
        Submodule.span A (Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
          g (f4ShortRootEndBasis
            (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)))) := rfl
    _ = Submodule.span A (Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
          g (f4ShortRootRepresentedIdealBasis i)) := by
      apply congrArg (Submodule.span A)
      apply congrArg Set.range
      funext i
      exact congrArg g ((f4ShortRootEndBasis_range
        (Fin.castAdd 26 i)).trans (congrArg
          (fun z : f4ShortRootRepresentedRange =>
            (z : Module.End 𝔽₂ f4ShortRootLieIdeal))
          (f4ShortRootRepresentedRangeBasis_ideal i)))
    _ = Submodule.span A (Set.range
          (((g.comp f4ShortRootRepresentedRange.subtype).comp
            f4ShortRootRepresentedIdeal.subtype) ∘ f4ShortRootRepresentedIdealBasis)) := rfl
    _ = Submodule.span A (Set.range
          ((g.comp f4ShortRootRepresentedRange.subtype).comp
            f4ShortRootRepresentedIdeal.subtype)) :=
      (span_range_eq_span_range_basis (S := A) f4ShortRootRepresentedIdealBasis
        ((g.comp f4ShortRootRepresentedRange.subtype).comp
          f4ShortRootRepresentedIdeal.subtype)).symm
    _ = Submodule.span A (Set.range
          (g.comp (f4ShortRootAdjointLinearMap.comp f4ShortRootSubspace.subtype))) :=
      congrArg (Submodule.span A) (range_comp_map_subtype f4ShortRootAdjointLinearMap
        f4ShortRootSubspace g).symm
    _ = Submodule.span A (Set.range fun y : f4ShortRootLieIdeal =>
          f4ShortRootAdjointMatrixBaseChange (A := A)
            (y : f4ModularChevalleyLieAlgebra)) := by
      apply congrArg (Submodule.span A)
      ext M
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨⟨y, mem_f4ShortRootLieIdeal_iff.mpr y.property⟩,
          (f4ShortRootEndMatrixBaseChangeLinearMap_adjoint y).symm⟩
      · rintro ⟨y, rfl⟩
        exact ⟨⟨y, mem_f4ShortRootLieIdeal_iff.mp y.property⟩,
          f4ShortRootEndMatrixBaseChangeLinearMap_adjoint y⟩
    _ = f4ShortRootRepresentedIdealMatrixSpan (A := A) :=
      f4ShortRootRepresentedIdealMatrixSpan_eq_span_range.symm
    _ = f4ShortRootRepresentedIdealMatrixBaseChange (A := A) :=
      f4ShortRootRepresentedIdealMatrixBaseChange_eq_span.symm

/-- Scalar extension of the cotangent-dual matrix coordinates used by the adjoint comodule. -/
@[expose] noncomputable def f4ShortRootCotangentBaseChangeMatrixEquiv :
    TensorProduct 𝔽₂ A (Module.Dual 𝔽₂
          (Bialgebra.CotangentSpace 𝔽₂
            (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26))) ≃ₗ[A]
      Matrix (Fin 26) (Fin 26) A :=
  Derivation.tangentScalarExtensionEquiv
      (R := 𝔽₂) (A := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (B := A) ≪≫ₗ
    GeneralLinear.tangentLinearEquivMatrix 26

/-- Evaluation of the scalar-extended cotangent matrix equivalence. -/
theorem f4ShortRootCotangentBaseChangeMatrixEquiv_apply (x) :
    f4ShortRootCotangentBaseChangeMatrixEquiv (A := A) x =
      GeneralLinear.tangentMatrix 26
        (Derivation.tangentScalarExtensionEquiv
          (R := 𝔽₂) (A := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (B := A) x) := by
  change GeneralLinear.tangentLinearEquivMatrix 26
      (Derivation.tangentScalarExtensionEquiv
        (R := 𝔽₂) (A := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (B := A) x) = _
  rw [GeneralLinear.tangentLinearEquivMatrix_apply]

/-- The transported adapted cotangent basis is the entrywise scalar extension of the adapted
endomorphism basis. -/
theorem f4ShortRootCotangentBaseChangeMatrixEquiv_basis (i) :
    f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
        (f4ShortRootCotangentFlagBasis.baseChange A i) =
      f4ShortRootEndMatrixBaseChangeLinearMap (A := A) (f4ShortRootEndBasis i) := by
  have hbasis : f4ShortRootCotangentFlagBasis i =
      f4ShortRootEndEquivCotangentDual (f4ShortRootEndBasis i) :=
    Module.Basis.map_apply f4ShortRootEndBasis f4ShortRootEndEquivCotangentDual i
  calc
    f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
        (f4ShortRootCotangentFlagBasis.baseChange A i) =
      GeneralLinear.tangentMatrix 26
        (Derivation.tangentScalarExtensionEquiv
          (R := 𝔽₂) (A := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (B := A)
          (f4ShortRootCotangentFlagBasis.baseChange A i)) :=
      f4ShortRootCotangentBaseChangeMatrixEquiv_apply _
    _ = GeneralLinear.tangentMatrix 26
        (Derivation.tangentScalarExtensionEquiv
          (R := 𝔽₂) (A := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (B := A)
          (1 ⊗ₜ[𝔽₂] f4ShortRootCotangentFlagBasis i)) := congrArg
      (fun x => GeneralLinear.tangentMatrix 26
        (Derivation.tangentScalarExtensionEquiv
          (R := 𝔽₂) (A := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (B := A) x))
      (Module.Basis.baseChange_apply A f4ShortRootCotangentFlagBasis i)
    _ = (GeneralLinear.cotangentDualMatrixEquiv (f4ShortRootCotangentFlagBasis i)).map
        (algebraMap 𝔽₂ A) :=
      GeneralLinear.tangentMatrix_tangentScalarExtensionEquiv_one_tmul
        (k := 𝔽₂) (A := A) (n := 26) (f4ShortRootCotangentFlagBasis i)
    _ = (GeneralLinear.cotangentDualMatrixEquiv
          (f4ShortRootEndEquivCotangentDual (f4ShortRootEndBasis i))).map
        (algebraMap 𝔽₂ A) := congrArg
      (fun X => (GeneralLinear.cotangentDualMatrixEquiv X).map (algebraMap 𝔽₂ A)) hbasis
    _ = ((LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis)
          (f4ShortRootEndBasis i)).map (algebraMap 𝔽₂ A) := by
      exact congrArg (fun X => X.map (algebraMap 𝔽₂ A))
        (cotangentDualMatrixEquiv_f4ShortRootEndEquivCotangentDual
          (f4ShortRootEndBasis i))
    _ = f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
        (f4ShortRootEndBasis i) := rfl

/-- Under cotangent-dual matrix coordinates, the first adapted basis block is exactly the
scalar-extended represented ideal. -/
theorem f4ShortRootCotangentFlagIdeal_map :
    (Submodule.span A <| Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
      f4ShortRootCotangentFlagBasis.baseChange A
        (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i))).map
        (f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)).toLinearMap =
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  rw [LinearMap.map_span, ← f4ShortRootRepresentedIdealBasisMatrixBaseChange_eq]
  congr 1
  ext X
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (f4ShortRootCotangentBaseChangeMatrixEquiv_basis _).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, f4ShortRootCotangentBaseChangeMatrixEquiv_basis _⟩

/-- Under cotangent-dual matrix coordinates, the first two adapted basis blocks are exactly the
scalar-extended represented range. -/
theorem f4ShortRootCotangentFlagRange_map :
    (Submodule.span A <| Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
      f4ShortRootCotangentFlagBasis.baseChange A
        (Fin.castAdd f4ShortRootRepresentedComplementRank i)).map
        (f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)).toLinearMap =
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  rw [LinearMap.map_span, ← f4ShortRootRepresentedRangeBasisMatrixBaseChange_eq]
  congr 1
  ext X
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (f4ShortRootCotangentBaseChangeMatrixEquiv_basis _).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, f4ShortRootCotangentBaseChangeMatrixEquiv_basis _⟩

end

end TauCeti.DynkinType
