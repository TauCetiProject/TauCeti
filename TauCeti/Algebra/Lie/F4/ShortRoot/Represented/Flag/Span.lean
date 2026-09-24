/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Represented.Flag.Basic
public import TauCeti.Algebra.Lie.F4.ShortRoot.TorusAction
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction
public import TauCeti.LinearAlgebra.Basis.RangeSpan
public import TauCeti.LinearAlgebra.LinearMap.Range
public import TauCeti.LinearAlgebra.LinearEquiv.Basic

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
local notation "ρ" => (f4ShortRootAdjoint :
  f4ModularChevalleyLieAlgebra →ₗ[𝔽₂] Module.End 𝔽₂ f4ShortRootLieIdeal)

/-- The cotangent-dual adjoint module of `GL₂₆` over `ZMod 2`. -/
abbrev f4ShortRootCotangentDual :=
  Module.Dual 𝔽₂
    (Bialgebra.CotangentSpace 𝔽₂ (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26))

variable {A : Type} [CommRing A] [Algebra 𝔽₂ A]

/-- The scalar-extended represented-ideal term of the cotangent flag. -/
noncomputable def cotangentFlagIdeal :
    Submodule A (TensorProduct 𝔽₂ A f4ShortRootCotangentDual) :=
  Submodule.span A <| Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
    f4ShortRootCotangentFlagBasis.baseChange A
      (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i))

/-- The scalar-extended represented-range term of the cotangent flag. -/
noncomputable def cotangentFlagRange :
    Submodule A (TensorProduct 𝔽₂ A f4ShortRootCotangentDual) :=
  Submodule.span A <| Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
    f4ShortRootCotangentFlagBasis.baseChange A
      (Fin.castAdd f4ShortRootRepresentedComplementRank i)

/-! ### Stability of the represented flag

The following two submodules are the matrix-coordinate scalar extensions of the represented
range `M` and its represented ideal `J`.  We give them by the images of their distinguished
bases.  This form makes the torus stability argument valid over an arbitrary value algebra,
without any flatness or injectivity hypothesis on its structure map from `ZMod 2`.
-/

/-- The base-changed matrix-coordinate range of the short-root adjoint representation. -/
@[expose] noncomputable def f4ShortRootRepresentedRangeMatrixBaseChange :
    Submodule A (Matrix (Fin 26) (Fin 26) A) :=
  Submodule.span A <| Set.range fun k : f4ChevalleyIndex =>
    f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularChevalleyBasis k)

/-- Each Chevalley adjoint matrix is in the scalar-extended represented range. -/
theorem f4ShortRootRepresentedRangeMatrixBaseChange_mem_basis (k : f4ChevalleyIndex) :
    f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularChevalleyBasis k) ∈
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  unfold f4ShortRootRepresentedRangeMatrixBaseChange
  exact Submodule.subset_span (Set.mem_range_self k)

/-- The base-changed matrix-coordinate image of the short-root ideal. -/
@[expose] noncomputable def f4ShortRootRepresentedIdealMatrixBaseChange :
    Submodule A (Matrix (Fin 26) (Fin 26) A) :=
  Submodule.span A <| Set.range fun i : Fin 26 =>
    f4ShortRootAdjointMatrixBaseChange (A := A)
      (f4ShortRootLieIdealBasis i : f4ModularChevalleyLieAlgebra)

/-- Each ideal-basis adjoint matrix is in the scalar-extended represented ideal. -/
theorem f4ShortRootRepresentedIdealMatrixBaseChange_mem_basis (i : Fin 26) :
    f4ShortRootAdjointMatrixBaseChange (A := A)
        (f4ShortRootLieIdealBasis i : f4ModularChevalleyLieAlgebra) ∈
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  unfold f4ShortRootRepresentedIdealMatrixBaseChange
  exact Submodule.subset_span (Set.mem_range_self i)

private noncomputable def f4ShortRootAdjointMatrixBaseChangeLinearMap :
    f4ModularChevalleyLieAlgebra →ₗ[ZMod 2] Matrix (Fin 26) (Fin 26) A :=
  (Algebra.linearMap (ZMod 2) A).mapMatrix.comp
    ((LinearMap.toMatrix f4ShortRootLieIdealBasis
      f4ShortRootLieIdealBasis).toLinearMap.comp ρ)

private theorem f4ShortRootAdjointMatrixBaseChangeLinearMap_apply
    (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootAdjointMatrixBaseChangeLinearMap (A := A) X =
      f4ShortRootAdjointMatrixBaseChange (A := A) X := by
  ext i j
  simp [f4ShortRootAdjointMatrixBaseChangeLinearMap, f4ShortRootAdjointMatrixBaseChange,
    LinearMap.toMatrix_apply, f4ShortRootLieIdealBasis_repr_apply]

private noncomputable def f4ShortRootIdealAdjointMatrixBaseChangeLinearMap :
    f4ShortRootLieIdeal →ₗ[ZMod 2] Matrix (Fin 26) (Fin 26) A :=
  (f4ShortRootAdjointMatrixBaseChangeLinearMap (A := A)).comp
    f4ShortRootLieIdeal.toSubmodule.subtype

private theorem f4ShortRootIdealAdjointMatrixBaseChangeLinearMap_apply
    (y : f4ShortRootLieIdeal) :
    f4ShortRootIdealAdjointMatrixBaseChangeLinearMap (A := A) y =
      f4ShortRootAdjointMatrixBaseChange (A := A)
        (y : f4ModularChevalleyLieAlgebra) := by
  exact f4ShortRootAdjointMatrixBaseChangeLinearMap_apply _

/-- The distinguished-basis definition of the base-changed represented range agrees with the
`A`-span of every entrywise base-changed matrix in `M`. -/
theorem f4ShortRootRepresentedRangeMatrixBaseChange_eq_span :
    f4ShortRootRepresentedRangeMatrixBaseChange (A := A) =
      Submodule.span A (Set.range fun X : f4ModularChevalleyLieAlgebra =>
        f4ShortRootAdjointMatrixBaseChange (A := A) X) := by
  -- Identify the bundled linear map with its named pointwise matrix function.
  simpa only [f4ShortRootRepresentedRangeMatrixBaseChange,
    Function.comp_def,
    f4ShortRootAdjointMatrixBaseChangeLinearMap_apply,
    show ⇑(f4ShortRootAdjointMatrixBaseChangeLinearMap (A := A)) =
      f4ShortRootAdjointMatrixBaseChange from
        funext f4ShortRootAdjointMatrixBaseChangeLinearMap_apply] using
    (Module.Basis.span_range_eq_span_range_basis (S := A) f4ModularChevalleyBasis
      (f4ShortRootAdjointMatrixBaseChangeLinearMap (A := A))).symm

/-- The distinguished-basis definition of the base-changed represented ideal agrees with the
`A`-span of every entrywise base-changed matrix in `J`. -/
theorem f4ShortRootRepresentedIdealMatrixBaseChange_eq_span :
    f4ShortRootRepresentedIdealMatrixBaseChange (A := A) =
      Submodule.span A (Set.range fun y : f4ShortRootLieIdeal =>
        f4ShortRootAdjointMatrixBaseChange (A := A)
          (y : f4ModularChevalleyLieAlgebra)) := by
  -- Identify the restricted linear map with its named matrix function.
  simpa only [f4ShortRootRepresentedIdealMatrixBaseChange,
    Function.comp_def,
    f4ShortRootIdealAdjointMatrixBaseChangeLinearMap_apply,
    show ⇑(f4ShortRootIdealAdjointMatrixBaseChangeLinearMap (A := A)) =
      (fun y : f4ShortRootLieIdeal =>
        f4ShortRootAdjointMatrixBaseChange (A := A) (y : f4ModularChevalleyLieAlgebra)) from
        funext f4ShortRootIdealAdjointMatrixBaseChangeLinearMap_apply] using
    (Module.Basis.span_range_eq_span_range_basis (S := A) f4ShortRootLieIdealBasis
      (f4ShortRootIdealAdjointMatrixBaseChangeLinearMap (A := A))).symm

/-- The base-changed represented ideal is contained in the base-changed represented range. -/
theorem f4ShortRootRepresentedIdealMatrixBaseChange_le_range :
    f4ShortRootRepresentedIdealMatrixBaseChange (A := A) ≤
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  rw [f4ShortRootRepresentedIdealMatrixBaseChange, Submodule.span_le]
  rintro X ⟨i, rfl⟩
  -- Coerce an ideal-basis vector to the ambient Lie algebra.
  change f4ShortRootAdjointMatrixBaseChange (A := A)
      (f4ShortRootLieIdealBasis i : f4ModularChevalleyLieAlgebra) ∈ _
  rw [coe_f4ShortRootLieIdealBasis]
  exact Submodule.subset_span (Set.mem_range_self (f4ShortRootBasisCoordinate i))

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
    f4ShortRootEndMatrixBaseChangeLinearMap (A := A) (f4ShortRootAdjoint X) =
      f4ShortRootAdjointMatrixBaseChange (A := A) X := by
  ext i j
  simp [f4ShortRootEndMatrixBaseChangeLinearMap, f4ShortRootAdjointMatrixBaseChange,
    LinearMap.toMatrix_apply]

/-- The first two adapted basis blocks span exactly the represented range after scalar extension. -/
private theorem f4ShortRootRepresentedRangeBasisMatrixBaseChange_eq :
    Submodule.span A (Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
      f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
        (f4ShortRootEndBasis (Fin.castAdd f4ShortRootRepresentedComplementRank i))) =
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  let g := f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
  calc
    Submodule.span A (Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
          g (f4ShortRootEndBasis (Fin.castAdd f4ShortRootRepresentedComplementRank i))) =
        Submodule.span A (Set.range fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
          g (f4ShortRootRepresentedRangeBasis i)) := by
      apply congrArg (Submodule.span A)
      apply congrArg Set.range
      funext i
      exact congrArg g (f4ShortRootEndBasis_range i)
    _ = Submodule.span A (Set.range
          ((g.comp f4ShortRootRepresentedRange.subtype) ∘
            f4ShortRootRepresentedRangeBasis)) := rfl
    _ = Submodule.span A (Set.range (g.comp f4ShortRootRepresentedRange.subtype)) :=
      (Module.Basis.span_range_eq_span_range_basis (S := A) f4ShortRootRepresentedRangeBasis
        (g.comp f4ShortRootRepresentedRange.subtype)).symm
    _ = Submodule.span A (Set.range (g.comp ρ)) :=
      congrArg (Submodule.span A) (LinearMap.range_comp_rangeRestrict
        ρ g).symm
    _ = Submodule.span A (Set.range fun X : f4ModularChevalleyLieAlgebra =>
          f4ShortRootAdjointMatrixBaseChange (A := A) X) := by
      congr 2
      funext X
      exact f4ShortRootEndMatrixBaseChangeLinearMap_adjoint X
    _ = f4ShortRootRepresentedRangeMatrixBaseChange (A := A) :=
      f4ShortRootRepresentedRangeMatrixBaseChange_eq_span.symm

/-- The first adapted basis block spans exactly the represented ideal after scalar extension. -/
private theorem f4ShortRootRepresentedIdealBasisMatrixBaseChange_eq :
    Submodule.span A (Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
      f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
        (f4ShortRootEndBasis
          (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)))) =
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  let g := f4ShortRootEndMatrixBaseChangeLinearMap (A := A)
  calc
    Submodule.span A (Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
          g (f4ShortRootEndBasis
            (Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)))) =
        Submodule.span A (Set.range fun i : Fin f4ShortRootRepresentedIdealRank =>
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
      (Module.Basis.span_range_eq_span_range_basis (S := A) f4ShortRootRepresentedIdealBasis
        ((g.comp f4ShortRootRepresentedRange.subtype).comp
          f4ShortRootRepresentedIdeal.subtype)).symm
    _ = Submodule.span A (Set.range
          (g.comp ((ρ).comp f4ShortRootSubspace.subtype))) :=
      congrArg (Submodule.span A) (LinearMap.range_comp_map_subtype ρ
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
    _ = f4ShortRootRepresentedIdealMatrixBaseChange (A := A) :=
      f4ShortRootRepresentedIdealMatrixBaseChange_eq_span.symm

/-- Scalar extension of the cotangent-dual matrix coordinates used by the adjoint comodule. -/
noncomputable def f4ShortRootCotangentBaseChangeMatrixEquiv :
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
  -- Expose the second equivalence in the composition to use its evaluation theorem.
  change GeneralLinear.tangentLinearEquivMatrix 26
      (Derivation.tangentScalarExtensionEquiv
        (R := 𝔽₂) (A := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (B := A) x) = _
  rw [GeneralLinear.tangentLinearEquivMatrix_apply]

/-- The transported adapted cotangent basis is the entrywise scalar extension of the adapted
endomorphism basis. -/
@[simp] theorem f4ShortRootCotangentBaseChangeMatrixEquiv_basis (i) :
    f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
        (1 ⊗ₜ[𝔽₂] f4ShortRootEndEquivCotangentDual (f4ShortRootEndBasis i)) =
      f4ShortRootEndMatrixBaseChangeLinearMap (A := A) (f4ShortRootEndBasis i) := by
  suffices h : f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)
      (f4ShortRootCotangentFlagBasis.baseChange A i) =
        f4ShortRootEndMatrixBaseChangeLinearMap (A := A) (f4ShortRootEndBasis i) by
    simpa only [Module.Basis.baseChange_apply, f4ShortRootCotangentFlagBasis_apply] using h
  have hbasis : f4ShortRootCotangentFlagBasis i =
      f4ShortRootEndEquivCotangentDual (f4ShortRootEndBasis i) :=
    f4ShortRootCotangentFlagBasis_apply i
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
    (cotangentFlagIdeal (A := A)).map
        (f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)).toLinearMap =
      f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  rw [cotangentFlagIdeal, LinearMap.map_span,
    ← f4ShortRootRepresentedIdealBasisMatrixBaseChange_eq]
  congr 1
  ext X
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    simpa only [Module.Basis.baseChange_apply, f4ShortRootCotangentFlagBasis_apply,
      LinearEquiv.coe_coe] using (f4ShortRootCotangentBaseChangeMatrixEquiv_basis (A := A) _).symm
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simpa only [Module.Basis.baseChange_apply, f4ShortRootCotangentFlagBasis_apply,
      LinearEquiv.coe_coe] using (f4ShortRootCotangentBaseChangeMatrixEquiv_basis (A := A) _)

/-- Under cotangent-dual matrix coordinates, the first two adapted basis blocks are exactly the
scalar-extended represented range. -/
theorem f4ShortRootCotangentFlagRange_map :
    (cotangentFlagRange (A := A)).map
        (f4ShortRootCotangentBaseChangeMatrixEquiv (A := A)).toLinearMap =
      f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  rw [cotangentFlagRange, LinearMap.map_span,
    ← f4ShortRootRepresentedRangeBasisMatrixBaseChange_eq]
  congr 1
  ext X
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    simpa only [Module.Basis.baseChange_apply, f4ShortRootCotangentFlagBasis_apply,
      LinearEquiv.coe_coe] using (f4ShortRootCotangentBaseChangeMatrixEquiv_basis (A := A) _).symm
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simpa only [Module.Basis.baseChange_apply, f4ShortRootCotangentFlagBasis_apply,
      LinearEquiv.coe_coe] using (f4ShortRootCotangentBaseChangeMatrixEquiv_basis (A := A) _)

/-- A cotangent vector belongs to the ideal flag term exactly when its matrix coordinates
belong to the base-changed represented ideal. -/
@[simp] theorem mem_cotangentFlagIdeal_iff
    (x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual) :
    x ∈ cotangentFlagIdeal (A := A) ↔
      f4ShortRootCotangentBaseChangeMatrixEquiv (A := A) x ∈
        f4ShortRootRepresentedIdealMatrixBaseChange (A := A) := by
  rw [← f4ShortRootCotangentFlagIdeal_map, Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply]

/-- A cotangent vector belongs to the range flag term exactly when its matrix coordinates
belong to the base-changed represented range. -/
@[simp] theorem mem_cotangentFlagRange_iff
    (x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual) :
    x ∈ cotangentFlagRange (A := A) ↔
      f4ShortRootCotangentBaseChangeMatrixEquiv (A := A) x ∈
        f4ShortRootRepresentedRangeMatrixBaseChange (A := A) := by
  rw [← f4ShortRootCotangentFlagRange_map, Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_apply_apply]

/-- The represented ideal is the first step of the represented range flag. -/
theorem cotangentFlagIdeal_le_range :
    cotangentFlagIdeal (A := A) ≤ cotangentFlagRange (A := A) := by
  intro x hx
  exact (mem_cotangentFlagRange_iff x).mpr
    (f4ShortRootRepresentedIdealMatrixBaseChange_le_range
      ((mem_cotangentFlagIdeal_iff x).mp hx))

/-- The adjoint comodule structure used for the represented cotangent flag. -/
local instance f4ShortRootCotangentAdjointComodule :
    Comodule 𝔽₂ (GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) f4ShortRootCotangentDual :=
  Derivation.adjointComodule
    (R := 𝔽₂) (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)

/-- A point acts block triangularly on the adapted flag if it preserves its two nontrivial steps. -/
theorem f4ShortRoot_adjoint_blockTriangular_of_preserves_flag
    (g : HopfAlgebra.points
      (H := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26) (CommAlgCat.of 𝔽₂ A))
    (hIdeal : ∀ {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual},
      x ∈ cotangentFlagIdeal (A := A) →
        Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
          cotangentFlagIdeal (A := A))
    (hRange : ∀ {x : TensorProduct 𝔽₂ A f4ShortRootCotangentDual},
      x ∈ cotangentFlagRange (A := A) →
        Comodule.endOfPoint f4ShortRootCotangentDual g.ofConv x ∈
          cotangentFlagRange (A := A)) :
    ((Comodule.coefficientMatrix
        (C := GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26)
        f4ShortRootCotangentFlagBasis).map g.ofConv).BlockTriangular
      (OrderDual.toDual ∘ f4ShortRootCotangentFlagWeight) := by
  intro i j hij
  rw [← Comodule.toMatrix_endOfPoint, LinearMap.toMatrix_apply]
  have hweight : f4ShortRootCotangentFlagWeight i <
      f4ShortRootCotangentFlagWeight j := OrderDual.toDual_lt_toDual.mp hij
  by_cases hjIdeal : j.val < f4ShortRootRepresentedIdealRank
  · let j' : Fin f4ShortRootRepresentedIdealRank := ⟨j.val, hjIdeal⟩
    have hj : j = Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 j') :=
      Fin.ext rfl
    have hjmem : f4ShortRootCotangentFlagBasis.baseChange A j ∈
        cotangentFlagIdeal (A := A) := by
      unfold cotangentFlagIdeal
      exact Submodule.subset_span ⟨j', by rw [hj]⟩
    have hmap := hIdeal hjmem
    unfold cotangentFlagIdeal at hmap
    apply Module.Basis.repr_eq_zero_of_mem_span_range
      (f4ShortRootCotangentFlagBasis.baseChange A)
      (fun i : Fin f4ShortRootRepresentedIdealRank =>
        Fin.castAdd f4ShortRootRepresentedComplementRank (Fin.castAdd 26 i)) hmap
    rintro ⟨i', hi'⟩
    have hiIdeal : i.val < f4ShortRootRepresentedIdealRank := by
      rw [← hi']
      exact i'.isLt
    rw [f4ShortRootCotangentFlagWeight_of_ideal j hjIdeal,
      f4ShortRootCotangentFlagWeight_of_ideal i hiIdeal] at hweight
    omega
  · by_cases hjRange : j.val < f4ShortRootRepresentedIdealRank + 26
    · let j' : Fin (f4ShortRootRepresentedIdealRank + 26) := ⟨j.val, hjRange⟩
      have hj : j = Fin.castAdd f4ShortRootRepresentedComplementRank j' := Fin.ext rfl
      have hjmem : f4ShortRootCotangentFlagBasis.baseChange A j ∈
          cotangentFlagRange (A := A) := by
        unfold cotangentFlagRange
        exact Submodule.subset_span ⟨j', by rw [hj]⟩
      have hmap := hRange hjmem
      unfold cotangentFlagRange at hmap
      apply Module.Basis.repr_eq_zero_of_mem_span_range
        (f4ShortRootCotangentFlagBasis.baseChange A)
        (fun i : Fin (f4ShortRootRepresentedIdealRank + 26) =>
          Fin.castAdd f4ShortRootRepresentedComplementRank i) hmap
      rintro ⟨i', hi'⟩
      have hiRange : i.val < f4ShortRootRepresentedIdealRank + 26 := by
        rw [← hi']
        exact i'.isLt
      have hjWeight : f4ShortRootCotangentFlagWeight j = 1 :=
        f4ShortRootCotangentFlagWeight_of_quotient j hjIdeal hjRange
      have hiWeight : 1 ≤ f4ShortRootCotangentFlagWeight i := by
        by_cases hiIdeal : i.val < f4ShortRootRepresentedIdealRank
        · rw [f4ShortRootCotangentFlagWeight_of_ideal i hiIdeal]
          omega
        · rw [f4ShortRootCotangentFlagWeight_of_quotient i hiIdeal hiRange]
      omega
    · have hjWeight : f4ShortRootCotangentFlagWeight j = 0 :=
        f4ShortRootCotangentFlagWeight_of_complement j hjRange
      have hiNonneg : 0 ≤ f4ShortRootCotangentFlagWeight i := by
        by_cases hiIdeal : i.val < f4ShortRootRepresentedIdealRank
        · rw [f4ShortRootCotangentFlagWeight_of_ideal i hiIdeal]
          omega
        · by_cases hiRange : i.val < f4ShortRootRepresentedIdealRank + 26
          · rw [f4ShortRootCotangentFlagWeight_of_quotient i hiIdeal hiRange]
            omega
          · rw [f4ShortRootCotangentFlagWeight_of_complement i hiRange]
      omega

end

end TauCeti.DynkinType
