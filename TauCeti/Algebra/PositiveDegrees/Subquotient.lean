/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.PositiveDegrees.Grading

/-!
# Positive gradings of homogeneous subquotients

Images and injective preimages preserve the support of a positive grading. In particular,
homogeneous submodules and their quotients inherit positive internal gradings. At each
cutoff the restricted filtration is the preimage of the ambient degree submodule, and
the quotient filtration is its image.

Adapted from `Mei/Algebra/PositiveDegrees/Subquotient.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e`, released under Apache 2.0.
-/

public section

namespace TauCeti

section LinearMap

variable {ι R M M' : Type*} [AddCommMonoid ι] [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  {d : PositiveDegrees ι} {ℳ : ι → Submodule R M}

namespace IsPositiveGrading

/-- Taking linear images of the homogeneous pieces preserves positive support. -/
instance map [IsPositiveGrading d ℳ] (f : M →ₗ[R] M') :
    IsPositiveGrading d (fun i => (ℳ i).map f) where
  eq_bot i hi := by rw [eq_bot (d := d) (ℒ := ℳ) i hi, Submodule.map_bot]

/-- Taking preimages under an injective linear map preserves positive support. -/
theorem comap [IsPositiveGrading d ℳ] (f : M' →ₗ[R] M) (hf : Function.Injective f) :
    IsPositiveGrading d (fun i => (ℳ i).comap f) where
  eq_bot i hi := by
    rw [eq_bot (d := d) (ℒ := ℳ) i hi, Submodule.comap_bot,
      LinearMap.ker_eq_bot_of_injective hf]

end IsPositiveGrading

/-- Taking linear images of the pieces commutes with forming a degree submodule. -/
theorem PositiveDegrees.degreeSubmodule_map (d : PositiveDegrees ι)
    (ℳ : ι → Submodule R M) (f : M →ₗ[R] M') (k : ℕ) :
    d.degreeSubmodule (fun i => (ℳ i).map f) k = (d.degreeSubmodule ℳ k).map f := by
  rw [degreeSubmodule_def, degreeSubmodule_def, Submodule.map_iSup]

end LinearMap

section Submodule

variable {ι R S M : Type*} [AddCommMonoid ι] [DecidableEq ι] [Semiring R] [Semiring S]
  [SMul R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  {d : PositiveDegrees ι} (G : InternalGrading R M ι) (U : Submodule S M)
  (hU : DirectSum.SetLike.IsHomogeneous G.piece U)

/-- The inherited grading of a homogeneous submodule is positive. -/
instance IsPositiveGrading.submodule [IsPositiveGrading d G.piece] :
    IsPositiveGrading d (G.submodule U hU).piece := by
  rw [funext (G.submodule_piece U hU)]
  exact IsPositiveGrading.comap (U.subtype.restrictScalars R) Subtype.val_injective

/-- At every cutoff a homogeneous submodule inherits the restricted degree filtration. -/
theorem PositiveDegrees.degreeSubmodule_submodule (d : PositiveDegrees ι) (k : ℕ) :
    d.degreeSubmodule (G.submodule U hU).piece k =
      (d.degreeSubmodule G.piece k).comap (U.subtype.restrictScalars R) := by
  ext x
  change x ∈ d.degreeSubmodule (G.submodule U hU).piece k ↔
    (x : M) ∈ d.degreeSubmodule G.piece k
  rw [d.mem_degreeSubmodule_iff, d.mem_degreeSubmodule_iff]
  simp only [← G.coe_decompose_submodule U hU]
  exact ⟨fun h i hi => congrArg Subtype.val (h i hi),
    fun h i hi => Subtype.val_injective (h i hi)⟩

end Submodule

section Quotient

variable {ι R S M : Type*} [AddCommMonoid ι] [DecidableEq ι] [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {d : PositiveDegrees ι} (G : InternalGrading R M ι) (U : Submodule S M)
  (hU : DirectSum.SetLike.IsHomogeneous G.piece U)

/-- The inherited grading of a homogeneous quotient is positive. -/
instance IsPositiveGrading.quotient [IsPositiveGrading d G.piece] :
    IsPositiveGrading d (G.quotient U hU).piece := by
  rw [funext (G.quotient_piece U hU)]
  exact IsPositiveGrading.map (U.mkQ.restrictScalars R)

/-- At every cutoff the degree filtration of a homogeneous quotient is the image of the
ambient filtration. -/
theorem PositiveDegrees.degreeSubmodule_quotient (d : PositiveDegrees ι) (k : ℕ) :
    d.degreeSubmodule (G.quotient U hU).piece k =
      (d.degreeSubmodule G.piece k).map (U.mkQ.restrictScalars R) := by
  rw [funext (G.quotient_piece U hU), d.degreeSubmodule_map]

end Quotient
end TauCeti
