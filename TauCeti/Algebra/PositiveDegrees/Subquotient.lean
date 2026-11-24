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
@[simp]
theorem PositiveDegrees.degreeSubmodule_submodule (d : PositiveDegrees ι) (k : ℕ) :
    d.degreeSubmodule (G.submodule U hU).piece k =
      (d.degreeSubmodule G.piece k).comap (U.subtype.restrictScalars R) := by
  simp only [degreeSubmodule_eq_degreeTail]
  exact (LinearMap.comap_degreeTail_eq_of_injective (U.subtype.restrictScalars R)
    (G.submodule U hU).piece G.piece Subtype.val_injective (fun _ _ hx => by
      simpa only [LinearMap.restrictScalars_apply, Submodule.subtype_apply] using
        (G.mem_submodule_piece U hU).mp hx) d.degree (k + 1)).symm

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
@[simp]
theorem PositiveDegrees.degreeSubmodule_quotient (d : PositiveDegrees ι) (k : ℕ) :
    d.degreeSubmodule (G.quotient U hU).piece k =
      (d.degreeSubmodule G.piece k).map (U.mkQ.restrictScalars R) := by
  rw [funext (G.quotient_piece U hU), d.degreeSubmodule_map]

end Quotient
end TauCeti
