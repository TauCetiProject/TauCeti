/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.LowerCentralSeries
public import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# The closed lower central series of the free pro-`p` group on two generators

Let `F = freeProP p (Fin 2)` be the free pro-`p` group on two generators `x_0`, `x_1`, and let
`gr_n(F)` be the graded pieces of its closed lower central series, which are `ℤ_p`-modules. By the
degree-zero and degree-one bases of a free pro-`p` group, `gr_0(F)` is free over `ℤ_p` on the
classes `e_0`, `e_1` of `x_0`, `x_1` (so `gr_0(F) ≃ ℤ_p²` by
`(freeProP.lcsDegreeZeroBasis p (Fin 2)).equivFun`), and `gr_1(F)` is free over `ℤ_p` on the
brackets `[e_i, e_j]` with `i < j`. In rank two there is exactly one such pair, so
`gr_1(F) = ℤ_p [e_0, e_1]` is free of rank one. This file makes the
rank-one statement explicit and computes the bracket and the functoriality in these coordinates:

* the bracket `gr_0(F) × gr_0(F) → gr_1(F)` is the determinant: `[a, b]` is
  `det (a, b) • [e_0, e_1]`, where `det (a, b)` is the determinant of the coordinates of `a` and
  `b` in the basis `e_0, e_1`;
* a continuous endomorphism of `F` acts on `gr_1(F)` by multiplication by the determinant of its
  action on `gr_0(F)`.

The first transports the determinant formula `a ∧ b = det (a, b) • (e_0 ∧ e_1)` in the top
exterior power along the identification `⋀²gr_0(F) ≃ gr_1(F)` of the degree-one basis.
The second follows from it because graded maps commute with the bracket and with the `ℤ_p`-action.
Together they say that `gr_1(F)` is the determinant line of `gr_0(F)`, the rank-two case of the
identification of `gr_1(F)` with the exterior square of `gr_0(F)`.

## Main definitions

* `TauCeti.freeProP.padicIntEquivLcsGradedPieceOne`: the isomorphism `ℤ_p ≃ gr_1(F)`,
  `c ↦ c • [e_0, e_1]`.

## Main results

* `TauCeti.freeProP.lcsBracket_eq_det_smul`: `[a, b] = det (a, b) • [e_0, e_1]` in `gr_1(F)`.
* `TauCeti.freeProP.padicIntEquivLcsGradedPieceOne_symm_lcsBracket`: in the coordinate of
  `gr_1(F) ≃ ℤ_p`, the bracket of `a` and `b` is `det (a, b)`.
* `TauCeti.freeProP.gradedMap_one_eq_det_smul`: a continuous endomorphism `f` of `F` acts on
  `gr_1(F)` as multiplication by the determinant of the matrix of `f` on `gr_0(F)`.

## References

* J.-P. Serre, *Lie Algebras and Lie Groups*, Part I, Chapter IV, for the graded Lie ring of the
  lower central series of a free group.
-/

public section

namespace TauCeti

namespace freeProP

variable (p : ℕ) [Fact p.Prime]

/-- **The bracket of the free pro-`p` group of rank two is the determinant.** For classes `a`, `b`
in `gr_0` of the free pro-`p` group on two generators, the bracket `[a, b]` in `gr_1` is the
determinant of the coordinates of `a` and `b` in the basis `e_0, e_1`, times `[e_0, e_1]`. -/
theorem lcsBracket_eq_det_smul (a b : lcsGradedPiece (freeProP p (Fin 2)) 0) :
    lcsBracket (freeProP p (Fin 2)) 0 0 a b =
      (lcsDegreeZeroBasis p (Fin 2)).det ![a, b] •
        lcsBracket (freeProP p (Fin 2)) 0 0 (gradedMkZero 0 _ (of 0))
          (gradedMkZero 0 _ (of 1)) := by
  -- Transport `a ∧ b = det (a, b) • (e_0 ∧ e_1)` along `⋀²gr_0 ≃ gr_1`.
  have h := congrArg (exteriorSquareEquivLcsGradedPieceOne p (Fin 2))
    ((lcsDegreeZeroBasis p (Fin 2)).exteriorPower_ιMulti_eq_det_smul ![a, b])
  simpa [lcsDegreeZeroBasis_apply] using h

/-- **`gr_1` of the free pro-`p` group of rank two is free of rank one** over `ℤ_p`, on the bracket
`[e_0, e_1]`: the isomorphism `ℤ_p ≃ gr_1`, `c ↦ c • [e_0, e_1]`
(`padicIntEquivLcsGradedPieceOne_apply`). -/
noncomputable def padicIntEquivLcsGradedPieceOne :
    ℤ_[p] ≃ₗ[ℤ_[p]] lcsGradedPiece (freeProP p (Fin 2)) 1 :=
  (lcsDegreeZeroBasis p (Fin 2)).exteriorPowerTopEquiv.symm ≪≫ₗ
    exteriorSquareEquivLcsGradedPieceOne p (Fin 2)

@[simp]
theorem padicIntEquivLcsGradedPieceOne_apply (c : ℤ_[p]) :
    padicIntEquivLcsGradedPieceOne p c =
      c • lcsBracket (freeProP p (Fin 2)) 0 0 (gradedMkZero 0 _ (of 0))
        (gradedMkZero 0 _ (of 1)) := by
  simp [padicIntEquivLcsGradedPieceOne, lcsDegreeZeroBasis_apply]

/-- **In the coordinate of `gr_1 ≃ ℤ_p`, the bracket is the determinant**: the coordinate of
`[a, b]` is the determinant of the coordinates of `a` and `b` in the basis `e_0, e_1`. -/
@[simp]
theorem padicIntEquivLcsGradedPieceOne_symm_lcsBracket
    (a b : lcsGradedPiece (freeProP p (Fin 2)) 0) :
    (padicIntEquivLcsGradedPieceOne p).symm (lcsBracket (freeProP p (Fin 2)) 0 0 a b) =
      (lcsDegreeZeroBasis p (Fin 2)).det ![a, b] := by
  rw [LinearEquiv.symm_apply_eq, padicIntEquivLcsGradedPieceOne_apply, lcsBracket_eq_det_smul]

/-- **Continuous endomorphisms act on `gr_1` by the determinant.** A continuous endomorphism `f` of
the free pro-`p` group of rank two acts on `gr_1` as multiplication by the determinant of the
matrix of its action on `gr_0` in the basis `e_0, e_1`. -/
theorem gradedMap_one_eq_det_smul (f : freeProP p (Fin 2) →* freeProP p (Fin 2))
    (hf : Continuous f) (z : lcsGradedPiece (freeProP p (Fin 2)) 1) :
    gradedMap 0 f hf 1 z =
      (lcsDegreeZeroBasis p (Fin 2)).det (gradedMap 0 f hf 0 ∘ lcsDegreeZeroBasis p (Fin 2)) •
        z := by
  have hF := isProP_freeProP p (Fin 2)
  obtain ⟨c, rfl⟩ := (padicIntEquivLcsGradedPieceOne p).surjective z
  have hv : gradedMap 0 f hf 0 ∘ lcsDegreeZeroBasis p (Fin 2) =
      ![gradedMap 0 f hf 0 (gradedMkZero 0 _ (of 0)),
        gradedMap 0 f hf 0 (gradedMkZero 0 _ (of 1))] := by
    ext i
    fin_cases i <;> simp
  rw [padicIntEquivLcsGradedPieceOne_apply, hF.gradedMap_smul hF, gradedMap_gradedBracket_zero_zero,
    lcsBracket_eq_det_smul, hv, smul_comm]

end freeProP

end TauCeti
