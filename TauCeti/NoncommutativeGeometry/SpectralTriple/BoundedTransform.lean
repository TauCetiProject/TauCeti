/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.BoundedTransform
public import TauCeti.NoncommutativeGeometry.FredholmModule.Basic
public import TauCeti.NoncommutativeGeometry.SpectralTriple.Basic
import TauCeti.Algebra.Ring.Commute

/-!
# The bounded transform of a spectral triple

Every spectral triple `(A, H, D)` determines a bounded self-adjoint contraction
`F_D = D (1 + D²)⁻¹/²` (`SpectralTriple.boundedTransform`) with `1 - F_D² = (1 + D²)⁻¹` compact
and `[F_D, π(a)]` compact with `‖[F_D, π(a)]‖ ≤ (5 / 4) ‖[D, π(a)]‖`, yielding a Fredholm
module `SpectralTriple.toFredholmModule` (and an even Fredholm module
`EvenSpectralTriple.toEvenFredholmModule`), equivariantly under unitary transport.

## Main definitions

* `TauCeti.SpectralTriple.boundedTransform`: the bounded transform `F_D = D (1 + D²)⁻¹/²`.
* `TauCeti.SpectralTriple.toFredholmModule`: the Fredholm module `(H, π, F_D)`.
* `TauCeti.EvenSpectralTriple.toEvenFredholmModule`: the even Fredholm module `(H, π, F_D, γ)`.

## References

* S. Baaj and P. Julg, *C. R. Acad. Sci. Paris Sér. I Math.* 296 (1983), 875–878.
* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §2.
-/

public section

noncomputable section

open scoped ComplexStarModule

namespace TauCeti

variable {A : Type*} [Semiring A] [Algebra ℂ A] [Star A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Bounded transform of an odd spectral triple -/

namespace SpectralTriple

variable (S : SpectralTriple A H)

/-- The **bounded transform** (or Woronowicz–Baaj–Julg transform) `F_D = D (1 + D²)⁻¹/²` of the
Dirac operator of a spectral triple. -/
abbrev boundedTransform : H →L[ℂ] H :=
  S.operator.boundedTransform S.isSelfAdjoint_operator S.hasCompactResolvent_operator

/-- **Baaj–Julg compactness theorem for spectral triples.** For every `a : A`, the commutator
`[F_D, π(a)]` is a compact operator. -/
theorem isCompactOperator_commutator_boundedTransform (a : A) :
    IsCompactOperator ⇑(S.boundedTransform * S.rep a - S.rep a * S.boundedTransform) :=
  S.operator.isCompactOperator_commutator_boundedTransform S.isSelfAdjoint_operator
    S.hasCompactResolvent_operator (S.sylvesterEquation_commutator a)

/-- **Baaj–Julg norm estimate for spectral triples.** For every `a : A`,
`‖[F_D, π(a)]‖ ≤ (5 / 4) ‖[D, π(a)]‖`. -/
theorem norm_commutator_boundedTransform_le (a : A) :
    ‖S.boundedTransform * S.rep a - S.rep a * S.boundedTransform‖ ≤ 5 / 4 * ‖S.commutator a‖ :=
  S.operator.norm_commutator_boundedTransform_le S.isSelfAdjoint_operator
    S.hasCompactResolvent_operator (S.sylvesterEquation_commutator a)

/-- Unitary transport commutes with the bounded transform. -/
@[simp]
theorem boundedTransform_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') :
    (S.conj U).boundedTransform = U.conjStarAlgEquiv S.boundedTransform := by
  simp only [boundedTransform, conj_operator]
  exact S.operator.boundedTransform_conj S.isSelfAdjoint_operator
    S.hasCompactResolvent_operator U

/-- Algebra pullback preserves the bounded transform. -/
@[simp]
theorem boundedTransform_comap {B : Type*} [Semiring B] [Algebra ℂ B] [Star B]
    (φ : B →⋆ₐ[ℂ] A) :
    (S.comap φ).boundedTransform = S.boundedTransform := by
  simp only [boundedTransform, comap_operator]

/-! ### Conversion to a Fredholm module -/

/-- **Baaj–Julg Fredholm module.** The bounded Fredholm module `(H, π, F_D)` associated to a
spectral triple `(A, H, D)` via its bounded transform `F_D = D (1 + D²)⁻¹/²`. -/
def toFredholmModule : FredholmModule A H where
  rep := S.rep.toNonUnitalStarAlgHom
  operator := S.boundedTransform
  isSelfAdjoint_operator := S.operator.isSelfAdjoint_boundedTransform
    S.isSelfAdjoint_operator S.hasCompactResolvent_operator
  isCompactOperator_commutator := S.isCompactOperator_commutator_boundedTransform
  isCompactOperator_mul_self_sub_one_mul a :=
    (S.operator.isCompactOperator_boundedTransform_mul_self_sub_one S.isSelfAdjoint_operator
      S.hasCompactResolvent_operator).mul_right (S.rep a)

@[simp]
theorem toFredholmModule_rep : S.toFredholmModule.rep = S.rep.toNonUnitalStarAlgHom :=
  (rfl)

theorem toFredholmModule_rep_apply (a : A) : S.toFredholmModule.rep a = S.rep a :=
  (rfl)

@[simp]
theorem toFredholmModule_operator : S.toFredholmModule.operator = S.boundedTransform :=
  (rfl)

/-- Unitary equivalence of spectral triples induces unitary equivalence of their bounded-transform
Fredholm modules. -/
@[simp]
theorem toFredholmModule_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') :
    (S.conj U).toFredholmModule = S.toFredholmModule.conj U := by
  ext1 <;> (ext1 a; simp)

end SpectralTriple

/-! ### Even spectral triples and even Fredholm modules -/

namespace EvenSpectralTriple

variable (S : EvenSpectralTriple A H)

/-- The grading of an even spectral triple anticommutes with its bounded transform `F_D`. -/
theorem grading_mul_boundedTransform :
    S.grading * S.boundedTransform = -(S.boundedTransform * S.grading) :=
  S.operator.mul_boundedTransform_of_anticommute S.isSelfAdjoint_operator
    S.hasCompactResolvent_operator (fun _ hx ↦ S.grading_mem_domain hx) S.grading_apply_operator

/-- The grading of an even spectral triple commutes with `(1 + D²)⁻¹`. -/
theorem commute_grading_invOneAddSq : Commute S.grading S.operator.invOneAddSq := by
  rw [← S.operator.one_sub_boundedTransform_mul_self S.isSelfAdjoint_operator
    S.hasCompactResolvent_operator]
  have h : S.boundedTransform * S.grading = -(S.grading * S.boundedTransform) := by
    rw [S.grading_mul_boundedTransform, neg_neg]
  exact (Commute.one_right _).sub_right (TauCeti.commute_mul_of_mul_eq_neg_mul h h).symm

/-- **Baaj–Julg even Fredholm module.** The even Fredholm module `(H, π, F_D, γ)` associated to an
even spectral triple `(A, H, D, γ)`. -/
def toEvenFredholmModule : EvenFredholmModule A H where
  toFredholmModule := S.toSpectralTriple.toFredholmModule
  grading := S.grading
  isSelfAdjoint_grading := S.isSelfAdjoint_grading
  grading_mul_grading := S.grading_mul_grading
  commute_grading_rep := S.commute_grading_rep
  grading_mul_operator := S.grading_mul_boundedTransform

@[simp]
theorem toEvenFredholmModule_toFredholmModule :
    S.toEvenFredholmModule.toFredholmModule = S.toSpectralTriple.toFredholmModule :=
  (rfl)

@[simp]
theorem toEvenFredholmModule_grading : S.toEvenFredholmModule.grading = S.grading :=
  (rfl)

/-- Unitary equivalence of even spectral triples induces unitary equivalence of their
bounded-transform even Fredholm modules. -/
@[simp]
theorem toEvenFredholmModule_conj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') :
    (S.conj U).toEvenFredholmModule = S.toEvenFredholmModule.conj U := by
  ext1 <;> (ext1 a; simp)

end EvenSpectralTriple

end TauCeti
