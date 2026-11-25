/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Conjugation
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra

/-!
# Conjugating the GNS von Neumann algebra by the modular conjugation

Let `f` be a tracial positive functional on a possibly nonunital C⋆-algebra `A`, with GNS
representation `π`, right representation `πᵒᵖ`, `πᵒᵖ(bᵒᵖ)[c] = [c b]`, and modular conjugation
`J`, `J [a] = [a⋆]`. Since `J` is conjugate linear, `x ↦ J x J` is a map of complex linear
operators of the GNS space, `PositiveLinearMap.gnsConjOperator`. It is multiplicative and
involutive, and it exchanges the two representations: `J π(b) J = πᵒᵖ(b⋆ᵒᵖ)` and
`J πᵒᵖ(bᵒᵖ) J = π(b⋆)`, so `πᵒᵖ(bᵒᵖ) = J π(b⋆) J`. Consequently `J M_f J ⊆ M_f'` for the GNS von
Neumann algebra `M_f = π(A)''`: for `x ∈ M_f`, the operator `J x J` commutes with `π(a)` because
`x` commutes with `J π(a) J = πᵒᵖ(a⋆ᵒᵖ)`, which lies in `M_f'`.

## Main definitions

* `PositiveLinearMap.gnsConjOperator f hf x`: the operator `J x J`.

## Main results

* `PositiveLinearMap.gnsConjOperator_gnsNonUnitalStarAlgHom`: `J π(b) J = πᵒᵖ(b⋆ᵒᵖ)`.
* `PositiveLinearMap.gnsConjOperator_gnsRightNonUnitalStarAlgHom`: `J πᵒᵖ(bᵒᵖ) J = π(b⋆)`.
* `PositiveLinearMap.gnsRightNonUnitalStarAlgHom_eq_gnsConjOperator`: `πᵒᵖ(bᵒᵖ) = J π(b⋆) J`.
* `PositiveLinearMap.gnsConjOperator_mem_commutant`: `J M_f J ⊆ M_f'`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), Chapter 2, for the GNS representation of a tracial state.
-/

public section

open MulOpposite
open scoped ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : A →ₚ[ℂ] ℂ) (hf : ∀ a b, f (a * b) = f (b * a))

/-- The operator `J x J` obtained by conjugating an operator `x` of the GNS space of a tracial
functional by the modular conjugation `J`. It is complex linear, `J` being conjugate linear. -/
noncomputable def gnsConjOperator (x : f.GNS →L[ℂ] f.GNS) : f.GNS →L[ℂ] f.GNS :=
  ((gnsConj f hf).toContinuousLinearEquiv : f.GNS →SL[starRingEnd ℂ] f.GNS).comp
    (x.comp ((gnsConj f hf).toContinuousLinearEquiv : f.GNS →SL[starRingEnd ℂ] f.GNS))

@[simp]
theorem gnsConjOperator_apply (x : f.GNS →L[ℂ] f.GNS) (y : f.GNS) :
    gnsConjOperator f hf x y = gnsConj f hf (x (gnsConj f hf y)) :=
  (rfl)

/-- Conjugation by `J` is an involution. -/
@[simp]
theorem gnsConjOperator_gnsConjOperator (x : f.GNS →L[ℂ] f.GNS) :
    gnsConjOperator f hf (gnsConjOperator f hf x) = x := by
  ext y
  simp

/-- Conjugation by `J` is multiplicative. -/
theorem gnsConjOperator_mul (x y : f.GNS →L[ℂ] f.GNS) :
    gnsConjOperator f hf (x * y) = gnsConjOperator f hf x * gnsConjOperator f hf y := by
  ext z
  simp

/-- Conjugating the GNS representation by the modular conjugation gives the right
representation: `J π(b) J = πᵒᵖ(b⋆ᵒᵖ)`. -/
theorem gnsConjOperator_gnsNonUnitalStarAlgHom (b : A) :
    gnsConjOperator f hf (f.gnsNonUnitalStarAlgHom b) =
      f.gnsRightNonUnitalStarAlgHom hf (op (star b)) := by
  refine f.gns_continuousLinearMap_ext fun c ↦ ?_
  have h := gnsConj_gnsNonUnitalStarAlgHom_gnsConj_toGNS f hf b (f.ofPreGNS c)
  simp only [toGNS_apply, toPreGNS_ofPreGNS] at h
  rw [gnsConjOperator_apply, h, gnsRightNonUnitalStarAlgHom_apply_coe, unop_op,
    rightMulMapPreGNS_apply]

/-- Conjugating the right representation by the modular conjugation gives the GNS
representation: `J πᵒᵖ(bᵒᵖ) J = π(b⋆)`. -/
theorem gnsConjOperator_gnsRightNonUnitalStarAlgHom (b : Aᵐᵒᵖ) :
    gnsConjOperator f hf (f.gnsRightNonUnitalStarAlgHom hf b) =
      f.gnsNonUnitalStarAlgHom (star b.unop) := by
  rw [← gnsConjOperator_gnsConjOperator f hf (f.gnsNonUnitalStarAlgHom (star b.unop)),
    gnsConjOperator_gnsNonUnitalStarAlgHom, star_star, op_unop]

/-- The right representation is the conjugate of the GNS representation by the modular
conjugation: `πᵒᵖ(bᵒᵖ) = J π(b⋆) J`. -/
theorem gnsRightNonUnitalStarAlgHom_eq_gnsConjOperator (b : A) :
    f.gnsRightNonUnitalStarAlgHom hf (op b) =
      gnsConjOperator f hf (f.gnsNonUnitalStarAlgHom (star b)) := by
  rw [gnsConjOperator_gnsNonUnitalStarAlgHom, star_star]

/-- **`J M_f J ⊆ M_f'`.** Conjugating an element of the GNS von Neumann algebra `M_f = π(A)''` of a
tracial functional by the modular conjugation gives an element of its commutant. -/
theorem gnsConjOperator_mem_commutant {x : f.GNS →L[ℂ] f.GNS}
    (hx : x ∈ f.gnsVonNeumannAlgebra) :
    gnsConjOperator f hf x ∈ f.gnsVonNeumannAlgebra.commutant := by
  -- `x` commutes with `J π(a) J = πᵒᵖ(a⋆ᵒᵖ)`, which lies in the commutant of `M_f`.
  have key (a : A) : f.gnsNonUnitalStarAlgHom a * gnsConjOperator f hf x =
      gnsConjOperator f hf x * f.gnsNonUnitalStarAlgHom a := by
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp
      (f.gnsRightNonUnitalStarAlgHom_mem_commutant hf (op (star a))) x hx
    rw [← gnsConjOperator_gnsNonUnitalStarAlgHom] at hc
    have := congrArg (gnsConjOperator f hf) hc
    rw [gnsConjOperator_mul, gnsConjOperator_mul, gnsConjOperator_gnsConjOperator] at this
    exact this.symm
  rw [← SetLike.mem_coe, gnsVonNeumannAlgebra_def, VonNeumannAlgebra.coe_commutant_adjoin]
  rintro y (⟨a, rfl⟩ | ⟨a, ha⟩)
  · exact key a
  · rw [← star_star y, ← ha, ← map_star]
    exact key _

end PositiveLinearMap
