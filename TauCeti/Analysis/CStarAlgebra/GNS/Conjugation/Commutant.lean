/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Conjugation.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
public import TauCeti.Analysis.InnerProductSpace.ConjOperator

/-!
# Conjugating the GNS von Neumann algebra by the modular conjugation

Let `f` be a tracial positive functional on a possibly nonunital C⋆-algebra `A`, with GNS
representation `π`, right representation `πᵒᵖ`, `πᵒᵖ(bᵒᵖ)[c] = [c b]`, and modular conjugation
`J`, `J [a] = [a⋆]`. Since `J` is conjugate linear, `x ↦ J x J` maps complex linear operators of
the GNS space to complex linear operators; it is a conjugate-linear isometric equivalence of the
operator algebra, `PositiveLinearMap.gnsConjOperator`, the case of `J` of the general conjugation
`LinearIsometryEquiv.conjOperator`. It is involutive, unital, multiplicative and compatible with
adjoints, and it exchanges the two representations: `J π(b) J = πᵒᵖ(b⋆ᵒᵖ)` and
`J πᵒᵖ(bᵒᵖ) J = π(b⋆)`, so `πᵒᵖ(bᵒᵖ) = J π(b⋆) J`. Consequently `J M_f J ⊆ M_f'` for the GNS von
Neumann algebra `M_f = π(A)''`: for `x ∈ M_f`, the operator `J x J` commutes with `π(a)` because
`x` commutes with `J π(a) J = πᵒᵖ(a⋆ᵒᵖ)`, which lies in `M_f'`. For unital `A`, with GNS vector
`Ω = [1]`, `J` acts on `M_f Ω` by `J x Ω = x⋆ Ω`: the vector functionals `x ↦ ⟪J u, x Ω⟫` and
`x ↦ ⟪Ω, x u⟫` agree on `π(A)` by traciality, hence on `M_f`.

## Main definitions

* `PositiveLinearMap.gnsConjOperator f hf`: the conjugate-linear isometric equivalence
  `x ↦ J x J`.

## Main results

* `PositiveLinearMap.gnsConjOperator_gnsNonUnitalStarAlgHom`: `J π(b) J = πᵒᵖ(b⋆ᵒᵖ)`.
* `PositiveLinearMap.gnsConjOperator_gnsRightNonUnitalStarAlgHom`: `J πᵒᵖ(bᵒᵖ) J = π(b⋆)`.
* `PositiveLinearMap.gnsRightNonUnitalStarAlgHom_eq_gnsConjOperator`: `πᵒᵖ(bᵒᵖ) = J π(b⋆) J`.
* `PositiveLinearMap.gnsConjOperator_mem_commutant`: `J M_f J ⊆ M_f'`.
* `PositiveLinearMap.gnsConj_apply_apply_gnsVector_of_mem`: `J x Ω = x⋆ Ω` for `x ∈ M_f`.

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

/-- The conjugation `x ↦ J x J` of operators of the GNS space of a tracial functional by the
modular conjugation `J`, the general conjugation `LinearIsometryEquiv.conjOperator` of operators by
a conjugate-linear isometric equivalence; each `J x J` is complex linear, `J` being conjugate
linear. -/
noncomputable def gnsConjOperator :
    (f.GNS →L[ℂ] f.GNS) ≃ₗᵢ⋆[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  (gnsConj f hf).conjOperator

/-- The operator `J x J` acts by `y ↦ J (x (J y))`. -/
@[simp]
theorem gnsConjOperator_apply (x : f.GNS →L[ℂ] f.GNS) (y : f.GNS) :
    gnsConjOperator f hf x y = gnsConj f hf (x (gnsConj f hf y)) := by
  simp [gnsConjOperator, gnsConj_symm]

/-- Conjugation by `J` is its own inverse. -/
@[simp]
theorem gnsConjOperator_symm : (gnsConjOperator f hf).symm = gnsConjOperator f hf := by
  rw [gnsConjOperator, LinearIsometryEquiv.conjOperator_symm, gnsConj_symm]

/-- Conjugation by `J` is an involution. -/
@[simp]
theorem gnsConjOperator_gnsConjOperator (x : f.GNS →L[ℂ] f.GNS) :
    gnsConjOperator f hf (gnsConjOperator f hf x) = x := by
  simpa only [gnsConjOperator_symm] using (gnsConjOperator f hf).symm_apply_apply x

/-- Conjugation by `J` fixes the identity operator. -/
@[simp]
theorem gnsConjOperator_one : gnsConjOperator f hf 1 = 1 :=
  (gnsConj f hf).conjOperator_one

/-- Conjugation by `J` is multiplicative. -/
@[simp]
theorem gnsConjOperator_mul (x y : f.GNS →L[ℂ] f.GNS) :
    gnsConjOperator f hf (x * y) = gnsConjOperator f hf x * gnsConjOperator f hf y :=
  (gnsConj f hf).conjOperator_mul x y

/-- Conjugation by `J` commutes with adjoints: `J x⋆ J = (J x J)⋆`. -/
@[simp]
theorem gnsConjOperator_star (x : f.GNS →L[ℂ] f.GNS) :
    gnsConjOperator f hf (star x) = star (gnsConjOperator f hf x) :=
  (gnsConj f hf).conjOperator_star x

/-- Conjugating the GNS representation by the modular conjugation gives the right
representation: `J π(b) J = πᵒᵖ(b⋆ᵒᵖ)`. -/
@[simp]
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
@[simp]
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
  exact (f.mem_gnsVonNeumannAlgebra_commutant_iff).2 key

section Unital

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (g : B →ₚ[ℂ] ℂ) (hg : ∀ a b, g (a * b) = g (b * a))

/-- **`J x Ω = x⋆ Ω` on the GNS von Neumann algebra.** For a tracial positive functional on a
unital C⋆-algebra and `x ∈ M_g`, the modular conjugation sends `x Ω` to `x⋆ Ω`. -/
theorem gnsConj_apply_apply_gnsVector_of_mem {x : g.GNS →L[ℂ] g.GNS}
    (hx : x ∈ g.gnsVonNeumannAlgebra) :
    gnsConj g hg (x g.gnsVector) = star x g.gnsVector := by
  -- The vector functionals `x ↦ ⟪J u, x Ω⟫` and `x ↦ ⟪Ω, x u⟫` agree on `π(B)`, by traciality
  -- on classes `u = [b]` and by continuity in `u`, hence on `M_g`.
  have hπ (u : g.GNS) (c : B) : inner ℂ (gnsConj g hg u) (g.gnsNonUnitalStarAlgHom c g.gnsVector) =
      inner ℂ g.gnsVector (g.gnsNonUnitalStarAlgHom c u) := by
    induction u using UniformSpace.Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih u =>
      rw [← g.toPreGNS_ofPreGNS u]
      generalize g.ofPreGNS u = b
      simp only [gnsConj_apply_coe, gnsNonUnitalStarAlgHom_apply_gnsVector,
        gnsNonUnitalStarAlgHom_apply_coe, leftMulMapPreGNS_apply, inner_gnsVector_coe,
        UniformSpace.Completion.inner_coe, preGNS_inner_def, ofPreGNS_toPreGNS, star_star]
      -- traciality: `g (b c) = g (c b)`
      exact hg b c
  refine ext_inner_left ℂ fun u ↦ ?_
  have h := g.inner_apply_eq_of_mem_gnsVonNeumannAlgebra (u₁ := gnsConj g hg u)
    (v₁ := g.gnsVector) (u₂ := g.gnsVector) (v₂ := u) (hπ u) hx
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  calc inner ℂ u (gnsConj g hg (x g.gnsVector))
      = inner ℂ (gnsConj g hg (gnsConj g hg u)) (gnsConj g hg (x g.gnsVector)) := by
        rw [gnsConj_gnsConj]
    _ = starRingEnd ℂ (inner ℂ (gnsConj g hg u) (x g.gnsVector)) := by
        rw [inner_gnsConj_gnsConj, inner_conj_symm]
    _ = inner ℂ (x u) g.gnsVector := by rw [h, inner_conj_symm]

end Unital

end PositiveLinearMap
