/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Bilinear
public import TauCeti.Algebra.Star.TensorProductLift
public import TauCeti.Analysis.CStarAlgebra.GNS.RightRepresentation

/-!
# The product representation of a tracial functional

Let `f` be a tracial positive functional on a possibly nonunital C⋆-algebra `A`, with GNS
representation `π_f` and right representation `π_fᵒᵖ` of `Aᵐᵒᵖ` on the GNS space `L²(A, f)`
(`TauCeti.Analysis.CStarAlgebra.GNS.RightRepresentation`). The two representations commute, so
they combine to the star homomorphism `PositiveLinearMap.gnsProductNonUnitalStarAlgHom` of the
algebraic tensor product `A ⊗ Aᵐᵒᵖ`, `a ⊗ bᵒᵖ ↦ π_f(a) π_fᵒᵖ(bᵒᵖ)`, which acts on classes by
`[c] ↦ [a c b]`.

The *tensor functional* `PositiveLinearMap.gnsTensorFunctional` is the linear functional
`μ_f(a ⊗ bᵒᵖ) = f (a b)` on `A ⊗ Aᵐᵒᵖ`, that is `f` composed with the multiplication map
`TauCeti.LinearMap.mulUnop' : A ⊗ Aᵐᵒᵖ → A` (`TauCeti.Algebra.Algebra.Bilinear`,
`PositiveLinearMap.gnsTensorFunctional_apply`). It is defined for every positive functional. For
tracial `f`, `μ_f(s⋆ t) = f ((m s)⋆ (m t))` with `m` the multiplication map
(`PositiveLinearMap.gnsTensorFunctional_star_mul`), so `μ_f` is positive
(`PositiveLinearMap.gnsTensorFunctional_star_mul_self_nonneg`).

For unital `A`, the product representation is unital, `PositiveLinearMap.gnsProductStarAlgHom`,
and `μ_f` is its vector functional at the GNS vector `Ω = [1]`,
`μ_f(t) = ⟪Ω, (π_f × π_fᵒᵖ)(t) Ω⟫` (`PositiveLinearMap.gnsTensorFunctional_eq_inner`). Hence
`μ_f(1) = f 1` and `μ_f(t⋆ t) = ‖(π_f × π_fᵒᵖ)(t) Ω‖ ^ 2`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), §3.1, for the tensor functional `a ⊗ bᵒᵖ ↦ τ(a b)` of a tracial state.
-/

public section

open scoped InnerProductSpace ComplexOrder TensorProduct
open MulOpposite

namespace PositiveLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : A →ₚ[ℂ] ℂ)

/-- **The product representation** of a tracial positive functional: the star homomorphism
`π_f × π_fᵒᵖ : A ⊗ Aᵐᵒᵖ → B(L²(A, f))`, `a ⊗ bᵒᵖ ↦ π_f(a) π_fᵒᵖ(bᵒᵖ)`, on the algebraic tensor
product. -/
noncomputable def gnsProductNonUnitalStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    A ⊗[ℂ] Aᵐᵒᵖ →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom f.gnsNonUnitalStarAlgHom
    (f.gnsRightNonUnitalStarAlgHom hf)
    (f.commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom hf)

@[simp]
theorem gnsProductNonUnitalStarAlgHom_tmul (hf : ∀ a b, f (a * b) = f (b * a)) (a : A)
    (b : Aᵐᵒᵖ) :
    f.gnsProductNonUnitalStarAlgHom hf (a ⊗ₜ b) =
      f.gnsNonUnitalStarAlgHom a * f.gnsRightNonUnitalStarAlgHom hf b :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom_tmul _ a b

/-- The product representation acts on classes by two-sided multiplication:
`(π_f × π_fᵒᵖ)(a ⊗ bᵒᵖ)[c] = [a c b]`. -/
theorem gnsProductNonUnitalStarAlgHom_tmul_apply_toGNS (hf : ∀ a b, f (a * b) = f (b * a))
    (a b c : A) :
    f.gnsProductNonUnitalStarAlgHom hf (a ⊗ₜ op b) (f.toGNS c) = f.toGNS (a * c * b) := by
  simp [mul_assoc]

/-- **The tensor functional** `μ_f` of a positive functional `f`: the linear functional on
`A ⊗ Aᵐᵒᵖ` with `μ_f(a ⊗ bᵒᵖ) = f (a b)`, that is, `f` composed with multiplication
`A ⊗ Aᵐᵒᵖ → A`. -/
noncomputable def gnsTensorFunctional : A ⊗[ℂ] Aᵐᵒᵖ →ₗ[ℂ] ℂ :=
  (f : A →ₗ[ℂ] ℂ) ∘ₗ TauCeti.LinearMap.mulUnop' ℂ A

omit [StarOrderedRing A] in
/-- The tensor functional is `f` composed with the multiplication map:
`μ_f(t) = f (m t)` for every tensor `t`. -/
theorem gnsTensorFunctional_apply (t : A ⊗[ℂ] Aᵐᵒᵖ) :
    f.gnsTensorFunctional t = f (TauCeti.LinearMap.mulUnop' ℂ A t) :=
  (rfl)

omit [StarOrderedRing A] in
/-- The tensor functional on elementary tensors: `μ_f(a ⊗ bᵒᵖ) = f (a b)`. -/
@[simp]
theorem gnsTensorFunctional_tmul (a : A) (b : Aᵐᵒᵖ) :
    f.gnsTensorFunctional (a ⊗ₜ b) = f (a * b.unop) := by
  rw [gnsTensorFunctional_apply, TauCeti.LinearMap.mulUnop'_tmul]

omit [StarOrderedRing A] in
/-- For tracial `f`, the tensor functional at `s⋆ t` is `f` at `(m s)⋆ (m t)`, for `m` the
multiplication map `A ⊗ Aᵐᵒᵖ → A`. -/
theorem gnsTensorFunctional_star_mul (hf : ∀ a b, f (a * b) = f (b * a))
    (s t : A ⊗[ℂ] Aᵐᵒᵖ) :
    f.gnsTensorFunctional (star s * t) =
      f (star (TauCeti.LinearMap.mulUnop' ℂ A s) * TauCeti.LinearMap.mulUnop' ℂ A t) := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' => simp [star_add, add_mul, hs, hs']
  | tmul a b =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [mul_add, map_add, ht, ht']
    | tmul a' b' => simpa [mul_assoc] using hf (star a * a' * b'.unop) (star b.unop)

/-- For tracial `f`, the tensor functional is positive: `0 ≤ μ_f(t⋆ t)`. -/
theorem gnsTensorFunctional_star_mul_self_nonneg (hf : ∀ a b, f (a * b) = f (b * a))
    (t : A ⊗[ℂ] Aᵐᵒᵖ) : 0 ≤ f.gnsTensorFunctional (star t * t) := by
  rw [f.gnsTensorFunctional_star_mul hf]
  exact f.map_nonneg (star_mul_self_nonneg _)

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

/-- The product representation of a tracial functional on a unital C⋆-algebra is unital. -/
@[simp]
theorem gnsProductNonUnitalStarAlgHom_one (hf : ∀ a b, f (a * b) = f (b * a)) :
    f.gnsProductNonUnitalStarAlgHom hf 1 = 1 :=
  f.gns_continuousLinearMap_ext fun c ↦ by simp [Algebra.TensorProduct.one_def]

/-- **The unital product representation** of a tracial positive functional on a unital
C⋆-algebra: `π_f × π_fᵒᵖ` as a unital star homomorphism `A ⊗ Aᵐᵒᵖ → B(L²(A, f))`. -/
noncomputable def gnsProductStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    A ⊗[ℂ] Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  { f.gnsProductNonUnitalStarAlgHom hf with
    map_one' := f.gnsProductNonUnitalStarAlgHom_one hf
    commutes' r := by simp [Algebra.algebraMap_eq_smul_one] }

@[simp]
theorem coe_gnsProductStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    ⇑(f.gnsProductStarAlgHom hf) = f.gnsProductNonUnitalStarAlgHom hf :=
  (rfl)

/-- The unital product representation has underlying non-unital star homomorphism
`gnsProductNonUnitalStarAlgHom`. -/
@[simp]
theorem toNonUnitalStarAlgHom_gnsProductStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    (f.gnsProductStarAlgHom hf).toNonUnitalStarAlgHom =
      f.gnsProductNonUnitalStarAlgHom hf :=
  (rfl)

/-- For tracial `f`, the tensor functional is the vector functional of the product representation
at the GNS vector: `μ_f(t) = ⟪Ω, (π_f × π_fᵒᵖ)(t) Ω⟫`. -/
theorem gnsTensorFunctional_eq_inner (hf : ∀ a b, f (a * b) = f (b * a)) (t : A ⊗[ℂ] Aᵐᵒᵖ) :
    f.gnsTensorFunctional t =
      ⟪f.gnsVector, f.gnsProductNonUnitalStarAlgHom hf t f.gnsVector⟫_ℂ := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp [ht, ht', inner_add_right]
  | tmul a b => simp

omit [StarOrderedRing A] in
/-- The tensor functional takes the value `f 1` at the unit, so it is normalized for a
state. -/
@[simp]
theorem gnsTensorFunctional_one : f.gnsTensorFunctional 1 = f 1 := by
  simp [Algebra.TensorProduct.one_def]

/-- For tracial `f`, the tensor functional at `t⋆ t` is the squared norm of
`(π_f × π_fᵒᵖ)(t) Ω`. -/
theorem gnsTensorFunctional_star_mul_self (hf : ∀ a b, f (a * b) = f (b * a))
    (t : A ⊗[ℂ] Aᵐᵒᵖ) :
    f.gnsTensorFunctional (star t * t) =
      (‖f.gnsProductNonUnitalStarAlgHom hf t f.gnsVector‖ ^ 2 : ℝ) := by
  simp [f.gnsTensorFunctional_eq_inner hf, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]

end Unital

end PositiveLinearMap
