/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The right representation of a tracial functional

Let `f` be a tracial positive functional on a possibly nonunital C⋆-algebra `A`, so
`f (a b) = f (b a)`, with GNS space `L²(A, f)`, classes `[a]` and GNS representation `π_f`,
`π_f(a)[c] = [a c]`. Right multiplication `[c] ↦ [c b]` is then bounded by `‖b‖`, because
`f ((c b)⋆ (c b)) = f (c (b b⋆) c⋆) ≤ ‖b‖ ^ 2 f (c c⋆) = ‖b‖ ^ 2 f (c⋆ c)` by traciality, and it
extends to the GNS space. This gives the *right representation*
`PositiveLinearMap.gnsRightNonUnitalStarAlgHom` of the opposite algebra `Aᵐᵒᵖ`,
`π_fᵒᵖ(bᵒᵖ)[c] = [c b]`, a star homomorphism: the adjoint of right multiplication by `b` is
right multiplication by `b⋆` because `f (a⋆ c b) = f (b a⋆ c)`.

The right representation commutes with `π_f`,
`PositiveLinearMap.commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom`, so its range lies
in the commutant `M_f'` of the GNS von Neumann algebra `M_f = π_f(A)''`,
`PositiveLinearMap.gnsRightNonUnitalStarAlgHom_mem_commutant`. The two representations combine
to the star homomorphism `PositiveLinearMap.gnsProductNonUnitalStarAlgHom` of the algebraic
tensor product `A ⊗ Aᵐᵒᵖ`, `a ⊗ bᵒᵖ ↦ π_f(a) π_fᵒᵖ(bᵒᵖ)`.

For unital `A`, the right representation is unital, `PositiveLinearMap.gnsRightStarAlgHom`, and
so is the product representation, `PositiveLinearMap.gnsProductNonUnitalStarAlgHom_one`. The GNS
vector `Ω = [1]` satisfies `π_fᵒᵖ(bᵒᵖ) Ω = [b]`, so it is cyclic for `π_fᵒᵖ(Aᵐᵒᵖ)`,
`PositiveLinearMap.denseRange_gnsRightStarAlgHom_gnsVector`. The vector functional of the
product representation at `Ω` is the tensor functional `μ_f(a ⊗ bᵒᵖ) = f (a b)`,
`PositiveLinearMap.gnsTensorFunctional_tmul`, and it is positive on `A ⊗ Aᵐᵒᵖ`:
`μ_f(t⋆ t) = ‖π(t) Ω‖ ^ 2`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), Chapter 2 and §3.1, for the right representation of a tracial state
  and the tensor functional `a ⊗ bᵒᵖ ↦ τ(a b)`.
-/

public section

open scoped InnerProductSpace ComplexOrder TensorProduct
open MulOpposite UniformSpace

namespace PositiveLinearMap

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : A →ₚ[ℂ] ℂ)

/-- For a tracial positive functional `f`, right multiplication by `b` on the GNS pre-Hilbert
space, `[c] ↦ [c b]`, as a bounded operator of norm at most `‖b‖`. -/
noncomputable def rightMulMapPreGNS (hf : ∀ a b, f (a * b) = f (b * a)) (b : A) :
    f.PreGNS →L[ℂ] f.PreGNS :=
  f.toPreGNS.toLinearMap ∘ₗ LinearMap.mulRight ℂ b ∘ₗ f.ofPreGNS.toLinearMap |>.mkContinuous
    ‖b‖ fun x ↦ by
    rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, ← RCLike.ofReal_le_ofReal (K := ℂ),
      RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, preGNS_norm_sq]
    set c := f.ofPreGNS x
    have hle : c * (b * star b) * star c ≤ ‖b * star b‖ • (c * star c) :=
      CStarAlgebra.star_right_conjugate_le_norm_smul c (b * star b)
    have hcomm : f (star (c * b) * (c * b)) = f (c * (b * star b) * star c) := by
      rw [star_mul, hf]
      simp only [mul_assoc]
    calc (f (star (f.ofPreGNS (f.toPreGNS (c * b))) * f.ofPreGNS (f.toPreGNS (c * b))))
        = f (c * (b * star b) * star c) := by simpa using hcomm
      _ ≤ f (‖b * star b‖ • (c * star c)) := OrderHomClass.mono f hle
      _ = ((‖b‖ ^ 2 : ℝ) : ℂ) * f (star c * c) := by
        rw [CStarRing.norm_self_mul_star, ← sq, ← Complex.coe_smul, map_smul, smul_eq_mul, hf]
      _ = _ := by simp [c, preGNS_norm_sq]

@[simp]
theorem rightMulMapPreGNS_apply (hf : ∀ a b, f (a * b) = f (b * a)) (b : A) (c : f.PreGNS) :
    f.rightMulMapPreGNS hf b c = f.toPreGNS (f.ofPreGNS c * b) :=
  (rfl)

/-- **The right representation** of a tracial positive functional `f`: the star homomorphism
`π_fᵒᵖ : Aᵐᵒᵖ → B(L²(A, f))` with `π_fᵒᵖ(bᵒᵖ)[c] = [c b]`. -/
noncomputable def gnsRightNonUnitalStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    Aᵐᵒᵖ →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  toFun b := (f.rightMulMapPreGNS hf b.unop).completion
  map_smul' m b := by
    ext c
    induction c using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih c => simp [← Completion.coe_smul, mul_smul_comm]
  map_zero' := by
    ext c
    induction c using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih c => simp
  map_add' _ _ := by
    ext c
    induction c using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih c => simp [mul_add, Completion.coe_add]
  map_mul' _ _ := by
    ext c
    induction c using Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih c => simp [mul_assoc]
  map_star' b := by
    refine (ContinuousLinearMap.eq_adjoint_iff (f.rightMulMapPreGNS hf (star b).unop).completion
      (f.rightMulMapPreGNS hf b.unop).completion).mpr ?_
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y =>
      simp only [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe, unop_star,
        rightMulMapPreGNS_apply, preGNS_inner_def, ofPreGNS_toPreGNS, star_mul, star_star]
      rw [mul_assoc, hf, mul_assoc]

theorem gnsRightNonUnitalStarAlgHom_apply (hf : ∀ a b, f (a * b) = f (b * a)) (b : Aᵐᵒᵖ) :
    f.gnsRightNonUnitalStarAlgHom hf b = (f.rightMulMapPreGNS hf b.unop).completion :=
  (rfl)

@[simp]
theorem gnsRightNonUnitalStarAlgHom_apply_coe (hf : ∀ a b, f (a * b) = f (b * a)) (b : Aᵐᵒᵖ)
    (c : f.PreGNS) :
    f.gnsRightNonUnitalStarAlgHom hf b c = f.rightMulMapPreGNS hf b.unop c := by
  simp [gnsRightNonUnitalStarAlgHom_apply]

/-- The right representation acts on classes by right multiplication: `π_fᵒᵖ(bᵒᵖ)[c] = [c b]`. -/
theorem gnsRightNonUnitalStarAlgHom_apply_toGNS (hf : ∀ a b, f (a * b) = f (b * a)) (b c : A) :
    f.gnsRightNonUnitalStarAlgHom hf (op b) (f.toGNS c) = f.toGNS (c * b) := by
  simp

/-- The left and right representations of a tracial functional commute. -/
theorem commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom
    (hf : ∀ a b, f (a * b) = f (b * a)) (a : A) (b : Aᵐᵒᵖ) :
    Commute (f.gnsNonUnitalStarAlgHom a) (f.gnsRightNonUnitalStarAlgHom hf b) := by
  ext c
  induction c using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih c => simp [mul_assoc]

/-- The right representation takes values in the commutant `M_f'` of the GNS von Neumann
algebra. -/
theorem gnsRightNonUnitalStarAlgHom_mem_commutant (hf : ∀ a b, f (a * b) = f (b * a))
    (b : Aᵐᵒᵖ) : f.gnsRightNonUnitalStarAlgHom hf b ∈ f.gnsVonNeumannAlgebra.commutant := by
  rw [← SetLike.mem_coe, gnsVonNeumannAlgebra_def, VonNeumannAlgebra.coe_commutant_adjoin]
  rintro x (⟨a, rfl⟩ | ⟨a, ha⟩)
  · exact (f.commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom hf a b).eq
  · rw [← star_star x, ← ha, ← map_star]
    exact (f.commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom hf _ b).eq

/-- The bilinear map `(a, bᵒᵖ) ↦ π_f(a) π_fᵒᵖ(bᵒᵖ)` underlying the product representation. -/
noncomputable def gnsProductLinearMap (hf : ∀ a b, f (a * b) = f (b * a)) :
    A ⊗[ℂ] Aᵐᵒᵖ →ₗ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  TensorProduct.lift <| (LinearMap.mul ℂ (f.GNS →L[ℂ] f.GNS)).compl₁₂
    (f.gnsNonUnitalStarAlgHom : A →ₗ[ℂ] (f.GNS →L[ℂ] f.GNS))
    (f.gnsRightNonUnitalStarAlgHom hf : Aᵐᵒᵖ →ₗ[ℂ] (f.GNS →L[ℂ] f.GNS))

@[simp]
theorem gnsProductLinearMap_tmul (hf : ∀ a b, f (a * b) = f (b * a)) (a : A) (b : Aᵐᵒᵖ) :
    f.gnsProductLinearMap hf (a ⊗ₜ b) =
      f.gnsNonUnitalStarAlgHom a * f.gnsRightNonUnitalStarAlgHom hf b :=
  (rfl)

/-- **The product representation** of a tracial positive functional: the star homomorphism
`π_f × π_fᵒᵖ : A ⊗ Aᵐᵒᵖ → B(L²(A, f))`, `a ⊗ bᵒᵖ ↦ π_f(a) π_fᵒᵖ(bᵒᵖ)`, on the algebraic tensor
product. -/
noncomputable def gnsProductNonUnitalStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    A ⊗[ℂ] Aᵐᵒᵖ →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  __ := f.gnsProductLinearMap hf
  map_zero' := map_zero _
  map_mul' x y := by
    change f.gnsProductLinearMap hf (x * y) =
      f.gnsProductLinearMap hf x * f.gnsProductLinearMap hf y
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp [add_mul, hx, hx']
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp [mul_add, hy, hy']
      | tmul a' b' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, gnsProductLinearMap_tmul, map_mul]
        simp only [mul_assoc]
        rw [← mul_assoc (f.gnsRightNonUnitalStarAlgHom hf b),
          ← (f.commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom hf a' b).eq, mul_assoc]
  map_star' x := by
    change f.gnsProductLinearMap hf (star x) = star (f.gnsProductLinearMap hf x)
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp_all [star_add]
    | tmul a b =>
      simp only [TensorProduct.star_tmul, gnsProductLinearMap_tmul,
        map_star, star_mul]
      simpa only [map_star] using
        (f.commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom hf (star a) (star b)).eq

@[simp]
theorem gnsProductNonUnitalStarAlgHom_tmul (hf : ∀ a b, f (a * b) = f (b * a)) (a : A)
    (b : Aᵐᵒᵖ) :
    f.gnsProductNonUnitalStarAlgHom hf (a ⊗ₜ b) =
      f.gnsNonUnitalStarAlgHom a * f.gnsRightNonUnitalStarAlgHom hf b :=
  (rfl)

/-- The product representation acts on classes by two-sided multiplication:
`(π_f × π_fᵒᵖ)(a ⊗ bᵒᵖ)[c] = [a c b]`. -/
theorem gnsProductNonUnitalStarAlgHom_tmul_apply_toGNS (hf : ∀ a b, f (a * b) = f (b * a))
    (a b c : A) :
    f.gnsProductNonUnitalStarAlgHom hf (a ⊗ₜ op b) (f.toGNS c) = f.toGNS (a * c * b) := by
  simp [mul_assoc]

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

/-- The right representation of a tracial positive functional on a unital C⋆-algebra, as a
unital star homomorphism `Aᵐᵒᵖ → B(L²(A, f))`. -/
noncomputable def gnsRightStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  { f.gnsRightNonUnitalStarAlgHom hf with
    map_one' := by
      ext c
      induction c using Completion.induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp [gnsRightNonUnitalStarAlgHom_apply_coe]
    commutes' r := by
      ext c
      induction c using Completion.induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp [Algebra.algebraMap_eq_smul_one, ← Completion.coe_smul] }

@[simp]
theorem coe_gnsRightStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    ⇑(f.gnsRightStarAlgHom hf) = f.gnsRightNonUnitalStarAlgHom hf :=
  (rfl)

/-- The right representation maps the GNS vector `Ω = [1]` to the class of the acting element:
`π_fᵒᵖ(bᵒᵖ) Ω = [b]`. -/
@[simp]
theorem gnsRightNonUnitalStarAlgHom_apply_gnsVector (hf : ∀ a b, f (a * b) = f (b * a))
    (b : Aᵐᵒᵖ) :
    f.gnsRightNonUnitalStarAlgHom hf b f.gnsVector = (f.toPreGNS b.unop : f.GNS) := by
  simp [gnsVector_def]

/-- The GNS vector `Ω` is cyclic for the right representation. -/
theorem denseRange_gnsRightStarAlgHom_gnsVector (hf : ∀ a b, f (a * b) = f (b * a)) :
    DenseRange (fun b : Aᵐᵒᵖ => f.gnsRightStarAlgHom hf b f.gnsVector) := by
  refine f.denseRange_toGNS.mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨op a, by simp⟩

/-- The product representation of a tracial functional on a unital C⋆-algebra is unital. -/
@[simp]
theorem gnsProductNonUnitalStarAlgHom_one (hf : ∀ a b, f (a * b) = f (b * a)) :
    f.gnsProductNonUnitalStarAlgHom hf 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, gnsProductNonUnitalStarAlgHom_tmul]
  change f.gnsStarAlgHom 1 * f.gnsRightStarAlgHom hf 1 = 1
  rw [map_one, map_one, one_mul]

/-- The tensor functional `μ_f` of a tracial positive functional on a unital C⋆-algebra: the
vector functional `t ↦ ⟪Ω, (π_f × π_fᵒᵖ)(t) Ω⟫` of the product representation at the GNS
vector, with `μ_f(a ⊗ bᵒᵖ) = f (a b)`. -/
noncomputable def gnsTensorFunctional (hf : ∀ a b, f (a * b) = f (b * a)) :
    A ⊗[ℂ] Aᵐᵒᵖ →ₗ[ℂ] ℂ where
  toFun t := ⟪f.gnsVector, f.gnsProductNonUnitalStarAlgHom hf t f.gnsVector⟫_ℂ
  map_add' _ _ := by simp [inner_add_right]
  map_smul' _ _ := by simp [inner_smul_right]

theorem gnsTensorFunctional_apply (hf : ∀ a b, f (a * b) = f (b * a)) (t : A ⊗[ℂ] Aᵐᵒᵖ) :
    f.gnsTensorFunctional hf t =
      ⟪f.gnsVector, f.gnsProductNonUnitalStarAlgHom hf t f.gnsVector⟫_ℂ :=
  (rfl)

/-- The tensor functional on elementary tensors: `μ_f(a ⊗ bᵒᵖ) = f (a b)`. -/
@[simp]
theorem gnsTensorFunctional_tmul (hf : ∀ a b, f (a * b) = f (b * a)) (a : A) (b : Aᵐᵒᵖ) :
    f.gnsTensorFunctional hf (a ⊗ₜ b) = f (a * b.unop) := by
  simp [gnsTensorFunctional_apply]

/-- The tensor functional takes the value `f 1` at the unit, so it is normalized for a
state. -/
@[simp]
theorem gnsTensorFunctional_one (hf : ∀ a b, f (a * b) = f (b * a)) :
    f.gnsTensorFunctional hf 1 = f 1 := by
  simp [Algebra.TensorProduct.one_def]

/-- The tensor functional at `t⋆ t` is the squared norm of `(π_f × π_fᵒᵖ)(t) Ω`; in particular
the tensor functional is positive. -/
theorem gnsTensorFunctional_star_mul_self (hf : ∀ a b, f (a * b) = f (b * a))
    (t : A ⊗[ℂ] Aᵐᵒᵖ) :
    f.gnsTensorFunctional hf (star t * t) =
      (‖f.gnsProductNonUnitalStarAlgHom hf t f.gnsVector‖ ^ 2 : ℝ) := by
  rw [gnsTensorFunctional_apply, map_mul, mul_apply_eq_comp,
    map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp

end Unital

end PositiveLinearMap
