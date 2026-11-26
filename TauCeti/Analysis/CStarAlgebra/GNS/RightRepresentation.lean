/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic

/-!
# The right representation of a tracial functional

Let `f` be a tracial positive functional on a possibly nonunital C⋆-algebra `A`, so
`f (a b) = f (b a)`, with GNS space `L²(A, f)`, classes `[a]` and GNS representation `π_f`,
`π_f(a)[c] = [a c]`. Right multiplication `[c] ↦ [c b]` is then bounded by `‖b‖`, because
`f ((c b)⋆ (c b)) = f (c (b b⋆) c⋆) ≤ ‖b‖ ^ 2 f (c c⋆) = ‖b‖ ^ 2 f (c⋆ c)` by traciality, and it
extends to the GNS space. This gives the *right representation*
`PositiveLinearMap.gnsRightNonUnitalStarAlgHom` of the opposite algebra `Aᵐᵒᵖ`,
`π_fᵒᵖ(bᵒᵖ)[c] = [c b]`, a star homomorphism: the adjoint of right multiplication by `b` is
right multiplication by `b⋆` because `f (a⋆ c b) = f (b a⋆ c)`. The right representation commutes
with `π_f`, `PositiveLinearMap.commute_gnsNonUnitalStarAlgHom_gnsRightNonUnitalStarAlgHom`.

For unital `A`, the right representation is unital, `PositiveLinearMap.gnsRightStarAlgHom`. The
GNS vector `Ω = [1]` satisfies `π_fᵒᵖ(bᵒᵖ) Ω = [b]`, so it is cyclic for `π_fᵒᵖ(Aᵐᵒᵖ)`,
`PositiveLinearMap.denseRange_gnsRightStarAlgHom_gnsVector`.

The range of the right representation lies in the commutant of the GNS von Neumann algebra
(`TauCeti.Analysis.CStarAlgebra.GNS.VonNeumannAlgebra`), and together with `π_f` it gives the
product representation of `A ⊗ Aᵐᵒᵖ` (`TauCeti.Analysis.CStarAlgebra.GNS.ProductRepresentation`).

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), Chapter 2, for the right representation of a tracial state.
* The constructions follow the left-action ones of Mathlib's
  `Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal`: `rightMulMapPreGNS` follows
  `PositiveLinearMap.leftMulMapPreGNS`, `gnsRightNonUnitalStarAlgHom` and its application lemmas
  follow `PositiveLinearMap.gnsNonUnitalStarAlgHom`, and `gnsRightStarAlgHom` follows
  `PositiveLinearMap.gnsStarAlgHom`.
-/

public section

open scoped InnerProductSpace ComplexOrder
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
    set c := f.ofPreGNS x
    have key : ((‖f.toPreGNS (c * b)‖ ^ 2 : ℝ) : ℂ) ≤ (((‖b‖ * ‖x‖) ^ 2 : ℝ) : ℂ) :=
      calc ((‖f.toPreGNS (c * b)‖ ^ 2 : ℝ) : ℂ)
          = f (star (c * b) * (c * b)) := by
            rw [Complex.ofReal_pow, preGNS_norm_sq, ofPreGNS_toPreGNS]
        _ = f (c * (b * star b) * star c) := by
          rw [star_mul, hf (star b * star c) (c * b)]
          simp only [mul_assoc]
        _ ≤ f (‖b * star b‖ • (c * star c)) :=
          OrderHomClass.mono f (CStarAlgebra.star_right_conjugate_le_norm_smul c (b * star b))
        _ = ((‖b‖ ^ 2 : ℝ) : ℂ) * f (star c * c) := by
          rw [CStarRing.norm_self_mul_star, ← sq, ← Complex.coe_smul, map_smul, smul_eq_mul,
            hf c (star c)]
        _ = (((‖b‖ * ‖x‖) ^ 2 : ℝ) : ℂ) := by
          rw [mul_pow, Complex.ofReal_mul, Complex.ofReal_pow ‖x‖, preGNS_norm_sq]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp (Complex.real_le_real.mp key)

@[simp]
theorem rightMulMapPreGNS_apply (hf : ∀ a b, f (a * b) = f (b * a)) (b : A) (c : f.PreGNS) :
    f.rightMulMapPreGNS hf b c = f.toPreGNS (f.ofPreGNS c * b) :=
  (rfl)

/-- **The right representation** of a tracial positive functional `f`: the star homomorphism
`π_fᵒᵖ : Aᵐᵒᵖ → B(L²(A, f))` with `π_fᵒᵖ(bᵒᵖ)[c] = [c b]`. -/
noncomputable def gnsRightNonUnitalStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    Aᵐᵒᵖ →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  toFun b := (f.rightMulMapPreGNS hf b.unop).completion
  map_smul' m b := f.gns_continuousLinearMap_ext fun c ↦ by
    simp [← Completion.coe_smul, mul_smul_comm]
  map_zero' := f.gns_continuousLinearMap_ext fun c ↦ by simp
  map_add' _ _ := f.gns_continuousLinearMap_ext fun c ↦ by simp [mul_add, Completion.coe_add]
  map_mul' _ _ := f.gns_continuousLinearMap_ext fun c ↦ by simp [mul_assoc]
  map_star' b := by
    refine (ContinuousLinearMap.eq_adjoint_iff (f.rightMulMapPreGNS hf (star b).unop).completion
      (f.rightMulMapPreGNS hf b.unop).completion).mpr ?_
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y =>
      simp only [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe, unop_star,
        rightMulMapPreGNS_apply, preGNS_inner_def, ofPreGNS_toPreGNS, star_mul, star_star]
      rw [mul_assoc, hf b.unop (star (f.ofPreGNS x) * f.ofPreGNS y), mul_assoc]

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
    Commute (f.gnsNonUnitalStarAlgHom a) (f.gnsRightNonUnitalStarAlgHom hf b) :=
  f.gns_continuousLinearMap_ext fun c ↦ by simp [mul_assoc]

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

/-- The right representation of a tracial functional on a unital C⋆-algebra preserves the unit. -/
@[simp]
theorem gnsRightNonUnitalStarAlgHom_one (hf : ∀ a b, f (a * b) = f (b * a)) :
    f.gnsRightNonUnitalStarAlgHom hf 1 = 1 :=
  f.gns_continuousLinearMap_ext fun c ↦ by simp

/-- The right representation of a tracial positive functional on a unital C⋆-algebra, as a
unital star homomorphism `Aᵐᵒᵖ → B(L²(A, f))`. -/
noncomputable def gnsRightStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    Aᵐᵒᵖ →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
  { f.gnsRightNonUnitalStarAlgHom hf with
    map_one' := f.gnsRightNonUnitalStarAlgHom_one hf
    commutes' r := by simp [Algebra.algebraMap_eq_smul_one] }

@[simp]
theorem coe_gnsRightStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    ⇑(f.gnsRightStarAlgHom hf) = f.gnsRightNonUnitalStarAlgHom hf :=
  (rfl)

/-- The unital right representation has underlying non-unital star homomorphism
`gnsRightNonUnitalStarAlgHom`. -/
@[simp]
theorem toNonUnitalStarAlgHom_gnsRightStarAlgHom (hf : ∀ a b, f (a * b) = f (b * a)) :
    (f.gnsRightStarAlgHom hf).toNonUnitalStarAlgHom = f.gnsRightNonUnitalStarAlgHom hf :=
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

end Unital

end PositiveLinearMap
