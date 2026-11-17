/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import TauCeti.RingTheory.Jacobson.NonUnital

import TauCeti.Analysis.Normed.Algebra.Jacobson
import TauCeti.Analysis.Normed.Algebra.Unitization.Basic
import TauCeti.RingTheory.Jacobson.Spectrum

/-!
# Characters and the radical of commutative Banach algebras

A character of a complex algebra `A` is an algebra homomorphism `A → ℂ`. In the nonunital setting
it is a nonunital algebra homomorphism, and the zero map is allowed. A nonunital character of a
Banach algebra is bounded by the norm, with no unit and no continuity assumption, because its
values lie in the quasispectrum.

Every character kills the Jacobson radical. In a commutative complex Banach algebra the converse
holds. By Gelfand–Mazur every point of the spectrum is the value of a character, so an element
killed by every character has only quasinilpotent left multiples, and lies in the radical. Thus
the kernel of the Gelfand transform of a commutative unital complex Banach algebra is its radical.
The nonunital
statement is reduced to the unital one through the ℓ¹ unitization, which is commutative when the
algebra is.

These facts are the input to Šilov's theorem that homomorphisms into commutative semisimple
Banach algebras are automatically continuous.

## Main results

* `NonUnitalAlgHom.norm_apply_le_self`, `NonUnitalAlgHom.instContinuousLinearMapClass`: nonunital
  characters of Banach algebras are contractive, hence continuous.
* `NonUnitalAlgHom.toContinuousLinearMap`, `NonUnitalAlgHom.norm_toContinuousLinearMap_le`: bundling
  a nonunital character as a continuous linear functional in `StrongDual 𝕜 A` of operator norm at
  most `1`.
* `TauCeti.Ring.mem_jacobson_iff_forall_algHom_apply_eq_zero`,
  `TauCeti.ker_gelfandTransform`: in a commutative unital complex Banach algebra the radical is
  the common kernel of the characters, which is the kernel of the Gelfand transform.
* `TauCeti.mem_nonUnitalJacobson_iff_forall_nonUnitalAlgHom_apply_eq_zero`: the same for the
  radical of a commutative nonunital complex Banach algebra and its nonunital characters.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §1.5 for the radical, and its
  Gelfand theory of commutative Banach algebras.
* The Gelfand–Mazur step is Mathlib's `WeakDual.CharacterSpace.mem_spectrum_iff_exists`.
-/

public section

namespace NonUnitalAlgHom

section FunLike

variable {𝕜 A F : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A] [FunLike F A 𝕜] [NonUnitalAlgHomClass F 𝕜 A 𝕜]

/-- A nonunital character of a Banach algebra is contractive. No continuity is assumed, and the
scalar field need not be complete. -/
theorem norm_apply_le_self (φ : F) (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  by_contra! h
  have hφ : φ a ≠ 0 := fun h0 ↦ (norm_nonneg a).not_gt (by simpa [h0] using h)
  -- If `‖φ a‖ > ‖a‖`, then `b = (φ a)⁻¹ • a` has norm `< 1` and `φ b = 1`, but the geometric
  -- series `s` of `b` satisfies `b + b * s = s`, so `1 + φ s = φ s`.
  have hb : φ ((φ a)⁻¹ • a) = 1 := by simp [hφ]
  have hbn : ‖(φ a)⁻¹ • a‖ < 1 := by
    rw [norm_smul, norm_inv]
    exact (inv_mul_lt_iff₀ (norm_pos_iff.2 hφ)).2 (by simpa using h)
  simpa [hb] using congrArg φ (add_self_mul_geom_series hbn)

/-- A nonunital character of a Banach algebra is automatically continuous, so `map_continuous`
applies to it. This is the nonunital counterpart of Mathlib's instance for unital characters. -/
instance (priority := 100) instContinuousLinearMapClass : ContinuousLinearMapClass F 𝕜 A 𝕜 :=
  { NonUnitalAlgHomClass.instLinearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 fun a => by simpa using norm_apply_le_self φ a }

end FunLike

section NormedField

variable {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A]

/-- A nonunital algebra homomorphism from a complete normed algebra into its scalar field, bundled
as a continuous linear functional in `StrongDual 𝕜 A`. No continuity hypothesis on `φ` is needed. -/
def toContinuousLinearMap (φ : A →ₙₐ[𝕜] 𝕜) : StrongDual 𝕜 A where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ
  cont := map_continuous φ

@[simp]
theorem coe_toContinuousLinearMap (φ : A →ₙₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_apply (φ : A →ₙₐ[𝕜] 𝕜) (a : A) :
    φ.toContinuousLinearMap a = φ a :=
  (rfl)

theorem toContinuousLinearMap_injective :
    Function.Injective (toContinuousLinearMap (𝕜 := 𝕜) (A := A)) := fun φ ψ h =>
  DFunLike.ext φ ψ fun a => congrArg (fun f : StrongDual 𝕜 A => f a) h

@[simp]
theorem toContinuousLinearMap_inj {φ ψ : A →ₙₐ[𝕜] 𝕜} :
    φ.toContinuousLinearMap = ψ.toContinuousLinearMap ↔ φ = ψ :=
  toContinuousLinearMap_injective.eq_iff

@[simp]
theorem toContinuousLinearMap_zero :
    (0 : A →ₙₐ[𝕜] 𝕜).toContinuousLinearMap = 0 :=
  DFunLike.ext _ _ fun _ => rfl

@[simp]
theorem toContinuousLinearMap_eq_zero {φ : A →ₙₐ[𝕜] 𝕜} :
    φ.toContinuousLinearMap = 0 ↔ φ = 0 := by
  rw [← toContinuousLinearMap_zero, toContinuousLinearMap_inj]

end NormedField

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A]

/-- Every nonunital character of a complete normed algebra has operator norm at most `1`. -/
theorem norm_toContinuousLinearMap_le (φ : A →ₙₐ[𝕜] 𝕜) : ‖φ.toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    simpa only [one_mul, toContinuousLinearMap_apply] using norm_apply_le_self φ a

end NontriviallyNormedField

end NonUnitalAlgHom

namespace TauCeti

namespace Ring

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- In a commutative unital complex Banach algebra, an element lies in the Jacobson radical
exactly when every character kills it. -/
theorem mem_jacobson_iff_forall_algHom_apply_eq_zero {a : A} :
    a ∈ Ring.jacobson A ↔ ∀ φ : A →ₐ[ℂ] ℂ, φ a = 0 := by
  refine ⟨fun ha φ => φ.apply_eq_zero_of_mem_jacobson ha, fun h => ?_⟩
  -- Every point of the spectrum of a left multiple `b * a` is a character value `φ b * φ a`.
  refine (mem_jacobson_iff_forall_spectrum_mul_subset_singleton_zero (𝕜 := ℂ)).mpr
    fun b z hz => ?_
  obtain ⟨φ, rfl⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  have hφ := h (WeakDual.CharacterSpace.equivAlgHom φ)
  rw [WeakDual.CharacterSpace.equivAlgHom_coe] at hφ
  simp [hφ]

end Ring

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The kernel of the Gelfand transform of a commutative unital complex Banach algebra is its
Jacobson radical. -/
theorem ker_gelfandTransform :
    RingHom.ker (WeakDual.gelfandTransform ℂ A) = Ring.jacobson A := by
  ext a
  rw [RingHom.mem_ker, Ring.mem_jacobson_iff_forall_algHom_apply_eq_zero,
    WeakDual.CharacterSpace.equivAlgHom.forall_congr_right.symm]
  simp [ContinuousMap.ext_iff]

variable {B : Type*} [NonUnitalNormedCommRing B] [NormedSpace ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] [CompleteSpace B]

/-- In a commutative complex Banach algebra, possibly without unit, an element lies in the
Jacobson radical exactly when every nonunital character kills it. -/
theorem mem_nonUnitalJacobson_iff_forall_nonUnitalAlgHom_apply_eq_zero {b : B} :
    b ∈ nonUnitalJacobson ℂ B ↔ ∀ φ : B →ₙₐ[ℂ] ℂ, φ b = 0 := by
  refine ⟨fun hb φ => φ.apply_eq_zero_of_mem_nonUnitalJacobson hb, fun h => ?_⟩
  -- A character `φ` of the ℓ¹ unitization restricts to the nonunital character `φ ∘ inr`.
  rw [mem_nonUnitalJacobson_iff_toLp_mem_jacobson ℂ B,
    Ring.mem_jacobson_iff_forall_algHom_apply_eq_zero]
  intro φ
  exact h ((φ.comp (WithLp.unitizationAlgEquiv ℂ).symm.toAlgHom).toNonUnitalAlgHom.comp
    (Unitization.inrNonUnitalAlgHom ℂ B))

end TauCeti
