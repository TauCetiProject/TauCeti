/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Pairings between cyclic spans

A bilinear pairing whose value on two generators is a unit identifies the span of the first
generator with the dual of the span of the second. The ambient modules may be different, and
the coefficient ring need only be a commutative semiring.
-/

public section

namespace LinearMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A unit generator pairing makes the pairing between the two cyclic spans bijective onto
the dual of the right span. -/
theorem compl₁₂_span_singleton_bijective_of_isUnit (B : M →ₗ[R] N →ₗ[R] R)
    (x : M) (y : N) (hxy : IsUnit (B x y)) :
    Function.Bijective (B.compl₁₂ (R ∙ x).subtype (R ∙ y).subtype) := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hxy
  let S : Submodule R M := R ∙ x
  let T : Submodule R N := R ∙ y
  have hxS : x ∈ S := Submodule.mem_span_singleton_self x
  have hyT : y ∈ T := Submodule.mem_span_singleton_self y
  constructor
  · intro v w hvw
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp v.property
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.property
    have hval : B (v : M) y = B (w : M) y := by
      simpa only [compl₁₂_apply, Submodule.subtype_apply] using
        DFunLike.congr_fun hvw (⟨y, hyT⟩ : T)
    rw [← hb, ← hc, map_smul, map_smul, smul_apply, smul_apply] at hval
    simp only [smul_eq_mul] at hval
    have hbc : b = c := by
      simpa only [mul_assoc, ha, mul_one] using congrArg (fun z ↦ z * a) hval
    apply Subtype.ext
    rw [← hb, ← hc, hbc]
  · intro f
    refine ⟨⟨(a * f ⟨y, hyT⟩) • x, Submodule.smul_mem S _ hxS⟩, ?_⟩
    ext z
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp z.property
    have hz : z = b • (⟨y, hyT⟩ : T) := Subtype.ext hb.symm
    rw [hz]
    simp only [compl₁₂_apply, Submodule.subtype_apply, map_smul, smul_apply, smul_eq_mul]
    calc
      b * (a * f ⟨y, hyT⟩ * B x y) = b * f ⟨y, hyT⟩ * (B x y * a) := by ac_rfl
      _ = b * f ⟨y, hyT⟩ := by rw [ha, mul_one]

end LinearMap
