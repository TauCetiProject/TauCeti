/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Spectrum
public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Unitization

/-!
# Holomorphic functional calculus for nonunital Banach algebras

For an element `a` of a nonunital complex Banach algebra `A`, embedding `a` into its external `ℓ¹`
unitization `WithLp 1 (Unitization ℂ A)` via `WithLp.unitizationInrL ℂ A` identifies
`spectrum ℂ (WithLp.unitizationInrL ℂ A a)` with `quasispectrum ℂ a` (which always contains `0`).
By `WithLp.unitizationFstA_holomorphicCalculus` (applied to `WithLp.unitizationInrL ℂ A a`), the
scalar part of `g(a)` is `g(0)`, so `g(a)` lies in the embedded copy of `A` if and only if
`g(0) = 0`.

On the nonunital subalgebra `holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 _` of holomorphic
germs near `quasispectrum ℂ a` that vanish at `0`, projecting onto `A` yields the nonunital
complex-algebra homomorphism `nonUnitalHolomorphicCalculus a` sending the coordinate germ `z ↦ z`
to `a`, intertwining the unitization inclusion with `holomorphicCalculus`, and obeying the
nonunital spectral mapping theorem: `quasispectrum ℂ (nonUnitalHolomorphicCalculus a g)` is the
set of point evaluations `holomorphicGerms.eval z _ g.val` for `z ∈ quasispectrum ℂ a` (and
`f '' quasispectrum ℂ a` for an analytic representative `f` with `f 0 = 0`).

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Complex Set TopologicalSpace

namespace TauCeti

open HolomorphicFunctions

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

/-- **Nonunital holomorphic functional calculus.** For an element `a` of a nonunital complex Banach
algebra `A`, evaluating holomorphic germs near `quasispectrum ℂ a` that vanish at `0` in the `ℓ¹`
unitization and projecting onto `A` defines a nonunital complex-algebra homomorphism into `A`. -/
def nonUnitalHolomorphicCalculus (a : A) :
    holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a) →ₙₐ[ℂ] A where
  toFun g := WithLp.unitizationSndL ℂ A (holomorphicCalculus (WithLp.unitizationInrL ℂ A a)
    (holomorphicGerms.restrict (WithLp.spectrum_unitizationInrL a).le g.val))
  map_smul' c g := by simp
  map_zero' := by simp
  map_add' g₁ g₂ := by simp
  map_mul' g₁ g₂ := by
    have hfst (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0
        (quasispectrum.zero_mem ℂ a)) :
        (WithLp.ofLp (holomorphicCalculus (WithLp.unitizationInrL ℂ A a)
          (holomorphicGerms.restrict (WithLp.spectrum_unitizationInrL a).le g.val))).fst = 0 := by
      simpa only [WithLp.unitizationFstA_apply] using
        ((WithLp.unitizationInrL ℂ A a).unitizationFstA_holomorphicCalculus _).trans (by simp)
    simp only [MulMemClass.coe_mul, map_mul, WithLp.unitizationSndL_apply,
      WithLp.unitization_mul, Unitization.snd_mul, hfst g₁, hfst g₂, zero_smul, zero_add]

/-- Formula for `nonUnitalHolomorphicCalculus a g` via the `ℓ¹` unitization. -/
theorem nonUnitalHolomorphicCalculus_apply (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    nonUnitalHolomorphicCalculus a g = WithLp.unitizationSndL ℂ A
      (holomorphicCalculus (WithLp.unitizationInrL ℂ A a)
        (holomorphicGerms.restrict (WithLp.spectrum_unitizationInrL a).le g.val)) := (rfl)

/-- Embedding `nonUnitalHolomorphicCalculus a g` into the `ℓ¹` unitization agrees with the unital
`holomorphicCalculus` of the embedded element. -/
@[simp]
theorem toLp_inr_nonUnitalHolomorphicCalculus (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    WithLp.toLp 1 (nonUnitalHolomorphicCalculus a g : Unitization ℂ A) =
      holomorphicCalculus (WithLp.unitizationInrL ℂ A a)
        (holomorphicGerms.restrict (WithLp.spectrum_unitizationInrL a).le g.val) := by
  rw [nonUnitalHolomorphicCalculus_apply]
  simpa only [WithLp.unitizationInrL_apply] using
    WithLp.unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_eq_zero
      (WithLp.unitizationInrL ℂ A a) (by simp)

/-- The nonunital holomorphic functional calculus sends the coordinate germ `z ↦ z` to `a`. -/
@[simp]
theorem nonUnitalHolomorphicCalculus_id (a : A) :
    nonUnitalHolomorphicCalculus a
      (holomorphicGerms.ofFunVanishingAt (quasispectrum.zero_mem ℂ a) id analyticOnNhd_id rfl) =
      a :=
  (WithLp.unitization_isometry_inr (𝕜 := ℂ) (A := A)).injective (by simp)

/-- **Nonunital spectral mapping theorem** for holomorphic germs vanishing at `0`. -/
theorem quasispectrum_nonUnitalHolomorphicCalculus (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    quasispectrum ℂ (nonUnitalHolomorphicCalculus a g) =
      {c | ∃ (z : ℂ) (hz : z ∈ quasispectrum ℂ a), holomorphicGerms.eval z hz g.val = c} := by
  rw [← TauCeti.spectrum_unitization_toLp_inr, toLp_inr_nonUnitalHolomorphicCalculus,
    spectrum_holomorphicCalculus, holomorphicGerms.spectrum_eq]
  ext c; constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, (WithLp.spectrum_unitizationInrL a).le hz,
      (holomorphicGerms.eval_restrict _ z hz g.val).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, (WithLp.spectrum_unitizationInrL a).ge hz,
      holomorphicGerms.eval_restrict _ z _ g.val⟩

/-- **Nonunital spectral mapping theorem** for an analytic representative `f` with `f 0 = 0`:
`quasispectrum ℂ (f(a)) = f '' quasispectrum ℂ a`. -/
@[simp]
theorem quasispectrum_nonUnitalHolomorphicCalculus_ofFunVanishingAt (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (quasispectrum ℂ a)) (hf0 : f 0 = 0) :
    quasispectrum ℂ (nonUnitalHolomorphicCalculus a
        (holomorphicGerms.ofFunVanishingAt (quasispectrum.zero_mem ℂ a) f hf hf0)) =
      f '' quasispectrum ℂ a := by
  rw [quasispectrum_nonUnitalHolomorphicCalculus]
  ext c; simp [Set.mem_image]

end NonUnital

end TauCeti
