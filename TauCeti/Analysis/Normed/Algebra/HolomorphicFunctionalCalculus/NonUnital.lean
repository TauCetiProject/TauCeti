/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Spectrum
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic
import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Unitization

/-!
# Holomorphic functional calculus for nonunital Banach algebras

For an element `a` of a nonunital complex Banach algebra `A`, embedding `a` into its external `ℓ¹`
unitization `WithLp 1 (Unitization ℂ A)` via `WithLp.unitizationInrL ℂ A` identifies
`spectrum ℂ (WithLp.unitizationInrL ℂ A a)` with `quasispectrum ℂ a` (which always contains `0`).
By `AlgHom.map_holomorphicCalculus_eq_eval` applied to `WithLp.unitizationFstA ℂ A` and
`WithLp.unitizationInrL ℂ A a`, the scalar part of `g(a)` is `g(0)`, so `g(a)` lies in the embedded
copy of `A` if and only if `g(0) = 0`.

On the nonunital subalgebra `holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 _` of holomorphic
germs near `quasispectrum ℂ a` that vanish at `0`, projecting onto `A` yields the nonunital
complex-algebra homomorphism `nonUnitalHolomorphicCalculus a` sending the coordinate germ `z ↦ z`
to `a`, intertwining the unitization inclusion with `holomorphicCalculus`, continuous for the
compact-open topology after precomposition with `HolomorphicFunctions.toGermVanishingAt` on each
open neighbourhood of `quasispectrum ℂ a`, and obeying the nonunital spectral mapping theorem:
`quasispectrum ℂ (nonUnitalHolomorphicCalculus a g)` is the set of point evaluations
`holomorphicGerms.eval z _ g.val` for `z ∈ quasispectrum ℂ a` (and `f '' quasispectrum ℂ a` for an
analytic representative `f` with `f 0 = 0`).

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

private theorem fst_holomorphicCalculus_eq_zero (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    (WithLp.ofLp (holomorphicCalculus (WithLp.unitizationInrL ℂ A a)
      (holomorphicGerms.restrict (WithLp.spectrum_unitizationInrL a).le g.val))).fst = 0 := by
  rw [← WithLp.unitizationFstA_apply, ← WithLp.mem_range_unitizationInrL_iff,
    WithLp.holomorphicCalculus_mem_range_unitizationInrL_iff]
  simp

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
    apply (WithLp.unitization_isometry_inr (𝕜 := ℂ) (A := A)).injective
    simp only [← WithLp.unitizationInrL_apply, WithLp.unitizationInrL_mul,
      WithLp.unitizationInrL_unitizationSndL_of_fst_eq_zero (fst_holomorphicCalculus_eq_zero a _)]
    simp only [MulMemClass.coe_mul, map_mul]

/-- Formula for `nonUnitalHolomorphicCalculus a g` via the `ℓ¹` unitization. -/
theorem nonUnitalHolomorphicCalculus_apply (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    nonUnitalHolomorphicCalculus a g = WithLp.unitizationSndL ℂ A
      (holomorphicCalculus (WithLp.unitizationInrL ℂ A a)
        (holomorphicGerms.restrict (WithLp.spectrum_unitizationInrL a).le g.val)) := (rfl)

/-- Evaluating `nonUnitalHolomorphicCalculus a` on a holomorphic function on an open
neighbourhood `U` of `quasispectrum ℂ a` vanishing at `0` agrees with projecting the unital
`holomorphicCalculusOn` of the embedded element onto `A`. -/
@[simp]
theorem nonUnitalHolomorphicCalculus_toGermVanishingAt (a : A) (U : Opens ℂ)
    (ha : quasispectrum ℂ a ⊆ U)
    (f : vanishingAt U 0 (ha (quasispectrum.zero_mem ℂ a))) :
    nonUnitalHolomorphicCalculus a (toGermVanishingAt ha (quasispectrum.zero_mem ℂ a) f) =
      WithLp.unitizationSndL ℂ A (holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U
        ((WithLp.spectrum_unitizationInrL a).le.trans ha) f.val) := by
  simp [nonUnitalHolomorphicCalculus_apply]

/-- For every open neighbourhood `U` of `quasispectrum ℂ a`, composing
`nonUnitalHolomorphicCalculus a` with the chart map `HolomorphicFunctions.toGermVanishingAt` is
continuous for the compact-open topology on `HolomorphicFunctions.vanishingAt U 0 _`. -/
@[continuity]
theorem continuous_nonUnitalHolomorphicCalculus_comp_toGermVanishingAt (a : A)
    (U : Opens ℂ) (ha : quasispectrum ℂ a ⊆ U) :
    Continuous (nonUnitalHolomorphicCalculus a ∘
      toGermVanishingAt ha (quasispectrum.zero_mem ℂ a)) := by
  have heq : (nonUnitalHolomorphicCalculus a ∘
      toGermVanishingAt ha (quasispectrum.zero_mem ℂ a)) =
      fun f ↦ WithLp.unitizationSndL ℂ A (holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U
        ((WithLp.spectrum_unitizationInrL a).le.trans ha) f.val) :=
    funext (nonUnitalHolomorphicCalculus_toGermVanishingAt a U ha)
  rw [heq]
  exact ((WithLp.unitizationSndL ℂ A).continuous.comp
    (continuous_holomorphicCalculusOn _ _ _)).comp continuous_subtypeVal

/-- Embedding `nonUnitalHolomorphicCalculus a g` into the `ℓ¹` unitization agrees with the unital
`holomorphicCalculus` of the embedded element. -/
@[simp]
theorem toLp_inr_nonUnitalHolomorphicCalculus (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    WithLp.toLp 1 (nonUnitalHolomorphicCalculus a g : Unitization ℂ A) =
      holomorphicCalculus (WithLp.unitizationInrL ℂ A a)
        (holomorphicGerms.restrict (WithLp.spectrum_unitizationInrL a).le g.val) := by
  rw [nonUnitalHolomorphicCalculus_apply, ← WithLp.unitizationInrL_apply]
  exact WithLp.unitizationInrL_unitizationSndL_of_fst_eq_zero (fst_holomorphicCalculus_eq_zero a g)

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
    spectrum_holomorphicCalculus,
    holomorphicGerms.spectrum_restrict_of_eq (WithLp.spectrum_unitizationInrL a),
    holomorphicGerms.spectrum_eq]

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

/-- **Nonunital spectral mapping theorem (open-domain form).** For a holomorphic function `f` on
an open neighbourhood `U` of `quasispectrum ℂ a` vanishing at `0`,
`quasispectrum ℂ (nonUnitalHolomorphicCalculus a (toGermVanishingAt ha _ f)) =`
`extend f.val '' quasispectrum ℂ a`. -/
theorem quasispectrum_nonUnitalHolomorphicCalculus_toGermVanishingAt (a : A) (U : Opens ℂ)
    (ha : quasispectrum ℂ a ⊆ U)
    (f : vanishingAt U 0 (ha (quasispectrum.zero_mem ℂ a))) :
    quasispectrum ℂ (nonUnitalHolomorphicCalculus a
        (toGermVanishingAt ha (quasispectrum.zero_mem ℂ a) f)) =
      extend f.val '' quasispectrum ℂ a := by
  rw [quasispectrum_nonUnitalHolomorphicCalculus]
  ext c
  constructor <;> rintro ⟨z, hz, rfl⟩
  · exact ⟨z, hz, by simp [extend_apply f.val ⟨z, ha hz⟩]⟩
  · exact ⟨z, hz, by simp [(extend_apply f.val ⟨z, ha hz⟩).symm]⟩

end NonUnital

end TauCeti
