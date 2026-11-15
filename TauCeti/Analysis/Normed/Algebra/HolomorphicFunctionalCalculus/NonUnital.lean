/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.SpectralMapping
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic

/-!
# Holomorphic functional calculus for nonunital Banach algebras

For an element `a` of a nonunital complex Banach algebra `A`, embedding `a` into its external `ℓ¹`
unitization `WithLp 1 (Unitization ℂ A)` identifies `spectrum ℂ (toLp 1 ↑a)` with
`quasispectrum ℂ a` (which always contains `0`). Applying naturality of `holomorphicCalculus` along
the continuous scalar augmentation `WithLp.unitizationFstA ℂ A` identifies the scalar part of
`g(a)` with `g(0)`, so `g(a)` lies in the embedded copy of `A` if and only if `g(0) = 0`.

On the nonunital subalgebra `holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 _` of holomorphic
germs near `quasispectrum ℂ a` that vanish at `0`, projecting onto `A` yields the nonunital
complex-algebra homomorphism `nonUnitalHolomorphicCalculus a` satisfying `a ↦ a`, intertwining the
unitization inclusion with `holomorphicCalculus`, and obeying the nonunital spectral mapping
theorem `quasispectrum ℂ (nonUnitalHolomorphicCalculus a g) = g '' quasispectrum ℂ a`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Complex Set TopologicalSpace

namespace TauCeti

open HolomorphicFunctions

namespace holomorphicGerms

/-- The nonunital complex subalgebra of `holomorphicGerms s` consisting of germs vanishing at a
marked point `x ∈ s`. -/
def vanishingAt (s : Set ℂ) (x : ℂ) (hx : x ∈ s) :
    NonUnitalSubalgebra ℂ (holomorphicGerms s) where
  carrier := {g | eval x hx g = 0}
  zero_mem' := map_zero _
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  mul_mem' {a b} ha _ := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_mul, ha, zero_mul]
  smul_mem' c {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_smul, ha, smul_zero]

/-- Membership in `holomorphicGerms.vanishingAt s x hx` means vanishing under `eval x hx`. -/
@[simp]
theorem mem_vanishingAt_iff {s : Set ℂ} {x : ℂ} {hx : x ∈ s} {g : holomorphicGerms s} :
    g ∈ vanishingAt s x hx ↔ eval x hx g = 0 := Iff.rfl

/-- Construct an element of `holomorphicGerms.vanishingAt` from an analytic representative `f`
satisfying `f x = 0`. -/
def ofFunVanishingAt {s : Set ℂ} {x : ℂ} (hx : x ∈ s) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f s)
    (hf0 : f x = 0) : vanishingAt s x hx :=
  ⟨ofFun f hf, mem_vanishingAt_iff.mpr (by simpa using hf0)⟩

/-- Coercing `ofFunVanishingAt` back to `holomorphicGerms s` recovers `ofFun f hf`. -/
@[simp]
theorem coe_ofFunVanishingAt {s : Set ℂ} {x : ℂ} (hx : x ∈ s) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f s) (hf0 : f x = 0) :
    (ofFunVanishingAt hx f hf hf0 : holomorphicGerms s) = ofFun f hf := (rfl)

end holomorphicGerms

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

/-- Applying the scalar augmentation `WithLp.unitizationFstA` to `holomorphicCalculusOn` of an
element of `A` embedded in its `ℓ¹` unitization evaluates the holomorphic function at `0`. -/
theorem unitizationFstA_holomorphicCalculusOn_toLp_inr (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)) ⊆ U) (f : holomorphicFunctions U) :
    WithLp.unitizationFstA ℂ A
        (holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f) =
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_toLp_inr a)⟩ := by
  rw [AlgHom.map_holomorphicCalculusOn_continuousMapClass]
  simp

/-- Applying the scalar augmentation `WithLp.unitizationFstA` to `holomorphicCalculus` of an
element of `A` embedded in its `ℓ¹` unitization evaluates the germ at `0`. -/
theorem unitizationFstA_holomorphicCalculus_toLp_inr (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)))) :
    WithLp.unitizationFstA ℂ A
        (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g) =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_toLp_inr a) g := by
  rw [AlgHom.map_holomorphicCalculus_continuousMapClass]
  simp

/-- In the `ℓ¹` unitization of `A`, `holomorphicCalculusOn` of an embedded element `a : A` lies in
`Set.range (WithLp.unitizationInrL ℂ A)` if and only if `f 0 = 0`. -/
theorem holomorphicCalculusOn_toLp_inr_mem_range_unitizationInrL_iff (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (WithLp.toLp 1 (a : Unitization ℂ A)) U ha f ∈
        Set.range (WithLp.unitizationInrL ℂ A) ↔
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_toLp_inr a)⟩ = 0 := by
  rw [WithLp.mem_range_unitizationInrL_iff, unitizationFstA_holomorphicCalculusOn_toLp_inr]

/-- In the `ℓ¹` unitization of `A`, `holomorphicCalculus` of an embedded element `a : A` lies in
`Set.range (WithLp.unitizationInrL ℂ A)` if and only if the germ vanishes at `0`. -/
theorem holomorphicCalculus_toLp_inr_mem_range_unitizationInrL_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)))) :
    holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g ∈
        Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_toLp_inr a) g = 0 := by
  rw [WithLp.mem_range_unitizationInrL_iff, unitizationFstA_holomorphicCalculus_toLp_inr]

/-- When a holomorphic germ vanishes at `0`, projecting its unitized calculus value to `A` and
re-embedding recovers the unitized calculus value. -/
theorem unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_zero (a : A)
    {g : holomorphicGerms (spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)))}
    (hg : holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_toLp_inr a) g = 0) :
    WithLp.unitizationInrL ℂ A
        (WithLp.unitizationSndL ℂ A
          (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g)) =
      holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A)) g := by
  apply WithLp.unitizationInrL_unitizationSndL_of_fst_eq_zero
  simpa only [WithLp.unitizationFstA_apply] using
    (unitizationFstA_holomorphicCalculus_toLp_inr a g).trans hg

/-- **Nonunital holomorphic functional calculus.** For an element `a` of a nonunital complex Banach
algebra `A`, evaluating holomorphic germs near `quasispectrum ℂ a` that vanish at `0` in the `ℓ¹`
unitization and projecting onto `A` defines a nonunital complex-algebra homomorphism into `A`. -/
def nonUnitalHolomorphicCalculus (a : A) :
    holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a) →ₙₐ[ℂ] A where
  toFun g :=
    WithLp.unitizationSndL ℂ A
      (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
        (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g.val))
  map_smul' c g := by simp
  map_zero' := by simp
  map_add' g₁ g₂ := by simp
  map_mul' g₁ g₂ := by
    apply (WithLp.unitization_isometry_inr (𝕜 := ℂ) (A := A)).injective
    have h₁ :
        WithLp.unitizationInrL ℂ A
            (WithLp.unitizationSndL ℂ A
              (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
                (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g₁.val))) =
          holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
            (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g₁.val) :=
      unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_zero a
        (by simp [holomorphicGerms.mem_vanishingAt_iff.mp g₁.property])
    have h₂ :
        WithLp.unitizationInrL ℂ A
            (WithLp.unitizationSndL ℂ A
              (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
                (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g₂.val))) =
          holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
            (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g₂.val) :=
      unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_zero a
        (by simp [holomorphicGerms.mem_vanishingAt_iff.mp g₂.property])
    have h₁₂ :
        WithLp.unitizationInrL ℂ A
            (WithLp.unitizationSndL ℂ A
              (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
                (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le (g₁ * g₂).val))) =
          holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
            (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le (g₁ * g₂).val) :=
      unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_zero a
        (by simp [holomorphicGerms.mem_vanishingAt_iff.mp g₁.property])
    calc WithLp.toLp 1
          ((WithLp.unitizationSndL ℂ A
            (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
              (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le (g₁ * g₂).val)) : A) :
            Unitization ℂ A)
        = WithLp.unitizationInrL ℂ A
            (WithLp.unitizationSndL ℂ A
              (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
                (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le (g₁ * g₂).val))) :=
          (WithLp.unitizationInrL_apply ℂ A _).symm
      _ = WithLp.unitizationInrL ℂ A
            (WithLp.unitizationSndL ℂ A
                (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
                  (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g₁.val)) *
              WithLp.unitizationSndL ℂ A
                (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
                  (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g₂.val))) := by
          rw [h₁₂, WithLp.unitizationInrL_mul, h₁, h₂, ← map_mul, ← map_mul]
          rfl
      _ = _ := WithLp.unitizationInrL_apply ℂ A _

/-- Formula for `nonUnitalHolomorphicCalculus a g` via the `ℓ¹` unitization. -/
theorem nonUnitalHolomorphicCalculus_apply (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    nonUnitalHolomorphicCalculus a g =
      WithLp.unitizationSndL ℂ A
        (holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
          (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g.val)) := (rfl)

/-- Embedding `nonUnitalHolomorphicCalculus a g` into the `ℓ¹` unitization agrees with the unital
`holomorphicCalculus` of the embedded element. -/
theorem unitizationInrL_nonUnitalHolomorphicCalculus (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    WithLp.unitizationInrL ℂ A (nonUnitalHolomorphicCalculus a g) =
      holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
        (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g.val) :=
  unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_zero a
    (by simp [holomorphicGerms.mem_vanishingAt_iff.mp g.property])

/-- `WithLp.toLp 1` embedding form of `unitizationInrL_nonUnitalHolomorphicCalculus`. -/
@[simp]
theorem toLp_inr_nonUnitalHolomorphicCalculus (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    WithLp.toLp 1 (nonUnitalHolomorphicCalculus a g : Unitization ℂ A) =
      holomorphicCalculus (WithLp.toLp 1 (a : Unitization ℂ A))
        (holomorphicGerms.restrict (WithLp.spectrum_toLp_inr a).le g.val) := by
  simpa only [WithLp.unitizationInrL_apply] using unitizationInrL_nonUnitalHolomorphicCalculus a g

/-- The nonunital holomorphic functional calculus sends the coordinate germ `z ↦ z` to `a`. -/
@[simp]
theorem nonUnitalHolomorphicCalculus_id (a : A) :
    nonUnitalHolomorphicCalculus a
      (holomorphicGerms.ofFunVanishingAt (quasispectrum.zero_mem ℂ a) id analyticOnNhd_id rfl) =
      a := by
  apply (WithLp.unitization_isometry_inr (𝕜 := ℂ) (A := A)).injective
  simp

/-- **Nonunital spectral mapping theorem** for holomorphic germs vanishing at `0`. -/
@[simp]
theorem quasispectrum_nonUnitalHolomorphicCalculus (a : A)
    (g : holomorphicGerms.vanishingAt (quasispectrum ℂ a) 0 (quasispectrum.zero_mem ℂ a)) :
    quasispectrum ℂ (nonUnitalHolomorphicCalculus a g) =
      {c | ∃ (z : ℂ) (hz : z ∈ quasispectrum ℂ a), holomorphicGerms.eval z hz g.val = c} := by
  rw [← WithLp.spectrum_toLp_inr, toLp_inr_nonUnitalHolomorphicCalculus,
    spectrum_holomorphicCalculus]
  ext c
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, (WithLp.spectrum_toLp_inr a).le hz,
      (holomorphicGerms.eval_restrict (WithLp.spectrum_toLp_inr a).le z hz g.val).symm⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ spectrum ℂ (WithLp.toLp 1 (a : Unitization ℂ A)) :=
      (WithLp.spectrum_toLp_inr a).ge hz
    exact ⟨z, hz', holomorphicGerms.eval_restrict (WithLp.spectrum_toLp_inr a).le z hz' g.val⟩

/-- **Nonunital spectral mapping theorem** for an analytic representative `f` with `f 0 = 0`:
`quasispectrum ℂ (f(a)) = f '' quasispectrum ℂ a`. -/
theorem quasispectrum_nonUnitalHolomorphicCalculus_ofFun (a : A) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (quasispectrum ℂ a)) (hf0 : f 0 = 0) :
    quasispectrum ℂ
        (nonUnitalHolomorphicCalculus a
          (holomorphicGerms.ofFunVanishingAt (quasispectrum.zero_mem ℂ a) f hf hf0)) =
      f '' quasispectrum ℂ a := by
  ext c
  simp [Set.mem_image]

end NonUnital

end TauCeti
