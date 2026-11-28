/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Coinduced
public import TauCeti.GroupTheory.DoubleCoset.Positivity
public import TauCeti.RepresentationTheory.Smooth.Basic
import Mathlib.Algebra.Order.Module.Rat
import TauCeti.RepresentationTheory.Coinduced

/-!
# Positive diagonals on smooth coinduced representations

Integrating the diagonal of a positive definite coefficient form gives a positive value on
any nonzero smooth coinduced function. This is the positive definiteness argument for the
class-integral pairing of algebraic modular forms in B. Gross, *Algebraic modular forms*,
Israel J. Math. 113 (1999), §4.
-/

public section

open TauCeti

namespace Representation

/-- The real part of the class integral of the pointwise diagonal of a positive definite
coefficient form is positive exactly for nonzero smooth coinduced vectors. The coefficient
form itself need not be invariant: its positive diagonal detects the invariant nonzero locus. -/
theorem classIntegral_re_apply_coindV_self_pos_iff {H G V : Type*} [Group H] [Group G]
    [TopologicalSpace G] [SeparatelyContinuousMul G] [AddCommMonoid V] [Module ℂ V]
    {φ : H →* G} {ρ : Representation ℂ H V} (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hpos : ∀ v ≠ 0, 0 < (B v v).re)
    {K : Subgroup G} (hK : HasFiniteType φ.range K) {f : coindV φ ρ}
    (hf : f ∈ (coind φ ρ).smoothVectors) :
    0 < (classIntegral φ.range K (fun g ↦ B (f.val g) (f.val g))).re ↔ f ≠ 0 := by
  let d : G → ℂ := fun g ↦ B (f.val g) (f.val g)
  have ho : IsOpen (rightTranslationStabilizer f.val : Set G) :=
    stabilizer_coind_eq f ▸ mem_smoothVectors_iff.mp hf
  have hd : IsOpen (rightTranslationStabilizer d : Set G) := by
    refine Subgroup.isOpen_mono (fun k hk ↦ mem_rightTranslationStabilizer.mpr fun g ↦ ?_) ho
    simp only [d, mem_rightTranslationStabilizer.mp hk g]
  have hpoint (v : V) : 0 < (B v v).re ↔ v ≠ 0 := by
    refine ⟨fun hv hz ↦ ?_, hpos v⟩
    simp [hz] at hv
  have hn (g : G) : 0 ≤ (d g).re := by
    rcases eq_or_ne (f.val g) 0 with h | h
    · simp [d, h]
    · exact (hpos _ h).le
  have hl : ∀ γ ∈ φ.range, ∀ g, 0 < (d (γ * g)).re ↔ 0 < (d g).re := by
    rintro γ ⟨h, rfl⟩ g
    simp only [d, hpoint, (mem_coindV φ ρ _).mp f.property h g]
    refine not_congr ⟨fun hz ↦ ?_, fun hz ↦ by simp [hz]⟩
    simpa [← mul_apply_eq_comp, ← map_mul] using congrArg (ρ h⁻¹) hz
  rw [← Complex.coe_reAddGroupHom, map_classIntegral_pos_iff hK Complex.reAddGroupHom hl hd hn]
  simp only [Complex.coe_reAddGroupHom, d, hpoint, Ne, Subtype.ext_iff, funext_iff,
    Submodule.coe_zero, Pi.zero_apply, not_forall]

end Representation
