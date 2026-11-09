/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Characters from unitary multipliers

A unitary representation need not be continuous in the norm of a C⋆-algebra. Nevertheless,
a character of a subalgebra detects a continuous circle-valued character whenever it is nonzero
on an operator whose translates are norm continuous and belong to the subalgebra. The resulting
character describes every translate that belongs to the subalgebra, so it is independent of
the operator used to detect it.

This is the character-identification step in the spectral representation of a strongly
continuous unitary representation, applied to a nonzero integrated operator.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, second edition, §4.4.
-/

public section

open WeakDual

namespace TauCeti

variable {G B : Type*} [Monoid G] [TopologicalSpace G] [CStarAlgebra B]

/-- A character nonzero on a commuting operator with norm-continuous unitary translates
induces a unique continuous circle-valued character. It describes every translate in the subalgebra,
not just the translates of the witnessing operator. -/
theorem _root_.MonoidHom.existsUnique_pontryaginDual_of_unitary_translate
    (ρ : G →* B) (hρ : ∀ g, ρ g ∈ unitary B)
    (A : StarSubalgebra ℂ B) [CompleteSpace A]
    (a : A) (hcomm : ∀ g, Commute (ρ g) (a : B))
    (hmem : ∀ g, ρ g * (a : B) ∈ A)
    (hcont : Continuous fun g => ρ g * (a : B))
    (ω : characterSpace ℂ A) (ha : ω a ≠ 0) :
    ∃! χ : PontryaginDual G,
      ∀ (g : G) (b : A) (hb : ρ g * (b : B) ∈ A),
        ω ⟨ρ g * (b : B), hb⟩ = (χ g : ℂ) * ω b := by
  let : CStarAlgebra A := {}
  -- Translate one witnessing operator, and compare products and squared absolute values.
  let v (g : G) : A := ⟨ρ g * (a : B), hmem g⟩
  have hvmul (g h : G) : v (g * h) * a = v g * v h := Subtype.ext <| by
    simpa [v, mul_assoc] using congrArg (fun x : B => ρ g * x * (a : B)) (hcomm h).eq
  have hvnorm (g : G) : ‖ω (v g)‖ = ‖ω a‖ := by
    have hvstar : star (v g) * v g = star a * a := Subtype.ext <| by
      simp only [MulMemClass.coe_mul, StarMemClass.coe_star, v, star_mul]
      rw [mul_assoc, ← mul_assoc (star (ρ g)), Unitary.star_mul_self_of_mem (hρ g), one_mul]
    have heq := congrArg (‖ω ·‖) hvstar
    simp only [map_mul, map_star, norm_mul, norm_star] at heq
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp heq
  -- Dividing by the nonzero character value gives a circle-valued homomorphism.
  let c (g : G) : ℂ := ω (v g) / ω a
  have hcmul (g h : G) : c (g * h) = c g * c h := by
    have heq := congrArg ω (hvmul g h)
    simp only [map_mul] at heq
    simp only [c]
    field_simp
    exact heq
  let χ : PontryaginDual G :=
    { toFun g := ⟨c g, mem_sphere_zero_iff_norm.mpr <| by simp [c, hvnorm g, ha]⟩
      map_one' := Circle.ext <| by simp [c, v, ha]
      map_mul' g h := Circle.ext (hcmul g h)
      continuous_toFun :=
        (((CharacterSpace.toCLM ω).continuous.comp
          (hcont.subtype_mk hmem)).div_const (ω a)).subtype_mk _ }
  -- Commutation with the witness determines the multiplier on every admissible operator.
  have hχcoe (g : G) : (χ g : ℂ) = c g := rfl
  have hχ (g : G) (b : A) (hb : ρ g * (b : B) ∈ A) :
      ω ⟨ρ g * (b : B), hb⟩ = (χ g : ℂ) * ω b := by
    have hcross : v g * b = a * ⟨ρ g * (b : B), hb⟩ := Subtype.ext <| by
      simpa [v, mul_assoc] using congrArg (fun x : B => x * (b : B)) (hcomm g).eq
    have heq := congrArg ω hcross
    simp only [map_mul] at heq
    rw [hχcoe, div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination -heq
  refine ⟨χ, hχ, fun ψ hψ => PontryaginDual.ext fun g => Circle.ext ?_⟩
  exact mul_right_cancel₀ ha ((hψ g a (hmem g)).symm.trans (hχ g a (hmem g)))

end TauCeti
