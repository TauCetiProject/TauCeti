/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import TauCeti.RingTheory.Isocrystal.SemistableComplex
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Tactic.NormNum

/-!
# Checks for the semistable complex

These examples evaluate `TauCeti.semistableComplexD₀`, `TauCeti.semistableComplexD₁` and the
rescaling chain map `TauCeti.semistableComplexRescale` on the two-dimensional Frobenius–monodromy
datum of a semistable point at `p = 2`: `D = E = ℚ e₀ ⊕ ℚ e₁`, written `ℚ × ℚ`, with `φ e₀ = e₀`,
`φ e₁ = 2 e₁`, `N e₁ = e₀`, `N e₀ = 0` and `ι = id`. It satisfies `N φ = 2 φ N`.

* `N (1 - φ / 2 ^ r) e₁ = (1 - 2 ^ (1 - r)) e₀` for every `r : ℤ`, which is also the value of the
  lower map `1 - φ / 2 ^ (r - 1)` on `N e₁`; reusing `1 - φ / 2 ^ r` below would give
  `(1 - 2 ^ (-r)) e₀` instead.
* The values `D₁ (e₁, 0, 0) = e₀` and `D₁ (0, 0, e₀) = e₀` in weight `0`, and `D₁ (0, 0, e₁) = e₁`
  in weight `1`, separately detect the `N` term, the sign of the subtraction and the lower exponent.
* In weight `0` the lower map is `1 - 2 φ`: the image of `e₁` is `(-e₁, e₁, e₀)`, and `D₁` kills it.
* For the normalized monodromy `-N / e` with `e = 2`, the first differential sends `e₁` to
  `(-e₁, e₁, -e₀ / 2)`, and the second sends `(e₁, 0, 0)` to `-e₀ / 2` rather than `e₀`; a
  sign-only change of convention would give `-e₀`.
* With `N = 0` rescaling leaves both differentials unchanged, but the chain map still multiplies the
  last term by `-1 / e`, so it is not the identity.
* At `e = 0` the convention `0⁻¹ = 0` scales `N` to zero. Both chain-map squares still hold, but the
  chain map kills the last term of a nonzero complex, so it is not an isomorphism.
-/

public section

open CategoryTheory TauCeti

namespace TauCeti.SemistableComplexChecks

/-- The Frobenius `φ e₀ = e₀`, `φ e₁ = 2 e₁`. -/
noncomputable def frob : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ := LinearMap.id.prodMap ((2 : ℚ) • LinearMap.id)

/-- The monodromy `N e₀ = 0`, `N e₁ = e₀`. -/
noncomputable def mono : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ := LinearMap.inl ℚ ℚ ℚ ∘ₗ LinearMap.snd ℚ ℚ ℚ

@[simp] lemma frob_apply (x : ℚ × ℚ) : frob x = (x.1, 2 * x.2) := by simp [frob]

@[simp] lemma mono_apply (x : ℚ × ℚ) : mono x = (x.2, 0) := by simp [mono]

/-- The datum satisfies the Frobenius–monodromy relation `N φ = 2 φ N`. -/
lemma mono_comp_frob : mono ∘ₗ frob = (2 : ℚ) • (frob ∘ₗ mono) := by
  ext <;> simp

-- `N (1 - φ / 2 ^ r) e₁ = (1 - 2 ^ (1 - r)) e₀`, the value of the lower map on `N e₁ = e₀`.
example (r : ℤ) :
    mono ((0, 1) - (2 : ℚ) ^ (-r) • frob (0, 1)) = ((1 : ℚ) - 2 ^ (1 - r)) • ((1, 0) : ℚ × ℚ) ∧
      mono (0, 1) - (2 : ℚ) ^ (1 - r) • frob (mono (0, 1)) =
        ((1 : ℚ) - 2 ^ (1 - r)) • ((1, 0) : ℚ × ℚ) := by
  have h : ((2 : ℚ) ^ r)⁻¹ * 2 = 2 ^ (1 - r) := by
    rw [zpow_sub₀ two_ne_zero, zpow_one, div_eq_inv_mul]
  refine ⟨?_, ?_⟩ <;> ext <;> simp [h]

-- `D₁ (e₁, 0, 0) = e₀` and `D₁ (0, 0, e₀) = e₀` in weight `0`.
example : semistableComplexD₁ (2 : ℚ) 0 frob mono (E := ℚ × ℚ) ((0, 1), 0, 0) = (1, 0) ∧
    semistableComplexD₁ (2 : ℚ) 0 frob mono (E := ℚ × ℚ) (0, 0, (1, 0)) = (1, 0) := by
  refine ⟨?_, ?_⟩ <;> ext <;> norm_num

-- `D₁ (0, 0, e₁) = e₁` in weight `1`.
example : semistableComplexD₁ (2 : ℚ) 1 frob mono (E := ℚ × ℚ) (0, 0, (0, 1)) = (0, 1) := by
  ext <;> norm_num

-- In weight `0` the image of `e₁` is `(-e₁, e₁, e₀)`, and `D₁` kills it.
example : semistableComplexD₀ (2 : ℚ) 0 frob LinearMap.id mono (0, 1) = ((0, -1), (0, 1), (1, 0)) ∧
    semistableComplexD₁ (2 : ℚ) 0 frob mono (E := ℚ × ℚ) ((0, -1), (0, 1), (1, 0)) = 0 := by
  refine ⟨?_, ?_⟩ <;> ext <;> norm_num

-- The normalized monodromy `-N / 2`: `D₀ e₁ = (-e₁, e₁, -e₀ / 2)` and `D₁ (e₁, 0, 0) = -e₀ / 2`.
example :
    semistableComplexD₀ (2 : ℚ) 0 frob LinearMap.id (-(2 : ℚ)⁻¹ • mono) (0, 1) =
        ((0, -1), (0, 1), (-1 / 2, 0)) ∧
      semistableComplexD₁ (2 : ℚ) 0 frob (-(2 : ℚ)⁻¹ • mono) (E := ℚ × ℚ) ((0, 1), 0, 0) =
        (-1 / 2, 0) := by
  refine ⟨?_, ?_⟩ <;> ext <;> norm_num

-- With `N = 0` rescaling changes neither differential, yet the chain map scales the last term.
example (r : ℤ) :
    semistableComplexD₀ (2 : ℚ) r frob LinearMap.id (-(2 : ℚ)⁻¹ • (0 : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ)) =
        semistableComplexD₀ (2 : ℚ) r frob LinearMap.id 0 ∧
      semistableComplexD₁ (2 : ℚ) r frob (-(2 : ℚ)⁻¹ • (0 : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ)) (E := ℚ × ℚ) =
        semistableComplexD₁ (2 : ℚ) r frob 0 ∧
      (semistableComplexRescale (r := r) (ι := LinearMap.id) (two_ne_zero : (2 : ℚ) ≠ 0)
        (by simp : (0 : ℚ × ℚ →ₗ[ℚ] ℚ × ℚ) ∘ₗ frob = (2 : ℚ) • (frob ∘ₗ 0))
          (-(2 : ℚ)⁻¹)).τ₃.hom (1, 0) ≠ (1, 0) := by
  refine ⟨by simp, by simp, ?_⟩
  simp only [semistableComplexRescale_τ₃, ModuleCat.hom_ofHom, LinearMap.smul_apply,
    LinearMap.id_apply, ne_eq]
  rw [Prod.ext_iff]
  norm_num

-- At `e = 0` the monodromy is scaled to zero: `D₀ e₁ = (-e₁, e₁, 0)`, which `D₁` kills.
example : semistableComplexD₀ (2 : ℚ) 0 frob LinearMap.id (-(0 : ℚ)⁻¹ • mono) (0, 1) =
      ((0, -1), (0, 1), 0) ∧
    semistableComplexD₁ (2 : ℚ) 0 frob (-(0 : ℚ)⁻¹ • mono) (E := ℚ × ℚ) ((0, -1), (0, 1), 0) =
      0 := by
  refine ⟨?_, ?_⟩ <;> ext <;> norm_num

-- At `e = 0` the rescaling chain map is not an isomorphism: it kills `e₀` in the last term.
example : ¬ IsIso (semistableComplexRescale (r := 0) (ι := LinearMap.id)
    (two_ne_zero : (2 : ℚ) ≠ 0) mono_comp_frob (-(0 : ℚ)⁻¹)) := by
  rw [ShortComplex.isIso_iff]
  rintro ⟨-, -, h₃⟩
  have h := (ModuleCat.mono_iff_injective (semistableComplexRescale (r := 0) (ι := LinearMap.id)
    (two_ne_zero : (2 : ℚ) ≠ 0) mono_comp_frob (-(0 : ℚ)⁻¹)).τ₃).mp inferInstance
    (a₁ := ((1, 0) : ℚ × ℚ)) (a₂ := 0)
  simp [Prod.ext_iff] at h

end TauCeti.SemistableComplexChecks
