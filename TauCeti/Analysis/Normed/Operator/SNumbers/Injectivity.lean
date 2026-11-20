/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Bernstein
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Injective and surjective s-number sequences

A metric injection is a linear isometry `J : Y →ₗᵢ[𝕜] Z`, and a metric surjection is a bounded
operator `Q : W →L[𝕜] X` whose underlying bounded additive homomorphism is a normed quotient map
(`NormedAddGroupHom.IsQuotient`). Postcomposing with a metric injection and precomposing with a
metric surjection both leave the operator norm unchanged
(`LinearIsometry.norm_toContinuousLinearMap_comp`,
`ContinuousLinearMap.opNNNorm_comp_of_isQuotient`). An s-number family is *injective* when
postcomposing with metric injections leaves all its terms unchanged, and *surjective* when
precomposing with metric surjections does.

The Gelfand and Bernstein numbers are injective, and the Kolmogorov numbers are surjective, over
every nontrivially normed field. The Bernstein numbers are the smallest injective strict s-number
sequence: `bₙ(T) ≤ sₙ(T)` for every injective strict s-number sequence `s`. If `T` is
`c`-coercive on a subspace `M` of rank `n + 1` with `c > 0`, then `T` maps `M` isomorphically onto
its image `T(M)`, with an inverse of norm at most `c⁻¹`, so strictness on `M` and injectivity
along the inclusion of `T(M)` give `1 = sₙ(id_M) ≤ c⁻¹ sₙ(T|_M) ≤ c⁻¹ sₙ(T)`.

## Main declarations

* `TauCeti.SNumbers.IsInjective`, `TauCeti.SNumbers.IsSurjective`: injective and surjective
  s-number families.
* `TauCeti.SNumbers.isInjective_gelfand`, `TauCeti.SNumbers.isInjective_bernstein`: the Gelfand
  and Bernstein numbers are injective.
* `TauCeti.SNumbers.isSurjective_kolmogorov`: the Kolmogorov numbers are surjective.
* `TauCeti.SNumbers.IsStrictSNumberSequence.bernsteinNumber_le`: `bₙ(T) ≤ sₙ(T)` for every
  injective strict s-number sequence `s`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974).
* A. Pietsch, *Operator Ideals*, North-Holland (1980), Chapter 11.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Injectivity.lean`: an earlier Lean formalization of injective and surjective
  s-numbers.
-/

public section

open scoped NNReal

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- An s-number family is injective when postcomposing with a linear isometry, a metric
injection, leaves every term unchanged. -/
structure IsInjective (s : SNumberFamily 𝕜) : Prop where
  /-- Postcomposing with a linear isometry leaves every term unchanged. -/
  linearIsometry_comp : ∀ {X Y Z : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (J : Y →ₗᵢ[𝕜] Z) (T : X →L[𝕜] Y) (n : ℕ), s (J.toContinuousLinearMap ∘L T) n = s T n

/-- An s-number family is surjective when precomposing with a normed quotient map, a metric
surjection, leaves every term unchanged. -/
structure IsSurjective (s : SNumberFamily 𝕜) : Prop where
  /-- Precomposing with a normed quotient map leaves every term unchanged. -/
  comp_of_isQuotient : ∀ {W X Y : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) {Q : W →L[𝕜] X}, Q.toNormedAddGroupHom.IsQuotient →
      ∀ n : ℕ, s (T ∘L Q) n = s T n

/-- The Gelfand numbers are injective. -/
theorem isInjective_gelfand : IsInjective (gelfand (𝕜 := 𝕜)) :=
  ⟨fun _ _ _ ↦ by simp⟩

/-- The Bernstein numbers are injective. -/
theorem isInjective_bernstein : IsInjective (bernstein (𝕜 := 𝕜)) :=
  ⟨fun _ _ _ ↦ by simp⟩

/-- The Kolmogorov numbers are surjective. -/
theorem isSurjective_kolmogorov : IsSurjective (kolmogorov (𝕜 := 𝕜)) :=
  ⟨fun T _ hQ n ↦ by simpa using T.kolmogorovNumber_comp_of_isQuotient hQ n⟩

/-- **The Bernstein numbers are the smallest injective strict s-numbers.** Every injective
strict s-number sequence `s` satisfies `bₙ(T) ≤ sₙ(T)`. -/
theorem IsStrictSNumberSequence.bernsteinNumber_le {s : SNumberFamily 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : IsInjective s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : T.bernsteinNumber n ≤ s T n := by
  refine ContinuousLinearMap.bernsteinNumber_le_iff.mpr fun M hM c hc ↦ ?_
  rcases eq_or_ne c 0 with rfl | hc0
  · exact zero_le
  have hcpos : 0 < c := pos_iff_ne_zero.mpr hc0
  -- `T` maps `M` onto `N = T(M)` with `‖x‖ ≤ c⁻¹ ‖T x‖`, so it has an inverse `S` of norm `≤ c⁻¹`.
  let N := LinearMap.range ((T : X →ₗ[𝕜] Y) ∘ₗ M.subtype)
  let T₀ : M →L[𝕜] N := (T ∘L M.subtypeL).codRestrict N fun x ↦ ⟨x, rfl⟩
  have hT₀ : Function.Surjective T₀ := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hC (x : M) : ‖x‖ ≤ (c⁻¹ : ℝ≥0) * ‖T₀ x‖ := by
    rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff₀' (NNReal.coe_pos.mpr hcpos)]
    -- Submodules carry the ambient norm, and `T₀ x = T x` by `codRestrict`.
    exact_mod_cast hc x x.2
  let S : N →L[𝕜] M := T₀.inverse
  have hST : S ∘L T₀ = ContinuousLinearMap.id 𝕜 M :=
    (ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le hT₀ hC).inverse_comp_self
  have hS : ‖S‖₊ ≤ c⁻¹ := by
    rw [← NNReal.coe_le_coe, coe_nnNorm]
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le hT₀ hC)
  have hsT₀ : s T₀ n ≤ s T n := by
    -- Including `T(M)` back into `Y` undoes `codRestrict`, by definition.
    have hfac : N.subtypeₗᵢ.toContinuousLinearMap ∘L T₀ = T ∘L M.subtypeL := rfl
    rw [← hinj.linearIsometry_comp N.subtypeₗᵢ, hfac]
    exact (hs.comp_le_right T M.subtypeL n).trans <|
      mul_le_of_le_one_right' (by exact_mod_cast Submodule.norm_subtypeL_le M)
  have hM' : (n : Cardinal) < Module.rank 𝕜 M := by
    rw [hM]
    exact_mod_cast n.lt_succ_self
  calc c = c * s (S ∘L T₀) n := by rw [hST, hs.normalize_of_lt_rank n hM', mul_one]
    _ ≤ c * (‖S‖₊ * s T₀ n) := by
      gcongr
      exact hs.comp_le_left S T₀ n
    _ ≤ c * (c⁻¹ * s T n) := by gcongr
    _ = s T n := by rw [mul_inv_cancel_left₀ hc0]

end TauCeti.SNumbers
