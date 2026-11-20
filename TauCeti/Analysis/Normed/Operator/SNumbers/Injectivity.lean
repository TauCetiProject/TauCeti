/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Bernstein
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov

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
  ⟨fun J T n ↦ by simpa using T.gelfandNumber_linearIsometry_comp J n⟩

/-- The Bernstein numbers are injective. -/
theorem isInjective_bernstein : IsInjective (bernstein (𝕜 := 𝕜)) :=
  ⟨fun J T n ↦ by simpa using T.bernsteinNumber_linearIsometry_comp J n⟩

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
  -- `T` is injective on `M`, hence an isomorphism `e` of `M` onto `T(M)`.
  have hTinj : Function.Injective ((T : X →ₗ[𝕜] Y) ∘ₗ M.subtype) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    have hTx : T x = 0 := by simpa using hx
    simpa [hTx, hc0] using hc x x.2
  let N := LinearMap.range ((T : X →ₗ[𝕜] Y) ∘ₗ M.subtype)
  let e : M ≃ₗ[𝕜] N := LinearEquiv.ofInjective _ hTinj
  have hinv (y : N) : ‖e.symm y‖₊ ≤ c⁻¹ * ‖y‖₊ := by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [e.symm_apply_apply, le_inv_mul_iff₀ hcpos]
    -- Submodules carry the ambient norm, and `e x = T x` by `LinearEquiv.ofInjective`.
    exact hc x x.2
  let E : M ≃L[𝕜] N := e.toContinuousLinearEquivOfBounds ‖T‖ c⁻¹
    (fun x ↦ T.le_opNorm x) fun y ↦ by exact_mod_cast hinv y
  let T₀ : M →L[𝕜] N := E
  let S : N →L[𝕜] M := E.symm
  have hST : S ∘L T₀ = ContinuousLinearMap.id 𝕜 M := E.coe_symm_comp_coe
  have hS : ‖S‖₊ ≤ c⁻¹ := ContinuousLinearMap.opNNNorm_le_bound _ _ hinv
  have hT₀ : s T₀ n ≤ s T n := by
    -- `E` is `e` together with its continuity, so `E x = e x` by `LinearEquiv.ofInjective`.
    have hfac : N.subtypeₗᵢ.toContinuousLinearMap ∘L T₀ = T ∘L M.subtypeL := by
      ext x
      exact LinearEquiv.ofInjective_apply (h := hTinj) (x := x)
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
