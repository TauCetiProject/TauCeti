/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.GradedIntegral
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# The integral Morse chain complex

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f`, and `𝔬 : TauCeti.MorseOrientation f X` orientations of the unstable manifolds. Whenever the
integral Morse boundary `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary` with coefficients in
a ring `R` squares to zero, its graded pieces
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt` are the differentials of a chain complex
of `R`-modules indexed by `ℕ` (`TauCeti.IsAdaptedPseudoGradient.signedMorseComplex`). Its term in
degree `n` is the free `R`-module on the critical points of index `n`, and its differential from
degree `n + 1` to degree `n` counts the trajectories between critical points with their signs.
Its homology is the Morse homology of `(f, X)` with coefficients in `R`.

The vanishing of `∂ ∘ ∂` is a hypothesis of the construction. By
`IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff` (in the namespace
`TauCeti.IsAdaptedPseudoGradient`) it holds exactly when the signed counts of broken index-two
trajectories vanish. It holds trivially when the boundary vanishes, as for the standard Morse
function on the torus. This file proves it under the Morse–Smale condition on a manifold of
dimension at most two with a unique minimum
(`IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_finrank_le_two`): there the
differential into degree `0` vanishes, and no critical point has index `3` or more. This covers the
moment function on `ℝℙ²` and the sphere `S²` with two maxima. In dimension at most one it holds
for every pseudo-gradient and every choice of orientations, since there are no critical points of
index `2` (`signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_finrank_le_one`).

With coefficients in `ZMod 2` and under the Morse–Smale condition, the integral boundary squares to
zero and the complex is the mod-two Morse complex
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`, whatever the orientations
(`IsMorseSmale.signedMorseComplex_zmod_two`). The complex and its homology vanish above the
dimension of `M`. When the boundary vanishes, the homology in degree `n` is free of rank the number
of critical points of index `n`
(`free_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero` and
`finrank_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero` in the namespace
`TauCeti.IsAdaptedPseudoGradient`). If `f` has a unique critical point of index `0` and the
differential from degree `1` to degree `0` vanishes, the homology in degree `0` is `R`
(`TauCeti.IsAdaptedPseudoGradient.nonempty_linearEquiv_homology_zero_signedMorseComplex`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `signedMorseComplex`: the integral Morse chain complex, with coefficients in a ring `R`.
* `signedMorseComplex_X`, `signedMorseComplex_d_apply`: its terms and differentials.
* `IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_zmod_two`,
  `IsMorseSmale.signedMorseComplex_zmod_two`: modulo two it is the mod-two Morse complex.
* `IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_finrank_le_two`: `∂² = 0`
  in dimension at most two when the minimum is unique.
* `signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_finrank_le_one`: `∂² = 0` in dimension
  at most one.
* `isZero_homology_signedMorseComplex_of_finrank_lt`: the homology vanishes above the dimension.
* `free_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero`,
  `finrank_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero`: with zero boundary, the
  homology is free of rank the number of critical points of each index.
* `nonempty_linearEquiv_homology_zero_signedMorseComplex`: with a unique minimum and zero
  differential into degree `0`, the homology in degree `0` is `R`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients and its homology).
-/

public section

open CategoryTheory Limits Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {𝔬 : MorseOrientation f X}
  {hf : IsMorse 𝓘(ℝ, E) f} {R : Type*} [Ring R]

variable (hX 𝔬 hf R) in
/-- **The integral Morse chain complex.** When the integral Morse boundary with coefficients in
`R` squares to zero, the graded boundaries `signedMorseBoundaryAt` are the differentials of a chain
complex of `R`-modules indexed by `ℕ`. Its term in degree `n` is the free `R`-module on the
critical points of index `n`, and its differential from degree `n + 1` to degree `n` sends a
critical point `p` to the critical points `q` of index `n`, each weighted by the signed count of
the trajectories from `p` to `q`. -/
-- The body is exposed so that the terms of the complex compute to the free modules on the
-- critical points of each index, which the statements of `signedMorseComplex_X` and
-- `signedMorseComplex_d` need.
@[expose]
noncomputable def signedMorseComplex
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) :
    ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (fun n ↦ ModuleCat.of R
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R))
    (fun n ↦ ModuleCat.ofHom (hX.signedMorseBoundaryAt 𝔬 hf R n))
    fun n ↦ by
      rw [← ModuleCat.ofHom_comp,
        (signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff hf).2 hsq n,
        ModuleCat.ofHom_zero]

variable (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0)

/-- The term of the integral Morse chain complex in degree `n` is the free `R`-module on the
critical points of index `n`. -/
@[simp]
theorem signedMorseComplex_X (n : ℕ) :
    (hX.signedMorseComplex 𝔬 hf R hsq).X n = ModuleCat.of R
      ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :=
  (rfl)

/-- The differential of the integral Morse chain complex from degree `n + 1` to degree `n` is the
graded integral Morse boundary. -/
theorem signedMorseComplex_d (n : ℕ) :
    (hX.signedMorseComplex 𝔬 hf R hsq).d (n + 1) n =
      ModuleCat.ofHom (hX.signedMorseBoundaryAt 𝔬 hf R n) := by
  simp [signedMorseComplex]

/-- The differential of the integral Morse chain complex from degree `n + 1` to degree `n`,
applied to a chain, is the graded integral Morse boundary of that chain. -/
@[simp]
theorem signedMorseComplex_d_apply (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) :
    (hX.signedMorseComplex 𝔬 hf R hsq).d (n + 1) n c = hX.signedMorseBoundaryAt 𝔬 hf R n c := by
  rw [signedMorseComplex_d]
  -- Neither `rw [ModuleCat.hom_ofHom]` nor `simp` fires here: the morphism is still typed between
  -- the terms `(signedMorseComplex _).X _`, which are the chain modules only by definition.
  exact ModuleCat.ofHom_apply _ c

/-- The integral Morse chain complex vanishes above the dimension of `M`. -/
theorem isZero_signedMorseComplex_X_of_finrank_lt {n : ℕ} (hn : finrank ℝ E < n) :
    IsZero ((hX.signedMorseComplex 𝔬 hf R hsq).X n) := by
  rw [signedMorseComplex_X, ModuleCat.isZero_iff_subsingleton]
  have : IsEmpty {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} :=
    ⟨fun p ↦ (manifoldMorseIndex_le_finrank.trans_lt hn).ne p.property⟩
  infer_instance

/-- The integral Morse homology vanishes above the dimension of `M`. -/
theorem isZero_homology_signedMorseComplex_of_finrank_lt {n : ℕ} (hn : finrank ℝ E < n) :
    IsZero ((hX.signedMorseComplex 𝔬 hf R hsq).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (isZero_signedMorseComplex_X_of_finrank_lt hsq hn)).isZero_homology

/-- If the total integral Morse boundary vanishes, so does every graded boundary. -/
theorem signedMorseBoundaryAt_eq_zero_of_signedMorseBoundary_eq_zero
    (h0 : hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ) :
    hX.signedMorseBoundaryAt 𝔬 hf R n = 0 :=
  LinearMap.ext fun c ↦ Finsupp.mapDomain_injective Subtype.val_injective <| by
    simp [mapDomain_signedMorseBoundaryAt, h0]

/-- The differential of the integral Morse chain complex from degree `n + 1` to degree `n`
vanishes when the graded boundary from degree `n + 1` to degree `n` does. -/
theorem signedMorseComplex_d_eq_zero_of_signedMorseBoundaryAt_eq_zero (n : ℕ)
    (h0 : hX.signedMorseBoundaryAt 𝔬 hf R n = 0) :
    (hX.signedMorseComplex 𝔬 hf R hsq).d (n + 1) n = 0 := by
  rw [signedMorseComplex_d, h0, ModuleCat.ofHom_zero]
  -- Both sides are the zero morphism; they differ only in how the terms are written.
  rfl

/-- If the total integral Morse boundary vanishes, every differential of the integral Morse chain
complex is zero. -/
theorem signedMorseComplex_d_eq_zero_of_signedMorseBoundary_eq_zero
    (h0 : hX.signedMorseBoundary 𝔬 hf R = 0) (i j : ℕ) :
    (hX.signedMorseComplex 𝔬 hf R hsq).d i j = 0 := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := hij
    exact signedMorseComplex_d_eq_zero_of_signedMorseBoundaryAt_eq_zero hsq j
      (signedMorseBoundaryAt_eq_zero_of_signedMorseBoundary_eq_zero h0 j)
  · exact (hX.signedMorseComplex 𝔬 hf R hsq).shape i j hij

/-- **`∂² = 0` in dimension at most one.** On a manifold of dimension at most one the integral
Morse boundary squares to zero, with coefficients in any ring and whatever the orientations and the
pseudo-gradient: a composite of two graded boundaries starts at critical points of index at least
`2`, and there are none. -/
theorem signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_finrank_le_one
    (hdim : finrank ℝ E ≤ 1) :
    hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  refine (signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff hf).1 fun n ↦ ?_
  have : IsEmpty {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1 + 1} :=
    ⟨fun p ↦ by
      have := manifoldMorseIndex_le_finrank (I := 𝓘(ℝ, E)) (f := f) (x := p.val)
      omega⟩
  exact LinearMap.ext fun c ↦ by simp [Subsingleton.elim c 0]

/-- **Integral Morse homology with zero boundary is free.** If the integral Morse boundary
vanishes, the Morse homology in each degree is a free `R`-module. -/
theorem free_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero
    (h0 : hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ) :
    Module.Free R ((hX.signedMorseComplex 𝔬 hf R hsq).homology n) :=
  have : Module.Free R ((hX.signedMorseComplex 𝔬 hf R hsq).X n) := by
    rw [signedMorseComplex_X]
    exact Module.Free.finsupp R R _
  Module.Free.of_equiv ((hX.signedMorseComplex 𝔬 hf R hsq).XIsoHomologyOfDEqZero n
    (signedMorseComplex_d_eq_zero_of_signedMorseBoundary_eq_zero hsq h0 _ _)
    (signedMorseComplex_d_eq_zero_of_signedMorseBoundary_eq_zero hsq h0 _ _)).toLinearEquiv

/-- **The rank of integral Morse homology with zero boundary.** If the integral Morse boundary
vanishes, the Morse homology in degree `n` has rank the number of critical points of index
`n`. -/
theorem finrank_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero
    [StrongRankCondition R] (h0 : hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ) :
    finrank R ((hX.signedMorseComplex 𝔬 hf R hsq).homology n) =
      (criticalCount 𝓘(ℝ, E) f n).toNat := by
  have := hf.finite_criticalPoints.to_subtype
  let _ := Fintype.ofFinite
    {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}
  rw [(hX.signedMorseComplex 𝔬 hf R hsq).finrank_homology_eq_finrank_X_of_d_eq_zero n
      (signedMorseComplex_d_eq_zero_of_signedMorseBoundary_eq_zero hsq h0 _ _)
      (signedMorseComplex_d_eq_zero_of_signedMorseBoundary_eq_zero hsq h0 _ _),
    signedMorseComplex_X]
  -- The carrier of `ModuleCat.of R A` is `A` itself; rewriting it with `ModuleCat.coe_of` is
  -- blocked by the module instance depending on it.
  refine (finrank_finsupp_self (R := R)).trans ?_
  rw [← Nat.card_eq_fintype_card, natCard_criticalPoints_manifoldMorseIndex_eq_toNat_criticalCount]

/-- **Integral Morse homology in degree `0` with a unique minimum.** If `f` has exactly one
critical point of index `0` and the graded integral boundary into degree `0` vanishes, the integral
Morse homology in degree `0` is `R`: every chain of index `0` is a cycle and none but zero is a
boundary. -/
theorem nonempty_linearEquiv_homology_zero_signedMorseComplex
    (h0 : hX.signedMorseBoundaryAt 𝔬 hf R 0 = 0)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = 0})
    (hp : ∀ q : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = 0}, q = p) :
    Nonempty ((hX.signedMorseComplex 𝔬 hf R hsq).homology 0 ≃ₗ[R] R) :=
  haveI : Subsingleton {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = 0} :=
    ⟨fun q r ↦ (hp q).trans (hp r).symm⟩
  ⟨((hX.signedMorseComplex 𝔬 hf R hsq).XIsoHomologyOfDEqZero 0
    (by
      rw [ChainComplex.prev]
      exact signedMorseComplex_d_eq_zero_of_signedMorseBoundaryAt_eq_zero hsq 0 h0)
    ((hX.signedMorseComplex 𝔬 hf R hsq).shape _ _ (by simp))).toLinearEquiv.symm.trans
    (Finsupp.uniqueLinearEquiv R R p)⟩

namespace IsMorseSmale

variable (h : hX.IsMorseSmale)
include h

/-- **The integral Morse boundary squares to zero modulo two.** Under the Morse–Smale condition,
the integral Morse boundary with coefficients in `ZMod 2` is the mod-two Morse boundary, whatever
the orientations, so it squares to zero. -/
theorem signedMorseBoundary_comp_signedMorseBoundary_zmod_two :
    hX.signedMorseBoundary 𝔬 hf (ZMod 2) ∘ₗ hX.signedMorseBoundary 𝔬 hf (ZMod 2) = 0 :=
  (signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff hf).1 fun n ↦ by
    rw [h.signedMorseBoundaryAt_eq_morseBoundaryAt, h.signedMorseBoundaryAt_eq_morseBoundaryAt,
      h.morseBoundaryAt_comp_morseBoundaryAt]

/-- **The integral Morse complex modulo two is the mod-two Morse complex.** Under the Morse–Smale
condition, the integral Morse chain complex with coefficients in `ZMod 2` is the mod-two Morse
chain complex, whatever the orientations of the unstable manifolds. -/
theorem signedMorseComplex_zmod_two
    (hsq : hX.signedMorseBoundary 𝔬 hf (ZMod 2) ∘ₗ hX.signedMorseBoundary 𝔬 hf (ZMod 2) = 0) :
    hX.signedMorseComplex 𝔬 hf (ZMod 2) hsq = h.morseComplex hf := by
  unfold signedMorseComplex morseComplex
  congr 1
  funext n
  rw [h.signedMorseBoundaryAt_eq_morseBoundaryAt]

/-- **`∂² = 0` on surfaces with a unique minimum.** Under the Morse–Smale condition, on a manifold
of dimension at most two on which `f` has at most one critical point of index `0`, the integral
Morse boundary squares to zero, with coefficients in any ring and whatever the orientations: the
differential from degree `1` to degree `0` vanishes, and no critical point has index `3` or
more. -/
theorem signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_finrank_le_two
    (hdim : finrank ℝ E ≤ 2)
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton) :
    hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  refine (signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff hf).1 fun n ↦ ?_
  cases n with
  | zero => rw [h.signedMorseBoundaryAt_zero_eq_zero_of_unique_index_zero hf hmin,
      LinearMap.zero_comp]
  | succ n =>
    -- There are no chains of index `n + 3`, which exceeds the dimension.
    have : IsEmpty
        {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1 + 1 + 1} :=
      ⟨fun p ↦ by
        have := manifoldMorseIndex_le_finrank (I := 𝓘(ℝ, E)) (f := f) (x := p.val)
        omega⟩
    exact LinearMap.ext fun c ↦ by simp [Subsingleton.elim c 0]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
