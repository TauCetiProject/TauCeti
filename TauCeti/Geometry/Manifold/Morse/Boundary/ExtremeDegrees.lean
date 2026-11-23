/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Augmentation
public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex

/-!
# Mod-two Morse homology in the extreme degrees

Let `f` be a Morse function on a nonempty compact boundaryless manifold `M` of dimension `n`, and
`X` an adapted pseudo-gradient satisfying the Morse–Smale condition. This file shows that the
mod-two Morse homology of `(f, X)`, the homology of
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`, is nonzero in degrees `0` and `n`.

* In degree `n`, the fundamental chain `TauCeti.morseFundamentalChain`, the sum of the critical
  points of index `n`, is a cycle
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_morseFundamentalChain`). It is
  nonzero because `f` attains its maximum at a critical point of index `n`, and nothing bounds it
  because the complex vanishes in degree `n + 1`.
* In degree `0`, the augmentation, which adds the coefficients of the critical points of index
  `0`, vanishes on boundaries
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseAugmentation_morseBoundary`) and is nonzero
  on a minimum of `f`, so the boundaries form a proper subspace of the chains of degree `0`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `finrank_homology_morseComplex_finrank_pos`: Morse homology is nonzero in the top degree.
* `finrank_homology_morseComplex_zero_pos`: Morse homology is nonzero in degree `0`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex and its homology).
-/

public section

open CategoryTheory Limits Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- A chain of degree `k` whose total Morse boundary vanishes is a cycle of the Morse complex. -/
private theorem morseComplex_d_apply_eq_zero {k j : ℕ}
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = k} →₀ ZMod 2)
    (hc : h.morseBoundary hf (c.mapDomain Subtype.val) = 0) :
    ((h.morseComplex hf).d k j).hom c = 0 := by
  by_cases hkj : k = j + 1
  · subst hkj
    refine (h.morseComplex_d_apply hf j c).trans <|
      Finsupp.mapDomain_injective Subtype.val_injective ?_
    rw [mapDomain_morseBoundaryAt, hc]
    exact Finsupp.mapDomain_zero.symm
  · rw [(h.morseComplex hf).shape _ _ (by simpa [eq_comm] using hkj)]
    rfl

/-- **Morse homology is nonzero in the top degree.** On a nonempty manifold of dimension `n`, the
`n`-th mod-two Morse homology is nonzero: the fundamental chain is a nonzero cycle, and the Morse
complex vanishes in degree `n + 1`. -/
theorem finrank_homology_morseComplex_finrank_pos [Nonempty M] :
    0 < finrank (ZMod 2) ((h.morseComplex hf).homology (finrank ℝ E)) := by
  set K := h.morseComplex hf
  set n := finrank ℝ E
  have : Module.Finite (ZMod 2) (K.sc n).X₂ := h.finite_morseComplex_X hf n
  have := hf.finite_criticalPoints.to_subtype
  -- `f` has a critical point `x` of top index, at a maximum.
  have hcount := hf.criticalCount_finrank_ne_zero
  rw [criticalCount_def] at hcount
  obtain ⟨x, hx, hxn⟩ := nonempty_of_encard_ne_zero hcount
  -- The fundamental chain, as a chain of degree `n`, takes the value `1` everywhere.
  let c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ZMod 2 :=
    Finsupp.equivFunOnFinite.symm 1
  have hcf : c.mapDomain Subtype.val = morseFundamentalChain hf := by
    ext p
    by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = n
    · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective c ⟨p, hp⟩).trans
        (by simp [c, hp, n])
    · rw [Finsupp.mapDomain_of_notMem_range _ _ fun ⟨q, hq⟩ ↦ hp (hq ▸ q.property)]
      simp [hp, n]
  have hc : c ≠ 0 := fun hc0 ↦ by
    have h1 := Finsupp.ext_iff.1 hc0 ⟨⟨x, hx⟩, hxn⟩
    simp [c] at h1
  have hcyc : c ∈ LinearMap.ker (K.sc n).g.hom :=
    h.morseComplex_d_apply_eq_zero hf c (hcf ▸ h.morseBoundary_morseFundamentalChain hf)
  -- Nothing of degree `n + 1` bounds it, so the homology is the space of cycles.
  have hf0 : (K.sc n).f = 0 :=
    (h.isZero_morseComplex_X_of_finrank_lt hf (by rw [ChainComplex.prev]; omega)).eq_of_src _ _
  have hkey := (K.sc n).finrank_homology_add_finrank_range_f
  rw [hf0, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot, add_zero] at hkey
  -- The homology of `K` in degree `n` is by definition that of the short complex `K.sc n`.
  change 0 < finrank (ZMod 2) (K.sc n).homology
  rw [hkey]
  exact Module.finrank_pos_iff_exists_ne_zero.2
    ⟨⟨c, hcyc⟩, fun h0 ↦ hc (congrArg Subtype.val h0)⟩

/-- **Morse homology is nonzero in degree `0`.** On a nonempty manifold, the `0`-th mod-two Morse
homology is nonzero: the augmentation vanishes on boundaries and is nonzero on a minimum of `f`. -/
theorem finrank_homology_morseComplex_zero_pos [Nonempty M] :
    0 < finrank (ZMod 2) ((h.morseComplex hf).homology 0) := by
  -- `f` has a critical point `x` of index `0`, at a minimum.
  have hcount := criticalCount_zero_ne_zero (I := 𝓘(ℝ, E)) (hf.contMDiff.of_le (by norm_cast))
  rw [criticalCount_def] at hcount
  obtain ⟨x, hx, hx0⟩ := nonempty_of_encard_ne_zero hcount
  -- The boundaries of degree `0` are a proper subspace: the augmentation vanishes on them, but
  -- not on the minimum `x`.
  have hne : LinearMap.range ((h.morseComplex hf).d 1 0).hom ≠ ⊤ := fun htop ↦ by
    obtain ⟨y, hy⟩ : ∃ y :
        {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = 0 + 1} →₀ ZMod 2,
        ((h.morseComplex hf).d 1 0).hom y = Finsupp.single ⟨⟨x, hx⟩, hx0⟩ 1 :=
      LinearMap.range_eq_top.1 htop _
    -- The boundary of `y` as a chain of all indices is the minimum `x`.
    have key : h.morseBoundary hf (y.mapDomain Subtype.val) = Finsupp.single ⟨x, hx⟩ 1 := by
      rw [← mapDomain_morseBoundaryAt, ← morseComplex_d_apply]
      exact (congrArg (Finsupp.mapDomain Subtype.val) hy).trans Finsupp.mapDomain_single
    have h1 := congrArg (morseAugmentation f) key
    rw [h.morseAugmentation_morseBoundary hf, morseAugmentation_single] at h1
    simp [hx0] at h1
  have h0 := (h.morseComplex hf).finrank_X_zero
  have hlt := Submodule.finrank_lt hne
  omega

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
