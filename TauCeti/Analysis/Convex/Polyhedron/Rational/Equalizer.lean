/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Cone
public import TauCeti.Geometry.Toric.Algebraic.RationalFunctional

/-!
# Rational affine equalizers

The locus where two affine maps with rational linear parts agree is a closed
rational-normal polyhedron. Real offsets and noninjective maps are allowed.
These equalizers impose the matching equation in a pullback of semilinear families.

Adapted from `Mei/Geometry/Convex/Polyhedron/Rational/Equalizer.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

open TauCeti

namespace AffineMap

variable {N N' N'' V W X : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [NormedAddCommGroup V] [AddCommGroup W] [NormedAddCommGroup X]
  [NormedSpace ℝ V] [Module ℝ W] [NormedSpace ℝ X]
  {i : N →+ V} {i' : N' →+ W} {i'' : N'' →+ X}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- The equalizer of rational affine maps is a rational-normal polyhedron,
including when it is empty or either map has a kernel. -/
theorem isRationalNormalPolyhedron_equalizer (f g : V →ᵃ[ℝ] W)
    (hf : Toric.IsRationalLinearMap h h' f.linear)
    (hg : Toric.IsRationalLinearMap h h' g.linear) :
    IsRationalNormalPolyhedron h {x | f x = g x} := by
  have := h.finiteDimensional
  have := h'.finiteDimensional
  let b := Module.finBasis ℝ W
  let _ : NormedAddCommGroup W :=
    NormedAddCommGroup.induced W (Fin (Module.finrank ℝ W) → ℝ) b.equivFun b.equivFun.injective
  let _ : NormedSpace ℝ W := NormedSpace.induced ℝ W (Fin (Module.finrank ℝ W) → ℝ) b.equivFun
  let δ : V →ᴬ[ℝ] W :=
    ⟨f - g, (f - g).continuous_of_finiteDimensional⟩
  have hδ : Toric.IsRationalLinearMap h h' δ.toAffineMap.linear := by
    simpa only [δ, AffineMap.sub_linear] using hf.sub hg
  have he : δ ⁻¹' {0} = {x | f x = g x} := by
    ext x
    simp [δ, sub_eq_zero]
  rw [← he]
  exact (isRationalNormalPolyhedron_singleton h' (0 : W)).preimage δ hδ

/-- The matching locus of two rational affine maps with a common target is a
rational-normal polyhedron in the product of their source spaces. -/
theorem isRationalNormalPolyhedron_pullback_matching (g : V →ᵃ[ℝ] W)
    (φ : X →ᵃ[ℝ] W) (hg : Toric.IsRationalLinearMap h h' g.linear)
    (hφ : Toric.IsRationalLinearMap h'' h' φ.linear) :
    IsRationalNormalPolyhedron (h.prod h'') {p : V × X | g p.1 = φ p.2} :=
  AffineMap.isRationalNormalPolyhedron_equalizer
    (g.comp (AffineMap.fst : V × X →ᵃ[ℝ] V))
    (φ.comp (AffineMap.snd : V × X →ᵃ[ℝ] X))
    (hg.comp (Toric.IsRationalLinearMap.fst h h''))
    (hφ.comp (Toric.IsRationalLinearMap.snd h h''))

end AffineMap
