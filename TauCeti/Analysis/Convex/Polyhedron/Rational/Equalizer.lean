/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic

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
  [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
  [Module ℝ V] [Module ℝ W] [Module ℝ X]
  [TopologicalSpace V] [TopologicalSpace X]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
  {i : N →+ V} {i' : N' →+ W} {i'' : N'' →+ X}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {h'' : TauCeti.Toric.IsIntegralLattice i''}

/-- The equalizer of rational affine maps is a rational-normal polyhedron,
including when it is empty or either map has a kernel. -/
theorem isRationalNormalPolyhedron_setOf_eq (f g : V →ᵃ[ℝ] W)
    (hf : Toric.IsRationalLinearMap h h' f.linear)
    (hg : Toric.IsRationalLinearMap h h' g.linear) :
    IsRationalNormalPolyhedron h {x | f x = g x} := by
  have := h.finiteDimensional
  have := h'.free
  have := h'.finite
  let b := Module.Free.chooseBasis ℤ N'
  let B := h'.isBaseChange.basis b
  let χ (p : Module.Free.ChooseBasisIndex ℤ N') : W →ₗ[ℝ] ℝ :=
    h'.realCharacter (b.coord p).toAddMonoidHom
  let δ := f - g
  let ψ (p : Module.Free.ChooseBasisIndex ℤ N') : V →ᵃ[ℝ] ℝ :=
    (χ p).toAffineMap.comp δ
  let F (p : Module.Free.ChooseBasisIndex ℤ N') : V →ᴬ[ℝ] ℝ :=
    ⟨ψ p, AffineMap.continuous_linear_iff.1 (ψ p).linear.continuous_of_finiteDimensional⟩
  have hF (p : Module.Free.ChooseBasisIndex ℤ N') :
      Toric.IsRationalFunctional h (F p).toAffineMap.linear :=
    (hf.sub hg).map_functional (Toric.IsRationalFunctional.realCharacter h' (b.coord p))
  have hF_apply (p : Module.Free.ChooseBasisIndex ℤ N') (x : V) :
      F p x = χ p (δ x) := rfl
  have δ_apply (x : V) : δ x = f x - g x := rfl
  have he : {x | f x = g x} = {x | ∀ p, F p x ≤ 0} ∩ {x | ∀ p, (-F p) x ≤ 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro hx
      have hδ : δ x = 0 := sub_eq_zero.mpr hx
      have hzero (p) : χ p (δ x) = 0 := by rw [hδ, map_zero]
      simp only [hF_apply, hzero, ContinuousAffineMap.neg_apply, neg_zero, le_refl,
        implies_true, and_self]
    · rintro ⟨hp, hn⟩
      rw [← sub_eq_zero]
      refine B.ext_elem fun p => ?_
      rw [← Module.Basis.coord_apply, ← h'.realCharacter_coord, map_zero, Finsupp.zero_apply]
      have hle : χ p (δ x) ≤ 0 := by simpa only [hF_apply] using hp p
      have hge : 0 ≤ χ p (δ x) := by
        have := hn p
        rw [ContinuousAffineMap.neg_apply, neg_le, neg_zero, hF_apply] at this
        exact this
      have hz := le_antisymm hle hge
      rw [δ_apply] at hz
      exact hz
  rw [he]
  exact (isRationalNormalPolyhedron_setOf_forall F hF).inter
    (isRationalNormalPolyhedron_setOf_forall (fun p => -F p) fun p => (hF p).neg)

/-- The matching locus of two rational affine maps with a common target is a
rational-normal polyhedron in the product of their source spaces. -/
theorem isRationalNormalPolyhedron_setOf_apply_fst_eq_apply_snd (g : V →ᵃ[ℝ] W)
    (φ : X →ᵃ[ℝ] W) (hg : Toric.IsRationalLinearMap h h' g.linear)
    (hφ : Toric.IsRationalLinearMap h'' h' φ.linear) :
    IsRationalNormalPolyhedron (h.prod h'') {p : V × X | g p.1 = φ p.2} :=
  AffineMap.isRationalNormalPolyhedron_setOf_eq
    (g.comp (AffineMap.fst : V × X →ᵃ[ℝ] V))
    (φ.comp (AffineMap.snd : V × X →ᵃ[ℝ] X))
    (hg.comp (Toric.IsRationalLinearMap.fst h h''))
    (hφ.comp (Toric.IsRationalLinearMap.snd h h''))

end AffineMap
