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
  let r (a : Module.Free.ChooseBasisIndex ℤ N' × Bool) : V →ᴬ[ℝ] ℝ :=
    if a.2 = true then -F a.1 else F a.1
  have hF (p : Module.Free.ChooseBasisIndex ℤ N') :
      Toric.IsRationalFunctional h (F p).toAffineMap.linear :=
    (hf.sub hg).map_functional (Toric.IsRationalFunctional.realCharacter h' (b.coord p))
  have hr (a : Module.Free.ChooseBasisIndex ℤ N' × Bool) :
      Toric.IsRationalFunctional h (r a).toAffineMap.linear := by
    obtain ⟨p, s⟩ := a
    cases s with
    | false => exact hF p
    | true => exact (hF p).neg
  have heval (p) (s : Bool) (x : V) :
      r (p, s) x = if s = true then -(χ p) (δ x) else (χ p) (δ x) := by
    have hψ : (F p) x = (χ p) (δ x) := by
      rw [show χ p (δ x) = (ψ p).linear x + (ψ p) 0 by
        change χ p (δ x) = χ p (δ.linear x) + χ p (δ 0)
        rw [← map_add]
        congr 1
        exact congrFun δ.decomp x]
      exact congrFun (ψ p).decomp x
    cases s
    · exact hψ
    · change -(F p) x = -(χ p) (δ x)
      rw [hψ]
  have he : {x | f x = g x} = {x | ∀ a, r a x ≤ 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Prod.forall, heval]
    constructor
    · intro hx p s
      have hzero : δ x = 0 := sub_eq_zero.mpr hx
      have hz : χ p (δ x) = 0 := by rw [hzero, map_zero]
      cases s <;> simp [hz]
    · intro hx
      have hzero (p) : χ p (δ x) = 0 := by
        have hp := hx p false
        have hn := hx p true
        simp only [Bool.false_eq_true, ↓reduceIte] at hp hn
        have hn' := neg_le.mp hn
        rw [neg_zero] at hn'
        exact le_antisymm hp hn'
      change f x = g x
      rw [← sub_eq_zero]
      refine B.ext_elem fun p => ?_
      rw [← Module.Basis.coord_apply, ← h'.realCharacter_coord]
      change χ p (f x - g x) = (B.repr 0) p
      rw [map_zero, Finsupp.zero_apply]
      exact hzero p
  rw [he]
  exact isRationalNormalPolyhedron_setOf_forall r hr

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
