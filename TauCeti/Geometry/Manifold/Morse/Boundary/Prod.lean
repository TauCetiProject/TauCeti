/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod

/-!
# The mod-two Morse complex of a product manifold

Let `f` be a Morse function on a compact boundaryless manifold `M` and `g` one on `N`, with
Morse–Smale adapted pseudo-gradients `X` and `Y`. The product field `(X, Y)` is a Morse–Smale
pseudo-gradient adapted to the separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N`
(`TauCeti.IsAdaptedPseudoGradient.prod`, `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`), so
the product has a mod-two Morse boundary. This file computes it: the mod-two Morse complex of the
product is the tensor product of the mod-two Morse complexes of the factors.

The critical points of the separated sum are the pairs `(p, q)` of critical points
(`TauCeti.criticalPointsCompFstAddCompSndEquiv`), of index `ind p + ind q`. Its flow is the
product of the two flows, so a trajectory from `(p, q)` to `(p', q')` is a pair of trajectories,
from `p` to `p'` and from `q` to `q'`. Under the Morse–Smale condition the index drops strictly
along a nonconstant trajectory, so if the index of the pair drops by one, one of the two
components is constant: either `p = p'` and the trajectory is a trajectory of `Y` from `q` to
`q'`, or `q = q'` and it is a trajectory of `X`. On the middle level
these are read off by projecting to the moving factor. Hence the boundary coefficients of the
product are

`⟨∂ (p, q), (p', q')⟩ = [p = p'] ⟨∂ q, q'⟩ + [q = q'] ⟨∂ p, p'⟩`,

and on chains `∂ (p ⊗ q) = ∂ p ⊗ q + p ⊗ ∂ q`. Over `ZMod 2` there is no Koszul sign.

The Morse boundary is defined for manifolds modelled on a normed space `F` with the model
`𝓘(ℝ, F)`, so the product `M × N` is charted by the products of charts with values in `E × E'`
(`TauCeti.chartedSpaceProd` and `TauCeti.isManifold_chartedSpaceProd`, local instances), as for the
product pseudo-gradient. This is the manifold form of
`TauCeti.morseChainSeparatedSumEquiv_comp_morseBoundary`, which treats negative-gradient flows of
separated sums on inner product spaces.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_left` and
  `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_right`: trajectories of the product
  field in which one component is a critical point are trajectories of the other factor.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseTrajectorySlice_prod_eq_empty`: under the
  Morse–Smale condition no trajectory between critical points whose index differs by one moves
  both components.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeff_prod`: the boundary
  coefficients of the product.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_prod_single`: the boundary of a
  pair of critical points.
* `TauCeti.morseChainProdEquiv` and
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_morseBoundary`: the
  mod-two Morse chains of the product are the tensor product of the mod-two Morse chains of the
  factors, and the boundary corresponds to `∂ ⊗ 1 + 1 ⊗ ∂`.

## References

* M. Hutchings, *Lecture notes on Morse homology*, 2002, §3, Exercise 2 (the Morse complex of a
  product is the tensor product of the Morse complexes).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
-/

public section

open Set
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
  [ChartedSpace E' N] {f : M → ℝ} {g : N → ℝ}

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

/-! ### Trajectories -/

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {X : (z : M) → TangentSpace 𝓘(ℝ, E) z} {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}
  (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)

/-- **Trajectories of a product field that are constant in the first factor.** Between pairs with
the same critical point `x` of `f` in the first factor, the trajectories of `(X, Y)` are the
trajectories of `Y`, on the middle level. -/
theorem morseTrajectorySlice_prod_left {x : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (q q' : N) :
    (hX.prod hY).morseTrajectorySlice (x, q) (x, q') =
      (fun y ↦ (x, y)) '' hY.morseTrajectorySlice q q' := by
  ext z
  -- The membership lemma is applied to `hX.prod hY` explicitly: the topology on `E` inside the
  -- product charts is found by another instance path, which defeats rewriting with the generic
  -- form of the lemma.
  rw [(hX.prod hY).mem_morseTrajectorySlice, hX.unstableSet_prod hY, hX.stableSet_prod hY]
  simp only [mem_prod, Pi.add_apply, Function.comp_apply, mem_image, mem_morseTrajectorySlice]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₁ := (hX.mem_unstableSet_inter_stableSet_self_iff hx).1 ⟨hu₁, hs₁⟩
    rw [hz₁] at hz
    exact ⟨z.2, ⟨hu₂, hs₂, by linarith⟩, Prod.ext hz₁.symm rfl⟩
  · rintro ⟨y, ⟨hu, hs, hy⟩, rfl⟩
    have hxx := (hX.mem_unstableSet_inter_stableSet_self_iff hx (y := x)).2 rfl
    refine ⟨⟨hxx.1, hu⟩, ⟨hxx.2, hs⟩, ?_⟩
    dsimp only
    linarith

/-- **Trajectories of a product field that are constant in the second factor.** Between pairs with
the same critical point `y` of `g` in the second factor, the trajectories of `(X, Y)` are the
trajectories of `X`, on the middle level. -/
theorem morseTrajectorySlice_prod_right {y : N} (hy : mfderiv 𝓘(ℝ, E') 𝓘(ℝ) g y = 0) (p p' : M) :
    (hX.prod hY).morseTrajectorySlice (p, y) (p', y) =
      (fun x ↦ (x, y)) '' hX.morseTrajectorySlice p p' := by
  ext z
  rw [(hX.prod hY).mem_morseTrajectorySlice, hX.unstableSet_prod hY, hX.stableSet_prod hY]
  simp only [mem_prod, Pi.add_apply, Function.comp_apply, mem_image, mem_morseTrajectorySlice]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₂ := (hY.mem_unstableSet_inter_stableSet_self_iff hy).1 ⟨hu₂, hs₂⟩
    rw [hz₂] at hz
    exact ⟨z.1, ⟨hu₁, hs₁, by linarith⟩, Prod.ext rfl hz₂.symm⟩
  · rintro ⟨x, ⟨hu, hs, hx⟩, rfl⟩
    have hyy := (hY.mem_unstableSet_inter_stableSet_self_iff hy (y := y)).2 rfl
    refine ⟨⟨hu, hyy.1⟩, ⟨hs, hyy.2⟩, ?_⟩
    dsimp only
    linarith

omit hX hY in
/-- **No trajectory of index one moves both components.** For Morse–Smale `X` and `Y`, if the sum
of the indices drops by at most one from `(p, q)` to `(p', q')` with `p ≠ p'` and `q ≠ q'`, there is
no trajectory of `(X, Y)` between them: each component would lower the index of its factor by at
least one. -/
theorem IsMorseSmale.morseTrajectorySlice_prod_eq_empty {hX : IsAdaptedPseudoGradient f X}
    {hY : IsAdaptedPseudoGradient g Y} (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g) {p p' : M} {q q' : N} (hpp' : p ≠ p')
    (hqq' : q ≠ q')
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q ≤
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1) :
    (hX.prod hY).morseTrajectorySlice (p, q) (p', q') = ∅ := by
  refine eq_empty_of_forall_notMem fun z hz ↦ ?_
  rw [(hX.prod hY).mem_morseTrajectorySlice, hX.unstableSet_prod hY, hX.stableSet_prod hY] at hz
  simp only [mem_prod] at hz
  obtain ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, -⟩ := hz
  have h₁ := hXs.manifoldMorseIndex_lt hf hpp' ⟨z.1, hu₁, hs₁⟩
  have h₂ := hYs.manifoldMorseIndex_lt hg hqq' ⟨z.2, hu₂, hs₂⟩
  omega

/-! ### The boundary -/

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} {hY : IsAdaptedPseudoGradient g Y}
  (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (hg : IsMorse 𝓘(ℝ, E') g)

omit [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N] in
include hf hg in
/-- At a pair of critical points of Morse functions, the index of the separated sum is the sum of
the indices. -/
private theorem manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm
    (p : criticalPoints 𝓘(ℝ, E) f) (q : criticalPoints 𝓘(ℝ, E') g) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)
        ((criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable hY.mdifferentiable).symm
          (p, q) : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q := by
  rw [coe_criticalPointsCompFstAddCompSndEquiv_symm]
  exact manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd
    ((isManifoldNondegenerateCriticalPoint_iff _).1
      (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2))).contDiffAt
    ((isManifoldNondegenerateCriticalPoint_iff _).1
      (hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2))).contDiffAt

open scoped Classical in
/-- **The boundary coefficients of a product.** The coefficient of `(p', q')` in the mod-two Morse
boundary of `(p, q)` counts the trajectories of `Y` from `q` to `q'` when `p = p'`, and the
trajectories of `X` from `p` to `p'` when `q = q'`; it vanishes when both components differ. -/
theorem morseBoundaryCoeff_prod (p p' : criticalPoints 𝓘(ℝ, E) f)
    (q q' : criticalPoints 𝓘(ℝ, E') g) :
    (hXs.prod hYs).morseBoundaryCoeff (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        ((criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable hY.mdifferentiable).symm (p, q))
        ((criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable hY.mdifferentiable).symm
          (p', q')) =
      (if p = p' then hYs.morseBoundaryCoeff hg q q' else 0) +
        if q = q' then hXs.morseBoundaryCoeff hf p p' else 0 := by
  have hindP := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm (hX := hX) (hY := hY)
    hf hg p q
  have hindQ := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm (hX := hX) (hY := hY)
    hf hg p' q'
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  swap
  · -- The index does not drop by one, so every coefficient vanishes.
    rw [(hXs.prod hYs).morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _
      (by rw [hindP, hindQ]; exact hind)]
    have h₁ : (if p = p' then hYs.morseBoundaryCoeff hg q q' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact hYs.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ (by omega)
      · rfl
    have h₂ : (if q = q' then hXs.morseBoundaryCoeff hf p p' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact hXs.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ (by omega)
      · rfl
    rw [h₁, h₂, add_zero]
  rw [(hXs.prod hYs).morseBoundaryCoeff_eq_ncard _ (by rw [hindP, hindQ]; exact hind)]
  simp only [coe_criticalPointsCompFstAddCompSndEquiv_symm]
  by_cases hpp : p = p'
  · subst hpp
    have hqq : q ≠ q' := by rintro rfl; omega
    rw [hX.morseTrajectorySlice_prod_left hY (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2),
      ncard_image_of_injective _ (Prod.mk_right_injective _),
      hYs.morseBoundaryCoeff_eq_ncard hg (p := q) (q := q') (by omega)]
    simp [hqq]
  by_cases hqq : q = q'
  · subst hqq
    rw [hX.morseTrajectorySlice_prod_right hY (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2),
      ncard_image_of_injective _ (Prod.mk_left_injective _),
      hXs.morseBoundaryCoeff_eq_ncard hf (p := p) (q := p') (by omega)]
    simp [hpp]
  rw [hXs.morseTrajectorySlice_prod_eq_empty hYs hf hg (fun h ↦ hpp (Subtype.ext h))
      (fun h ↦ hqq (Subtype.ext h)) hind.le, ncard_empty, Nat.cast_zero]
  simp [hpp, hqq]

/-- **The boundary of a pair of critical points** is `∂ (p, q) = (∂ p, q) + (p, ∂ q)`: the sum of
the boundary of `p` paired with `q` and of `p` paired with the boundary of `q`. -/
theorem morseBoundary_prod_single (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) (a : ZMod 2) :
    (hXs.prod hYs).morseBoundary (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        (Finsupp.single
          ((criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable hY.mdifferentiable).symm
            (p, q)) a) =
      Finsupp.mapDomain
          (fun p' ↦ (criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable
            hY.mdifferentiable).symm (p', q))
          (hXs.morseBoundary hf (Finsupp.single p a)) +
        Finsupp.mapDomain
          (fun q' ↦ (criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable
            hY.mdifferentiable).symm (p, q'))
          (hYs.morseBoundary hg (Finsupp.single q a)) := by
  classical
  set e := criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable hY.mdifferentiable
  ext Q
  obtain ⟨⟨p', q'⟩, rfl⟩ := e.symm.surjective Q
  have hinjL : Function.Injective fun p' ↦ e.symm (p', q) :=
    e.symm.injective.comp (Prod.mk_left_injective q)
  have hinjR : Function.Injective fun q' ↦ e.symm (p, q') :=
    e.symm.injective.comp (Prod.mk_right_injective p)
  -- Read off each image of `mapDomain`: it is the corresponding coefficient on the range, and `0`
  -- off it.
  have hL : Finsupp.mapDomain (fun p' ↦ e.symm (p', q))
      (hXs.morseBoundary hf (Finsupp.single p a)) (e.symm (p', q')) =
        if q = q' then a * hXs.morseBoundaryCoeff hf p p' else 0 := by
    split_ifs with h
    · subst h
      rw [Finsupp.mapDomain_apply_of_injective hinjL, hXs.morseBoundary_single_apply]
    · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨p'', hp''⟩
      exact h (congrArg Prod.snd (e.symm.injective hp''))
  have hR : Finsupp.mapDomain (fun q' ↦ e.symm (p, q'))
      (hYs.morseBoundary hg (Finsupp.single q a)) (e.symm (p', q')) =
        if p = p' then a * hYs.morseBoundaryCoeff hg q q' else 0 := by
    split_ifs with h
    · subst h
      rw [Finsupp.mapDomain_apply_of_injective hinjR, hYs.morseBoundary_single_apply]
    · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨q'', hq''⟩
      exact h (congrArg Prod.fst (e.symm.injective hq''))
  rw [Finsupp.add_apply, hL, hR, (hXs.prod hYs).morseBoundary_single_apply,
    morseBoundaryCoeff_prod hXs hYs hf hg, mul_add]
  split_ifs <;> simp [add_comm]

end IsMorseSmale

end IsAdaptedPseudoGradient

/-! ### Chains -/

/-- **The mod-two Morse chains of a separated sum are the tensor product** of the mod-two Morse
chains of the summands: the pair `(p, q)` of critical points corresponds to `p ⊗ q`. -/
noncomputable def morseChainProdEquiv (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    (criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) →₀ ZMod 2) ≃ₗ[ZMod 2]
      (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) ⊗[ZMod 2] (criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) :=
  (Finsupp.domLCongr (criticalPointsCompFstAddCompSndEquiv hf hg)).trans
    (finsuppTensorFinsupp' (ZMod 2) _ _).symm

/-- The chain `a • (p, q)` corresponds to `a • p ⊗ q`. -/
@[simp]
theorem morseChainProdEquiv_single (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) (a : ZMod 2) :
    morseChainProdEquiv hf hg
        (Finsupp.single ((criticalPointsCompFstAddCompSndEquiv hf hg).symm (p, q)) a) =
      Finsupp.single p a ⊗ₜ Finsupp.single q 1 := by
  simp [morseChainProdEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

/-- Pairing a chain of `f` with a fixed critical point of `g` corresponds to its tensor product
with that critical point. -/
private theorem morseChainProdEquiv_mapDomain_left (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (q : criticalPoints 𝓘(ℝ, E') g)
    (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :
    morseChainProdEquiv hf hg
        (Finsupp.mapDomain (fun p' ↦ (criticalPointsCompFstAddCompSndEquiv hf hg).symm (p', q))
          c) =
      c ⊗ₜ Finsupp.single q 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.add_tmul]
  | single p' b => rw [Finsupp.mapDomain_single, morseChainProdEquiv_single]

/-- Pairing a fixed critical point of `f` with a chain of `g` corresponds to its tensor product
with that critical point. -/
private theorem morseChainProdEquiv_mapDomain_right (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (p : criticalPoints 𝓘(ℝ, E) f)
    (c : criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) :
    morseChainProdEquiv hf hg
        (Finsupp.mapDomain (fun q' ↦ (criticalPointsCompFstAddCompSndEquiv hf hg).symm (p, q'))
          c) =
      Finsupp.single p 1 ⊗ₜ c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.tmul_add]
  | single q' b =>
    rw [Finsupp.mapDomain_single, morseChainProdEquiv_single, ← mul_one b, ← smul_eq_mul,
      ← Finsupp.smul_single, ← Finsupp.smul_single, TensorProduct.smul_tmul]

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {X : (z : M) → TangentSpace 𝓘(ℝ, E) z} {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}
  {hX : IsAdaptedPseudoGradient f X} {hY : IsAdaptedPseudoGradient g Y}

/-- **The Künneth formula for the mod-two Morse complex of a product manifold.** Under the
identification of the mod-two Morse chains of the product with the tensor product of the chains of
the factors, the Morse boundary of the product field `(X, Y)` is `∂ ⊗ 1 + 1 ⊗ ∂`. -/
theorem morseChainProdEquiv_comp_morseBoundary (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g) :
    (morseChainProdEquiv hX.mdifferentiable hY.mdifferentiable).toLinearMap ∘ₗ
        (hXs.prod hYs).morseBoundary (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) =
      ((hXs.morseBoundary hf).rTensor (criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) +
          (hYs.morseBoundary hg).lTensor (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2)) ∘ₗ
        (morseChainProdEquiv hX.mdifferentiable hY.mdifferentiable).toLinearMap := by
  refine Finsupp.lhom_ext fun P a ↦ ?_
  obtain ⟨⟨p, q⟩, rfl⟩ :=
    (criticalPointsCompFstAddCompSndEquiv hX.mdifferentiable hY.mdifferentiable).symm.surjective P
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    morseBoundary_prod_single hXs hYs hf hg, map_add, morseChainProdEquiv_mapDomain_left,
    morseChainProdEquiv_mapDomain_right, morseChainProdEquiv_single, LinearMap.add_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  congr 1
  rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, ← Finsupp.smul_single, map_smul,
    TensorProduct.smul_tmul]

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
