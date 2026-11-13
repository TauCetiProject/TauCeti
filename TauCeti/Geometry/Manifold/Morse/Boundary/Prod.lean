/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# The Künneth formula for the mod-two Morse complex of a product manifold

Let `f` be a Morse function on a compact boundaryless manifold `M` modelled on a finite-dimensional
real normed space `E`, with a Morse–Smale adapted pseudo-gradient `X`, and let `g` and `Y` be the
same data on `N`, modelled on `E'`. With `M × N` charted on `E × E'`
(`TauCeti.chartedSpaceProd`), the product field `(X, Y)` is a Morse–Smale pseudo-gradient
adapted to `f ∘ Prod.fst + g ∘ Prod.snd` (`TauCeti.IsAdaptedPseudoGradient.prod` and
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`), so it has a mod-two Morse boundary. This file
computes it: the mod-two Morse complex of the product is the tensor product of the mod-two Morse
complexes of the factors.

The critical points of the separated sum are the pairs `(p, q)` of critical points, of index
`ind p + ind q`. Its flow is the product of the two flows, so a trajectory from `(p, q)` to
`(p', q')` is a pair of trajectories, from `p` to `p'` and from `q` to `q'`. Under the Morse–Smale
condition the index drops strictly along a nonconstant trajectory, so if the index of the pair
drops by one, one of the two components is constant: either `p = p'` and the trajectory is one of
`Y` from `q` to `q'` with `ind q = ind q' + 1`, or `q = q'` and it is one of `X`. On the middle
level these are read off from the moving factor. Hence the boundary coefficients of the product are

`⟨∂ (p, q), (p', q')⟩ = [p = p'] ⟨∂ q, q'⟩ + [q = q'] ⟨∂ p, p'⟩`,

and on chains `∂ (p ⊗ q) = ∂ p ⊗ q + p ⊗ ∂ q`. Over `ZMod 2` there is no Koszul sign.

This is the manifold form of `TauCeti.Analysis.Calculus.Morse.Boundary.Prod`, which treats
separated sums on Euclidean spaces.

## Main declarations

* `TauCeti.criticalPointsProdEquiv`: the critical points of the separated sum are the pairs of
  critical points.
* `TauCeti.morseChainProdEquiv`: the mod-two Morse chains of the separated sum are the tensor
  product of the mod-two Morse chains of `f` and `g`.
* `TauCeti.IsAdaptedPseudoGradient.prod_morseTrajectorySlice_left` and
  `TauCeti.IsAdaptedPseudoGradient.prod_morseTrajectorySlice_right`: trajectories in which one
  component is constant are trajectories of the other factor.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod_morseTrajectorySlice_eq_empty`: under the
  Morse–Smale condition no trajectory between critical points whose index differs by one moves both
  components.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod_morseBoundaryCoeff`: the boundary coefficients
  of the product.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod_morseBoundary_single`: the boundary of a pair
  of critical points.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_prod_morseBoundary`:
  **the Künneth formula**, `∂ = ∂ ⊗ 1 + 1 ⊗ ∂` on the tensor product of the chains.

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

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace E' N] [IsManifold 𝓘(ℝ, E') ∞ N]
  [CompactSpace N] [T2Space N]
  {f : M → ℝ} {g : N → ℝ}
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {Y : (y : N) → TangentSpace 𝓘(ℝ, E') y}

/-! ### Critical points -/

/-- **The critical points of a separated sum are the pairs of critical points.** -/
noncomputable def criticalPointsProdEquiv (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) ≃
      criticalPoints 𝓘(ℝ, E) f × criticalPoints 𝓘(ℝ, E') g where
  toFun P :=
    have h := (mem_criticalPoints_comp_fst_add_comp_snd_iff_chartedSpaceProd hf hg).1 P.2
    (⟨P.1.1, h.1⟩, ⟨P.1.2, h.2⟩)
  invFun pq := ⟨(pq.1.1, pq.2.1),
    (mem_criticalPoints_comp_fst_add_comp_snd_iff_chartedSpaceProd hf hg).2 ⟨pq.1.2, pq.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N] in
/-- The critical point of the separated sum attached to a pair `(p, q)` is the point `(p, q)`. -/
@[simp]
theorem coe_criticalPointsProdEquiv_symm (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g)
    (pq : criticalPoints 𝓘(ℝ, E) f × criticalPoints 𝓘(ℝ, E') g) :
    ((criticalPointsProdEquiv hf hg).symm pq : M × N) = ((pq.1 : M), (pq.2 : N)) :=
  (rfl)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N] in
/-- The first component of a critical point of the separated sum. -/
@[simp]
theorem coe_criticalPointsProdEquiv_fst (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g)
    (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) :
    ((criticalPointsProdEquiv hf hg P).1 : M) = (P : M × N).1 :=
  (rfl)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N] in
/-- The second component of a critical point of the separated sum. -/
@[simp]
theorem coe_criticalPointsProdEquiv_snd (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g)
    (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) :
    ((criticalPointsProdEquiv hf hg P).2 : N) = (P : M × N).2 :=
  (rfl)

/-- **The mod-two Morse chains of a separated sum are the tensor product** of the mod-two Morse
chains of the summands: the pair `(p, q)` of critical points corresponds to `p ⊗ q`. -/
noncomputable def morseChainProdEquiv (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    (criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) →₀ ZMod 2) ≃ₗ[ZMod 2]
      (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) ⊗[ZMod 2] (criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) :=
  (Finsupp.domLCongr (criticalPointsProdEquiv hf hg)).trans
    (finsuppTensorFinsupp' (ZMod 2) _ _).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N] in
/-- The chain `a • (p, q)` corresponds to `a • p ⊗ q`. -/
@[simp]
theorem morseChainProdEquiv_single (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) (a : ZMod 2) :
    morseChainProdEquiv hf hg (Finsupp.single ((criticalPointsProdEquiv hf hg).symm (p, q)) a) =
      Finsupp.single p a ⊗ₜ Finsupp.single q 1 := by
  simp [morseChainProdEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N] in
/-- Pairing a chain of `f` with a fixed critical point of `g` corresponds to its tensor product
with that critical point. -/
private theorem morseChainProdEquiv_mapDomain_left (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (q : criticalPoints 𝓘(ℝ, E') g)
    (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :
    morseChainProdEquiv hf hg
        (Finsupp.mapDomain (fun p' ↦ (criticalPointsProdEquiv hf hg).symm (p', q)) c) =
      c ⊗ₜ Finsupp.single q 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.add_tmul]
  | single p' b => rw [Finsupp.mapDomain_single, morseChainProdEquiv_single]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  [T2Space M] [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace N] [T2Space N] in
/-- Pairing a fixed critical point of `f` with a chain of `g` corresponds to its tensor product
with that critical point. -/
private theorem morseChainProdEquiv_mapDomain_right (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (p : criticalPoints 𝓘(ℝ, E) f)
    (c : criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) :
    morseChainProdEquiv hf hg
        (Finsupp.mapDomain (fun q' ↦ (criticalPointsProdEquiv hf hg).symm (p, q')) c) =
      Finsupp.single p 1 ⊗ₜ c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.tmul_add]
  | single q' b =>
    rw [Finsupp.mapDomain_single, morseChainProdEquiv_single, ← mul_one b,
      ← smul_eq_mul, ← Finsupp.smul_single, ← Finsupp.smul_single, TensorProduct.smul_tmul]

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)
  (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)

/-! ### Trajectories -/

/-- **Trajectories of a product that are constant in the first factor.** Between pairs with the
same critical point `x` of `f` in the first factor, the trajectories of the product field are the
trajectories of `Y`, on the middle level. -/
theorem prod_morseTrajectorySlice_left {x : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (q q' : N) :
    (hX.prod hY).morseTrajectorySlice (x, q) (x, q') =
      (fun z ↦ (x, z)) '' hY.morseTrajectorySlice q q' := by
  have hxx : x ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet x :=
    ⟨Flow.self_mem_unstableSet_iff.2 (hX.flow_apply_of_mfderiv_eq_zero hx),
      Flow.self_mem_stableSet_iff.2 (hX.flow_apply_of_mfderiv_eq_zero hx)⟩
  ext z
  obtain ⟨z₁, z₂⟩ := z
  simp only [(hX.prod hY).mem_morseTrajectorySlice, mem_morseTrajectorySlice,
    unstableSet_prod hX hY, stableSet_prod hX hY, mem_prod, mem_image, Pi.add_apply,
    Function.comp_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    obtain rfl := hX.eq_of_mem_unstableSet_inter_stableSet ⟨hu₁, hs₁⟩
    exact ⟨z₂, ⟨hu₂, hs₂, by linarith⟩, rfl, rfl⟩
  · rintro ⟨z, ⟨hu, hs, hz⟩, rfl, rfl⟩
    exact ⟨⟨hxx.1, hu⟩, ⟨hxx.2, hs⟩, by linarith⟩

/-- **Trajectories of a product that are constant in the second factor.** Between pairs with the
same critical point `y` of `g` in the second factor, the trajectories of the product field are the
trajectories of `X`, on the middle level. -/
theorem prod_morseTrajectorySlice_right {y : N} (hy : mfderiv 𝓘(ℝ, E') 𝓘(ℝ) g y = 0) (p p' : M) :
    (hX.prod hY).morseTrajectorySlice (p, y) (p', y) =
      (fun z ↦ (z, y)) '' hX.morseTrajectorySlice p p' := by
  have hyy : y ∈ hY.flow.unstableSet y ∩ hY.flow.stableSet y :=
    ⟨Flow.self_mem_unstableSet_iff.2 (hY.flow_apply_of_mfderiv_eq_zero hy),
      Flow.self_mem_stableSet_iff.2 (hY.flow_apply_of_mfderiv_eq_zero hy)⟩
  ext z
  obtain ⟨z₁, z₂⟩ := z
  simp only [(hX.prod hY).mem_morseTrajectorySlice, mem_morseTrajectorySlice,
    unstableSet_prod hX hY, stableSet_prod hX hY, mem_prod, mem_image, Pi.add_apply,
    Function.comp_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    obtain rfl := hY.eq_of_mem_unstableSet_inter_stableSet ⟨hu₂, hs₂⟩
    exact ⟨z₁, ⟨hu₁, hs₁, by linarith⟩, rfl, rfl⟩
  · rintro ⟨z, ⟨hu, hs, hz⟩, rfl, rfl⟩
    exact ⟨⟨hu, hyy.1⟩, ⟨hs, hyy.2⟩, by linarith⟩

variable {hX hY} in
include hf hg in
/-- **No trajectory of index one moves both components.** For Morse–Smale `X` and `Y`, if the
index of the separated sum drops by one from `(p, q)` to `(p', q')` with `p ≠ p'` and `q ≠ q'`,
there is no trajectory between them: each component would lower the index of its factor by at
least one. -/
theorem IsMorseSmale.prod_morseTrajectorySlice_eq_empty (hXs : hX.IsMorseSmale)
    (hYs : hY.IsMorseSmale) {p p' : M} {q q' : N} (hpp' : p ≠ p') (hqq' : q ≠ q')
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1) :
    (hX.prod hY).morseTrajectorySlice (p, q) (p', q') = ∅ := by
  refine eq_empty_of_forall_notMem fun z hz ↦ ?_
  simp only [(hX.prod hY).mem_morseTrajectorySlice, unstableSet_prod hX hY,
    stableSet_prod hX hY, mem_prod] at hz
  obtain ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, -⟩ := hz
  have h₁ := hXs.manifoldMorseIndex_lt hf hpp' ⟨z.1, hu₁, hs₁⟩
  have h₂ := hYs.manifoldMorseIndex_lt hg hqq' ⟨z.2, hu₂, hs₂⟩
  omega

/-! ### The boundary -/

namespace IsMorseSmale

variable {hX hY} (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale)

open scoped Classical in
/-- **The boundary coefficients of a product.** The coefficient of `(p', q')` in the mod-two Morse
boundary of `(p, q)` counts the trajectories of `Y` from `q` to `q'` when `p = p'`, and the
trajectories of `X` from `p` to `p'` when `q = q'`; it vanishes when both components differ. -/
theorem prod_morseBoundaryCoeff (p p' : criticalPoints 𝓘(ℝ, E) f)
    (q q' : criticalPoints 𝓘(ℝ, E') g) :
    (hXs.prod hYs).morseBoundaryCoeff (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        ((criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable).symm (p, q))
        ((criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable).symm (p', q')) =
      (if p = p' then hYs.morseBoundaryCoeff hg q q' else 0) +
        if q = q' then hXs.morseBoundaryCoeff hf p p' else 0 := by
  set e := criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable
  have hp := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2)
  have hp' := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 p'.2)
  have hq := hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2)
  have hq' := hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 q'.2)
  have hindP :
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p, q) : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q :=
    hp.manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd hq
  have hindQ :
      manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) (e.symm (p', q') : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' :=
    hp'.manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd hq'
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  swap
  · -- The index does not drop by one, so every coefficient vanishes.
    rw [(hXs.prod hYs).morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one
      (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
      (by rw [hindP, hindQ]; exact hind)]
    have h₁ : (if p = p' then hYs.morseBoundaryCoeff hg q q' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ _ (by omega)
      · rfl
    have h₂ : (if q = q' then hXs.morseBoundaryCoeff hf p p' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ _ (by omega)
      · rfl
    rw [h₁, h₂, add_zero]
  rw [(hXs.prod hYs).morseBoundaryCoeff_eq_ncard (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
      (by rw [hindP, hindQ]; exact hind),
    coe_criticalPointsProdEquiv_symm, coe_criticalPointsProdEquiv_symm]
  by_cases hpp : p = p'
  · subst hpp
    have hqq : q ≠ q' := by rintro rfl; omega
    rw [prod_morseTrajectorySlice_left hX hY
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2),
      ncard_image_of_injective _ (Prod.mk_right_injective _),
      morseBoundaryCoeff_eq_ncard hYs hg (p := q) (q := q') (by omega)]
    simp [hqq]
  by_cases hqq : q = q'
  · subst hqq
    rw [prod_morseTrajectorySlice_right hX hY
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2),
      ncard_image_of_injective _ (Prod.mk_left_injective _),
      morseBoundaryCoeff_eq_ncard hXs hf (p := p) (q := p') (by omega)]
    simp [hpp]
  rw [hXs.prod_morseTrajectorySlice_eq_empty hf hg hYs (fun h ↦ hpp (Subtype.ext h))
      (fun h ↦ hqq (Subtype.ext h)) hind, ncard_empty, Nat.cast_zero]
  simp [hpp, hqq]

/-- **The boundary of a pair of critical points** is `∂ (p, q) = (∂ p, q) + (p, ∂ q)`: the sum of
the boundary of `p` paired with `q` and of `p` paired with the boundary of `q`. -/
theorem prod_morseBoundary_single (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) (a : ZMod 2) :
    (hXs.prod hYs).morseBoundary (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        (Finsupp.single ((criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable).symm
          (p, q)) a) =
      Finsupp.mapDomain
          (fun p' ↦ (criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable).symm (p', q))
          (hXs.morseBoundary hf (Finsupp.single p a)) +
        Finsupp.mapDomain
          (fun q' ↦ (criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable).symm (p, q'))
          (hYs.morseBoundary hg (Finsupp.single q a)) := by
  classical
  set e := criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable
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
      rw [Finsupp.mapDomain_apply_of_injective hinjL, morseBoundary_single_apply]
    · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨p'', hp''⟩
      exact h (congrArg Prod.snd (e.symm.injective hp''))
  have hR : Finsupp.mapDomain (fun q' ↦ e.symm (p, q'))
      (hYs.morseBoundary hg (Finsupp.single q a)) (e.symm (p', q')) =
        if p = p' then a * hYs.morseBoundaryCoeff hg q q' else 0 := by
    split_ifs with h
    · subst h
      rw [Finsupp.mapDomain_apply_of_injective hinjR, morseBoundary_single_apply]
    · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨q'', hq''⟩
      exact h (congrArg Prod.fst (e.symm.injective hq''))
  rw [Finsupp.add_apply, hL, hR,
    (hXs.prod hYs).morseBoundary_single_apply (hf.comp_fst_add_comp_snd_chartedSpaceProd hg),
    hXs.prod_morseBoundaryCoeff hf hg hYs, mul_add]
  split_ifs <;> simp [add_comm]

/-- **The Künneth formula for the mod-two Morse complex.** Under the identification of the mod-two
Morse chains of `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N` with the tensor product of the chains of
`f` and of `g`, the Morse boundary of the product pseudo-gradient `(X, Y)` is `∂ ⊗ 1 + 1 ⊗ ∂`. -/
theorem morseChainProdEquiv_comp_prod_morseBoundary :
    (morseChainProdEquiv hf.mdifferentiable hg.mdifferentiable).toLinearMap ∘ₗ
        (hXs.prod hYs).morseBoundary (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) =
      ((hXs.morseBoundary hf).rTensor _ + (hYs.morseBoundary hg).lTensor _) ∘ₗ
        (morseChainProdEquiv hf.mdifferentiable hg.mdifferentiable).toLinearMap := by
  refine Finsupp.lhom_ext fun P a ↦ ?_
  obtain ⟨⟨p, q⟩, rfl⟩ :=
    (criticalPointsProdEquiv hf.mdifferentiable hg.mdifferentiable).symm.surjective P
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    hXs.prod_morseBoundary_single hf hg hYs, map_add, morseChainProdEquiv_mapDomain_left,
    morseChainProdEquiv_mapDomain_right, morseChainProdEquiv_single, LinearMap.add_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  congr 1
  rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, ← Finsupp.smul_single, map_smul,
    TensorProduct.smul_tmul]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
