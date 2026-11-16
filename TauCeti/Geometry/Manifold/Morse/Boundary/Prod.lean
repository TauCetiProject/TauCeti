/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod
import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# The mod-two Morse complex of a product of compact manifolds

Let `f` be a Morse function on a compact boundaryless manifold `M` and `g` one on `N`, charted on
finite-dimensional normed spaces `E` and `E'`, with Morse–Smale adapted pseudo-gradients `X` and
`Y`. The product field `(x, y) ↦ (X x, Y y)` is a Morse–Smale pseudo-gradient adapted to the
separated sum `f ∘ Prod.fst + g ∘ Prod.snd` on `M × N`, read in the product charts with values
in the normed space `E × E'` (`TauCeti.chartedSpaceProd`,
`TauCeti.IsAdaptedPseudoGradient.prod`, `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`), so
it has a mod-two Morse boundary. This file computes it: the mod-two Morse complex of the product is
the tensor product of the mod-two Morse complexes of the factors.

The critical points of the separated sum are the pairs `(p, q)` of critical points, of index
`ind p + ind q`, and the flow of the product field is the product of the two flows. So a trajectory
from `(p, q)` to `(p', q')` is a pair of trajectories, from `p` to `p'` and from `q` to `q'`. Under
the Morse–Smale condition the index drops strictly along a nonconstant trajectory, so if the index
of the pair drops by one, one of the two components is constant: either `p = p'` and the trajectory
is a trajectory of `Y` from `q` to `q'`, or `q = q'` and it is a trajectory of `X`. Hence the
boundary coefficients of the product are

`⟨∂ (p, q), (p', q')⟩ = [p = p'] ⟨∂ q, q'⟩ + [q = q'] ⟨∂ p, p'⟩`,

and on chains `∂ (p ⊗ q) = ∂ p ⊗ q + p ⊗ ∂ q`. Over `ZMod 2` there is no Koszul sign.

This is the manifold form of `TauCeti.Analysis.Calculus.Morse.Boundary.Prod`, which treats
separated sums on Euclidean spaces.

## Main declarations

* `TauCeti.criticalPointsProdEquiv`: the critical points of the separated sum are the pairs of
  critical points.
* `TauCeti.morseChainProdEquiv`: the mod-two Morse chains of the separated sum are the tensor
  product of the mod-two Morse chains of the summands.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseTrajectorySlice_prod_left`, `morseTrajectorySlice_prod_right`: trajectories in which one
  component is constant are trajectories of the other factor.
* `IsMorseSmale.morseTrajectorySlice_prod_eq_empty`: under the Morse–Smale condition no trajectory
  between critical points whose indices differ by one moves both components.
* `IsMorseSmale.morseBoundaryCoeff_prod`: the boundary coefficients of the product.
* `IsMorseSmale.morseChainProdEquiv_comp_morseBoundary`: the boundary of the product corresponds to
  `∂ ⊗ 1 + 1 ⊗ ∂`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 2 (the Morse complex of a product is the tensor
  product of the Morse complexes).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
-/

public section

open Set
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

attribute [local instance low] chartedSpaceProd
attribute [local instance] isManifold_chartedSpaceProd

variable {E E' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N]
  {f : M → ℝ} {g : N → ℝ}

/-- **The critical points of a separated sum are the pairs of critical points**, as an
equivalence of the critical sets. -/
noncomputable def criticalPointsProdEquiv (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) ≃
      criticalPoints 𝓘(ℝ, E) f × criticalPoints 𝓘(ℝ, E') g where
  toFun P :=
    have h := (criticalPoints_comp_fst_add_comp_snd_chartedSpaceProd hf hg ▸ P.2 :
      (P : M × N) ∈ _ ×ˢ _)
    (⟨(P : M × N).1, h.1⟩, ⟨(P : M × N).2, h.2⟩)
  invFun pq := ⟨((pq.1 : M), (pq.2 : N)),
    (criticalPoints_comp_fst_add_comp_snd_chartedSpaceProd hf hg).symm ▸ ⟨pq.1.2, pq.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The critical point of the separated sum attached to a pair `(p, q)` is the point `(p, q)`. -/
@[simp]
theorem coe_criticalPointsProdEquiv_symm (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g)
    (pq : criticalPoints 𝓘(ℝ, E) f × criticalPoints 𝓘(ℝ, E') g) :
    ((criticalPointsProdEquiv hf hg).symm pq : M × N) = ((pq.1 : M), (pq.2 : N)) :=
  (rfl)

/-- The first component of a critical point of the separated sum. -/
@[simp]
theorem coe_criticalPointsProdEquiv_fst (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g)
    (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) :
    ((criticalPointsProdEquiv hf hg P).1 : M) = (P : M × N).1 :=
  (rfl)

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
    (finsuppTensorFinsupp' (ZMod 2) (criticalPoints 𝓘(ℝ, E) f) (criticalPoints 𝓘(ℝ, E') g)).symm

/-- The chain `a • (p, q)` corresponds to `a • p ⊗ q`. -/
@[simp]
theorem morseChainProdEquiv_single (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) (a : ZMod 2) :
    morseChainProdEquiv hf hg (Finsupp.single ((criticalPointsProdEquiv hf hg).symm (p, q)) a) =
      Finsupp.single p a ⊗ₜ Finsupp.single q 1 := by
  simp [morseChainProdEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- The Morse index of the separated sum at the pair `(p, q)` is the sum of the Morse indices of `p`
and `q`. -/
theorem manifoldMorseIndex_criticalPointsProdEquiv_symm (hf : IsMorse 𝓘(ℝ, E) f)
    (hg : IsMorse 𝓘(ℝ, E') g)
    (pq : criticalPoints 𝓘(ℝ, E) f × criticalPoints 𝓘(ℝ, E') g) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)
        ((criticalPointsProdEquiv (hf.contMDiff.mdifferentiable (by simp))
          (hg.contMDiff.mdifferentiable (by simp))).symm pq : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f pq.1 + manifoldMorseIndex 𝓘(ℝ, E') g pq.2 := by
  rw [coe_criticalPointsProdEquiv_symm]
  have hp := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 pq.1.2)
  exact hp.manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd
    (hg.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 pq.2.2))

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E') ∞ N]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {Y : (y : N) → TangentSpace 𝓘(ℝ, E') y}

variable [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)
  (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g)

namespace IsAdaptedPseudoGradient

/-- **Trajectories of the product that are constant in the first factor.** Between pairs with the
same critical point `x` of `f` in the first factor, the trajectories of the product pseudo-gradient
are the trajectories of `Y`, on the middle level. -/
theorem morseTrajectorySlice_prod_left {x : M} (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (q q' : N) :
    (hX.prod hY).morseTrajectorySlice (x, q) (x, q') =
      (fun y ↦ (x, y)) '' hY.morseTrajectorySlice q q' := by
  have hfix := hX.flow_apply_of_mfderiv_eq_zero hx
  ext z
  rw [(hX.prod hY).mem_morseTrajectorySlice (p := (x, q)) (q := (x, q')) (z := z)]
  simp only [unstableSet_prod hX hY, stableSet_prod hX hY, mem_prod, mem_image,
    mem_morseTrajectorySlice, Pi.add_apply, Function.comp_apply]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₁ : z.1 = x := hX.eq_of_mem_unstableSet_inter_stableSet ⟨hu₁, hs₁⟩
    refine ⟨z.2, ⟨hu₂, hs₂, by rw [hz₁] at hz; linarith⟩, ?_⟩
    rw [← hz₁]
  · rintro ⟨y, ⟨hu, hs, hy⟩, rfl⟩
    have hxu : x ∈ hX.flow.unstableSet x := Flow.self_mem_unstableSet_iff.2 hfix
    have hxs : x ∈ hX.flow.stableSet x := Flow.self_mem_stableSet_iff.2 hfix
    exact ⟨⟨hxu, hu⟩, ⟨hxs, hs⟩, by simp only; linarith⟩

/-- **Trajectories of the product that are constant in the second factor.** Between pairs with the
same critical point `y` of `g` in the second factor, the trajectories of the product pseudo-gradient
are the trajectories of `X`, on the middle level. -/
theorem morseTrajectorySlice_prod_right {y : N} (hy : mfderiv 𝓘(ℝ, E') 𝓘(ℝ) g y = 0) (p p' : M) :
    (hX.prod hY).morseTrajectorySlice (p, y) (p', y) =
      (fun x ↦ (x, y)) '' hX.morseTrajectorySlice p p' := by
  have hfix := hY.flow_apply_of_mfderiv_eq_zero hy
  ext z
  rw [(hX.prod hY).mem_morseTrajectorySlice (p := (p, y)) (q := (p', y)) (z := z)]
  simp only [unstableSet_prod hX hY, stableSet_prod hX hY, mem_prod, mem_image,
    mem_morseTrajectorySlice, Pi.add_apply, Function.comp_apply]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₂ : z.2 = y := hY.eq_of_mem_unstableSet_inter_stableSet ⟨hu₂, hs₂⟩
    refine ⟨z.1, ⟨hu₁, hs₁, by rw [hz₂] at hz; linarith⟩, ?_⟩
    rw [← hz₂]
  · rintro ⟨x, ⟨hu, hs, hx⟩, rfl⟩
    have hyu : y ∈ hY.flow.unstableSet y := Flow.self_mem_unstableSet_iff.2 hfix
    have hys : y ∈ hY.flow.stableSet y := Flow.self_mem_stableSet_iff.2 hfix
    exact ⟨⟨hu, hyu⟩, ⟨hs, hys⟩, by simp only; linarith⟩

variable {hX hY}

include hf hg in
/-- **No trajectory of index one moves both components.** For Morse–Smale `X` and `Y`, if the
index of the separated sum drops by one from `(p, q)` to `(p', q')` with `p ≠ p'` and `q ≠ q'`,
there is no trajectory between them. -/
theorem IsMorseSmale.morseTrajectorySlice_prod_eq_empty (h₁ : hX.IsMorseSmale)
    (h₂ : hY.IsMorseSmale) {p p' : M} {q q' : N} (hpp' : p ≠ p') (hqq' : q ≠ q')
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1) :
    (hX.prod hY).morseTrajectorySlice (p, q) (p', q') = ∅ := by
  -- Each component of a trajectory would lower the index of its factor by at least one.
  refine eq_empty_of_forall_notMem fun z hz ↦ ?_
  rw [(hX.prod hY).mem_morseTrajectorySlice (p := (p, q)) (q := (p', q')) (z := z)] at hz
  simp only [unstableSet_prod hX hY, stableSet_prod hX hY, mem_prod] at hz
  obtain ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, -⟩ := hz
  have i₁ := h₁.manifoldMorseIndex_lt hf hpp' ⟨z.1, hu₁, hs₁⟩
  have i₂ := h₂.manifoldMorseIndex_lt hg hqq' ⟨z.2, hu₂, hs₂⟩
  omega

namespace IsMorseSmale

variable (h₁ : hX.IsMorseSmale) (h₂ : hY.IsMorseSmale)

open scoped Classical in
/-- **The boundary coefficients of the product.** The coefficient of `(p', q')` in the mod-two Morse
boundary of `(p, q)` counts the trajectories of `Y` from `q` to `q'` when `p = p'`, and those of
`X` from `p` to `p'` when `q = q'`; it vanishes when both components differ. -/
theorem morseBoundaryCoeff_prod (p p' : criticalPoints 𝓘(ℝ, E) f)
    (q q' : criticalPoints 𝓘(ℝ, E') g) :
    (h₁.prod h₂).morseBoundaryCoeff (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        ((criticalPointsProdEquiv (hf.contMDiff.mdifferentiable (by simp))
          (hg.contMDiff.mdifferentiable (by simp))).symm (p, q))
        ((criticalPointsProdEquiv (hf.contMDiff.mdifferentiable (by simp))
          (hg.contMDiff.mdifferentiable (by simp))).symm (p', q')) =
      (if p = p' then h₂.morseBoundaryCoeff hg q q' else 0) +
        if q = q' then h₁.morseBoundaryCoeff hf p p' else 0 := by
  have hindP := manifoldMorseIndex_criticalPointsProdEquiv_symm hf hg (p, q)
  have hindQ := manifoldMorseIndex_criticalPointsProdEquiv_symm hf hg (p', q')
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  swap
  · -- The index does not drop by one, so every coefficient vanishes.
    rw [(h₁.prod h₂).morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _
      (by rw [hindP, hindQ]; exact hind)]
    have e₁ : (if p = p' then h₂.morseBoundaryCoeff hg q q' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ _ (by omega)
      · rfl
    have e₂ : (if q = q' then h₁.morseBoundaryCoeff hf p p' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ _ (by omega)
      · rfl
    rw [e₁, e₂, add_zero]
  rw [(h₁.prod h₂).morseBoundaryCoeff_eq_ncard _ (by rw [hindP, hindQ]; exact hind),
    coe_criticalPointsProdEquiv_symm, coe_criticalPointsProdEquiv_symm]
  by_cases hpp : p = p'
  · subst hpp
    have hqq : q ≠ q' := by rintro rfl; omega
    rw [morseTrajectorySlice_prod_left hX hY
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2),
      ncard_image_of_injective _ (Prod.mk_right_injective _),
      h₂.morseBoundaryCoeff_eq_ncard hg (p := q) (q := q') (by omega)]
    simp [hqq]
  by_cases hqq : q = q'
  · subst hqq
    rw [morseTrajectorySlice_prod_right hX hY
        (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2),
      ncard_image_of_injective _ (Prod.mk_left_injective _),
      h₁.morseBoundaryCoeff_eq_ncard hf (p := p) (q := p') (by omega)]
    simp [hpp]
  rw [h₁.morseTrajectorySlice_prod_eq_empty hf hg h₂ (fun h ↦ hpp (Subtype.ext h))
      (fun h ↦ hqq (Subtype.ext h)) hind, ncard_empty, Nat.cast_zero]
  simp [hpp, hqq]

/-- **The Künneth formula for the mod-two Morse complex of a product.** Under the identification
`TauCeti.morseChainProdEquiv` of the mod-two Morse chains of the separated sum with the tensor
product of the chains of `f` and of `g`, the Morse boundary of the product pseudo-gradient is
`∂ ⊗ 1 + 1 ⊗ ∂`. -/
theorem morseChainProdEquiv_comp_morseBoundary :
    (morseChainProdEquiv (hf.contMDiff.mdifferentiable (by simp))
        (hg.contMDiff.mdifferentiable (by simp))).toLinearMap ∘ₗ
      (h₁.prod h₂).morseBoundary
        (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) =
      ((h₁.morseBoundary hf).rTensor (criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) +
          (h₂.morseBoundary hg).lTensor (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2)) ∘ₗ
        (morseChainProdEquiv (hf.contMDiff.mdifferentiable (by simp))
          (hg.contMDiff.mdifferentiable (by simp))).toLinearMap := by
  classical
  refine domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_lTensor _
    fun p p' q q' ↦ ?_
  rw [morseBoundary_single_apply, morseBoundary_single_apply,
    (h₁.prod h₂).morseBoundary_single_apply (hf.comp_fst_add_comp_snd_chartedSpaceProd hg),
    morseBoundaryCoeff_prod hf hg h₁ h₂, one_mul, one_mul, one_mul]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
