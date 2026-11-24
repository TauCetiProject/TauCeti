/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod
public import TauCeti.LinearAlgebra.DirectSum.Finsupp

/-!
# The mod-two Morse complex of a product manifold

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a Morse–Smale
pseudo-gradient adapted to `f`, and likewise `g`, `Y` on `N`. The separated sum
`f ∘ Prod.fst + g ∘ Prod.snd` is a Morse function on `M × N`
(`TauCeti.IsMorse.comp_fst_add_comp_snd_chartedSpaceProd`, for the model `𝓘(ℝ, E × E')` of the
charts below), the product field `(X, Y)` is a pseudo-gradient adapted to it
(`TauCeti.IsAdaptedPseudoGradient.prod`), and it is Morse–Smale
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.prod`). This file computes the mod-two Morse
boundary of these product data: the mod-two Morse complex of `M × N` is the tensor product of the
mod-two Morse complexes of `M` and of `N`.

The critical points of the separated sum are the pairs `(p, q)` of critical points
(`TauCeti.criticalPointsCompFstAddCompSndEquiv`), of index `ind p + ind q`
(`TauCeti.manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd`). The flow of `(X, Y)` is
the product of the two flows, and its stable and unstable manifolds are the products of those of
the factors. So a trajectory from `(p, q)` to `(p', q')` is a pair of trajectories, from `p` to
`p'` and from `q` to `q'`. Under the Morse–Smale condition the index drops strictly along every
nonconstant trajectory, so if the index of the pair drops by one, one of the two components is
constant: either `p = p'` and the trajectory is a trajectory of `Y` from `q` to `q'`, or `q = q'`
and it is a trajectory of `X` from `p` to `p'`. Hence the boundary coefficients of the product are

`⟨∂ (p, q), (p', q')⟩ = [p = p'] ⟨∂ q, q'⟩ + [q = q'] ⟨∂ p, p'⟩`,

and on chains `∂ (p ⊗ q) = ∂ p ⊗ q + p ⊗ ∂ q`. Over `ZMod 2` there is no Koszul sign; with integral
coefficients the second term carries the sign `(-1)^{ind p}`, which comes from orienting the
unstable manifold of `(p, q)` by the unstable manifold of `p` followed by that of `q`
(`TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Integral`).

This is the manifold form of `TauCeti.Analysis.Calculus.Morse.Boundary.Prod`, which treats
separated sums on Euclidean spaces. On compact manifolds no sublevel or Lipschitz hypothesis is
needed.

As in `TauCeti.Geometry.Manifold.Morse.PseudoGradient.Prod`, the charts of `M × N` are read on the
normed space `E × E'` (`TauCeti.chartedSpaceProd` and `TauCeti.isManifold_chartedSpaceProd`, local
instances), so that the product carries the model `𝓘(ℝ, E × E')` on which the Morse complex is
defined.

## Main declarations

* `TauCeti.criticalPointsCompFstAddCompSndEquiv`: the critical points of the separated sum are the
  pairs of critical points.
* `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_left` and
  `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_prod_right`: trajectories of the product in
  which one component is constant are trajectories of the other factor.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseTrajectorySlice_prod_eq_empty`: under the
  Morse–Smale condition, no trajectory along which the index drops by at most one moves both
  components.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundaryCoeff_prod`: the boundary coefficients
  of the product.
* `TauCeti.morseChainProdEquiv` and
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseChainProdEquiv_comp_morseBoundary`: the Morse
  chains of the product are the tensor product of the Morse chains of the factors, and the mod-two
  Morse boundary corresponds to `∂ ⊗ 1 + 1 ⊗ ∂`. This is a chain-level statement; the Künneth
  formula for Morse homology is deduced from it in
  `TauCeti.Geometry.Manifold.Morse.Boundary.Kunneth`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 2 (the Morse complex of a product is the tensor
  product of the Morse complexes).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
-/

public section

open Function Set
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N]
  [ChartedSpace E' N] {f : M → ℝ} {g : N → ℝ}

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

/-! ### Critical points and chains -/

variable (f g) in
/-- **The critical points of a separated sum are the pairs of critical points**, as an equivalence
of critical sets, for differentiable `f` and `g`. -/
-- The body is exposed: orientation data on the product (`TauCeti.MorseOrientation.prod`) attach to
-- the critical point `(p, q)` objects whose types mention the pair of points, which must reduce to
-- `(p, q)`.
@[expose]
noncomputable def criticalPointsCompFstAddCompSndEquiv (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) ≃
      criticalPoints 𝓘(ℝ, E) f × criticalPoints 𝓘(ℝ, E') g :=
  (Equiv.subtypeEquivRight fun _ ↦
    mem_criticalPoints_comp_fst_add_comp_snd_iff_chartedSpaceProd (hf _) (hg _)).trans
    Equiv.subtypeProdEquivProd

section Equiv

variable {hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f} {hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g}

/-- The first component of the pair attached to a critical point of the separated sum. -/
@[simp]
theorem coe_criticalPointsCompFstAddCompSndEquiv_fst
    (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) :
    ((criticalPointsCompFstAddCompSndEquiv f g hf hg P).1 : M) = (P : M × N).1 :=
  (rfl)

/-- The second component of the pair attached to a critical point of the separated sum. -/
@[simp]
theorem coe_criticalPointsCompFstAddCompSndEquiv_snd
    (P : criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)) :
    ((criticalPointsCompFstAddCompSndEquiv f g hf hg P).2 : N) = (P : M × N).2 :=
  (rfl)

/-- The critical point of the separated sum attached to a pair `(p, q)` is the point `(p, q)`. -/
@[simp]
theorem coe_criticalPointsCompFstAddCompSndEquiv_symm
    (pq : criticalPoints 𝓘(ℝ, E) f × criticalPoints 𝓘(ℝ, E') g) :
    ((criticalPointsCompFstAddCompSndEquiv f g hf hg).symm pq : M × N) =
      ((pq.1 : M), (pq.2 : N)) :=
  (rfl)

/-- The Morse index of the separated sum at the critical point attached to `(p, q)` is the sum of
the indices of `p` and `q`. -/
theorem manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ E'] (hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hg' : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ) 2 g) (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) :
    manifoldMorseIndex 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd)
        ((criticalPointsCompFstAddCompSndEquiv f g hf hg).symm (p, q) : M × N) =
      manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q :=
  manifoldMorseIndex_comp_fst_add_comp_snd_chartedSpaceProd (hf' _) (hg' _)

end Equiv

variable (f g) in
/-- **The Morse chains of a separated sum are the tensor product** of the Morse chains of the
summands, with coefficients in any commutative semiring `R`: the pair `(p, q)` of critical points
corresponds to `p ⊗ q`. -/
noncomputable def morseChainProdEquiv (R : Type*) [CommSemiring R]
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) (hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g) :
    (criticalPoints 𝓘(ℝ, E × E') (f ∘ Prod.fst + g ∘ Prod.snd) →₀ R) ≃ₗ[R]
      (criticalPoints 𝓘(ℝ, E) f →₀ R) ⊗[R] (criticalPoints 𝓘(ℝ, E') g →₀ R) :=
  (Finsupp.domLCongr (criticalPointsCompFstAddCompSndEquiv f g hf hg)).trans
    (finsuppTensorFinsupp' R _ _).symm

section Chain

variable {R : Type*} [CommSemiring R] {hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f}
  {hg : MDifferentiable 𝓘(ℝ, E') 𝓘(ℝ) g}

/-- The defining formula of the identification of the chains of a separated sum with the tensor
product of chains. -/
theorem morseChainProdEquiv_def (R : Type*) [CommSemiring R] :
    morseChainProdEquiv f g R hf hg =
      (Finsupp.domLCongr (criticalPointsCompFstAddCompSndEquiv f g hf hg)).trans
        (finsuppTensorFinsupp' R _ _).symm :=
  (rfl)

/-- The chain `a • (p, q)` corresponds to `a • p ⊗ q`. -/
@[simp]
theorem morseChainProdEquiv_single (p : criticalPoints 𝓘(ℝ, E) f)
    (q : criticalPoints 𝓘(ℝ, E') g) (a : R) :
    morseChainProdEquiv f g R hf hg
        (Finsupp.single ((criticalPointsCompFstAddCompSndEquiv f g hf hg).symm (p, q)) a) =
      Finsupp.single p a ⊗ₜ Finsupp.single q 1 := by
  simp [morseChainProdEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

end Chain

/-! ### Trajectories -/

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E') ∞ N] [CompactSpace M] [T2Space M] [CompactSpace N] [T2Space N]
  {X : (z : M) → TangentSpace 𝓘(ℝ, E) z} {Y : (z : N) → TangentSpace 𝓘(ℝ, E') z}
  (hX : IsAdaptedPseudoGradient f X) (hY : IsAdaptedPseudoGradient g Y)

/-- **Trajectories of a product that are constant in the first factor.** Between pairs with the
same critical point `x` of `f` in the first factor, the trajectories of the product field `(X, Y)`
are the trajectories of `Y`, on the middle level. -/
theorem morseTrajectorySlice_prod_left {x : M} (hx : x ∈ criticalPoints 𝓘(ℝ, E) f) (q q' : N) :
    (hX.prod hY).morseTrajectorySlice (x, q) (x, q') =
      (fun y ↦ (x, y)) '' hY.morseTrajectorySlice q q' := by
  have hxx := hX.mem_unstableSet_inter_stableSet_self (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)
  refine Set.ext fun z ↦ ?_
  -- `simp` does not unfold membership in the slice of the product field, whose tangent spaces are
  -- those of the product model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`; `rw` does.
  rw [(hX.prod hY).mem_morseTrajectorySlice]
  simp only [mem_morseTrajectorySlice, hX.unstableSet_prod hY, hX.stableSet_prod hY, mem_prod,
    Pi.add_apply, comp_apply, mem_image]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₁ : z.1 = x := hX.eq_of_mem_unstableSet_inter_stableSet ⟨hu₁, hs₁⟩
    exact ⟨z.2, ⟨hu₂, hs₂, by rw [hz₁] at hz; linarith⟩, Prod.ext hz₁.symm rfl⟩
  · rintro ⟨y, ⟨hu, hs, hy⟩, rfl⟩
    exact ⟨⟨hxx.1, hu⟩, ⟨hxx.2, hs⟩, by linarith⟩

/-- **Trajectories of a product that are constant in the second factor.** Between pairs with the
same critical point `y` of `g` in the second factor, the trajectories of the product field `(X, Y)`
are the trajectories of `X`, on the middle level. -/
theorem morseTrajectorySlice_prod_right {y : N} (hy : y ∈ criticalPoints 𝓘(ℝ, E') g) (p p' : M) :
    (hX.prod hY).morseTrajectorySlice (p, y) (p', y) =
      (fun x ↦ (x, y)) '' hX.morseTrajectorySlice p p' := by
  have hyy := hY.mem_unstableSet_inter_stableSet_self (mem_criticalPoints_iff_mfderiv_eq_zero.1 hy)
  refine Set.ext fun z ↦ ?_
  rw [(hX.prod hY).mem_morseTrajectorySlice]
  simp only [mem_morseTrajectorySlice, hX.unstableSet_prod hY, hX.stableSet_prod hY, mem_prod,
    Pi.add_apply, comp_apply, mem_image]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₂ : z.2 = y := hY.eq_of_mem_unstableSet_inter_stableSet ⟨hu₂, hs₂⟩
    exact ⟨z.1, ⟨hu₁, hs₁, by rw [hz₂] at hz; linarith⟩, Prod.ext rfl hz₂.symm⟩
  · rintro ⟨x, ⟨hu, hs, hx⟩, rfl⟩
    exact ⟨⟨hu, hyy.1⟩, ⟨hs, hyy.2⟩, by linarith⟩

omit hX hY in
/-- **No trajectory of index one moves both components.** For Morse–Smale `X` and `Y`, if the
index drops by at most one from `(p, q)` to `(p', q')` with `p ≠ p'` and `q ≠ q'`, there is no
trajectory of the product between them: each component would lower the index of its factor by at
least one. -/
theorem IsMorseSmale.morseTrajectorySlice_prod_eq_empty {hX : IsAdaptedPseudoGradient f X}
    {hY : IsAdaptedPseudoGradient g Y} (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hg : IsMorse 𝓘(ℝ, E') g) {p p' : M} {q q' : N} (hpp' : p ≠ p')
    (hqq' : q ≠ q')
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q ≤
      manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1) :
    (hX.prod hY).morseTrajectorySlice (p, q) (p', q') = ∅ := by
  refine eq_empty_of_forall_notMem fun z hz ↦ ?_
  rw [(hX.prod hY).mem_morseTrajectorySlice] at hz
  simp only [hX.unstableSet_prod hY, hX.stableSet_prod hY, mem_prod] at hz
  obtain ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, -⟩ := hz
  have h₁ := hXs.manifoldMorseIndex_lt hf hpp' ⟨z.1, hu₁, hs₁⟩
  have h₂ := hYs.manifoldMorseIndex_lt hg hqq' ⟨z.2, hu₂, hs₂⟩
  omega

/-! ### The boundary -/

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} {hY : IsAdaptedPseudoGradient g Y}
  (hXs : hX.IsMorseSmale) (hYs : hY.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (hg : IsMorse 𝓘(ℝ, E') g)

open scoped Classical in
/-- **The boundary coefficients of a product.** The coefficient of `(p', q')` in the mod-two Morse
boundary of `(p, q)` counts the trajectories of `Y` from `q` to `q'` when `p = p'`, and the
trajectories of `X` from `p` to `p'` when `q = q'`; it vanishes when both components differ. -/
theorem morseBoundaryCoeff_prod (p p' : criticalPoints 𝓘(ℝ, E) f)
    (q q' : criticalPoints 𝓘(ℝ, E') g) :
    (hXs.prod hYs).morseBoundaryCoeff (hf.comp_fst_add_comp_snd_chartedSpaceProd hg)
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p, q))
        ((criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable).symm
          (p', q')) =
      (if p = p' then hYs.morseBoundaryCoeff hg q q' else 0) +
        if q = q' then hXs.morseBoundaryCoeff hf p p' else 0 := by
  set e := criticalPointsCompFstAddCompSndEquiv f g hX.mdifferentiable hY.mdifferentiable
  have h := hXs.prod hYs
  have hfg := hf.comp_fst_add_comp_snd_chartedSpaceProd hg
  have hindP := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm
    (hf := hX.mdifferentiable) (hg := hY.mdifferentiable)
    (hf.contMDiff.of_le (by norm_num)) (hg.contMDiff.of_le (by norm_num)) p q
  have hindQ := manifoldMorseIndex_criticalPointsCompFstAddCompSndEquiv_symm
    (hf := hX.mdifferentiable) (hg := hY.mdifferentiable)
    (hf.contMDiff.of_le (by norm_num)) (hg.contMDiff.of_le (by norm_num)) p' q'
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p + manifoldMorseIndex 𝓘(ℝ, E') g q =
    manifoldMorseIndex 𝓘(ℝ, E) f p' + manifoldMorseIndex 𝓘(ℝ, E') g q' + 1
  swap
  · -- The index does not drop by one, so every coefficient vanishes.
    rw [h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hfg (by
      rw [hindP, hindQ]
      exact hind)]
    have h₁ : (if p = p' then hYs.morseBoundaryCoeff hg q q' else 0) = 0 := by
      split_ifs with hpp
      · subst hpp
        exact hYs.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hg (by omega)
      · rfl
    have h₂ : (if q = q' then hXs.morseBoundaryCoeff hf p p' else 0) = 0 := by
      split_ifs with hqq
      · subst hqq
        exact hXs.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf (by omega)
      · rfl
    rw [h₁, h₂, add_zero]
  rw [h.morseBoundaryCoeff_eq_ncard hfg (by rw [hindP, hindQ]; exact hind)]
  -- The product field has its tangent spaces for the model `𝓘(ℝ, E).prod 𝓘(ℝ, E')`, which agree
  -- with those for `𝓘(ℝ, E × E')` only up to unfolding, so `simp` cannot rewrite inside the
  -- trajectory slice of the product; `rw` can.
  rw [coe_criticalPointsCompFstAddCompSndEquiv_symm, coe_criticalPointsCompFstAddCompSndEquiv_symm]
  by_cases hpp : p = p'
  · subst hpp
    have hqq : q ≠ q' := by rintro rfl; omega
    rw [hX.morseTrajectorySlice_prod_left hY p.property,
      ncard_image_of_injective _ (Prod.mk_right_injective _),
      hYs.morseBoundaryCoeff_eq_ncard hg (p := q) (q := q') (by omega)]
    simp [hqq]
  by_cases hqq : q = q'
  · subst hqq
    rw [hX.morseTrajectorySlice_prod_right hY q.property,
      ncard_image_of_injective _ (Prod.mk_left_injective _),
      hXs.morseBoundaryCoeff_eq_ncard hf (p := p) (q := p') (by omega)]
    simp [hpp]
  rw [hXs.morseTrajectorySlice_prod_eq_empty hYs hf hg (fun h ↦ hpp (Subtype.ext h))
      (fun h ↦ hqq (Subtype.ext h)) hind.le, ncard_empty, Nat.cast_zero]
  simp [hpp, hqq]

/-- **The mod-two Morse complex of a product is the tensor product complex.** Under the
identification of the mod-two Morse chains of `M × N` with the tensor product of the chains of `M`
and of `N`, the Morse boundary of the product field `(X, Y)` is `∂ ⊗ 1 + 1 ⊗ ∂`. This is a
chain-level statement: the Künneth formula for the homology of these complexes is
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseHomologyKunnethIso`. -/
theorem morseChainProdEquiv_comp_morseBoundary :
    (morseChainProdEquiv f g (ZMod 2) hX.mdifferentiable hY.mdifferentiable).toLinearMap ∘ₗ
        (hXs.prod hYs).morseBoundary (hf.comp_fst_add_comp_snd_chartedSpaceProd hg) =
      ((hXs.morseBoundary hf).rTensor (criticalPoints 𝓘(ℝ, E') g →₀ ZMod 2) +
          (hYs.morseBoundary hg).lTensor (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2)) ∘ₗ
        (morseChainProdEquiv f g (ZMod 2) hX.mdifferentiable hY.mdifferentiable).toLinearMap := by
  classical
  refine domLCongr_trans_finsuppTensorFinsupp'_symm_comp_eq_rTensor_add_lTensor _ _ _ _
    fun p p' q q' ↦ ?_
  -- As in `morseBoundaryCoeff_prod`, `simp` cannot rewrite the boundary of the product field, whose
  -- tangent spaces are those of the product model; `rw` can.
  rw [(hXs.prod hYs).morseBoundary_single_apply (hf.comp_fst_add_comp_snd_chartedSpaceProd hg),
    one_mul, morseBoundaryCoeff_prod hXs hYs hf hg]
  simp only [morseBoundary_single_apply, one_mul]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
