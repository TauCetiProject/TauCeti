/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Boundary.Basic
public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Prod
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
import TauCeti.Analysis.Calculus.Morse.Boundary.Square
import TauCeti.Analysis.Calculus.Morse.Stable

/-!
# The mod-two Morse complex of a separated sum

Let `f` on `E` and `g` on `F` be `C²` functions with globally Lipschitz gradients, nondegenerate
critical points, compact sublevels and the Morse–Smale property, on finite-dimensional real inner
product spaces. Their separated sum `TauCeti.separatedSum f g (x, y) = f x + g y` on the `L²`
product `WithLp 2 (E × F)` has all of these properties too
(`TauCeti.Analysis.Calculus.Morse.MorseSmale.Prod`), so it has a mod-two Morse boundary. This file
computes it: the mod-two Morse complex of the separated sum is the tensor product of the
mod-two Morse complexes of `f` and of `g`.

The critical points of the separated sum are the pairs `(p, q)` of critical points, of index
`ind p + ind q`. Its negative-gradient flow is the product of the two flows, so a trajectory from
`(p, q)` to `(p', q')` is a pair of trajectories, from `p` to `p'` and from `q` to `q'`. Under the
Morse–Smale condition the index drops strictly along a nonconstant trajectory, so if the index of
the pair drops by one, one of the two components is constant: either `p = p'` and the trajectory
is a trajectory of `g` from `q` to `q'` with `ind q = ind q' + 1`, or `q = q'` and it is a
trajectory of `f`. On the middle level these are read off by projecting to the moving factor.
Hence the boundary coefficients of the separated sum are

`⟨∂ (p, q), (p', q')⟩ = [p = p'] ⟨∂ q, q'⟩ + [q = q'] ⟨∂ p, p'⟩`,

and on chains `∂ (p ⊗ q) = ∂ p ⊗ q + p ⊗ ∂ q`. Over `ZMod 2` there is no Koszul sign.

The statements take the hypotheses that define the boundary of the separated sum as arguments;
they are supplied by `ContDiff.separatedSum`, `TauCeti.lipschitzWith_gradient_separatedSum`,
`HasNondegenerateCriticalPointsOn.separatedSum`, `TauCeti.isCompact_sublevel_separatedSum` and
`TauCeti.IsMorseSmale.separatedSum`.

## Main declarations

* `TauCeti.MorseCriticalPoint.separatedSumEquiv`: the critical points of the separated sum are
  the pairs of critical points.
* `TauCeti.morseTrajectorySlice_separatedSum_toLp_left` and
  `TauCeti.morseTrajectorySlice_separatedSum_toLp_right`: trajectories in which one component
  is constant are trajectories of the other summand.
* `TauCeti.morseTrajectorySlice_separatedSum_toLp_eq_empty`: under the Morse–Smale condition no
  trajectory between critical points whose index differs by one moves both components.
* `TauCeti.morseBoundaryCoeff_separatedSum`: the boundary coefficients of the separated sum.
* `TauCeti.morseBoundary_separatedSum_single`: the boundary of a pair of critical points.
* `TauCeti.morseChainSeparatedSumEquiv` and
  `TauCeti.morseChainSeparatedSumEquiv_comp_morseBoundary`: the mod-two Morse chains of the
  separated sum are the tensor product of the mod-two Morse chains of `f` and `g`, and the
  boundary corresponds to `∂ ⊗ 1 + 1 ⊗ ∂`.

## References

* M. Hutchings, *Lecture notes on Morse homology*, 2002, §3, Exercise 2 (the Morse complex of a
  product is the tensor product of the Morse complexes).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
-/

public section

open Set
open scoped Gradient NNReal TensorProduct

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f : E → ℝ} {g : F → ℝ} {K K' K'' : ℝ≥0}

/-! ### Critical points -/

namespace MorseCriticalPoint

variable (f g) in
/-- **The critical points of a separated sum are the pairs of critical points.** -/
noncomputable def separatedSumEquiv :
    MorseCriticalPoint (separatedSum f g) ≃ MorseCriticalPoint f × MorseCriticalPoint g where
  toFun P :=
    have h := isNondegenerateCriticalPoint_separatedSum_iff.1 P.2
    (⟨P.1.fst, h.1⟩, ⟨P.1.snd, h.2⟩)
  invFun pq := ⟨WithLp.toLp 2 (pq.1.1, pq.2.1), pq.1.2.separatedSum pq.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The critical point of the separated sum attached to a pair `(p, q)` is the point `(p, q)`. -/
@[simp]
theorem coe_separatedSumEquiv_symm (pq : MorseCriticalPoint f × MorseCriticalPoint g) :
    ((separatedSumEquiv f g).symm pq : WithLp 2 (E × F)) =
      WithLp.toLp 2 ((pq.1 : E), (pq.2 : F)) :=
  (rfl)

/-- The first component of a critical point of the separated sum. -/
@[simp]
theorem coe_separatedSumEquiv_fst (P : MorseCriticalPoint (separatedSum f g)) :
    ((separatedSumEquiv f g P).1 : E) = (P : WithLp 2 (E × F)).fst :=
  (rfl)

/-- The second component of a critical point of the separated sum. -/
@[simp]
theorem coe_separatedSumEquiv_snd (P : MorseCriticalPoint (separatedSum f g)) :
    ((separatedSumEquiv f g P).2 : F) = (P : WithLp 2 (E × F)).snd :=
  (rfl)

end MorseCriticalPoint

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-! ### Trajectories -/

/-- **Trajectories of a separated sum that are constant in the first factor.** Between pairs with
the same critical point `x` of `f` in the first factor, the trajectories of the separated sum are
the trajectories of `g`, on the middle level. -/
theorem morseTrajectorySlice_separatedSum_toLp_left (hfd : Differentiable ℝ f)
    (hgd : Differentiable ℝ g) (hf : LipschitzWith K (∇ f)) (hg : LipschitzWith K' (∇ g))
    (hh : LipschitzWith K'' (∇ (separatedSum f g))) {x : E} (hx : ∇ f x = 0) (q q' : F) :
    morseTrajectorySlice hh (WithLp.toLp 2 (x, q)) (WithLp.toLp 2 (x, q')) =
      (fun y ↦ WithLp.toLp 2 (x, y)) '' morseTrajectorySlice hg q q' := by
  have hfix := (forall_negativeGradientFlow_eq_self_iff f hf x).2 hx
  ext z
  simp only [mem_morseTrajectorySlice, mem_unstableSet_separatedSum hfd hgd hf hg hh,
    mem_stableSet_separatedSum hfd hgd hf hg hh, WithLp.toLp_fst, WithLp.toLp_snd,
    separatedSum_apply, mem_image]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₁ : z.fst = x := ((isNegativeGradient_negativeGradientFlow f hf
      ).mem_unstableSet_inter_stableSet_self_iff hfd hfix).1 ⟨hu₁, hs₁⟩
    refine ⟨z.snd, ⟨hu₂, hs₂, by rw [hz₁] at hz; linarith⟩, ?_⟩
    rw [← hz₁]
    rfl
  · rintro ⟨y, ⟨hu, hs, hy⟩, rfl⟩
    have hxx := ((isNegativeGradient_negativeGradientFlow f hf
      ).mem_unstableSet_inter_stableSet_self_iff hfd hfix (x := x)).2 rfl
    exact ⟨⟨hxx.1, hu⟩, ⟨hxx.2, hs⟩, by simp only [WithLp.toLp_fst, WithLp.toLp_snd]; linarith⟩

/-- **Trajectories of a separated sum that are constant in the second factor.** Between pairs with
the same critical point `y` of `g` in the second factor, the trajectories of the separated sum are
the trajectories of `f`, on the middle level. -/
theorem morseTrajectorySlice_separatedSum_toLp_right (hfd : Differentiable ℝ f)
    (hgd : Differentiable ℝ g) (hf : LipschitzWith K (∇ f)) (hg : LipschitzWith K' (∇ g))
    (hh : LipschitzWith K'' (∇ (separatedSum f g))) {y : F} (hy : ∇ g y = 0) (p p' : E) :
    morseTrajectorySlice hh (WithLp.toLp 2 (p, y)) (WithLp.toLp 2 (p', y)) =
      (fun x ↦ WithLp.toLp 2 (x, y)) '' morseTrajectorySlice hf p p' := by
  have hfix := (forall_negativeGradientFlow_eq_self_iff g hg y).2 hy
  ext z
  simp only [mem_morseTrajectorySlice, mem_unstableSet_separatedSum hfd hgd hf hg hh,
    mem_stableSet_separatedSum hfd hgd hf hg hh, WithLp.toLp_fst, WithLp.toLp_snd,
    separatedSum_apply, mem_image]
  constructor
  · rintro ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, hz⟩
    have hz₂ : z.snd = y := ((isNegativeGradient_negativeGradientFlow g hg
      ).mem_unstableSet_inter_stableSet_self_iff hgd hfix).1 ⟨hu₂, hs₂⟩
    refine ⟨z.fst, ⟨hu₁, hs₁, by rw [hz₂] at hz; linarith⟩, ?_⟩
    rw [← hz₂]
    rfl
  · rintro ⟨x, ⟨hu, hs, hx⟩, rfl⟩
    have hyy := ((isNegativeGradient_negativeGradientFlow g hg
      ).mem_unstableSet_inter_stableSet_self_iff hgd hfix (x := y)).2 rfl
    exact ⟨⟨hu, hyy.1⟩, ⟨hs, hyy.2⟩, by simp only [WithLp.toLp_fst, WithLp.toLp_snd]; linarith⟩

/-- **No trajectory of index one moves both components.** For Morse–Smale `f` and `g`, if the
index of the separated sum drops by one from `(p, q)` to `(p', q')` with `p ≠ p'` and `q ≠ q'`,
there is no trajectory between them: each component would lower the index of its factor by at
least one. -/
theorem morseTrajectorySlice_separatedSum_toLp_eq_empty (hfs : ContDiff ℝ 2 f)
    (hgs : ContDiff ℝ 2 g) {hf : LipschitzWith K (∇ f)} {hg : LipschitzWith K' (∇ g)}
    (htf : IsMorseSmale f hf) (htg : IsMorseSmale g hg)
    (hh : LipschitzWith K'' (∇ (separatedSum f g))) {p p' : E} {q q' : F}
    (hp : IsNondegenerateCriticalPoint f p) (hp' : IsNondegenerateCriticalPoint f p')
    (hq : IsNondegenerateCriticalPoint g q) (hq' : IsNondegenerateCriticalPoint g q')
    (hpp' : p ≠ p') (hqq' : q ≠ q')
    (hind : morseIndex f p + morseIndex g q = morseIndex f p' + morseIndex g q' + 1) :
    morseTrajectorySlice hh (WithLp.toLp 2 (p, q)) (WithLp.toLp 2 (p', q')) = ∅ := by
  have hfd := hfs.differentiable two_ne_zero
  have hgd := hgs.differentiable two_ne_zero
  refine eq_empty_of_forall_notMem fun z hz ↦ ?_
  simp only [mem_morseTrajectorySlice, mem_unstableSet_separatedSum hfd hgd hf hg hh,
    mem_stableSet_separatedSum hfd hgd hf hg hh, WithLp.toLp_fst, WithLp.toLp_snd] at hz
  obtain ⟨⟨hu₁, hu₂⟩, ⟨hs₁, hs₂⟩, -⟩ := hz
  have h₁ := htf.morseIndex_lt hp hp' hfs hpp' hu₁ hs₁
  have h₂ := htg.morseIndex_lt hq hq' hgs hqq' hu₂ hs₂
  omega

/-! ### The boundary -/

section Boundary

variable (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
  (hM : HasNondegenerateCriticalPointsOn f univ) (hcf : ∀ c : ℝ, IsCompact {x | f x ≤ c})
  (htf : IsMorseSmale f hf)
  (hgs : ContDiff ℝ 2 g) (hg : LipschitzWith K' (∇ g))
  (hN : HasNondegenerateCriticalPointsOn g univ) (hcg : ∀ c : ℝ, IsCompact {y | g y ≤ c})
  (htg : IsMorseSmale g hg)
  (hh : LipschitzWith K'' (∇ (separatedSum f g)))

open scoped Classical in
/-- **The boundary coefficients of a separated sum.** The coefficient of `(p', q')` in the mod-two
Morse boundary of `(p, q)` counts the trajectories of `g` from `q` to `q'` when `p = p'`, and the
trajectories of `f` from `p` to `p'` when `q = q'`; it vanishes when both components differ. -/
theorem morseBoundaryCoeff_separatedSum (hhs : ContDiff ℝ 2 (separatedSum f g))
    (hMh : HasNondegenerateCriticalPointsOn (separatedSum f g) univ)
    (hch : ∀ c : ℝ, IsCompact {z | separatedSum f g z ≤ c})
    (hth : IsMorseSmale (separatedSum f g) hh) (p p' : MorseCriticalPoint f)
    (q q' : MorseCriticalPoint g) :
    morseBoundaryCoeff hhs hh hMh hch hth
        ((MorseCriticalPoint.separatedSumEquiv f g).symm (p, q))
        ((MorseCriticalPoint.separatedSumEquiv f g).symm (p', q')) =
      (if p = p' then morseBoundaryCoeff hgs hg hN hcg htg q q' else 0) +
        if q = q' then morseBoundaryCoeff hfs hf hM hcf htf p p' else 0 := by
  have hfd := hfs.differentiable two_ne_zero
  have hgd := hgs.differentiable two_ne_zero
  have hindP := morseIndex_separatedSum (z := WithLp.toLp 2 ((p : E), (q : F)))
    hfs.contDiffAt hgs.contDiffAt
  have hindQ := morseIndex_separatedSum (z := WithLp.toLp 2 ((p' : E), (q' : F)))
    hfs.contDiffAt hgs.contDiffAt
  simp only [WithLp.toLp_fst, WithLp.toLp_snd] at hindP hindQ
  by_cases hind : morseIndex f p + morseIndex g q = morseIndex f p' + morseIndex g q' + 1
  swap
  · -- The index does not drop by one, so every coefficient vanishes.
    rw [morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ _ _ _ _ _ _ (by
      rw [MorseCriticalPoint.coe_separatedSumEquiv_symm,
        MorseCriticalPoint.coe_separatedSumEquiv_symm, hindP, hindQ]
      exact hind)]
    have h₁ : (if p = p' then morseBoundaryCoeff hgs hg hN hcg htg q q' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ _ _ _ _ _ _ (by omega)
      · rfl
    have h₂ : (if q = q' then morseBoundaryCoeff hfs hf hM hcf htf p p' else 0) = 0 := by
      split_ifs with h
      · subst h
        exact morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one _ _ _ _ _ _ _ (by omega)
      · rfl
    rw [h₁, h₂, add_zero]
  rw [morseBoundaryCoeff_eq_ncard hhs hh hMh hch hth (by
    rw [MorseCriticalPoint.coe_separatedSumEquiv_symm,
      MorseCriticalPoint.coe_separatedSumEquiv_symm, hindP, hindQ]
    exact hind)]
  simp only [MorseCriticalPoint.coe_separatedSumEquiv_symm]
  by_cases hpp : p = p'
  · subst hpp
    have hqq : q ≠ q' := by rintro rfl; omega
    rw [morseTrajectorySlice_separatedSum_toLp_left hfd hgd hf hg hh
        p.isNondegenerate.gradient_eq_zero,
      ncard_image_of_injective _ fun y y' h ↦ by simpa using congrArg WithLp.snd h,
      morseBoundaryCoeff_eq_ncard hgs hg hN hcg htg (p := q) (q := q') (by omega)]
    simp [hqq]
  by_cases hqq : q = q'
  · subst hqq
    rw [morseTrajectorySlice_separatedSum_toLp_right hfd hgd hf hg hh
        q.isNondegenerate.gradient_eq_zero,
      ncard_image_of_injective _ fun x x' h ↦ by simpa using congrArg WithLp.fst h,
      morseBoundaryCoeff_eq_ncard hfs hf hM hcf htf (p := p) (q := p') (by omega)]
    simp [hpp]
  rw [morseTrajectorySlice_separatedSum_toLp_eq_empty hfs hgs htf htg hh p.isNondegenerate
      p'.isNondegenerate q.isNondegenerate q'.isNondegenerate (fun h ↦ hpp (Subtype.ext h))
      (fun h ↦ hqq (Subtype.ext h)) hind,
    ncard_empty, Nat.cast_zero]
  simp [hpp, hqq]

/-- **The boundary of a pair of critical points** is `∂ (p, q) = (∂ p, q) + (p, ∂ q)`: the sum of
the boundary of `p` paired with `q` and of `p` paired with the boundary of `q`. -/
theorem morseBoundary_separatedSum_single (hhs : ContDiff ℝ 2 (separatedSum f g))
    (hMh : HasNondegenerateCriticalPointsOn (separatedSum f g) univ)
    (hch : ∀ c : ℝ, IsCompact {z | separatedSum f g z ≤ c})
    (hth : IsMorseSmale (separatedSum f g) hh) (p : MorseCriticalPoint f)
    (q : MorseCriticalPoint g) (a : ZMod 2) :
    morseBoundary hhs hh hMh hch hth
        (Finsupp.single ((MorseCriticalPoint.separatedSumEquiv f g).symm (p, q)) a) =
      Finsupp.mapDomain (fun p' ↦ (MorseCriticalPoint.separatedSumEquiv f g).symm (p', q))
          (morseBoundary hfs hf hM hcf htf (Finsupp.single p a)) +
        Finsupp.mapDomain (fun q' ↦ (MorseCriticalPoint.separatedSumEquiv f g).symm (p, q'))
          (morseBoundary hgs hg hN hcg htg (Finsupp.single q a)) := by
  classical
  set e := MorseCriticalPoint.separatedSumEquiv f g
  ext Q
  obtain ⟨⟨p', q'⟩, rfl⟩ := e.symm.surjective Q
  have hinjL : Function.Injective fun p' ↦ e.symm (p', q) :=
    e.symm.injective.comp (Prod.mk_left_injective q)
  have hinjR : Function.Injective fun q' ↦ e.symm (p, q') :=
    e.symm.injective.comp (Prod.mk_right_injective p)
  -- Read off each image of `mapDomain`: it is the corresponding coefficient on the range, and `0`
  -- off it.
  have hL : Finsupp.mapDomain (fun p' ↦ e.symm (p', q))
      (morseBoundary hfs hf hM hcf htf (Finsupp.single p a)) (e.symm (p', q')) =
        if q = q' then a * morseBoundaryCoeff hfs hf hM hcf htf p p' else 0 := by
    split_ifs with h
    · subst h
      rw [Finsupp.mapDomain_apply_of_injective hinjL]
      simp [morseBoundaryOnGenerator_apply]
    · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨p'', hp''⟩
      exact h (congrArg Prod.snd (e.symm.injective hp''))
  have hR : Finsupp.mapDomain (fun q' ↦ e.symm (p, q'))
      (morseBoundary hgs hg hN hcg htg (Finsupp.single q a)) (e.symm (p', q')) =
        if p = p' then a * morseBoundaryCoeff hgs hg hN hcg htg q q' else 0 := by
    split_ifs with h
    · subst h
      rw [Finsupp.mapDomain_apply_of_injective hinjR]
      simp [morseBoundaryOnGenerator_apply]
    · refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨q'', hq''⟩
      exact h (congrArg Prod.fst (e.symm.injective hq''))
  rw [Finsupp.add_apply, hL, hR, morseBoundary_single, Finsupp.smul_apply,
    morseBoundaryOnGenerator_apply, morseBoundaryCoeff_separatedSum hfs hf hM hcf htf hgs hg hN hcg
      htg hh hhs hMh hch hth, smul_eq_mul, mul_add]
  split_ifs <;> simp [add_comm]

variable (f g) in
/-- **The mod-two Morse chains of a separated sum are the tensor product** of the mod-two Morse
chains of the summands: the pair `(p, q)` of critical points corresponds to `p ⊗ q`. -/
noncomputable def morseChainSeparatedSumEquiv :
    MorseChain (separatedSum f g) ≃ₗ[ZMod 2] MorseChain f ⊗[ZMod 2] MorseChain g :=
  (Finsupp.domLCongr (MorseCriticalPoint.separatedSumEquiv f g)).trans
    (finsuppTensorFinsupp' (ZMod 2) (MorseCriticalPoint f) (MorseCriticalPoint g)).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The chain `a • (p, q)` corresponds to `a • p ⊗ q`. -/
@[simp]
theorem morseChainSeparatedSumEquiv_single (p : MorseCriticalPoint f) (q : MorseCriticalPoint g)
    (a : ZMod 2) :
    morseChainSeparatedSumEquiv f g
        (Finsupp.single ((MorseCriticalPoint.separatedSumEquiv f g).symm (p, q)) a) =
      Finsupp.single p a ⊗ₜ Finsupp.single q 1 := by
  simp [morseChainSeparatedSumEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Pairing a chain of `f` with a fixed critical point of `g` corresponds to its tensor product
with that critical point. -/
private theorem morseChainSeparatedSumEquiv_mapDomain_left (q : MorseCriticalPoint g)
    (c : MorseChain f) :
    morseChainSeparatedSumEquiv f g
        (Finsupp.mapDomain (fun p' ↦ (MorseCriticalPoint.separatedSumEquiv f g).symm (p', q))
          c) =
      c ⊗ₜ Finsupp.single q 1 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.add_tmul]
  | single p' b => rw [Finsupp.mapDomain_single, morseChainSeparatedSumEquiv_single]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Pairing a fixed critical point of `f` with a chain of `g` corresponds to its tensor product
with that critical point. -/
private theorem morseChainSeparatedSumEquiv_mapDomain_right (p : MorseCriticalPoint f)
    (c : MorseChain g) :
    morseChainSeparatedSumEquiv f g
        (Finsupp.mapDomain (fun q' ↦ (MorseCriticalPoint.separatedSumEquiv f g).symm (p, q'))
          c) =
      Finsupp.single p 1 ⊗ₜ c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, TensorProduct.tmul_add]
  | single q' b =>
    rw [Finsupp.mapDomain_single, morseChainSeparatedSumEquiv_single, ← mul_one b,
      ← smul_eq_mul, ← Finsupp.smul_single, ← Finsupp.smul_single, TensorProduct.smul_tmul]

/-- **The Künneth formula for the mod-two Morse complex.** Under the identification of the mod-two
Morse chains of the separated sum with the tensor product of the chains of `f` and of `g`, the
Morse boundary of the separated sum is `∂ ⊗ 1 + 1 ⊗ ∂`. -/
theorem morseChainSeparatedSumEquiv_comp_morseBoundary (hhs : ContDiff ℝ 2 (separatedSum f g))
    (hMh : HasNondegenerateCriticalPointsOn (separatedSum f g) univ)
    (hch : ∀ c : ℝ, IsCompact {z | separatedSum f g z ≤ c})
    (hth : IsMorseSmale (separatedSum f g) hh) :
    (morseChainSeparatedSumEquiv f g).toLinearMap ∘ₗ morseBoundary hhs hh hMh hch hth =
      ((morseBoundary hfs hf hM hcf htf).rTensor (MorseChain g) +
          (morseBoundary hgs hg hN hcg htg).lTensor (MorseChain f)) ∘ₗ
        (morseChainSeparatedSumEquiv f g).toLinearMap := by
  refine Finsupp.lhom_ext fun P a ↦ ?_
  obtain ⟨⟨p, q⟩, rfl⟩ := (MorseCriticalPoint.separatedSumEquiv f g).symm.surjective P
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    morseBoundary_separatedSum_single hfs hf hM hcf htf hgs hg hN hcg htg hh hhs hMh hch hth,
    map_add, morseChainSeparatedSumEquiv_mapDomain_left,
    morseChainSeparatedSumEquiv_mapDomain_right,
    morseChainSeparatedSumEquiv_single, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  congr 1
  rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, ← Finsupp.smul_single, map_smul,
    TensorProduct.smul_tmul]

end Boundary

end TauCeti
