/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Analytic.Submanifold.Transport
public import TauCeti.Analysis.Complex.CoordinateRealification

/-!
# Realification of complex analytic submanifolds in coordinate spaces

Under any continuous `ℝ`-linear equivalence `(Fin n → ℂ) ≃L[ℝ] Fin m → ℝ` (forcing `m = 2 * n`), a
`d`-dimensional complex analytic submanifold of `ℂⁿ` becomes a `(2 * d)`-dimensional real analytic
submanifold of `ℝᵐ`, and a complex analytic function on it becomes real analytic on the image.
Only the forward implication holds: an even-dimensional real analytic submanifold of `ℂⁿ` need not
be complex analytic. In addition, the conjugation-fixed locus `{z : Fin n → ℂ | star z = z}` (the
standard copy of `ℝⁿ` in `ℂⁿ`) maps to an `n`-dimensional real analytic submanifold.

`TauCeti.complexPiEquivRealPi` (the sup-norm `Fin n → ℂ` counterpart of
`TauCeti.complexEuclideanRealLinearIsometryEquiv`) interleaves real and imaginary parts so that the
subspace of the first `d` complex coordinates corresponds directly to the subspace of the first
`2 * d` real coordinates; arbitrary continuous `ℝ`-linear coordinate equivalences relate to it via
`TauCeti.IsAnalyticSubmanifold.image_continuousLinearEquiv`.

## Main declarations

* `TauCeti.complexPiEquivRealPi_firstCoords`: `TauCeti.complexPiEquivRealPi` commutes with
  `TauCeti.firstCoords` in both directions.
* `TauCeti.IsAnalyticChart.realImage_complexPiEquivRealPi`: a complex analytic chart in dimension
  `d` induces a real analytic chart in dimension `2 * d`.
* `TauCeti.IsAnalyticSubmanifold.image_realContinuousLinearEquiv`: a `d`-dimensional complex
  analytic submanifold maps to a `(2 * d)`-dimensional real analytic submanifold under any
  `(Fin n → ℂ) ≃L[ℝ] Fin m → ℝ`.
* `TauCeti.AnalyticOnSubmanifold.comp_symm_realContinuousLinearEquiv`: complex analytic functions
  on a submanifold become real analytic in dimension `2 * d`.
* `TauCeti.isAnalyticSubmanifold_image_setOf_star_eq`,
  `IsOpen.isAnalyticSubmanifold_image_inter_setOf_star_eq`: `{z : Fin n → ℂ | star z = z}` (and its
  nonempty intersections with open subsets) maps to an `n`-dimensional real analytic submanifold
  under any `(Fin n → ℂ) ≃L[ℝ] Fin m → ℝ`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §1.1–1.2.
* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti

/-! ### Interleaved real coordinates and `firstCoords` -/

/-- Interleaved real coordinates commute with `TauCeti.firstCoords` in both directions (inclusion
and projection). -/
theorem complexPiEquivRealPi_firstCoords (m k : ℕ) (u : Fin m → ℂ) :
    complexPiEquivRealPi k (firstCoords ℂ m k u) =
      firstCoords ℝ (2 * m) (2 * k) (complexPiEquivRealPi m u) := by
  ext ⟨j, hj⟩
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · have hi : i < k := by omega
    by_cases him : i < m
    · have hj' : 2 * i < 2 * m := by omega
      have hL := complexPiEquivRealPi_apply_two_mul (firstCoords ℂ m k u) ⟨i, hi⟩
      have hR := complexPiEquivRealPi_apply_two_mul u ⟨i, him⟩
      simpa [firstCoords_apply, him, hj', hR] using hL
    · have hj' : ¬ 2 * i < 2 * m := by omega
      simpa [firstCoords_apply, him, hj'] using
        complexPiEquivRealPi_apply_two_mul (firstCoords ℂ m k u) ⟨i, hi⟩
  · have hi : i < k := by omega
    by_cases him : i < m
    · have hj' : 2 * i + 1 < 2 * m := by omega
      have hL := complexPiEquivRealPi_apply_two_mul_add_one (firstCoords ℂ m k u) ⟨i, hi⟩
      have hR := complexPiEquivRealPi_apply_two_mul_add_one u ⟨i, him⟩
      simpa [firstCoords_apply, him, hj', hR] using hL
    · have hj' : ¬ 2 * i + 1 < 2 * m := by omega
      simpa [firstCoords_apply, him, hj'] using
        complexPiEquivRealPi_apply_two_mul_add_one (firstCoords ℂ m k u) ⟨i, hi⟩

/-! ### Realification of complex analytic submanifolds -/

/-- Conjugating a `d`-dimensional complex analytic chart of `S ⊆ ℂⁿ` by
`TauCeti.complexPiEquivRealPi` produces a `(2 * d)`-dimensional real analytic chart of the image of
`S` in `ℝ²ⁿ`. -/
theorem IsAnalyticChart.realImage_complexPiEquivRealPi {n d : ℕ} {S : Set (Fin n → ℂ)}
    {c : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ)} (hc : IsAnalyticChart d S c) :
    IsAnalyticChart (2 * d) (complexPiEquivRealPi n '' S)
      ((complexPiEquivRealPi n).symm.toHomeomorph.toOpenPartialHomeomorph.trans
        (c.trans (complexPiEquivRealPi n).toHomeomorph.toOpenPartialHomeomorph)) := by
  let L := complexPiEquivRealPi n
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : L.symm x ∈ c.source := by
      simpa [L, OpenPartialHomeomorph.trans_source] using hx
    simpa only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def] using
      (L.analyticAt _).comp (((hc.analyticOnNhd _ hx').restrictScalars (𝕜 := ℝ)).comp
        (L.symm.analyticAt x))
  · intro y hy
    have hy' : L.symm y ∈ c.target := by
      simpa [L, OpenPartialHomeomorph.trans_target] using hy
    simpa only [OpenPartialHomeomorph.coe_trans_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply,
      ContinuousLinearEquiv.coe_symm_toHomeomorph, ContinuousLinearEquiv.symm_symm,
      Function.comp_def] using
      (L.analyticAt _).comp (((hc.analyticOnNhd_symm _ hy').restrictScalars (𝕜 := ℝ)).comp
        (L.symm.analyticAt y))
  · intro x hx
    have hx' : L.symm x ∈ c.source := by
      simpa [L, OpenPartialHomeomorph.trans_source] using hx
    simp only [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, mem_ofPred_eq,
      forall_two_mul_le_complexPiEquivRealPi_eq_zero_iff]
    rw [← hc.mem_iff hx']
    exact ⟨fun h ↦ ⟨L.symm x, h, L.apply_symm_apply x⟩,
      by rintro ⟨z, hz, rfl⟩; rwa [L.symm_apply_apply]⟩

/-- A `d`-dimensional complex analytic submanifold of `ℂⁿ` maps under any continuous `ℝ`-linear
equivalence `(Fin n → ℂ) ≃L[ℝ] Fin m → ℝ` to a `(2 * d)`-dimensional real analytic submanifold of
`ℝᵐ`. -/
theorem IsAnalyticSubmanifold.image_realContinuousLinearEquiv {n m d : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsAnalyticSubmanifold d S) (e : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ) :
    IsAnalyticSubmanifold (2 * d) (e '' S) := by
  have hbase : IsAnalyticSubmanifold (2 * d) (complexPiEquivRealPi n '' S) := by
    refine ⟨hS.nonempty.image _, Nat.mul_le_mul_left 2 hS.le, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hzc, hc⟩ := hS.exists_isAnalyticChart z hz
    exact ⟨_, by simpa [OpenPartialHomeomorph.trans_source] using hzc,
      hc.realImage_complexPiEquivRealPi⟩
  have heq : e '' S = ((complexPiEquivRealPi n).symm.trans e) '' (complexPiEquivRealPi n '' S) := by
    rw [← image_comp]
    ext y
    simp
  rw [heq]
  exact hbase.image_continuousLinearEquiv ((complexPiEquivRealPi n).symm.trans e)

/-- A complex analytic function on a `d`-dimensional complex analytic submanifold of `ℂⁿ` becomes
real analytic in dimension `2 * d` after transporting coordinates by any
`(Fin n → ℂ) ≃L[ℝ] Fin m → ℝ`. -/
theorem AnalyticOnSubmanifold.comp_symm_realContinuousLinearEquiv {n m d : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {S : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → F} (hf : AnalyticOnSubmanifold d f S)
    (e : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ) :
    AnalyticOnSubmanifold (2 * d) (f ∘ e.symm) (e '' S) := by
  have hbase : AnalyticOnSubmanifold (2 * d) (f ∘ (complexPiEquivRealPi n).symm)
      (complexPiEquivRealPi n '' S) := by
    rw [analyticOnSubmanifold_iff] at hf ⊢
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hzc, hc, hf'⟩ := hf z hz
    refine ⟨_, by simpa [OpenPartialHomeomorph.trans_source] using hzc,
      hc.realImage_complexPiEquivRealPi, ?_⟩
    have hpt : firstCoords ℝ (2 * n) (2 * d) (complexPiEquivRealPi n (c z)) =
        complexPiEquivRealPi d (firstCoords ℂ n d (c z)) :=
      (complexPiEquivRealPi_firstCoords n d (c z)).symm
    have han : AnalyticAt ℝ
        (fun v : Fin (2 * d) → ℝ ↦
          f (c.symm (firstCoords ℂ d n ((complexPiEquivRealPi d).symm v))))
        (complexPiEquivRealPi d (firstCoords ℂ n d (c z))) :=
      (hf'.restrictScalars (𝕜 := ℝ)).comp_of_eq ((complexPiEquivRealPi d).symm.analyticAt _)
        (by simp)
    have hfun : (fun v : Fin (2 * d) → ℝ ↦
          (f ∘ (complexPiEquivRealPi n).symm)
            (((complexPiEquivRealPi n).symm.toHomeomorph.toOpenPartialHomeomorph.trans
              (c.trans (complexPiEquivRealPi n).toHomeomorph.toOpenPartialHomeomorph)).symm
              (firstCoords ℝ (2 * d) (2 * n) v))) =
        fun v ↦ f (c.symm (firstCoords ℂ d n ((complexPiEquivRealPi d).symm v))) := by
      ext v
      have hv : (complexPiEquivRealPi n).symm (firstCoords ℝ (2 * d) (2 * n) v) =
          firstCoords ℂ d n ((complexPiEquivRealPi d).symm v) := by
        rw [ContinuousLinearEquiv.symm_apply_eq, complexPiEquivRealPi_firstCoords,
          ContinuousLinearEquiv.apply_symm_apply]
      simp [OpenPartialHomeomorph.coe_trans_symm, hv]
    rw [hfun]
    simpa [OpenPartialHomeomorph.trans_apply, hpt] using han
  have heq : e '' S = ((complexPiEquivRealPi n).symm.trans e) '' (complexPiEquivRealPi n '' S) := by
    rw [← image_comp]
    ext y
    simp
  rw [heq]
  simpa [Function.comp_def] using
    hbase.comp_symm_continuousLinearEquiv ((complexPiEquivRealPi n).symm.trans e)

/-! ### The conjugation-fixed real locus in `ℂⁿ` -/

/-- The real locus `{z | star z = z}` is, in the real coordinates of `complexPiEquivRealPi`, the
preimage of a coordinate subspace under a coordinate permutation. -/
private theorem image_complexPiEquivRealPi_setOf_star_eq (n : ℕ) :
    ∃ τ : Fin (2 * n) ≃ Fin (2 * n),
      complexPiEquivRealPi n '' {z : Fin n → ℂ | star z = z} =
        (fun y : Fin (2 * n) → ℝ ↦ y ∘ τ) ⁻¹'
          {w : Fin (2 * n) → ℝ | ∀ k : Fin (2 * n), n ≤ k.val → w k = 0} := by
  let σ₀ : Fin 2 × Fin n ≃ Fin (2 * n) := finProdFinEquiv
  let σ₁ : Fin 2 × Fin n ≃ Fin (2 * n) :=
    ((Equiv.prodComm (Fin 2) (Fin n)).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm n 2))
  let τ : Fin (2 * n) ≃ Fin (2 * n) := σ₀.symm.trans σ₁
  have hσ₀ (i : Fin n) : σ₀ (1, i) = ⟨n + i.val, by omega⟩ := by
    ext
    simp [σ₀, finProdFinEquiv]
    omega
  have hσ₁ (i : Fin n) : σ₁ (1, i) = ⟨2 * i.val + 1, by omega⟩ := by
    ext
    simp [σ₁, finProdFinEquiv]
    omega
  refine ⟨τ, ?_⟩
  ext y
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  simp only [mem_preimage, mem_ofPred_eq, Function.comp_apply]
  constructor
  · intro hy ⟨k, hk⟩ hnk
    dsimp at hnk
    let i : Fin n := ⟨k - n, by omega⟩
    have hk_eq : (⟨k, hk⟩ : Fin (2 * n)) = σ₀ (1, i) := by
      rw [hσ₀]
      ext
      dsimp [i]
      omega
    have hτk : τ ⟨k, hk⟩ = ⟨2 * i.val + 1, by omega⟩ := by
      rw [hk_eq]
      simpa [τ] using hσ₁ i
    have him : ((complexPiEquivRealPi n).symm y i).im = 0 := by
      have := congrArg Complex.im (congrFun hy i)
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_im] at this
      linarith
    rw [complexPiEquivRealPi_symm_apply] at him
    rwa [hτk]
  · intro hy
    ext i
    rw [Pi.star_apply, Complex.star_def, complexPiEquivRealPi_symm_apply]
    have hτi : τ (σ₀ (1, i)) = ⟨2 * i.val + 1, by omega⟩ := by simpa [τ] using hσ₁ i
    have him : y ⟨2 * i.val + 1, by omega⟩ = 0 := by
      rw [← hτi]
      exact hy (σ₀ (1, i)) (by rw [hσ₀]; dsimp; omega)
    apply Complex.ext <;> simp [him]

/-- The conjugation-fixed locus `{z : Fin n → ℂ | star z = z}` maps under any continuous `ℝ`-linear
equivalence `(Fin n → ℂ) ≃L[ℝ] Fin m → ℝ` to an `n`-dimensional real analytic submanifold. -/
theorem isAnalyticSubmanifold_image_setOf_star_eq {n m : ℕ}
    (e : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ) :
    IsAnalyticSubmanifold n (e '' {z : Fin n → ℂ | star z = z}) := by
  obtain ⟨τ, hperm⟩ := image_complexPiEquivRealPi_setOf_star_eq n
  have hbase :
      IsAnalyticSubmanifold n (complexPiEquivRealPi n '' {z : Fin n → ℂ | star z = z}) := by
    rw [hperm]
    exact (isAnalyticSubmanifold_coordSubspace (by omega)).preimage_comp_equiv τ
  have heq : e '' {z : Fin n → ℂ | star z = z} =
      ((complexPiEquivRealPi n).symm.trans e) ''
        (complexPiEquivRealPi n '' {z : Fin n → ℂ | star z = z}) := by
    rw [← image_comp]
    ext y
    simp
  rw [heq]
  exact hbase.image_continuousLinearEquiv ((complexPiEquivRealPi n).symm.trans e)

/-- On any open subset `W ⊆ ℂⁿ` meeting `{z | star z = z}`, the real locus `{z ∈ W | star z = z}`
maps under any `(Fin n → ℂ) ≃L[ℝ] Fin m → ℝ` to an `n`-dimensional real analytic submanifold. -/
theorem _root_.IsOpen.isAnalyticSubmanifold_image_inter_setOf_star_eq {n m : ℕ}
    {W : Set (Fin n → ℂ)} (hW : IsOpen W) (hne : (W ∩ {z : Fin n → ℂ | star z = z}).Nonempty)
    (e : (Fin n → ℂ) ≃L[ℝ] Fin m → ℝ) :
    IsAnalyticSubmanifold n (e '' (W ∩ {z : Fin n → ℂ | star z = z})) := by
  have heq : e '' (W ∩ {z : Fin n → ℂ | star z = z}) =
      (e '' {z : Fin n → ℂ | star z = z}) ∩ (e '' W) := by
    rw [inter_comm, Set.image_inter e.injective]
  rw [heq]
  refine (isAnalyticSubmanifold_image_setOf_star_eq e).inter (e.toHomeomorph.isOpenMap W hW) ?_
  rw [← heq]
  exact hne.image e

end TauCeti

end
