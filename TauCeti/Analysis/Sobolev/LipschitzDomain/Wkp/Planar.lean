/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Plane
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.LinearIsometry
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Rellich–Kondrachov and Morrey on planar discs and half-discs

The Lipschitz-domain theorems for `W^{k,p}`, transported to isometric copies of the model space in
`TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.LinearIsometry`, specialise to the two planar domains
of the analysis of pseudoholomorphic curves:

* a disc `Metric.ball c r ⊆ ℂ`, whose image under `Complex.equivRealProdL2` is the ball
  `ball (equivRealProdL2 c) r` of the model space `WithLp 2 (ℝ × ℝ)`
  (`TauCeti.isLipschitzDomainWith_ball`);
* the half-disc `{z | |z| < r, 0 < Im z}`, the preimage of the model half-disc
  `TauCeti.halfDisc r` under `Complex.equivRealProdL2Swap`, which puts the normal coordinate
  `Im z` first (`TauCeti.exists_isLipschitzDomainWith_halfDisc`).

On both, forgetting the highest weak derivative is a compact operator `W^{k+1,p} → W^{k,p}` for
every `k` and every `1 ≤ p ≤ ∞`, and for `2 < k p` every member of `W^{k,p}` has a representative
which is Hölder of exponent `1 - 2/(k p)` up to the boundary, depending linearly and boundedly on
it. These are global statements on the closed disc and the closed half-disc; the local forms on
open subsets of `ℂ` and of the closed upper half-plane are stated for `TauCeti.MemWkpLoc` in
`TauCeti.Analysis.Sobolev.Local`.

## Main declarations

* `TauCeti.Wkp.isCompactOperator_lowerOrderL_complexBall`,
  `TauCeti.Wkp.isCompactOperator_lowerOrderL_complexHalfDisc`: Rellich–Kondrachov.
* `TauCeti.Wkp.exists_morreyEmbeddingL_complexBall`,
  `TauCeti.Wkp.exists_morreyEmbeddingL_complexHalfDisc`: the Morrey embedding
  `W^{k+1,p} → C^{0,1-2/q}` for `1/p - k/2 ≤ 1/q ≤ 1/p` and `2 < q < ∞`.
* `TauCeti.Wkp.exists_holderEmbeddingL_complexBall`,
  `TauCeti.Wkp.exists_holderEmbeddingL_complexHalfDisc`: the Hölder embedding
  `W^{k,p} → C^{0,1-2/(k p)}` for `2 < k p`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix B.1.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorems 4.12 and 6.3.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Metric MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace Wkp

/-- The image of a disc of `ℂ` under `Complex.equivRealProdL2` is a Lipschitz domain. For a
nonpositive radius the disc is empty. -/
private theorem isLipschitzDomainWith_image_complexBall (c : ℂ) (r : ℝ) :
    (Complex.equivRealProdL2 '' ball c r).IsLipschitzDomainWith 1 := by
  rw [Complex.equivRealProdL2.image_ball]
  rcases lt_or_ge 0 r with hr | hr
  · exact isLipschitzDomainWith_ball _ hr one_pos
  · rw [ball_eq_empty.2 hr]
    exact (isLipschitzDomainWith_iff _ _).2 ⟨isOpen_empty, by simp⟩

/-- The image of the half-disc `{z | |z| < r, 0 < Im z}` under `Complex.equivRealProdL2Swap` is
the model half-disc, a Lipschitz domain. -/
private theorem exists_isLipschitzDomainWith_image_complexHalfDisc (r : ℝ) :
    ∃ L : ℝ≥0, (Complex.equivRealProdL2Swap ''
      (Complex.equivRealProdL2Swap ⁻¹' (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))).IsLipschitzDomainWith
        L := by
  rw [image_preimage_eq _ Complex.equivRealProdL2Swap.surjective]
  exact exists_isLipschitzDomainWith_halfDisc r

/-- The half-disc `{z | |z| < r, 0 < Im z}` is bounded. -/
private theorem isBounded_complexHalfDisc (r : ℝ) :
    IsBounded (Complex.equivRealProdL2Swap ⁻¹' (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) := by
  refine (isBounded_ball (x := (0 : ℂ)) (r := r)).subset fun z hz => ?_
  rw [mem_ball, dist_zero_right, ← Complex.equivRealProdL2Swap.norm_map]
  exact (mem_halfDisc.1 hz).1

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Rellich–Kondrachov on a disc.** On a disc `Metric.ball c r` of `ℂ`, forgetting the highest
weak derivative is a compact operator `W^{k+1,p} → W^{k,p}` for every `k` and every
`1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_lowerOrderL_complexBall (c : ℂ) (r : ℝ) (k : ℕ) :
    IsCompactOperator (lowerOrderL (mu := volume) (p := p)
      (Omega := ⟨ball c r, isOpen_ball⟩) k) :=
  isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image Complex.equivRealProdL2
    (isLipschitzDomainWith_image_complexBall c r) isBounded_ball k

/-- **Rellich–Kondrachov on the planar half-disc.** On the half-disc
`{z | |z| < r, 0 < Im z} = Complex.equivRealProdL2Swap ⁻¹' halfDisc r` in `ℂ`, forgetting the
highest weak derivative is a compact operator `W^{k+1,p} → W^{k,p}` for every `k` and every
`1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_lowerOrderL_complexHalfDisc (r : ℝ) (k : ℕ) :
    IsCompactOperator (lowerOrderL (mu := volume) (p := p)
      (Omega := ⟨Complex.equivRealProdL2Swap ⁻¹' halfDisc r,
        (halfDisc r).isOpen.preimage Complex.equivRealProdL2Swap.continuous⟩) k) := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_image_complexHalfDisc r
  exact isCompactOperator_lowerOrderL_of_isLipschitzDomainWith_image (L := L)
    Complex.equivRealProdL2Swap hL (isBounded_complexHalfDisc r) k

/-- **Morrey's embedding on a disc.** On a disc `Metric.ball c r` of `ℂ`, if
`1/p - k/2 ≤ 1/q ≤ 1/p` with `2 < q < ∞`, every `u ∈ W^{k+1,p}` agrees almost everywhere with a
function on the closed disc which is Hölder of exponent `1 - 2/q`, depending linearly and
boundedly on `u`. -/
theorem exists_morreyEmbeddingL_complexBall (c : ℂ) (r : ℝ) (k : ℕ) {q : ℝ≥0} (hq : 2 < q)
    (hq₁ : p⁻¹ ≤ (q : ℝ≥0∞)⁻¹ + k * 2⁻¹) (hq₂ : (q : ℝ≥0∞)⁻¹ ≤ p⁻¹) :
    ∃ T : Wkp volume (⟨ball c r, isOpen_ball⟩ : Opens ℂ) p (k + 1) →L[ℝ]
        HolderSpace (1 - 2 / q) (closure (ball c r)) ℝ,
      ∀ u, ∀ᵐ z ∂volume, ∀ hz : z ∈ ball c r,
        T u ⟨z, subset_closure hz⟩ = value (k + 1) u z := by
  have h := exists_morreyEmbeddingL_of_isLipschitzDomainWith_image (p := p) (q := q)
    Complex.equivRealProdL2 (Ω := ⟨ball c r, isOpen_ball⟩)
    (isLipschitzDomainWith_image_complexBall c r) isBounded_ball k
    (by simpa [Complex.finrank_real_complex] using hq)
    (by simpa [Complex.finrank_real_complex] using hq₁) hq₂
  rw [Complex.finrank_real_complex, Nat.cast_ofNat] at h
  exact h

/-- **Morrey's embedding on the planar half-disc.** On the half-disc
`{z | |z| < r, 0 < Im z}`, if `1/p - k/2 ≤ 1/q ≤ 1/p` with `2 < q < ∞`, every `u ∈ W^{k+1,p}`
agrees almost everywhere with a function on the closed half-disc which is Hölder of exponent
`1 - 2/q`, depending linearly and boundedly on `u`. -/
theorem exists_morreyEmbeddingL_complexHalfDisc (r : ℝ) (k : ℕ) {q : ℝ≥0} (hq : 2 < q)
    (hq₁ : p⁻¹ ≤ (q : ℝ≥0∞)⁻¹ + k * 2⁻¹) (hq₂ : (q : ℝ≥0∞)⁻¹ ≤ p⁻¹) :
    ∃ T : Wkp volume (⟨Complex.equivRealProdL2Swap ⁻¹' halfDisc r,
          (halfDisc r).isOpen.preimage Complex.equivRealProdL2Swap.continuous⟩ : Opens ℂ) p
          (k + 1) →L[ℝ]
        HolderSpace (1 - 2 / q) (closure (Complex.equivRealProdL2Swap ⁻¹' halfDisc r)) ℝ,
      ∀ u, ∀ᵐ z ∂volume, ∀ hz : z ∈ Complex.equivRealProdL2Swap ⁻¹' halfDisc r,
        T u ⟨z, subset_closure hz⟩ = value (k + 1) u z := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_image_complexHalfDisc r
  have h := exists_morreyEmbeddingL_of_isLipschitzDomainWith_image (p := p) (q := q)
    Complex.equivRealProdL2Swap (Ω := ⟨_, (halfDisc r).isOpen.preimage
      Complex.equivRealProdL2Swap.continuous⟩) hL (isBounded_complexHalfDisc r) k
    (by simpa [Complex.finrank_real_complex] using hq)
    (by simpa [Complex.finrank_real_complex] using hq₁) hq₂
  rw [Complex.finrank_real_complex, Nat.cast_ofNat] at h
  exact h

/-- **Hölder embedding on a disc.** On a disc `Metric.ball c r` of `ℂ`, if `1 ≤ p < ∞` and
`2 < k p`, every `u ∈ W^{k,p}` agrees almost everywhere with a function on the closed disc which
is Hölder of exponent `1 - 2/(k p)`, depending linearly and boundedly on `u`. In particular
members of `W^{k,p}` with `2 < k p` are continuous up to the boundary. -/
theorem exists_holderEmbeddingL_complexBall {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (c : ℂ) (r : ℝ)
    {k : ℕ} (hkp : 2 < k * p) :
    ∃ T : Wkp volume (⟨ball c r, isOpen_ball⟩ : Opens ℂ) p k →L[ℝ]
        HolderSpace (1 - 2 / (k * p)) (closure (ball c r)) ℝ,
      ∀ u, ∀ᵐ z ∂volume, ∀ hz : z ∈ ball c r, T u ⟨z, subset_closure hz⟩ = value k u z := by
  have h := exists_holderEmbeddingL_of_isLipschitzDomainWith_image (p := p)
    Complex.equivRealProdL2 (Ω := ⟨ball c r, isOpen_ball⟩)
    (isLipschitzDomainWith_image_complexBall c r) isBounded_ball (k := k)
    (by simpa [Complex.finrank_real_complex] using hkp)
  rw [Complex.finrank_real_complex, Nat.cast_ofNat] at h
  exact h

/-- **Hölder embedding on the planar half-disc.** On the half-disc `{z | |z| < r, 0 < Im z}`, if
`1 ≤ p < ∞` and `2 < k p`, every `u ∈ W^{k,p}` agrees almost everywhere with a function on the
closed half-disc which is Hölder of exponent `1 - 2/(k p)`, depending linearly and boundedly on
`u`. In particular members of `W^{k,p}` with `2 < k p` are continuous up to the real axis. -/
theorem exists_holderEmbeddingL_complexHalfDisc {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (r : ℝ)
    {k : ℕ} (hkp : 2 < k * p) :
    ∃ T : Wkp volume (⟨Complex.equivRealProdL2Swap ⁻¹' halfDisc r,
          (halfDisc r).isOpen.preimage Complex.equivRealProdL2Swap.continuous⟩ : Opens ℂ) p
          k →L[ℝ]
        HolderSpace (1 - 2 / (k * p)) (closure (Complex.equivRealProdL2Swap ⁻¹' halfDisc r)) ℝ,
      ∀ u, ∀ᵐ z ∂volume, ∀ hz : z ∈ Complex.equivRealProdL2Swap ⁻¹' halfDisc r,
        T u ⟨z, subset_closure hz⟩ = value k u z := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_image_complexHalfDisc r
  have h := exists_holderEmbeddingL_of_isLipschitzDomainWith_image (p := p)
    Complex.equivRealProdL2Swap (Ω := ⟨_, (halfDisc r).isOpen.preimage
      Complex.equivRealProdL2Swap.continuous⟩) hL (isBounded_complexHalfDisc r) (k := k)
    (by simpa [Complex.finrank_real_complex] using hkp)
  rw [Complex.finrank_real_complex, Nat.cast_ofNat] at h
  exact h

end Wkp

end TauCeti
