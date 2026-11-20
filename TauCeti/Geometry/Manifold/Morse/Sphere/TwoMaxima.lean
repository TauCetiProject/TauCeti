/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Sphere.Saddle
import TauCeti.AlgebraicTopology.Sphere.Puncture
import TauCeti.Geometry.Manifold.Morse.Boundary.OneTrajectory
import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation

/-!
# The Morse complex of the sphere with two maxima

Let `u` and `v` be orthogonal unit vectors of a real inner product space of dimension `n + 1`,
with `n ≥ 2`, and `0 < t < 2`. The function `f = hᵤ² + t hᵥ` on the sphere `Sⁿ`
(`TauCeti.Geometry.Manifold.Morse.Sphere.Saddle`) is a Morse function with four critical points:
the minimum `-v` of index `0`, the saddle `v` of index `n - 1` and two maxima of index `n`. For
every pseudo-gradient `X` adapted to `f`, this file computes the integral boundaries of the maxima
and of the saddle, and the coefficient of the saddle in the mod-two boundary of each maximum.

* `X` is Morse–Smale, whatever its choice: the saddle is the only critical point whose index is
  neither `0` nor `n`.
* **Each maximum sends exactly one trajectory to the saddle**
  (`ncard_morseTrajectorySlice_sphereHeight_sq_add_smul_sphereHeight`).
  The stable manifold of the saddle is the saddle together with two trajectories, and since the
  sphere minus the minimum is connected, every maximum sends one of them
  (`TauCeti.IsAdaptedPseudoGradient.ncard_morseTrajectorySlice_eq_one_of_isPreconnected`). On the
  torus with one maximum, both trajectories into a saddle come from that maximum, so this is a
  global fact about the sphere.
* So the saddle has coefficient `1` in the mod-two boundary of each maximum
  (`IsMorseSmale.morseBoundaryCoeff_eq_one_sphereHeight_sq_add_smul_sphereHeight`), and the
  integral boundary of each maximum is `±` the saddle, with the sign given by the orientations of
  the unstable manifolds (`signedMorseBoundary_single_sphereHeight_sq_add_smul_sphereHeight`).
  The integral boundary of the saddle vanishes
  (`signedMorseBoundary_single_eq_zero_sphereHeight_sq_add_smul_sphereHeight`): for
  `n = 2` its two trajectories to the minimum carry opposite signs, and for `n ≥ 3` there is no
  critical point of index `n - 2`.
* Reversing the orientations at the maxima whose boundary is `-v`, the orientations can be chosen
  so that both maxima have boundary the saddle
  (`exists_signedMorseBoundaryCoeff_eq_one_sphereHeight_sq_add_smul_sphereHeight`).
  Then the difference of the two maxima is a cycle
  (`signedMorseBoundary_single_sub_single_eq_zero_sphereHeight_sq_add_smul_sphereHeight`), while
  neither maximum alone is one, its boundary being `±v`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (orientations, and the Morse complex of the sphere with two
  maxima, a saddle and a minimum).
-/

public section

open Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {u v : sphere (0 : E) 1} {t : ℝ}

namespace IsAdaptedPseudoGradient

/-- The critical points of `hᵤ² + t hᵥ` for `0 < t < 2` are the poles `±v` and points of index
`n`. -/
private theorem eq_or_eq_or_manifoldMorseIndex_eq (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t)
    (ht₂ : t < 2) {y : sphere (0 : E) 1}
    (hy : mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight u ^ 2 + t • sphereHeight v) y = 0) :
    y = v ∨ y = -v ∨ manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) y = n := by
  rcases (mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀.ne').1
    (mem_criticalPoints_iff_mfderiv_eq_zero.2 hy) with h | h | ⟨h₁, h₂⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_of_eq huv h₁ h₂
      (by nlinarith)))

/-- The poles are critical points of `hᵤ² + t hᵥ`. -/
private theorem mfderiv_eq_zero_of_eq_or_eq (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t)
    {y : sphere (0 : E) 1} (hy : y = v ∨ y = -v) :
    mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight u ^ 2 + t • sphereHeight v) y = 0 :=
  mem_criticalPoints_iff_mfderiv_eq_zero.1
    ((mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀.ne').2
      (hy.imp id Or.inl))

/-- The index of a point of index `n` is one more than the index of the saddle `v` of
`hᵤ² + t hᵥ`. -/
private theorem manifoldMorseIndex_eq_add_one_of_eq_finrank (huv : ⟪(u : E), (v : E)⟫ = 0)
    (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2) {p q : sphere (0 : E) 1}
    (hp : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) p = n)
    (hq : q = v) :
    manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) p =
      manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) q + 1 := by
  rw [hq, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀ ht₂, hp]
  omega

variable [FiniteDimensional ℝ E] {X : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}

/-- **The function `hᵤ² + t hᵥ` is Morse–Smale for every pseudo-gradient.** For `0 < t < 2`,
every pseudo-gradient adapted to `hᵤ² + t hᵥ` on the sphere satisfies the Morse–Smale condition:
its saddle `v` is its only critical point of index neither `0` nor `n`. -/
theorem isMorseSmale_sphereHeight_sq_add_smul_sphereHeight (huv : ⟪(u : E), (v : E)⟫ = 0)
    (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X) :
    hX.IsMorseSmale := by
  refine IsMorseSmale.of_subsingleton
    (isMorse_sphereHeight_sq_add_smul_sphereHeight huv ht₀.ne' (by nlinarith))
    (subsingleton_singleton (a := v) |>.anti fun y ⟨hy, hy0, hyn⟩ ↦ ?_)
  rw [finrank_euclideanSpace_fin] at hyn
  rcases eq_or_eq_or_manifoldMorseIndex_eq huv ht₀ ht₂ hy with rfl | rfl | h
  · rfl
  · exact absurd (manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self huv ht₀) hy0
  · exact absurd h hyn

/-- **One trajectory from each maximum to the saddle.** For `n ≥ 2`, `0 < t < 2` and every
pseudo-gradient adapted to `hᵤ² + t hᵥ` on `Sⁿ`, exactly one trajectory runs from each critical
point of index `n` to the saddle `v`. -/
theorem ncard_morseTrajectorySlice_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    {m : sphere (0 : E) 1}
    (hm : mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight u ^ 2 + t • sphereHeight v) m = 0)
    (hmind : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) m = n) :
    (hX.morseTrajectorySlice m v).ncard = 1 := by
  have hf := isMorse_sphereHeight_sq_add_smul_sphereHeight (n := n) huv ht₀.ne' (by nlinarith)
  have hvind := manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self (n := n) huv ht₀ ht₂
  have hv0 := manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self (n := n) huv ht₀
  replace hmind := hmind.trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)).symm
  -- The minimum `-v` is the only critical point of index `0`.
  have hmin : {y : sphere (0 : E) 1 |
      mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight u ^ 2 + t • sphereHeight v) y = 0 ∧
        manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) y = 0} = {-v} := by
    ext y
    refine ⟨fun ⟨hy, hy0⟩ ↦ ?_, fun hy ↦ ?_⟩
    · rcases eq_or_eq_or_manifoldMorseIndex_eq huv ht₀ ht₂ hy with rfl | rfl | h
      · omega
      · rfl
      · omega
    · rw [mem_singleton_iff] at hy
      exact ⟨mfderiv_eq_zero_of_eq_or_eq huv ht₀ (Or.inr hy), hy ▸ hv0⟩
  -- The sphere minus a point is contractible.
  have hconn : IsPreconnected ({-v} : Set (sphere (0 : E) 1))ᶜ :=
    have := contractibleSpace_sphere_compl_singleton (-v)
    isPreconnected_iff_preconnectedSpace.2 inferInstance
  -- A second critical point of index `n`.
  have hcount := criticalCount_sphereHeight_sq_add_smul_sphereHeight huv hn ht₀.ne'
    (by nlinarith) n
  simp only [↓reduceIte, criticalCount_def, encard_eq_two] at hcount
  obtain ⟨a, b, hab, hset⟩ := hcount
  have hmem : m ∈ {x ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) |
      manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = n} :=
    ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hm, by rwa [finrank_euclideanSpace_fin] at hmind⟩
  obtain ⟨m', hm'mem, hmm'⟩ : ∃ m' ∈ ({a, b} : Set (sphere (0 : E) 1)), m ≠ m' := by
    rw [hset, mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨b, by simp, hab⟩
    · exact ⟨a, by simp, hab.symm⟩
  rw [← hset] at hm'mem
  refine hX.ncard_morseTrajectorySlice_eq_one_of_isPreconnected hf
    (mfderiv_eq_zero_of_eq_or_eq huv ht₀ (Or.inl rfl)) (by rw [finrank_euclideanSpace_fin]; omega)
    (fun y hy hyv ↦ ?_) (hmin ▸ hconn) hm hmind
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hm'mem.1)
    (by rw [finrank_euclideanSpace_fin]; exact hm'mem.2) hmm'
  rcases eq_or_eq_or_manifoldMorseIndex_eq huv ht₀ ht₂ hy with rfl | rfl | h
  · exact absurd rfl hyv
  · exact Or.inl hv0
  · exact Or.inr (by rw [finrank_euclideanSpace_fin, h])

/-- **The integral boundary of a maximum is `±` the saddle.** For `n ≥ 2` and `0 < t < 2`, the
integral Morse boundary of `a` times a critical point `p` of index `n` of `hᵤ² + t hᵥ` is `±a`
times the saddle `v`, the sign being `signedMorseBoundaryCoeff 𝔬 p q`, which is `1` or `-1`
(`signedMorseBoundaryCoeff_eq_one_or_eq_neg_one_sphereHeight_sq_add_smul_sphereHeight`). -/
theorem signedMorseBoundary_single_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    (hf : IsMorse (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (𝔬 : MorseOrientation (sphereHeight u ^ 2 + t • sphereHeight v) X) {R : Type*} [Ring R]
    {p q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
    (hp : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
        (p : sphere (0 : E) 1) = n)
    (hq : (q : sphere (0 : E) 1) = v) (a : R) :
    hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p a) =
      Finsupp.single q (a * (hX.signedMorseBoundaryCoeff 𝔬 p q : R)) := by
  ext r
  rw [signedMorseBoundary_single_apply]
  by_cases hrq : r = q
  · rw [hrq, Finsupp.single_eq_same]
  rw [Finsupp.single_eq_of_ne hrq]
  -- The only critical point of index `n - 1` is the saddle.
  suffices hpr : hX.signedMorseBoundaryCoeff 𝔬 p r = 0 by rw [hpr, Int.cast_zero, mul_zero]
  by_contra hpr
  have hind := morseIndex_eq_add_one_of_signedMorseBoundaryCoeff_ne_zero hpr
  rcases eq_or_eq_or_manifoldMorseIndex_eq huv ht₀ ht₂
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 r.2) with hr | hr | hr
  · exact hrq (Subtype.ext (hr.trans hq.symm))
  · rw [hr, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self huv ht₀] at hind
    omega
  · omega

/-- **The integral boundary of a maximum is `±` the saddle: the coefficient.** For `n ≥ 2` and
`0 < t < 2`, the coefficient of the saddle `v` in the integral Morse boundary of a critical point
of index `n` of `hᵤ² + t hᵥ` is `1` or `-1`, for every choice of orientations: it is the sign of
the only trajectory from that critical point to `v`. -/
theorem signedMorseBoundaryCoeff_eq_one_or_eq_neg_one_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    (𝔬 : MorseOrientation (sphereHeight u ^ 2 + t • sphereHeight v) X)
    {p q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
    (hp : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
        (p : sphere (0 : E) 1) = n)
    (hq : (q : sphere (0 : E) 1) = v) :
    hX.signedMorseBoundaryCoeff 𝔬 p q = 1 ∨ hX.signedMorseBoundaryCoeff 𝔬 p q = -1 := by
  have h := hX.isMorseSmale_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂
  have hf := isMorse_sphereHeight_sq_add_smul_sphereHeight (n := n) huv ht₀.ne' (by nlinarith)
  have hone := hX.ncard_morseTrajectorySlice_sphereHeight_sq_add_smul_sphereHeight huv hn ht₀ ht₂
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2) hp
  obtain ⟨y, hy⟩ := ncard_eq_one.1 hone
  replace hy : hX.morseTrajectorySlice p q = {y} := by rw [hq]; exact hy
  have hyuq : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q := by
    have hy' : y ∈ hX.morseTrajectorySlice p q := hy ▸ mem_singleton y
    rw [mem_morseTrajectorySlice] at hy'
    exact ⟨hy'.1, hy'.2.1⟩
  rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one
      (manifoldMorseIndex_eq_add_one_of_eq_finrank huv hn ht₀ ht₂ hp hq),
    signedTrajectoryCount_def, hy, finsum_mem_singleton]
  exact trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q)
    h hf hyuq

/-- **The saddle is an integral cycle.** For `n ≥ 2` and `0 < t < 2`, the integral Morse boundary
of the saddle `v` of `hᵤ² + t hᵥ` vanishes, for every choice of orientations: for `n = 2` its two
trajectories to the minimum carry opposite signs, and for `n ≥ 3` there is no critical point of
index `n - 2`. -/
theorem signedMorseBoundary_single_eq_zero_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    (hf : IsMorse (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (𝔬 : MorseOrientation (sphereHeight u ^ 2 + t • sphereHeight v) X) {R : Type*} [Ring R]
    {q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
    (hq : (q : sphere (0 : E) 1) = v) (a : R) :
    hX.signedMorseBoundary 𝔬 hf R (Finsupp.single q a) = 0 := by
  have h := hX.isMorseSmale_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂
  ext r
  rw [signedMorseBoundary_single_apply, Finsupp.coe_zero, Pi.zero_apply]
  suffices hqr : hX.signedMorseBoundaryCoeff 𝔬 q r = 0 by rw [hqr, Int.cast_zero, mul_zero]
  have hv0 := manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self (n := n) huv ht₀
  by_cases hr : (r : sphere (0 : E) 1) = -v
  · -- The minimum is the only critical point of index `0`.
    obtain ⟨r, hr'⟩ := r
    dsimp only at hr
    subst hr
    refine h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬 (fun y hy hy0 ↦ ?_) q
    rcases eq_or_eq_or_manifoldMorseIndex_eq huv ht₀ ht₂ hy with rfl | rfl | hyn
    · rw [manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀ ht₂] at hy0
      omega
    · rfl
    · omega
  by_contra hqr
  have hind := morseIndex_eq_add_one_of_signedMorseBoundaryCoeff_ne_zero hqr
  rw [hq, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀ ht₂] at hind
  rcases eq_or_eq_or_manifoldMorseIndex_eq huv ht₀ ht₂
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 r.2) with hrv | hrv | hrn
  · rw [hrv, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀ ht₂] at hind
    omega
  · exact hr hrv
  · omega

namespace IsMorseSmale

/-- **The mod-two coefficient of the saddle in the boundary of a maximum is `1`.** For `n ≥ 2`
and `0 < t < 2`, the coefficient of the saddle `v` in the mod-two Morse boundary of a critical
point of index `n` of `hᵤ² + t hᵥ` is `1`. -/
theorem morseBoundaryCoeff_eq_one_sphereHeight_sq_add_smul_sphereHeight
    {hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X}
    (h : hX.IsMorseSmale) (hf : IsMorse (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (huv : ⟪(u : E), (v : E)⟫ = 0) (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2)
    {p q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
    (hp : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
        (p : sphere (0 : E) 1) = n)
    (hq : (q : sphere (0 : E) 1) = v) : h.morseBoundaryCoeff hf p q = 1 := by
  rw [h.morseBoundaryCoeff_eq_ncard hf
      (manifoldMorseIndex_eq_add_one_of_eq_finrank huv hn ht₀ ht₂ hp hq), hq,
    hX.ncard_morseTrajectorySlice_sphereHeight_sq_add_smul_sphereHeight huv hn ht₀ ht₂
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2) hp, Nat.cast_one]

end IsMorseSmale

/-- **Orientations making both maxima bound the saddle.** For `n ≥ 2` and `0 < t < 2`, every
pseudo-gradient adapted to `hᵤ² + t hᵥ` has orientation data for which the integral boundary of
each critical point of index `n` is exactly the saddle `v`. They are obtained from any orientation
data by reversing the orientations at the maxima whose boundary is `-v`. -/
theorem exists_signedMorseBoundaryCoeff_eq_one_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X) :
    ∃ 𝔬 : MorseOrientation (sphereHeight u ^ 2 + t • sphereHeight v) X,
      ∀ p q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v),
        manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
            (p : sphere (0 : E) 1) = n →
          (q : sphere (0 : E) 1) = v → hX.signedMorseBoundaryCoeff 𝔬 p q = 1 := by
  classical
  obtain ⟨𝔬⟩ := hX.nonempty_morseOrientation
  -- Reverse the orientations at the critical points whose boundary coefficient along `v` is `-1`.
  set S := {p : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) |
    ∀ q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v),
      (q : sphere (0 : E) 1) = v → hX.signedMorseBoundaryCoeff 𝔬 p q = -1}
  refine ⟨𝔬.reverse S, fun p q hp hq ↦ ?_⟩
  have hqS : q ∉ S := fun hqS ↦ by
    have := hqS q hq
    rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega)] at this
    norm_num at this
  rw [signedMorseBoundaryCoeff_reverse]
  rcases hX.signedMorseBoundaryCoeff_eq_one_or_eq_neg_one_sphereHeight_sq_add_smul_sphereHeight huv
    hn ht₀ ht₂ 𝔬 hp hq with hc | hc
  · have hpS : p ∉ S := fun hpS ↦ by
      have := hpS q hq
      rw [hc] at this
      norm_num at this
    simp [hpS, hqS, hc]
  · have hpS : p ∈ S := fun q' hq' ↦ (Subtype.ext (hq'.trans hq.symm) : q' = q) ▸ hc
    simp [hpS, hqS, hc]

/-- **The difference of the two maxima is an integral cycle.** For `n ≥ 2` and `0 < t < 2`, with
orientation data for which both critical points of index `n` of `hᵤ² + t hᵥ` have boundary the
saddle, as `exists_signedMorseBoundaryCoeff_eq_one_sphereHeight_sq_add_smul_sphereHeight` provides,
the boundary of `a p₁ - a p₂` vanishes for any two critical points `p₁` and `p₂` of index `n`. -/
theorem signedMorseBoundary_single_sub_single_eq_zero_sphereHeight_sq_add_smul_sphereHeight
    (huv : ⟪(u : E), (v : E)⟫ = 0) (hn : 2 ≤ n) (ht₀ : 0 < t) (ht₂ : t < 2)
    (hX : IsAdaptedPseudoGradient (sphereHeight u ^ 2 + t • sphereHeight v) X)
    (hf : IsMorse (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    {𝔬 : MorseOrientation (sphereHeight u ^ 2 + t • sphereHeight v) X}
    (h𝔬 : ∀ p q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v),
      manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
          (p : sphere (0 : E) 1) = n →
        (q : sphere (0 : E) 1) = v → hX.signedMorseBoundaryCoeff 𝔬 p q = 1)
    {R : Type*} [Ring R] {p₁ p₂ : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)}
    (hp₁ : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
        (p₁ : sphere (0 : E) 1) = n)
    (hp₂ : manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
        (p₂ : sphere (0 : E) 1) = n) (a : R) :
    hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p₁ a - Finsupp.single p₂ a) = 0 := by
  set q : criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) :=
    ⟨v, mem_criticalPoints_iff_mfderiv_eq_zero.2 (mfderiv_eq_zero_of_eq_or_eq huv ht₀ (Or.inl rfl))⟩
  rw [map_sub, signedMorseBoundary_single_sphereHeight_sq_add_smul_sphereHeight huv hn ht₀ ht₂ hX
      hf 𝔬 hp₁ (q := q) rfl,
    signedMorseBoundary_single_sphereHeight_sq_add_smul_sphereHeight huv hn ht₀ ht₂ hX hf 𝔬 hp₂
      (q := q) rfl, h𝔬 p₁ q hp₁ rfl, h𝔬 p₂ q hp₂ rfl, sub_self]

end IsAdaptedPseudoGradient

end TauCeti
