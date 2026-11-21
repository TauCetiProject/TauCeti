/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.IntegralManifold.Basic
import TauCeti.Geometry.Manifold.Distribution.Levi
import TauCeti.Geometry.Manifold.VectorField.Immersion

/-!
# Integrable distributions are involutive

A distribution of class at least `C¹` is involutive when every point lies in an integral
manifold of regularity at least `C²`. This is the necessity direction of the Frobenius
integrability criterion: failure of involutivity obstructs integral manifolds through
every point.

The ambient manifold is at least `C²` and has a complete real model. It may have corners;
Hausdorffness and finite ambient dimension are not assumed. Integral manifolds carry their own
manifold structures; their maps need not be injective.

## Main results

* `TauCeti.IsContMDiffDistribution.isInvolutiveDistribution_of_forall_exists_integralManifold`:
  integral manifolds through every point imply involutivity.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Proposition 19.3, pp. 492–493 (integrability implies involutivity), using Corollary 8.32
  (tangent vector fields are closed under the Lie bracket).
-/

public section

open Set Filter Manifold VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

private local instance : IsManifold I 1 M := .of_le (n := 2) (by norm_num)

/-- A distribution of class at least `C¹` is involutive if every point belongs to a `C^m` integral
manifold with `2 ≤ m`, including smooth and analytic integral manifolds. The ambient manifold
is at least `C²` and its real model is complete. Finite dimensionality, separation axioms and
boundarylessness are not required. -/
theorem IsContMDiffDistribution.isInvolutiveDistribution_of_forall_exists_integralManifold
    {n : ℕ∞ω} {k : ℕ} {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (hD : IsContMDiffDistribution I n k D) (hn : 1 ≤ n) {m : ℕ∞ω} (hm : 2 ≤ m)
    (h : ∀ x : M, ∃ N : IntegralManifold (I := I) m D k, x ∈ range N.map) :
    IsInvolutiveDistribution I D := by
  apply (isInvolutiveDistribution_iff_distributionLeviForm_eq_zero hD hn).mpr
  intro x
  apply (distributionLeviForm_eq_zero_iff hD hn).mpr
  intro U hU hxU V W hV hW hVD hWD
  obtain ⟨N, y, hy⟩ := h x
  let _ : IsManifold (𝓡 k) 2 N.carrier := .of_le hm
  let _ : IsManifold (𝓡 k) 1 N.carrier := .of_le (n := 2) (by norm_num)
  -- Local tangency pulls back to differential-image membership along the integral immersion.
  have hpre : ∀ᶠ z in 𝓝 y, N.map z ∈ U :=
    N.contMDiff_map.continuous.continuousAt.preimage_mem_nhds
      (show U ∈ 𝓝 (N.map y) by rw [hy]; exact hU.mem_nhds hxU)
  have prepare (Z : ∀ z : M, TangentSpace I z) (hZ : CMDiff[U] n (T% Z))
      (hZD : ∀ z ∈ U, Z z ∈ D z) :
      ContMDiffAt I I.tangent 1 (T% Z) (N.map y) ∧
        ∀ᶠ z in 𝓝 y, Z (N.map z) ∈ (mfderiv (𝓡 k) I N.map z).range := by
    refine ⟨?_, hpre.mono fun z hz ↦ (N.range_mfderiv z).symm ▸ hZD _ hz⟩
    rw [hy]
    exact (hZ.contMDiffAt (hU.mem_nhds hxU)).of_le hn
  obtain ⟨hVN, hVtan⟩ := prepare V hV hVD
  obtain ⟨hWN, hWtan⟩ := prepare W hW hWD
  have hsplit : (mfderiv (𝓡 k) I N.map y).HasLeftInverse :=
    isDiffImmersionAt_iff.mp (N.isImmersion.isDiffImmersionAt
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) hm)) y)
  have : IsManifold (𝓡 k) (minSmoothness ℝ 2) N.carrier := by
    simpa using (inferInstance : IsManifold (𝓡 k) 2 N.carrier)
  have : IsManifold I (minSmoothness ℝ 2) M := by
    simpa using (inferInstance : IsManifold I 2 M)
  have hbr := (N.contMDiff_map y).mlieBracket_mem_range_mfderiv (by simpa using hm) hsplit
    hVN hWN hVtan hWtan
  rw [← hy]
  exact N.range_mfderiv y ▸ hbr

end TauCeti
