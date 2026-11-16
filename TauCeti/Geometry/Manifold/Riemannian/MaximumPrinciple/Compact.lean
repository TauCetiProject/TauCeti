/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# The weak maximum principle on compact sets

Let `K` be a compact subset of a boundaryless Riemannian manifold. Its *boundary part*
`K \ interior K` plays the role of the boundary of a domain. This file proves the classical weak
maximum principle on `K` for the Laplace–Beltrami operator `Δ = div ∘ grad`.

If `Δ w > 0` on the interior of `K`, then `w` attains its maximum over `K` at a point of
`K \ interior K`, because at an interior maximum the Laplacian is nonpositive. If moreover
`Δ u ≥ 0` on the interior of `K`, then the same holds for `u + ε w` for every `ε > 0`, and letting
`ε → 0` shows that `u` is bounded on `K` by its bounds on `K \ interior K`. In Euclidean space
`w = |x|²` is such a strict subsolution; on a general manifold one has to be supplied.

## Main results

* `TauCeti.Manifold.exists_mem_diff_interior_isMaxOn_of_laplaceBeltrami_pos`: a function with
  positive Laplacian on the interior of a nonempty compact set `K` attains its maximum over `K`
  on `K \ interior K`.
* `TauCeti.Manifold.le_of_forall_mem_diff_interior_le`: the weak maximum principle for
  subharmonic functions, in the presence of a strict subsolution.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, Theorem 3.1.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {K : Set M}

/-- **Strict weak maximum principle.** A function that is continuous on a nonempty compact set
`K`, and `C²` with positive Laplacian on the interior of `K`, attains its maximum over `K` at a
point of `K \ interior K`. -/
theorem exists_mem_diff_interior_isMaxOn_of_laplaceBeltrami_pos (hK : IsCompact K)
    (hne : K.Nonempty) {w : M → ℝ} (hcont : ContinuousOn w K)
    (hw : ∀ x ∈ interior K, ContMDiffAt I 𝓘(ℝ) 2 w x)
    (hpos : ∀ x ∈ interior K, 0 < laplaceBeltrami I w x) :
    ∃ x ∈ K \ interior K, IsMaxOn w K x := by
  obtain ⟨x, hxK, hmax⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨x, ⟨hxK, fun hx ↦ ?_⟩, hmax⟩
  exact (hpos x hx).not_ge (laplaceBeltrami_nonpos_of_isLocalMax (hw x hx)
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.1 hx)))

/-- **Weak maximum principle.** Let `K` be compact and let `u` be a `C²` function with
`Δ u ≥ 0` on the interior of `K`. If some `C²` function `w` has `Δ w > 0` on the interior of
`K`, then every upper bound of `u` on `K \ interior K` is an upper bound of `u` on `K`. -/
theorem le_of_forall_mem_diff_interior_le (hK : IsCompact K) {u w : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hw : ContMDiff I 𝓘(ℝ) 2 w)
    (hΔu : ∀ x ∈ interior K, 0 ≤ laplaceBeltrami I u x)
    (hΔw : ∀ x ∈ interior K, 0 < laplaceBeltrami I w x) {c : ℝ}
    (hc : ∀ x ∈ K \ interior K, u x ≤ c) {x : M} (hx : x ∈ K) : u x ≤ c := by
  obtain ⟨x₁, -, hx₁⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hw.continuous.continuousOn
  have hD : 0 ≤ w x₁ - w x := sub_nonneg.2 (hx₁ hx)
  have key (ε : ℝ) (hε : 0 < ε) : u x ≤ c + ε * (w x₁ - w x) := by
    have hεw : ContMDiff I 𝓘(ℝ) 2 (ε • w) :=
      (contMDiff_const (c := ε)).mul hw
    have hv : ContMDiff I 𝓘(ℝ) 2 (u + ε • w) := hu.add hεw
    obtain ⟨z, hz, hmax⟩ := exists_mem_diff_interior_isMaxOn_of_laplaceBeltrami_pos hK
      ⟨x, hx⟩ hv.continuous.continuousOn (fun y _ ↦ hv.contMDiffAt) fun y hy ↦ by
        rw [laplaceBeltrami_add (hf := hu) (hg := hεw), laplaceBeltrami_smul (hf := hw)]
        exact add_pos_of_nonneg_of_pos (hΔu y hy) (mul_pos hε (hΔw y hy))
    have h : u x + ε * w x ≤ u z + ε * w z := isMaxOn_iff.1 hmax x hx
    have h₁ : w z ≤ w x₁ := isMaxOn_iff.1 hx₁ z hz.1
    nlinarith [hc z hz, mul_le_mul_of_nonneg_left h₁ hε.le]
  refine le_of_forall_pos_le_add fun δ hδ ↦ (key (δ / (w x₁ - w x + 1)) (by positivity)).trans ?_
  gcongr
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

end TauCeti.Manifold
