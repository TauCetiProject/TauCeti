/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Convergence

/-!
# Solving Poisson's equation along an exhaustion

Let `Ω` be a subset of a finite-dimensional real inner product space, exhausted by sets
`K n ⊆ interior (K (n + 1))`, so that `Ω` is open, and let `F` be a finite-dimensional real
normed space. Suppose `uₙ : E → F` is of class `C^k`, `k ≥ 2`, at every point of `K n` and solves
Poisson's equation `Δuₙ = f` near `K n`. Two successive local solutions differ near `K n` by a
harmonic function. If `Hₙ` is harmonic on all of `Ω` and approximates `uₙ₊₁ - uₙ` uniformly on
`K n` with summable errors, then the corrected telescoping series

`v = u₀ + ∑ₙ (uₙ₊₁ - uₙ - Hₙ)`

is of class `C^k` on `Ω` and solves `Δv = f` on all of `Ω`.

This is the step that turns approximation of harmonic functions on the sets of an exhaustion
(Runge approximation) into global solvability of Poisson's equation on `Ω`, and from there into
surjectivity of the top-degree Dolbeault operator. Local solutions near compact sets are provided
by `TauCeti.exists_contDiff_laplacian_eventuallyEq_nhdsSet`, and compact exhaustions by sets with
no relatively compact holes, the setting of harmonic Runge approximation, which would supply the
`Hₙ`, by `IsOpen.exists_isFilledIn_compact_exhaustion`.

Only uniform approximation on each `K n` is needed. On `interior (K N)` the tail
`∑_{n ≥ N} (uₙ₊₁ - uₙ - Hₙ)` is a uniform limit of harmonic functions, hence harmonic
(`TauCeti.harmonicOnNhd_of_tendstoLocallyUniformlyOn`) and real analytic
(`InnerProductSpace.HarmonicAt.analyticAt`), so near each point `v` is `u_N` plus a harmonic
function.

## Main declarations

* `TauCeti.contDiffOn_add_tsum_sub_sub_of_harmonicOnNhd`: `v` is of class `C^k` on `Ω`.
* `TauCeti.laplacian_add_tsum_sub_sub_eq_of_harmonicOnNhd`: `Δv = f` on `Ω`.

## References

* B. Malgrange, *Existence et approximation des solutions des équations aux dérivées partielles
  et des équations de convolution*, Ann. Inst. Fourier 6 (1955–1956), 271–355.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Section 1.4
  (the same telescoping argument for the inhomogeneous Cauchy–Riemann equation on plane
  domains).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Set Topology

variable {E F : Type*} [NormedAddCommGroup F] {Ω : Set E} {K : ℕ → Set E} {u H : ℕ → E → F}
  {f : E → F} {ε : ℕ → ℝ} {k : WithTop ℕ∞}

/-- At a point of `K N`, the corrected differences of index at least `N` are bounded by the
errors. -/
private theorem norm_sub_sub_le (hK : Monotone K)
    (hHu : ∀ n, ∀ x ∈ K n, ‖u (n + 1) x - u n x - H n x‖ ≤ ε n) {N : ℕ} {x : E} (hx : x ∈ K N)
    (m : ℕ) : ‖u (m + N + 1) x - u (m + N) x - H (m + N) x‖ ≤ ε (m + N) :=
  hHu _ x (hK (Nat.le_add_left N m) hx)

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]

/-- Two local solutions of `Δu = f` differ by a harmonic function, and so do their differences
corrected by a harmonic function. -/
private theorem harmonicOnNhd_sub_sub (hK : ∀ n, K n ⊆ interior (K (n + 1)))
    (hKΩ : ⋃ n, K n = Ω) (hk : 2 ≤ k) (hu : ∀ n, ∀ x ∈ K n, ContDiffAt ℝ k (u n) x)
    (huf : ∀ n, Δ (u n) =ᶠ[𝓝ˢ (K n)] f) (hH : ∀ n, HarmonicOnNhd (H n) Ω) (n : ℕ) :
    HarmonicOnNhd (fun x ↦ u (n + 1) x - u n x - H n x) (K n) := by
  intro x hx
  have hx₁ : x ∈ K (n + 1) := (hK n).trans interior_subset hx
  have hd : HarmonicAt (u (n + 1) - u n) x :=
    ((hu (n + 1) x hx₁).of_le hk).harmonicAt_sub_of_laplacian_eventuallyEq
      ((hu n x hx).of_le hk) <| ((huf (n + 1)).filter_mono (nhds_le_nhdsSet hx₁)).trans
        ((huf n).filter_mono (nhds_le_nhdsSet hx)).symm
  exact hd.sub (hH n x (hKΩ ▸ mem_iUnion_of_mem n hx))

variable [FiniteDimensional ℝ F]

/-- Near each point of `Ω`, the corrected telescoping series is a local solution `u_N` plus a
harmonic function. -/
private theorem exists_harmonicAt_eventuallyEq_add (hK : ∀ n, K n ⊆ interior (K (n + 1)))
    (hKΩ : ⋃ n, K n = Ω) (hk : 2 ≤ k)
    (hu : ∀ n, ∀ x ∈ K n, ContDiffAt ℝ k (u n) x) (huf : ∀ n, Δ (u n) =ᶠ[𝓝ˢ (K n)] f)
    (hH : ∀ n, HarmonicOnNhd (H n) Ω) (hε : Summable ε)
    (hHu : ∀ n, ∀ x ∈ K n, ‖u (n + 1) x - u n x - H n x‖ ≤ ε n) {x : E} (hx : x ∈ Ω) :
    ∃ N, x ∈ K N ∧ ∃ w : E → F, HarmonicAt w x ∧
      (fun y ↦ u 0 y + ∑' n, (u (n + 1) y - u n y - H n y)) =ᶠ[𝓝 x] u N + w := by
  have hmono : Monotone K := monotone_nat_of_le_succ fun n ↦ (hK n).trans interior_subset
  -- Choose `N` with `x ∈ interior (K N)`.
  obtain ⟨J, hJ⟩ := mem_iUnion.1 (hKΩ ▸ hx)
  set N := J + 1
  have hxN : x ∈ interior (K N) := hK J hJ
  have hKNΩ : K N ⊆ Ω := hKΩ ▸ subset_iUnion K N
  -- The tail of the series is a uniform limit on `K N` of harmonic functions.
  set g : ℕ → E → F := fun m y ↦ u (m + N + 1) y - u (m + N) y - H (m + N) y
  have hεN : Summable fun m ↦ ε (m + N) := (summable_nat_add_iff N).2 hε
  have htail : HarmonicOnNhd (fun y ↦ ∑' m, g m y) (interior (K N)) := by
    refine harmonicOnNhd_of_tendstoLocallyUniformlyOn isOpen_interior
      (Eventually.of_forall fun M ↦ HarmonicOnNhd.sum fun m _ ↦ ?_)
      ((tendstoUniformlyOn_tsum_nat hεN fun m y hy ↦ norm_sub_sub_le hmono hHu hy m).mono
        interior_subset).tendstoLocallyUniformlyOn
    exact (harmonicOnNhd_sub_sub hK hKΩ hk hu huf hH (m + N)).mono <| interior_subset.trans <|
      hmono (Nat.le_add_left N m)
  have hHsum : HarmonicOnNhd (fun y ↦ ∑ n ∈ Finset.range N, H n y) Ω :=
    HarmonicOnNhd.sum fun n _ ↦ hH n
  refine ⟨N, interior_subset hxN, fun y ↦ ∑' m, g m y - ∑ n ∈ Finset.range N, H n y,
    (htail x hxN).sub (hHsum x (hKNΩ (interior_subset hxN))), ?_⟩
  -- On `K N` the head of the series telescopes to `u_N - ∑_{n < N} Hₙ`.
  filter_upwards [isOpen_interior.mem_nhds hxN] with y hy
  have hyN : y ∈ K N := interior_subset hy
  have hsum : Summable fun m ↦ g m y :=
    hεN.of_norm_bounded (norm_sub_sub_le hmono hHu hyN)
  rw [Pi.add_apply, ← hsum.sum_add_tsum_nat_add', Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun n ↦ u n y)]
  abel

/-- **Regularity of the corrected telescoping series.** Let `Ω` be exhausted by sets
`K n ⊆ interior (K (n + 1))`. Let `uₙ`, with values in a finite-dimensional real normed space,
be of class `C^k`, `k ≥ 2`, at every point of `K n`, with `Δuₙ = f` near `K n`, and let `Hₙ` be
harmonic on `Ω` with `‖uₙ₊₁ - uₙ - Hₙ‖ ≤ εₙ` on `K n`, where `ε` is summable.
Then `v = u₀ + ∑ₙ (uₙ₊₁ - uₙ - Hₙ)` is of class `C^k` on `Ω`. -/
theorem contDiffOn_add_tsum_sub_sub_of_harmonicOnNhd
    (hK : ∀ n, K n ⊆ interior (K (n + 1))) (hKΩ : ⋃ n, K n = Ω) (hk : 2 ≤ k)
    (hu : ∀ n, ∀ x ∈ K n, ContDiffAt ℝ k (u n) x)
    (huf : ∀ n, Δ (u n) =ᶠ[𝓝ˢ (K n)] f) (hH : ∀ n, HarmonicOnNhd (H n) Ω) (hε : Summable ε)
    (hHu : ∀ n, ∀ x ∈ K n, ‖u (n + 1) x - u n x - H n x‖ ≤ ε n) :
    ContDiffOn ℝ k (fun x ↦ u 0 x + ∑' n, (u (n + 1) x - u n x - H n x)) Ω := by
  intro x hx
  obtain ⟨N, hxN, w, hw, hv⟩ := exists_harmonicAt_eventuallyEq_add hK hKΩ hk hu huf hH hε hHu hx
  exact (((hu N x hxN).add hw.analyticAt.contDiffAt).congr_of_eventuallyEq hv).contDiffWithinAt

/-- **Poisson's equation along an exhaustion.** Let `Ω` be exhausted by sets
`K n ⊆ interior (K (n + 1))`. Let `uₙ`, with values in a finite-dimensional real normed space,
be of class `C^k`, `k ≥ 2`, at every point of `K n`, with `Δuₙ = f` near `K n`, and let `Hₙ` be
harmonic on `Ω` with `‖uₙ₊₁ - uₙ - Hₙ‖ ≤ εₙ` on `K n`, where `ε` is summable.
Then `v = u₀ + ∑ₙ (uₙ₊₁ - uₙ - Hₙ)` solves `Δv = f` on all of `Ω`. -/
theorem laplacian_add_tsum_sub_sub_eq_of_harmonicOnNhd
    (hK : ∀ n, K n ⊆ interior (K (n + 1))) (hKΩ : ⋃ n, K n = Ω) (hk : 2 ≤ k)
    (hu : ∀ n, ∀ x ∈ K n, ContDiffAt ℝ k (u n) x)
    (huf : ∀ n, Δ (u n) =ᶠ[𝓝ˢ (K n)] f) (hH : ∀ n, HarmonicOnNhd (H n) Ω) (hε : Summable ε)
    (hHu : ∀ n, ∀ x ∈ K n, ‖u (n + 1) x - u n x - H n x‖ ≤ ε n) {x : E} (hx : x ∈ Ω) :
    Δ (fun x ↦ u 0 x + ∑' n, (u (n + 1) x - u n x - H n x)) x = f x := by
  obtain ⟨N, hxN, w, hw, hv⟩ :=
    exists_harmonicAt_eventuallyEq_add hK hKΩ hk hu huf hH hε hHu hx
  rw [(laplacian_congr_nhds hv).eq_of_nhds,
    ((hu N x hxN).of_le hk).laplacian_add hw.1, hw.2.eq_of_nhds,
    Pi.zero_apply, add_zero, (huf N).self_of_nhdsSet hxN]

end TauCeti
