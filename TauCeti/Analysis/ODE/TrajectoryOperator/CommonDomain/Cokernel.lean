/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SemiFredholm
public import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.InnerProductSpace.Lions
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The cokernel of the trajectory operator over a compactly embedded domain

Let `ι : D →L[ℝ] H` map a Banach space `D` into a Hilbert space `H`, and let `A` be an
essentially bounded family of operators `D →L[ℝ] H`, given as a class `AL` in
`L∞(ℝ, D →L[ℝ] H)`, `ι`-symmetric for almost every `s`: `⟪A(s) x, ι y⟫ = ⟪ι x, A(s) y⟫`. When `ι`
is the inclusion of a dense domain, this says that `A(s)` is a symmetric operator on `H` with
domain `D`. The operator `D_A u = (ι ∘ u)' + A(s) u(s)` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to
`L²(ℝ, H)` is `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι AL`. This file identifies its
cokernel with the kernel of its formal adjoint, and deduces that `D_A` is Fredholm when `ι` is
compact and the limits of `A` at `±∞` are invertible.

**The formal adjoint.** Integrating by parts
(`TauCeti.WeakDerivStep.inner_weakFDeriv_apply_one_compLpL_eq_neg_inner`),
`⟪D_A u, ι ∘ w⟫ = -⟪ι ∘ u, D_{-A} w⟫` for all `u` and `w` in the graph space
(`TauCeti.WeakDerivStep.inner_familyDomainTrajectoryOperator_compLpL_prev`): the formal adjoint of
`d/ds + A` is `-d/ds + A = -D_{-A}`. So `ι ∘ z` is orthogonal to the range of `D_A` for every `z`
in the kernel of `D_{-A}`.

**Regularity of the cokernel.** Conversely, suppose that `A(s)` differs from an invertible
`ι`-symmetric operator `B` by an operator bounded through `ι`: `‖(A(s) - B) x‖ ≤ c ‖ι x‖` for
almost every `s`. For the linearized Floer operator `A(s) = J₀ ∂ₜ + S(s, t)` on `D = H¹` and
`H = L²` with `B = J₀ ∂ₜ + S₊(t)`, this is the bound of the multiplication operators
`S(s, ·) - S₊` on `L²`. A priori an `η ∈ L²(ℝ, H)` orthogonal to the range of `D_A` is only square
integrable with values in `H`; it is in fact a path `ι ∘ w` for some `w` in the graph space
(`exists_compLpL_prev_eq_of_mem_orthogonal_range_familyDomainTrajectoryOperator` in the namespace
`TauCeti.WeakDerivStep`).
The pairing `u ↦ ⟪η, (D_A - D_B) u⟫` is bounded by `c ‖η‖ ‖ι ∘ u‖`, so by Lions' representation
theorem (`LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`) it is `u ↦ ⟪ι ∘ u, g⟫` for
some `g ∈ L²(ℝ, H)`. The autonomous operator `D_{-B}` is invertible
(`TauCeti.WeakDerivStep.bijective_domainTrajectoryOperator`); for the solution `w` of
`D_{-B} w = g`, the integration by parts gives `⟪D_B u, η - ι ∘ w⟫ = 0` for every `u`, and since
`D_B` is onto, `η = ι ∘ w`.

Then `h = D_{-A} w` is orthogonal to every path `ι ∘ u`, and it is removed by a correction in
`ker ι`: the path `z = B⁻¹ ∘ h` satisfies `⟪B ∘ u, ι ∘ z⟫ = ⟪ι ∘ u, h⟫ = 0` for every `u`, and
the paths `B ∘ u` are dense in `L²(ℝ, H)` since `B` is onto
(`TauCeti.WeakDerivStep.eq_zero_of_forall_inner_compLpL_prev_eq_zero`), so `ι ∘ z = 0`. Hence `z`
lies in the graph space, `A z = B z = h` because `A - B` is bounded through `ι`, and
`w + z` solves `D_{-A} (w + z) = h - A z = 0` with `ι ∘ (w + z) = η`. So the orthogonal complement
of the range of `D_A` is exactly the image of the kernel of `D_{-A}` under `z ↦ ι ∘ z`
(`TauCeti.WeakDerivStep.orthogonal_range_familyDomainTrajectoryOperator_eq_map_ker`). No density
of the range of `ι` is needed.

**Fredholmness.** Now let `ι` be compact, let `A(s)` converge to invertible operators `B₋` and
`B₊` as `s → -∞` and `s → ∞`, and take `B = B₊`. The semi-Fredholm estimate
(`TauCeti.WeakDerivStep.finiteDimensional_ker_familyDomainTrajectoryOperator`,
`TauCeti.WeakDerivStep.isClosed_range_familyDomainTrajectoryOperator`) gives `D_A` and `D_{-A}`,
whose coefficient has the limits `-B₋` and `-B₊`, finite-dimensional kernels and closed ranges.
Since the cokernel of `D_A` is the image of the kernel of `D_{-A}`, it is finite dimensional, and
`D_A` is Fredholm (`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`). On the
kernel of `D_{-A}` the map `z ↦ ι ∘ z` is injective, since `ι ∘ z = 0` forces `B₊ z = A z = 0`, so
the index of `D_A` is `dim ker D_A - dim ker D_{-A}`
(`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator`).

This is the infinite-dimensional counterpart of
`TauCeti.WeakDerivStep.orthogonal_range_trajectoryOperator_eq_map_ker` and
`TauCeti.WeakDerivStep.index_trajectoryOperator_of_isClosed_range`, for paths in a
finite-dimensional space, where the regularity of the cokernel is automatic.

## Main results

* `TauCeti.WeakDerivStep.inner_familyDomainTrajectoryOperator_compLpL_prev`: the formal adjoint of
  `D_A` is `-D_{-A}`.
* `TauCeti.WeakDerivStep.inner_domainTrajectoryOperator_compLpL_prev`: the same for the
  autonomous operator `D_B` of a constant `B`.
* `exists_compLpL_prev_eq_of_mem_orthogonal_range_familyDomainTrajectoryOperator` (in the namespace
  `TauCeti.WeakDerivStep`): the paths orthogonal to the range of `D_A` lie in the graph space.
* `TauCeti.WeakDerivStep.orthogonal_range_familyDomainTrajectoryOperator_eq_map_ker`: the
  orthogonal complement of the range of `D_A` is the image of the kernel of `D_{-A}`.
* `TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`: for compact `ι` and
  invertible limits, `D_A` is Fredholm.
* `TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator`: its index is
  `dim ker D_A - dim ker D_{-A}`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3 (the operator `d/ds + A(s)` over a compactly embedded domain is
  Fredholm, its cokernel being the kernel of the formal adjoint).
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology Distributions

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : D →L[ℝ] H}

/-! ### The formal adjoint -/

omit [CompleteSpace D] [CompleteSpace H] in
/-- If `A - B` is bounded through `ι`, then `A` and `B` agree on the kernel of `ι`. -/
private theorem apply_eq_of_map_eq_zero {A B : D →L[ℝ] H} {c : ℝ}
    (h : ∀ x, ‖(A - B) x‖ ≤ c * ‖ι x‖) {x : D} (hx : ι x = 0) : A x = B x := by
  simpa [hx, sub_eq_zero] using h x

/-- **The formal adjoint of the trajectory operator.** For an almost everywhere `ι`-symmetric
coefficient `A`, `⟪D_A u, ι ∘ w⟫ = -⟪ι ∘ u, D_{-A} w⟫` in `L²(ℝ, H)`, where
`D_A u = (ι ∘ u)' + A u`: the formal adjoint of `d/ds + A` is `-d/ds + A = -D_{-A}`. -/
theorem inner_familyDomainTrajectoryOperator_compLpL_prev {AL : Lp (D →L[ℝ] H) ∞ μ₀}
    (hSymm : ∀ᵐ s ∂μ₀, ∀ x y : D, ⟪AL s x, ι y⟫_ℝ = ⟪ι x, AL s y⟫_ℝ)
    (u w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ⟪familyDomainTrajectoryOperator ι AL u, ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) w)⟫_ℝ =
      -⟪ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u),
        familyDomainTrajectoryOperator ι (-AL) w⟫_ℝ := by
  rw [familyDomainTrajectoryOperator_apply, familyDomainTrajectoryOperator_apply, map_neg,
    neg_apply, inner_add_left, inner_add_right, inner_neg_right,
    Lp.inner_operatorMultiplication_compLpL hSymm, inner_weakFDeriv_apply_one_compLpL_eq_neg_inner]
  ring

/-- **The formal adjoint of the autonomous trajectory operator.** For a constant `ι`-symmetric
`B`, `⟪D_B u, ι ∘ w⟫ = -⟪ι ∘ u, D_{-B} w⟫` in `L²(ℝ, H)`, where `D_B u = (ι ∘ u)' + B u`: the
formal adjoint of `d/ds + B` is `-D_{-B}`. -/
theorem inner_domainTrajectoryOperator_compLpL_prev {B : D →L[ℝ] H}
    (hSymmB : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (u w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
    ⟪domainTrajectoryOperator ι B u, ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) w)⟫_ℝ =
      -⟪ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u), domainTrajectoryOperator ι (-B) w⟫_ℝ := by
  have hB := (memLp_top_const (μ := μ₀) B).coeFn_toLp
  have hnegB : -(memLp_top_const (μ := μ₀) B).toLp _ =ᵐ[μ₀] fun _ ↦ -B := by
    filter_upwards [Lp.coeFn_neg ((memLp_top_const (μ := μ₀) B).toLp _), hB] with s hn hs
    rw [hn, Pi.neg_apply, hs]
  rw [← familyDomainTrajectoryOperator_toLp_const, ← familyDomainTrajectoryOperator_of_ae_eq_const
    ι hnegB]
  exact inner_familyDomainTrajectoryOperator_compLpL_prev (hB.mono fun s hs ↦ hs ▸ hSymmB) u w

/-! ### The cokernel -/

/-- **The kernel of the formal adjoint is orthogonal to the range.** For an almost everywhere
`ι`-symmetric coefficient `A`, the path `ι ∘ z` is orthogonal to the range of
`D_A u = (ι ∘ u)' + A u` for every solution `z` of `D_{-A} z = 0`. -/
theorem map_ker_le_orthogonal_range_familyDomainTrajectoryOperator
    {AL : Lp (D →L[ℝ] H) ∞ μ₀}
    (hSymm : ∀ᵐ s ∂μ₀, ∀ x y : D, ⟪AL s x, ι y⟫_ℝ = ⟪ι x, AL s y⟫_ℝ) :
    (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker.map
        ((ι.compLpL 2 μ₀).comp (prevL (ι.compLpL 2 μ₀)) : _ →ₗ[ℝ] _) ≤
      (familyDomainTrajectoryOperator (p := 2) ι AL).rangeᗮ := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨u, rfl⟩
  have hz' : familyDomainTrajectoryOperator ι (-AL) z = 0 := LinearMap.mem_ker.1 hz
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, prevL_apply]
  rw [inner_familyDomainTrajectoryOperator_compLpL_prev hSymm, hz', inner_zero_right, neg_zero]

/-- **Regularity of the cokernel.** Let the coefficient `A` differ from an invertible `ι`-symmetric
`B` by an operator bounded through `ι`: `‖(A(s) - B) x‖ ≤ c ‖ι x‖` for almost every `s`. Then every
`η ∈ L²(ℝ, H)` orthogonal to the range of `D_A u = (ι ∘ u)' + A u` is a path `ι ∘ w` for some `w`
in the graph space `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)`. -/
theorem exists_compLpL_prev_eq_of_mem_orthogonal_range_familyDomainTrajectoryOperator
    {B : D →L[ℝ] H} (hSymmB : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (hB : B.IsInvertible)
    {AL : Lp (D →L[ℝ] H) ∞ μ₀} {c : ℝ} (hc : ∀ᵐ s ∂μ₀, ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖)
    {η : Lp H 2 μ₀} (hη : η ∈ (familyDomainTrajectoryOperator (p := 2) ι AL).rangeᗮ) :
    ∃ w : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀), ι.compLpL 2 μ₀ (prev _ w) = η := by
  set base := ι.compLpL 2 μ₀
  set J : WeakDerivStep volume ⊤ 2 base →L[ℝ] Lp H 2 μ₀ := base.comp (prevL base)
  have hJ (u : WeakDerivStep volume ⊤ 2 base) : J u = base (prev base u) := by
    simp [J, prevL_apply]
  have hη' (u : WeakDerivStep volume ⊤ 2 base) :
      ⟪familyDomainTrajectoryOperator ι AL u, η⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).1 hη _ ⟨u, rfl⟩
  -- The difference `K = D_A - D_B` is bounded by `c` times `‖ι ∘ u‖`.
  set K := familyDomainTrajectoryOperator (p := 2) ι AL - domainTrajectoryOperator ι B
  have hK (u : WeakDerivStep volume ⊤ 2 base) : ‖K u‖ ≤ max c 0 * ‖J u‖ := by
    rw [hJ]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_ae ι AL B u, hc,
      ι.coeFn_compLpL (prev base u)] with s hs hcs hι
    rw [sub_apply, hs, hι]
    exact (hcs _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- So the pairing `u ↦ ⟪η, K u⟫` factors through `J`: it is `u ↦ ⟪ι ∘ u, g⟫` for some `g`, by
  -- Lions' representation theorem for the coercive form `⟪ι ∘ u, ·⟫`.
  obtain ⟨g, hg, -⟩ := LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive
    ((innerSL ℝ).comp J).toLinearMap J (fun u ↦ ‖J u‖) ((innerSL ℝ η).comp K).toLinearMap one_pos
    (by positivity : 0 ≤ ‖η‖ * max c 0) (fun u ↦ by simp) (fun _ ↦ le_rfl) fun u ↦ by
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      rw [mul_assoc]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hK u) (norm_nonneg _))
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    at hg
  -- Solve the adjoint autonomous equation `D_{-B} w = g`.
  obtain ⟨w, hw⟩ := (bijective_domainTrajectoryOperator (inner_neg_apply_eq_inner hSymmB)
    (ContinuousLinearMap.isInvertible_neg_iff.2 hB)).2 g
  -- Then `⟪D_B u, η - ι ∘ w⟫ = 0` for every `u`, and `D_B` is onto, so `η = ι ∘ w`.
  refine ⟨w, (sub_eq_zero.1 (inner_self_eq_zero (𝕜 := ℝ) |>.1 ?_)).symm⟩
  obtain ⟨u, hu⟩ := (bijective_domainTrajectoryOperator hSymmB hB).2 (η - J w)
  have hDB : domainTrajectoryOperator ι B u = familyDomainTrajectoryOperator ι AL u - K u := by
    simp [K]
  have e₁ : ⟪domainTrajectoryOperator ι B u, J w⟫_ℝ = -⟪J u, g⟫_ℝ := by
    rw [hJ w, inner_domainTrajectoryOperator_compLpL_prev hSymmB, hw, ← hJ]
  have e₂ : ⟪domainTrajectoryOperator ι B u, η⟫_ℝ = -⟪η, K u⟫_ℝ := by
    rw [hDB, inner_sub_left, hη', real_inner_comm η, zero_sub]
  rw [← hJ]
  nth_rw 1 [← hu]
  rw [inner_sub_right, e₁, e₂, hg, neg_sub_neg, sub_self]

/-- **Paths orthogonal to the range lie in the image of the kernel of the formal adjoint.** Let
the coefficient `A` be almost everywhere `ι`-symmetric, and let it differ from an invertible
`ι`-symmetric `B` by an operator bounded through `ι`: `‖(A(s) - B) x‖ ≤ c ‖ι x‖` for almost every
`s`. Then every `η ∈ L²(ℝ, H)` orthogonal to the range of `D_A u = (ι ∘ u)' + A u` is `ι ∘ z` for a
solution `z ∈ L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` of `D_{-A} z = 0`. -/
theorem orthogonal_range_familyDomainTrajectoryOperator_le_map_ker
    {B : D →L[ℝ] H} (hSymmB : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (hB : B.IsInvertible)
    {AL : Lp (D →L[ℝ] H) ∞ μ₀}
    (hSymm : ∀ᵐ s ∂μ₀, ∀ x y : D, ⟪AL s x, ι y⟫_ℝ = ⟪ι x, AL s y⟫_ℝ) {c : ℝ}
    (hc : ∀ᵐ s ∂μ₀, ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).rangeᗮ ≤
      (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker.map
        ((ι.compLpL 2 μ₀).comp (prevL (ι.compLpL 2 μ₀)) : _ →ₗ[ℝ] _) := by
  intro η hη
  obtain ⟨w, rfl⟩ :=
    exists_compLpL_prev_eq_of_mem_orthogonal_range_familyDomainTrajectoryOperator hSymmB hB hc hη
  set h := familyDomainTrajectoryOperator ι (-AL) w
  -- `⟪ι ∘ u, D_{-A} w⟫ = -⟪D_A u, ι ∘ w⟫ = 0` for every `u`.
  have hh (u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)) :
      ⟪ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) u), h⟫_ℝ = 0 := by
    rw [← neg_eq_zero, ← inner_familyDomainTrajectoryOperator_compLpL_prev hSymm]
    exact (Submodule.mem_orthogonal _ _).1 hη _ ⟨u, rfl⟩
  -- The path `z = B⁻¹ ∘ D_{-A} w` has `ι ∘ z = 0`, since `⟪B ∘ u, ι ∘ z⟫ = ⟪ι ∘ u, B ∘ z⟫ = 0` for
  -- every `u` and the paths `B ∘ u` are dense.
  obtain ⟨e, rfl⟩ := hB
  set z := (e.symm : H →L[ℝ] D).compLpL 2 μ₀ h
  have hBz : (e : D →L[ℝ] H).compLpL 2 μ₀ z = h := by
    rw [ContinuousLinearMap.compLpL_compLpL]; simp
  have hιz : ι.compLpL 2 μ₀ z = 0 :=
    eq_zero_of_forall_inner_compLpL_prev_eq_zero (ι := ι) e.surjective.denseRange fun u ↦ by
      rw [Lp.inner_compLpL_compLpL hSymmB, hBz, hh u]
  -- So `A z = B z + (A - B) z = D_{-A} w`, the difference `(A - B) z` being bounded by
  -- `c ‖ι ∘ z‖ = 0`, and `z` lies in the graph space with `D_{-A} z = -A z = -D_{-A} w`.
  have hAz : (0 : ℝ → H) =ᵐ[μ₀] fun s ↦ (-h) s - (-AL) s (z s) := by
    filter_upwards [hc, ι.coeFn_compLpL z, Lp.coeFn_zero H 2 μ₀,
      (e : D →L[ℝ] H).coeFn_compLpL z, Lp.coeFn_neg h, Lp.coeFn_neg AL] with s hcs hιs h0 hBs
      hneg hnegA
    have hAs : AL s (z s) = h s := by
      rw [apply_eq_of_map_eq_zero hcs (by rw [← hιs, hιz, h0, Pi.zero_apply]), ← hBz, hBs]
    rw [hneg, hnegA]
    simp [hAs]
  have hz : HasWeakLineDerivOn volume ⊤ (ι.compLpL 2 μ₀ z) (fun s ↦ (-h) s - (-AL) s (z s)) 1 :=
    (hasWeakLineDerivOn_zero.congr_ae (by rw [hιz]; exact (Lp.coeFn_zero H 2 μ₀).symm))
      |>.congr_ae_deriv hAz
  obtain ⟨z', hz'z, hz'⟩ :=
    exists_prev_eq_and_familyDomainTrajectoryOperator_eq_of_hasWeakLineDerivOn ι (-AL) hz
  -- Then `w + z'` solves `D_{-A} (w + z') = 0` and has the same path `ι ∘ (w + z') = ι ∘ w`.
  have hwz : familyDomainTrajectoryOperator ι (-AL) (w + z') = 0 := by
    rw [map_add, hz', add_neg_cancel]
  refine ⟨w + z', hwz, ?_⟩
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, prevL_apply, map_add,
    hz'z, hιz, add_zero]

/-- **The orthogonal complement of the range is the image of the kernel of the formal adjoint.**
Let the coefficient `A` be almost everywhere `ι`-symmetric, and let it differ from an invertible
`ι`-symmetric `B` by an operator bounded through `ι`: `‖(A(s) - B) x‖ ≤ c ‖ι x‖` for almost every
`s`. Then the orthogonal complement of the range of `D_A u = (ι ∘ u)' + A u` in `L²(ℝ, H)` consists
exactly of the paths `ι ∘ z` for the solutions
`z ∈ L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` of `D_{-A} z = 0`. -/
theorem orthogonal_range_familyDomainTrajectoryOperator_eq_map_ker
    {B : D →L[ℝ] H} (hSymmB : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (hB : B.IsInvertible)
    {AL : Lp (D →L[ℝ] H) ∞ μ₀}
    (hSymm : ∀ᵐ s ∂μ₀, ∀ x y : D, ⟪AL s x, ι y⟫_ℝ = ⟪ι x, AL s y⟫_ℝ) {c : ℝ}
    (hc : ∀ᵐ s ∂μ₀, ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).rangeᗮ =
      (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker.map
        ((ι.compLpL 2 μ₀).comp (prevL (ι.compLpL 2 μ₀)) : _ →ₗ[ℝ] _) :=
  (orthogonal_range_familyDomainTrajectoryOperator_le_map_ker hSymmB hB hSymm hc).antisymm
    (map_ker_le_orthogonal_range_familyDomainTrajectoryOperator hSymm)

omit [CompleteSpace D] in
/-- On the kernel of the formal adjoint `D_{-A}`, the path `ι ∘ z` determines `z`, when `A`
differs from an injective `B` by an operator bounded through `ι`: if `ι ∘ z = 0`, then
`(ι ∘ z)' = 0`, so `A z = 0`, and `B z = A z = 0`. -/
private theorem injective_compLpL_prev_comp_subtype_ker {B : D →L[ℝ] H}
    (hB : Function.Injective B) {AL : Lp (D →L[ℝ] H) ∞ μ₀} {c : ℝ}
    (hc : ∀ᵐ s ∂μ₀, ∀ x, ‖(AL s - B) x‖ ≤ c * ‖ι x‖) :
    Function.Injective (((ι.compLpL 2 μ₀).comp (prevL (ι.compLpL 2 μ₀))).toLinearMap.comp
      (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker.subtype) := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨z, hz⟩ hιz ↦ ?_
  have hιz' : ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) z) = 0 := by simpa [prevL_apply] using hιz
  have hz' : familyDomainTrajectoryOperator ι (-AL) z = 0 := LinearMap.mem_ker.1 hz
  rw [familyDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn, hιz'] at hz'
  -- The weak derivative of `ι ∘ z = 0` vanishes, so `A z = 0`.
  have hAz := hz'.ae_eq (hasWeakLineDerivOn_zero.congr_ae (Lp.coeFn_zero H 2 μ₀).symm)
  have hιz0 : ⇑(ι.compLpL 2 μ₀ (prev (ι.compLpL 2 μ₀) z)) =ᵐ[μ₀] 0 := by
    rw [hιz']; exact Lp.coeFn_zero H 2 μ₀
  refine Subtype.ext (ext ?_)
  rw [ZeroMemClass.coe_zero, prev_zero]
  refine Lp.ext ?_
  filter_upwards [hAz, hc, ι.coeFn_compLpL (prev (ι.compLpL 2 μ₀) z), hιz0,
    Lp.coeFn_zero H 2 μ₀, Lp.coeFn_zero D 2 μ₀, Lp.coeFn_neg AL] with s hs hcs hιs h0 h0H hd0 hnegA
  have hAs : AL s (prev (ι.compLpL 2 μ₀) z s) = 0 := by
    rw [h0H, hnegA] at hs
    simpa using hs
  rw [hd0, Pi.zero_apply]
  exact hB (by
    rw [← apply_eq_of_map_eq_zero hcs (by rw [← hιs, h0, Pi.zero_apply]), hAs, map_zero])

/-! ### Fredholmness -/

section Fredholm

variable {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} {Bbot Btop : D →L[ℝ] H}

omit [CompleteSpace D] [CompleteSpace H] in
/-- The limits `B₋` and `B₊` at `-∞` and `∞` of an almost everywhere `ι`-symmetric family are
`ι`-symmetric. -/
private theorem inner_apply_eq_inner_of_tendsto_atBot_atTop
    (hSymm : ∀ᵐ s ∂volume, ∀ x y : D, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop)) :
    (∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ) ∧
      ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ := by
  -- A property of almost every `s` holds on every half-line, which has positive measure.
  refine ⟨inner_apply_eq_inner_of_tendsto (frequently_atBot.2 fun a ↦ ?_) hbot,
    inner_apply_eq_inner_of_tendsto (frequently_atTop.2 fun a ↦ ?_) htop⟩
  · have : (ae (volume.restrict (Iic a))).NeBot := ae_restrict_neBot.2 (by simp)
    exact ((ae_restrict_mem measurableSet_Iic).and (ae_restrict_of_ae hSymm)).exists
  · have : (ae (volume.restrict (Ici a))).NeBot := ae_restrict_neBot.2 (by simp)
    exact ((ae_restrict_mem measurableSet_Ici).and (ae_restrict_of_ae hSymm)).exists

omit [CompleteSpace D] [CompleteSpace H] in
/-- A property of almost every `A s` holds for almost every `AL s`, when `AL = A` almost
everywhere. -/
private theorem ae_of_ae_eq (hAL : AL =ᵐ[μ₀] A) {P : (D →L[ℝ] H) → Prop}
    (h : ∀ᵐ s ∂volume, P (A s)) : ∀ᵐ s ∂μ₀, P (AL s) :=
  (hAL.and (ae_restrict_of_ae h)).mono fun _ hs ↦ hs.1 ▸ hs.2

/-- Under the hypotheses of `isFredholm_familyDomainTrajectoryOperator`, the range of `D_A` is
closed. -/
private theorem isClosed_range_familyDomainTrajectoryOperator_of_ae (hι : IsCompactOperator ι)
    (hSymm : ∀ᵐ s ∂volume, ∀ x y : D, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop)) {c : ℝ}
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    IsClosed ((familyDomainTrajectoryOperator (p := 2) ι AL).range : Set (Lp H 2 μ₀)) :=
  have hlim := inner_apply_eq_inner_of_tendsto_atBot_atTop hSymm hbot htop
  isClosed_range_familyDomainTrajectoryOperator hι hlim.1 hBbot hlim.2 hBtop hAL hbot htop
    fun _ ↦ ⟨c, hc.mono fun _ hs _ ↦ hs⟩

/-- The formal adjoint `D_{-A}` has a finite-dimensional kernel: the coefficient `-A` satisfies the
hypotheses of the semi-Fredholm estimate, with the limits `-B₋` and `-B₊`. -/
private theorem finiteDimensional_ker_familyDomainTrajectoryOperator_neg
    (hι : IsCompactOperator ι) (hSymmbot : ∀ x y : D, ⟪Bbot x, ι y⟫_ℝ = ⟪ι x, Bbot y⟫_ℝ)
    (hBbot : Bbot.IsInvertible) (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop)) {c : ℝ}
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    FiniteDimensional ℝ (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker := by
  refine finiteDimensional_ker_familyDomainTrajectoryOperator (A := -A) hι
    (inner_neg_apply_eq_inner hSymmbot) (ContinuousLinearMap.isInvertible_neg_iff.2 hBbot)
    (inner_neg_apply_eq_inner hSymmtop) (ContinuousLinearMap.isInvertible_neg_iff.2 hBtop)
    ((Lp.coeFn_neg AL).trans hAL.neg) hbot.neg htop.neg fun _ ↦ ⟨c, hc.mono fun s hs _ x ↦ ?_⟩
  -- `(-A s) - (-B₊) = -(A s - B₊)`.
  simpa only [Pi.neg_apply, neg_sub_neg, ← neg_sub (A s), neg_apply, norm_neg] using hs x

/-- Under the hypotheses of `isFredholm_familyDomainTrajectoryOperator`, the orthogonal
complement of the range of `D_A` is the image of the kernel of `D_{-A}`. -/
private theorem orthogonal_range_familyDomainTrajectoryOperator_eq_map_ker_of_tendsto
    (hSymm : ∀ᵐ s ∂volume, ∀ x y : D, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hSymmtop : ∀ x y : D, ⟪Btop x, ι y⟫_ℝ = ⟪ι x, Btop y⟫_ℝ)
    (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A) {c : ℝ}
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).rangeᗮ =
      (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker.map
        ((ι.compLpL 2 μ₀).comp (prevL (ι.compLpL 2 μ₀)) : _ →ₗ[ℝ] _) :=
  orthogonal_range_familyDomainTrajectoryOperator_eq_map_ker hSymmtop hBtop
    (ae_of_ae_eq hAL (P := fun T ↦ ∀ x y, ⟪T x, ι y⟫_ℝ = ⟪ι x, T y⟫_ℝ) hSymm)
    (ae_of_ae_eq hAL (P := fun T ↦ ∀ x, ‖(T - Btop) x‖ ≤ c * ‖ι x‖) hc)

/-- Under the hypotheses of `isFredholm_familyDomainTrajectoryOperator`, the cokernel of `D_A` is
linearly equivalent, through the orthogonal complement of the range, to the image of the kernel
of `D_{-A}` under `z ↦ ι ∘ z`. -/
private noncomputable def quotientRangeEquivMapKer (hι : IsCompactOperator ι)
    (hSymm : ∀ᵐ s ∂volume, ∀ x y : D, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop)) {c : ℝ}
    (hc : ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (Lp H 2 μ₀ ⧸ (familyDomainTrajectoryOperator (p := 2) ι AL).range) ≃ₗ[ℝ]
      (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker.map
        ((ι.compLpL 2 μ₀).comp (prevL (ι.compLpL 2 μ₀)) : _ →ₗ[ℝ] Lp H 2 μ₀) :=
  haveI := (isClosed_range_familyDomainTrajectoryOperator_of_ae hι hSymm hBbot hBtop hAL hbot htop
    hc).completeSpace_coe
  (familyDomainTrajectoryOperator (p := 2) ι AL).range.quotientEquivOrthogonal.toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (orthogonal_range_familyDomainTrajectoryOperator_eq_map_ker_of_tendsto
      hSymm (inner_apply_eq_inner_of_tendsto_atBot_atTop hSymm hbot htop).2 hBtop hAL hc))

/-- **The trajectory operator over a compactly embedded domain is Fredholm.** Let `ι : D →L[ℝ] H`
be a compact operator, and let `A : ℝ → (D →L[ℝ] H)` be a family of operators, `ι`-symmetric for
almost every `s`, with an `L∞` class `AL`, converging to invertible operators `B₋` and `B₊`
as `s → -∞` and `s → ∞` and differing from `B₊` by operators bounded through `ι`:
`‖(A(s) - B₊) x‖ ≤ c ‖ι x‖` for almost every `s`. Then `D_A u = (ι ∘ u)' + A u` from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is Fredholm. -/
theorem isFredholm_familyDomainTrajectoryOperator (hι : IsCompactOperator ι)
    (hSymm : ∀ᵐ s ∂volume, ∀ x y : D, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∃ c, ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).IsFredholm := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨hSymmbot, hSymmtop⟩ := inner_apply_eq_inner_of_tendsto_atBot_atTop hSymm hbot htop
  have := finiteDimensional_ker_familyDomainTrajectoryOperator_neg hι hSymmbot hBbot hSymmtop hBtop
    hAL hbot htop hc
  refine ContinuousLinearMap.IsFredholm.of_finite_ker_coker _
    (finiteDimensional_ker_familyDomainTrajectoryOperator hι hSymmbot hBbot hSymmtop hBtop hAL hbot
      htop fun _ ↦ ⟨c, hc.mono fun _ hs _ ↦ hs⟩) ?_
  -- The cokernel is the orthogonal complement of the range, the image of a finite-dimensional
  -- kernel.
  exact (quotientRangeEquivMapKer hι hSymm hBbot hBtop hAL hbot htop hc).symm.finiteDimensional

/-- **The index of the trajectory operator over a compactly embedded domain.** Under the
hypotheses of `isFredholm_familyDomainTrajectoryOperator`, the index of `D_A u = (ι ∘ u)' + A u` is
`dim ker D_A - dim ker D_{-A}`: its cokernel is the kernel of the formal adjoint `-d/ds + A`, whose
solutions are those of `D_{-A} z = 0`. -/
theorem index_familyDomainTrajectoryOperator (hι : IsCompactOperator ι)
    (hSymm : ∀ᵐ s ∂volume, ∀ x y : D, ⟪A s x, ι y⟫_ℝ = ⟪ι x, A s y⟫_ℝ)
    (hBbot : Bbot.IsInvertible) (hBtop : Btop.IsInvertible) (hAL : AL =ᵐ[μ₀] A)
    (hbot : Tendsto A atBot (𝓝 Bbot)) (htop : Tendsto A atTop (𝓝 Btop))
    (hc : ∃ c, ∀ᵐ s ∂volume, ∀ x, ‖(A s - Btop) x‖ ≤ c * ‖ι x‖) :
    (familyDomainTrajectoryOperator (p := 2) ι AL).index =
      (Module.finrank ℝ (familyDomainTrajectoryOperator (p := 2) ι AL).ker : ℤ) -
        Module.finrank ℝ (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker := by
  obtain ⟨c, hc⟩ := hc
  -- On the kernel of `D_{-A}`, the path `ι ∘ z` determines `z`.
  obtain ⟨e, rfl⟩ := id hBtop
  have hJ := injective_compLpL_prev_comp_subtype_ker e.injective
    (ae_of_ae_eq hAL (P := fun T ↦ ∀ x, ‖(T - e) x‖ ≤ c * ‖ι x‖) hc)
  have hcoker :
      Module.finrank ℝ (Lp H 2 μ₀ ⧸ (familyDomainTrajectoryOperator (p := 2) ι AL).range) =
      Module.finrank ℝ (familyDomainTrajectoryOperator (p := 2) ι (-AL)).ker :=
    ((quotientRangeEquivMapKer hι hSymm hBbot hBtop hAL hbot htop hc).trans
      ((LinearEquiv.ofEq _ _ (by rw [LinearMap.range_comp, Submodule.range_subtype])).trans
        (LinearEquiv.ofInjective _ hJ).symm)).finrank_eq
  rw [ContinuousLinearMap.index_eq_finrank_sub, hcoker]

end Fredholm

end TauCeti.WeakDerivStep
