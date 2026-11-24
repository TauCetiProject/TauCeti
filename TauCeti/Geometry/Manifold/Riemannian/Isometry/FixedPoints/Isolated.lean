/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Invariant
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints

/-!
# Isolated fixed points have no invariant tangent vectors

Let a group `K` act on a manifold `M` by smooth isometries of a Riemannian metric, and let `p` be a
fixed point of `K`. The Riemannian logarithm at `p` flattens the fixed set `M^K` near `p` onto the
subspace `V^K` of tangent vectors at `p` fixed by the differential of every element of `K`
(`TauCeti.exists_isSliceChart_fixedPoints`). So the exponential images of the small multiples of
a vector of `V^K` are fixed points converging to `p`. If `p` is an isolated fixed point, they all
equal `p`, and the vector is zero: an isolated fixed point has no nonzero tangent vector fixed by
the differentials of all group elements (`TauCeti.eq_zero_of_forall_mfderiv_smul_eq`).

A compact Lie group acting smoothly on a σ-compact manifold preserves a smooth Riemannian metric,
so the same holds for such actions with no metric given
(`TauCeti.eq_zero_of_forall_mfderiv_smul_eq_of_compactSpace`). This is the hypothesis under which
the generic components of the moment map of a Hamiltonian torus action are Morse functions
(`TauCeti.SmoothTwoForm.IsMomentMap.dense_setOf_isMorse`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2.
-/

public section

open Bundle Filter Manifold MulAction Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {p : M}

/-- **An isolated fixed point has no invariant tangent vectors.** For a group acting by smooth
isometries and an isolated point `p` of its fixed set, the only tangent vector at `p` fixed by
the differential of every group element is zero. -/
theorem eq_zero_of_forall_mfderiv_smul_eq [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M]
    (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
      inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)
    (hp : p ∈ fixedPoints K M) (hiso : ∀ᶠ q in 𝓝 p, q ∈ fixedPoints K M → q = p)
    {v : TangentSpace I p} (hv : ∀ k : K, mfderiv I I (k • ·) p v = v) : v = 0 := by
  obtain ⟨φ, hpφ, hφp, -, hφ⟩ := exists_isSliceChart_fixedPoints hK hp
  set ψ := φ.toOpenPartialHomeomorph
  have hψp : ψ p = 0 := hφp
  have h0 : (0 : TangentSpace I p) ∈ ψ.target := hψp ▸ ψ.map_source hpφ
  -- The multiples `t • v` lie in the slice, so their images under `ψ⁻¹` are fixed points.
  have hline : Tendsto (fun t : ℝ ↦ t • v) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const v
  have htarget : ∀ᶠ t : ℝ in 𝓝 0, t • v ∈ ψ.target :=
    hline.eventually (ψ.open_target.mem_nhds h0)
  have hcurve : Tendsto (fun t : ℝ ↦ ψ.symm (t • v)) (𝓝 0) (𝓝 p) := by
    have := (ψ.continuousAt_symm h0).tendsto.comp hline
    rwa [Function.comp_def, ← hψp, ψ.left_inv hpφ] at this
  have hfix : ∀ᶠ t : ℝ in 𝓝 0, ψ.symm (t • v) = p := by
    filter_upwards [htarget, hcurve.eventually hiso] with t ht hiso'
    refine hiso' ((isSliceChart_iff.1 hφ _ (ψ.map_target ht)).2 ?_)
    rw [ψ.right_inv ht]
    exact fun k ↦ by rw [map_smul, hv k]; rfl
  -- Hence `t • v = ψ p = 0` for all small `t`, in particular for a small nonzero `t`.
  obtain ⟨t, ht, ht0⟩ := ((hfix.and htarget).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {t : ℝ | t ≠ 0} ∈ 𝓝[≠] 0) |>.exists
  have htv : t • v = 0 := by rw [← ψ.right_inv ht.2, ht.1, hψp]
  exact (smul_eq_zero.1 htv).resolve_left ht0

/-- **An isolated fixed point of a compact group action has no invariant tangent vectors.** For a
compact Lie group acting smoothly on a σ-compact manifold and an isolated point `p` of its fixed
set, the only tangent vector at `p` fixed by the differential of every group element is zero. -/
theorem eq_zero_of_forall_mfderiv_smul_eq_of_compactSpace [SigmaCompactSpace M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
    (J : ModelWithCorners ℝ E' H') {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [ChartedSpace H' G] [IsManifold J ∞ G]
    [MulAction G M] [ContMDiffSMul J I ∞ G M]
    (hp : p ∈ fixedPoints G M) (hiso : ∀ᶠ q in 𝓝 p, q ∈ fixedPoints G M → q = p)
    {v : TangentSpace I p} (hv : ∀ g : G, mfderiv I I (g • ·) p v = v) : v = 0 := by
  have : ContMDiffConstSMul I ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := J)⟩
  exact of_forall_riemannianBundle_inner_mfderiv J G fun hK ↦
    eq_zero_of_forall_mfderiv_smul_eq hK hp hiso hv

end TauCeti
