/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Otis Chodosh
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

import TauCeti.Analysis.Calculus.ContDiff.Differentiable

/-!
# The maximum principle for the Laplace–Beltrami operator

On a boundaryless Riemannian manifold, this file proves the pointwise second-derivative test for
the Riemannian Hessian and the Laplace–Beltrami operator `Δ = div ∘ grad`, and the resulting
comparison principle for semilinear elliptic equations on a compact manifold.

At a critical point of a `C²` function the Levi-Civita correction term of the Hessian vanishes,
so the Riemannian Hessian is the ordinary second derivative of the function read in the
preferred chart. Consequently the Hessian is negative semidefinite at a local maximum and
positive semidefinite at a local minimum, and the same holds for its trace `Δ`.

On a compact boundaryless manifold, evaluating at a maximum of `u - v` gives the comparison
principle: if `h(x, ·)` is strictly increasing for every `x`, a subsolution
`h(x, u) ≤ Δ u` lies below a supersolution `Δ v ≤ h(x, v)`. In particular a semilinear equation
`Δ u = h(x, u)` with strictly increasing nonlinearity has at most one `C²` solution. This is the
uniqueness mechanism for the curvature equation of conformal metrics on closed surfaces.

The second-derivative test also applies to functions that are only lower semicontinuous,
through smooth barriers. Two `C²` functions `f ≤ g` touching at `x` satisfy `Δ f x ≤ Δ g x`.
Hence, if a lower semicontinuous `μ` has at each point where `μ < m` a `C²` upper barrier
`f ≥ μ`, touching `μ` there, with `Δ f < 0`, then `μ ≥ m` on a compact manifold: at a minimum of
`μ` the constant function touches `f` from below. The main example is the pointwise least value
`μ y` of a family of `C²` functions `q y` on a set `S`, for instance the least eigenvalue of a
field of symmetric bilinear forms, where `q y v = B y v v` and `S` is the unit sphere. Any member
`q · v` of the family attaining the least value at `y` is an upper barrier there, so the maximum
principle only needs `Δ (q · v)` at the minimizing `v`, the unit eigenvectors of the least
eigenvalue, and no differentiability of `μ`, which fails where eigenvalues cross. This is
Hamilton's maximum principle for symmetric tensors, in the form used by Taubes for the Hermitian
part of the curvature of large-parameter Seiberg–Witten solutions.

## Main results

* `TauCeti.Manifold.hessian_self_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.hessian_self_nonneg_of_isLocalMin`: the second-derivative test.
* `TauCeti.Manifold.laplaceBeltrami_nonpos_of_isLocalMax`,
  `TauCeti.Manifold.laplaceBeltrami_nonneg_of_isLocalMin`: the sign of `Δ` at local extrema.
* `TauCeti.Manifold.hessian_self_le_of_eventuallyLE_of_eq`,
  `TauCeti.Manifold.laplaceBeltrami_le_of_eventuallyLE_of_eq`: a function touching another
  from above has larger diagonal Hessian and Laplace–Beltrami operator at contact.
* `TauCeti.Manifold.laplaceBeltrami_add_mul_nonpos_of_isLocalMax`: `Δ f + k Δ g ≤ 0` at a local
  maximum of `f + k g`.
* `TauCeti.Manifold.exists_forall_ge_and_laplaceBeltrami_nonpos`,
  `TauCeti.Manifold.exists_forall_le_and_laplaceBeltrami_nonneg`: on a compact manifold a `C²`
  function attains its maximum at a point where `Δ` is nonpositive, and its minimum at a point
  where `Δ` is nonnegative.
* `TauCeti.Manifold.laplaceBeltrami_le_laplaceBeltrami_of_eventuallyLE`: touching `C²` functions
  `f ≤ g` satisfy `Δ f ≤ Δ g` at the contact point.
* `TauCeti.Manifold.le_of_forall_exists_laplaceBeltrami_neg`: the maximum principle for a
  lower semicontinuous function with smooth upper barriers of negative Laplacian.
* `TauCeti.Manifold.le_of_isLeast_of_laplaceBeltrami_neg`: the maximum principle for the least
  value of a family of `C²` functions, tested only at the minimizers.
* `TauCeti.Manifold.forall_le_apply_self_of_laplaceBeltrami_neg`: Hamilton's maximum principle
  `B ≥ -C g` for a field of bilinear forms, tested only at the minimizing unit vectors.
* `TauCeti.Manifold.le_of_le_laplaceBeltrami_of_laplaceBeltrami_le`: the comparison principle.
* `TauCeti.Manifold.le_max_div_zero_of_mul_sq_sub_mul_le_laplaceBeltrami`: the bound
  `u ≤ max (b / a) 0` for a subsolution of `a u² - b u ≤ Δu` with `a > 0`.

## References

* Otis Chodosh's formalization in `riccardobrasca/ColdingMinicozziTheory`,
  `ForTauCeti/Geometry/Manifold/Riemannian/Hessian/Contact.lean`, revision
  `d540eafdb38a37ee49e7298d601131ceaa207ced`, for the upper-contact comparisons.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001, Chapter 3 (the classical maximum principle).
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47 (comparison of sub- and supersolutions on a compact manifold).
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 4 (the maximum principle for symmetric tensors).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

/-- At a local maximum of a `C²` function on a boundaryless Riemannian manifold, the Hessian is
negative semidefinite. -/
theorem hessian_self_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmax : IsLocalMax f x) (v : TangentSpace I x) : hessian I f x v v ≤ 0 := by
  have hmax' : IsLocalMax (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hm : IsLocalMax f ((extChartAt I x).symm (extChartAt I x x)) := by simpa using hmax
    exact hm.comp_continuous (continuousAt_extChartAt_symm x)
  rw [hessian_eq_criticalHessian hf (mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I))),
    criticalHessian_def]
  exact fderiv_fderiv_self_nonpos_of_isLocalMax
    (hf.contDiffAt_comp_extChartAt_symm.eventually_differentiableAt (by norm_num)) hmax' v

/-- At a local maximum of a `C²` function on a boundaryless Riemannian manifold, the
Laplace–Beltrami operator `Δ = div ∘ grad` is nonpositive. -/
theorem laplaceBeltrami_nonpos_of_isLocalMax (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmax : IsLocalMax f x) : laplaceBeltrami I f x ≤ 0 := by
  rw [laplaceBeltrami_eq_sum_hessian I f x (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact Finset.sum_nonpos fun i _ ↦ hessian_self_nonpos_of_isLocalMax hf hmax _

/-- At a local maximum of `f + k g`, with `f` and `g` both `C²`, on a boundaryless Riemannian
manifold, `Δ f + k Δ g ≤ 0`. -/
theorem laplaceBeltrami_add_mul_nonpos_of_isLocalMax {g : M → ℝ} {k : ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x)
    (hmax : IsLocalMax (fun y ↦ f y + k * g y) x) :
    laplaceBeltrami I f x + k * laplaceBeltrami I g x ≤ 0 := by
  have hkg : ContMDiffAt I 𝓘(ℝ) 2 (k • g) x := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using contMDiffAt_const.mul hg
  -- The pointwise function `y ↦ f y + k * g y` is `f + k • g`.
  have hfg : (fun y ↦ f y + k * g y) = f + k • g := rfl
  have hΔ := laplaceBeltrami_nonpos_of_isLocalMax (hf.add hkg) (hfg ▸ hmax)
  rwa [laplaceBeltrami_add_of_contMDiffAt I hf hkg,
    laplaceBeltrami_smul_of_contMDiffAt I k hg] at hΔ

/-- At a local minimum of a `C²` function on a boundaryless Riemannian manifold, the Hessian is
positive semidefinite. -/
theorem hessian_self_nonneg_of_isLocalMin (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmin : IsLocalMin f x) (v : TangentSpace I x) : 0 ≤ hessian I f x v v := by
  have hmin' : IsLocalMin (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    have hm : IsLocalMin f ((extChartAt I x).symm (extChartAt I x x)) := by simpa using hmin
    exact hm.comp_continuous (continuousAt_extChartAt_symm x)
  rw [hessian_eq_criticalHessian hf (mem_criticalPoints.1 (hmin.mem_criticalPoints (I := I))),
    criticalHessian_def]
  exact fderiv_fderiv_self_nonneg_of_isLocalMin
    (hf.contDiffAt_comp_extChartAt_symm.eventually_differentiableAt (by norm_num)) hmin' v

/-- At a local minimum of a `C²` function on a boundaryless Riemannian manifold, the
Laplace–Beltrami operator `Δ = div ∘ grad` is nonnegative. -/
theorem laplaceBeltrami_nonneg_of_isLocalMin (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hmin : IsLocalMin f x) : 0 ≤ laplaceBeltrami I f x := by
  rw [laplaceBeltrami_eq_sum_hessian I f x (stdOrthonormalBasis ℝ (TangentSpace I x))]
  exact Finset.sum_nonneg fun i _ ↦ hessian_self_nonneg_of_isLocalMin hf hmin _

/-- If `g` touches `f` from above, its diagonal Hessian at the contact point is larger. -/
theorem hessian_self_le_of_eventuallyLE_of_eq {g : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hle : ∀ᶠ y in 𝓝 x, f y ≤ g y)
    (heq : f x = g x) (v : TangentSpace I x) : hessian I f x v v ≤ hessian I g x v v := by
  have hmin : IsLocalMin (g - f) x := by
    filter_upwards [hle] with y hy
    simpa only [Pi.sub_apply, ← heq, sub_self] using sub_nonneg.mpr hy
  have hh : 0 ≤ hessian I (g - f) x v v :=
    hessian_self_nonneg_of_isLocalMin (hg.sub hf) hmin v
  rw [hessian_sub_of_contMDiffAt I (f := g) (g := f) hg hf] at hh
  exact sub_nonneg.mp hh

/-- If `g` touches `f` from above, its Laplace–Beltrami operator is larger at contact. -/
theorem laplaceBeltrami_le_of_eventuallyLE_of_eq {g : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hle : ∀ᶠ y in 𝓝 x, f y ≤ g y)
    (heq : f x = g x) : laplaceBeltrami I f x ≤ laplaceBeltrami I g x := by
  have hmax : IsLocalMax (f - g) x := by
    filter_upwards [hle] with y hy
    simpa only [Pi.sub_apply, heq, sub_self] using sub_nonpos.mpr hy
  have hsub : ContMDiffAt I 𝓘(ℝ) 2 (f - g) x := hf.sub hg
  have hadd := laplaceBeltrami_add_of_contMDiffAt I hsub hg
  rw [sub_add_cancel] at hadd
  have hΔ := laplaceBeltrami_nonpos_of_isLocalMax hsub hmax
  linarith

/-- On a compact boundaryless Riemannian manifold, a `C²` function attains its maximum at a point
where its Laplace–Beltrami operator `Δ = div ∘ grad` is nonpositive. -/
theorem exists_forall_ge_and_laplaceBeltrami_nonpos [CompactSpace M] [Nonempty M]
    (hf : ContMDiff I 𝓘(ℝ) 2 f) : ∃ x₀, (∀ y, f y ≤ f x₀) ∧ laplaceBeltrami I f x₀ ≤ 0 := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuous.continuousOn
  exact ⟨x₀, fun y ↦ hx₀ (Set.mem_univ y),
    laplaceBeltrami_nonpos_of_isLocalMax hf.contMDiffAt (hx₀.isLocalMax Filter.univ_mem)⟩

/-- On a compact boundaryless Riemannian manifold, a `C²` function attains its minimum at a point
where its Laplace–Beltrami operator `Δ = div ∘ grad` is nonnegative. -/
theorem exists_forall_le_and_laplaceBeltrami_nonneg [CompactSpace M] [Nonempty M]
    (hf : ContMDiff I 𝓘(ℝ) 2 f) : ∃ x₀, (∀ y, f x₀ ≤ f y) ∧ 0 ≤ laplaceBeltrami I f x₀ := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuous.continuousOn
  exact ⟨x₀, fun y ↦ hx₀ (Set.mem_univ y),
    laplaceBeltrami_nonneg_of_isLocalMin hf.contMDiffAt (hx₀.isLocalMin Filter.univ_mem)⟩

/-- **Touching functions are ordered by their Laplacians.** If `f ≤ g` near `x` and `f x = g x`,
with `f` and `g` both `C²` at `x`, on a boundaryless Riemannian manifold, then `Δ f x ≤ Δ g x`.
Neither function needs to be `C²` away from `x`; for instance `g` may be a smooth upper barrier
for a function `μ` that is not differentiable, touching it at `x`, and `f` a test function touching
`μ` from below. -/
theorem laplaceBeltrami_le_laplaceBeltrami_of_eventuallyLE {g : M → ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hle : f ≤ᶠ[𝓝 x] g)
    (heq : f x = g x) : laplaceBeltrami I f x ≤ laplaceBeltrami I g x := by
  -- `f - g` has a local maximum, of value `0`, at `x`.
  have hΔ := laplaceBeltrami_add_mul_nonpos_of_isLocalMax (k := -1) hf hg (by
    filter_upwards [hle] with y hy
    rw [heq]
    linarith)
  linarith

/-- **The maximum principle for functions with smooth upper barriers.** On a compact boundaryless
Riemannian manifold, let `μ` be a lower semicontinuous function, not necessarily continuous or
differentiable. Suppose
that at every point `y` where `μ y < m` there is a function `f`, `C²` at `y`, with `μ ≤ f` near
`y`, `f y = μ y` and `Δ f y < 0`. Then `m ≤ μ` everywhere.

This applies to the pointwise least value `μ` of a family of smooth functions, such as the least
eigenvalue of a field of symmetric bilinear forms, which is not differentiable where eigenvalues
cross; a member of the family attaining the least value at `y` is an upper barrier
(`TauCeti.Manifold.le_of_isLeast_of_laplaceBeltrami_neg`). -/
theorem le_of_forall_exists_laplaceBeltrami_neg [CompactSpace M] {μ : M → ℝ} {m : ℝ}
    (hμ : LowerSemicontinuous μ)
    (h : ∀ y, μ y < m → ∃ f : M → ℝ, ContMDiffAt I 𝓘(ℝ) 2 f y ∧ μ ≤ᶠ[𝓝 y] f ∧ f y = μ y ∧
      laplaceBeltrami I f y < 0)
    (y : M) : m ≤ μ y := by
  obtain ⟨x₀, -, hx₀⟩ :=
    (hμ.lowerSemicontinuousOn _).exists_isMinOn ⟨y, Set.mem_univ y⟩ isCompact_univ
  refine le_trans ?_ (hx₀ (Set.mem_univ y))
  by_contra! hlt
  obtain ⟨f, hf, hle, heq, hΔ⟩ := h x₀ hlt
  -- The constant `μ x₀` touches the barrier `f` from below at the minimum `x₀` of `μ`.
  have hconst : (fun _ ↦ μ x₀) ≤ᶠ[𝓝 x₀] f := by
    filter_upwards [hle] with z hz
    exact (hx₀ (Set.mem_univ z)).trans hz
  have hΔ₀ := laplaceBeltrami_le_laplaceBeltrami_of_eventuallyLE contMDiffAt_const hf hconst
    heq.symm
  rw [laplaceBeltrami_const] at hΔ₀
  linarith

/-- **The maximum principle for a least value.** On a compact boundaryless Riemannian manifold,
let `μ y` be the least value of the function `q y` on a set `S`, for every `y`, and let `μ` be
lower semicontinuous. Suppose that at every point `y` with `μ y < m`, and for every `v ∈ S`
attaining the least value there, the function `z ↦ q z v` is `C²` at `y` with
`Δ (q · v) y < 0`. Then `m ≤ μ` everywhere.

For a field of symmetric bilinear forms `B` on a fixed inner product space, with `q y v = B y v v`
and `S` the unit sphere, `μ` is the least eigenvalue of `B` and the hypothesis concerns its unit
eigenvectors: no differentiability of `μ` across eigenvalue crossings is used. -/
theorem le_of_isLeast_of_laplaceBeltrami_neg [CompactSpace M] {ι : Type*} {q : M → ι → ℝ}
    {S : Set ι} {μ : M → ℝ} {m : ℝ} (hμ : ∀ y, IsLeast (q y '' S) (μ y))
    (hμc : LowerSemicontinuous μ)
    (hq : ∀ y, ∀ v ∈ S, q y v = μ y → μ y < m → ContMDiffAt I 𝓘(ℝ) 2 (fun z ↦ q z v) y)
    (hΔ : ∀ y, ∀ v ∈ S, q y v = μ y → μ y < m → laplaceBeltrami I (fun z ↦ q z v) y < 0)
    (y : M) : m ≤ μ y := by
  refine le_of_forall_exists_laplaceBeltrami_neg (I := I) hμc (fun x hx ↦ ?_) y
  obtain ⟨v, hv, hvx⟩ := (hμ x).1
  exact ⟨fun z ↦ q z v, hq x v hv hvx hx,
    Eventually.of_forall fun z ↦ (hμ z).2 (Set.mem_image_of_mem _ hv), hvx, hΔ x v hv hvx hx⟩

/-- **Hamilton's maximum principle for a field of bilinear forms.** On a compact boundaryless
Riemannian manifold `M`, let `B` be a field of bilinear forms on a fixed finite-dimensional normed
space `V` such that `(y, w) ↦ B y w w` is continuous and each `z ↦ B z w w` is `C²`. Suppose that
for every point `y` and every unit vector `v` minimizing `B y w w` over the unit vectors `w`, with
`B y v v < -C`, the function `z ↦ B z v v` has negative Laplace–Beltrami operator at `y`. Then
`-C ‖v‖² ≤ B y v v` for every `y` and `v`.

For symmetric bilinear forms on an inner product space this is the lower bound `B ≥ -C g` on the
least eigenvalue, from a hypothesis at its unit eigenvectors only
(`TauCeti.Manifold.le_of_isLeast_of_laplaceBeltrami_neg`). The regularity hypotheses `hc` and
`hB` hold for every `C²` field of continuous bilinear forms. -/
theorem forall_le_apply_self_of_laplaceBeltrami_neg [CompactSpace M] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {B : M → LinearMap.BilinForm ℝ V} (hc : Continuous fun p : M × V ↦ B p.1 p.2 p.2)
    (hB : ∀ w, ContMDiff I 𝓘(ℝ) 2 fun z ↦ B z w w) {C : ℝ}
    (hΔ : ∀ y, ∀ v : V, ‖v‖ = 1 → (∀ w : V, ‖w‖ = 1 → B y v v ≤ B y w w) → B y v v < -C →
      laplaceBeltrami I (fun z ↦ B z v v) y < 0)
    (y : M) : ∀ v : V, -C * ‖v‖ ^ 2 ≤ B y v v := by
  intro v
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [Subsingleton.elim v 0]
  set S := Metric.sphere (0 : V) 1
  set q : M → V → ℝ := fun y w ↦ B y w w with hq_def
  have hS : IsCompact S := isCompact_sphere 0 1
  -- The least value `μ y` of `q y` on the unit sphere.
  set μ : M → ℝ := fun y ↦ sInf (q y '' S)
  have hμ : ∀ y, IsLeast (q y '' S) (μ y) := fun y ↦
    (hS.image (hc.comp (Continuous.prodMk_right y))).isLeast_sInf
      ((NormedSpace.sphere_nonempty.2 zero_le_one).image _)
  -- A unit vector attaining `μ y` minimizes `q y` on the unit sphere.
  have hmin : ∀ y v, q y v = μ y → ∀ w : V, ‖w‖ = 1 → q y v ≤ q y w :=
    fun y v hv w hw ↦
      hv.le.trans ((hμ y).2 (Set.mem_image_of_mem _ (mem_sphere_zero_iff_norm.2 hw)))
  have hlow : -C ≤ μ y :=
    le_of_isLeast_of_laplaceBeltrami_neg (I := I) hμ (hS.continuous_sInf hc).lowerSemicontinuous
      (fun _ w _ _ _ ↦ (hB w).contMDiffAt)
      (fun x w hw hwx hlt ↦ hΔ x w (mem_sphere_zero_iff_norm.1 hw) (hmin x w hwx)
        (hwx.trans_lt hlt)) y
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  -- Scale `v` to the unit vector `u = v / ‖v‖`, at which `q y u ≥ μ y ≥ -C`.
  set u := ‖v‖⁻¹ • v
  have hu : u ∈ S := mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (𝕜 := ℝ) hv)
  have hvu : v = ‖v‖ • u := (smul_inv_smul₀ (norm_ne_zero_iff.2 hv) v).symm
  have hqu : μ y ≤ q y u := (hμ y).2 (Set.mem_image_of_mem _ hu)
  have hscale : B y v v = ‖v‖ ^ 2 * q y u := by
    conv_lhs => rw [hvu]
    simp only [hq_def, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hscale]
  nlinarith [sq_nonneg ‖v‖]

/-- **The comparison principle** for semilinear equations `Δ u = h(x, u)` on a compact
boundaryless Riemannian manifold, with `h(x, ·)` strictly increasing for every `x`: a `C²`
subsolution `h(x, u) ≤ Δ u` lies below a `C²` supersolution `Δ v ≤ h(x, v)`. -/
theorem le_of_le_laplaceBeltrami_of_laplaceBeltrami_le [CompactSpace M] {h : M → ℝ → ℝ}
    (hh : ∀ x, StrictMono (h x)) {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (hsub : ∀ x, h x (u x) ≤ laplaceBeltrami I u x)
    (hsuper : ∀ x, laplaceBeltrami I v x ≤ h x (v x)) : u ≤ v := by
  intro y
  have : Nonempty M := ⟨y⟩
  -- At a maximum `x₀` of `u - v`, the Laplacian of `u - v` is nonpositive.
  obtain ⟨x₀, hx₀, hmax⟩ := exists_forall_ge_and_laplaceBeltrami_nonpos (f := u - v) (hu.sub hv)
  rw [laplaceBeltrami_sub I hu hv] at hmax
  -- Hence `h x₀ (u x₀) ≤ h x₀ (v x₀)`, so `u x₀ ≤ v x₀` by strict monotonicity.
  have hle : u x₀ ≤ v x₀ :=
    (hh x₀).le_iff_le.1 (by linarith [hsub x₀, hsuper x₀])
  have hy : u y - v y ≤ u x₀ - v x₀ := hx₀ y
  linarith

/-- **The maximum principle bound for a quadratic subsolution.** On a compact boundaryless
Riemannian manifold, a `C²` function `u` with `a u² - b u ≤ Δu` and `a > 0` satisfies
`u ≤ max (b / a) 0`. For instance a subsolution of `-Δu / 2 + (r / 4) (u - 1) u ≤ k u` with
`r > 0` and `k ≥ 0` is at most `1 + 4 k / r`. -/
theorem le_max_div_zero_of_mul_sq_sub_mul_le_laplaceBeltrami [CompactSpace M] {u : M → ℝ}
    {a b : ℝ} (ha : 0 < a) (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (h : ∀ x, a * u x ^ 2 - b * u x ≤ laplaceBeltrami I u x) (x : M) :
    u x ≤ max (b / a) 0 := by
  have : Nonempty M := ⟨x⟩
  obtain ⟨x₀, hx₀, hΔ⟩ := exists_forall_ge_and_laplaceBeltrami_nonpos hu
  refine (hx₀ x).trans ?_
  rcases le_or_gt (u x₀) 0 with hu₀ | hu₀
  · exact hu₀.trans (le_max_right _ _)
  -- At the maximum `Δu ≤ 0`, so `(a u) u ≤ b u`, and `u > 0` there.
  have hle : u x₀ * a * u x₀ ≤ b * u x₀ := by linarith [h x₀]
  exact le_max_of_le_left ((le_div_iff₀ ha).2 (le_of_mul_le_mul_right hle hu₀))

end TauCeti.Manifold
