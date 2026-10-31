/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.RegularValue.Fibre

/-!
# The integral formula for the degree near a regular value

Let `f : M → N` be a `C¹` map from a compact boundaryless manifold to a Hausdorff manifold of the
same dimension, with orientations `o` of `M` and `o'` of `N`, and let `y` be a regular value of
`f`. The fibre over `y` is finite and `f` is a local diffeomorphism at each of its points. Near
`y`, the preimage of a small neighbourhood `V` of `y` is therefore a finite disjoint union of open
sheets, each carried diffeomorphically onto its image by `f`, and on each sheet `f` either
preserves or reverses orientation, according to its orientation sign at the point of the fibre.
This is the *stack of records* over `y`.

Splitting the pullback `f^*φ` of an integrable top form `φ` supported in `V` along the sheets and
changing variables on each of them gives
$$\int_M f^*\varphi = \deg_y(f) \int_N \varphi,$$
where `deg_y(f)` is the signed count `TauCeti.degreeAtRegularValue o o' f y` of the fibre
(`TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`). This is the
local computation in the proof that, between compact connected oriented manifolds, the signed
count does not depend on the regular value and computes `∫_M f^*φ / ∫_N φ` for every top form
[Lee, Thm. 17.35].

## Main results

* `TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`: every regular
  value `y` has a neighbourhood `V` such that `∫_M f^*φ = deg_y(f) · ∫_N φ` for every integrable
  top form `φ` supported in `V`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory, proof of Theorem 17.35.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §1 (the stack of records) and §5.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {k : ℕ}

open Manifold.Orientation

/-- **The stack of records.** Over a regular value `y` of a `C¹` map `f` from a compact
boundaryless manifold to a Hausdorff manifold, the points `x` of the fibre have pairwise disjoint
open neighbourhoods, the sources of open partial homeomorphisms `e x` agreeing with `f`, on which
the orientation sign of `f` is constant; and `y` has a neighbourhood whose preimage is covered by
these sheets and which lies in each of their images. -/
private theorem exists_stack_of_records [CompactSpace M] [T2Space M] [T2Space N]
    [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f) {y : N}
    (hy : IsRegularValue I J f y) (s : Finset M) (hs : ∀ x, x ∈ s ↔ f x = y) :
    ∃ e : s → OpenPartialHomeomorph M N, (∀ x, (x : M) ∈ (e x).source) ∧
      (∀ x, EqOn f (e x) (e x).source) ∧
      (∀ x, ∀ z ∈ (e x).source, orientationSign o o' f z = orientationSign o o' f x) ∧
      Pairwise (fun x x' ↦ Disjoint (e x).source (e x').source) ∧
      ∃ V ∈ 𝓝 y, (∀ x, V ⊆ (e x).target) ∧ f ⁻¹' V ⊆ ⋃ x, (e x).source := by
  obtain ⟨U, hU, hUd⟩ := (s.finite_toSet).t2_separation
  -- At each point of the fibre, `f` is a local diffeomorphism by the inverse function theorem;
  -- restrict a witnessing partial diffeomorphism to a separating neighbourhood on which the
  -- orientation sign is constant.
  have key (x : s) : ∃ e : OpenPartialHomeomorph M N, (x : M) ∈ e.source ∧ EqOn f e e.source ∧
      e.source ⊆ U x ∧ ∀ z ∈ e.source, orientationSign o o' f z = orientationSign o o' f x := by
    obtain ⟨D, hD⟩ := (isRegularPoint_iff_isInvertible_mfderiv rfl).mp
      (hy.isRegularPoint ((hs x).mp x.2))
    have hld : IsLocalDiffeomorphAt I J 1 f x := isLocalDiffeomorphAt_of_mfderiv_eq
      hf.contMDiffOn isOpen_univ (mem_univ _) BoundarylessManifold.isInteriorPoint le_rfl hD
    have hlh : IsLocalHomeomorphOn f {(x : M)} :=
      ((isLocalDiffeomorphOn_iff _).mpr fun z ↦
        (mem_singleton_iff.mp z.2) ▸ hld).isLocalHomeomorphOn
    obtain ⟨Φ, hxΦ, hfΦ⟩ := hlh x rfl
    obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp
      (inter_mem ((hU x).2.mem_nhds (hU x).1)
        (hld.eventually_orientationSign_eq (o := o) (o' := o')))
    refine ⟨Φ.restrOpen W hWo, ⟨hxΦ, hxW⟩, fun z _ ↦ congrFun hfΦ z,
      fun z hz ↦ (hWsub hz.2).1, fun z hz ↦ (hWsub hz.2).2⟩
  choose e hxe hfe hU' hsgn using key
  refine ⟨e, hxe, hfe, hsgn, fun x x' hxx' ↦ ?_, ?_⟩
  · exact (hUd x.2 x'.2 (Subtype.coe_injective.ne hxx')).mono (hU' x) (hU' x')
  -- The points outside the sheets form a compact set whose image misses `y`.
  set C := (⋃ x, (e x).source)ᶜ
  have hC : IsCompact (f '' C) :=
    ((isOpen_iUnion fun x ↦ (e x).open_source).isClosed_compl.isCompact).image hf.continuous
  refine ⟨(⋂ x, (e x).target) ∩ (f '' C)ᶜ, inter_mem
    (Filter.iInter_mem.mpr fun x ↦ (e x).open_target.mem_nhds ?_)
    (hC.isClosed.isOpen_compl.mem_nhds ?_), fun x ↦ inter_subset_left.trans (iInter_subset _ x),
    fun z hz ↦ ?_⟩
  · rw [← (hs x).mp x.2, hfe x (hxe x)]
    exact (e x).map_source (hxe x)
  · rintro ⟨z, hzC, hzy⟩
    exact hzC (mem_iUnion.mpr ⟨⟨z, (hs z).mpr hzy⟩, hxe _⟩)
  · by_contra hz'
    exact hz.2 ⟨z, hz', rfl⟩

/-- **The integral formula for the degree near a regular value.** Let `f : M → N` be a `C¹` map
from a compact boundaryless manifold to a Hausdorff manifold modelled on the same space, with
orientations `o` and `o'`, and let `y` be a regular value of `f`. Then `y` has a neighbourhood `V`
such that every integrable top form `φ` on `N` supported in `V` satisfies
`∫_M f^*φ = deg_y(f) · ∫_N φ`, where `deg_y(f)` is the signed count of the fibre over `y`. -/
theorem exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul [CompactSpace M]
    [T2Space M] [T2Space N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f) {y : N}
    (hy : IsRegularValue I J f y) :
    ∃ V ∈ 𝓝 y, ∀ φ : RoughForm J N ℝ k, IntegrableTopForm φ →
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V →
        integralTopForm o (mpullback I J f φ) =
          degreeAtRegularValue o o' f y * integralTopForm o' φ := by
  classical
  -- Split `f^*φ` into its parts on the sheets of the stack of records over `y`, change variables
  -- on each sheet according to the orientation sign there, and sum.
  set s := (hy.finite_preimage rfl hf one_ne_zero).toFinset
  have hs (x : M) : x ∈ s ↔ f x = y := by simp [s]
  obtain ⟨e, hxe, hfe, hsgn, hdisj, V, hV, hVt, hVs⟩ :=
    exists_stack_of_records o o' hf hy s hs
  refine ⟨V, hV, fun φ hφ hφV ↦ ?_⟩
  set K := _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ
  -- The part of `f^*φ` on the sheet over `x`.
  let ψ (x : s) : RoughForm I M ℝ k := fun z ↦
    (e x).source.indicator (fun _ ↦ (1 : ℝ)) z • mpullback I J f φ z
  have hψ_eq (x : s) (z : M) (hz : z ∈ (e x).source) : ψ x z = mpullback I J f φ z := by
    simp only [ψ, indicator_of_mem hz, one_smul]
  have hψ_zero (x : s) (z : M) (hz : z ∉ (e x).source) : ψ x z = 0 := by
    simp only [ψ, indicator_of_notMem hz, zero_smul]
  have hpull_zero (z : M) (hz : f z ∉ K) : mpullback I J f φ z = 0 :=
    RoughForm.mpullback_apply_eq_zero (image_eq_zero_of_notMem_tsupport hz)
  -- On each sheet the support of `ψ x` lies in the compact image of `K` under the inverse.
  have hK (x : s) : IsCompact ((e x).symm '' K) :=
    hφ.isCompact.image_of_continuousOn ((e x).continuousOn_symm.mono (hφV.trans (hVt x)))
  have hψK (x : s) : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (ψ x) ⊆ (e x).symm '' K := by
    refine closure_minimal (fun z hz ↦ ?_) (hK x).isClosed
    have hzs : z ∈ (e x).source := by_contra fun h ↦ hz (hψ_zero x z h)
    have hfz : f z ∈ K := by_contra fun h ↦ hz ((hψ_eq x z hzs).trans (hpull_zero z h))
    exact ⟨f z, hfz, by rw [hfe x hzs, (e x).left_inv hzs]⟩
  have hψs (x : s) : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (ψ x) ⊆ (e x).source :=
    (hψK x).trans (image_subset_iff.mpr fun q hq ↦ (e x).map_target (hVt x (hφV hq)))
  have hψc (x : s) : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (ψ x)) :=
    (hK x).of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) _) (hψK x)
  have hmd (x : s) : ∀ z ∈ (e x).source, MDifferentiableAt I J f z :=
    fun z _ ↦ hf.mdifferentiable one_ne_zero z
  -- The sheets decompose `f^*φ`.
  have hsum : mpullback I J f φ = ∑ x, ψ x := by
    funext z
    rw [Finset.sum_apply]
    by_cases hz : ∃ x, z ∈ (e x).source
    · obtain ⟨x, hx⟩ := hz
      rw [Finset.sum_eq_single x (fun x' _ hx' ↦ hψ_zero x' z fun h ↦
        (hdisj hx').le_bot ⟨h, hx⟩) (by simp), hψ_eq x z hx]
    · simp only [not_exists] at hz
      rw [Finset.sum_eq_zero fun x _ ↦ hψ_zero x z (hz x)]
      refine hpull_zero z fun hfz ↦ ?_
      obtain ⟨x, hx⟩ := mem_iUnion.mp (hVs (hφV hfz))
      exact hz x hx
  -- On each sheet, change variables according to the orientation sign.
  have hint (x : s) :
      integralTopForm o (ψ x) = orientationSign o o' f x * integralTopForm o' φ := by
    rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o')
      (hy.isRegularPoint ((hs x).mp x.2)) with h | h
    · rw [h, Int.cast_one, one_mul]
      exact (e x).integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt (hfe x) (hmd x)
        (fun z hz ↦ orientationSign_eq_one_iff.mp ((hsgn x z hz).trans h)) hφ
        (hφV.trans (hVt x)) (hψc x) (hψs x) (hψ_eq x)
    · rw [h, Int.cast_neg, Int.cast_one, neg_one_mul]
      exact (e x).integralTopForm_of_eq_mpullback_of_isOrientationReversingAt (hfe x) (hmd x)
        (fun z hz ↦ orientationSign_eq_neg_one_iff.mp ((hsgn x z hz).trans h)) hφ
        (hφV.trans (hVt x)) (hψc x) (hψs x) (hψ_eq x)
  rw [hsum, integralTopForm_sum o ψ Finset.univ fun x _ ↦
      (e x).integrableTopForm_of_eq_mpullback (hfe x) (hmd x) hφ (hψc x) (hψs x) (hψ_eq x),
    degreeAtRegularValue_eq_sum hs, Int.cast_sum, Finset.sum_mul,
    ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun x _ ↦ hint x

end TauCeti
