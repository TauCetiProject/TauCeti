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

Let `f : M → N` be a `C¹` map from a compact Hausdorff boundaryless manifold to a Hausdorff manifold
modelled on the same space, with orientations `o` of `M` and `o'` of `N`, and let `y` be a regular
value of `f`. The fibre over `y` is finite and `f` is a local diffeomorphism at each of its points.
Near `y`, the preimage of a small neighbourhood `V` of `y` is therefore a finite disjoint union of
open sheets, each carried diffeomorphically onto its image by `f`, and on each sheet `f` either
preserves or reverses orientation, according to its orientation sign at the point of the fibre. This
is the *stack of records* over `y`.

Splitting the pullback `f^*φ` of an integrable top form `φ` supported in `V` along the sheets and
changing variables on each of them gives
$$\int_M f^*\varphi = \deg_y(f) \int_N \varphi,$$
where `deg_y(f)` is the signed count `TauCeti.degreeAtRegularValue o o' f y` of the fibre
(`TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`). This is the
local computation in the proof that, between compact connected oriented manifolds, the signed
count does not depend on the regular value and satisfies `∫_M f^*φ = deg · ∫_N φ` for every top
form [Lee, Thm. 17.35].

## Main results

* `TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`: every regular
  value `y` has a neighbourhood `V` such that `∫_M f^*φ = deg_y(f) · ∫_N φ` for every integrable
  top form `φ` supported in `V`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory, proof of Theorem 17.35.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §1 (the stack of records) and §5.
* The construction of the stack of records follows the proof of Mathlib's
  `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph` (`Mathlib/Topology/Covering/Basic.lean`),
  which separates a finite fibre by `Set.Finite.t2_separation` and uses that `f` is a closed map
  to find a neighbourhood of the base point whose preimage lies in the separated sheets.
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

/-- **The stack of records.** Over a regular value `y` of a `C¹` map `f` from a compact Hausdorff
boundaryless manifold to a Hausdorff manifold, the points `x` of the fibre have pairwise disjoint
open neighbourhoods, the sources of open partial homeomorphisms `e x` agreeing with `f`, on which
the orientation sign of `f` is constant; and `y` has a neighbourhood whose preimage is covered by
these sheets and which lies in each of their images. The construction adapts the proof of
Mathlib's `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph`. -/
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
        (eventually_orientationSign_eq (o := o) (o' := o') hf.contMDiffAt ⟨D, hD⟩))
    refine ⟨Φ.restrOpen W hWo, ⟨hxΦ, hxW⟩, fun z _ ↦ congrFun hfΦ z,
      fun z hz ↦ (hWsub hz.2).1, fun z hz ↦ (hWsub hz.2).2⟩
  choose e hxe hfe hU' hsgn using key
  refine ⟨e, hxe, hfe, hsgn, fun x x' hxx' ↦ ?_, ?_⟩
  · exact (hUd x.2 x'.2 (Subtype.coe_injective.ne hxx')).mono (hU' x) (hU' x')
  -- Since `f` is a closed map, the fibres near `y` stay inside the open union of the sheets.
  have hE := hf.continuous.isClosedMap.eventually_nhds_fiber (p := (· ∈ ⋃ x, (e x).source)) y
    fun z hz ↦ (isOpen_iUnion fun x ↦ (e x).open_source).mem_nhds
      (mem_iUnion.mpr ⟨⟨z, (hs z).mpr hz⟩, hxe _⟩)
  refine ⟨(⋂ x, (e x).target) ∩ {y' | ∀ z ∈ f ⁻¹' {y'}, z ∈ ⋃ x, (e x).source}, inter_mem
    (Filter.iInter_mem.mpr fun x ↦ (e x).open_target.mem_nhds ?_) hE,
    fun x ↦ inter_subset_left.trans (iInter_subset _ x), fun z hz ↦ hz.2 z rfl⟩
  rw [← (hs x).mp x.2, hfe x (hxe x)]
  exact (e x).map_source (hxe x)

/-- **One sheet of the stack of records.** Let `e` be an open partial homeomorphism agreeing with
`f` on its source, on which the orientation sign of `f` is constant, equal to its value at a
regular point `x`. For an integrable top form `φ` supported in the target of `e`, a form `ψ`
vanishing off the source of `e` and agreeing there with `f^*φ` is integrable, and
`∫_M ψ = sign_x(f) · ∫_N φ`. -/
private theorem integrableTopForm_and_integralTopForm_sheet [T2Space M]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : ContMDiff I J 1 f) (e : OpenPartialHomeomorph M N) (hfe : EqOn f e e.source) {x : M}
    (hx : IsRegularPoint I J f x)
    (hsgn : ∀ z ∈ e.source, orientationSign o o' f z = orientationSign o o' f x)
    {φ : RoughForm J N ℝ k} {ψ : RoughForm I M ℝ k} (hφ : IntegrableTopForm φ)
    (hφt : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ e.target)
    (hψ0 : ∀ z ∉ e.source, ψ z = 0) (hψφ : ∀ z ∈ e.source, ψ z = mpullback I J f φ z) :
    IntegrableTopForm ψ ∧
      integralTopForm o ψ = orientationSign o o' f x * integralTopForm o' φ := by
  set K := _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ
  -- `ψ` vanishes off the source and `f^*φ` vanishes off `f ⁻¹' K`, so the support of `ψ` lies in
  -- `e.symm '' K`. That set is compact, hence closed since `M` is Hausdorff, and lies in the
  -- source.
  have hK : IsCompact (e.symm '' K) :=
    hφ.isCompact.image_of_continuousOn (e.continuousOn_symm.mono hφt)
  have hψs : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ψ ⊆ e.source := by
    refine (closure_minimal (fun z hz ↦ ?_) hK.isClosed).trans
      (image_subset_iff.mpr fun q hq ↦ e.map_target (hφt hq))
    have hzs : z ∈ e.source := by_contra fun h ↦ hz (hψ0 z h)
    have hfz : f z ∈ K := by_contra fun h ↦ hz ((hψφ z hzs).trans
      (mpullback_apply_eq_zero (image_eq_zero_of_notMem_tsupport h)))
    exact ⟨f z, hfz, by rw [hfe hzs, e.left_inv hzs]⟩
  have hmd : ∀ z ∈ e.source, MDifferentiableAt I J f z :=
    fun z _ ↦ hf.mdifferentiable one_ne_zero z
  refine ⟨e.integrableTopForm_of_eq_mpullback hfe hmd rfl hφ hφt hψs hψφ, ?_⟩
  -- Change variables according to the orientation sign on the sheet.
  rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o') hx with h | h
  · rw [h, Int.cast_one, one_mul]
    exact e.integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt hfe hmd
      (fun z hz ↦ orientationSign_eq_one_iff.mp ((hsgn z hz).trans h)) hφ hφt hψs hψφ
  · rw [h, Int.cast_neg, Int.cast_one, neg_one_mul]
    exact e.integralTopForm_of_eq_mpullback_of_isOrientationReversingAt hfe hmd
      (fun z hz ↦ orientationSign_eq_neg_one_iff.mp ((hsgn z hz).trans h)) hφ hφt hψs hψφ

/-- **The integral formula for the degree near a regular value.** Let `f : M → N` be a `C¹` map
from a compact Hausdorff boundaryless manifold to a Hausdorff manifold modelled on the same space,
with orientations `o` and `o'`, and let `y` be a regular value of `f`. Then `y` has a neighbourhood
`V` such that every integrable top form `φ` on `N` supported in `V` satisfies
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
    mpullback_apply_eq_zero (image_eq_zero_of_notMem_tsupport hz)
  -- Each part is integrable, with integral the orientation sign at `x` times `∫_N φ`.
  have hsheet (x : s) := integrableTopForm_and_integralTopForm_sheet o o' hf (e x) (hfe x)
    (hy.isRegularPoint ((hs x).mp x.2)) (hsgn x) hφ (hφV.trans (hVt x)) (hψ_zero x) (hψ_eq x)
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
  rw [hsum, integralTopForm_sum o ψ Finset.univ fun x _ ↦ (hsheet x).1,
    degreeAtRegularValue_eq_sum hs, Int.cast_sum, Finset.sum_mul, ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun x _ ↦ (hsheet x).2

end TauCeti
