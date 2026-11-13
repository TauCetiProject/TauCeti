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
# The integral formula for the degree

Let `f : M → N` be a `C¹` map from a compact Hausdorff boundaryless manifold to a Hausdorff manifold
of the same dimension, with orientations `o` of `M` and `o'` of `N`, and let `y` be a regular
value of `f`. The fibre over `y` is finite and `f` is a local diffeomorphism at each of its points.
Near `y`, the preimage of a small neighbourhood `V` of `y` is therefore a finite disjoint union of
open sheets, each carried diffeomorphically onto its image by `f`, and on each sheet `f` either
preserves or reverses orientation, according to its orientation sign at the point of the fibre. This
is the *stack of records* over `y`.

Every value in `V` then has exactly one preimage in each sheet, with the orientation sign of that
sheet, so it is again a regular value with the same signed count of preimages: the degree
`deg_y(f) = TauCeti.degreeAtRegularValue o o' f y` is locally constant on the regular values
(`TauCeti.eventually_isRegularValue_and_degreeAtRegularValue_eq`). In particular, when every value
is regular, as for a local diffeomorphism, and `N` is preconnected, the degree does not depend on
the value (`TauCeti.degreeAtRegularValue_eq_of_forall_isRegularValue`).

Splitting the pullback `f^*φ` of an integrable top form `φ` supported in `V` along the sheets and
changing variables on each of them gives
$$\int_M f^*\varphi = \deg_y(f) \int_N \varphi$$
(`TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`). A partition of
unity subordinate to finitely many such neighbourhoods globalizes the formula: if every point of
the support of `φ` is a regular value, then `f^*φ` is integrable
(`TauCeti.integrableTopForm_mpullback_of_forall_mem_tsupport`), and if moreover the degree is `c`
at each of them, then `∫_M f^*φ = c ∫_N φ`
(`TauCeti.integralTopForm_mpullback_eq_mul_of_forall_mem_tsupport`). When
every value is regular and `N` is preconnected this holds for every integrable top form, with `c`
the degree at any point
(`TauCeti.integralTopForm_mpullback_eq_degreeAtRegularValue_mul_of_forall_isRegularValue`). This
is the integral formula for the degree [Lee, Thm. 17.35] for `C¹` maps all of whose values in the
support of `φ` are regular; no Sard theorem is used. For smooth maps to a connected σ-compact
manifold modelled on the same space, `TauCeti/Geometry/Manifold/Degree/Global.lean` proves the
formula for every compactly supported smooth top form and every regular value.

The two manifolds may be modelled on different spaces of the same dimension.

## Main results

* `TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`: every regular
  value `y` has a neighbourhood `V` such that `∫_M f^*φ = deg_y(f) · ∫_N φ` for every integrable
  top form `φ` supported in `V`.
* `TauCeti.eventually_isRegularValue_and_degreeAtRegularValue_eq`: values near a regular value are
  regular, with the same degree.
* `TauCeti.degreeAtRegularValue_eq_of_forall_isRegularValue`: if every value is regular and `N`
  is preconnected, the degree is constant.
* `TauCeti.integrableTopForm_mpullback_of_forall_mem_tsupport`: the pullback of an integrable top
  form supported in regular values is integrable.
* `TauCeti.integralTopForm_mpullback_eq_mul_of_forall_mem_tsupport`: the integral formula for top
  forms supported in regular values of a fixed degree.
* `TauCeti.integralTopForm_mpullback_eq_degreeAtRegularValue_mul_of_forall_isRegularValue`: the
  integral formula when every value is regular and `N` is preconnected.
* `IsLocalDiffeomorph.integralTopForm_mpullback_eq_ncard_mul`: an orientation-preserving local
  diffeomorphism onto a preconnected manifold integrates every integrable top form as the number
  of preimages of any point times its integral.

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

variable {E E' H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
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
    obtain ⟨D, hD⟩ := (isRegularPoint_iff_isInvertible_mfderiv
      (o.card_eq.symm.trans o'.card_eq)).mp
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
    (hφt : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ e.target)
    (hψ0 : ∀ z ∉ e.source, ψ z = 0) (hψφ : ∀ z ∈ e.source, ψ z = mpullback I J f φ z) :
    IntegrableTopForm ψ ∧
      integralTopForm o ψ = orientationSign o o' f x * integralTopForm o' φ := by
  set K := _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ
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
  refine ⟨e.integrableTopForm_of_eq_mpullback hfe hmd (o.card_eq.symm.trans o'.card_eq) hφ hφt
    hψs hψφ, ?_⟩
  -- Change variables according to the orientation sign on the sheet.
  rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o') hx with h | h
  · rw [h, Int.cast_one, one_mul]
    exact e.integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt hfe
      (fun z hz ↦ orientationSign_eq_one_iff.mp ((hsgn z hz).trans h)) hφ hφt hψs hψφ
  · rw [h, Int.cast_neg, Int.cast_one, neg_one_mul]
    exact e.integralTopForm_of_eq_mpullback_of_isOrientationReversingAt hfe
      (fun z hz ↦ orientationSign_eq_neg_one_iff.mp ((hsgn z hz).trans h)) hφ hφt hψs hψφ

/-- The integral formula near a regular value, together with the integrability of the pullback:
`y` has a neighbourhood `V` such that for every integrable top form `φ` supported in `V`, the
pullback `f^*φ` is integrable and `∫_M f^*φ = deg_y(f) · ∫_N φ`. -/
private theorem exists_mem_nhds_integrableTopForm_and_integralTopForm [CompactSpace M]
    [T2Space M] [T2Space N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f) {y : N}
    (hy : IsRegularValue I J f y) :
    ∃ V ∈ 𝓝 y, ∀ φ : RoughForm J N ℝ k, IntegrableTopForm φ →
      _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V →
        IntegrableTopForm (mpullback I J f φ) ∧ integralTopForm o (mpullback I J f φ) =
          degreeAtRegularValue o o' f y * integralTopForm o' φ := by
  classical
  -- Split `f^*φ` into its parts on the sheets of the stack of records over `y`, change variables
  -- on each sheet according to the orientation sign there, and sum.
  set s := (hy.finite_preimage (o.card_eq.symm.trans o'.card_eq) hf.continuous).toFinset
  have hs (x : M) : x ∈ s ↔ f x = y := by simp [s]
  obtain ⟨e, hxe, hfe, hsgn, hdisj, V, hV, hVt, hVs⟩ :=
    exists_stack_of_records o o' hf hy s hs
  refine ⟨V, hV, fun φ hφ hφV ↦ ?_⟩
  set K := _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ
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
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  refine ⟨hsum ▸ IntegrableTopForm.sum b ψ Finset.univ fun x _ ↦ (hsheet x).1, ?_⟩
  rw [hsum, integralTopForm_sum o ψ Finset.univ fun x _ ↦ (hsheet x).1,
    degreeAtRegularValue_eq_sum hs, Int.cast_sum, Finset.sum_mul, ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun x _ ↦ (hsheet x).2

/-- **The integral formula for the degree near a regular value.** Let `f : M → N` be a `C¹` map
from a compact Hausdorff boundaryless manifold to a Hausdorff manifold of the same dimension,
with orientations `o` and `o'`, and let `y` be a regular value of `f`. Then `y` has a neighbourhood
`V` such that every integrable top form `φ` on `N` supported in `V` satisfies
`∫_M f^*φ = deg_y(f) · ∫_N φ`, where `deg_y(f)` is the signed count of the fibre over `y`. -/
theorem exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul [CompactSpace M]
    [T2Space M] [T2Space N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f) {y : N}
    (hy : IsRegularValue I J f y) :
    ∃ V ∈ 𝓝 y, ∀ φ : RoughForm J N ℝ k, IntegrableTopForm φ →
      _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V →
        integralTopForm o (mpullback I J f φ) =
          degreeAtRegularValue o o' f y * integralTopForm o' φ := by
  obtain ⟨V, hV, h⟩ := exists_mem_nhds_integrableTopForm_and_integralTopForm o o' hf hy
  exact ⟨V, hV, fun φ hφ hφV ↦ (h φ hφ hφV).2⟩

/-- **The degree is locally constant on the regular values.** Let `f : M → N` be a `C¹` map from a
compact Hausdorff boundaryless manifold to a Hausdorff manifold of the same dimension, with
orientations `o` and `o'`. Every value near a regular value `y` of `f` is a regular value, with the
same signed count of preimages: each sheet of the stack of records over `y` contains exactly one
preimage of it, at which `f` has the orientation sign of the sheet. -/
theorem eventually_isRegularValue_and_degreeAtRegularValue_eq [CompactSpace M] [T2Space M]
    [T2Space N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f) {y : N}
    (hy : IsRegularValue I J f y) :
    ∀ᶠ y' in 𝓝 y, IsRegularValue I J f y' ∧
      degreeAtRegularValue o o' f y' = degreeAtRegularValue o o' f y := by
  classical
  set s := (hy.finite_preimage (o.card_eq.symm.trans o'.card_eq) hf.continuous).toFinset
  have hs (x : M) : x ∈ s ↔ f x = y := by simp [s]
  obtain ⟨e, -, hfe, hsgn, hdisj, V, hV, hVt, hVs⟩ :=
    exists_stack_of_records o o' hf hy s hs
  filter_upwards [hV] with y' hy'
  -- Over `y'`, the sheet over `x` contains the preimage `(e x).symm y'`, and no other.
  have hzs (x : s) : (e x).symm y' ∈ (e x).source := (e x).map_target (hVt x hy')
  have hfz (x : s) : f ((e x).symm y') = y' := by
    rw [hfe x (hzs x), (e x).right_inv (hVt x hy')]
  have hfib (w : M) (hw : f w = y') : ∃ x, (e x).symm y' = w := by
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hVs (show f w ∈ V from hw ▸ hy'))
    exact ⟨x, by rw [← hw, hfe x hx, (e x).left_inv hx]⟩
  have hinj : Function.Injective fun x : s ↦ (e x).symm y' := fun x x' hxx' ↦ by
    by_contra hne
    exact (hdisj hne).le_bot ⟨hzs x, (congrArg (· ∈ (e x').source) hxx').mpr (hzs x')⟩
  -- The orientation sign at `(e x).symm y'` is the nonzero sign at `x`, so it is a regular point.
  have hsign (x : s) : orientationSign o o' f ((e x).symm y') = orientationSign o o' f x :=
    hsgn x _ (hzs x)
  have hreg (x : s) : IsRegularPoint I J f ((e x).symm y') := by
    rw [isRegularPoint_iff_isInvertible_mfderiv (o.card_eq.symm.trans o'.card_eq),
      ← not_not (a := (mfderiv I J f _).IsInvertible), ← orientationSign_eq_zero_iff (o := o)
      (o' := o'), hsign]
    rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o')
      (hy.isRegularPoint ((hs x).mp x.2)) with h | h <;> simp [h]
  have hmem (w : M) : w ∈ Finset.univ.image (fun x : s ↦ (e x).symm y') ↔ f w = y' := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ hfz x, hfib w⟩
  refine ⟨isRegularValue_iff.2 fun w hw ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hfib w hw
    exact hreg x
  · rw [degreeAtRegularValue_eq_sum hmem, Finset.sum_image fun x _ x' _ h ↦ hinj h,
      degreeAtRegularValue_eq_sum hs, ← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun x _ ↦ hsign x

/-- **The degree of a map without critical values is constant.** If every value of a `C¹` map `f`
from a compact Hausdorff boundaryless manifold to a preconnected Hausdorff manifold of the same
dimension is regular, as for a local diffeomorphism, then the signed count of preimages is the
same at every value. -/
theorem degreeAtRegularValue_eq_of_forall_isRegularValue [CompactSpace M] [T2Space M] [T2Space N]
    [PreconnectedSpace N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f)
    (hreg : ∀ y, IsRegularValue I J f y) (y y' : N) :
    degreeAtRegularValue o o' f y = degreeAtRegularValue o o' f y' :=
  ((IsLocallyConstant.iff_eventually_eq _).2 fun y ↦
    (eventually_isRegularValue_and_degreeAtRegularValue_eq o o' hf (hreg y)).mono
      fun _ h ↦ h.2).apply_eq_of_preconnectedSpace y y'

/-- The integrability of the pullback of a top form supported in regular values, together with
the global integral formula when the degree is `c` on its support. -/
private theorem integrableTopForm_and_integralTopForm_mpullback_of_forall_mem_tsupport
    [CompactSpace M] [T2Space M] [T2Space N] [BoundarylessManifold I M]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : ContMDiff I J 1 f) {φ : RoughForm J N ℝ k} (hφ : IntegrableTopForm φ)
    (hreg : ∀ y ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ, IsRegularValue I J f y) :
    IntegrableTopForm (mpullback I J f φ) ∧ ∀ c : ℤ,
      (∀ y ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ, degreeAtRegularValue o o' f y = c) →
        integralTopForm o (mpullback I J f φ) = c * integralTopForm o' φ := by
  classical
  have : LocallyCompactSpace H' := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  set K := _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ
  -- Each point of the support has a neighbourhood on which the local integral formula holds.
  choose V hV hVφ using fun y : K ↦
    exists_mem_nhds_integrableTopForm_and_integralTopForm o o' hf (hreg y y.2)
  obtain ⟨t, ht⟩ := hφ.isCompact.elim_finite_subcover (fun y : K ↦ interior (V y))
    (fun _ ↦ isOpen_interior) fun y hy ↦
      mem_iUnion.mpr ⟨⟨y, hy⟩, mem_interior_iff_mem_nhds.mpr (hV ⟨y, hy⟩)⟩
  -- A partition of unity subordinate to finitely many of them splits `φ` into localized pieces.
  obtain ⟨ρ, hρ, -⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hφ.isCompact (fun y : t ↦ interior (V y)) (fun _ ↦ isOpen_interior)
    (locallyFinite_of_finite _) fun y hy ↦ by
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (ht hy)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩
  let φ' (i : t) : RoughForm J N ℝ k := fun y ↦ ρ i y • φ y
  have hφ' (i : t) : IntegrableTopForm (φ' i) :=
    hφ.fun_smul (ρ i).continuous fun y ↦ abs_le.mpr
      ⟨by linarith [ρ.nonneg i y], ρ.le_one i y⟩
  have hφ'V (i : t) : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) (φ' i) ⊆ V i :=
    (tsupport_smul_subset_left _ _).trans ((hρ i).trans interior_subset)
  have hsum : φ = ∑ i, φ' i :=
    (φ.eq_sum_fun_smul (fun i : t ↦ ρ i) fun y hy ↦ by
      rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one hy).trans (Finset.sum_fn _ _).symm
  have hpull : mpullback I J f φ = ∑ i, mpullback I J f (φ' i) := by
    rw [hsum]
    exact map_sum (AddMonoidHom.mk' (mpullback I J f) (mpullback_add f)) _ _
  have hloc (i : t) := hVφ i (φ' i) (hφ' i) (hφ'V i)
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using o.card_eq.symm)
  refine ⟨hpull ▸ IntegrableTopForm.sum b _ Finset.univ fun i _ ↦ (hloc i).1, fun c hc ↦ ?_⟩
  rw [hpull, integralTopForm_sum o _ Finset.univ fun i _ ↦ (hloc i).1, hsum,
    integralTopForm_sum o' _ Finset.univ fun i _ ↦ hφ' i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [(hloc i).2, hc i (i : K).2]

/-- **Integrability of pullbacks of top forms supported in regular values.** Let `f : M → N` be a
`C¹` map from a compact Hausdorff boundaryless manifold to a Hausdorff manifold of the same
dimension, with orientations `o` and `o'`, and let `φ` be an integrable top form on `N` every point
of whose support is a regular value of `f`. Then `f^*φ` is integrable. -/
theorem integrableTopForm_mpullback_of_forall_mem_tsupport [CompactSpace M] [T2Space M]
    [T2Space N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f)
    {φ : RoughForm J N ℝ k} (hφ : IntegrableTopForm φ)
    (hreg : ∀ y ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ, IsRegularValue I J f y) :
    IntegrableTopForm (mpullback I J f φ) :=
  (integrableTopForm_and_integralTopForm_mpullback_of_forall_mem_tsupport o o' hf hφ hreg).1

/-- **The integral formula for the degree.** Let `f : M → N` be a `C¹` map from a compact
Hausdorff boundaryless manifold to a Hausdorff manifold of the same dimension, with orientations
`o` and `o'`, and let `φ` be an integrable top form on `N` every point of whose support is a
regular value of `f` at which the degree is `c`. Then `∫_M f^*φ = c · ∫_N φ`. -/
theorem integralTopForm_mpullback_eq_mul_of_forall_mem_tsupport [CompactSpace M] [T2Space M]
    [T2Space N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f)
    {φ : RoughForm J N ℝ k} (hφ : IntegrableTopForm φ) {c : ℤ}
    (hc : ∀ y ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ,
      IsRegularValue I J f y ∧ degreeAtRegularValue o o' f y = c) :
    integralTopForm o (mpullback I J f φ) = c * integralTopForm o' φ :=
  (integrableTopForm_and_integralTopForm_mpullback_of_forall_mem_tsupport o o' hf hφ
    fun y hy ↦ (hc y hy).1).2 c fun y hy ↦ (hc y hy).2

/-- **The integral formula for a map without critical values.** If every value of a `C¹` map `f`
from a compact Hausdorff boundaryless manifold to a preconnected Hausdorff manifold of the same
dimension is regular, as for a local diffeomorphism, then `∫_M f^*φ = deg_y(f) · ∫_N φ` for every
integrable top form `φ` and every value `y`. -/
theorem integralTopForm_mpullback_eq_degreeAtRegularValue_mul_of_forall_isRegularValue
    [CompactSpace M] [T2Space M] [T2Space N] [PreconnectedSpace N] [BoundarylessManifold I M]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : ContMDiff I J 1 f) (hreg : ∀ y, IsRegularValue I J f y) (y : N)
    {φ : RoughForm J N ℝ k} (hφ : IntegrableTopForm φ) :
    integralTopForm o (mpullback I J f φ) = degreeAtRegularValue o o' f y * integralTopForm o' φ :=
  integralTopForm_mpullback_eq_mul_of_forall_mem_tsupport o o' hf hφ fun y' _ ↦
    ⟨hreg y', degreeAtRegularValue_eq_of_forall_isRegularValue o o' hf hreg y' y⟩

/-- **The integral formula for an orientation-preserving local diffeomorphism.** Let `f : M → N`
be a `C¹` local diffeomorphism from a compact Hausdorff boundaryless manifold to a preconnected
Hausdorff manifold, preserving the orientations `o` and `o'` at every point. Then
`∫_M f^*φ = |f⁻¹(p)| · ∫_N φ` for every integrable top form `φ` and every point `p` of `N`: the
fibres all have the same finite number of points, the degree of `f`. -/
theorem _root_.IsLocalDiffeomorph.integralTopForm_mpullback_eq_ncard_mul [CompactSpace M]
    [T2Space M] [T2Space N] [PreconnectedSpace N] [BoundarylessManifold I M] {n : WithTop ℕ∞}
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0)
    (hor : ∀ x, IsOrientationPreservingAt o o' f x) (p : N) {φ : RoughForm J N ℝ k}
    (hφ : IntegrableTopForm φ) :
    integralTopForm o (mpullback I J f φ) = (f ⁻¹' {p}).ncard * integralTopForm o' φ := by
  rw [integralTopForm_mpullback_eq_degreeAtRegularValue_mul_of_forall_isRegularValue o o'
    (hf.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)) (hf.isRegularValue hn) p hφ,
    degreeAtRegularValue_eq_ncard fun x _ ↦ hor x,
    Int.cast_natCast]

end TauCeti
