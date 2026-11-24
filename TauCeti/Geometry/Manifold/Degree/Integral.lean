/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.LocallyConstant
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.RegularValue.Covering

/-!
# The integral formula for the degree

Let `f : M → N` be a proper `C¹` map from a Hausdorff boundaryless manifold to a manifold of the
same dimension, with orientations `o` of `M` and `o'` of `N`, and let `y` be a regular value of `f`;
every continuous map from a compact space to a Hausdorff space is proper. The fibre over `y` is
finite, and over a small neighbourhood `V` of `y` the map `f` is trivialized
(`TauCeti.IsRegularValue.exists_trivialization_contMDiffOn_symm`). The preimage of `V` is therefore
a finite disjoint union of open sheets, labelled by the points of the fibre, each carried
homeomorphically onto `V` by `f`; shrinking `V`, `f` either preserves or reverses orientation on
each sheet, according to its orientation sign at the point of the fibre. This is the *stack of
records* over `y`.

Splitting the pullback `f^*φ` of an integrable top form `φ` supported in `V` along the sheets and
changing variables on each of them gives
$$\int_M f^*\varphi = \deg_y(f) \int_N \varphi$$
(`TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`), where
`deg_y(f) = TauCeti.degreeAtRegularValue o o' f y` is the signed count of the fibre. A partition of
unity subordinate to finitely many such neighbourhoods
(`TauCeti.IntegrableTopForm.exists_eq_sum_tsupport_subset`) globalizes the formula: if every point
of the support of `φ` is a regular value, then `f^*φ` is integrable, with no orientation needed
(`TauCeti.integrableTopForm_mpullback_of_isRegularValue_on_tsupport`), and if moreover the degree is
`c` at each of them, then `∫_M f^*φ = c ∫_N φ`
(`TauCeti.integralTopForm_mpullback_eq_mul_of_isRegularValue_and_const_degree_on_tsupport`). When
every value is regular and `N` is preconnected, the degree is constant
(`TauCeti.degreeAtRegularValue_eq_of_forall_isRegularValue`, in
`TauCeti/Geometry/Manifold/Degree/LocallyConstant.lean`), so the formula holds for every
integrable top form, with `c` the degree at any point
(`TauCeti.integralTopForm_mpullback_eq_degreeAtRegularValue_mul_of_forall_isRegularValue`). This
is the integral formula for the degree [Lee, Thm. 17.35] for `C¹` maps all of whose values in the
support of `φ` are regular; no Sard theorem is used. For smooth proper maps to a connected
σ-compact Hausdorff boundaryless manifold, `TauCeti/Geometry/Manifold/Degree/Global.lean` proves
the formula for every compactly supported smooth top form and every regular value.

The two manifolds may be modelled on different spaces of the same dimension.

## Main results

* `TauCeti.exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul`: every regular
  value `y` has a neighbourhood `V` such that `∫_M f^*φ = deg_y(f) · ∫_N φ` for every integrable
  top form `φ` supported in `V`.
* `TauCeti.integrableTopForm_mpullback_of_isRegularValue_on_tsupport`: the pullback of an
  integrable top form supported in regular values is integrable.
* `TauCeti.integralTopForm_mpullback_eq_mul_of_isRegularValue_and_const_degree_on_tsupport`: the
  integral formula for top forms supported in regular values of a fixed degree.
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
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {k : ℕ}

open Manifold.Orientation

/-- **The stack of records.** Over a regular value `y` of a proper `C¹` map `f` from a Hausdorff
boundaryless manifold to a manifold of the same dimension, the points `x` of the fibre label
pairwise disjoint open sheets, the sources of open partial homeomorphisms `e x` agreeing with `f`,
on which a property `P x` that holds near `x` holds throughout; and `y` has a neighbourhood whose
preimage is covered by these sheets and which lies in each of their images. The sheets are the
slices of a trivialization of `f` near `y`
(`TauCeti.IsRegularValue.exists_trivialization_contMDiffOn_symm`), over a neighbourhood of `y`
small enough for the finitely many conditions `P x`. -/
private theorem exists_stack_of_records [T2Space M] [BoundarylessManifold I M]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {f : M → N} (hf : ContMDiff I J 1 f)
    (hfp : IsProperMap f) {y : N} (hy : IsRegularValue I J f y) {P : M → M → Prop}
    (hP : ∀ x, f x = y → ∀ᶠ z in 𝓝 x, P x z) :
    ∃ e : f ⁻¹' {y} → OpenPartialHomeomorph M N, (∀ x, EqOn f (e x) (e x).source) ∧
      (∀ x : f ⁻¹' {y}, ∀ z ∈ (e x).source, P x z) ∧
      Pairwise (fun x x' ↦ Disjoint (e x).source (e x').source) ∧
      ∃ V ∈ 𝓝 y, (∀ x, V ⊆ (e x).target) ∧ f ⁻¹' V ⊆ ⋃ x, (e x).source := by
  by_cases hyf : y ∉ range f
  · -- The fibre is empty, and so are the fibres over the open complement of the closed range.
    have : IsEmpty (f ⁻¹' {y}) := ⟨fun x ↦ hyf ⟨x, x.property⟩⟩
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, (range f)ᶜ,
      hfp.isClosedMap.isClosed_range.isOpen_compl.mem_nhds hyf, isEmptyElim,
      fun z hz ↦ (hz ⟨z, rfl⟩).elim⟩
  obtain ⟨t, hyt, -, hlabel, hsmooth⟩ :=
    hy.exists_trivialization_contMDiffOn_symm hdim hf le_rfl hfp (not_not.1 hyf)
  have : Finite (f ⁻¹' {y}) := (hy.finite_preimage_of_isProperMap hdim hfp).to_subtype
  -- Shrink the base of `t` to an open neighbourhood `W` of `y` over which the branch of `f`
  -- through each point `x` of the fibre satisfies `P x`.
  have hPW : ∀ᶠ w in 𝓝 y, w ∈ t.baseSet ∧
      ∀ x : f ⁻¹' {y}, P x (t.toOpenPartialHomeomorph.symm (w, x)) := by
    refine (t.open_baseSet.eventually_mem hyt).and (eventually_all.2 fun x ↦ Tendsto.eventually
      (p := P x) ((hsmooth x).continuousOn.continuousAt (t.open_baseSet.mem_nhds hyt)) ?_)
    simp only [hlabel x]
    exact hP x x.property
  obtain ⟨W, hWP, hWo, hyW⟩ := mem_nhds_iff.1 hPW
  -- The sheet labelled by `x` is the slice of `t` over `W` at `x`; its inverse is the branch.
  have hleft (x : f ⁻¹' {y}) {z : M} (hz : z ∈ t.source ∩ t ⁻¹' (W ×ˢ {x})) :
      t.toOpenPartialHomeomorph.symm (f z, x) = z := by
    rw [← mem_singleton_iff.1 hz.2.2]
    exact t.symm_apply_mk_proj hz.1
  let e (x : f ⁻¹' {y}) : OpenPartialHomeomorph M N :=
    { toFun := f
      invFun w := t.toOpenPartialHomeomorph.symm (w, x)
      source := t.source ∩ t ⁻¹' (W ×ˢ {x})
      target := W
      map_source' _ hz := t.coe_fst hz.1 ▸ hz.2.1
      map_target' w hw := ⟨t.map_target (t.mem_target.2 (hWP hw).1), by
        rw [mem_preimage, t.apply_symm_apply' (hWP hw).1]
        exact ⟨hw, rfl⟩⟩
      left_inv' _ hz := hleft x hz
      right_inv' w hw := t.proj_symm_apply' (hWP hw).1
      open_source := t.toOpenPartialHomeomorph.isOpen_inter_preimage
        (hWo.prod (isOpen_discrete _))
      open_target := hWo
      continuousOn_toFun := hf.continuous.continuousOn
      continuousOn_invFun := (hsmooth x).continuousOn.mono fun _ hw ↦ (hWP hw).1 }
  refine ⟨e, fun _ _ _ ↦ rfl, fun x z hz ↦ hleft x hz ▸ (hWP ((e x).map_source hz)).2 x,
    fun x x' hxx' ↦ disjoint_left.2 fun z hz hz' ↦
      hxx' ((mem_singleton_iff.1 hz.2.2).symm.trans (mem_singleton_iff.1 hz'.2.2)),
    W, hWo.mem_nhds hyW, fun _ ↦ subset_rfl, fun z hz ↦ mem_iUnion.2 ⟨(t z).2,
      t.mem_source.2 (hWP hz).1, ?_⟩⟩
  rw [mem_preimage, ← t.mk_proj_snd' (hWP hz).1]
  exact ⟨hz, rfl⟩

omit [FiniteDimensional ℝ E'] in
/-- **One sheet of the stack of records: integrability.** Let `e` be an open partial homeomorphism
agreeing with a `C¹` map `f` between manifolds of the same dimension on its source. For an
integrable top form `φ` supported in the target of `e`, the part of `f^*φ` on the source of `e` is
integrable. -/
private theorem integrableTopForm_sheet [T2Space M]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {f : M → N} (hf : ContMDiff I J 1 f)
    (e : OpenPartialHomeomorph M N) (hfe : EqOn f e e.source) {φ : RoughForm J N ℝ k}
    (hφ : IntegrableTopForm φ) (hφt : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ e.target) :
    IntegrableTopForm (I := I) fun z ↦
      e.source.indicator (fun _ ↦ (1 : ℝ)) z • mpullback I J f φ z :=
  have hψφ (z : M) (hz : z ∈ e.source) :
      e.source.indicator (fun _ ↦ (1 : ℝ)) z • mpullback I J f φ z = mpullback I J f φ z := by
    rw [indicator_of_mem hz, one_smul]
  e.integrableTopForm_of_eq_mpullback hfe (fun z _ ↦ hf.mdifferentiable one_ne_zero z) hdim hφ hφt
    (e.tsupport_subset_source_of_eq_mpullback hfe hφ.isCompact hφt
      (fun _ hz ↦ by rw [indicator_of_notMem hz, zero_smul]) hψφ) hψφ

/-- **One sheet of the stack of records: the integral.** Let `e` be an open partial homeomorphism
agreeing with `f` on its source, on which the orientation sign of `f` is constant, equal to its
value at a regular point `x`. For an integrable top form `φ` supported in the target of `e`, the
part `ψ` of `f^*φ` on the source of `e` satisfies `∫_M ψ = sign_x(f) · ∫_N φ`. -/
private theorem integralTopForm_sheet [T2Space M]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (e : OpenPartialHomeomorph M N) (hfe : EqOn f e e.source) {x : M}
    (hx : IsRegularPoint I J f x)
    (hsgn : ∀ z ∈ e.source, orientationSign o o' f z = orientationSign o o' f x)
    {φ : RoughForm J N ℝ k} (hφ : IntegrableTopForm φ)
    (hφt : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ e.target) :
    integralTopForm o (fun z ↦ e.source.indicator (fun _ ↦ (1 : ℝ)) z • mpullback I J f φ z) =
      orientationSign o o' f x * integralTopForm o' φ := by
  have hψφ (z : M) (hz : z ∈ e.source) :
      e.source.indicator (fun _ ↦ (1 : ℝ)) z • mpullback I J f φ z = mpullback I J f φ z := by
    rw [indicator_of_mem hz, one_smul]
  have hψs := e.tsupport_subset_source_of_eq_mpullback hfe hφ.isCompact hφt
    (fun _ hz ↦ by rw [indicator_of_notMem hz, zero_smul]) hψφ
  -- Change variables according to the orientation sign on the sheet.
  rcases orientationSign_eq_one_or_eq_neg_one_of_isRegularPoint (o := o) (o' := o') hx with h | h
  · rw [h, Int.cast_one, one_mul]
    exact e.integralTopForm_of_eq_mpullback_of_isOrientationPreservingAt hfe
      (fun z hz ↦ orientationSign_eq_one_iff.mp ((hsgn z hz).trans h)) hφ hφt hψs hψφ
  · rw [h, Int.cast_neg, Int.cast_one, neg_one_mul]
    exact e.integralTopForm_of_eq_mpullback_of_isOrientationReversingAt hfe
      (fun z hz ↦ orientationSign_eq_neg_one_iff.mp ((hsgn z hz).trans h)) hφ hφt hψs hψφ

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [FiniteDimensional ℝ E'] [IsManifold J 1 N] in
/-- **The sheets decompose the pullback.** If the preimage of `V` is covered by pairwise disjoint
sheets, the pullback of a form supported in `V` is the sum of its parts on the sheets. -/
private theorem mpullback_eq_sum_indicator {ι : Type*} [Fintype ι] {f : M → N}
    (e : ι → OpenPartialHomeomorph M N)
    (hdisj : Pairwise (fun x x' ↦ Disjoint (e x).source (e x').source)) {V : Set N}
    (hVs : f ⁻¹' V ⊆ ⋃ x, (e x).source) {φ : RoughForm J N ℝ k}
    (hφV : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V) :
    mpullback I J f φ = ∑ x, fun z ↦
      (e x).source.indicator (fun _ ↦ (1 : ℝ)) z • mpullback I J f φ z := by
  classical
  funext z
  rw [Finset.sum_apply]
  by_cases hz : ∃ x, z ∈ (e x).source
  · obtain ⟨x, hx⟩ := hz
    rw [Finset.sum_eq_single x (fun x' _ hx' ↦ by
      rw [indicator_of_notMem fun h ↦ (hdisj hx').le_bot ⟨h, hx⟩, zero_smul]) (by simp),
      indicator_of_mem hx, one_smul]
  · simp only [not_exists] at hz
    rw [Finset.sum_eq_zero fun x _ ↦ by rw [indicator_of_notMem (hz x), zero_smul]]
    refine mpullback_apply_eq_zero (image_eq_zero_of_notMem_tsupport fun hfz ↦ ?_)
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hVs (hφV hfz))
    exact hz x hx

omit [FiniteDimensional ℝ E'] [IsManifold J 1 N] in
/-- An integrable top form of degree `k` on `N` forces `E'`, and hence `E` when the two have the
same dimension, to have dimension `k`. -/
private theorem nonempty_basis_of_integrableTopForm
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {φ : RoughForm J N ℝ k}
    (hφ : IntegrableTopForm φ) : Nonempty (Module.Basis (Fin k) ℝ E) := by
  obtain ⟨b⟩ := hφ.nonempty_basis
  exact ⟨Module.finBasisOfFinrankEq ℝ E
    (hdim.trans ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin k)))⟩

omit [FiniteDimensional ℝ E'] in
/-- **The stack of records: integrability.** If the preimage of `V` is covered by pairwise
disjoint sheets of open partial homeomorphisms agreeing with a `C¹` map `f` between manifolds of
the same dimension, each containing `V` in its image, then the pullback of an integrable top form
supported in `V` is integrable: it is the sum of its integrable parts on the sheets. -/
private theorem integrableTopForm_mpullback_of_stack [T2Space M]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {f : M → N} (hf : ContMDiff I J 1 f)
    {ι : Type*} [Finite ι] (e : ι → OpenPartialHomeomorph M N)
    (hfe : ∀ x, EqOn f (e x) (e x).source)
    (hdisj : Pairwise (fun x x' ↦ Disjoint (e x).source (e x').source)) {V : Set N}
    (hVt : ∀ x, V ⊆ (e x).target) (hVs : f ⁻¹' V ⊆ ⋃ x, (e x).source) {φ : RoughForm J N ℝ k}
    (hφ : IntegrableTopForm φ) (hφV : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V) :
    IntegrableTopForm (mpullback I J f φ) := by
  have := Fintype.ofFinite ι
  obtain ⟨b⟩ := nonempty_basis_of_integrableTopForm hdim hφ
  rw [mpullback_eq_sum_indicator e hdisj hVs hφV]
  exact IntegrableTopForm.sum b _ Finset.univ fun x _ ↦
    integrableTopForm_sheet hdim hf (e x) (hfe x) hφ (hφV.trans (hVt x))

/-- Pullbacks near a regular value are integrable: `y` has a neighbourhood `V` such that for every
integrable top form `φ` supported in `V`, the pullback `f^*φ` is integrable. -/
private theorem exists_mem_nhds_integrableTopForm [T2Space M] [BoundarylessManifold I M]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {f : M → N} (hf : ContMDiff I J 1 f)
    (hfp : IsProperMap f) {y : N} (hy : IsRegularValue I J f y) :
    ∃ V ∈ 𝓝 y, ∀ φ : RoughForm J N ℝ k, IntegrableTopForm φ →
      _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V → IntegrableTopForm (mpullback I J f φ) := by
  have : Finite (f ⁻¹' {y}) := (hy.finite_preimage_of_isProperMap hdim hfp).to_subtype
  obtain ⟨e, hfe, -, hdisj, V, hV, hVt, hVs⟩ := exists_stack_of_records hdim hf hfp hy
    (P := fun _ _ ↦ True) fun _ _ ↦ Eventually.of_forall fun _ ↦ trivial
  exact ⟨V, hV, fun φ hφ hφV ↦
    integrableTopForm_mpullback_of_stack hdim hf e hfe hdisj hVt hVs hφ hφV⟩

/-- The integral formula near a regular value, together with the integrability of the pullback:
`y` has a neighbourhood `V` such that for every integrable top form `φ` supported in `V`, the
pullback `f^*φ` is integrable and `∫_M f^*φ = deg_y(f) · ∫_N φ`. -/
private theorem exists_mem_nhds_integrableTopForm_and_integralTopForm [T2Space M]
    [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f)
    (hfp : IsProperMap f) {y : N} (hy : IsRegularValue I J f y) :
    ∃ V ∈ 𝓝 y, ∀ φ : RoughForm J N ℝ k, IntegrableTopForm φ →
      _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V →
        IntegrableTopForm (mpullback I J f φ) ∧ integralTopForm o (mpullback I J f φ) =
          degreeAtRegularValue o o' f y * integralTopForm o' φ := by
  -- Split `f^*φ` into its parts on the sheets of the stack of records over `y`, change variables
  -- on each sheet according to the orientation sign there, and sum.
  have hdim := o.card_eq.symm.trans o'.card_eq
  have : Finite (f ⁻¹' {y}) := (hy.finite_preimage_of_isProperMap hdim hfp).to_subtype
  have := Fintype.ofFinite (f ⁻¹' {y})
  obtain ⟨e, hfe, hsgn, hdisj, V, hV, hVt, hVs⟩ := exists_stack_of_records hdim hf hfp hy
    (P := fun x z ↦ orientationSign o o' f z = orientationSign o o' f x) fun _ hx ↦
      eventually_orientationSign_eq hf.contMDiffAt
        ((isRegularPoint_iff_isInvertible_mfderiv hdim).mp (hy.isRegularPoint hx))
  refine ⟨V, hV, fun φ hφ hφV ↦
    ⟨integrableTopForm_mpullback_of_stack hdim hf e hfe hdisj hVt hVs hφ hφV, ?_⟩⟩
  rw [mpullback_eq_sum_indicator e hdisj hVs hφV, integralTopForm_sum o _ Finset.univ fun x _ ↦
      integrableTopForm_sheet hdim hf (e x) (hfe x) hφ (hφV.trans (hVt x))]
  -- Index the signed count of the fibre by its points, as the sheets are.
  rw [degreeAtRegularValue_def, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  rw [Int.cast_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ ↦ integralTopForm_sheet o o' (e x) (hfe x)
    (hy.isRegularPoint x.property) (hsgn x) hφ (hφV.trans (hVt x))

/-- **The integral formula for the degree near a regular value.** Let `f : M → N` be a proper `C¹`
map from a Hausdorff boundaryless manifold to a manifold of the same dimension,
with orientations `o` and `o'`, and let `y` be a regular value of `f`. Then `y` has a neighbourhood
`V` such that every integrable top form `φ` on `N` supported in `V` satisfies
`∫_M f^*φ = deg_y(f) · ∫_N φ`, where `deg_y(f)` is the signed count of the fibre over `y`. -/
theorem exists_mem_nhds_integralTopForm_mpullback_eq_degreeAtRegularValue_mul [T2Space M]
    [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f)
    (hfp : IsProperMap f) {y : N} (hy : IsRegularValue I J f y) :
    ∃ V ∈ 𝓝 y, ∀ φ : RoughForm J N ℝ k, IntegrableTopForm φ →
      _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ V →
        integralTopForm o (mpullback I J f φ) =
          degreeAtRegularValue o o' f y * integralTopForm o' φ := by
  obtain ⟨V, hV, h⟩ := exists_mem_nhds_integrableTopForm_and_integralTopForm o o' hf hfp hy
  exact ⟨V, hV, fun φ hφ hφV ↦ (h φ hφ hφV).2⟩

/-- **Integrability of pullbacks of top forms supported in regular values.** Let `f : M → N` be a
proper `C¹` map from a Hausdorff boundaryless manifold to a Hausdorff manifold of the same
dimension, and let `φ` be an integrable top form on `N` every point of whose support is a regular
value of `f`. Then `f^*φ` is integrable. No orientation is needed. -/
theorem integrableTopForm_mpullback_of_isRegularValue_on_tsupport [T2Space M] [T2Space N]
    [BoundarylessManifold I M] (hdim : Module.finrank ℝ E = Module.finrank ℝ E') {f : M → N}
    (hf : ContMDiff I J 1 f) (hfp : IsProperMap f) {φ : RoughForm J N ℝ k}
    (hφ : IntegrableTopForm φ)
    (hreg : ∀ y ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ, IsRegularValue I J f y) :
    IntegrableTopForm (mpullback I J f φ) := by
  -- Each point of the support has a neighbourhood on which pullbacks are integrable.
  choose V hV hVφ using fun y : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ↦
    exists_mem_nhds_integrableTopForm (k := k) hdim hf hfp (hreg y y.property)
  obtain ⟨t, φ', hφ', hφ'V, hsum⟩ := hφ.exists_eq_sum_tsupport_subset V hV
  obtain ⟨b⟩ := nonempty_basis_of_integrableTopForm hdim hφ
  rw [hsum, mpullback_sum]
  exact IntegrableTopForm.sum b _ Finset.univ fun i _ ↦ hVφ i (φ' i) (hφ' i) (hφ'V i)

/-- **The integral formula for the degree.** Let `f : M → N` be a proper `C¹` map from a Hausdorff
boundaryless manifold to a Hausdorff manifold of the same dimension, with orientations
`o` and `o'`, and let `φ` be an integrable top form on `N` every point of whose support is a
regular value of `f` at which the degree is `c`. Then `∫_M f^*φ = c · ∫_N φ`. -/
theorem integralTopForm_mpullback_eq_mul_of_isRegularValue_and_const_degree_on_tsupport
    [T2Space M] [T2Space N] [BoundarylessManifold I M] (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : M → N} (hf : ContMDiff I J 1 f)
    (hfp : IsProperMap f) {φ : RoughForm J N ℝ k} (hφ : IntegrableTopForm φ) {c : ℤ}
    (hc : ∀ y ∈ _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ,
      IsRegularValue I J f y ∧ degreeAtRegularValue o o' f y = c) :
    integralTopForm o (mpullback I J f φ) = c * integralTopForm o' φ := by
  -- Each point of the support has a neighbourhood on which the local integral formula holds; a
  -- partition of unity subordinate to finitely many of them splits `φ` into localized pieces.
  choose V hV hVφ using fun y : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ ↦
    exists_mem_nhds_integrableTopForm_and_integralTopForm o o' hf hfp (hc y y.property).1
  obtain ⟨t, φ', hφ', hφ'V, hsum⟩ := hφ.exists_eq_sum_tsupport_subset V hV
  have hloc (i : t) := hVφ i (φ' i) (hφ' i) (hφ'V i)
  rw [hsum, mpullback_sum, integralTopForm_sum o _ Finset.univ fun i _ ↦ (hloc i).1,
    integralTopForm_sum o' _ Finset.univ fun i _ ↦ hφ' i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [(hloc i).2, (hc i (i : _root_.tsupport (α := E' [⋀^Fin k]→L[ℝ] ℝ) φ).property).2]

/-- **The integral formula for a map without critical values.** If every value of a proper `C¹`
map `f` from a Hausdorff boundaryless manifold to a preconnected Hausdorff manifold of the same
dimension is regular, as for a local diffeomorphism, then `∫_M f^*φ = deg_y(f) · ∫_N φ` for every
integrable top form `φ` and every value `y`. -/
theorem integralTopForm_mpullback_eq_degreeAtRegularValue_mul_of_forall_isRegularValue
    [T2Space M] [T2Space N] [PreconnectedSpace N] [BoundarylessManifold I M]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : ContMDiff I J 1 f) (hfp : IsProperMap f) (hreg : ∀ y, IsRegularValue I J f y) (y : N)
    {φ : RoughForm J N ℝ k} (hφ : IntegrableTopForm φ) :
    integralTopForm o (mpullback I J f φ) = degreeAtRegularValue o o' f y * integralTopForm o' φ :=
  integralTopForm_mpullback_eq_mul_of_isRegularValue_and_const_degree_on_tsupport o o' hf hfp hφ
    fun y' _ ↦ ⟨hreg y', degreeAtRegularValue_eq_of_forall_isRegularValue o o' hf hfp hreg y' y⟩

/-- **The integral formula for an orientation-preserving local diffeomorphism.** Let `f : M → N`
be a proper `C¹` local diffeomorphism from a Hausdorff boundaryless manifold to a preconnected
Hausdorff manifold, preserving the orientations `o` and `o'` at every point. Then
`∫_M f^*φ = |f⁻¹(p)| · ∫_N φ` for every integrable top form `φ` and every point `p` of `N`: the
fibres all have the same finite number of points, the degree of `f`. -/
theorem _root_.IsLocalDiffeomorph.integralTopForm_mpullback_eq_ncard_mul [T2Space M] [T2Space N]
    [PreconnectedSpace N] [BoundarylessManifold I M] {n : WithTop ℕ∞}
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) {f : M → N}
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) (hfp : IsProperMap f)
    (hor : ∀ x, IsOrientationPreservingAt o o' f x) (p : N) {φ : RoughForm J N ℝ k}
    (hφ : IntegrableTopForm φ) :
    integralTopForm o (mpullback I J f φ) = (f ⁻¹' {p}).ncard * integralTopForm o' φ := by
  rw [integralTopForm_mpullback_eq_degreeAtRegularValue_mul_of_forall_isRegularValue o o'
    (hf.contMDiff.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)) hfp (hf.isRegularValue hn) p hφ,
    degreeAtRegularValue_eq_ncard fun x _ ↦ hor x,
    Int.cast_natCast]

end TauCeti
