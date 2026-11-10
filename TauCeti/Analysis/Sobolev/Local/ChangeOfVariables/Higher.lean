/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Reflection
public import TauCeti.Analysis.Sobolev.Local.Wkp
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Locality

/-!
# Change of variables of every order in local Sobolev classes

Let `U` and `V` be open subsets of `ℂ`, let `1 ≤ p < ∞` and `k ≥ 1`, and let `Φ` be `Cᵏ` on `U`,
injective with invertible derivative there, and mapping `U` into `V`. For maps into a
finite-dimensional real normed space, precomposition with `Φ` maps `TauCeti.MemWkpLoc p V k` into
`TauCeti.MemWkpLoc p U k` (`TauCeti.MemWkpLoc.comp_contDiffOn_injOn`). For an open partial
homeomorphism that is `Cᵏ` in both directions this is an equivalence between the classes on its
target and on its source (`TauCeti.memWkpLoc_comp_openPartialHomeomorph_iff`).

The same holds for the half-disc classes `MemWkpLoc p (U ∩ {0 ≤ im}) k`, whose `Lᵖ` bounds reach
the real axis, when `Φ` is `Cᵏ` with invertible derivative on the open set `U` and maps
`U ∩ {0 ≤ im}` into `V ∩ {0 ≤ im}` (`TauCeti.MemWkpLoc.comp_contDiffOn_injOn_halfPlane`). A
diffeomorphism between half-discs preserving the real axis has this form.

## The argument

On a relatively compact open `W ⋐ U` the derivatives of `Φ` of orders `1` through `k` are bounded
and its Jacobian is bounded below on `closure W`
(`TauCeti.Wkp.IsChangeOfVariables.exists_of_isCompact_closure`), so precomposition with `Φ` is the
bounded operator `TauCeti.Wkp.compL` from `W^{k,p}(V')` to `W^{k,p}(W)`, for an open `V' ⋐ V`
containing `Φ (closure W)`. This gives the local bound
(`TauCeti.Wkp.exists_comp_norm_le_of_isCompact_closure`). For real functions, the comparison
`TauCeti.memWkpLoc_iff_forall_wkp` of the local class with the spaces `W^{k,p}(W)` then gives the
invariance; vector-valued maps are handled in coordinates (`Module.Basis.memWkpLoc_iff`).

For half-discs the property is checked locally (`TauCeti.memWkpLoc_iff_locally`). Near a point
whose image lies on the real axis, the higher-order reflection
`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball` extends `u` to a disc centred on
the axis; the open case applies to the extension, which agrees with `u` on the closed upper
half-plane, where `Φ` takes its values.

## Main declarations

* `TauCeti.Wkp.exists_comp_norm_le_of_isCompact_closure`: the local bound on `W ⋐ U`.
* `TauCeti.MemWkpLoc.comp_contDiffOn_injOn`: invariance under `Cᵏ` changes of variables.
* `TauCeti.memWkpLoc_comp_openPartialHomeomorph_iff`: invariance under `Cᵏ` diffeomorphisms.
* `TauCeti.MemWkpLoc.comp_contDiffOn_injOn_halfPlane`,
  `TauCeti.memWkpLoc_comp_openPartialHomeomorph_halfPlane_iff`: the half-disc versions.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 3.41 (invariance under
  `Cᵏ` diffeomorphisms).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} {k : ℕ} {Φ : ℂ → ℂ}

/-! ### Open planar domains -/

section Open

/-- **The local bound.** Let `Φ` be `Cᵏ` with `k ≥ 1` on an open `U`, injective with invertible
derivative there. For an open `W` whose closure is compact and contained in `U`, and an open `V'`
into which `Φ` maps `W`, there are a bound `L` for the derivatives of `Φ` of orders `1` through
`k` and a positive lower bound `c` for its Jacobian on `closure W` such that every
`v ∈ W^{k,p}(V')` composed with `Φ` is represented by an element of `W^{k,p}(W)` of norm at most
`TauCeti.Wkp.compLBound p k L c * ‖v‖`. -/
theorem Wkp.exists_comp_norm_le_of_isCompact_closure [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    {U W V' : Opens ℂ} (hΦ : ContDiffOn ℝ k Φ U) (hinj : InjOn Φ U)
    (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0)
    (hWc : IsCompact (closure (W : Set ℂ))) (hWU : closure (W : Set ℂ) ⊆ U)
    (hWV' : MapsTo Φ W V') :
    ∃ L c : ℝ, 0 < c ∧ ∀ v : Wkp volume V' p k, ∃ w : Wkp volume W p k,
      (Wkp.value k w : ℂ → ℝ) =ᵐ[volume.restrict W] (fun z => Wkp.value k v (Φ z)) ∧
      ‖w‖ ≤ Wkp.compLBound p k L c * ‖v‖ := by
  obtain ⟨L, c, h⟩ := Wkp.IsChangeOfVariables.exists_of_isCompact_closure U.isOpen hk hΦ
    (hinj.mono (subset_closure.trans hWU)) (fun z hz => hdet z (hWU hz)) hWc hWU hWV'
  exact ⟨L, c, h.pos, fun v => ⟨Wkp.compL h hp v, Wkp.value_compL_ae h hp v,
    Wkp.norm_compL_le h hp v⟩⟩

/-- The real case of `TauCeti.MemWkpLoc.comp_contDiffOn_injOn`. -/
private theorem MemWkpLoc.comp_contDiffOn_injOn_real [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    {U V : Opens ℂ} {u : ℂ → ℝ} (hu : MemWkpLoc p V k u) (hΦ : ContDiffOn ℝ k Φ U)
    (hinj : InjOn Φ U) (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0)
    (hmaps : MapsTo Φ U V) : MemWkpLoc p U k (fun z => u (Φ z)) := by
  refine memWkpLoc_of_forall_wkp fun W hWc hWU => ?_
  have hK : IsCompact (Φ '' closure (W : Set ℂ)) :=
    hWc.image_of_continuousOn (hΦ.continuousOn.mono hWU)
  obtain ⟨V', hV'o, hKV', hV'V, hV'c⟩ := exists_open_between_and_isCompact_closure hK V.isOpen
    (by rintro _ ⟨z, hz, rfl⟩; exact hmaps (hWU hz))
  obtain ⟨L, c, h⟩ := Wkp.IsChangeOfVariables.exists_of_isCompact_closure (V := ⟨V', hV'o⟩)
    U.isOpen hk hΦ (hinj.mono (subset_closure.trans hWU)) (fun z hz => hdet z (hWU hz)) hWc hWU
    fun z hz => hKV' ⟨z, subset_closure hz, rfl⟩
  obtain ⟨v, hv⟩ := hu.exists_wkp (W := ⟨V', hV'o⟩) hV'c hV'V
  exact ⟨Wkp.compL h hp v, (Wkp.value_compL_ae h hp v).trans (h.ae_comp hv)⟩

variable [FiniteDimensional ℝ F]

/-- **Change of variables of every order.** Let `1 ≤ p < ∞` and `k ≥ 1`, and let `Φ` be `Cᵏ` on
an open set `U ⊆ ℂ`, injective with invertible derivative there, and mapping `U` into an open set
`V`. For a map `u` into a finite-dimensional space, `u ∈ W^{k,p}_loc(V)` implies
`u ∘ Φ ∈ W^{k,p}_loc(U)`. -/
theorem MemWkpLoc.comp_contDiffOn_injOn [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    {U V : Opens ℂ} {u : ℂ → F} (hu : MemWkpLoc p V k u) (hΦ : ContDiffOn ℝ k Φ U)
    (hinj : InjOn Φ U) (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0)
    (hmaps : MapsTo Φ U V) : MemWkpLoc p U k (fun z => u (Φ z)) := by
  have b := Module.finBasis ℝ F
  rw [b.memWkpLoc_iff] at hu ⊢
  exact fun i => (hu i).comp_contDiffOn_injOn_real hp hk hΦ hinj hdet hmaps

/-- The derivative of a map that is differentiable in both directions of an open partial
homeomorphism is invertible on its source. -/
private theorem det_fderiv_ne_zero_of_openPartialHomeomorph (e : OpenPartialHomeomorph ℂ ℂ)
    {z : ℂ} (hz : z ∈ e.source) (he : DifferentiableAt ℝ e z)
    (he' : DifferentiableAt ℝ e.symm (e z)) : (fderiv ℝ e z).det ≠ 0 := by
  have hcomp : (fderiv ℝ e.symm (e z)).comp (fderiv ℝ e z) = ContinuousLinearMap.id ℝ ℂ := by
    have hl : (e.symm ∘ e) =ᶠ[𝓝 z] id := e.eventually_left_inverse hz
    rw [← fderiv_comp z he' he, hl.fderiv_eq, fderiv_id]
  intro h0
  have := congrArg ContinuousLinearMap.det hcomp
  simp [ContinuousLinearMap.det, LinearMap.det_comp, h0] at this

/-- The derivative of an open partial homeomorphism that is `Cᵏ` in both directions, `k ≥ 1`, is
invertible on its source. -/
private theorem det_fderiv_ne_zero_of_contDiffOn (e : OpenPartialHomeomorph ℂ ℂ) (hk : 1 ≤ k)
    (he : ContDiffOn ℝ k e e.source) (he' : ContDiffOn ℝ k e.symm e.target) :
    ∀ z ∈ e.source, (fderiv ℝ e z).det ≠ 0 := fun z hz =>
  det_fderiv_ne_zero_of_openPartialHomeomorph e hz
    ((he.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt (by positivity))
    ((he'.contDiffAt (e.open_target.mem_nhds (e.map_source hz))).differentiableAt
      (by positivity))

/-- **Invariance under `Cᵏ` diffeomorphisms.** For an open partial homeomorphism `e` of `ℂ` that
is `Cᵏ` in both directions, `k ≥ 1`, and `1 ≤ p < ∞`, a map `u` into a finite-dimensional space
satisfies `u ∘ e ∈ W^{k,p}_loc(e.source)` exactly when `u ∈ W^{k,p}_loc(e.target)`. -/
theorem memWkpLoc_comp_openPartialHomeomorph_iff [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ContDiffOn ℝ k e e.source)
    (he' : ContDiffOn ℝ k e.symm e.target) {u : ℂ → F} :
    MemWkpLoc p e.source k (fun z => u (e z)) ↔ MemWkpLoc p e.target k u := by
  refine ⟨fun h => ?_, fun h => MemWkpLoc.comp_contDiffOn_injOn (U := ⟨_, e.open_source⟩)
    (V := ⟨_, e.open_target⟩) hp hk h he e.injOn (det_fderiv_ne_zero_of_contDiffOn e hk he he')
    e.mapsTo⟩
  have h' := MemWkpLoc.comp_contDiffOn_injOn (U := ⟨_, e.open_target⟩) (V := ⟨_, e.open_source⟩)
    hp hk h he' e.symm.injOn (det_fderiv_ne_zero_of_contDiffOn e.symm hk he' he) e.symm.mapsTo
  exact h'.congr_ae (ae_restrict_of_forall_mem e.open_target.measurableSet
    fun y hy => by simp only [e.right_inv hy])

end Open

/-! ### Half-discs -/

section HalfPlane

/-- Near a point `w` of the closed upper half-plane in an open set `V`, a member of the half-disc
class on `V ∩ {0 ≤ im}` agrees on the closed upper half-plane with a member of the class on a
disc about `w`: the higher-order reflection when `w` is real, and the map itself otherwise. -/
private theorem MemWkpLoc.exists_ball_extension (hp : 1 ≤ p) {V : Set ℂ} (hV : IsOpen V)
    {u : ℂ → F} (hu : MemWkpLoc p (V ∩ {z | 0 ≤ z.im}) k u) {w : ℂ} (hw : w ∈ V)
    (hw0 : 0 ≤ w.im) : ∃ r > 0, ∃ v : ℂ → F, MemWkpLoc p (ball w r) k v ∧
      ∀ y ∈ ball w r, 0 ≤ y.im → v y = u y := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV w hw
  rcases hw0.lt_or_eq with hw0 | hw0
  · refine ⟨min r w.im, lt_min hr hw0, u, hu.mono fun y hy => ⟨hrV (ball_subset_ball
      (min_le_left _ _) hy), ?_⟩, fun _ _ _ => rfl⟩
    have := (Complex.abs_im_le_norm (y - w)).trans_lt ((mem_ball_iff_norm.1 hy).trans_le
      (min_le_right _ _))
    rw [Complex.sub_im, abs_lt] at this
    change 0 ≤ y.im
    linarith [this.1]
  · have hwx : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hw0])
    refine ⟨r, hr, TauCeti.planarReflection (higherReflectionCoeff k) u, ?_, fun y _ hy =>
      planarReflection_of_nonneg _ u hy⟩
    rw [← hwx]
    exact MemWkpLoc.planarReflection_higherReflectionCoeff_ball hp w.re r
      (hu.mono (inter_subset_inter_left _ (by rw [hwx]; exact hrV)))

variable [FiniteDimensional ℝ F]

/-- **Change of variables on half-discs.** Let `1 ≤ p < ∞` and `k ≥ 1`, and let `Φ` be `Cᵏ` on an
open set `U ⊆ ℂ`, injective with invertible derivative there, and mapping `U ∩ {0 ≤ im}` into
`V ∩ {0 ≤ im}` for an open `V`. For a map `u` into a finite-dimensional space, `u` in the half-disc
class `W^{k,p}_loc(V ∩ {0 ≤ im})` implies `u ∘ Φ ∈ W^{k,p}_loc(U ∩ {0 ≤ im})`. Diffeomorphisms
between half-discs that preserve the real axis map the closed upper parts into each other. -/
theorem MemWkpLoc.comp_contDiffOn_injOn_halfPlane [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    {U V : Opens ℂ} {u : ℂ → F} (hu : MemWkpLoc p ((V : Set ℂ) ∩ {z | 0 ≤ z.im}) k u)
    (hΦ : ContDiffOn ℝ k Φ U) (hinj : InjOn Φ U) (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0)
    (hmaps : MapsTo Φ ((U : Set ℂ) ∩ {z | 0 ≤ z.im}) ((V : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    MemWkpLoc p ((U : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => u (Φ z)) := by
  refine memWkpLoc_iff_locally.2 fun z hz => ?_
  obtain ⟨hzV, hz0⟩ := hmaps hz
  obtain ⟨r, hr, v, hv, hvu⟩ := hu.exists_ball_extension Fact.out V.isOpen hzV hz0
  set O : Opens ℂ := ⟨U ∩ Φ ⁻¹' ball (Φ z) r, hΦ.continuousOn.isOpen_inter_preimage U.isOpen
    isOpen_ball⟩
  have hvO := hv.comp_contDiffOn_injOn (U := O) (V := ⟨_, isOpen_ball⟩) hp hk
    (hΦ.mono inter_subset_left) (hinj.mono inter_subset_left)
    (fun y hy => hdet y hy.1) fun y hy => hy.2
  refine ⟨((U : Set ℂ) ∩ {z | 0 ≤ z.im}) ∩ O, inter_mem_nhdsWithin _ (O.isOpen.mem_nhds ?_), ?_⟩
  · exact ⟨hz.1, by simpa using hr⟩
  · refine (hvO.mono inter_subset_right).congr_ae (ae_restrict_of_forall_mem
      ((U.isOpen.measurableSet.inter (measurableSet_le measurable_const
        Complex.measurable_im)).inter O.isOpen.measurableSet) fun y hy => ?_)
    exact hvu _ hy.2.2 (hmaps hy.1).2

/-- **Invariance of the half-disc classes under `Cᵏ` diffeomorphisms.** Let `e` be an open partial
homeomorphism of `ℂ` that is `Cᵏ` in both directions, `k ≥ 1`, mapping `e.source ∩ {0 ≤ im}` into
the closed upper half-plane, with inverse mapping `e.target ∩ {0 ≤ im}` into it. For
`1 ≤ p < ∞` and a map `u` into a finite-dimensional space,
`u ∘ e ∈ W^{k,p}_loc(e.source ∩ {0 ≤ im})` exactly when `u ∈ W^{k,p}_loc(e.target ∩ {0 ≤ im})`. -/
theorem memWkpLoc_comp_openPartialHomeomorph_halfPlane_iff [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hk : 1 ≤ k) (e : OpenPartialHomeomorph ℂ ℂ) (he : ContDiffOn ℝ k e e.source)
    (he' : ContDiffOn ℝ k e.symm e.target)
    (hmaps : ∀ z ∈ e.source, 0 ≤ z.im → 0 ≤ (e z).im)
    (hmaps' : ∀ z ∈ e.target, 0 ≤ z.im → 0 ≤ (e.symm z).im) {u : ℂ → F} :
    MemWkpLoc p (e.source ∩ {z | 0 ≤ z.im}) k (fun z => u (e z)) ↔
      MemWkpLoc p (e.target ∩ {z | 0 ≤ z.im}) k u := by
  refine ⟨fun h => ?_, fun h => MemWkpLoc.comp_contDiffOn_injOn_halfPlane
    (U := ⟨_, e.open_source⟩) (V := ⟨_, e.open_target⟩) hp hk h he e.injOn
    (det_fderiv_ne_zero_of_contDiffOn e hk he he') fun z hz =>
      ⟨e.map_source hz.1, hmaps z hz.1 hz.2⟩⟩
  have h' := MemWkpLoc.comp_contDiffOn_injOn_halfPlane (U := ⟨_, e.open_target⟩)
    (V := ⟨_, e.open_source⟩) hp hk h he' e.symm.injOn
    (det_fderiv_ne_zero_of_contDiffOn e.symm hk he' he)
    fun z hz => ⟨e.map_target hz.1, hmaps' z hz.1 hz.2⟩
  exact h'.congr_ae (ae_restrict_of_forall_mem (e.open_target.measurableSet.inter
    (measurableSet_le measurable_const Complex.measurable_im)) fun y hy => by
      simp only [e.right_inv hy.1])

end HalfPlane

end TauCeti
