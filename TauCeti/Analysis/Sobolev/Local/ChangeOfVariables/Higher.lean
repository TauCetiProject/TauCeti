/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Reflection
public import TauCeti.Analysis.Sobolev.Local.Wkp
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.TangentCone.Chart
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Locality

/-!
# Change of variables of every order in local Sobolev classes

Let `U` and `V` be open subsets of `ℂ`, let `1 ≤ p < ∞` and `k ≥ 1`, and let `Φ` be `Cᵏ` on `U`
with invertible derivative there, mapping `U` into `V`. For maps into a finite-dimensional real
normed space, precomposition with `Φ` maps `TauCeti.MemWkpLoc p V k` into
`TauCeti.MemWkpLoc p U k` (`TauCeti.MemWkpLoc.comp_contDiffOn`). For an open partial
homeomorphism that is `Cᵏ` in both directions this is an equivalence between the classes on its
target and on its source (`TauCeti.memWkpLoc_comp_openPartialHomeomorph_iff`).

The same holds for the half-disc classes `MemWkpLoc p (U ∩ {0 ≤ im}) k`, whose `Lᵖ` bounds reach
the real axis, when `Φ` is `Cᵏ` with invertible derivative on the open set `U` and maps
`U ∩ {0 ≤ im}` into `V ∩ {0 ≤ im}` (`TauCeti.MemWkpLoc.comp_contDiffOn_halfPlane`). A
diffeomorphism between half-discs preserving the real axis has this form once it is extended to a
`Cᵏ` map with invertible derivative on an open neighbourhood of the closed half-disc.

## The argument

The class is checked locally (`TauCeti.memWkpLoc_iff_locally`), and by the inverse function
theorem `Φ` is injective near each point of `U`. Where `Φ` is injective, on a relatively compact
open `W ⋐ U` the derivatives of `Φ` of orders `1` through `k` are bounded and its Jacobian is
bounded below on `closure W` (`TauCeti.Wkp.IsChangeOfVariables.exists_of_isCompact_closure`), so
precomposition with `Φ` is the bounded operator `TauCeti.Wkp.compL` from `W^{k,p}(V')` to
`W^{k,p}(W)`, for an open `V' ⋐ V` containing `Φ (closure W)`. For real functions, the comparison
`TauCeti.memWkpLoc_iff_forall_wkp` of the local class with the spaces `W^{k,p}(W)` then gives the
invariance; vector-valued maps are handled in coordinates (`Module.Basis.memWkpLoc_iff`).

For half-discs the property is checked locally (`TauCeti.memWkpLoc_iff_locally`). Near a point
whose image lies on the real axis, the higher-order reflection
`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball` extends `u` to a disc centred on
the axis (`TauCeti.MemWkpLoc.exists_ball_extension`); the open case applies to the extension,
which agrees with `u` on the closed upper half-plane, where `Φ` takes its values.

## Main declarations

* `TauCeti.MemWkpLoc.comp_contDiffOn`: invariance under `Cᵏ` changes of variables.
* `TauCeti.memWkpLoc_comp_openPartialHomeomorph_iff`: invariance under `Cᵏ` diffeomorphisms.
* `TauCeti.MemWkpLoc.comp_contDiffOn_halfPlane`,
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

/-- The real case of `TauCeti.MemWkpLoc.comp_contDiffOn` for an injective `Φ`. -/
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
an open set `U ⊆ ℂ` with invertible derivative there, mapping `U` into an open set `V`. For a map
`u` into a finite-dimensional space, `u ∈ W^{k,p}_loc(V)` implies `u ∘ Φ ∈ W^{k,p}_loc(U)`. -/
theorem MemWkpLoc.comp_contDiffOn [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    {U V : Opens ℂ} {u : ℂ → F} (hu : MemWkpLoc p V k u) (hΦ : ContDiffOn ℝ k Φ U)
    (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0)
    (hmaps : MapsTo Φ U V) : MemWkpLoc p U k (fun z => u (Φ z)) := by
  have b := Module.finBasis ℝ F
  rw [b.memWkpLoc_iff] at hu ⊢
  refine fun i => memWkpLoc_iff_locally.2 fun z hz => ?_
  -- By the inverse function theorem `Φ` is injective on an open neighbourhood of `z` in `U`.
  obtain ⟨Θ, hΘ, hzΘ, hΘU, -⟩ := ContDiffOn.exists_openPartialHomeomorph hΦ U.isOpen hz
    (by exact_mod_cast hk)
    (e := (LinearMap.equivOfDetNeZero _ (hdet z hz)).toContinuousLinearEquiv) rfl
  refine ⟨Θ.source, mem_nhdsWithin_of_mem_nhds (Θ.open_source.mem_nhds hzΘ), ?_⟩
  exact (hu i).comp_contDiffOn_injOn_real (U := ⟨_, Θ.open_source⟩) hp hk (hΦ.mono hΘU)
    (hΘ ▸ Θ.injOn) (fun y hy => hdet y (hΘU hy)) fun y hy => hmaps (hΘU hy)

/-- **Invariance under `Cᵏ` diffeomorphisms.** For an open partial homeomorphism `e` of `ℂ` that
is `Cᵏ` in both directions, `k ≥ 1`, and `1 ≤ p < ∞`, a map `u` into a finite-dimensional space
satisfies `u ∘ e ∈ W^{k,p}_loc(e.source)` exactly when `u ∈ W^{k,p}_loc(e.target)`. -/
theorem memWkpLoc_comp_openPartialHomeomorph_iff [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ContDiffOn ℝ k e e.source)
    (he' : ContDiffOn ℝ k e.symm e.target) {u : ℂ → F} :
    MemWkpLoc p e.source k (fun z => u (e z)) ↔ MemWkpLoc p e.target k u := by
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk
  have hdet (f : OpenPartialHomeomorph ℂ ℂ) (hf : ContDiffOn ℝ k f f.source)
      (hf' : ContDiffOn ℝ k f.symm f.target) (y : ℂ) (hy : y ∈ f.source) :
      (fderiv ℝ f y).det ≠ 0 :=
    f.det_fderiv_ne_zero hy ((hf.differentiableOn hk0).differentiableAt
      (f.open_source.mem_nhds hy))
      ((hf'.differentiableOn hk0).differentiableAt (f.open_target.mem_nhds (f.map_source hy)))
  refine ⟨fun h => ?_, fun h => MemWkpLoc.comp_contDiffOn (U := ⟨_, e.open_source⟩)
    (V := ⟨_, e.open_target⟩) hp hk h he
    (hdet e he he')
    e.mapsTo⟩
  have h' := MemWkpLoc.comp_contDiffOn (U := ⟨_, e.open_target⟩) (V := ⟨_, e.open_source⟩) hp hk h
    he' (hdet e.symm he' he)
    e.symm.mapsTo
  exact h'.congr_ae (ae_restrict_of_forall_mem e.open_target.measurableSet
    fun y hy => by simp only [e.right_inv hy])

end Open

/-! ### Half-discs -/

section HalfPlane

variable [FiniteDimensional ℝ F]

/-- **Change of variables on half-discs.** Let `1 ≤ p < ∞` and `k ≥ 1`, and let `Φ` be `Cᵏ` on an
open set `U ⊆ ℂ` with invertible derivative there, mapping `U ∩ {0 ≤ im}` into `V ∩ {0 ≤ im}`
for an open `V`. For a map `u` into a finite-dimensional space, `u` in the half-disc class
`W^{k,p}_loc(V ∩ {0 ≤ im})` implies `u ∘ Φ ∈ W^{k,p}_loc(U ∩ {0 ≤ im})`. A diffeomorphism between
half-discs that preserves the real axis satisfies the mapping hypothesis; the regularity and
Jacobian hypotheses ask for an extension of it to an open set `U` containing the half-disc. -/
theorem MemWkpLoc.comp_contDiffOn_halfPlane [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hk : 1 ≤ k)
    {U V : Opens ℂ} {u : ℂ → F} (hu : MemWkpLoc p ((V : Set ℂ) ∩ {z | 0 ≤ z.im}) k u)
    (hΦ : ContDiffOn ℝ k Φ U) (hdet : ∀ z ∈ (U : Set ℂ), (fderiv ℝ Φ z).det ≠ 0)
    (hmaps : MapsTo Φ ((U : Set ℂ) ∩ {z | 0 ≤ z.im}) ((V : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    MemWkpLoc p ((U : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => u (Φ z)) := by
  refine memWkpLoc_iff_locally.2 fun z hz => ?_
  obtain ⟨hzV, hz0⟩ := hmaps hz
  obtain ⟨r, hr, v, hv, hvu⟩ := hu.exists_ball_extension Fact.out V.isOpen hzV hz0
  set O : Opens ℂ := ⟨U ∩ Φ ⁻¹' ball (Φ z) r, hΦ.continuousOn.isOpen_inter_preimage U.isOpen
    isOpen_ball⟩
  have hvO := hv.comp_contDiffOn (U := O) (V := ⟨_, isOpen_ball⟩) hp hk
    (hΦ.mono inter_subset_left) (fun y hy => hdet y hy.1) fun y hy => hy.2
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
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk
  have hdet (f : OpenPartialHomeomorph ℂ ℂ) (hf : ContDiffOn ℝ k f f.source)
      (hf' : ContDiffOn ℝ k f.symm f.target) (y : ℂ) (hy : y ∈ f.source) :
      (fderiv ℝ f y).det ≠ 0 :=
    f.det_fderiv_ne_zero hy ((hf.differentiableOn hk0).differentiableAt
      (f.open_source.mem_nhds hy))
      ((hf'.differentiableOn hk0).differentiableAt (f.open_target.mem_nhds (f.map_source hy)))
  refine ⟨fun h => ?_, fun h => MemWkpLoc.comp_contDiffOn_halfPlane
    (U := ⟨_, e.open_source⟩) (V := ⟨_, e.open_target⟩) hp hk h he
    (hdet e he he')
    fun z hz => ⟨e.map_source hz.1, hmaps z hz.1 hz.2⟩⟩
  have h' := MemWkpLoc.comp_contDiffOn_halfPlane (U := ⟨_, e.open_target⟩)
    (V := ⟨_, e.open_source⟩) hp hk h he'
    (hdet e.symm he' he)
    fun z hz => ⟨e.map_target hz.1, hmaps' z hz.1 hz.2⟩
  exact h'.congr_ae (ae_restrict_of_forall_mem (e.open_target.measurableSet.inter
    (measurableSet_le measurable_const Complex.measurable_im)) fun y hy => by
      simp only [e.right_inv hy.1])

end HalfPlane

end TauCeti
