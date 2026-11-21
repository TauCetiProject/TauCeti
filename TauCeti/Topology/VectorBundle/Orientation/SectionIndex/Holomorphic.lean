/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.LocalIndex
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree
import TauCeti.Analysis.Analytic.Order

/-!
# The local index of a section at a holomorphic zero is its order

Let `s` be a continuous section of an oriented real plane bundle `E → M` with fibre `ℂ`, over an
oriented surface `M` charted on `ℂ`, and `z` a zero of `s`. Read the section in a linear
trivialization `e` and a chart `φ` as `f y = (e (s (φ⁻¹ y))).2`. If near `z` the trivialization
`e` reads the bundle orientation as an orientation `ω` of `ℂ`, the translated chart
`y ↦ φ y - φ z` carries the local orientation of `M` at `z` to the local orientation selected by
`ω`, as in the transverse case
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`), and `f` is complex
analytic at `φ z`, then the local index of `s` at `z`
(`TauCeti.VectorBundleOrientation.sectionIndex`) is the order of vanishing of `f` at `φ z`
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`). This holds at every zero;
both sides vanish at a zero which is not isolated. At an isolated zero the order is a positive
integer (`TauCeti.VectorBundleOrientation.sectionIndex_pos_of_analyticAt`).

Over a compact surface, if a section has finitely many zeros and is complex analytic in such
coordinates at each of them, the Euler number `⟨e(E), [M]⟩` is the sum of the orders of the zeros,
hence nonnegative
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`,
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_nonneg_of_analyticAt`).

The local statement composes three facts. The local index of `s` is the local index of its fibre
coordinate (`TauCeti.VectorBundleOrientation.sectionIndex_eq_localIndex_fiberCoord`). On the
source of `φ`, the orientation pulled back from `ℂ` along `φ` agrees at `z` with the one restricted
from `M` (`TauCeti.HomologicalOrientation.comap_apply_eq_of_localHomologyMap_chart_sub`), and the
local index only sees the orientations at the point and its image
(`TauCeti.HomologicalOrientation.localIndex_eq_localIndex_of_apply_eq`). Finally, the local index
of a holomorphic map is its order of vanishing
(`TauCeti.HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub`).

On the trivial line bundle over `ℂ`, the section `z ↦ z ^ m` has local index `m` at `0`
(`TauCeti.VectorBundleOrientation.sectionIndex_trivial_pow`), while `z ↦ conj z`, which is not
holomorphic, has local index `-1` (`TauCeti.VectorBundleOrientation.sectionIndex_trivial_conj`).

## Main results

* `TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`: at a zero where the section
  is complex analytic in oriented coordinates, the local index is the order of vanishing.
* `TauCeti.VectorBundleOrientation.sectionIndex_pos_of_analyticAt`: at an isolated such zero it is
  positive.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`: the
  Euler number is the sum of the orders of the zeros of a section with finitely many zeros, each
  complex analytic in oriented coordinates.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_nonneg_of_analyticAt`: so it is
  nonnegative.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52 (2012), Appendix C.1 (the zeros of a section in the kernel of a real
  Cauchy-Riemann operator on a line bundle, and their count by the first Chern number).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §3.3 (the local
  mapping theorem).
-/

public section

noncomputable section

open Bundle CategoryTheory Filter Module Set Topology

namespace TauCeti

namespace VectorBundleOrientation

section Holomorphic

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] {E : M → Type}
  [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle ℂ E] [VectorBundle ℝ ℂ E]
  (o : VectorBundleOrientation ℂ E (Fin (1 + 1))) (hF : finrank ℝ ℂ = 1 + 1)
  (oM : HomologicalOrientation M ℂ (1 + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' ℂ x (s x))

section Local

variable (e : Trivialization ℂ (π ℂ E)) [e.IsLinear ℝ]

/-- **The local index of a section at a holomorphic zero is its order.** Let `e` be a linear
trivialization of a real plane bundle `E` with fibre `ℂ` and `φ` a chart of `M` with values in
`ℂ`, both defined at `z`. Suppose that near `z` the trivialization `e` reads the orientation of
every fibre as the orientation `ω` of `ℂ`, and that `φ`, followed by the translation taking `φ z`
to the origin, carries the local orientation `oM z` to the local orientation of `ℂ` selected by
`ω`. If the section, read in these coordinates as `y ↦ (e (s (φ⁻¹ y))).2`, is complex analytic at
`φ z`, then the local index of `s` at `z` is the order of vanishing of this coordinate expression
at `φ z`. Both sides are `0` when `s z ≠ 0` and when `z` is a zero which is not isolated. -/
theorem sectionIndex_eq_analyticOrderNatAt (φ : OpenPartialHomeomorph M ℂ) {z : M}
    (hze : z ∈ e.baseSet) (hzφ : z ∈ φ.source) {ω : Orientation ℝ ℂ (Fin (1 + 1))}
    (ho : ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ e.baseSet, e.mapOrientation (Fin (1 + 1)) hx (o x) = ω)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, ℂ)) (S := {⟨z, hzφ⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.property hzφ (sub_eq_zero.1 hx))) (1 + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ⟩
          (1 + 1)).symm (oM z)).val =
      (ω.localOrientation hF).val)
    (hA : AnalyticAt ℂ (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) (φ z)) :
    o.sectionIndex hF oM hs z =
      analyticOrderNatAt (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) (φ z) := by
  set f : ℂ → ℂ := fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2 with hf
  have hfφ : ∀ x ∈ φ.source, f (φ x) = (e (TotalSpace.mk' ℂ x (s x))).2 := fun x hx ↦ by
    simp only [hf]
    rw [φ.left_inv hx]
  by_cases hsz : s z = 0
  swap
  · -- Away from the zeros both sides vanish.
    have hf0 : f (φ z) ≠ 0 := by
      rw [hfφ z hzφ]
      exact (e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' ℂ z (s z)) hze).2 hsz
    rw [o.sectionIndex_of_ne_zero hF oM hs hsz, analyticOrderNatAt,
      analyticOrderAt_eq_zero.2 (Or.inr hf0)]
    rfl
  -- The common domain `U` of `e` and `φ`, the orientation `oF` of `ℂ` selected by `ω`, and the
  -- restriction of `φ` to `U`.
  let U : TopologicalSpace.Opens M := ⟨φ.source ∩ e.baseSet, φ.open_source.inter e.open_baseSet⟩
  have hz : z ∈ U := ⟨hzφ, hze⟩
  have hUe : (U : Set M) ⊆ e.baseSet := fun _ hx ↦ hx.2
  have hUφ : (U : Set M) ⊆ φ.source := fun _ hx ↦ hx.1
  have hf0 : f (φ z) = 0 := (hfφ z hzφ).trans
    ((fiberCoord_apply hs e hUe ⟨z, hz⟩).symm.trans ((fiberCoord_eq_zero_iff hs e hUe _).2 hsz))
  let oF : HomologicalOrientation ℂ ℂ (1 + 1) :=
    .ofSimplyConnectedSpace 0 (ω.localOrientation hF)
  have hoF : oF 0 = ω.localOrientation hF :=
    HomologicalOrientation.ofSimplyConnectedSpace_apply_self _ _
  let W : TopologicalSpace.Opens M := ⟨φ.source, φ.open_source⟩
  have hj : IsOpenEmbedding (fun x : U ↦ φ x) := φ.isOpenEmbedding_restrict.comp
    ((IsOpenEmbedding.of_comp_iff (fun x : U ↦ (⟨x.val, hUφ x.property⟩ : W)) W.isOpenEmbedding').1
      U.isOpenEmbedding')
  -- The orientation of `U` pulled back from `oF` along `φ` agrees at `z` with the one restricted
  -- from `oM`.
  have horient := HomologicalOrientation.comap_apply_eq_of_localHomologyMap_chart_sub oF hF oM φ U
    hz hUφ (hoF ▸ hφ) hj
  rw [o.sectionIndex_eq_localIndex_fiberCoord hF oM hs e U hz hsz hUe ho oF hoF,
    HomologicalOrientation.localIndex_eq_localIndex_of_apply_eq _ oF _ horient.symm
      (p' := oF.comap IsOpenEmbedding.id) (by rw [HomologicalOrientation.comap_id]),
    HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub oF hj IsOpenEmbedding.id
      (f := fiberCoord hs e hUe) (φ := f)
      (.of_forall fun x ↦ (hfφ x.val (hUφ x.property)).trans (fiberCoord_apply hs e hUe x).symm) hA]
  simp only [hf0, sub_zero]

/-- **The local index of a section at an isolated holomorphic zero is positive.** Under the
hypotheses of `TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`, if `z` is an
isolated zero of `s`, the local index of `s` at `z` is positive: the coordinate expression of `s`
vanishes at `φ z`, and not identically near `φ z`, so its order of vanishing there is a positive
integer. -/
theorem sectionIndex_pos_of_analyticAt (φ : OpenPartialHomeomorph M ℂ) {z : M}
    (hze : z ∈ e.baseSet) (hzφ : z ∈ φ.source) {ω : Orientation ℝ ℂ (Fin (1 + 1))}
    (ho : ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ e.baseSet, e.mapOrientation (Fin (1 + 1)) hx (o x) = ω)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, ℂ)) (S := {⟨z, hzφ⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.property hzφ (sub_eq_zero.1 hx))) (1 + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ⟩
          (1 + 1)).symm (oM z)).val =
      (ω.localOrientation hF).val)
    (hA : AnalyticAt ℂ (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) (φ z))
    (hsz : s z = 0) (hiso : ∀ᶠ x in 𝓝[≠] z, s x ≠ 0) :
    0 < o.sectionIndex hF oM hs z := by
  rw [o.sectionIndex_eq_analyticOrderNatAt hF oM hs e φ hze hzφ ho hφ hA,
    Nat.cast_pos, analyticOrderNatAt, Nat.pos_iff_ne_zero, ne_eq, ENat.toNat_eq_zero, not_or]
  set f : ℂ → ℂ := fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2
  have hf (x : M) (hxφ : x ∈ φ.source) (hxe : x ∈ e.baseSet) : f (φ x) = 0 ↔ s x = 0 := by
    simp only [f]
    rw [φ.left_inv hxφ]
    exact not_iff_not.1 (e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' ℂ x (s x)) hxe)
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- The order is not `0`, since `f` vanishes at `φ z`.
    exact (analyticOrderAt_eq_zero.1 h).resolve_left (not_not.2 hA) ((hf z hzφ hze).2 hsz)
  · -- The order is not infinite, since near `φ z` the function `f` vanishes only at `φ z`.
    obtain ⟨W, hW, hWo, hzW⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hiso)
    have hUo : IsOpen (φ.source ∩ e.baseSet ∩ W) :=
      (φ.open_source.inter e.open_baseSet).inter hWo
    refine analyticOrderAt_ne_top_of_zeros_subset (S := {φ z})
      (φ.isOpen_image_of_subset_source hUo fun _ hx ↦ hx.1.1)
      (mem_image_of_mem φ ⟨⟨hzφ, hze⟩, hzW⟩) ?_
    rintro _ ⟨x, ⟨⟨hxφ, hxe⟩, hxW⟩, rfl⟩ h0
    rw [Finset.mem_singleton]
    by_contra hne
    exact hW x hxW (fun hxz ↦ hne (congrArg φ hxz)) ((hf x hxφ hxe).1 h0)

end Local

section CompactSpace

variable [CompactSpace M] (φ : M → OpenPartialHomeomorph M ℂ) (e : M → Trivialization ℂ (π ℂ E))
  [∀ z, (e z).IsLinear ℝ] (ω : M → Orientation ℝ ℂ (Fin (1 + 1)))
  (hzφ : ∀ z, s z = 0 → z ∈ (φ z).source)

include hs in
/-- **The Euler number is the sum of the orders of the zeros of a section that is holomorphic in
oriented coordinates.** Let `M` be a compact surface with orientation `oM`, and let `s` be a
continuous section with finitely many zeros of an oriented real plane bundle `E → M` with fibre
`ℂ`. Suppose that at each zero `z` there are a chart `φ z` and a linear trivialization `e z` as in
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`: near `z`, `e z` reads the
orientation of `E` as the orientation `ω z` of `ℂ`, the translated chart carries `oM z` to the
local orientation selected by `ω z`, and the section is complex analytic in these coordinates at
`z`. Then the Euler class of `E`, evaluated on the fundamental class of `M`, is the sum of the
orders of vanishing of the section at its zeros. -/
theorem evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt (hZ : {x | s x = 0}.Finite)
    (hze : ∀ z, s z = 0 → z ∈ (e z).baseSet)
    (ho : ∀ z, s z = 0 → ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ (e z).baseSet,
      (e z).mapOrientation (Fin (1 + 1)) hx (o x) = ω z)
    (hφ : ∀ z (hz : s z = 0), localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (φ z).source ↦ φ z x - φ z z,
          (φ z).continuousOn.domRestrict.sub continuous_const⟩ : C((φ z).source, ℂ))
        (S := {⟨z, hzφ z hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((φ z).injOn x.property (hzφ z hz) (sub_eq_zero.1 hx))) (1 + 1)
        (((φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ z hz⟩
          (1 + 1)).symm (oM z)).val =
      ((ω z).localOrientation hF).val)
    (hA : ∀ z, s z = 0 → AnalyticAt ℂ
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (φ z z)) :
    (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down = ∑ z ∈ hZ.toFinset,
        (analyticOrderNatAt (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2)
          (φ z z) : ℤ) := by
  rw [o.evalFundamentalClass_eulerClass_eq_sum_sectionIndex hF oM hs hF hZ]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz0 : s z = 0 := hZ.mem_toFinset.1 hz
  exact o.sectionIndex_eq_analyticOrderNatAt hF oM hs (e z) (φ z) (hze z hz0) (hzφ z hz0)
    (ho z hz0) (hφ z hz0) (hA z hz0)

include hs in
/-- **The Euler number of a plane bundle with a section that is holomorphic in oriented coordinates
at its finitely many zeros is nonnegative.** Under the hypotheses of
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`, which
include that the section has finitely many zeros, the Euler class of `E` evaluated on the
fundamental class of `M` is a sum of orders of vanishing, so it is nonnegative. -/
theorem evalFundamentalClass_eulerClass_nonneg_of_analyticAt (hZ : {x | s x = 0}.Finite)
    (hze : ∀ z, s z = 0 → z ∈ (e z).baseSet)
    (ho : ∀ z, s z = 0 → ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ (e z).baseSet,
      (e z).mapOrientation (Fin (1 + 1)) hx (o x) = ω z)
    (hφ : ∀ z (hz : s z = 0), localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (φ z).source ↦ φ z x - φ z z,
          (φ z).continuousOn.domRestrict.sub continuous_const⟩ : C((φ z).source, ℂ))
        (S := {⟨z, hzφ z hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((φ z).injOn x.property (hzφ z hz) (sub_eq_zero.1 hx))) (1 + 1)
        (((φ z).open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hzφ z hz⟩
          (1 + 1)).symm (oM z)).val =
      ((ω z).localOrientation hF).val)
    (hA : ∀ z, s z = 0 → AnalyticAt ℂ
      (fun y ↦ (e z (TotalSpace.mk' ℂ ((φ z).symm y) (s ((φ z).symm y)))).2) (φ z z)) :
    0 ≤ (oM.evalFundamentalClass hF (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (o.eulerClass hF)).down := by
  rw [o.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt hF oM hs φ e ω hzφ hZ hze ho hφ
    hA]
  exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

end CompactSpace

end Holomorphic

/-! ### Checks: sections of the trivial line bundle over `ℂ` -/

section Checks

variable (hF : finrank ℝ ℂ = 1 + 1) (oM : HomologicalOrientation ℂ ℂ (1 + 1))
  {ω : Orientation ℝ ℂ (Fin (1 + 1))}

include hF in
/-- **Check: `z ↦ z ^ m` has local index `m` at `0`.** As a section of the trivial line bundle
over `ℂ`, oriented by `ω` in the fibres and by an orientation `oM` of `ℂ` which agrees with `ω` at
the origin, the function `z ↦ z ^ m` has local index `m` at `0`, its order of vanishing. -/
theorem sectionIndex_trivial_pow (hω : oM 0 = ω.localOrientation hF) (m : ℕ)
    (hs : Continuous fun x ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial ℂ ℂ) x (x ^ m)) :
    (trivial ℂ ω).sectionIndex hF oM hs 0 = m := by
  rcases eq_or_ne m 0 with rfl | hm
  · exact (trivial ℂ ω).sectionIndex_of_ne_zero hF oM _ (by simp)
  have h := (trivial ℂ ω).sectionIndex_eq_analyticOrderNatAt hF oM hs
    (Bundle.Trivial.trivialization ℂ ℂ) (OpenPartialHomeomorph.refl ℂ) (mem_univ 0) (mem_univ 0)
    (ω := ω) (.of_forall fun _ _ ↦ by simp)
    (by rw [← hω]; exact oM.localHomologyMap_refl_sub_localOrientationEquiv_symm hF 0) (by
      simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
        Trivial.trivialization_apply]
      fun_prop)
  have hpow : (fun y : ℂ ↦ y ^ m) = fun y ↦ y ^ m - 0 ^ m := by simp [zero_pow hm]
  rw [h]
  simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
    Trivial.trivialization_apply, Nat.cast_inj]
  rw [hpow, analyticOrderNatAt, analyticOrderAt_pow_sub_zero_pow hm, ENat.toNat_natCast]

include hF in
/-- **Check: complex conjugation has local index `-1` at `0`.** As a section of the trivial line
bundle over `ℂ`, oriented as in `TauCeti.VectorBundleOrientation.sectionIndex_trivial_pow`, the
function `z ↦ conj z` has local index `-1` at its only zero, the local index of complex
conjugation (`TauCeti.HomologicalOrientation.localIndex_conj`). It is real differentiable with
invertible derivative, but not complex analytic, and its local index is not an order of vanishing:
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt` uses its analyticity
hypothesis. -/
theorem sectionIndex_trivial_conj (hω : oM 0 = ω.localOrientation hF)
    (hs : Continuous fun x ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial ℂ ℂ) x (starRingEnd ℂ x)) :
    (trivial ℂ ω).sectionIndex hF oM hs 0 = -1 := by
  have hUe : ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆
      (Bundle.Trivial.trivialization ℂ ℂ).baseSet := fun x _ ↦ mem_univ x
  rw [(trivial ℂ ω).sectionIndex_eq_localIndex_fiberCoord hF oM hs
    (Bundle.Trivial.trivialization ℂ ℂ) ⊤ (mem_univ 0) (map_zero _) hUe
    (.of_forall fun _ _ ↦ by simp) oM hω]
  -- The fibre coordinate is complex conjugation on the open set `⊤`.
  have h := HomologicalOrientation.localIndex_comap hF oM oM
    (⊤ : TopologicalSpace.Opens ℂ).isOpenEmbedding' IsOpenEmbedding.id
    (f := fiberCoord hs (Bundle.Trivial.trivialization ℂ ℂ) hUe)
    (g := ⟨starRingEnd ℂ, Complex.continuous_conj⟩) (x := ⟨0, mem_univ 0⟩)
    (.of_forall fun _ ↦ by rw [fiberCoord_apply]; rfl)
  rw [HomologicalOrientation.comap_id] at h
  exact h.trans (oM.localIndex_conj 0)

end Checks

end VectorBundleOrientation

end TauCeti
