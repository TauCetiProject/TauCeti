/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LocalIndex
public import TauCeti.Analysis.Complex.Conformal.LocalIndex
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree
import Mathlib.LinearAlgebra.Complex.Determinant
import TauCeti.Analysis.Analytic.Order

/-!
# The local index of a section at a holomorphic zero is its order

Let `s` be a continuous section of an oriented real vector bundle `E → M` over an oriented
manifold, and `z` an isolated zero of `s`. Its local index
(`TauCeti.VectorBundleOrientation.sectionIndex`) is computed in a linear trivialization `e` by the
fibre coordinate `σ x = (e (s x)).2`
(`TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul`). This file restates that
computation as a local index of a map, and specializes it to holomorphic sections of line bundles.

* **The fibre coordinate.** On an open neighbourhood `U` of `z` isolating it among the zeros, the
  local index of `s` at `z` is the local index
  (`TauCeti.HomologicalOrientation.localIndex`) of `σ : U → F` at `z`, for the orientation of `U`
  restricted from that of `M` and any orientation of `F` whose local orientation at the origin is
  the one in which `e` reads the bundle orientation
  (`TauCeti.VectorBundleOrientation.sectionIndex_eq_localIndex_fiberCoord`).
* **Holomorphic zeros.** For a plane bundle with fibre `ℂ` over a surface charted on `ℂ`, read the
  section in a chart `φ` as `f y = (e (s (φ⁻¹ y))).2`. If the translated chart `y ↦ φ y - φ z`
  carries the local orientation of `M` at `z` to the one in which `e` reads the bundle orientation,
  as in the transverse case
  (`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`), and `f` is complex
  analytic at `φ z`, then the local index of `s` at `z` is the order of vanishing of `f` at `φ z`
  (`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`). Since `z` is an isolated
  zero, this order is a positive integer
  (`TauCeti.VectorBundleOrientation.sectionIndex_pos_of_analyticAt`).
* **The Euler number.** Over a compact surface, if a section with finitely many zeros is
  holomorphic in such coordinates at each zero, the Euler number `⟨e(E), [M]⟩` is the sum of the
  orders of the zeros, hence nonnegative
  (`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`,
  `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_nonneg`).

The holomorphic statement composes the first with the computation of the local index of a
holomorphic map as its order of vanishing
(`TauCeti.HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub`), applied to the
chart `φ` restricted to `U` with the orientation pulled back from `ℂ`. That orientation agrees at
`z` with the one restricted from `M`, because the translated chart has local index `1` for both
(`TauCeti.HomologicalOrientation.apply_eq_of_localIndex_eq`), and the local index only sees the
orientations at the point and its image
(`TauCeti.HomologicalOrientation.localIndex_eq_localIndex_of_apply_eq`).

On the trivial line bundle over `ℂ`, the section `z ↦ z ^ m` has local index `m` at `0`
(`TauCeti.VectorBundleOrientation.sectionIndex_trivial_pow`), while `z ↦ conj z`, which is not
holomorphic, has local index `-1` (`TauCeti.VectorBundleOrientation.sectionIndex_trivial_conj`).

## Main results

* `TauCeti.VectorBundleOrientation.sectionIndex_eq_localIndex_fiberCoord`: the local index of a
  section is the local index of its fibre coordinate.
* `TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`: at a zero where the section
  is holomorphic in oriented coordinates, the local index is the order of vanishing.
* `TauCeti.VectorBundleOrientation.sectionIndex_pos_of_analyticAt`: so it is positive.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`: the
  Euler number is the sum of the orders of the zeros of a holomorphic section.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_nonneg`: so it is nonnegative.

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

section General

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
  (oM : HomologicalOrientation M E' (n + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]

/-- **The local index of a section is the local index of its fibre coordinate.** Let `e` be a
linear trivialization of `E` and `U` an open neighbourhood of a zero `z` of `s`, inside the base
set of `e` and containing no other zero of `s`, on which `e` reads the orientation of every fibre
as the orientation `ω` of `F`. Orient `F` by any homological orientation `oF` whose local
orientation at the origin is the one selected by `ω`. Then the local index of `s` at `z` is the
local index at `z` of the fibre coordinate `σ x = (e (s x)).2`, a map `U → F`, for the orientation
of `U` restricted from `oM` and the orientation `oF` of `F`. -/
theorem sectionIndex_eq_localIndex_fiberCoord {z : M} (U : TopologicalSpace.Opens M)
    (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) (hsz : s z = 0)
    (hUe : (U : Set M) ⊆ e.baseSet) {ω : Orientation ℝ F (Fin (n + 1))}
    (ho : ∀ x (hx : x ∈ U), e.mapOrientation (Fin (n + 1)) (hUe hx) (o x) = ω)
    (oF : HomologicalOrientation F F (n + 1)) (hoF : oF 0 = ω.localOrientation hF)
    (σ : C(U, F)) (hσ : ∀ x : U, σ x = (e (TotalSpace.mk' F x.1 (s x.1))).2) :
    o.sectionIndex hF oM hs z = (oM.comap U.isOpenEmbedding').localIndex oF σ ⟨z, hz⟩ := by
  have hσ0 (x : U) : σ x = 0 ↔ s x.1 = 0 := by
    rw [hσ]
    exact not_iff_not.1 (e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' F x.1 (s x.1)) (hUe x.2))
  have hσz : σ ⁻¹' {0} ⊆ {⟨z, hz⟩} := fun x hx ↦ Subtype.ext (hUz x x.2 ((hσ0 x).1 hx))
  rw [eq_comm, (oM.comap U.isOpenEmbedding').localIndex_eq_iff_of_preimage_subset oF hF σ
    ((hσ0 _).2 hsz) hσz, hoF, HomologicalOrientation.comap_apply]
  exact o.localHomologyMap_eq_sectionIndex_smul hF oM hs e U.isOpen hz hUz hUe ho σ hσ hσz

end General

section Holomorphic

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] {E : M → Type}
  [TopologicalSpace (TotalSpace ℂ E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle ℂ E] [VectorBundle ℝ ℂ E]
  (o : VectorBundleOrientation ℂ E (Fin (1 + 1))) (hF : finrank ℝ ℂ = 1 + 1)
  (oM : HomologicalOrientation M ℂ (1 + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' ℂ x (s x))

include hF in
/-- If the chart `φ`, followed by the translation taking `φ z` to the origin, carries the local
orientation `oM z` to the local orientation of `ℂ` at the origin given by an orientation `oF`, then
`φ` restricts to an open embedding of any open set `V` inside its source, and the orientation of
`V` pulled back from `oF` along `φ` agrees at `z` with the one restricted from `oM`: the translated
chart has local index `1` at `z` for both. -/
private theorem exists_comap_chart_apply_eq (φ : OpenPartialHomeomorph M ℂ) {z : M}
    (V : TopologicalSpace.Opens M) (hz : z ∈ V) (hVφ : (V : Set M) ⊆ φ.source)
    (oF : HomologicalOrientation ℂ ℂ (1 + 1))
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, ℂ)) (S := {⟨z, hVφ hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.2 (hVφ hz) (sub_eq_zero.1 hx))) (1 + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hVφ hz⟩
          (1 + 1)).symm (oM z)).val =
      (oF 0).val) :
    ∃ hj : IsOpenEmbedding (fun x : V ↦ φ x),
      (oF.comap hj) ⟨z, hz⟩ = (oM.comap V.isOpenEmbedding') ⟨z, hz⟩ := by
  let W : TopologicalSpace.Opens M := ⟨φ.source, φ.open_source⟩
  let incl : V → W := fun x ↦ ⟨x.1, hVφ x.2⟩
  have hincl : IsOpenEmbedding incl :=
    (IsOpenEmbedding.of_comp_iff _ W.isOpenEmbedding').1 V.isOpenEmbedding'
  have hj : IsOpenEmbedding (fun x : V ↦ φ x) := φ.isOpenEmbedding_restrict.comp hincl
  -- The translated chart `τ` on the source of `φ` has local index `1` at `z` for `oM`, by `hφ`, ...
  let τ : C(W, ℂ) := ⟨fun x ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩
  have hτ : (oM.comap W.isOpenEmbedding').localIndex oF τ ⟨z, hVφ hz⟩ = 1 := by
    rw [HomologicalOrientation.localIndex_eq_iff_of_preimage_subset _ oF hF τ
      (x := ⟨z, hVφ hz⟩) (sub_self _)
      (fun x hx ↦ Subtype.ext (φ.injOn x.2 (hVφ hz) (sub_eq_zero.1 (hx : φ x - φ z = 0)))),
      one_smul, HomologicalOrientation.comap_apply]
    exact hφ
  -- ... so does its restriction to `V`, for the orientation of `V` restricted from `oM` ...
  let τV : C(V, ℂ) := τ.comp ⟨incl, hincl.continuous⟩
  have hτV : (oM.comap V.isOpenEmbedding').localIndex oF τV ⟨z, hz⟩ = 1 := by
    have h := HomologicalOrientation.localIndex_comap hF (oM.comap W.isOpenEmbedding') oF hincl
      IsOpenEmbedding.id (f := τV) (g := τ) (x := ⟨z, hz⟩) (.of_forall fun _ ↦ rfl)
    rw [HomologicalOrientation.comap_comap, HomologicalOrientation.comap_id,
      HomologicalOrientation.comap_congr _ _ V.isOpenEmbedding' rfl] at h
    exact h.trans hτ
  -- ... and for the orientation pulled back along `φ`, since translations preserve orientation.
  have hτj : (oF.comap hj).localIndex oF τV ⟨z, hz⟩ = 1 := by
    have h := HomologicalOrientation.localIndex_comap hF oF oF hj IsOpenEmbedding.id
      (f := τV) (g := ContinuousMap.addRight (-φ z)) (x := ⟨z, hz⟩)
      (.of_forall fun _ ↦ (sub_eq_add_neg _ _).symm)
    rwa [HomologicalOrientation.comap_id, HomologicalOrientation.localIndex_addRight oF hF] at h
  exact ⟨hj, HomologicalOrientation.apply_eq_of_localIndex_eq _ oF hF hF τV (hτj.trans hτV.symm)
    (by rw [hτV]; exact one_ne_zero)⟩

section Local

variable (e : Trivialization ℂ (π ℂ E)) [e.IsLinear ℝ]

/-- **The local index of a section at a holomorphic zero is its order.** Let `e` be a linear
trivialization of a real plane bundle `E` with fibre `ℂ` and `φ` a chart of `M` with values in
`ℂ`, and let `U` be an open neighbourhood of a zero `z` of `s`, inside the base set of `e` and the
source of `φ`, containing no other zero of `s`. Suppose that `e` reads the orientation of every
fibre over `U` as the orientation `ω` of `ℂ`, and that `φ`, followed by the translation taking
`φ z` to the origin, carries the local orientation `oM z` to the local orientation of `ℂ` selected
by `ω`. If the section, read in these coordinates as `y ↦ (e (s (φ⁻¹ y))).2`, is complex analytic
at `φ z`, then the local index of `s` at `z` is the order of vanishing of this coordinate
expression at `φ z`. -/
theorem sectionIndex_eq_analyticOrderNatAt (φ : OpenPartialHomeomorph M ℂ) {z : M}
    {U : Set M} (hU : IsOpen U) (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) (hsz : s z = 0)
    (hUe : U ⊆ e.baseSet) (hUφ : U ⊆ φ.source) {ω : Orientation ℝ ℂ (Fin (1 + 1))}
    (ho : ∀ x (hx : x ∈ U), e.mapOrientation (Fin (1 + 1)) (hUe hx) (o x) = ω)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, ℂ)) (S := {⟨z, hUφ hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.2 (hUφ hz) (sub_eq_zero.1 hx))) (1 + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hUφ hz⟩
          (1 + 1)).symm (oM z)).val =
      (ω.localOrientation hF).val)
    (hA : AnalyticAt ℂ (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) (φ z)) :
    o.sectionIndex hF oM hs z =
      analyticOrderNatAt (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) (φ z) := by
  set f : ℂ → ℂ := fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2 with hf
  have hfφ : ∀ x ∈ U, f (φ x) = (e (TotalSpace.mk' ℂ x (s x))).2 := fun x hx ↦ by
    simp only [hf]
    rw [φ.left_inv (hUφ hx)]
  have hf0 : f (φ z) = 0 := by
    rw [hfφ z hz]
    exact not_not.1 fun h ↦ (e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' ℂ z (s z))
      (hUe hz)).1 h hsz
  -- The neighbourhood `V`, the orientation `oF` of `ℂ` selected by `ω`, and the fibre coordinate.
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  let oF : HomologicalOrientation ℂ ℂ (1 + 1) :=
    .ofSimplyConnectedSpace 0 (ω.localOrientation hF)
  have hoF : oF 0 = ω.localOrientation hF :=
    HomologicalOrientation.ofSimplyConnectedSpace_apply_self _ _
  let σ : C(V, ℂ) := ⟨fun x ↦ (e (TotalSpace.mk' ℂ x.1 (s x.1))).2,
    continuous_snd.comp ((e.continuousOn.comp_continuous (hs.comp continuous_subtype_val)
      fun x ↦ e.mem_source.2 (hUe x.2)))⟩
  have h1 := o.sectionIndex_eq_localIndex_fiberCoord hF oM hs e V hz hUz hsz hUe ho oF hoF σ
    fun _ ↦ rfl
  -- The chart `φ` restricted to `V` is an open embedding, along which `oF` pulls back to an
  -- orientation of `V` that agrees at `z` with the one restricted from `oM`.
  obtain ⟨hj, horient⟩ := exists_comap_chart_apply_eq hF oM φ V hz hUφ oF (hoF ▸ hφ)
  rw [h1, HomologicalOrientation.localIndex_eq_localIndex_of_apply_eq _ oF hF σ horient.symm
      (p' := oF.comap IsOpenEmbedding.id) (by rw [HomologicalOrientation.comap_id]),
    HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub oF hj IsOpenEmbedding.id
      (f := σ) (φ := f) (.of_forall fun x ↦ hfφ x.1 x.2) hA]
  simp only [hf0, sub_zero]

/-- **The local index of a section at a holomorphic zero is positive.** Under the hypotheses of
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`, the local index of `s` at
the isolated zero `z` is positive: the coordinate expression of `s` vanishes at `φ z`, and not
identically near `φ z`, so its order of vanishing there is a positive integer. -/
theorem sectionIndex_pos_of_analyticAt (φ : OpenPartialHomeomorph M ℂ) {z : M}
    {U : Set M} (hU : IsOpen U) (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) (hsz : s z = 0)
    (hUe : U ⊆ e.baseSet) (hUφ : U ⊆ φ.source) {ω : Orientation ℝ ℂ (Fin (1 + 1))}
    (ho : ∀ x (hx : x ∈ U), e.mapOrientation (Fin (1 + 1)) (hUe hx) (o x) = ω)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, ℂ)) (S := {⟨z, hUφ hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.2 (hUφ hz) (sub_eq_zero.1 hx))) (1 + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hUφ hz⟩
          (1 + 1)).symm (oM z)).val =
      (ω.localOrientation hF).val)
    (hA : AnalyticAt ℂ (fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2) (φ z)) :
    0 < o.sectionIndex hF oM hs z := by
  rw [o.sectionIndex_eq_analyticOrderNatAt hF oM hs e φ hU hz hUz hsz hUe hUφ ho hφ hA,
    Nat.cast_pos, analyticOrderNatAt, Nat.pos_iff_ne_zero, ne_eq, ENat.toNat_eq_zero, not_or]
  set f : ℂ → ℂ := fun y ↦ (e (TotalSpace.mk' ℂ (φ.symm y) (s (φ.symm y)))).2
  have hf (x : M) (hx : x ∈ U) : f (φ x) = 0 ↔ s x = 0 := by
    simp only [f]
    rw [φ.left_inv (hUφ hx)]
    exact not_iff_not.1 (e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' ℂ x (s x)) (hUe hx))
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- The order is not `0`, since `f` vanishes at `φ z`.
    exact (analyticOrderAt_eq_zero.1 h).resolve_left (not_not.2 hA) ((hf z hz).2 hsz)
  · -- The order is not infinite, since `f` vanishes near `φ z` only at `φ z`.
    have hV : ∀ᶠ y in 𝓝 (φ z), y ∈ φ '' U :=
      (φ.isOpen_image_of_subset_source hU hUφ).mem_nhds (mem_image_of_mem φ hz)
    obtain ⟨_, ⟨hy0, x, hx, rfl⟩, hyz⟩ := ((eventually_nhdsWithin_of_eventually_nhds
      (s := {φ z}ᶜ) ((analyticOrderAt_eq_top.1 h).and hV)).and self_mem_nhdsWithin).exists
    exact hyz (congrArg φ (hUz x hx ((hf x hx).1 hy0)))

end Local

section CompactSpace

variable [CompactSpace M] (φ : M → OpenPartialHomeomorph M ℂ) (e : M → Trivialization ℂ (π ℂ E))
  [∀ z, (e z).IsLinear ℝ] (ω : M → Orientation ℝ ℂ (Fin (1 + 1)))
  (hzφ : ∀ z, s z = 0 → z ∈ (φ z).source)

include hs in
/-- **The Euler number is the sum of the orders of a holomorphic section.** Let `M` be a compact
surface with orientation `oM`, and let `s` be a continuous section with finitely many zeros of an
oriented real plane bundle `E → M` with fibre `ℂ`. Suppose that at each zero `z` there are a chart
`φ z` and a linear trivialization `e z` as in
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt`: `e z` reads the orientation
of `E` over the common domain as the orientation `ω z` of `ℂ`, the translated chart carries
`oM z` to the local orientation selected by `ω z`, and the section is complex analytic in these
coordinates. Then the Euler class of `E`, evaluated on the fundamental class of `M`, is the sum of
the orders of vanishing of the section at its zeros. -/
theorem evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt (hZ : {x | s x = 0}.Finite)
    (hze : ∀ z, s z = 0 → z ∈ (e z).baseSet)
    (ho : ∀ z, s z = 0 → ∀ x (hx : x ∈ (e z).baseSet), x ∈ (φ z).source →
      (e z).mapOrientation (Fin (1 + 1)) hx (o x) = ω z)
    (hφ : ∀ z (hz : s z = 0), localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (φ z).source ↦ φ z x - φ z z,
          (φ z).continuousOn.domRestrict.sub continuous_const⟩ : C((φ z).source, ℂ))
        (S := {⟨z, hzφ z hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((φ z).injOn x.2 (hzφ z hz) (sub_eq_zero.1 hx))) (1 + 1)
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
  -- The common domain of `φ z` and `e z`, with the other zeros removed, isolates `z`.
  let U := (φ z).source ∩ (e z).baseSet ∩ ({x | s x = 0} \ {z})ᶜ
  have hU : IsOpen U := ((φ z).open_source.inter (e z).open_baseSet).inter
    (hZ.subset sdiff_subset).isClosed.isOpen_compl
  have hUe : U ⊆ (e z).baseSet := fun x hx ↦ hx.1.2
  have hUφ : U ⊆ (φ z).source := fun x hx ↦ hx.1.1
  exact o.sectionIndex_eq_analyticOrderNatAt hF oM hs (e z) (φ z) hU
    ⟨⟨hzφ z hz0, hze z hz0⟩, fun h ↦ h.2 rfl⟩ (fun x hx hx0 ↦ by_contra fun h ↦ hx.2 ⟨hx0, h⟩)
    hz0 hUe hUφ (fun x hx ↦ ho z hz0 x (hUe hx) (hUφ hx)) (hφ z hz0) (hA z hz0)

include hs in
/-- **The Euler number of a bundle with a holomorphic section is nonnegative.** Under the
hypotheses of
`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_analyticOrderNatAt`, the
Euler class of `E` evaluated on the fundamental class of `M` is a sum of orders of vanishing,
so it is nonnegative. -/
theorem evalFundamentalClass_eulerClass_nonneg (hZ : {x | s x = 0}.Finite)
    (hze : ∀ z, s z = 0 → z ∈ (e z).baseSet)
    (ho : ∀ z, s z = 0 → ∀ x (hx : x ∈ (e z).baseSet), x ∈ (φ z).source →
      (e z).mapOrientation (Fin (1 + 1)) hx (o x) = ω z)
    (hφ : ∀ z (hz : s z = 0), localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (φ z).source ↦ φ z x - φ z z,
          (φ z).continuousOn.domRestrict.sub continuous_const⟩ : C((φ z).source, ℂ))
        (S := {⟨z, hzφ z hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((φ z).injOn x.2 (hzφ z hz) (sub_eq_zero.1 hx))) (1 + 1)
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

/-- The trivialization of the trivial bundle reads the constant orientation `ω` as `ω`. -/
private theorem mapOrientation_trivialization_trivial {x : ℂ}
    (hx : x ∈ (Bundle.Trivial.trivialization ℂ ℂ).baseSet) :
    (Bundle.Trivial.trivialization ℂ ℂ).mapOrientation (Fin (1 + 1)) hx (trivial ℂ ω x) = ω := by
  have h : (Bundle.Trivial.trivialization ℂ ℂ).linearEquivAt ℝ x hx = LinearEquiv.refl ℝ ℂ := by
    ext v
    rw [Trivialization.linearEquivAt_apply]
    rfl
  rw [Trivialization.mapOrientation_apply, h, trivial_apply, Orientation.map_refl, Equiv.refl_apply]

include hF in
/-- The identity chart of `ℂ` carries the local orientation `oM 0` to itself. -/
private theorem localHomologyMap_refl_sub_zero (hω : oM 0 = ω.localOrientation hF) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : (OpenPartialHomeomorph.refl ℂ).source ↦ OpenPartialHomeomorph.refl ℂ x -
            OpenPartialHomeomorph.refl ℂ 0,
          (OpenPartialHomeomorph.refl ℂ).continuousOn.domRestrict.sub continuous_const⟩ :
          C((OpenPartialHomeomorph.refl ℂ).source, ℂ)) (S := {⟨0, mem_univ 0⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext ((OpenPartialHomeomorph.refl ℂ).injOn x.2 (mem_univ 0)
            (sub_eq_zero.1 hx))) (1 + 1)
        (((OpenPartialHomeomorph.refl ℂ).open_source.isOpenEmbedding_subtypeVal
          |>.localOrientationEquiv ⟨0, mem_univ 0⟩ (1 + 1)).symm (oM 0)).val =
      (ω.localOrientation hF).val := by
  rw [← hω]
  convert IsOpenEmbedding.localHomologyMap_localOrientationEquiv_symm
    (OpenPartialHomeomorph.refl ℂ).open_source.isOpenEmbedding_subtypeVal ⟨0, mem_univ 0⟩ (oM 0)
    (fun x hx ↦ Subtype.ext hx) using 3
  ext x
  simp

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
    (Bundle.Trivial.trivialization ℂ ℂ)
    (OpenPartialHomeomorph.refl ℂ) isOpen_univ (mem_univ 0)
    (fun x _ hx ↦ pow_eq_zero_iff hm |>.1 hx) (zero_pow hm) (subset_univ _) (subset_univ _)
    (fun _ _ ↦ mapOrientation_trivialization_trivial _)
    (localHomologyMap_refl_sub_zero hF oM hω) (by
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
function `z ↦ conj z` has local index `-1` at its only zero. It is real differentiable with
invertible derivative, but not complex analytic, and its local index is not an order of vanishing:
`TauCeti.VectorBundleOrientation.sectionIndex_eq_analyticOrderNatAt` uses its analyticity
hypothesis. -/
theorem sectionIndex_trivial_conj (hω : oM 0 = ω.localOrientation hF)
    (hs : Continuous fun x ↦ TotalSpace.mk' ℂ (E := Bundle.Trivial ℂ ℂ) x (starRingEnd ℂ x)) :
    (trivial ℂ ω).sectionIndex hF oM hs 0 = -1 := by
  have hdet : (Complex.conjCLE : ℂ →L[ℝ] ℂ).det = -1 := by simp [ContinuousLinearMap.det]
  have hderiv : HasFDerivAt (fun y ↦ (Bundle.Trivial.trivialization ℂ ℂ
      (TotalSpace.mk' ℂ ((OpenPartialHomeomorph.refl ℂ).symm y)
        (starRingEnd ℂ ((OpenPartialHomeomorph.refl ℂ).symm y)))).2)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (OpenPartialHomeomorph.refl ℂ 0) := by
    simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq,
      Trivial.trivialization_apply]
    exact Complex.conjCLE.hasFDerivAt.congr_of_eventuallyEq (.of_forall Complex.conjCLE_apply)
  rw [(trivial ℂ ω).sectionIndex_eq_sign_det_of_hasFDerivAt hF oM hs
    (Bundle.Trivial.trivialization ℂ ℂ) (OpenPartialHomeomorph.refl ℂ) isOpen_univ (mem_univ 0)
    (fun x _ hx ↦ by simpa using hx) (map_zero _) (subset_univ _) (subset_univ _)
    (fun _ _ ↦ mapOrientation_trivialization_trivial _) (localHomologyMap_refl_sub_zero hF oM hω)
    hderiv (by rw [hdet]; norm_num), hdet]
  simp

end Checks

end VectorBundleOrientation

end TauCeti
