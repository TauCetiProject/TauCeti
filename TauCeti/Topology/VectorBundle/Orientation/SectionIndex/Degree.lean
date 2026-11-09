/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Derivative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex
public import TauCeti.Topology.VectorBundle.Thom.Class

/-!
# The local index of a section in local coordinates

Let `s` be a continuous section of a real vector bundle `E → M` of rank `n + 1` with orientation
`o`, over a manifold `M` of dimension `n + 1` with homological orientation `oM`, and let `z` be an
isolated zero of `s`. Its local index (`TauCeti.VectorBundleOrientation.sectionIndex`) is defined
by pulling back the Thom class along `s`. This file computes it in local coordinates.

* **In a trivialization.** Let `e` be a linear trivialization of `E` and `U` an open neighbourhood
  of `z` in the base set of `e`, containing no other zero of `s`, on which `e` reads the
  orientation of every fibre as one orientation `ω` of the model fibre `F`. Then the fibre
  coordinate `x ↦ (e (s x)).2` is a map of pairs `(U, U ∖ {z}) ⟶ (F, F ∖ {0})`, and it carries the
  local orientation `oM z` to the local index times the local orientation of `F` at the origin
  selected by `ω` (`TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul`).
  So the local index of the section is the local degree of its fibre coordinate.
* **At a transverse zero.** If moreover `φ` is a chart of `M` with values in `F` that carries
  `oM z` to the local orientation selected by `ω` (after translating `φ z` to the origin), and the
  section read in these coordinates, `y ↦ (e (s (φ⁻¹ y))).2`, is differentiable at `φ z` with
  derivative `A` of nonzero determinant, then the local index is `sign (det A)`
  (`TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`).

Combined with `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`,
this computes the Euler number of an oriented bundle over a compact oriented manifold as the signed
count of the transverse zeros of a section.

The first statement comes from the Thom class over a trivializing set: over a set inside the base
set of `e` on which `e` reads the orientation as `ω`, the Thom class restricts to the pull-back,
along `E|_U ≅ U × F → F`, of the generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected by `ω`, since both
restrict to the same generators on the fibres and a top-degree class over a trivializing set is
determined by its restrictions to the fibres
(`Bundle.Trivialization.singularCohomology_thomPairOver_ext`). The local index is then the
pairing of that generator with the image of `oM z` under the fibre coordinate. The second
statement composes the first with the action of a map on local homology at a point where it has
invertible derivative
(`TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`).

## Main results

* `TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul`: the fibre coordinate
  of `s` acts on local homology at `z` by the local index.
* `TauCeti.VectorBundleOrientation.sectionIndex_eq_sign_det_of_hasFDerivAt`: at a transverse zero
  the local index is the sign of the Jacobian determinant in oriented coordinates.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11.
* G. E. Bredon, *Topology and Geometry*, Graduate Texts in Mathematics 139, Springer (1993),
  Chapter VI, §12 (indices of sections at isolated zeros, computed in local coordinates).
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set Topology

namespace TauCeti

namespace VectorBundleOrientation

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : M → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)
  (oM : HomologicalOrientation M E' (n + 1)) {s : ∀ x, E x}
  (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]

/-- The fibre coordinate `x ↦ (e (s x)).2` of a section `s` in a trivialization `e`, on an open
set `U` inside the base set of `e`. -/
private def fiberCoord {U : Set M} (hUe : U ⊆ e.baseSet) : C(U, F) :=
  ⟨fun x ↦ (e (TotalSpace.mk' F x.1 (s x.1))).2,
    continuous_snd.comp ((e.continuousOn.comp_continuous (hs.comp continuous_subtype_val)
      fun x ↦ e.mem_source.2 (hUe x.2)))⟩

omit [T2Space M] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E] in
/-- The fibre coordinate vanishes exactly where the section does. -/
private theorem fiberCoord_eq_zero_iff {U : Set M} (hUe : U ⊆ e.baseSet) (x : U) :
    fiberCoord hs e hUe x = 0 ↔ s x.1 = 0 := by
  have := e.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' F x.1 (s x.1)) (hUe x.2)
  exact not_iff_not.1 this

omit [T2Space M] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E] in
/-- On a neighbourhood containing no other zero of `s`, the fibre coordinate is a map of pairs
`(U, U ∖ {z}) ⟶ (F, F ∖ {0})`. -/
private theorem fiberCoord_preimage_subset {z : M} {U : Set M} (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) (hUe : U ⊆ e.baseSet) :
    fiberCoord hs e hUe ⁻¹' {0} ⊆ {⟨z, hz⟩} := fun x hx ↦
  Subtype.ext (hUz x.1 x.2 ((fiberCoord_eq_zero_iff hs e hUe x).1 hx))

/-- The projection `(W × F, W × (F ∖ {0})) ⟶ (F, F ∖ {0})` of the Thom pair of a product bundle
onto the fibre pair. -/
private def prodThomPairSnd (W : Type) [TopologicalSpace W] :
    prodThomPair W F ⟶ TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) :=
  TopPair.ofSubsetMap (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) fun _ hp ↦ hp

omit [NormedSpace ℝ F] in
private theorem prodThomPairFiberMap_comp_prodThomPairSnd {W : Type} [TopologicalSpace W]
    (w : W) : prodThomPairFiberMap F w ≫ prodThomPairSnd W = 𝟙 _ :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦ by
    -- `TopPair.Hom.fst` of a composite is the composite of the `fst` maps only up to unfolding.
    erw [CategoryTheory.comp_apply, prodThomPairFiberMap_fst_apply, prodThomPairSnd,
      TopPair.ofSubsetMap_fst_apply]
    rfl)

omit [T2Space M] [VectorBundle ℝ F E] in
/-- A top-degree class over a trivializing set is determined on the fibres, in any degree equal to
the rank. -/
private theorem singularCohomology_thomPairOver_ext' [FiniteDimensional ℝ F] {W : Set M}
    (hW : W ⊆ e.baseSet) {d : ℕ} (hd : finrank ℝ F = d)
    {u v : (thomPairOver F E W).singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{0} ℤ)) d}
    (h : ∀ b (hb : b ∈ W), TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) d u =
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) d v) : u = v := by
  subst hd
  exact e.singularCohomology_thomPairOver_ext hW h

omit [T2Space M] in
/-- **The Thom class over an oriented trivializing set.** Over a set `W` inside the base set of a
linear trivialization `e` that reads the orientation of every fibre over `W` as the same
orientation `ω` of `F`, the Thom class restricts to the pull-back of the generator of
`Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected by `ω` along the projection `E|_W ≅ W × F → F`. -/
private theorem singularCohomologyMap_thomPairOver_thomClass {W : Set M} (hW : W ⊆ e.baseSet)
    {ω : Orientation ℝ F (Fin (n + 1))}
    (ho : ∀ b (hb : b ∈ W), e.mapOrientation (Fin (n + 1)) (hW hb) (o b) = ω) :
    TopPair.singularCohomologyMap
        (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom) (n + 1)
        (o.thomClass hF) =
      TopPair.singularCohomologyMap ((e.thomPairOverIso ℝ hW).hom ≫ prodThomPairSnd W) (n + 1)
        (ω.localCohomologyClass hF) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  refine singularCohomology_thomPairOver_ext' e hW hF fun b hb ↦ ?_
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
    fiberThomPairOverMap_comp_thomPairOverMap_assoc,
    fiberThomPairOverMap_comp_thomPairOverUnivIso_hom,
    o.singularCohomologyMap_fiberThomPairMap_thomClass hF e (hW hb), ho b hb,
    e.fiberThomPairOverMap_comp_thomPairOverIso_hom_assoc ℝ hW hb,
    prodThomPairFiberMap_comp_prodThomPairSnd, Category.comp_id]

/-- The section `s` on `U`, as a map of pairs `(U, U ∖ {z}) ⟶ (E|_U, E₀|_U)`. -/
private def sectionThomPairOverMap {z : M} {U : Set M} (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) :
    TopPair.ofSubset ({⟨z, hz⟩}ᶜ : Set (TopCat.of U)) ⟶ thomPairOver F E U :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x ↦ ⟨TotalSpace.mk' F x.1 (s x.1), x.2⟩,
      (hs.comp continuous_subtype_val).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨TotalSpace.mk' F x.1.1 (s x.1.1), x.1.2,
      mem_zeroSectionCompl.2 fun h0 ↦ x.2 (Subtype.ext (hUz x.1.1 x.1.2 h0))⟩,
      ((hs.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)⟩)
    (by ext; rfl)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ x, Module ℝ (E x)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [T2Space M] [VectorBundle ℝ F E] in
private theorem sectionThomPairOverMap_comp {z : M} {U : Set M} (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) :
    sectionThomPairOverMap hs hz hUz ≫ thomPairOverMap F E (subset_univ U) ≫
        (thomPairOverUnivIso F E).hom =
      thomPairMapOfNeZero ⟨fun x : U ↦ TotalSpace.mk' F x.1 (s x.1),
        hs.comp continuous_subtype_val⟩ (S := {⟨z, hz⟩})
        fun x hx h0 ↦ hx (mem_singleton_iff.2 (Subtype.ext (hUz x.1 x.2 h0))) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦ by
    change TopPair.Hom.fst (thomPairOverUnivIso F E).hom (TopPair.Hom.fst
      (thomPairOverMap F E (subset_univ U))
        (TopPair.Hom.fst (sectionThomPairOverMap hs hz hUz) x)) = _
    erw [thomPairOverMap_fst_apply, thomPairOverUnivIso_hom_fst_apply,
      thomPairMapOfNeZero_fst_apply]
    rfl)

omit [T2Space M] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E] in
private theorem sectionThomPairOverMap_comp_thomPairOverIso {z : M} {U : Set M} (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) (hUe : U ⊆ e.baseSet) :
    sectionThomPairOverMap hs hz hUz ≫ (e.thomPairOverIso ℝ hUe).hom ≫ prodThomPairSnd U =
      TopPair.ofSubsetMap (TopCat.ofHom (fiberCoord hs e hUe))
        ((mapsTo_preimage _ _).mono_left
          (compl_subset_compl.2 (fiberCoord_preimage_subset hs e hz hUz hUe))) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦ by
    change TopPair.Hom.fst (prodThomPairSnd U) (TopPair.Hom.fst (e.thomPairOverIso ℝ hUe).hom
      (TopPair.Hom.fst (sectionThomPairOverMap hs hz hUz) x)) = _
    erw [prodThomPairSnd, TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
      Trivialization.thomPairOverIso_hom_fst_apply]
    rfl)

/-- **The local index as a pairing in the fibre.** In a linear trivialization `e` reading the
orientation of every fibre over an isolating neighbourhood `U` of `z` as the orientation `ω` of
`F`, the local index of `s` at `z` is the pairing of the generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected
by `ω` with the image of the local orientation `oM z` under the fibre coordinate of `s`. -/
private theorem sectionIndex_eq_singularKronecker {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) (hUe : U ⊆ e.baseSet) {ω : Orientation ℝ F (Fin (n + 1))}
    (ho : ∀ x (hx : x ∈ U), e.mapOrientation (Fin (n + 1)) (hUe hx) (o x) = ω) :
    o.sectionIndex hF oM hs z =
      (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularKronecker ℤ (n + 1)
        (ω.localCohomologyClass hF)).hom
        (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (fiberCoord hs e hUe)
          (fiberCoord_preimage_subset hs e hz hUz hUe) (n + 1)
          ((hU.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm
            (oM z)).val)).down := by
  rw [sectionIndex_eq o hF oM hs hU hz hUz, ← sectionThomPairOverMap_comp hs hz hUz,
    TopPair.singularCohomologyMap_comp_apply,
    singularCohomologyMap_thomPairOver_thomClass o hF e hUe ho,
    ← TopPair.singularCohomologyMap_comp_apply,
    sectionThomPairOverMap_comp_thomPairOverIso hs e hz hUz hUe,
    TopPair.singularKronecker_naturality, IsOpenEmbedding.coe_localOrientationEquiv_symm,
    localHomologyMap_def]
  rfl

/-- The pairing of the generator selected by `ω` with an integral multiple of the local orientation
selected by `ω` is that multiple. -/
private theorem singularKronecker_localCohomologyClass_zsmul (ω : Orientation ℝ F (Fin (n + 1)))
    (c : ℤ) :
    (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularKronecker ℤ (n + 1)
      (ω.localCohomologyClass hF)).hom (c • (ω.localOrientation hF).val)).down = c := by
  rw [map_zsmul, Orientation.kronecker_localCohomologyClass]
  simp

/-- **The local index in a local trivialization.** Let `e` be a linear trivialization of `E` and
`U` an open neighbourhood of `z` inside its base set, containing no zero of `s` other than `z`, on
which `e` reads the orientation of every fibre as the orientation `ω` of `F`. The fibre coordinate
`σ x = (e (s x)).2` of `s` is a map of pairs `(U, U ∖ {z}) ⟶ (F, F ∖ {0})`, and it carries the
local orientation `oM z`, read in `U` through excision, to the local index of `s` at `z` times the
local orientation of `F` at the origin selected by `ω`. -/
theorem localHomologyMap_eq_sectionIndex_smul {z : M} {U : Set M}
    (hU : IsOpen U) (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) (hUe : U ⊆ e.baseSet)
    {ω : Orientation ℝ F (Fin (n + 1))}
    (ho : ∀ x (hx : x ∈ U), e.mapOrientation (Fin (n + 1)) (hUe hx) (o x) = ω) (σ : C(U, F))
    (hσ : ∀ x : U, σ x = (e (TotalSpace.mk' F x.1 (s x.1))).2)
    (hσz : σ ⁻¹' ({0} : Set F) ⊆ {(⟨z, hz⟩ : U)}) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) σ (S := {⟨z, hz⟩}) (T := {0}) hσz (n + 1)
        ((hU.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm (oM z)).val =
      o.sectionIndex hF oM hs z • (ω.localOrientation hF).val := by
  obtain rfl : σ = fiberCoord hs e hUe := ContinuousMap.ext hσ
  obtain ⟨c, hc⟩ := (isLocalOrientation_iff _ _ _).1 (ω.localOrientation hF).property
    (localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (fiberCoord hs e hUe) hσz (n + 1)
      ((hU.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm (oM z)).val)
  rw [sectionIndex_eq_singularKronecker o hF oM hs e hU hz hUz hUe ho, ← hc,
    singularKronecker_localCohomologyClass_zsmul]

/-- `TauCeti.localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt`, with the value at the
point named. -/
private theorem localHomologyMap_domRestrict_eq_sign_det_smul_of_eq [FiniteDimensional ℝ F]
    {f : F → F} {f' : F →L[ℝ] F} {x : F} {V : Set F} (hV : V ∈ 𝓝 x) (hfV : ContinuousOn f V)
    (hf : HasFDerivAt f f' x) (hdet : f'.det ≠ 0) {c : F} (hc : f x = c)
    (hfx : ∀ y ∈ V, f y = c → y = x) (k : ℕ) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (⟨V.domRestrict f, hfV.domRestrict⟩ : C(V, F))
        (S := {⟨x, mem_of_mem_nhds hV⟩}) (T := {c}) (fun y hy ↦ Subtype.ext (hfx y y.2 hy)) k =
      (SignType.sign f'.det : ℤ) •
        localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
          (⟨fun y : V ↦ c + (y - x), by fun_prop⟩ : C(V, F))
          (S := {⟨x, mem_of_mem_nhds hV⟩}) (T := {c})
          (by
            rintro y hy
            exact Subtype.ext (sub_eq_zero.1 (add_eq_left.1 hy))) k := by
  subst hc
  exact localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt _ hV hfV hf hdet hfx k

/-- **The local index at a transverse zero is the sign of the Jacobian.** Let `e` be a linear
trivialization of `E` and `φ` a chart of `M` with values in the model fibre `F`, and let `U` be an
open neighbourhood of a zero `z` of `s`, inside the base set of `e` and the source of `φ`,
containing no other zero of `s`. Suppose that `e` reads the orientation of every fibre over `U` as
the orientation `ω` of `F`, and that `φ`, followed by the translation taking `φ z` to the origin,
carries the local orientation `oM z` to the local orientation of `F` selected by `ω`. If the
section, read in these coordinates as `y ↦ (e (s (φ⁻¹ y))).2`, is differentiable at `φ z` with
derivative `A` of nonzero determinant, then the local index of `s` at `z` is the sign of
`det A`. -/
theorem sectionIndex_eq_sign_det_of_hasFDerivAt (φ : OpenPartialHomeomorph M F) {z : M}
    {U : Set M} (hU : IsOpen U) (hz : z ∈ U) (hUz : ∀ x ∈ U, s x = 0 → x = z) (hsz : s z = 0)
    (hUe : U ⊆ e.baseSet) (hUφ : U ⊆ φ.source) {ω : Orientation ℝ F (Fin (n + 1))}
    (ho : ∀ x (hx : x ∈ U), e.mapOrientation (Fin (n + 1)) (hUe hx) (o x) = ω)
    (hφ : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, F)) (S := {⟨z, hUφ hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (φ.injOn x.2 (hUφ hz) (sub_eq_zero.1 hx))) (n + 1)
        ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hUφ hz⟩
          (n + 1)).symm (oM z)).val =
      (ω.localOrientation hF).val)
    {A : F →L[ℝ] F}
    (hA : HasFDerivAt (fun y ↦ (e (TotalSpace.mk' F (φ.symm y) (s (φ.symm y)))).2) A (φ z))
    (hdet : A.det ≠ 0) :
    o.sectionIndex hF oM hs z = SignType.sign A.det := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  set f : F → F := fun y ↦ (e (TotalSpace.mk' F (φ.symm y) (s (φ.symm y)))).2
  have hleft : ∀ x ∈ U, φ.symm (φ x) = x := fun x hx ↦ φ.left_inv (hUφ hx)
  have hfφ : ∀ x ∈ U, f (φ x) = (e (TotalSpace.mk' F x (s x))).2 := fun x hx ↦ by
    change (e (TotalSpace.mk' F (φ.symm (φ x)) (s (φ.symm (φ x))))).2 = _
    rw [hleft x hx]
  -- The image `V = φ U` of the neighbourhood, on which the section reads as `f`.
  set V := φ '' U
  have hVo : IsOpen V := φ.isOpen_image_of_subset_source hU hUφ
  have hzV : φ z ∈ V := mem_image_of_mem φ hz
  have hVU : ∀ y ∈ V, φ.symm y ∈ U := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hleft x hx]
    exact hx
  have hVt : V ⊆ φ.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact φ.map_source (hUφ hx)
  have hfV : ContinuousOn f V :=
    continuous_snd.comp_continuousOn (e.continuousOn.comp
      (hs.comp_continuousOn (φ.continuousOn_symm.mono hVt))
      fun y hy ↦ e.mem_source.2 (hUe (hVU y hy)))
  have hf0 : f (φ z) = 0 := (hfφ z hz).trans ((fiberCoord_eq_zero_iff hs e hUe ⟨z, hz⟩).2 hsz)
  have hfx : ∀ y ∈ V, f y = 0 → y = φ z := by
    rintro _ ⟨x, hx, rfl⟩ h0
    rw [hfφ x hx] at h0
    rw [hUz x hx ((fiberCoord_eq_zero_iff hs e hUe ⟨x, hx⟩).1 h0)]
  let g : C(V, F) := ⟨V.domRestrict f, hfV.domRestrict⟩
  let φU : C(U, V) := ⟨fun x ↦ ⟨φ x, mem_image_of_mem φ x.2⟩,
    ((φ.continuousOn.mono hUφ).domRestrict).subtype_mk _⟩
  have hφU : φU ⁻¹' {⟨φ z, hzV⟩} ⊆ {⟨z, hz⟩} := fun x hx ↦
    Subtype.ext (φ.injOn (hUφ x.2) (hUφ hz) (congrArg Subtype.val hx :))
  have hg : g ⁻¹' {0} ⊆ {⟨φ z, hzV⟩} := fun y hy ↦ Subtype.ext (hfx y y.2 hy)
  have key := localHomologyMap_domRestrict_eq_sign_det_smul_of_eq (hVo.mem_nhds hzV) hfV hA hdet
    hf0 hfx (n + 1)
  -- The inclusion of `U` into the source of `φ` carries the local orientation of `U` at `z` to
  -- that of the source.
  have hincl : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.inclusion hUφ)
      (S := {⟨z, hz⟩}) (T := {⟨z, hUφ hz⟩})
      (by
        rintro x (hx : _ = _)
        have hx' := congrArg Subtype.val hx
        exact Subtype.ext hx') (n + 1)
      ((hU.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm (oM z)).val =
      ((φ.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hUφ hz⟩
        (n + 1)).symm (oM z)).val := by
    refine (ConcreteCategory.bijective_of_isIso (localHomologyIsoOfIsOpenEmbedding
      (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ))
      φ.open_source.isOpenEmbedding_subtypeVal ⟨z, hUφ hz⟩ (n + 1)).hom).1 ?_
    rw [localHomologyIsoOfIsOpenEmbedding_hom, ← ConcreteCategory.comp_apply]
    erw [localHomologyMap_comp]
    exact (hU.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm ⟨z, hz⟩
      (oM z) _).trans
      (φ.open_source.isOpenEmbedding_subtypeVal.localHomologyMap_localOrientationEquiv_symm
        ⟨z, hUφ hz⟩ (oM z) _).symm
  have ha := o.localHomologyMap_eq_sectionIndex_smul hF oM hs e hU hz
    hUz hUe ho (g.comp φU) (fun x ↦ hfφ x.1 x.2) ((preimage_mono hg).trans hφU)
  have hb : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (g.comp φU) (S := {⟨z, hz⟩})
      (T := {0}) ((preimage_mono hg).trans hφU) (n + 1)
      ((hU.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩ (n + 1)).symm (oM z)).val =
      (SignType.sign A.det : ℤ) • (ω.localOrientation hF).val := by
    have hτ : (⟨fun y : V ↦ (0 : F) + (y - φ z), by fun_prop⟩ : C(V, F)).comp φU =
        (⟨fun x : φ.source ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩ :
          C(φ.source, F)).comp (ContinuousMap.inclusion hUφ) :=
      ContinuousMap.ext fun _ ↦ zero_add _
    -- Integer multiples of morphisms of `ℤ`-modules act on elements by the multiple.
    have hsmul : ∀ (c : ℤ) {X Y : ModuleCat.{0} ℤ} (u : X ⟶ Y) (v : X), (c • u) v = c • u v :=
      fun _ _ _ _ _ ↦ rfl
    rw [← localHomologyMap_comp _ φU g hφU hg, ConcreteCategory.comp_apply, key, hsmul,
      ← ConcreteCategory.comp_apply]
    erw [localHomologyMap_comp]
    simp only [hτ]
    rw [← localHomologyMap_comp, ConcreteCategory.comp_apply, hincl, hφ]
    · rintro x (hx : _ = _)
      have hx' := congrArg Subtype.val hx
      exact Subtype.ext hx'
    · rintro x hx
      exact Subtype.ext (φ.injOn x.2 (hUφ hz) (sub_eq_zero.1 hx))
  rw [← singularKronecker_localCohomologyClass_zsmul hF ω (o.sectionIndex hF oM hs z), ← ha, hb,
    singularKronecker_localCohomologyClass_zsmul]

end VectorBundleOrientation

end TauCeti
