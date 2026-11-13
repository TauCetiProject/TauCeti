/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Derivative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex

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
along `E|_U ≅ U × F → F`, of the generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected by `ω`
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairOver_thomClass`). The local index
is then the pairing of that generator with the image of `oM z` under the fibre coordinate. The
second statement composes the first with the action of a map on local homology at a point where it
has invertible derivative
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
    -- The carriers of the pairs agree with `U` and the subspaces of the total space only up to
    -- unfolding, so `rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]` leaves the
    -- evaluation lemmas unable to match; split the composite into its evaluations instead.
    change TopPair.Hom.fst (thomPairOverUnivIso F E).hom (TopPair.Hom.fst
      (thomPairOverMap F E (subset_univ U))
        (TopPair.Hom.fst (sectionThomPairOverMap hs hz hUz) x)) = _
    erw [thomPairOverMap_fst_apply, thomPairOverUnivIso_hom_fst_apply,
      thomPairMapOfNeZero_fst_apply]
    rfl)

omit [T2Space M] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle ℝ F E] in
private theorem sectionThomPairOverMap_comp_thomPairOverIso {z : M} {U : Set M} (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s x = 0 → x = z) (hUe : U ⊆ e.baseSet) :
    sectionThomPairOverMap hs hz hUz ≫ (e.thomPairOverIso ℝ hUe).hom ≫ prodThomPairSnd U F =
      TopPair.ofSubsetMap (TopCat.ofHom (fiberCoord hs e hUe))
        ((mapsTo_preimage _ _).mono_left
          (compl_subset_compl.2 (fiberCoord_preimage_subset hs e hz hUz hUe))) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦ by
    -- The carriers of the pairs agree with `U`, `F` and the subspaces of the total space only up
    -- to unfolding, so `rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]` leaves the
    -- evaluation lemmas unable to match; split the composite into its evaluations instead.
    change TopPair.Hom.fst (prodThomPairSnd U F) (TopPair.Hom.fst (e.thomPairOverIso ℝ hUe).hom
      (TopPair.Hom.fst (sectionThomPairOverMap hs hz hUz) x)) = _
    erw [prodThomPairSnd_fst_apply, TopPair.ofSubsetMap_fst_apply,
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
  -- The mathematical input: the pull-back of the Thom class along `s` is the pull-back of the
  -- generator selected by `ω` along the fibre coordinate.
  have hclass : TopPair.singularCohomologyMap
      (sectionThomPairOverMap hs hz hUz ≫ thomPairOverMap F E (subset_univ U) ≫
        (thomPairOverUnivIso F E).hom) (n + 1) (o.thomClass hF) =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (TopCat.ofHom (fiberCoord hs e hUe))
          ((mapsTo_preimage _ _).mono_left
            (compl_subset_compl.2 (fiberCoord_preimage_subset hs e hz hUz hUe))))
        (n + 1) (ω.localCohomologyClass hF) := by
    rw [TopPair.singularCohomologyMap_comp_apply,
      o.singularCohomologyMap_thomPairOver_thomClass hF e hUe ho,
      ← TopPair.singularCohomologyMap_comp_apply,
      sectionThomPairOverMap_comp_thomPairOverIso hs e hz hUz hUe]
  rw [sectionIndex_eq o hF oM hs hU hz hUz, ← sectionThomPairOverMap_comp hs hz hUz, hclass,
    TopPair.singularKronecker_naturality, ModuleCat.hom_comp, LinearMap.comp_apply,
    IsOpenEmbedding.coe_localOrientationEquiv_symm, localHomologyMap_def]

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
    Orientation.kronecker_localCohomologyClass_zsmul]

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
  set f : F → F := fun y ↦ (e (TotalSpace.mk' F (φ.symm y) (s (φ.symm y)))).2 with hf
  have hleft : ∀ x ∈ U, φ.symm (φ x) = x := fun x hx ↦ φ.left_inv (hUφ hx)
  have hfφ : ∀ x ∈ U, f (φ x) = (e (TotalSpace.mk' F x (s x))).2 := fun x hx ↦ by
    simp only [hf]
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
  -- The action of `f` on local homology at `φ z`, with target the value `c = f (φ z)`. That value
  -- enters the morphism types and the proofs of the preimage conditions, so neither `rw` nor
  -- `simp` can replace it by `0` after the fact; it is generalized and substituted instead.
  have key : ∀ {c : F} (hc : f (φ z) = c),
      localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) g (S := {⟨φ z, hzV⟩}) (T := {c})
          (fun y hy ↦ Subtype.ext (hfx y y.2 ((hy : f y = c).trans (hc.symm.trans hf0))))
          (n + 1) =
        (SignType.sign A.det : ℤ) • localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
          (⟨fun y : V ↦ c + (y - φ z), by fun_prop⟩ : C(V, F)) (S := {⟨φ z, hzV⟩}) (T := {c})
          (by
            rintro y hy
            exact Subtype.ext (sub_eq_zero.1 (add_eq_left.1 hy))) (n + 1) := by
    rintro _ rfl
    exact localHomologyMap_domRestrict_eq_sign_det_smul_of_hasFDerivAt _ (hVo.mem_nhds hzV) hfV hA
      hdet (fun y hy h ↦ hfx y hy (h.trans hf0)) (n + 1)
  -- The translated chart `τ y = φ y - φ z` on the source of `φ`, which reads `oM z` as the local
  -- orientation selected by `ω` by `hφ`.
  let τ : C(φ.source, F) := ⟨fun x ↦ φ x - φ z, φ.continuousOn.domRestrict.sub continuous_const⟩
  have hτz : τ ⁻¹' {0} ⊆ {⟨z, hUφ hz⟩} := by
    rintro x hx
    exact Subtype.ext (φ.injOn x.2 (hUφ hz) (sub_eq_zero.1 hx))
  have hUz' : ContinuousMap.inclusion hUφ ⁻¹' {⟨z, hUφ hz⟩} ⊆ {⟨z, hz⟩} := by
    rintro x (hx : _ = _)
    exact Subtype.ext (congrArg Subtype.val hx :)
  -- On local homology, `g ∘ φU` acts as `sign (det A)` times the restriction of `τ` to `U`: this is
  -- `key` composed with `φU`, since `φU` followed by the translation by `-φ z` is `τ` on `U`.
  have hmor : localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ)) (g.comp φU) (S := {⟨z, hz⟩})
      (T := {0}) ((preimage_mono hg).trans hφU) (n + 1) =
      (SignType.sign A.det : ℤ) • localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (τ.comp (ContinuousMap.inclusion hUφ)) ((preimage_mono hτz).trans hUz') (n + 1) := by
    have hτ : (⟨fun y : V ↦ (0 : F) + (y - φ z), by fun_prop⟩ : C(V, F)).comp φU =
        τ.comp (ContinuousMap.inclusion hUφ) :=
      ContinuousMap.ext fun _ ↦ zero_add _
    rw [← localHomologyMap_comp _ φU g hφU hg, key hf0, Preadditive.comp_zsmul]
    -- The composite produced by `key` does not match `localHomologyMap_comp` syntactically.
    erw [localHomologyMap_comp]
    -- `hτ` also rewrites the map inside the dependent preimage condition, which `rw` cannot.
    simp only [hτ]
  -- Integer multiples of morphisms of `ℤ`-modules act on elements by the multiple.
  have hsmul : ∀ (c : ℤ) {X Y : ModuleCat.{0} ℤ} (u : X ⟶ Y) (v : X), (c • u) v = c • u v :=
    fun _ _ _ _ _ ↦ rfl
  have hb := o.localHomologyMap_eq_sectionIndex_smul hF oM hs e hU hz
    hUz hUe ho (g.comp φU) (fun x ↦ hfφ x.1 x.2) ((preimage_mono hg).trans hφU)
  -- The inclusion of `U` into the source of `φ` carries the local orientation of `U` at `z` to
  -- that of the source, which `τ` carries to the local orientation selected by `ω`.
  rw [hmor, hsmul, ← localHomologyMap_comp _ _ τ hUz' hτz, ConcreteCategory.comp_apply,
    φ.open_source.localHomologyMap_inclusion_localOrientationEquiv_symm hU hUφ hz (oM z) hUz',
    hφ] at hb
  rw [← ω.kronecker_localCohomologyClass_zsmul hF (o.sectionIndex hF oM hs z), ← hb,
    ω.kronecker_localCohomologyClass_zsmul hF]

end VectorBundleOrientation

end TauCeti
