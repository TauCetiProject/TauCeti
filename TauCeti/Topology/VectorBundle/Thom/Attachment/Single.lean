/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Attachment
public import TauCeti.Topology.VectorBundle.SphereBundle.Radius

/-!
# Attaching a single disc bundle and its Thom-pair homology and cohomology

Let `E → B` be a real vector bundle with continuous fibre norm and `r : B → ℝ` a continuous
positive radius function. If a space `Z` is obtained from a closed subset `X` by attaching the
closed disc bundle `D_r(E)` along its sphere bundle `S_r(E)` through a closed embedding
`f : (D_r(E), S_r(E)) ⟶ (Z, X)`, precomposing `f` with the radial rescaling isomorphism
`(D(E), S(E)) ≅ (D_r(E), S_r(E))` (`TauCeti.discSpherePairIsoOfRadius`) reduces to unit-radius
attachment (`TauCeti.isIso_singularHomologyMap_of_attach_discBundle`). Thus `f` induces
isomorphisms on relative singular homology
(`TauCeti.isIso_singularHomologyMap_of_attach_discBundleOfRadius`) and cohomology
(`TauCeti.isIso_singularCohomologyMap_of_attach_discBundleOfRadius`), and composing with
`(D_r(E), S_r(E)) ⟶ (E, E₀)` yields the Thom-pair identifications `Hₙ(E, E₀) ≅ Hₙ(Z, X)` and
`Hⁿ(Z, X) ≅ Hⁿ(E, E₀)` (`TauCeti.singularHomologyIsoThomPairOfAttachDiscBundleOfRadius`,
`TauCeti.singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius`, and their unit-radius
counterparts `TauCeti.singularHomologyIsoThomPairOfAttachDiscBundle`,
`TauCeti.singularCohomologyIsoThomPairOfAttachDiscBundle`).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology

universe uF w v u

namespace TauCeti

variable {B : Type w} {F : Type uF} {E : B → Type w} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] {Z : Type w} [TopologicalSpace Z] {X : Set Z}

section Radius

variable (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
  {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b)
  {f : discSpherePairOfRadius F E r ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : IsClosedEmbedding (TopPair.Hom.fst f)) (hX : IsClosed X)
  (hfX : ∀ v : discBundleOfRadius F E r,
    TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ sphereBundleOfRadius F E r)
  (hfcover : X ∪ range (TopPair.Hom.fst f) = univ)

include hr hrpos in
private lemma rescaledAttach_fst_apply (v : discBundle F E) :
    (TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f) v : Z) =
      TopPair.Hom.fst f (discBundleHomeomorphOfRadius F E hr hrpos v) :=
  (ConcreteCategory.comp_apply
    (TopPair.Hom.fst (discSpherePairIsoOfRadius F E hr hrpos).hom) (TopPair.Hom.fst f) v).trans
    (congrArg (TopPair.Hom.fst f) (discSpherePairIsoOfRadius_hom_fst_apply F E hr hrpos v))

include hr hrpos in
/-- Precomposing a map out of `(D_r(E), S_r(E))` with `(D(E), S(E)) ≅ (D_r(E), S_r(E))` preserves
the image of the ambient disc bundle. -/
theorem mem_range_fst_discSpherePairIsoOfRadius_hom_comp {z : Z} :
    z ∈ (range (TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f)) : Set Z) ↔
      z ∈ (range (TopPair.Hom.fst f) : Set Z) :=
  ⟨fun ⟨v, hv⟩ ↦ ⟨discBundleHomeomorphOfRadius F E hr hrpos v,
      (rescaledAttach_fst_apply hr hrpos (f := f) v).symm.trans hv⟩,
   fun ⟨w, hw⟩ ↦ ⟨(discBundleHomeomorphOfRadius F E hr hrpos).symm w,
      (rescaledAttach_fst_apply hr hrpos (f := f) _).trans <|
        (congrArg (TopPair.Hom.fst f)
          ((discBundleHomeomorphOfRadius F E hr hrpos).apply_symm_apply w)).trans hw⟩⟩

include hr hrpos hf in
/-- Precomposing a closed embedding of `D_r(E)` with radial rescaling gives a closed embedding of
`D(E)`. -/
theorem isClosedEmbedding_fst_discSpherePairIsoOfRadius_hom_comp :
    IsClosedEmbedding
      (TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f)) := by
  have hfn : (⇑(TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f)) :
      discBundle F E → Z) =
      ⇑(TopPair.Hom.fst f) ∘ ⇑(discBundleHomeomorphOfRadius F E hr hrpos) :=
    funext (rescaledAttach_fst_apply hr hrpos)
  exact hfn ▸ hf.comp (discBundleHomeomorphOfRadius F E hr hrpos).isClosedEmbedding

include hr hrpos hfX in
/-- If `f : D_r(E) → Z` meets `X` only along `S_r(E)`, its radial rescaling on `D(E)` meets `X`
only along `S(E)`. -/
theorem mem_sphereBundle_of_discSpherePairIsoOfRadius_hom_comp_mem (v : discBundle F E)
    (hv : TopPair.Hom.fst ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫ f) v ∈ X) :
    (v : TotalSpace F E) ∈ sphereBundle F E := by
  have hs := mem_sphereBundleOfRadius.1 (hfX _ (rescaledAttach_fst_apply hr hrpos (f := f) v ▸ hv))
  rw [coe_discBundleHomeomorphOfRadius_apply] at hs
  dsimp only [TotalSpace.mk'] at hs
  rw [norm_smul, Real.norm_of_nonneg (hrpos v.1.proj).le] at hs
  exact mem_sphereBundle.2 ((mul_right_eq_self₀.1 hs).resolve_right (hrpos v.1.proj).ne')

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

include hnorm hr hrpos hf hX hfX hfcover in
/-- **Attaching a disc bundle of positive continuous radius induces isomorphisms on relative
homology.** Let `E → B` be a real vector bundle with continuous fibre norm and `r : B → ℝ` a
continuous positive radius. If `Z` is obtained from a closed subset `X` by attaching `D_r(E)`
along `S_r(E)` via `f : (D_r(E), S_r(E)) ⟶ (Z, X)`, then `f` induces isomorphisms
`Hₙ(D_r(E), S_r(E)) ≅ Hₙ(Z, X)` in every degree. -/
theorem isIso_singularHomologyMap_of_attach_discBundleOfRadius (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap f R n) := by
  let e := TopPair.singularHomologyMapIso R (discSpherePairIsoOfRadius F E hr hrpos) n
  have hg : IsIso (e.hom ≫ TopPair.singularHomologyMap f R n) := by
    rw [TopPair.singularHomologyMapIso_hom, ← TopPair.singularHomologyMap_comp]
    exact isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n
      (isClosedEmbedding_fst_discSpherePairIsoOfRadius_hom_comp hr hrpos hf)
      (mem_sphereBundle_of_discSpherePairIsoOfRadius_hom_comp_mem hr hrpos hfX)
      (eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 hfcover z).imp_right
        (mem_range_fst_discSpherePairIsoOfRadius_hom_comp hr hrpos).2)
  exact IsIso.of_isIso_comp_left e.hom _

include hnorm hr hrpos hf hX hfX hfcover in
/-- **Attaching a disc bundle of positive continuous radius induces isomorphisms on relative
cohomology.** Under the hypotheses of
`TauCeti.isIso_singularHomologyMap_of_attach_discBundleOfRadius`, `f` induces isomorphisms
`Hⁿ(Z, X) ≅ Hⁿ(D_r(E), S_r(E))` in every degree. -/
theorem isIso_singularCohomologyMap_of_attach_discBundleOfRadius
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (discSpherePairIsoOfRadius F E hr hrpos).hom n) :=
    ⟨TopPair.singularCohomologyMap (discSpherePairIsoOfRadius F E hr hrpos).inv n,
      by rw [← TopPair.singularCohomologyMap_comp, Iso.inv_hom_id,
        TopPair.singularCohomologyMap_id],
      by rw [← TopPair.singularCohomologyMap_comp, Iso.hom_inv_id,
        TopPair.singularCohomologyMap_id]⟩
  have hg : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n ≫
      TopPair.singularCohomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom n) := by
    rw [← TopPair.singularCohomologyMap_comp]
    exact isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M
      (isClosedEmbedding_fst_discSpherePairIsoOfRadius_hom_comp hr hrpos hf)
      (mem_sphereBundle_of_discSpherePairIsoOfRadius_hom_comp_mem hr hrpos hfX)
      (eq_univ_of_forall fun z ↦ (eq_univ_iff_forall.1 hfcover z).imp_right
        (mem_range_fst_discSpherePairIsoOfRadius_hom_comp hr hrpos).2)
  exact IsIso.of_isIso_comp_right _
    (TopPair.singularCohomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom n)

/-- **Thom-pair homology of a single radius-`r` disc-bundle attachment**: `Hₙ(E, E₀) ≅ Hₙ(Z, X)`,
formed from the zig-zag `(E, E₀) ← (D_r(E), S_r(E)) → (Z, X)`. -/
def singularHomologyIsoThomPairOfAttachDiscBundleOfRadius (R : C) (n : ℕ) :
    (thomPair F E).singularHomology R n ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (@asIso _ _ _ _ (TopPair.singularHomologyMap
      (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n)
    (isIso_singularHomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R n)).symm ≪≫
  @asIso _ _ _ _ (TopPair.singularHomologyMap f R n)
    (isIso_singularHomologyMap_of_attach_discBundleOfRadius hnorm hr hrpos hf hX hfX hfcover R n)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairOfRadiusMap_comp_isoThomPair_hom (R : C) (n : ℕ) :
    TopPair.singularHomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundleOfRadius
          hnorm hr hrpos hf hX hfX hfcover R n).hom =
      TopPair.singularHomologyMap f R n := by
  have := isIso_singularHomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R n
  have := isIso_singularHomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R n
  simp [singularHomologyIsoThomPairOfAttachDiscBundleOfRadius]

@[reassoc (attr := simp)]
theorem singularHomologyMap_attach_comp_isoThomPairOfRadius_inv (R : C) (n : ℕ) :
    TopPair.singularHomologyMap f R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundleOfRadius
          hnorm hr hrpos hf hX hfX hfcover R n).inv =
      TopPair.singularHomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n := by
  have := isIso_singularHomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R n
  have := isIso_singularHomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R n
  simp [singularHomologyIsoThomPairOfAttachDiscBundleOfRadius]

/-- **Thom-pair cohomology of a single radius-`r` disc-bundle attachment**: `Hⁿ(Z, X) ≅ Hⁿ(E, E₀)`,
formed from the zig-zag `(E, E₀) ← (D_r(E), S_r(E)) → (Z, X)`. -/
def singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      (thomPair F E).singularCohomology R k M n :=
  @asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n)
    (isIso_singularCohomologyMap_of_attach_discBundleOfRadius
      hnorm hr hrpos hf hX hfX hfcover R k M n) ≪≫
  (@asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n)
    (isIso_singularCohomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius_hom_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius
        hnorm hr hrpos hf hX hfX hfcover R k M n).hom ≫
      TopPair.singularCohomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n =
      TopPair.singularCohomologyMap f n := by
  have := isIso_singularCohomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R k M n
  simp [singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius]

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius_inv_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius
        hnorm hr hrpos hf hX hfX hfcover R k M n).inv ≫
      TopPair.singularCohomologyMap f n =
      TopPair.singularCohomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n := by
  have := isIso_singularCohomologyMap_discSpherePairOfRadiusMap F E hnorm hr hrpos R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundleOfRadius
    hnorm hr hrpos hf hX hfX hfcover R k M n
  simp [singularCohomologyIsoThomPairOfAttachDiscBundleOfRadius]

end Radius

section UnitRadius

variable (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
  {f : discSpherePair F E ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : IsClosedEmbedding (TopPair.Hom.fst f)) (hX : IsClosed X)
  (hfX : ∀ v : discBundle F E, TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ sphereBundle F E)
  (hfcover : X ∪ range (TopPair.Hom.fst f) = univ)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- **Thom-pair homology of a single unit disc-bundle attachment**: `Hₙ(E, E₀) ≅ Hₙ(Z, X)`, formed
from `(E, E₀) ← (D(E), S(E)) → (Z, X)`. -/
def singularHomologyIsoThomPairOfAttachDiscBundle (R : C) (n : ℕ) :
    (thomPair F E).singularHomology R n ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (@asIso _ _ _ _ (TopPair.singularHomologyMap (discSpherePairMap F E) R n)
    (isIso_singularHomologyMap_discSpherePairMap F E hnorm R n)).symm ≪≫
  @asIso _ _ _ _ (TopPair.singularHomologyMap f R n)
    (isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n hf hfX hfcover)

@[reassoc (attr := simp)]
theorem singularHomologyMap_discSpherePairMap_comp_isoThomPair_hom (R : C) (n : ℕ) :
    TopPair.singularHomologyMap (discSpherePairMap F E) R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R n).hom =
      TopPair.singularHomologyMap f R n := by
  have := isIso_singularHomologyMap_discSpherePairMap F E hnorm R n
  have := isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n hf hfX hfcover
  simp [singularHomologyIsoThomPairOfAttachDiscBundle]

@[reassoc (attr := simp)]
theorem singularHomologyMap_attach_comp_isoThomPair_inv (R : C) (n : ℕ) :
    TopPair.singularHomologyMap f R n ≫
        (singularHomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R n).inv =
      TopPair.singularHomologyMap (discSpherePairMap F E) R n := by
  have := isIso_singularHomologyMap_discSpherePairMap F E hnorm R n
  have := isIso_singularHomologyMap_of_attach_discBundle hnorm hX R n hf hfX hfcover
  simp [singularHomologyIsoThomPairOfAttachDiscBundle]

/-- **Thom-pair cohomology of a single unit disc-bundle attachment**: `Hⁿ(Z, X) ≅ Hⁿ(E, E₀)`,
formed from `(E, E₀) ← (D(E), S(E)) → (Z, X)`. -/
def singularCohomologyIsoThomPairOfAttachDiscBundle
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      (thomPair F E).singularCohomology R k M n :=
  @asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n)
    (isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M hf hfX hfcover) ≪≫
  (@asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (discSpherePairMap F E) n)
    (isIso_singularCohomologyMap_discSpherePairMap F E hnorm R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundle_hom_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R k M n).hom ≫
      TopPair.singularCohomologyMap (discSpherePairMap F E) n =
      TopPair.singularCohomologyMap f n := by
  have := isIso_singularCohomologyMap_discSpherePairMap F E hnorm R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M hf hfX hfcover
  simp [singularCohomologyIsoThomPairOfAttachDiscBundle]

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachDiscBundle_inv_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachDiscBundle hnorm hf hX hfX hfcover R k M n).inv ≫
      TopPair.singularCohomologyMap f n =
      TopPair.singularCohomologyMap (discSpherePairMap F E) n := by
  have := isIso_singularCohomologyMap_discSpherePairMap F E hnorm R k M n
  have := isIso_singularCohomologyMap_of_attach_discBundle hnorm hX R n k M hf hfX hfcover
  simp [singularCohomologyIsoThomPairOfAttachDiscBundle]

end UnitRadius

end TauCeti
