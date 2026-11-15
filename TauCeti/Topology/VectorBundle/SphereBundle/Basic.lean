/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.EulerClass
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.VectorBundle.Smul

/-!
# Disc and sphere bundles and the Thom pair

Let `E → B` be a real vector bundle whose fibres carry norms, such that the fibre norm is a
continuous function on the total space; for instance a continuous Riemannian vector bundle
(`TauCeti.continuous_norm_bundle`). Its unit disc bundle `D(E)` and unit sphere bundle `S(E)` are
the vectors of norm at most one and exactly one (`TauCeti.discBundle`, `TauCeti.sphereBundle`).
The sphere bundle projects continuously onto the base (`TauCeti.sphereBundleProj`).

Radial rescaling compares them with the Thom pair `(E, E₀)` of the bundle, where `E₀` is the
complement of the zero section:

* the inclusion `D(E) → E` is a homotopy equivalence, with homotopy inverse the radial retraction
  `v ↦ v / max 1 ‖v‖` (`TauCeti.discBundleHomotopyEquiv`);
* the inclusion `S(E) → E₀` (`TauCeti.sphereBundleInclusion`) is a homotopy equivalence, with
  homotopy inverse the normalization `v ↦ v / ‖v‖` (`TauCeti.sphereBundleHomotopyEquiv`,
  `TauCeti.sphereBundleNormalization`), so it induces isomorphisms on cohomology
  (`TauCeti.isIso_singularCohomologyMap_sphereBundleInclusion`).

In both cases the homotopy is the straight line from the identity to the retraction, which only
rescales each vector by a positive factor. In general they do not combine into a homotopy
equivalence of pairs: when some fibre is nonzero, a continuous retraction of `E` onto `D(E)`
cannot carry all of `E₀` into `S(E)`. Comparing the long exact sequences of the two pairs
instead, the inclusion of pairs `(D(E), S(E)) ⟶ (E, E₀)` (`TauCeti.discSpherePairMap`) induces
isomorphisms on relative singular cohomology with arbitrary coefficients in every degree
(`TauCeti.isIso_singularCohomologyMap_discSpherePairMap`).

So Thom classes may be read on the disc-sphere pair `(D(E), S(E))`, and the cohomology of the
deleted total space `E₀` in the long exact sequence of the Thom pair is that of the sphere bundle,
as in the Gysin sequence: with the connecting morphism `Hˡ(S(E)) ⟶ Hˡ⁺¹(E, E₀)` of the sphere
bundle (`TauCeti.sphereBundleδ`), the sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(S(E)) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

of the Euler class maps, the pullback along `S(E) → B` and `TauCeti.sphereBundleδ` is exact
(`TauCeti.exact_eulerClass_singularCohomologyMap_sphereBundleProj`,
`TauCeti.exact_singularCohomologyMap_sphereBundleProj_sphereBundleδ`,
`TauCeti.exact_sphereBundleδ_eulerClass`). No orientation, finite-dimensionality or condition on
the base is needed. The rank zero case is included: there `S(E)` and `E₀` are empty and `D(E) = E`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (the pair `(E, E₀)`) and §12 (the Gysin sequence of the sphere bundle).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (the disc and sphere bundles and the Thom
  space `D(E)/S(E)`).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set
open scoped unitInterval ContinuousMap

universe w v u

namespace TauCeti

section Sets

variable {B : Type w} (F : Type*) (E : B → Type w) [∀ b, NormedAddCommGroup (E b)]

/-- The unit disc bundle `D(E)` of a bundle with normed fibres: the vectors of norm at most one. -/
def discBundle : Set (TotalSpace F E) :=
  {v | ‖v.2‖ ≤ 1}

/-- The unit sphere bundle `S(E)` of a bundle with normed fibres: the vectors of norm one. -/
def sphereBundle : Set (TotalSpace F E) :=
  {v | ‖v.2‖ = 1}

variable {F E} in
@[simp]
theorem mem_discBundle {v : TotalSpace F E} : v ∈ discBundle F E ↔ ‖v.2‖ ≤ 1 :=
  Iff.rfl

variable {F E} in
@[simp]
theorem mem_sphereBundle {v : TotalSpace F E} : v ∈ sphereBundle F E ↔ ‖v.2‖ = 1 :=
  Iff.rfl

/-- The sphere bundle lies in the disc bundle. -/
theorem sphereBundle_subset_discBundle : sphereBundle F E ⊆ discBundle F E :=
  fun _ hv ↦ (mem_sphereBundle.1 hv).le

/-- The sphere bundle lies in the complement `E₀` of the zero section. -/
theorem sphereBundle_subset_zeroSectionCompl : sphereBundle F E ⊆ zeroSectionCompl F E :=
  fun _ hv ↦
  mem_zeroSectionCompl.2 (norm_ne_zero_iff.1 ((mem_sphereBundle.1 hv).symm ▸ one_ne_zero))

variable [TopologicalSpace (TotalSpace F E)]

/-- The disc-sphere pair `(D(E), S(E))` of a bundle with normed fibres. -/
abbrev discSpherePair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) (sphereBundle_subset_discBundle F E)

/-- The inclusion `(D(E), S(E)) ⟶ (E, E₀)` of the disc-sphere pair into the Thom pair. -/
def discSpherePairMap : discSpherePair F E ⟶ thomPair F E :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom (ContinuousMap.inclusion (sphereBundle_subset_zeroSectionCompl F E)))
    (by ext; rfl)

@[simp]
theorem discSpherePairMap_fst_apply (v : discBundle F E) :
    TopPair.Hom.fst (discSpherePairMap F E) v = v.1 :=
  (rfl)

@[simp]
theorem discSpherePairMap_snd_apply (v : sphereBundle F E) :
    (TopPair.Hom.snd (discSpherePairMap F E) v).1 = v.1 :=
  (rfl)

/-- The inclusion `S(E) → E₀` of the unit sphere bundle into the complement of the zero section. -/
def sphereBundleInclusion : TopCat.of (sphereBundle F E) ⟶ (thomPair F E).snd :=
  TopCat.ofHom (ContinuousMap.inclusion (sphereBundle_subset_zeroSectionCompl F E))

@[simp]
theorem coe_sphereBundleInclusion_apply (v : sphereBundle F E) :
    @Subtype.val _ (· ∈ zeroSectionCompl F E) (sphereBundleInclusion F E v) = v :=
  (rfl)

/-- The subspace component of the inclusion `(D(E), S(E)) ⟶ (E, E₀)` is the inclusion
`S(E) → E₀`. -/
theorem discSpherePairMap_snd :
    TopPair.Hom.snd (discSpherePairMap F E) = sphereBundleInclusion F E :=
  (rfl)

end Sets

section Proj

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- The projection `S(E) → B` of the unit sphere bundle of a bundle with normed fibres. -/
def sphereBundleProj : C(sphereBundle F E, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj, (FiberBundle.continuous_proj F E).comp continuous_subtype_val⟩

@[simp]
theorem sphereBundleProj_apply (v : sphereBundle F E) :
    sphereBundleProj F E v = (v : TotalSpace F E).proj :=
  (rfl)

/-- The inclusion `S(E) → E₀` followed by the projection `π₀ : E₀ → B` is the projection of the
sphere bundle. -/
@[reassoc (attr := simp)]
theorem sphereBundleInclusion_comp_zeroSectionComplProj :
    sphereBundleInclusion F E ≫ zeroSectionComplProj F E = TopCat.ofHom (sphereBundleProj F E) :=
  TopCat.ext fun v ↦ (zeroSectionComplProj_apply F E _).trans (sphereBundleProj_apply F E v).symm

end Proj

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The radial retraction `v ↦ v / max 1 ‖v‖` of the total space onto the disc bundle. -/
private def discRetraction (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    C(TotalSpace F E, discBundle F E) where
  toFun v := ⟨TotalSpace.mk' F v.proj ((max 1 ‖v.2‖)⁻¹ • v.2), by
    have h : 0 < max 1 ‖v.2‖ := lt_max_of_lt_left one_pos
    rw [mem_discBundle, norm_smul, norm_inv, Real.norm_of_nonneg h.le, inv_mul_le_iff₀ h, mul_one]
    exact le_max_right _ _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.smul_totalSpace ?_ continuous_id) _
    exact (continuous_const.max hnorm).inv₀ fun v ↦ (lt_max_of_lt_left one_pos).ne'

/-- **The disc bundle is a deformation retract of the total space**: the inclusion `D(E) → E` is a
homotopy equivalence, with homotopy inverse the radial retraction `v ↦ v / max 1 ‖v‖`. -/
def discBundleHomotopyEquiv (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    discBundle F E ≃ₕ TotalSpace F E where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := discRetraction F E hnorm
  left_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (discBundle F E))
    ext ⟨⟨b, x⟩, hx⟩
    · rfl
    · simp [discRetraction, max_eq_left (mem_discBundle.1 hx)]
  right_inv := ⟨ContinuousMap.Homotopy.symm
    { toFun := fun p ↦ TotalSpace.mk' F p.2.proj ((1 - p.1 + p.1 * (max 1 ‖p.2.2‖)⁻¹) • p.2.2)
      continuous_toFun := by
        have ht : Continuous fun p : I × TotalSpace F E ↦ (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        exact Continuous.smul_totalSpace ((continuous_const.sub ht).add (ht.mul
          ((continuous_const.max (hnorm.comp continuous_snd)).inv₀
            fun _ ↦ (lt_max_of_lt_left one_pos).ne'))) continuous_snd
      map_zero_left := fun v ↦ by simp
      map_one_left := fun v ↦ by simp [discRetraction] }⟩

@[simp]
theorem coe_discBundleHomotopyEquiv (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    (v : discBundle F E) : discBundleHomotopyEquiv F E hnorm v = v.1 :=
  (rfl)

/-- The homotopy inverse of `D(E) ≃ₕ E` is the radial retraction `v ↦ v / max 1 ‖v‖`. -/
@[simp]
theorem coe_discBundleHomotopyEquiv_symm_apply (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    (v : TotalSpace F E) :
    ((discBundleHomotopyEquiv F E hnorm).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.proj ((max 1 ‖v.2‖)⁻¹ • v.2) :=
  (rfl)

/-- **The sphere bundle is a deformation retract of the deleted total space**: the inclusion
`S(E) → E₀` is a homotopy equivalence, with homotopy inverse the normalization `v ↦ v / ‖v‖`. -/
def sphereBundleHomotopyEquiv (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    sphereBundle F E ≃ₕ zeroSectionCompl F E :=
  ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction
    (sphereBundle_subset_zeroSectionCompl F E)
    (fun p ↦ TotalSpace.mk' F p.2.1.proj ((1 - p.1 + p.1 * ‖p.2.1.2‖⁻¹) • p.2.1.2))
    (have ht : Continuous fun p : I × zeroSectionCompl F E ↦ (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    Continuous.smul_totalSpace ((continuous_const.sub ht).add (ht.mul
      ((hnorm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
        fun p ↦ norm_ne_zero_iff.2 (mem_zeroSectionCompl.1 p.2.2))))
      (continuous_subtype_val.comp continuous_snd))
    (fun p ↦ have hp := mem_zeroSectionCompl.1 p.2.2
      mem_zeroSectionCompl.2 <|
        smul_ne_zero (by
          simpa using (convex_Ioi (0 : ℝ) one_pos (inv_pos.2 (norm_pos_iff.2 hp))
            (sub_nonneg.2 p.1.2.2) p.1.2.1 (sub_add_cancel 1 _)).ne') hp)
    (fun v ↦ by simp)
    (fun v ↦ by
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (mem_zeroSectionCompl.1 v.2))])
    (fun t v hv ↦ by simp [mem_sphereBundle.1 hv, hv])

@[simp]
theorem coe_sphereBundleHomotopyEquiv (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    (v : sphereBundle F E) : (sphereBundleHomotopyEquiv F E hnorm v : TotalSpace F E) = v.1 :=
  ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply _ _ _ _ _ _ _ v

/-- The homotopy inverse of `S(E) ≃ₕ E₀` is the normalization `v ↦ v / ‖v‖`. -/
@[simp]
theorem coe_sphereBundleHomotopyEquiv_symm_apply
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) (v : zeroSectionCompl F E) :
    ((sphereBundleHomotopyEquiv F E hnorm).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (‖v.1.2‖⁻¹ • v.1.2) := by
  rw [sphereBundleHomotopyEquiv,
    ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_symm_apply]
  simp

/-- The normalization `v ↦ v / ‖v‖` of `E₀` onto the sphere bundle, the homotopy inverse of the
inclusion `S(E) → E₀` (`TauCeti.sphereBundleHomotopyEquiv`). -/
def sphereBundleNormalization (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    (thomPair F E).snd ⟶ TopCat.of (sphereBundle F E) :=
  TopCat.ofHom (sphereBundleHomotopyEquiv F E hnorm).invFun

@[simp]
theorem coe_sphereBundleNormalization_apply (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    (v : zeroSectionCompl F E) :
    (sphereBundleNormalization F E hnorm v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (‖v.1.2‖⁻¹ • v.1.2) :=
  coe_sphereBundleHomotopyEquiv_symm_apply F E hnorm v

/-- The forward map of the homotopy equivalence `S(E) ≃ₕ E₀` is the inclusion `S(E) → E₀`. -/
theorem ofHom_sphereBundleHomotopyEquiv (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    TopCat.ofHom (sphereBundleHomotopyEquiv F E hnorm).toFun = sphereBundleInclusion F E :=
  TopCat.ext fun v ↦ Subtype.ext (coe_sphereBundleHomotopyEquiv F E hnorm v)

/-- The ambient component of the inclusion `(D(E), S(E)) ⟶ (E, E₀)` is the homotopy equivalence
`D(E) ≃ₕ E`. -/
private theorem discSpherePairMap_fst (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    TopPair.Hom.fst (discSpherePairMap F E) =
      TopCat.ofHom (discBundleHomotopyEquiv F E hnorm).toFun := by
  ext v
  exact (coe_discBundleHomotopyEquiv F E hnorm v).symm

/-- **The inclusion `S(E) → E₀` induces isomorphisms on cohomology** with arbitrary coefficients,
in every degree: it is a homotopy equivalence (`TauCeti.sphereBundleHomotopyEquiv`). -/
theorem isIso_singularCohomologyMap_sphereBundleInclusion
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (sphereBundleInclusion F E) n) := by
  rw [← ofHom_sphereBundleHomotopyEquiv F E hnorm]
  exact (sphereBundleHomotopyEquiv F E hnorm).isIso_singularCohomologyMap R k M n

/-- **The disc-sphere pair computes the cohomology of the Thom pair.** For a real vector bundle
whose fibre norm is continuous on the total space, the inclusion `(D(E), S(E)) ⟶ (E, E₀)` induces
isomorphisms `Hⁿ(E, E₀) ≅ Hⁿ(D(E), S(E))` on relative singular cohomology with arbitrary
coefficients, in every degree. -/
theorem isIso_singularCohomologyMap_discSpherePairMap
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (discSpherePairMap F E) n) := by
  refine TopPair.isIso_singularCohomologyMap_of_forall_isIso _ (fun m ↦ ?_) (fun m ↦ ?_) n
  · rw [discSpherePairMap_fst F E hnorm]
    exact (discBundleHomotopyEquiv F E hnorm).isIso_singularCohomologyMap R k M m
  · rw [discSpherePairMap_snd]
    exact isIso_singularCohomologyMap_sphereBundleInclusion F E hnorm R k M m

/-- **The disc-sphere pair computes the homology of the Thom pair.** For a real vector bundle
whose fibre norm is continuous on the total space, the inclusion `(D(E), S(E)) ⟶ (E, E₀)` induces
isomorphisms `Hₙ(D(E), S(E)) ≅ Hₙ(E, E₀)` on relative singular homology with arbitrary
coefficients, in every degree. -/
theorem isIso_singularHomologyMap_discSpherePairMap
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (discSpherePairMap F E) R n) :=
  TopPair.isIso_singularHomologyMap_of_homotopyEquiv _ _ _ (discSpherePairMap_fst F E hnorm)
    ((discSpherePairMap_snd F E).trans (ofHom_sphereBundleHomotopyEquiv F E hnorm).symm) R n

section Cohomology

variable (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C} {k : Type*} [Ring k]
  [Linear k C] {M : C}

/-- Restricting a class of `E₀` to `S(E)` and pulling it back along the normalization
`E₀ → S(E)` gives the class back. -/
@[simp]
theorem singularCohomologyMap_sphereBundleInclusion_normalization_apply {n : ℕ}
    (y : (thomPair F E).snd.singularCohomology R k M n) :
    TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) n
      (TopCat.singularCohomologyMap (sphereBundleInclusion F E) n y) = y := by
  have h := ((sphereBundleHomotopyEquiv F E hnorm).singularCohomologyIso R k M n).hom_inv_id_apply y
  rw [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv, ofHom_sphereBundleHomotopyEquiv] at h
  exact h

/-- Pulling a class of `S(E)` back along the normalization `E₀ → S(E)` and restricting it to `S(E)`
gives the class back. -/
@[simp]
theorem singularCohomologyMap_sphereBundleNormalization_inclusion_apply {n : ℕ}
    (y : (TopCat.of (sphereBundle F E)).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (sphereBundleInclusion F E) n
      (TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) n y) = y := by
  have h := ((sphereBundleHomotopyEquiv F E hnorm).singularCohomologyIso R k M n).inv_hom_id_apply y
  rw [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv, ofHom_sphereBundleHomotopyEquiv] at h
  exact h

variable (R k M)

/-- The connecting morphism `Hˡ(S(E)) ⟶ Hᵐ(E, E₀)` of the sphere bundle, `l + 1 = m`: the pullback
along the normalization `E₀ → S(E)`, which inverts the restriction `Hˡ(E₀) ≅ Hˡ(S(E))`, followed
by the connecting morphism of the Thom pair `(E, E₀)`. It is characterized by
`TauCeti.sphereBundleδ_singularCohomologyMap_sphereBundleInclusion`. -/
def sphereBundleδ (l m : ℕ) (hl : l + 1 = m) :
    (TopCat.of (sphereBundle F E)).singularCohomology R k M l ⟶
      (thomPair F E).singularCohomology R k M m :=
  TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) l ≫
    (thomPair F E).singularCohomologyδ R k M l m hl

theorem sphereBundleδ_def (l m : ℕ) (hl : l + 1 = m) :
    sphereBundleδ F E hnorm R k M l m hl =
      TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) l ≫
        (thomPair F E).singularCohomologyδ R k M l m hl :=
  (rfl)

variable {R k M} in
/-- The connecting morphism of the sphere bundle on the restriction of a class of `E₀` is the
connecting morphism of the Thom pair `(E, E₀)`. -/
@[simp]
theorem sphereBundleδ_singularCohomologyMap_sphereBundleInclusion {l m : ℕ} (hl : l + 1 = m)
    (y : (thomPair F E).snd.singularCohomology R k M l) :
    sphereBundleδ F E hnorm R k M l m hl
        (TopCat.singularCohomologyMap (sphereBundleInclusion F E) l y) =
      (thomPair F E).singularCohomologyδ R k M l m hl y := by
  rw [sphereBundleδ_def, ConcreteCategory.comp_apply,
    singularCohomologyMap_sphereBundleInclusion_normalization_apply]

include hnorm in
/-- **Exactness at the cohomology of the base, read on the sphere bundle**:
`Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(S(E))`, the Euler class map followed by the pullback along `S(E) → B`, is
exact. -/
theorem exact_eulerClass_singularCohomologyMap_sphereBundleProj (m : ℕ) :
    Function.Exact (eulerClass R k M F E m)
      (TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) m) := by
  intro y
  rw [← exact_eulerClass_singularCohomologyMap_zeroSectionComplProj R k M F E m y,
    ← sphereBundleInclusion_comp_zeroSectionComplProj, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply]
  -- The restriction `Hᵐ(E₀) ⟶ Hᵐ(S(E))` is injective.
  refine ⟨fun hy ↦ ?_, fun hy ↦ by rw [hy, map_zero]⟩
  rw [← singularCohomologyMap_sphereBundleInclusion_normalization_apply F E hnorm
    (TopCat.singularCohomologyMap (zeroSectionComplProj F E) m y), hy, map_zero]

/-- **Exactness at the cohomology of the sphere bundle**: `Hˡ(B) ⟶ Hˡ(S(E)) ⟶ Hᵐ(E, E₀)`, the
pullback along `S(E) → B` followed by the connecting morphism of the sphere bundle, is exact, for
`l + 1 = m`. -/
theorem exact_singularCohomologyMap_sphereBundleProj_sphereBundleδ (l m : ℕ) (hl : l + 1 = m) :
    Function.Exact (TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) l)
      (sphereBundleδ F E hnorm R k M l m hl) := by
  intro y
  rw [sphereBundleδ_def, ConcreteCategory.comp_apply,
    exact_singularCohomologyMap_zeroSectionComplProj_singularCohomologyδ R k M F E l m hl,
    ← sphereBundleInclusion_comp_zeroSectionComplProj]
  -- Transport exactness at `Hˡ(E₀)` along the isomorphism `Hˡ(E₀) ≅ Hˡ(S(E))`.
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
  · rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, hx,
      singularCohomologyMap_sphereBundleNormalization_inclusion_apply]
  · rw [← hx, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
      singularCohomologyMap_sphereBundleInclusion_normalization_apply]

/-- **Exactness at relative cohomology, read on the sphere bundle**:
`Hˡ(S(E)) ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B)`, the connecting morphism of the sphere bundle followed by the Euler
class map, is exact, for `l + 1 = m`. -/
theorem exact_sphereBundleδ_eulerClass (l m : ℕ) (hl : l + 1 = m) :
    Function.Exact (sphereBundleδ F E hnorm R k M l m hl) (eulerClass R k M F E m) := by
  intro y
  rw [exact_singularCohomologyδ_eulerClass R k M F E l m hl]
  -- Transport exactness at `Hᵐ(E, E₀)` along the isomorphism `Hˡ(E₀) ≅ Hˡ(S(E))`.
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (sphereBundleInclusion F E) l x, ?_⟩,
    fun ⟨x, hx⟩ ↦ ⟨TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) l x, hx⟩⟩
  rwa [sphereBundleδ_singularCohomologyMap_sphereBundleInclusion]

include hnorm in
/-- The Euler class map followed by the pullback along `S(E) → B` is zero. -/
@[reassoc (attr := simp)]
theorem eulerClass_comp_singularCohomologyMap_sphereBundleProj (m : ℕ) :
    eulerClass R k M F E m ≫ TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) m =
      0 := by
  ext y
  exact (exact_eulerClass_singularCohomologyMap_sphereBundleProj F E hnorm R k M
    m).apply_apply_eq_zero y

/-- The pullback along `S(E) → B` followed by the connecting morphism of the sphere bundle is
zero. -/
@[reassoc (attr := simp)]
theorem singularCohomologyMap_sphereBundleProj_comp_sphereBundleδ (l m : ℕ) (hl : l + 1 = m) :
    TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) l ≫
      sphereBundleδ F E hnorm R k M l m hl = 0 := by
  ext y
  exact (exact_singularCohomologyMap_sphereBundleProj_sphereBundleδ F E hnorm R k M l m
    hl).apply_apply_eq_zero y

/-- The connecting morphism of the sphere bundle followed by the Euler class map is zero. -/
@[reassoc (attr := simp)]
theorem sphereBundleδ_comp_eulerClass (l m : ℕ) (hl : l + 1 = m) :
    sphereBundleδ F E hnorm R k M l m hl ≫ eulerClass R k M F E m = 0 := by
  ext y
  exact (exact_sphereBundleδ_eulerClass F E hnorm R k M l m hl).apply_apply_eq_zero y

end Cohomology

end TauCeti
