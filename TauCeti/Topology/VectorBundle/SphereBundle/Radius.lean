/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
import TauCeti.Topology.VectorBundle.Smul

/-!
# Disc and sphere bundles of prescribed radius

Let `E → B` be a real vector bundle whose fibres carry norms, and let `r : B → ℝ` be a radius
function on the base. The closed disc bundle `D_r(E)` and sphere bundle `S_r(E)` of radius `r`
consist of the vectors of norm at most `r(π(v))` and equal to `r(π(v))`
(`TauCeti.discBundleOfRadius`, `TauCeti.sphereBundleOfRadius`), forming the topological pair
`(D_r(E), S_r(E))` (`TauCeti.discSpherePairOfRadius`). For the constant radius `1`, `D_1(E)` and
`S_1(E)` agree with the unit disc bundle and unit sphere bundle of
`TauCeti.Topology.VectorBundle.SphereBundle.Basic` (`TauCeti.discBundleOfRadius_const_one`,
`TauCeti.sphereBundleOfRadius_const_one`).

When `r` is continuous and everywhere positive, fibrewise multiplication by `r ∘ π` and `(r ∘ π)⁻¹`
defines homeomorphisms `D(E) ≃ₜ D_r(E)` (`TauCeti.discBundleHomeomorphOfRadius`) and
`S(E) ≃ₜ S_r(E)` (`TauCeti.sphereBundleHomeomorphOfRadius`), and hence an isomorphism of pairs
`(D(E), S(E)) ≅ (D_r(E), S_r(E))` (`TauCeti.discSpherePairIsoOfRadius`). Neither homeomorphism
needs continuity of the fibre norm on the total space: scalar multiplication on a topological
vector bundle is jointly continuous (`Continuous.smul_totalSpace`).

In the Thom pair `(E, E₀)`, the straight-line rescaling `((1 - t) + t · r(π(v))) • v` stays off
the zero section at every time `t ∈ [0, 1]` because `(0, ∞)` is convex. It therefore gives a
homotopy of maps of pairs (`TauCeti.discSpherePairOfRadiusHomotopy`) between the unit inclusion
`(D(E), S(E)) ⟶ (E, E₀)` and the composite `(D(E), S(E)) ≅ (D_r(E), S_r(E)) ⟶ (E, E₀)`.
Consequently the rescaling isomorphism commutes with the induced maps to and from the Thom pair on
relative singular homology and cohomology
(`TauCeti.singularHomologyMap_discSpherePairIsoOfRadius_hom_comp`,
`TauCeti.singularCohomologyMap_discSpherePairOfRadiusMap_comp_hom`), and when the fibre norm is
continuous on `E`, the inclusion `(D_r(E), S_r(E)) ⟶ (E, E₀)` induces isomorphisms on relative
singular homology and cohomology in every degree
(`TauCeti.isIso_singularHomologyMap_discSpherePairOfRadiusMap`,
`TauCeti.isIso_singularCohomologyMap_discSpherePairOfRadiusMap`).

## Main definitions and results

* `TauCeti.discBundleOfRadius`, `TauCeti.sphereBundleOfRadius`, `TauCeti.discSpherePairOfRadius`:
  the closed disc bundle, sphere bundle and disc-sphere pair `(D_r(E), S_r(E))` of radius `r`.
* `TauCeti.discSpherePairOfRadiusMap`: the inclusion `(D_r(E), S_r(E)) ⟶ (E, E₀)` for nowhere-zero
  radius `r`.
* `TauCeti.discBundleHomeomorphOfRadius`, `TauCeti.sphereBundleHomeomorphOfRadius`,
  `TauCeti.discSpherePairIsoOfRadius`: radial rescaling identifications with the unit bundles and
  pair for continuous positive `r`.
* `TauCeti.discSpherePairOfRadiusHomotopy`: homotopy compatibility with the Thom pair.
* `TauCeti.isIso_singularHomologyMap_discSpherePairOfRadiusMap`,
  `TauCeti.isIso_singularCohomologyMap_discSpherePairOfRadiusMap`: `(D_r(E), S_r(E)) ⟶ (E, E₀)`
  induces isomorphisms on relative singular homology and cohomology.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 and §12.
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set
open scoped unitInterval ContinuousMap

universe w v u

namespace TauCeti

section Sets

variable {B : Type w} (F : Type*) (E : B → Type w) [∀ b, NormedAddCommGroup (E b)]

/-- The closed disc bundle `D_r(E)` of radius `r : B → ℝ` in a bundle with normed fibres: the
vectors `v` satisfying `‖v.2‖ ≤ r v.proj`. -/
def discBundleOfRadius (r : B → ℝ) : Set (TotalSpace F E) :=
  {v | ‖v.2‖ ≤ r v.proj}

/-- The sphere bundle `S_r(E)` of radius `r : B → ℝ` in a bundle with normed fibres: the vectors
`v` satisfying `‖v.2‖ = r v.proj`. -/
def sphereBundleOfRadius (r : B → ℝ) : Set (TotalSpace F E) :=
  {v | ‖v.2‖ = r v.proj}

variable {F E} in
@[simp]
theorem mem_discBundleOfRadius {r : B → ℝ} {v : TotalSpace F E} :
    v ∈ discBundleOfRadius F E r ↔ ‖v.2‖ ≤ r v.proj :=
  Iff.rfl

variable {F E} in
@[simp]
theorem mem_sphereBundleOfRadius {r : B → ℝ} {v : TotalSpace F E} :
    v ∈ sphereBundleOfRadius F E r ↔ ‖v.2‖ = r v.proj :=
  Iff.rfl

/-- At constant radius `1`, `TauCeti.discBundleOfRadius` is the unit disc bundle. -/
@[simp]
theorem discBundleOfRadius_const_one : discBundleOfRadius F E (fun _ ↦ 1) = discBundle F E :=
  Set.ext fun _ ↦ mem_discBundle.symm

/-- At constant radius `1`, `TauCeti.sphereBundleOfRadius` is the unit sphere bundle. -/
@[simp]
theorem sphereBundleOfRadius_const_one : sphereBundleOfRadius F E (fun _ ↦ 1) = sphereBundle F E :=
  Set.ext fun _ ↦ mem_sphereBundle.symm

/-- The sphere bundle of radius `r` lies in the closed disc bundle of radius `r`. -/
theorem sphereBundleOfRadius_subset_discBundleOfRadius (r : B → ℝ) :
    sphereBundleOfRadius F E r ⊆ discBundleOfRadius F E r :=
  fun _ hv ↦ (mem_sphereBundleOfRadius.1 hv).le

/-- When `r` is nowhere zero, the sphere bundle of radius `r` lies in the complement `E₀` of the
zero section. -/
theorem sphereBundleOfRadius_subset_zeroSectionCompl {r : B → ℝ} (hr : ∀ b, r b ≠ 0) :
    sphereBundleOfRadius F E r ⊆ zeroSectionCompl F E :=
  fun v hv ↦ mem_zeroSectionCompl.2 <|
    norm_ne_zero_iff.1 ((mem_sphereBundleOfRadius.1 hv).symm ▸ hr v.proj)

variable {F E} in
/-- Enlarging the radius function enlarges the closed disc bundle. -/
theorem discBundleOfRadius_mono {r₁ r₂ : B → ℝ} (h : r₁ ≤ r₂) :
    discBundleOfRadius F E r₁ ⊆ discBundleOfRadius F E r₂ :=
  fun v hv ↦ (mem_discBundleOfRadius.1 hv).trans (h v.proj)

variable [TopologicalSpace (TotalSpace F E)]

/-- The disc-sphere pair `(D_r(E), S_r(E))` of radius `r : B → ℝ` in a bundle with normed fibres. -/
abbrev discSpherePairOfRadius (r : B → ℝ) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
    (sphereBundleOfRadius_subset_discBundleOfRadius F E r)

/-- At constant radius `1`, `TauCeti.discSpherePairOfRadius` is the unit disc-sphere pair. -/
theorem discSpherePairOfRadius_const_one :
    discSpherePairOfRadius F E (fun _ ↦ 1) = discSpherePair F E :=
  TopPair.ofInclusion_congr _ _ (sphereBundleOfRadius_const_one F E)
    (discBundleOfRadius_const_one F E)

/-- The inclusion `(D_r(E), S_r(E)) ⟶ (E, E₀)` of the disc-sphere pair of a nowhere-zero radius `r`
into the Thom pair. -/
def discSpherePairOfRadiusMap {r : B → ℝ} (hr : ∀ b, r b ≠ 0) :
    discSpherePairOfRadius F E r ⟶ thomPair F E :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom (ContinuousMap.inclusion (sphereBundleOfRadius_subset_zeroSectionCompl F E hr)))
    (by ext; rfl)

@[simp]
theorem discSpherePairOfRadiusMap_fst_apply {r : B → ℝ} (hr : ∀ b, r b ≠ 0)
    (v : discBundleOfRadius F E r) :
    TopPair.Hom.fst (discSpherePairOfRadiusMap F E hr) v = v.1 :=
  (rfl)

@[simp]
theorem discSpherePairOfRadiusMap_snd_apply {r : B → ℝ} (hr : ∀ b, r b ≠ 0)
    (v : sphereBundleOfRadius F E r) :
    (TopPair.Hom.snd (discSpherePairOfRadiusMap F E hr) v).1 = v.1 :=
  (rfl)

end Sets

section Closed

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- If the fibre norm is continuous on the total space and `r` is continuous on the base, the
closed disc bundle `D_r(E)` is closed in `E`. -/
theorem isClosed_discBundleOfRadius (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {r : B → ℝ} (hr : Continuous r) : IsClosed (discBundleOfRadius F E r) :=
  isClosed_le hnorm (hr.comp (FiberBundle.continuous_proj F E))

/-- If the fibre norm is continuous on the total space and `r` is continuous on the base, the
sphere bundle `S_r(E)` is closed in `E`. -/
theorem isClosed_sphereBundleOfRadius (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {r : B → ℝ} (hr : Continuous r) : IsClosed (sphereBundleOfRadius F E r) :=
  isClosed_eq hnorm (hr.comp (FiberBundle.continuous_proj F E))

/-- If the fibre norm is continuous on the total space, the unit disc bundle `D(E)` is closed in
`E`. -/
theorem isClosed_discBundle (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsClosed (discBundle F E) := by
  rw [← discBundleOfRadius_const_one]
  exact isClosed_discBundleOfRadius F E hnorm continuous_const

/-- If the fibre norm is continuous on the total space, the unit sphere bundle `S(E)` is closed in
`E`. -/
theorem isClosed_sphereBundle (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsClosed (sphereBundle F E) := by
  rw [← sphereBundleOfRadius_const_one]
  exact isClosed_sphereBundleOfRadius F E hnorm continuous_const

end Closed

section Rescale

section RescaleMem

variable {B : Type w} (F : Type*) (E : B → Type w) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, NormedSpace ℝ (E b)]

private lemma rescale_mem_discBundleOfRadius {r : B → ℝ} (hrpos : ∀ b, 0 < r b)
    (v : discBundle F E) :
    TotalSpace.mk' F v.1.proj (r v.1.proj • v.1.2) ∈ discBundleOfRadius F E r := by
  rw [mem_discBundleOfRadius]
  dsimp only [TotalSpace.mk']
  rw [norm_smul, Real.norm_of_nonneg (hrpos v.1.proj).le]
  exact mul_le_of_le_one_right (hrpos v.1.proj).le (mem_discBundle.1 v.2)

private lemma invRescale_mem_discBundle {r : B → ℝ} (hrpos : ∀ b, 0 < r b)
    (v : discBundleOfRadius F E r) :
    TotalSpace.mk' F v.1.proj ((r v.1.proj)⁻¹ • v.1.2) ∈ discBundle F E := by
  have h := hrpos v.1.proj
  rw [mem_discBundle, norm_smul, norm_inv, Real.norm_of_nonneg h.le, inv_mul_le_iff₀ h, mul_one]
  exact mem_discBundleOfRadius.1 v.2

private lemma rescale_mem_sphereBundleOfRadius {r : B → ℝ} (hrpos : ∀ b, 0 < r b)
    (v : sphereBundle F E) :
    TotalSpace.mk' F v.1.proj (r v.1.proj • v.1.2) ∈ sphereBundleOfRadius F E r := by
  rw [mem_sphereBundleOfRadius]
  dsimp only [TotalSpace.mk']
  rw [norm_smul, Real.norm_of_nonneg (hrpos v.1.proj).le, mem_sphereBundle.1 v.2, mul_one]

private lemma invRescale_mem_sphereBundle {r : B → ℝ} (hrpos : ∀ b, 0 < r b)
    (v : sphereBundleOfRadius F E r) :
    TotalSpace.mk' F v.1.proj ((r v.1.proj)⁻¹ • v.1.2) ∈ sphereBundle F E := by
  have h := hrpos v.1.proj
  rw [mem_sphereBundle, norm_smul, norm_inv, Real.norm_of_nonneg h.le,
    mem_sphereBundleOfRadius.1 v.2, inv_mul_cancel₀ h.ne']

private lemma homotopyRescale_mem_zeroSectionCompl [TopologicalSpace (TotalSpace F E)]
    {r : B → ℝ} (hrpos : ∀ b, 0 < r b) (p : I × (discSpherePair F E).snd) :
    TotalSpace.mk' F p.2.1.proj ((1 - (p.1 : ℝ) + (p.1 : ℝ) * r p.2.1.proj) • p.2.1.2) ∈
      zeroSectionCompl F E := by
  have hv : p.2.1.2 ≠ 0 :=
    norm_ne_zero_iff.1 ((mem_sphereBundle.1 p.2.2).symm ▸ one_ne_zero)
  exact mem_zeroSectionCompl.2 <| smul_ne_zero (by
    simpa using (convex_Ioi (0 : ℝ) one_pos (hrpos p.2.1.proj)
      (sub_nonneg.2 p.1.2.2) p.1.2.1 (sub_add_cancel 1 _)).ne') hv

end RescaleMem

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Fibrewise rescaling `v ↦ r(π(v)) • v` identifies the unit disc bundle `D(E)` with the closed
disc bundle `D_r(E)` of any continuous positive radius `r : B → ℝ`. -/
def discBundleHomeomorphOfRadius {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b) :
    discBundle F E ≃ₜ discBundleOfRadius F E r where
  toFun v := ⟨TotalSpace.mk' F v.1.proj (r v.1.proj • v.1.2),
    rescale_mem_discBundleOfRadius F E hrpos v⟩
  invFun v := ⟨TotalSpace.mk' F v.1.proj ((r v.1.proj)⁻¹ • v.1.2),
    invRescale_mem_discBundle F E hrpos v⟩
  left_inv v := Subtype.ext <| by
    obtain ⟨⟨b, x⟩, _⟩ := v
    simp [TotalSpace.mk', inv_mul_cancel₀ (hrpos b).ne', smul_smul]
  right_inv v := Subtype.ext <| by
    obtain ⟨⟨b, x⟩, _⟩ := v
    simp [TotalSpace.mk', mul_inv_cancel₀ (hrpos b).ne', smul_smul]
  continuous_toFun := Continuous.subtype_mk
    (Continuous.smul_totalSpace (hr.comp ((FiberBundle.continuous_proj F E).comp
      continuous_subtype_val)) continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.smul_totalSpace ((hr.comp ((FiberBundle.continuous_proj F E).comp
      continuous_subtype_val)).inv₀ fun v ↦ (hrpos v.1.proj).ne') continuous_subtype_val) _

@[simp]
theorem coe_discBundleHomeomorphOfRadius_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : discBundle F E) :
    (discBundleHomeomorphOfRadius F E hr hrpos v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (r v.1.proj • v.1.2) :=
  (rfl)

@[simp]
theorem coe_discBundleHomeomorphOfRadius_symm_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : discBundleOfRadius F E r) :
    ((discBundleHomeomorphOfRadius F E hr hrpos).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj ((r v.1.proj)⁻¹ • v.1.2) :=
  (rfl)

/-- Fibrewise rescaling `v ↦ r(π(v)) • v` identifies the unit sphere bundle `S(E)` with the sphere
bundle `S_r(E)` of any continuous positive radius `r : B → ℝ`. -/
def sphereBundleHomeomorphOfRadius {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b) :
    sphereBundle F E ≃ₜ sphereBundleOfRadius F E r where
  toFun v := ⟨TotalSpace.mk' F v.1.proj (r v.1.proj • v.1.2),
    rescale_mem_sphereBundleOfRadius F E hrpos v⟩
  invFun v := ⟨TotalSpace.mk' F v.1.proj ((r v.1.proj)⁻¹ • v.1.2),
    invRescale_mem_sphereBundle F E hrpos v⟩
  left_inv v := Subtype.ext <| by
    obtain ⟨⟨b, x⟩, _⟩ := v
    simp [TotalSpace.mk', inv_mul_cancel₀ (hrpos b).ne', smul_smul]
  right_inv v := Subtype.ext <| by
    obtain ⟨⟨b, x⟩, _⟩ := v
    simp [TotalSpace.mk', mul_inv_cancel₀ (hrpos b).ne', smul_smul]
  continuous_toFun := Continuous.subtype_mk
    (Continuous.smul_totalSpace (hr.comp ((FiberBundle.continuous_proj F E).comp
      continuous_subtype_val)) continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.smul_totalSpace ((hr.comp ((FiberBundle.continuous_proj F E).comp
      continuous_subtype_val)).inv₀ fun v ↦ (hrpos v.1.proj).ne') continuous_subtype_val) _

@[simp]
theorem coe_sphereBundleHomeomorphOfRadius_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : sphereBundle F E) :
    (sphereBundleHomeomorphOfRadius F E hr hrpos v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (r v.1.proj • v.1.2) :=
  (rfl)

@[simp]
theorem coe_sphereBundleHomeomorphOfRadius_symm_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : sphereBundleOfRadius F E r) :
    ((sphereBundleHomeomorphOfRadius F E hr hrpos).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj ((r v.1.proj)⁻¹ • v.1.2) :=
  (rfl)

/-- **Radial rescaling of the disc-sphere pair.** For a continuous positive radius `r : B → ℝ`,
fibrewise multiplication by `r ∘ π` defines an isomorphism of pairs
`(D(E), S(E)) ≅ (D_r(E), S_r(E))`, with inverse given by multiplication by `(r ∘ π)⁻¹`. -/
def discSpherePairIsoOfRadius {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b) :
    discSpherePair F E ≅ discSpherePairOfRadius F E r where
  hom := TopPair.ofHom (TopCat.ofHom (discBundleHomeomorphOfRadius F E hr hrpos))
    (TopCat.ofHom (sphereBundleHomeomorphOfRadius F E hr hrpos)) (by ext; rfl)
  inv := TopPair.ofHom (TopCat.ofHom (discBundleHomeomorphOfRadius F E hr hrpos).symm)
    (TopCat.ofHom (sphereBundleHomeomorphOfRadius F E hr hrpos).symm) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ <| TopCat.ext fun v ↦
    (discBundleHomeomorphOfRadius F E hr hrpos).symm_apply_apply v
  inv_hom_id := TopPair.hom_ext_of_fst _ <| TopCat.ext fun v ↦
    (discBundleHomeomorphOfRadius F E hr hrpos).apply_symm_apply v

@[simp]
theorem discSpherePairIsoOfRadius_hom_fst_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : discBundle F E) :
    TopPair.Hom.fst (discSpherePairIsoOfRadius F E hr hrpos).hom v =
      discBundleHomeomorphOfRadius F E hr hrpos v :=
  (rfl)

@[simp]
theorem discSpherePairIsoOfRadius_inv_fst_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : discBundleOfRadius F E r) :
    TopPair.Hom.fst (discSpherePairIsoOfRadius F E hr hrpos).inv v =
      (discBundleHomeomorphOfRadius F E hr hrpos).symm v :=
  (rfl)

@[simp]
theorem discSpherePairIsoOfRadius_hom_snd_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : sphereBundle F E) :
    TopPair.Hom.snd (discSpherePairIsoOfRadius F E hr hrpos).hom v =
      sphereBundleHomeomorphOfRadius F E hr hrpos v :=
  (rfl)

@[simp]
theorem discSpherePairIsoOfRadius_inv_snd_apply {r : B → ℝ} (hr : Continuous r)
    (hrpos : ∀ b, 0 < r b) (v : sphereBundleOfRadius F E r) :
    TopPair.Hom.snd (discSpherePairIsoOfRadius F E hr hrpos).inv v =
      (sphereBundleHomeomorphOfRadius F E hr hrpos).symm v :=
  (rfl)

/-- Straight-line rescaling `((1 - t) + t · r(π(v))) • v` on `D(E)` stays off the zero section on
`S(E)` at every time `t ∈ [0, 1]`, giving a homotopy of maps of pairs between the unit inclusion
`(D(E), S(E)) ⟶ (E, E₀)` and `(D(E), S(E)) ≅ (D_r(E), S_r(E)) ⟶ (E, E₀)`. -/
def discSpherePairOfRadiusHomotopy {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b) :
    TopPair.Homotopy (discSpherePairMap F E)
      ((discSpherePairIsoOfRadius F E hr hrpos).hom ≫
        discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') where
  fst :=
    { toFun p := TotalSpace.mk' F p.2.1.proj
        ((1 - (p.1 : ℝ) + (p.1 : ℝ) * r p.2.1.proj) • p.2.1.2)
      continuous_toFun := by
        have ht : Continuous fun p : I × (discSpherePair F E).fst ↦ (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have hv : Continuous fun p : I × (discSpherePair F E).fst ↦ p.2.1 :=
          continuous_subtype_val.comp continuous_snd
        exact Continuous.smul_totalSpace (F := F) (E := E) ((continuous_const.sub ht).add
          (ht.mul (hr.comp ((FiberBundle.continuous_proj F E).comp hv)))) hv
      map_zero_left v := by
        simpa [TotalSpace.mk'] using (discSpherePairMap_fst_apply F E v).symm
      map_one_left v := by
        simp only [Icc.coe_one, sub_self, one_mul, zero_add]
        exact ((congrArg (TopPair.Hom.fst (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne'))
          (discSpherePairIsoOfRadius_hom_fst_apply F E hr hrpos v)).trans
          ((discSpherePairOfRadiusMap_fst_apply F E (fun b ↦ (hrpos b).ne') _).trans
            (coe_discBundleHomeomorphOfRadius_apply F E hr hrpos v))).symm }
  snd :=
    { toFun p := ⟨TotalSpace.mk' F p.2.1.proj
        ((1 - (p.1 : ℝ) + (p.1 : ℝ) * r p.2.1.proj) • p.2.1.2),
        homotopyRescale_mem_zeroSectionCompl F E hrpos p⟩
      continuous_toFun := by
        have ht : Continuous fun p : I × (discSpherePair F E).snd ↦ (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have hv : Continuous fun p : I × (discSpherePair F E).snd ↦ p.2.1 :=
          continuous_subtype_val.comp continuous_snd
        exact Continuous.subtype_mk (Continuous.smul_totalSpace (F := F) (E := E)
          ((continuous_const.sub ht).add
            (ht.mul (hr.comp ((FiberBundle.continuous_proj F E).comp hv)))) hv) _
      map_zero_left v := Subtype.ext <| by
        simpa [TotalSpace.mk'] using (discSpherePairMap_snd_apply F E v).symm
      map_one_left v := Subtype.ext <| by
        simp only [Icc.coe_one, sub_self, one_mul, zero_add]
        exact ((congrArg
          (fun x ↦ (TopPair.Hom.snd (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') x).1)
          (discSpherePairIsoOfRadius_hom_snd_apply F E hr hrpos v)).trans
          ((discSpherePairOfRadiusMap_snd_apply F E (fun b ↦ (hrpos b).ne') _).trans
            (coe_sphereBundleHomeomorphOfRadius_apply F E hr hrpos v))).symm }
  w := by ext; rfl

/-- Radial rescaling `(D(E), S(E)) ≅ (D_r(E), S_r(E))` commutes with the maps to the Thom pair
`(E, E₀)` on relative singular homology. -/
@[reassoc]
theorem singularHomologyMap_discSpherePairIsoOfRadius_hom_comp
    {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) (n : ℕ) :
    TopPair.singularHomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom R n ≫
        TopPair.singularHomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n =
      TopPair.singularHomologyMap (discSpherePairMap F E) R n := by
  rw [← TopPair.singularHomologyMap_comp]
  exact (discSpherePairOfRadiusHomotopy F E hr hrpos).symm.congr_singularHomologyMap R n

/-- Radial rescaling `(D(E), S(E)) ≅ (D_r(E), S_r(E))` commutes with the maps from the Thom pair
`(E, E₀)` on relative singular cohomology. -/
@[reassoc]
theorem singularCohomologyMap_discSpherePairOfRadiusMap_comp_hom
    {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (M : C) (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
        (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n ≫
      TopPair.singularCohomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom n =
      TopPair.singularCohomologyMap (discSpherePairMap F E) n := by
  rw [← TopPair.singularCohomologyMap_comp]
  exact (discSpherePairOfRadiusHomotopy F E hr hrpos).symm.congr_singularCohomologyMap R k M n

/-- **The disc-sphere pair of a positive continuous radius computes the homology of the Thom
pair.** When the fibre norm is continuous on `E` and `r : B → ℝ` is continuous and positive, the
inclusion `(D_r(E), S_r(E)) ⟶ (E, E₀)` induces isomorphisms `Hₙ(D_r(E), S_r(E)) ≅ Hₙ(E, E₀)` on
relative singular homology in every degree. -/
theorem isIso_singularHomologyMap_discSpherePairOfRadiusMap
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n) := by
  have := isIso_singularHomologyMap_discSpherePairMap F E hnorm R n
  have := TopPair.isIso_singularHomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom
    (discSpherePairIsoOfRadius F E hr hrpos).inv
    (by rw [Iso.hom_inv_id]; exact TopPair.Homotopy.refl _)
    (by rw [Iso.inv_hom_id]; exact TopPair.Homotopy.refl _) R n
  have : IsIso (TopPair.singularHomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom R n ≫
      TopPair.singularHomologyMap (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') R n) := by
    rw [singularHomologyMap_discSpherePairIsoOfRadius_hom_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (TopPair.singularHomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom R n) _

/-- **The disc-sphere pair of a positive continuous radius computes the cohomology of the Thom
pair.** When the fibre norm is continuous on `E` and `r : B → ℝ` is continuous and positive, the
inclusion `(D_r(E), S_r(E)) ⟶ (E, E₀)` induces isomorphisms `Hⁿ(E, E₀) ≅ Hⁿ(D_r(E), S_r(E))` on
relative singular cohomology in every degree. -/
theorem isIso_singularCohomologyMap_discSpherePairOfRadiusMap
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n) := by
  have := isIso_singularCohomologyMap_discSpherePairMap F E hnorm R k M n
  have := TopPair.isIso_singularCohomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom
    (discSpherePairIsoOfRadius F E hr hrpos).inv
    (by rw [Iso.hom_inv_id]; exact TopPair.Homotopy.refl _)
    (by rw [Iso.inv_hom_id]; exact TopPair.Homotopy.refl _) R k M n
  have : IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (discSpherePairOfRadiusMap F E fun b ↦ (hrpos b).ne') n ≫
      TopPair.singularCohomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom n) := by
    rw [singularCohomologyMap_discSpherePairOfRadiusMap_comp_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (TopPair.singularCohomologyMap (discSpherePairIsoOfRadius F E hr hrpos).hom n)

end Rescale

end TauCeti
