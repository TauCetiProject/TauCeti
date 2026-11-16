/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Topology.VectorBundle.EulerClass
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.VectorBundle.Smul

/-!
# Disc and sphere bundles and the Thom pair

Let `E → B` be a real vector bundle whose fibres carry norms, such that the fibre norm is a
continuous function on the total space; for instance a continuous Riemannian vector bundle
(`TauCeti.continuous_norm_bundle`). Its unit disc bundle `D(E)` and unit sphere bundle `S(E)` are
the vectors of norm at most one and exactly one (`TauCeti.discBundle`, `TauCeti.sphereBundle`),
both closed in `TotalSpace F E` (`TauCeti.isClosed_discBundle`, `TauCeti.isClosed_sphereBundle`).
They project continuously onto the base (`TauCeti.discBundleProj`, `TauCeti.sphereBundleProj`), and
in rank zero (`Subsingleton` fibres or `Module.finrank 𝕜 F = 0`) the sphere bundle is empty while
the disc bundle is homeomorphic to `B` (`TauCeti.discBundleHomeomorphBaseOfSubsingleton`,
`TauCeti.discBundleHomeomorphBaseOfFinrankZero`).

Radial rescaling compares them with the Thom pair `(E, E₀)` of the bundle, where `E₀` is the
complement of the zero section:

* the inclusion `D(E) → E` is a homotopy equivalence, with homotopy inverse the radial retraction
  `v ↦ v / max 1 ‖v‖` (`TauCeti.discBundleHomotopyEquiv`);
* the inclusion `S(E) → E₀` is a homotopy equivalence, with homotopy inverse the normalization
  `v ↦ v / ‖v‖` (`TauCeti.sphereBundleHomotopyEquiv`).

In both cases the homotopy is the straight line from the identity to the retraction, which only
rescales each vector by a positive factor. In general they do not combine into a homotopy
equivalence of pairs: when some fibre is nonzero, a continuous retraction of `E` onto `D(E)`
cannot carry all of `E₀` into `S(E)`. Comparing the long exact sequences of the two pairs
instead, the inclusion of pairs `(D(E), S(E)) ⟶ (E, E₀)` (`TauCeti.discSpherePairMap`) induces
isomorphisms on relative singular cohomology with arbitrary coefficients in every degree
(`TauCeti.isIso_singularCohomologyMap_discSpherePairMap`).

So Thom classes may be read on the disc-sphere pair `(D(E), S(E))`, and the cohomology of the
deleted total space `E₀` in the long exact sequence of the Thom pair is that of the sphere bundle,
as in the Gysin sequence. No orientation, finite-dimensionality or condition on the base is
needed. The rank zero case is included: there `S(E)` and `E₀` are empty and `D(E) = E`.

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

/-- When every fibre is a subsingleton (for instance in rank zero), the unit disc bundle is the
whole total space. -/
theorem discBundle_eq_univ_of_subsingleton [∀ b, Subsingleton (E b)] :
    discBundle F E = univ :=
  eq_univ_of_forall fun v ↦ by simp [Subsingleton.elim v.2 0]

/-- When every fibre is a subsingleton (for instance in rank zero), the unit sphere bundle is
empty. -/
theorem sphereBundle_eq_empty_of_subsingleton [∀ b, Subsingleton (E b)] :
    sphereBundle F E = ∅ :=
  eq_empty_of_forall_notMem fun v hv ↦ by
    simpa [Subsingleton.elim v.2 0] using mem_sphereBundle.1 hv

variable [TopologicalSpace (TotalSpace F E)]

/-- The unit disc bundle is closed in the total space when the fibre norm is continuous. -/
theorem isClosed_discBundle (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsClosed (discBundle F E) := by
  have h : discBundle F E = {v | ‖v.2‖ ≤ 1} := Set.ext fun _ ↦ mem_discBundle
  exact h ▸ isClosed_le hnorm continuous_const

/-- The unit sphere bundle is closed in the total space when the fibre norm is continuous. -/
theorem isClosed_sphereBundle (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsClosed (sphereBundle F E) := by
  have h : sphereBundle F E = {v | ‖v.2‖ = 1} := Set.ext fun _ ↦ mem_sphereBundle
  exact h ▸ isClosed_eq hnorm continuous_const

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

end Proj

section DiscBundleBasic

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- The projection `D(E) → B` of the unit disc bundle of a bundle with normed fibres. -/
def discBundleProj : C(discBundle F E, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj,
    (FiberBundle.continuous_proj F E).comp continuous_subtype_val⟩

@[simp]
theorem discBundleProj_apply (v : discBundle F E) :
    discBundleProj F E v = (v : TotalSpace F E).proj :=
  (rfl)

/-- **Rank-zero disc bundle homeomorphism.** When every bundle fibre is a subsingleton, the
projection `discBundleProj F E : D(E) → B` is a homeomorphism, with inverse the zero section. -/
def discBundleHomeomorphBaseOfSubsingleton [∀ b, Subsingleton (E b)] :
    discBundle F E ≃ₜ B where
  toFun := discBundleProj F E
  invFun b := ⟨TotalSpace.mk' F b 0, by simp⟩
  left_inv := by
    rintro ⟨⟨b, u⟩, _⟩
    exact Subtype.ext (TotalSpace.ext rfl (heq_of_eq (Subsingleton.elim 0 u)))
  right_inv _ := rfl
  continuous_toFun := (discBundleProj F E).continuous
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_iff_continuousAt.2 fun b₀ ↦ ?_) _
    have : Subsingleton F := (FiberBundle.homeomorphAt F E b₀).symm.injective.subsingleton
    rw [FiberBundle.continuousAt_totalSpace]
    exact ⟨continuousAt_id,
      (continuousAt_const (y := (trivializationAt F E b₀ ⟨b₀, 0⟩).2)).congr
        (Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _)⟩

@[simp]
theorem discBundleHomeomorphBaseOfSubsingleton_apply [∀ b, Subsingleton (E b)]
    (v : discBundle F E) :
    discBundleHomeomorphBaseOfSubsingleton F E v = (v : TotalSpace F E).proj :=
  (rfl)

@[simp]
theorem coe_discBundleHomeomorphBaseOfSubsingleton_symm_apply [∀ b, Subsingleton (E b)] (b : B) :
    ((discBundleHomeomorphBaseOfSubsingleton F E).symm b : TotalSpace F E) =
      TotalSpace.mk' F b 0 :=
  (rfl)

variable {𝕜 : Type*} [Ring 𝕜] [StrongRankCondition 𝕜] [IsDomain 𝕜]
  [AddCommGroup F] [Module 𝕜 F] [Module.Finite 𝕜 F] [Module.IsTorsionFree 𝕜 F]

/-- In rank zero (`Module.finrank 𝕜 F = 0`), the unit disc bundle is the whole total space. -/
theorem discBundle_eq_univ_of_finrank_eq_zero (hF : Module.finrank 𝕜 F = 0) :
    discBundle F E = univ := by
  have : Subsingleton F := Module.finrank_zero_iff.1 hF
  have (b : B) : Subsingleton (E b) := (FiberBundle.homeomorphAt F E b).injective.subsingleton
  exact discBundle_eq_univ_of_subsingleton F E

/-- In rank zero (`Module.finrank 𝕜 F = 0`), the unit sphere bundle is empty. -/
theorem sphereBundle_eq_empty_of_finrank_eq_zero (hF : Module.finrank 𝕜 F = 0) :
    sphereBundle F E = ∅ := by
  have : Subsingleton F := Module.finrank_zero_iff.1 hF
  have (b : B) : Subsingleton (E b) := (FiberBundle.homeomorphAt F E b).injective.subsingleton
  exact sphereBundle_eq_empty_of_subsingleton F E

/-- In rank zero (`Module.finrank 𝕜 F = 0`), the unit disc bundle is homeomorphic to the base `B`
via the bundle projection, with inverse the zero section. -/
def discBundleHomeomorphBaseOfFinrankZero (hF : Module.finrank 𝕜 F = 0) :
    discBundle F E ≃ₜ B :=
  have : Subsingleton F := Module.finrank_zero_iff.1 hF
  have (b : B) : Subsingleton (E b) := (FiberBundle.homeomorphAt F E b).injective.subsingleton
  discBundleHomeomorphBaseOfSubsingleton F E

@[simp]
theorem discBundleHomeomorphBaseOfFinrankZero_apply (hF : Module.finrank 𝕜 F = 0)
    (v : discBundle F E) :
    discBundleHomeomorphBaseOfFinrankZero F E hF v = (v : TotalSpace F E).proj :=
  (rfl)

@[simp]
theorem coe_discBundleHomeomorphBaseOfFinrankZero_symm_apply (hF : Module.finrank 𝕜 F = 0)
    (b : B) :
    ((discBundleHomeomorphBaseOfFinrankZero F E hF).symm b : TotalSpace F E) =
      TotalSpace.mk' F b 0 :=
  (rfl)

end DiscBundleBasic

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

/-- The ambient component of the inclusion `(D(E), S(E)) ⟶ (E, E₀)` is the homotopy equivalence
`D(E) ≃ₕ E`. -/
private theorem discSpherePairMap_fst (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    TopPair.Hom.fst (discSpherePairMap F E) =
      TopCat.ofHom (discBundleHomotopyEquiv F E hnorm).toFun := by
  ext v
  exact (coe_discBundleHomotopyEquiv F E hnorm v).symm

/-- The subspace component of the inclusion `(D(E), S(E)) ⟶ (E, E₀)` is the homotopy equivalence
`S(E) ≃ₕ E₀`. -/
private theorem discSpherePairMap_snd (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    TopPair.Hom.snd (discSpherePairMap F E) =
      TopCat.ofHom (sphereBundleHomotopyEquiv F E hnorm).toFun := by
  ext v
  exact Subtype.ext (coe_sphereBundleHomotopyEquiv F E hnorm v).symm

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
  · rw [discSpherePairMap_snd F E hnorm]
    exact (sphereBundleHomotopyEquiv F E hnorm).isIso_singularCohomologyMap R k M m

/-- **The disc-sphere pair computes the homology of the Thom pair.** For a real vector bundle
whose fibre norm is continuous on the total space, the inclusion `(D(E), S(E)) ⟶ (E, E₀)` induces
isomorphisms `Hₙ(D(E), S(E)) ≅ Hₙ(E, E₀)` on relative singular homology with arbitrary
coefficients, in every degree. -/
theorem isIso_singularHomologyMap_discSpherePairMap
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (discSpherePairMap F E) R n) :=
  TopPair.isIso_singularHomologyMap_of_homotopyEquiv _ _ _ (discSpherePairMap_fst F E hnorm)
    (discSpherePairMap_snd F E hnorm) R n

end TauCeti
