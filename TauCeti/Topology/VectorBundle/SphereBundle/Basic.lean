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

Let `E → B` be a real vector bundle. A **fibre gauge** on `E` is a continuous function `ρ` on the
total space which is positively homogeneous on each fibre, `ρ (t • v) = t * ρ v` for `t ≥ 0`, and
positive off the zero section (`TauCeti.IsFiberGauge`). Its disc bundle `D_ρ(E)` and sphere bundle
`S_ρ(E)` are the vectors with `ρ v ≤ 1` and `ρ v = 1` (`TauCeti.gaugeDiscBundle`,
`TauCeti.gaugeSphereBundle`). The main example is the fibre norm when it is continuous on the total
space (`TauCeti.isFiberGauge_norm`), for instance for a continuous Riemannian vector bundle
(`TauCeti.continuous_norm_bundle`); its disc and sphere bundles are the unit disc bundle `D(E)` and
the unit sphere bundle `S(E)` (`TauCeti.discBundle`, `TauCeti.sphereBundle`). Another is the
square root of a continuous function `q` which is positively homogeneous of degree two on the
fibres and positive off the zero section (`TauCeti.isFiberGauge_sqrt`), such as `v ↦ Q_b(v, v)` for
a continuous family of positive definite quadratic forms `Q_b`. Its disc bundle `{q ≤ 1}` need not
be the unit disc bundle of any norm already carried by the fibres: for instance the negative disc
bundle `{-½ Hess(v, v) ≤ ε}` of a Morse–Bott critical submanifold, where `q v = -Hess(v, v) / (2ε)`
on the negative normal bundle. The unit sphere bundle projects continuously onto the base
(`TauCeti.sphereBundleProj`).

Radial rescaling compares a gauge disc-sphere pair with the Thom pair `(E, E₀)` of the bundle,
where `E₀` is the complement of the zero section:

* the inclusion `D_ρ(E) → E` is a homotopy equivalence, with homotopy inverse the radial
  retraction `v ↦ v / max 1 (ρ v)` (`TauCeti.gaugeDiscBundleHomotopyEquiv`);
* the inclusion `S_ρ(E) → E₀` is a homotopy equivalence, with homotopy inverse the normalization
  `v ↦ v / ρ v` (`TauCeti.gaugeSphereBundleHomotopyEquiv`). For the unit sphere bundle the
  inclusion `S(E) → E₀` (`TauCeti.sphereBundleInclusion`) and the normalization `v ↦ v / ‖v‖`
  (`TauCeti.sphereBundleNormalization`) are morphisms of topological spaces, and the inclusion
  induces isomorphisms on cohomology (`TauCeti.isIso_singularCohomologyMap_sphereBundleInclusion`).

In both cases the homotopy is the straight line from the identity to the retraction, which only
rescales each vector by a positive factor. In general they do not combine into a homotopy
equivalence of pairs: when some fibre is nonzero, a continuous retraction of `E` onto `D_ρ(E)`
cannot carry all of `E₀` into `S_ρ(E)`. Comparing the long exact sequences of the two pairs
instead, the inclusion of pairs `(D_ρ(E), S_ρ(E)) ⟶ (E, E₀)` (`TauCeti.gaugeDiscSpherePairMap`)
induces isomorphisms on relative singular homology and cohomology with arbitrary coefficients in
every degree (`TauCeti.isIso_singularHomologyMap_gaugeDiscSpherePairMap` and
`TauCeti.isIso_singularCohomologyMap_gaugeDiscSpherePairMap`).

So Thom classes may be read on any gauge disc-sphere pair, and the cohomology of the deleted total
space `E₀` in the long exact sequence of the Thom pair is that of the sphere bundle, as in the
Gysin sequence: with the connecting morphism `Hˡ(S(E)) ⟶ Hˡ⁺¹(E, E₀)` of the unit sphere bundle
(`TauCeti.sphereBundleδ`), the sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(S(E)) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

of the Euler class maps, the pullback along `S(E) → B` and `TauCeti.sphereBundleδ` is exact
(`TauCeti.exact_eulerClass_singularCohomologyMap_sphereBundleProj`,
`TauCeti.exact_singularCohomologyMap_sphereBundleProj_sphereBundleδ`,
`TauCeti.exact_sphereBundleδ_eulerClass`). No orientation, finite-dimensionality, norm on the
fibres or condition on the base is needed. The rank zero case is included: there `S_ρ(E)` and `E₀`
are empty and `D_ρ(E) = E`.

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

variable {B : Type w} {F : Type*} {E : B → Type w}

/-- The disc bundle `D_ρ(E) = {ρ ≤ 1}` of a function `ρ` on the total space of a bundle, typically
a fibre gauge (`TauCeti.IsFiberGauge`). -/
def gaugeDiscBundle (ρ : TotalSpace F E → ℝ) : Set (TotalSpace F E) :=
  {v | ρ v ≤ 1}

/-- The sphere bundle `S_ρ(E) = {ρ = 1}` of a function `ρ` on the total space of a bundle,
typically a fibre gauge (`TauCeti.IsFiberGauge`). -/
def gaugeSphereBundle (ρ : TotalSpace F E → ℝ) : Set (TotalSpace F E) :=
  {v | ρ v = 1}

@[simp]
theorem mem_gaugeDiscBundle {ρ : TotalSpace F E → ℝ} {v : TotalSpace F E} :
    v ∈ gaugeDiscBundle ρ ↔ ρ v ≤ 1 :=
  Iff.rfl

@[simp]
theorem mem_gaugeSphereBundle {ρ : TotalSpace F E → ℝ} {v : TotalSpace F E} :
    v ∈ gaugeSphereBundle ρ ↔ ρ v = 1 :=
  Iff.rfl

/-- The disc bundle of the square root of a function `q` is `{q ≤ 1}`. -/
theorem gaugeDiscBundle_sqrt (q : TotalSpace F E → ℝ) :
    gaugeDiscBundle (fun v ↦ √(q v)) = {v | q v ≤ 1} := by
  ext v
  exact Real.sqrt_le_one

/-- The sphere bundle of the square root of a function `q` is `{q = 1}`. -/
theorem gaugeSphereBundle_sqrt (q : TotalSpace F E → ℝ) :
    gaugeSphereBundle (fun v ↦ √(q v)) = {v | q v = 1} := by
  ext v
  exact Real.sqrt_eq_one

/-- The sphere bundle of a gauge lies in its disc bundle. -/
theorem gaugeSphereBundle_subset_gaugeDiscBundle (ρ : TotalSpace F E → ℝ) :
    gaugeSphereBundle ρ ⊆ gaugeDiscBundle ρ :=
  fun _ hv ↦ (mem_gaugeSphereBundle.1 hv).le

variable (F E) [∀ b, NormedAddCommGroup (E b)]

/-- The unit disc bundle `D(E)` of a bundle with normed fibres: the vectors of norm at most one,
the disc bundle of the fibre norm. -/
def discBundle : Set (TotalSpace F E) :=
  gaugeDiscBundle fun v : TotalSpace F E ↦ ‖v.2‖

/-- The unit sphere bundle `S(E)` of a bundle with normed fibres: the vectors of norm one, the
sphere bundle of the fibre norm. -/
def sphereBundle : Set (TotalSpace F E) :=
  gaugeSphereBundle fun v : TotalSpace F E ↦ ‖v.2‖

variable {F E} in
/-- The unit disc bundle is the disc bundle of the fibre norm. -/
theorem discBundle_def : discBundle F E = gaugeDiscBundle fun v : TotalSpace F E ↦ ‖v.2‖ :=
  (rfl)

variable {F E} in
/-- The unit sphere bundle is the sphere bundle of the fibre norm. -/
theorem sphereBundle_def : sphereBundle F E = gaugeSphereBundle fun v : TotalSpace F E ↦ ‖v.2‖ :=
  (rfl)

variable {F E} in
@[simp]
theorem mem_discBundle {v : TotalSpace F E} : v ∈ discBundle F E ↔ ‖v.2‖ ≤ 1 :=
  Iff.rfl

variable {F E} in
@[simp]
theorem mem_sphereBundle {v : TotalSpace F E} : v ∈ sphereBundle F E ↔ ‖v.2‖ = 1 :=
  Iff.rfl

variable {F E} [TopologicalSpace (TotalSpace F E)]

/-- The disc-sphere pair `(D_ρ(E), S_ρ(E))` of a function `ρ` on the total space of a bundle. -/
abbrev gaugeDiscSpherePair (ρ : TotalSpace F E → ℝ) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) (gaugeSphereBundle_subset_gaugeDiscBundle ρ)

variable (F E) in
/-- The inclusion `S(E) → E₀` of the unit sphere bundle into the complement of the zero section. -/
def sphereBundleInclusion : TopCat.of (sphereBundle F E) ⟶ (thomPair F E).snd :=
  TopCat.ofHom (ContinuousMap.inclusion fun _ hv ↦
    mem_zeroSectionCompl.2 (norm_ne_zero_iff.1 ((mem_sphereBundle.1 hv).symm ▸ one_ne_zero)))

variable (F E) in
@[simp]
theorem coe_sphereBundleInclusion_apply (v : sphereBundle F E) :
    @Subtype.val _ (· ∈ zeroSectionCompl F E) (sphereBundleInclusion F E v) = v :=
  (rfl)

end Sets

section Gauge

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [TopologicalSpace (TotalSpace F E)]

/-- A **fibre gauge** on a bundle of real vector spaces: a continuous function `ρ` on the total
space which is positively homogeneous on each fibre, `ρ (t • v) = t * ρ v` for `t ≥ 0`, and positive
off the zero section. It is in particular nonnegative and vanishes exactly on the zero section
(`TauCeti.IsFiberGauge.nonneg`, `TauCeti.IsFiberGauge.eq_zero_iff`). A continuous fibre norm is one
(`TauCeti.isFiberGauge_norm`); no triangle inequality is required. -/
structure IsFiberGauge (ρ : TotalSpace F E → ℝ) : Prop where
  continuous : Continuous ρ
  smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (v : TotalSpace F E) :
    ρ (TotalSpace.mk' F v.proj (t • v.2)) = t * ρ v
  pos {v : TotalSpace F E} (hv : v.2 ≠ 0) : 0 < ρ v

namespace IsFiberGauge

variable {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ)
include hρ

/-- A fibre gauge vanishes on the zero section. -/
theorem eq_zero_of_snd_eq_zero {v : TotalSpace F E} (hv : v.2 = 0) : ρ v = 0 := by
  have h := hρ.smul_of_nonneg le_rfl v
  rw [zero_smul, zero_mul, ← hv, TotalSpace.mk', TotalSpace.eta] at h
  exact h

/-- A fibre gauge is nonnegative. -/
theorem nonneg (v : TotalSpace F E) : 0 ≤ ρ v := by
  by_cases hv : v.2 = 0
  · exact (hρ.eq_zero_of_snd_eq_zero hv).ge
  · exact (hρ.pos hv).le

/-- A fibre gauge vanishes exactly on the zero section. -/
theorem eq_zero_iff {v : TotalSpace F E} : ρ v = 0 ↔ v.2 = 0 :=
  ⟨fun h ↦ by_contra fun hv ↦ (hρ.pos hv).ne' h, hρ.eq_zero_of_snd_eq_zero⟩

end IsFiberGauge

/-- The sphere bundle of a fibre gauge lies in the complement `E₀` of the zero section. -/
theorem IsFiberGauge.gaugeSphereBundle_subset_zeroSectionCompl {ρ : TotalSpace F E → ℝ}
    (hρ : IsFiberGauge ρ) : gaugeSphereBundle ρ ⊆ zeroSectionCompl F E :=
  fun _ hv ↦ mem_zeroSectionCompl.2 fun h0 ↦
    one_ne_zero ((mem_gaugeSphereBundle.1 hv).symm.trans (hρ.eq_zero_iff.2 h0))

/-- The inclusion `(D_ρ(E), S_ρ(E)) ⟶ (E, E₀)` of the disc-sphere pair of a fibre gauge into the
Thom pair. -/
def gaugeDiscSpherePairMap {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ) :
    gaugeDiscSpherePair ρ ⟶ thomPair F E :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom (ContinuousMap.inclusion hρ.gaugeSphereBundle_subset_zeroSectionCompl))
    (by ext; rfl)

variable {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ)

@[simp]
theorem gaugeDiscSpherePairMap_fst_apply (v : gaugeDiscBundle ρ) :
    TopPair.Hom.fst (gaugeDiscSpherePairMap hρ) v = v.1 :=
  (rfl)

@[simp]
theorem gaugeDiscSpherePairMap_snd_apply (v : gaugeSphereBundle ρ) :
    (TopPair.Hom.snd (gaugeDiscSpherePairMap hρ) v).1 = v.1 :=
  (rfl)

/-- The square root of a continuous function `q` on the total space which is positively homogeneous
of degree two on each fibre and positive off the zero section is a fibre gauge. For instance `q`
may be `v ↦ Q_b(v, v)` for a continuous family of positive definite quadratic forms `Q_b` on the
fibres. The disc and sphere bundles of `√q` are `{q ≤ 1}` and `{q = 1}`
(`TauCeti.gaugeDiscBundle_sqrt`, `TauCeti.gaugeSphereBundle_sqrt`). -/
theorem isFiberGauge_sqrt {q : TotalSpace F E → ℝ} (hq : Continuous q)
    (hsmul : ∀ {t : ℝ}, 0 ≤ t → ∀ v : TotalSpace F E,
      q (TotalSpace.mk' F v.proj (t • v.2)) = t ^ 2 * q v)
    (hpos : ∀ {v : TotalSpace F E}, v.2 ≠ 0 → 0 < q v) :
    IsFiberGauge fun v ↦ √(q v) where
  continuous := hq.sqrt
  smul_of_nonneg {t} ht v := by rw [hsmul ht, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  pos hv := Real.sqrt_pos.2 (hpos hv)

end Gauge

/-- A fibre norm which is continuous on the total space is a fibre gauge. Its disc and sphere
bundles are the unit disc bundle `D(E)` and the unit sphere bundle `S(E)`. -/
theorem isFiberGauge_norm {B : Type w} {F : Type*} {E : B → Type w}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)]
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖) :
    IsFiberGauge fun v : TotalSpace F E ↦ ‖v.2‖ where
  continuous := hnorm
  smul_of_nonneg ht v := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  pos hv := norm_pos_iff.2 hv

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

section GaugeHomotopy

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ)

/-- The radial retraction `v ↦ v / max 1 (ρ v)` of the total space onto the disc bundle of a fibre
gauge `ρ`. -/
private def gaugeDiscRetraction : C(TotalSpace F E, gaugeDiscBundle ρ) where
  toFun v := ⟨TotalSpace.mk' F v.proj ((max 1 (ρ v))⁻¹ • v.2), by
    have h : 0 < max 1 (ρ v) := lt_max_of_lt_left one_pos
    rw [mem_gaugeDiscBundle, hρ.smul_of_nonneg (inv_nonneg.2 h.le), inv_mul_le_iff₀ h, mul_one]
    exact le_max_right _ _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.smul_totalSpace ?_ continuous_id) _
    exact (continuous_const.max hρ.continuous).inv₀ fun v ↦ (lt_max_of_lt_left one_pos).ne'

/-- **The disc bundle of a fibre gauge is a deformation retract of the total space**: the inclusion
`D_ρ(E) → E` is a homotopy equivalence, with homotopy inverse the radial retraction
`v ↦ v / max 1 (ρ v)`. -/
def gaugeDiscBundleHomotopyEquiv : gaugeDiscBundle ρ ≃ₕ TotalSpace F E where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := gaugeDiscRetraction hρ
  left_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (gaugeDiscBundle ρ))
    ext ⟨⟨b, x⟩, hx⟩
    · rfl
    · simp [gaugeDiscRetraction, max_eq_left (mem_gaugeDiscBundle.1 hx)]
  right_inv := ⟨ContinuousMap.Homotopy.symm
    { toFun := fun p ↦ TotalSpace.mk' F p.2.proj ((1 - p.1 + p.1 * (max 1 (ρ p.2))⁻¹) • p.2.2)
      continuous_toFun := by
        have ht : Continuous fun p : I × TotalSpace F E ↦ (p.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        exact Continuous.smul_totalSpace ((continuous_const.sub ht).add (ht.mul
          ((continuous_const.max (hρ.continuous.comp continuous_snd)).inv₀
            fun _ ↦ (lt_max_of_lt_left one_pos).ne'))) continuous_snd
      map_zero_left := fun v ↦ by simp
      map_one_left := fun v ↦ by simp [gaugeDiscRetraction] }⟩

@[simp]
theorem coe_gaugeDiscBundleHomotopyEquiv (v : gaugeDiscBundle ρ) :
    gaugeDiscBundleHomotopyEquiv hρ v = v.1 :=
  (rfl)

/-- The homotopy inverse of `D_ρ(E) ≃ₕ E` is the radial retraction `v ↦ v / max 1 (ρ v)`. -/
@[simp]
theorem coe_gaugeDiscBundleHomotopyEquiv_symm_apply (v : TotalSpace F E) :
    ((gaugeDiscBundleHomotopyEquiv hρ).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.proj ((max 1 (ρ v))⁻¹ • v.2) :=
  (rfl)

/-- **The sphere bundle of a fibre gauge is a deformation retract of the deleted total space**: the
inclusion `S_ρ(E) → E₀` is a homotopy equivalence, with homotopy inverse the normalization
`v ↦ v / ρ v`. -/
def gaugeSphereBundleHomotopyEquiv : gaugeSphereBundle ρ ≃ₕ zeroSectionCompl F E :=
  ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction
    hρ.gaugeSphereBundle_subset_zeroSectionCompl
    (fun p ↦ TotalSpace.mk' F p.2.1.proj ((1 - p.1 + p.1 * (ρ p.2.1)⁻¹) • p.2.1.2))
    (have ht : Continuous fun p : I × zeroSectionCompl F E ↦ (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    Continuous.smul_totalSpace ((continuous_const.sub ht).add (ht.mul
      ((hρ.continuous.comp (continuous_subtype_val.comp continuous_snd)).inv₀
        fun p ↦ (hρ.pos (mem_zeroSectionCompl.1 p.2.2)).ne')))
      (continuous_subtype_val.comp continuous_snd))
    (fun p ↦ have hp := mem_zeroSectionCompl.1 p.2.2
      mem_zeroSectionCompl.2 <|
        smul_ne_zero (by
          simpa using (convex_Ioi (0 : ℝ) one_pos (inv_pos.2 (hρ.pos hp))
            (sub_nonneg.2 p.1.2.2) p.1.2.1 (sub_add_cancel 1 _)).ne') hp)
    (fun v ↦ by simp)
    (fun v ↦ by
      simp [hρ.smul_of_nonneg (inv_nonneg.2 (hρ.nonneg v.1)) v.1,
        inv_mul_cancel₀ (hρ.pos (mem_zeroSectionCompl.1 v.2)).ne'])
    (fun t v hv ↦ by simp [mem_gaugeSphereBundle.1 hv, hv])

@[simp]
theorem coe_gaugeSphereBundleHomotopyEquiv (v : gaugeSphereBundle ρ) :
    (gaugeSphereBundleHomotopyEquiv hρ v : TotalSpace F E) = v.1 :=
  ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply _ _ _ _ _ _ _ v

/-- The homotopy inverse of `S_ρ(E) ≃ₕ E₀` is the normalization `v ↦ v / ρ v`. -/
@[simp]
theorem coe_gaugeSphereBundleHomotopyEquiv_symm_apply (v : zeroSectionCompl F E) :
    ((gaugeSphereBundleHomotopyEquiv hρ).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj ((ρ v.1)⁻¹ • v.1.2) := by
  rw [gaugeSphereBundleHomotopyEquiv,
    ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_symm_apply]
  simp

/-- The ambient component of the inclusion `(D_ρ(E), S_ρ(E)) ⟶ (E, E₀)` is the homotopy
equivalence `D_ρ(E) ≃ₕ E`. -/
private theorem gaugeDiscSpherePairMap_fst :
    TopPair.Hom.fst (gaugeDiscSpherePairMap hρ) =
      TopCat.ofHom (gaugeDiscBundleHomotopyEquiv hρ).toFun := by
  ext v
  exact (coe_gaugeDiscBundleHomotopyEquiv hρ v).symm

/-- The subspace component of the inclusion `(D_ρ(E), S_ρ(E)) ⟶ (E, E₀)` is the homotopy
equivalence `S_ρ(E) ≃ₕ E₀`. -/
private theorem gaugeDiscSpherePairMap_snd :
    TopPair.Hom.snd (gaugeDiscSpherePairMap hρ) =
      TopCat.ofHom (gaugeSphereBundleHomotopyEquiv hρ).toFun := by
  ext v
  exact Subtype.ext (coe_gaugeSphereBundleHomotopyEquiv hρ v).symm

/-- **A gauge disc-sphere pair computes the cohomology of the Thom pair.** For a fibre gauge `ρ`
on a real vector bundle, the inclusion `(D_ρ(E), S_ρ(E)) ⟶ (E, E₀)` induces isomorphisms
`Hⁿ(E, E₀) ≅ Hⁿ(D_ρ(E), S_ρ(E))` on relative singular cohomology with arbitrary coefficients, in
every degree. For the fibre norm (`TauCeti.isFiberGauge_norm`) this is the unit disc-sphere pair
`(D(E), S(E))`. -/
theorem isIso_singularCohomologyMap_gaugeDiscSpherePairMap
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (gaugeDiscSpherePairMap hρ) n) := by
  refine TopPair.isIso_singularCohomologyMap_of_forall_isIso _ (fun m ↦ ?_) (fun m ↦ ?_) n
  · rw [gaugeDiscSpherePairMap_fst hρ]
    exact (gaugeDiscBundleHomotopyEquiv hρ).isIso_singularCohomologyMap R k M m
  · rw [gaugeDiscSpherePairMap_snd hρ]
    exact (gaugeSphereBundleHomotopyEquiv hρ).isIso_singularCohomologyMap R k M m

/-- **A gauge disc-sphere pair computes the homology of the Thom pair.** For a fibre gauge `ρ` on
a real vector bundle, the inclusion `(D_ρ(E), S_ρ(E)) ⟶ (E, E₀)` induces isomorphisms
`Hₙ(D_ρ(E), S_ρ(E)) ≅ Hₙ(E, E₀)` on relative singular homology with arbitrary coefficients, in
every degree. For the fibre norm (`TauCeti.isFiberGauge_norm`) this is the unit disc-sphere pair
`(D(E), S(E))`. -/
theorem isIso_singularHomologyMap_gaugeDiscSpherePairMap
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n) :=
  TopPair.isIso_singularHomologyMap_of_homotopyEquiv _ _ _ (gaugeDiscSpherePairMap_fst hρ)
    (gaugeDiscSpherePairMap_snd hρ) R n

end GaugeHomotopy

section Norm

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.2‖)

/-- The normalization `v ↦ v / ‖v‖` of `E₀` onto the unit sphere bundle, the homotopy inverse of
the inclusion `S(E) → E₀` (`TauCeti.gaugeSphereBundleHomotopyEquiv` for the fibre norm). -/
def sphereBundleNormalization : (thomPair F E).snd ⟶ TopCat.of (sphereBundle F E) :=
  TopCat.ofHom (gaugeSphereBundleHomotopyEquiv (isFiberGauge_norm hnorm)).invFun

@[simp]
theorem coe_sphereBundleNormalization_apply (v : zeroSectionCompl F E) :
    (sphereBundleNormalization F E hnorm v : TotalSpace F E) =
      TotalSpace.mk' F v.1.proj (‖v.1.2‖⁻¹ • v.1.2) :=
  coe_gaugeSphereBundleHomotopyEquiv_symm_apply (isFiberGauge_norm hnorm) v

/-- The forward map of the homotopy equivalence `S(E) ≃ₕ E₀` is the inclusion `S(E) → E₀`. -/
private theorem ofHom_gaugeSphereBundleHomotopyEquiv_norm :
    TopCat.ofHom (gaugeSphereBundleHomotopyEquiv (isFiberGauge_norm hnorm)).toFun =
      sphereBundleInclusion F E :=
  TopCat.ext fun v ↦ Subtype.ext (coe_gaugeSphereBundleHomotopyEquiv (isFiberGauge_norm hnorm) v)

include hnorm in
/-- **The inclusion `S(E) → E₀` induces isomorphisms on cohomology** with arbitrary coefficients,
in every degree: it is a homotopy equivalence (`TauCeti.gaugeSphereBundleHomotopyEquiv` for the
fibre norm). -/
theorem isIso_singularCohomologyMap_sphereBundleInclusion
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (k : Type*) [Ring k]
    [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M)
      (sphereBundleInclusion F E) n) := by
  rw [← ofHom_gaugeSphereBundleHomotopyEquiv_norm F E hnorm]
  exact (gaugeSphereBundleHomotopyEquiv (isFiberGauge_norm hnorm)).isIso_singularCohomologyMap
    R k M n

section Cohomology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C} {k : Type*}
  [Ring k] [Linear k C] {M : C}

/-- Restricting a class of `E₀` to `S(E)` and pulling it back along the normalization
`E₀ → S(E)` gives the class back. -/
@[simp]
theorem singularCohomologyMap_sphereBundleInclusion_normalization_apply {n : ℕ}
    (y : (thomPair F E).snd.singularCohomology R k M n) :
    TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) n
      (TopCat.singularCohomologyMap (sphereBundleInclusion F E) n y) = y := by
  have h := ((gaugeSphereBundleHomotopyEquiv (isFiberGauge_norm hnorm)).singularCohomologyIso R k M
    n).hom_inv_id_apply y
  rw [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv,
    ofHom_gaugeSphereBundleHomotopyEquiv_norm F E hnorm] at h
  exact h

/-- Pulling a class of `S(E)` back along the normalization `E₀ → S(E)` and restricting it to `S(E)`
gives the class back. -/
@[simp]
theorem singularCohomologyMap_sphereBundleNormalization_inclusion_apply {n : ℕ}
    (y : (TopCat.of (sphereBundle F E)).singularCohomology R k M n) :
    TopCat.singularCohomologyMap (sphereBundleInclusion F E) n
      (TopCat.singularCohomologyMap (sphereBundleNormalization F E hnorm) n y) = y := by
  have h := ((gaugeSphereBundleHomotopyEquiv (isFiberGauge_norm hnorm)).singularCohomologyIso R k M
    n).inv_hom_id_apply y
  rw [ContinuousMap.HomotopyEquiv.singularCohomologyIso_hom,
    ContinuousMap.HomotopyEquiv.singularCohomologyIso_inv,
    ofHom_gaugeSphereBundleHomotopyEquiv_norm F E hnorm] at h
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

end Norm

end TauCeti
