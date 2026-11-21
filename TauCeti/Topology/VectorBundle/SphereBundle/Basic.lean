/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
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
the unit sphere bundle `S(E)` (`TauCeti.discBundle`, `TauCeti.sphereBundle`), both closed in
`TotalSpace F E` (`TauCeti.isClosed_discBundle`, `TauCeti.isClosed_sphereBundle`). Another is the
square root of a continuous function `q` which is positively homogeneous of degree two on the
fibres and positive off the zero section (`TauCeti.isFiberGauge_sqrt`), such as `v ↦ Q_b(v, v)` for
a continuous family of positive definite quadratic forms `Q_b`. Its disc bundle `{q ≤ 1}` need not
be the unit disc bundle of any norm already carried by the fibres: for instance the negative disc
bundle `{-½ Hess(v, v) ≤ ε}` of a Morse–Bott critical submanifold, where `q v = -Hess(v, v) / (2ε)`
on the negative normal bundle. Dividing a fibre gauge by a continuous positive radius function
`r : B → ℝ` on the base yields another fibre gauge (`TauCeti.IsFiberGauge.div_comp_proj`), whose
disc and sphere bundles are `{v | ρ v ≤ r v.proj}` and `{v | ρ v = r v.proj}`
(`TauCeti.gaugeDiscBundle_div`, `TauCeti.gaugeSphereBundle_div`). Each point of `S(E)` gives a
unit vector in its fibre (`TauCeti.unitSphereOfSphereBundle`), and the unit disc and sphere bundles
project continuously onto the base (`TauCeti.discBundleProj`, `TauCeti.sphereBundleProj`). The pair
`(D(E), S(E))` (`TauCeti.discSpherePair`) is the gauge disc-sphere pair of the fibre norm
(`TauCeti.discSpherePair_eq_gaugeDiscSpherePair`). In rank zero (`Subsingleton` fibres or
`Module.finrank 𝕜 F = 0`) the sphere bundle is empty
(`TauCeti.isEmpty_sphereBundle_of_subsingleton`,
`TauCeti.sphereBundle_eq_empty_of_finrank_eq_zero`), the unit disc bundle is the whole total space
(`TauCeti.discBundle_eq_univ_of_subsingleton`, `TauCeti.discBundle_eq_univ_of_finrank_eq_zero`), and
the unit disc bundle is homeomorphic to `B` (`TauCeti.discBundleHomeomorphBaseOfSubsingleton`,
`TauCeti.discBundleHomeomorphBaseOfFinrankZero`).

The unit disc and sphere bundles are closed in the total space (`TauCeti.isClosed_discBundle`,
`TauCeti.isClosed_sphereBundle`). For a finite-rank bundle whose fibres carry inner products, the
projection of the disc bundle onto the base is proper (`TauCeti.isProperMap_discBundle_proj`):
every vector of norm at most one is an orthonormal frame applied to a vector of the unit ball, and
the orthonormal frame bundle is proper over the base. So the projection to the base of a closed
part of the disc bundle is closed (`TauCeti.isClosed_image_proj_of_subset_discBundle`), and the
unit disc of each fibre is compact (`TauCeti.isCompact_discBundle_inter_proj_preimage_singleton`).

Radial rescaling compares a gauge disc-sphere pair with the Thom pair `(E, E₀)` of the bundle,
where `E₀` is the complement of the zero section:

* the inclusion `D_ρ(E) → E` is a homotopy equivalence, with homotopy inverse the radial
  retraction `v ↦ v / max 1 (ρ v)` (`TauCeti.gaugeDiscBundleHomotopyEquiv`);
* the inclusion `S_ρ(E) → E₀` is a homotopy equivalence, with homotopy inverse the normalization
  `v ↦ v / ρ v` (`TauCeti.gaugeSphereBundleHomotopyEquiv`). For the unit sphere bundle the
  inclusion `S(E) → E₀` (`TauCeti.sphereBundleInclusion`) is a morphism of topological spaces.
  When the fibres are normed and the fibre norm is continuous on the total space, so is the
  normalization `v ↦ v / ‖v‖` (`TauCeti.sphereBundleNormalization`), and the inclusion induces
  isomorphisms on cohomology (`TauCeti.isIso_singularCohomologyMap_sphereBundleInclusion`).

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
Gysin sequence. For these fibre-gauge comparisons no orientation, finite-dimensionality, norm on
the fibres or condition on the base is needed. The rank zero case is included: there `S_ρ(E)` (and
in particular `S(E)`, via `TauCeti.isEmpty_sphereBundle_of_subsingleton`) and `E₀` are empty and
`D_ρ(E) = E`.

The disc bundle of a fibre gauge also contracts radially onto the zero section, so its projection
to the base is a homotopy equivalence with homotopy inverse the zero section
(`TauCeti.gaugeDiscBundleProjHomotopyEquiv`).

For the unit sphere bundle of a bundle with normed fibres whose fibre norm is continuous on the
total space, with the connecting morphism `Hˡ(S(E)) ⟶ Hˡ⁺¹(E, E₀)` (`TauCeti.sphereBundleδ`), the
sequence

`⋯ ⟶ Hᵐ(E, E₀) ⟶ Hᵐ(B) ⟶ Hᵐ(S(E)) ⟶ Hᵐ⁺¹(E, E₀) ⟶ Hᵐ⁺¹(B) ⟶ ⋯`

of the Euler class maps, the pullback along `S(E) → B` and `TauCeti.sphereBundleδ` is exact
(`TauCeti.exact_eulerClass_singularCohomologyMap_sphereBundleProj`,
`TauCeti.exact_singularCohomologyMap_sphereBundleProj_sphereBundleδ`,
`TauCeti.exact_sphereBundleδ_eulerClass`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (the pair `(E, E₀)`) and §12 (the Gysin sequence of the sphere bundle).
* A. Hatcher, *Vector Bundles and K-Theory*, §4.D (the disc and sphere bundles and the Thom
  space `D(E)/S(E)`).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Metric Set
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

/-- The disc bundle of a function `ρ` divided by a positive function `r` is `{v | ρ v ≤ r v}`. -/
theorem gaugeDiscBundle_div {ρ r : TotalSpace F E → ℝ} (hr : ∀ v, 0 < r v) :
    gaugeDiscBundle (fun v ↦ ρ v / r v) = {v | ρ v ≤ r v} := by
  ext v
  exact div_le_one (hr v)

/-- The sphere bundle of a function `ρ` divided by a nowhere-zero function `r` is
`{v | ρ v = r v}`. -/
theorem gaugeSphereBundle_div {ρ r : TotalSpace F E → ℝ} (hr : ∀ v, r v ≠ 0) :
    gaugeSphereBundle (fun v ↦ ρ v / r v) = {v | ρ v = r v} := by
  ext v
  exact div_eq_one_iff_eq (hr v)

/-- The sphere bundle of a gauge lies in its disc bundle. -/
theorem gaugeSphereBundle_subset_gaugeDiscBundle (ρ : TotalSpace F E → ℝ) :
    gaugeSphereBundle ρ ⊆ gaugeDiscBundle ρ :=
  fun _ hv ↦ (mem_gaugeSphereBundle.1 hv).le

variable (F E) [∀ b, NormedAddCommGroup (E b)]

/-- The unit disc bundle `D(E)` of a bundle with normed fibres: the vectors of norm at most one,
the disc bundle of the fibre norm. -/
def discBundle : Set (TotalSpace F E) :=
  gaugeDiscBundle fun v : TotalSpace F E ↦ ‖v.snd‖

/-- The unit sphere bundle `S(E)` of a bundle with normed fibres: the vectors of norm one, the
sphere bundle of the fibre norm. -/
@[expose] def sphereBundle : Set (TotalSpace F E) :=
  gaugeSphereBundle fun v : TotalSpace F E ↦ ‖v.snd‖

variable {F E} in
/-- The unit disc bundle is the disc bundle of the fibre norm. -/
theorem discBundle_def : discBundle F E = gaugeDiscBundle fun v : TotalSpace F E ↦ ‖v.snd‖ :=
  (rfl)

variable {F E} in
/-- The unit sphere bundle is the sphere bundle of the fibre norm. -/
theorem sphereBundle_def : sphereBundle F E = gaugeSphereBundle fun v : TotalSpace F E ↦ ‖v.snd‖ :=
  (rfl)

variable {F E} in
@[simp]
theorem mem_discBundle {v : TotalSpace F E} : v ∈ discBundle F E ↔ ‖v.snd‖ ≤ 1 :=
  Iff.rfl

variable {F E} in
@[simp]
theorem mem_sphereBundle {v : TotalSpace F E} : v ∈ sphereBundle F E ↔ ‖v.snd‖ = 1 :=
  Iff.rfl

/-- The unit sphere bundle lies in the unit disc bundle. -/
theorem sphereBundle_subset_discBundle : sphereBundle F E ⊆ discBundle F E :=
  gaugeSphereBundle_subset_gaugeDiscBundle _

variable {F E} in
/-- The vectors of norm less than one miss the sphere bundle. -/
theorem disjoint_norm_lt_one_sphereBundle :
    Disjoint {v : TotalSpace F E | ‖v.snd‖ < 1} (sphereBundle F E) :=
  Set.disjoint_left.2 fun _ hv hv' ↦ (mem_ofPred_eq ▸ hv).ne (mem_sphereBundle.1 hv')

variable {F E} in
/-- A point `q : S(E)` viewed as a unit vector in the fibre `E q.1.proj`. -/
abbrev unitSphereOfSphereBundle (q : sphereBundle F E) : sphere (0 : E q.val.proj) 1 :=
  ⟨q.val.snd, mem_sphere_zero_iff_norm.2 (mem_sphereBundle.1 q.property)⟩

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

variable (F E) in
/-- The pair `(D(E), S(E))` of the unit disc bundle and the unit sphere bundle of a bundle with
normed fibres. -/
abbrev discSpherePair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) (sphereBundle_subset_discBundle F E)

variable (F E) in
/-- The pair `(D(E), S(E))` is the disc-sphere pair of the fibre norm, as a fibre gauge. -/
theorem discSpherePair_eq_gaugeDiscSpherePair :
    discSpherePair F E = gaugeDiscSpherePair fun v : TotalSpace F E ↦ ‖v.snd‖ :=
  TopPair.ofInclusion_congr _ _ sphereBundle_def discBundle_def

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
    ρ (TotalSpace.mk' F v.proj (t • v.snd)) = t * ρ v
  pos {v : TotalSpace F E} (hv : v.snd ≠ 0) : 0 < ρ v

namespace IsFiberGauge

variable {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ)
include hρ

/-- A fibre gauge vanishes on the zero section. -/
theorem eq_zero_of_snd_eq_zero {v : TotalSpace F E} (hv : v.snd = 0) : ρ v = 0 := by
  have h := hρ.smul_of_nonneg le_rfl v
  rw [zero_smul, zero_mul, ← hv, TotalSpace.mk', TotalSpace.eta] at h
  exact h

/-- A fibre gauge is nonnegative. -/
theorem nonneg (v : TotalSpace F E) : 0 ≤ ρ v := by
  by_cases hv : v.snd = 0
  · exact (hρ.eq_zero_of_snd_eq_zero hv).ge
  · exact (hρ.pos hv).le

/-- A fibre gauge vanishes exactly on the zero section. -/
theorem eq_zero_iff {v : TotalSpace F E} : ρ v = 0 ↔ v.snd = 0 :=
  ⟨fun h ↦ by_contra fun hv ↦ (hρ.pos hv).ne' h, hρ.eq_zero_of_snd_eq_zero⟩

/-- Dividing a fibre gauge `ρ` by a continuous positive function `r` on the base yields a fibre
gauge whose disc and sphere bundles are `{v | ρ v ≤ r v.proj}` and `{v | ρ v = r v.proj}`
(`TauCeti.gaugeDiscBundle_div`, `TauCeti.gaugeSphereBundle_div`). -/
theorem div_comp_proj [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] {r : B → ℝ} (hr : Continuous r) (hrpos : ∀ b, 0 < r b) :
    IsFiberGauge fun v : TotalSpace F E ↦ ρ v / r v.proj where
  continuous := hρ.continuous.div (hr.comp (FiberBundle.continuous_proj F E))
    fun v ↦ (hrpos v.proj).ne'
  smul_of_nonneg ht v := by rw [hρ.smul_of_nonneg ht v, mul_div_assoc]
  pos {v} hv := div_pos (hρ.pos hv) (hrpos v.proj)

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
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
    (TopCat.ofHom (ContinuousMap.inclusion hρ.gaugeSphereBundle_subset_zeroSectionCompl))
    (by ext; rfl)

variable {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ)

@[simp]
theorem gaugeDiscSpherePairMap_fst_apply (v : gaugeDiscBundle ρ) :
    TopPair.Hom.fst (gaugeDiscSpherePairMap hρ) v = v.val :=
  (rfl)

@[simp]
theorem gaugeDiscSpherePairMap_snd_apply (v : gaugeSphereBundle ρ) :
    (TopPair.Hom.snd (gaugeDiscSpherePairMap hρ) v).val = v.val :=
  (rfl)

/-- The square root of a continuous function `q` on the total space which is positively homogeneous
of degree two on each fibre and positive off the zero section is a fibre gauge. For instance `q`
may be `v ↦ Q_b(v, v)` for a continuous family of positive definite quadratic forms `Q_b` on the
fibres. The disc and sphere bundles of `√q` are `{q ≤ 1}` and `{q = 1}`
(`TauCeti.gaugeDiscBundle_sqrt`, `TauCeti.gaugeSphereBundle_sqrt`). -/
theorem isFiberGauge_sqrt {q : TotalSpace F E → ℝ} (hq : Continuous q)
    (hsmul : ∀ {t : ℝ}, 0 ≤ t → ∀ v : TotalSpace F E,
      q (TotalSpace.mk' F v.proj (t • v.snd)) = t ^ 2 * q v)
    (hpos : ∀ {v : TotalSpace F E}, v.snd ≠ 0 → 0 < q v) :
    IsFiberGauge fun v ↦ √(q v) where
  continuous := hq.sqrt
  smul_of_nonneg {t} ht v := by rw [hsmul ht, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  pos hv := Real.sqrt_pos.2 (hpos hv)

end Gauge

/-- A fibre norm which is continuous on the total space is a fibre gauge. Its disc and sphere
bundles are the unit disc bundle `D(E)` and the unit sphere bundle `S(E)`. -/
theorem isFiberGauge_norm {B : Type w} {F : Type*} {E : B → Type w}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)]
    (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.snd‖) :
    IsFiberGauge fun v : TotalSpace F E ↦ ‖v.snd‖ where
  continuous := hnorm
  smul_of_nonneg ht v := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  pos hv := norm_pos_iff.2 hv

section Subsingleton

variable {B : Type w} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] [Subsingleton F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- When the model fibre is a subsingleton, the unit sphere bundle is empty: every fibre is
homeomorphic to `F` and hence a subsingleton, so no vector has norm `1`. -/
theorem sphereBundle_eq_empty_of_subsingleton : sphereBundle F E = ∅ :=
  eq_empty_iff_forall_notMem.2 fun v hv ↦ by
    have : Subsingleton (E v.proj) :=
      (FiberBundle.homeomorphAt F E v.proj).toEquiv.subsingleton
    exact one_ne_zero ((mem_sphereBundle.1 hv).symm.trans
      (by rw [Subsingleton.elim v.snd 0, norm_zero]))

/-- When the model fibre is a subsingleton, the unit sphere bundle is empty. -/
instance isEmpty_sphereBundle_of_subsingleton : IsEmpty (sphereBundle F E) := by
  rw [sphereBundle_eq_empty_of_subsingleton]
  infer_instance

/-- When the model fibre is a subsingleton, every vector is zero, so the unit disc bundle is the
whole total space. -/
theorem discBundle_eq_univ_of_subsingleton : discBundle F E = univ :=
  eq_univ_of_forall fun v ↦ by
    have : Subsingleton (E v.proj) :=
      (FiberBundle.homeomorphAt F E v.proj).toEquiv.subsingleton
    rw [mem_discBundle, Subsingleton.elim v.snd 0, norm_zero]
    exact zero_le_one

end Subsingleton

section Proj

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- The projection `S(E) → B` of the unit sphere bundle of a bundle with normed fibres. -/
def sphereBundleProj : C(sphereBundle F E, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj, (FiberBundle.continuous_proj F E).comp continuous_subtypeVal⟩

@[simp]
theorem sphereBundleProj_apply (v : sphereBundle F E) :
    sphereBundleProj F E v = (v : TotalSpace F E).proj :=
  (rfl)

/-- The inclusion `S(E) → E₀` followed by the projection `π₀ : E₀ → B` is the projection of the
sphere bundle. -/
@[reassoc (attr := simp)]
theorem sphereBundleInclusion_comp_zeroSectionComplProjHom :
    sphereBundleInclusion F E ≫ zeroSectionComplProjHom F E = TopCat.ofHom (sphereBundleProj F E) :=
  TopCat.ext fun v ↦ (zeroSectionComplProjHom_apply F E _).trans (sphereBundleProj_apply F E v).symm

/-- The inclusion `S(E_b) → S(E)` of the unit sphere of the fibre over `b` into the unit sphere
bundle. -/
def sphereBundleFiberIncl (b : B) : C(Metric.sphere (0 : E b) 1, sphereBundle F E) where
  toFun x := ⟨⟨b, x⟩, mem_sphereBundle.2 (mem_sphere_zero_iff_norm.1 x.property)⟩
  continuous_toFun :=
    ((FiberBundle.continuous_totalSpaceMk F E b).comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem coe_sphereBundleFiberIncl_apply (b : B) (x : Metric.sphere (0 : E b) 1) :
    (sphereBundleFiberIncl F E b x : TotalSpace F E) = ⟨b, x⟩ :=
  (rfl)

/-- The sphere of the fibre over `b` lies over `b`. -/
theorem sphereBundleProj_sphereBundleFiberIncl (b : B) (x : Metric.sphere (0 : E b) 1) :
    sphereBundleProj F E (sphereBundleFiberIncl F E b x) = b :=
  (rfl)

/-- The sphere of the fibre over `b` is exactly the fibre over `b` of the sphere bundle. -/
theorem range_sphereBundleFiberIncl (b : B) :
    range (sphereBundleFiberIncl F E b) = sphereBundleProj F E ⁻¹' {b} := by
  refine Subset.antisymm (range_subset_iff.2 fun x ↦ rfl) fun v hv ↦ ?_
  obtain ⟨⟨b', x⟩, hx⟩ := v
  obtain rfl : b' = b := hv
  exact ⟨⟨x, mem_sphere_zero_iff_norm.2 hx⟩, rfl⟩

/-- The inclusion of the sphere of the fibre over `b` into the sphere bundle is an embedding. -/
theorem isEmbedding_sphereBundleFiberIncl (b : B) :
    Topology.IsEmbedding (sphereBundleFiberIncl F E b) :=
  ⟨.of_comp (sphereBundleFiberIncl F E b).continuous continuous_subtypeVal
      ((FiberBundle.totalSpaceMk_isInducing F E b).comp .subtypeVal),
    fun _ _ h ↦ Subtype.ext (TotalSpace.mk_inj.1 (congrArg Subtype.val h))⟩

end Proj

section DiscBundleBasic

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

/-- The projection `D(E) → B` of the unit disc bundle of a bundle with normed fibres. -/
def discBundleProj : C(discBundle F E, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj,
    (FiberBundle.continuous_proj F E).comp continuous_subtypeVal⟩

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
  exact discBundle_eq_univ_of_subsingleton (F := F) (E := E)

/-- In rank zero (`Module.finrank 𝕜 F = 0`), the unit sphere bundle is empty. -/
theorem sphereBundle_eq_empty_of_finrank_eq_zero (hF : Module.finrank 𝕜 F = 0) :
    sphereBundle F E = ∅ := by
  have : Subsingleton F := Module.finrank_zero_iff.1 hF
  exact sphereBundle_eq_empty_of_subsingleton

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

section Closed

variable {B : Type w} (F : Type*) (E : B → Type w)
  [∀ b, NormedAddCommGroup (E b)] [TopologicalSpace (TotalSpace F E)] [ContinuousFiberNorm F E]

/-- The unit disc bundle is closed in the total space when the fibre norm is continuous. -/
theorem isClosed_discBundle : IsClosed (discBundle F E) :=
  isClosed_le ContinuousFiberNorm.continuous_norm continuous_const

/-- The unit sphere bundle is closed in the total space when the fibre norm is continuous. -/
theorem isClosed_sphereBundle : IsClosed (sphereBundle F E) :=
  isClosed_eq ContinuousFiberNorm.continuous_norm continuous_const

end Closed

section Proper

variable (𝕜 : Type*) [RCLike 𝕜] {B : Type w} [TopologicalSpace B] (F : Type*)
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] (E : B → Type w)
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace 𝕜 (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContinuousFiberNorm F E]

include 𝕜

/-- **The disc bundle is proper over the base.** For a finite-rank real or complex vector bundle
whose fibres carry inner products with norm continuous on the total space, the projection of the
unit disc bundle `D(E)` onto the base is a proper map. In particular it is a closed map, and the
unit disc of each fibre is compact. -/
theorem isProperMap_discBundle_proj :
    IsProperMap fun v : discBundle F E ↦ (v : TotalSpace F E).proj := by
  let V := EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))
  have hV : Module.finrank 𝕜 V = Module.finrank 𝕜 F := finrank_euclideanSpace_fin
  have : CompactSpace (Metric.closedBall (0 : V) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  -- The disc bundle is the image of the orthonormal frames paired with the unit ball of `V`, over
  -- which the projection is proper.
  let ev : OrthonormalFrameBundle 𝕜 F E V × Metric.closedBall (0 : V) 1 → discBundle F E :=
    fun q ↦ ⟨⟨q.1.proj, q.1.frame q.2⟩,
      mem_discBundle.2 ((q.1.frame.norm_map _).trans_le (mem_closedBall_zero_iff.1 q.2.property))⟩
  refine isProperMap_of_comp_of_surj (f := ev)
    ((OrthonormalFrameBundle.continuous_totalSpaceMk_frame_apply.comp
      (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _)
    ((FiberBundle.continuous_proj F E).comp continuous_subtypeVal)
    (OrthonormalFrameBundle.isProperMap_proj.comp isProperMap_fst_of_compactSpace) ?_
  -- Every vector of norm at most one is an orthonormal frame applied to a vector of norm at most
  -- one.
  rintro ⟨⟨b, v⟩, hv⟩
  let φ := (trivializationAt F E b).orthonormalFrame (Module.finBasisOfFinrankEq 𝕜 F hV.symm)
    (stdOrthonormalBasis 𝕜 V) ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact ⟨(⟨b, φ⟩, ⟨φ.symm v, by simpa using hv⟩), by simp [ev]⟩

variable {F E} in
/-- The projection to the base of a closed subset of the disc bundle is closed. -/
theorem isClosed_image_proj_of_subset_discBundle {S : Set (TotalSpace F E)}
    (hS : IsClosed S) (hSD : S ⊆ discBundle F E) : IsClosed (TotalSpace.proj '' S) := by
  have h := (isProperMap_discBundle_proj 𝕜 F E).isClosedMap _ (hS.preimage continuous_subtypeVal)
  convert h using 1
  ext b
  simp only [mem_image, mem_preimage, Subtype.exists, exists_and_left, exists_prop]
  exact ⟨fun ⟨v, hv, hvb⟩ ↦ ⟨v, hv, hSD hv, hvb⟩, fun ⟨v, hv, _, hvb⟩ ↦ ⟨v, hv, hvb⟩⟩

/-- The unit disc of each fibre is compact. -/
theorem isCompact_discBundle_inter_proj_preimage_singleton (b : B) :
    IsCompact (discBundle F E ∩ TotalSpace.proj ⁻¹' {b}) := by
  have h := ((isProperMap_discBundle_proj 𝕜 F E).isCompact_preimage
    (isCompact_singleton (x := b))).image continuous_subtypeVal
  convert h using 1
  ext v
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right]
  exact ⟨fun ⟨hv, hvb⟩ ↦ ⟨hv, hvb⟩, fun ⟨hv, hvb⟩ ↦ ⟨hv, hvb⟩⟩

end Proper

section GaugePair

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ)

/-- The radial retraction `v ↦ v / max 1 (ρ v)` of the total space onto the disc bundle of a fibre
gauge `ρ`. -/
private def gaugeDiscRetraction : C(TotalSpace F E, gaugeDiscBundle ρ) where
  toFun v := ⟨TotalSpace.mk' F v.proj ((max 1 (ρ v))⁻¹ • v.snd), by
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
  toFun := ⟨Subtype.val, continuous_subtypeVal⟩
  invFun := gaugeDiscRetraction hρ
  left_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (gaugeDiscBundle ρ))
    ext ⟨⟨b, x⟩, hx⟩
    · rfl
    · simp [gaugeDiscRetraction, max_eq_left (mem_gaugeDiscBundle.1 hx)]
  right_inv := ⟨ContinuousMap.Homotopy.symm
    { toFun := fun p ↦ TotalSpace.mk' F p.2.proj ((1 - p.1 + p.1 * (max 1 (ρ p.2))⁻¹) • p.2.snd)
      continuous_toFun := by
        have ht : Continuous fun p : I × TotalSpace F E ↦ (p.1 : ℝ) :=
          continuous_subtypeVal.comp continuous_fst
        exact Continuous.smul_totalSpace ((continuous_const.sub ht).add (ht.mul
          ((continuous_const.max (hρ.continuous.comp continuous_snd)).inv₀
            fun _ ↦ (lt_max_of_lt_left one_pos).ne'))) continuous_snd
      map_zero_left := fun v ↦ by simp
      map_one_left := fun v ↦ by simp [gaugeDiscRetraction] }⟩

@[simp]
theorem coe_gaugeDiscBundleHomotopyEquiv (v : gaugeDiscBundle ρ) :
    gaugeDiscBundleHomotopyEquiv hρ v = v.val :=
  (rfl)

/-- The homotopy inverse of `D_ρ(E) ≃ₕ E` is the radial retraction `v ↦ v / max 1 (ρ v)`. -/
@[simp]
theorem coe_gaugeDiscBundleHomotopyEquiv_symm_apply (v : TotalSpace F E) :
    ((gaugeDiscBundleHomotopyEquiv hρ).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.proj ((max 1 (ρ v))⁻¹ • v.snd) :=
  (rfl)

/-- **The sphere bundle of a fibre gauge is a deformation retract of the deleted total space**: the
inclusion `S_ρ(E) → E₀` is a homotopy equivalence, with homotopy inverse the normalization
`v ↦ v / ρ v`. -/
def gaugeSphereBundleHomotopyEquiv : gaugeSphereBundle ρ ≃ₕ zeroSectionCompl F E :=
  ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction
    hρ.gaugeSphereBundle_subset_zeroSectionCompl
    (fun p ↦ TotalSpace.mk' F p.2.val.proj ((1 - p.1 + p.1 * (ρ p.2.val)⁻¹) • p.2.val.snd))
    (have ht : Continuous fun p : I × zeroSectionCompl F E ↦ (p.1 : ℝ) :=
      continuous_subtypeVal.comp continuous_fst
    Continuous.smul_totalSpace ((continuous_const.sub ht).add (ht.mul
      ((hρ.continuous.comp (continuous_subtypeVal.comp continuous_snd)).inv₀
        fun p ↦ (hρ.pos (mem_zeroSectionCompl.1 p.2.property)).ne')))
      (continuous_subtypeVal.comp continuous_snd))
    (fun p ↦ have hp := mem_zeroSectionCompl.1 p.2.property
      mem_zeroSectionCompl.2 <|
        smul_ne_zero (by
          simpa using (convex_Ioi (0 : ℝ) one_pos (inv_pos.2 (hρ.pos hp))
            (sub_nonneg.2 p.1.property.2) p.1.property.1 (sub_add_cancel 1 _)).ne') hp)
    (fun v ↦ by simp)
    (fun v ↦ by
      simp [hρ.smul_of_nonneg (inv_nonneg.2 (hρ.nonneg v.val)) v.val,
        inv_mul_cancel₀ (hρ.pos (mem_zeroSectionCompl.1 v.property)).ne'])
    (fun t v hv ↦ by simp [mem_gaugeSphereBundle.1 hv, hv])

@[simp]
theorem coe_gaugeSphereBundleHomotopyEquiv (v : gaugeSphereBundle ρ) :
    (gaugeSphereBundleHomotopyEquiv hρ v : TotalSpace F E) = v.val :=
  ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply _ _ _ _ _ _ _ v

/-- The homotopy inverse of `S_ρ(E) ≃ₕ E₀` is the normalization `v ↦ v / ρ v`. -/
@[simp]
theorem coe_gaugeSphereBundleHomotopyEquiv_symm_apply (v : zeroSectionCompl F E) :
    ((gaugeSphereBundleHomotopyEquiv hρ).symm v : TotalSpace F E) =
      TotalSpace.mk' F v.val.proj ((ρ v.val)⁻¹ • v.val.snd) := by
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

/-! ### The disc bundle and the base -/

/-- The zero section, as a map into the disc bundle of a fibre gauge. -/
private def zeroSectionGaugeDisc : C(B, gaugeDiscBundle ρ) :=
  ⟨fun b ↦ ⟨zeroSection F E b, (hρ.eq_zero_of_snd_eq_zero rfl).trans_le zero_le_one⟩,
    (Trivialization.continuous_zeroSection ℝ).subtype_mk _⟩

/-- The projection of the disc bundle of a fibre gauge. -/
private def gaugeDiscProjMap : C(gaugeDiscBundle ρ, B) :=
  ⟨fun v ↦ (v : TotalSpace F E).proj, (FiberBundle.continuous_proj F E).comp continuous_subtypeVal⟩

/-- The radial contraction `(t, v) ↦ t • v` of the disc bundle of a fibre gauge onto the zero
section. -/
private def gaugeDiscBundleContraction :
    ContinuousMap.Homotopy ((zeroSectionGaugeDisc hρ).comp gaugeDiscProjMap)
      (ContinuousMap.id (gaugeDiscBundle ρ)) where
  toFun p := ⟨TotalSpace.mk' F (p.2 : TotalSpace F E).proj ((p.1 : ℝ) • (p.2 : TotalSpace F E).snd),
    by
      rw [mem_gaugeDiscBundle, hρ.smul_of_nonneg p.1.property.1]
      exact (mul_le_of_le_one_left (hρ.nonneg _) p.1.property.2).trans
          (mem_gaugeDiscBundle.1 p.2.property)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtypeVal.comp continuous_fst).smul_totalSpace
      (continuous_subtypeVal.comp continuous_snd)
  map_zero_left v := by
    ext : 1
    simp [zeroSectionGaugeDisc, gaugeDiscProjMap, zeroSection]
  map_one_left v := by
    ext : 1
    simp

/-- **The disc bundle of a fibre gauge is homotopy equivalent to the base**: its projection is a
homotopy equivalence, with homotopy inverse the zero section. -/
def gaugeDiscBundleProjHomotopyEquiv : gaugeDiscBundle ρ ≃ₕ B where
  toFun := gaugeDiscProjMap
  invFun := zeroSectionGaugeDisc hρ
  left_inv := ⟨gaugeDiscBundleContraction hρ⟩
  right_inv := by
    have h : gaugeDiscProjMap.comp (zeroSectionGaugeDisc hρ) = ContinuousMap.id B := by
      ext
      rfl
    rw [h]

@[simp]
theorem gaugeDiscBundleProjHomotopyEquiv_apply (v : gaugeDiscBundle ρ) :
    gaugeDiscBundleProjHomotopyEquiv hρ v = (v : TotalSpace F E).proj :=
  (rfl)

/-- The homotopy inverse of `D_ρ(E) ≃ₕ B` is the zero section. -/
@[simp]
theorem coe_gaugeDiscBundleProjHomotopyEquiv_symm_apply (b : B) :
    ((gaugeDiscBundleProjHomotopyEquiv hρ).symm b : TotalSpace F E) = zeroSection F E b :=
  (rfl)

end GaugePair

/-- For the fibre norm, the projection `D(E) → B` restricts on `S(E)` to the projection of the
sphere bundle. -/
@[reassoc]
theorem gaugeDiscSpherePair_map_comp_gaugeDiscBundleProjHomotopyEquiv_norm {B : Type w}
    [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type w}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle ℝ F E] (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.snd‖) :
    (gaugeDiscSpherePair fun v : TotalSpace F E ↦ ‖v.snd‖).map ≫
        TopCat.ofHom (gaugeDiscBundleProjHomotopyEquiv (isFiberGauge_norm hnorm)).toFun =
      TopCat.ofHom (sphereBundleProj F E) := by
  ext v
  exact (gaugeDiscBundleProjHomotopyEquiv_apply (isFiberGauge_norm hnorm) _).trans
    (sphereBundleProj_apply F E v).symm

section Norm

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.snd‖)

/-- The normalization `v ↦ v / ‖v‖` of `E₀` onto the unit sphere bundle, the homotopy inverse of
the inclusion `S(E) → E₀` (`TauCeti.gaugeSphereBundleHomotopyEquiv` for the fibre norm). -/
def sphereBundleNormalization : (thomPair F E).snd ⟶ TopCat.of (sphereBundle F E) :=
  TopCat.ofHom (gaugeSphereBundleHomotopyEquiv (isFiberGauge_norm hnorm)).invFun

@[simp]
theorem coe_sphereBundleNormalization_apply (v : zeroSectionCompl F E) :
    (sphereBundleNormalization F E hnorm v : TotalSpace F E) =
      TotalSpace.mk' F v.val.proj (‖v.val.snd‖⁻¹ • v.val.snd) :=
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
  rw [← exact_eulerClass_singularCohomologyMap_zeroSectionComplProjHom R k M F E m y,
    ← sphereBundleInclusion_comp_zeroSectionComplProjHom, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply]
  -- The restriction `Hᵐ(E₀) ⟶ Hᵐ(S(E))` is injective.
  refine ⟨fun hy ↦ ?_, fun hy ↦ by rw [hy, map_zero]⟩
  rw [← singularCohomologyMap_sphereBundleInclusion_normalization_apply F E hnorm
    (TopCat.singularCohomologyMap (zeroSectionComplProjHom F E) m y), hy, map_zero]

/-- **Exactness at the cohomology of the sphere bundle**: `Hˡ(B) ⟶ Hˡ(S(E)) ⟶ Hᵐ(E, E₀)`, the
pullback along `S(E) → B` followed by the connecting morphism of the sphere bundle, is exact, for
`l + 1 = m`. -/
theorem exact_singularCohomologyMap_sphereBundleProj_sphereBundleδ (l m : ℕ) (hl : l + 1 = m) :
    Function.Exact (TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) l)
      (sphereBundleδ F E hnorm R k M l m hl) := by
  intro y
  rw [sphereBundleδ_def, ConcreteCategory.comp_apply,
    exact_singularCohomologyMap_zeroSectionComplProjHom_singularCohomologyδ R k M F E l m hl,
    ← sphereBundleInclusion_comp_zeroSectionComplProjHom]
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

/-- The Euler class map followed by the pullback along `S(E) → B` is zero. -/
@[reassoc (attr := simp)]
theorem eulerClass_comp_singularCohomologyMap_sphereBundleProj (m : ℕ) :
    eulerClass R k M F E m ≫ TopCat.singularCohomologyMap (TopCat.ofHom (sphereBundleProj F E)) m =
      0 := by
  rw [← sphereBundleInclusion_comp_zeroSectionComplProjHom, TopCat.singularCohomologyMap_comp,
    eulerClass_comp_singularCohomologyMap_zeroSectionComplProjHom_assoc, zero_comp]

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
