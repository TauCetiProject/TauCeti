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
on the negative normal bundle. The unit disc and sphere bundles project continuously onto the base
(`TauCeti.discBundleProj`, `TauCeti.sphereBundleProj`), and in rank zero (`Subsingleton` fibres or
`Module.finrank 𝕜 F = 0`) the sphere bundle is empty while the disc bundle is homeomorphic to `B`
(`TauCeti.discBundleHomeomorphBaseOfSubsingleton`, `TauCeti.discBundleHomeomorphBaseOfFinrankZero`).

Radial rescaling compares a gauge disc-sphere pair with the Thom pair `(E, E₀)` of the bundle,
where `E₀` is the complement of the zero section:

* the inclusion `D_ρ(E) → E` is a homotopy equivalence, with homotopy inverse the radial
  retraction `v ↦ v / max 1 (ρ v)` (`TauCeti.gaugeDiscBundleHomotopyEquiv`);
* the inclusion `S_ρ(E) → E₀` is a homotopy equivalence, with homotopy inverse the normalization
  `v ↦ v / ρ v` (`TauCeti.gaugeSphereBundleHomotopyEquiv`).

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
Gysin sequence. No orientation, finite-dimensionality, norm on the fibres or condition on the base
is needed. The rank zero case is included: there `S_ρ(E)` and `E₀` are empty and `D_ρ(E) = E`.

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

variable {F E}

/-- The disc-sphere pair `(D_ρ(E), S_ρ(E))` of a function `ρ` on the total space of a bundle. -/
abbrev gaugeDiscSpherePair (ρ : TotalSpace F E → ℝ) : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E)) (gaugeSphereBundle_subset_gaugeDiscBundle ρ)

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

end TauCeti
