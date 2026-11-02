/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Symmetric
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Riemannian metrics as positive symmetric sections

The native `Bundle.ContMDiffRiemannianMetric` carrier embeds into the vector space of `C^n`
bilinear sections. Its image is exactly the positive-definite symmetric sections when the model
fibre is finite-dimensional. Thus the linear space of sections provides an ambient carrier for
studying spaces of metrics, with no choice of a background metric on the fibres.

`TauCeti.Manifold.positiveDefiniteBilinearSections` is the convex cone of such sections, and
`Bundle.ContMDiffRiemannianMetric.positiveDefiniteSectionEquiv` gives the comparison in both
directions. The reverse construction proves the native bounded-unit-set condition from finite
dimensionality; positivity alone would not suffice in infinite dimensions. The forward map and
convexity do not require finite dimensionality. All results allow boundary charts and arbitrary
regularity `n`.

The same comparison holds in the vector bundle `fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ` of
symmetric bilinear forms, which for the tangent bundle is `Sym²(T*M)`.
`TauCeti.Manifold.positiveDefiniteSymmetricSections` is the convex cone of its positive-definite
`C^n` sections, and `Bundle.ContMDiffRiemannianMetric.positiveDefiniteSymmetricSectionEquiv`
identifies it with the native metrics, through the identification
`TauCeti.Manifold.symmetricBilinearSectionEquiv` of `C^n` sections of the symmetric bundle with
symmetric `C^n` bilinear sections.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable (IB n F V) in
/-- The cone of symmetric `C^n` bilinear sections positive on every nonzero diagonal vector. -/
def positiveDefiniteBilinearSections : Set (BilinearSection IB F V ℝ n) :=
  {b | b ∈ symmetricBilinearSections ∧ ∀ x v, v ≠ 0 → 0 < b x v v}

/-- Membership in the metric cone consists of symmetry and strict diagonal positivity. -/
@[simp]
theorem mem_positiveDefiniteBilinearSections (b : BilinearSection IB F V ℝ n) :
    b ∈ positiveDefiniteBilinearSections IB n F V ↔
      b ∈ symmetricBilinearSections ∧ ∀ x v, v ≠ 0 → 0 < b x v v :=
  Iff.rfl

/-- Positive-definite symmetric sections are closed under convex combinations. -/
theorem convex_positiveDefiniteBilinearSections :
    Convex ℝ (positiveDefiniteBilinearSections IB n F V) := by
  rintro b hb c hc a d ha hd had
  refine ⟨(symmetricBilinearSections (IB := IB) (F := F) (V := V)
    (G := ℝ) (n := n)).add_mem
      (Submodule.smul_mem _ a hb.1) (Submodule.smul_mem _ d hc.1), fun x v hv ↦ ?_⟩
  have heval : (a • b + d • c) x v v = a * b x v v + d * c x v v := by simp
  rw [heval]
  rcases ha.eq_or_lt with rfl | ha
  · have hd1 : d = 1 := by simpa using had
    simpa [hd1] using hc.2 x v hv
  · exact add_pos_of_pos_of_nonneg (mul_pos ha (hb.2 x v hv))
      (mul_nonneg hd (hc.2 x v hv).le)

/-! ### The cone in the bundle of symmetric bilinear forms -/

variable (IB n F V) in
/-- The cone of `C^n` sections of the bundle of symmetric bilinear forms that are positive on
every nonzero vector. For the tangent bundle these are the metrics as sections of `Sym²(T*M)`. -/
def positiveDefiniteSymmetricSections :
    Set Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯ :=
  {σ | ∀ x v, v ≠ 0 → 0 < (σ x : V x →L[ℝ] V x →L[ℝ] ℝ) v v}

/-- Membership in the cone of positive-definite symmetric sections is strict diagonal
positivity. -/
@[simp]
theorem mem_positiveDefiniteSymmetricSections
    (σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯) :
    σ ∈ positiveDefiniteSymmetricSections IB n F V ↔
      ∀ x v, v ≠ 0 → 0 < (σ x : V x →L[ℝ] V x →L[ℝ] ℝ) v v :=
  Iff.rfl

/-- Identifying sections of the symmetric bundle with symmetric bilinear sections matches the two
cones of positive-definite sections. -/
theorem symmetricBilinearSectionEquiv_mem_positiveDefiniteBilinearSections_iff
    (σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯) :
    (symmetricBilinearSectionEquiv IB n σ : BilinearSection IB F V ℝ n) ∈
        positiveDefiniteBilinearSections IB n F V ↔
      σ ∈ positiveDefiniteSymmetricSections IB n F V := by
  simp [(symmetricBilinearSectionEquiv IB n σ).2]

/-- Positive-definite sections of the symmetric bundle are closed under convex combinations. -/
theorem convex_positiveDefiniteSymmetricSections :
    Convex ℝ (positiveDefiniteSymmetricSections IB n F V) := by
  have h := (convex_positiveDefiniteBilinearSections (IB := IB) (n := n) (F := F)
    (V := V)).linear_preimage (symmetricBilinearSections.subtype ∘ₗ
      (symmetricBilinearSectionEquiv IB n).toLinearMap)
  convert h using 1
  ext σ
  simp

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti TauCeti.Manifold

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The bilinear section underlying a native `C^n` Riemannian metric. -/
def toBilinearSection (g : ContMDiffRiemannianMetric IB n F V) : BilinearSection IB F V ℝ n :=
  ⟨g.inner, g.contMDiff⟩

@[simp]
theorem toBilinearSection_apply (g : ContMDiffRiemannianMetric IB n F V)
    (x : B) (v w : V x) : g.toBilinearSection x v w = g.inner x v w :=
  (rfl)

/-- The underlying bilinear section determines a Riemannian metric. -/
theorem toBilinearSection_injective :
    Function.Injective (toBilinearSection (IB := IB) (n := n) (F := F) (V := V)) := by
  intro g h heq
  exact ext fun x v w ↦ congrArg (fun b : BilinearSection IB F V ℝ n ↦ b x v w) heq

/-- The bilinear section of a Riemannian metric belongs to the positive symmetric cone. -/
@[simp↓]
theorem toBilinearSection_mem (g : ContMDiffRiemannianMetric IB n F V) :
    g.toBilinearSection ∈ positiveDefiniteBilinearSections IB n F V :=
  ⟨(mem_symmetricBilinearSections _).2 g.symm, g.pos⟩

/-- A native `C^n` Riemannian metric as a `C^n` section of the bundle of symmetric bilinear
forms. -/
def toSymmetricSection (g : ContMDiffRiemannianMetric IB n F V) :
    Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯ :=
  (symmetricBilinearSectionEquiv IB n).symm
    ⟨g.toBilinearSection, (mem_symmetricBilinearSections _).2 g.symm⟩

@[simp]
theorem coe_toSymmetricSection_apply (g : ContMDiffRiemannianMetric IB n F V) (x : B) :
    (g.toSymmetricSection x : V x →L[ℝ] V x →L[ℝ] ℝ) = g.inner x :=
  coe_symmetricBilinearSectionEquiv_symm_apply _ x

/-- Under the identification of sections of the symmetric bundle with symmetric bilinear
sections, the section of a metric is its bilinear section. -/
@[simp]
theorem symmetricBilinearSectionEquiv_toSymmetricSection
    (g : ContMDiffRiemannianMetric IB n F V) :
    (symmetricBilinearSectionEquiv IB n g.toSymmetricSection : BilinearSection IB F V ℝ n) =
      g.toBilinearSection := by
  simp [toSymmetricSection]

/-- The section of the symmetric bundle determines a Riemannian metric. -/
theorem toSymmetricSection_injective :
    Function.Injective (toSymmetricSection (IB := IB) (n := n) (F := F) (V := V)) := by
  intro g h heq
  exact ext fun x v w ↦ by
    simpa using congrArg (fun σ ↦ (σ x : V x →L[ℝ] V x →L[ℝ] ℝ) v w) heq

/-- The section of a Riemannian metric belongs to the positive-definite symmetric cone. -/
@[simp↓]
theorem toSymmetricSection_mem (g : ContMDiffRiemannianMetric IB n F V) :
    g.toSymmetricSection ∈ positiveDefiniteSymmetricSections IB n F V :=
  fun x v hv ↦ by simpa using g.pos x v hv

variable [FiniteDimensional ℝ F]

/-- A positive-definite symmetric section determines a native Riemannian metric.
The bounded-unit-set condition follows from finite dimensionality of the model fibre. -/
def ofPositiveDefiniteSection (b : BilinearSection IB F V ℝ n)
    (hb : b ∈ positiveDefiniteBilinearSections IB n F V) :
    ContMDiffRiemannianMetric IB n F V where
  inner := b
  symm := (mem_symmetricBilinearSections _).1 hb.1
  pos := hb.2
  isVonNBounded x := by
    let e := VectorBundle.continuousLinearEquivAt ℝ F V x
    let : IsNormableSpace ℝ (V x) := e.isNormableSpace
    let c := (b x).bilinearComp e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap
    have hc : Bornology.IsVonNBounded ℝ {v : F | c v v < 1} :=
      c.isVonNBounded_setOf_lt_one_of_pos fun v hv ↦ hb.2 x (e.symm v) (by simpa using hv)
    refine (hc.image e.symm.toContinuousLinearMap).subset ?_
    intro v hv
    exact ⟨e v, by simpa [c] using hv, by simp⟩
  contMDiff := b.contMDiff

@[simp]
theorem ofPositiveDefiniteSection_inner (b : BilinearSection IB F V ℝ n)
    (hb : b ∈ positiveDefiniteBilinearSections IB n F V) (x : B) (v w : V x) :
    (ofPositiveDefiniteSection b hb).inner x v w = b x v w :=
  (rfl)

/-- Recovering a metric from its section preserves the original metric. -/
@[simp]
theorem ofPositiveDefiniteSection_toBilinearSection (g : ContMDiffRiemannianMetric IB n F V) :
    ofPositiveDefiniteSection g.toBilinearSection g.toBilinearSection_mem = g := by
  ext x v w
  simp

/-- Recovering a metric from a positive symmetric section preserves that section. -/
@[simp]
theorem toBilinearSection_ofPositiveDefiniteSection (b : BilinearSection IB F V ℝ n)
    (hb : b ∈ positiveDefiniteBilinearSections IB n F V) :
    (ofPositiveDefiniteSection b hb).toBilinearSection = b := by
  ext x v w
  simp

/-- Native finite-rank `C^n` metrics are exactly positive-definite symmetric `C^n` sections. -/
def positiveDefiniteSectionEquiv : ContMDiffRiemannianMetric IB n F V ≃
    positiveDefiniteBilinearSections IB n F V where
  toFun g := ⟨g.toBilinearSection, g.toBilinearSection_mem⟩
  invFun b := ofPositiveDefiniteSection b.1 b.2
  left_inv := ofPositiveDefiniteSection_toBilinearSection
  right_inv b := Subtype.ext (toBilinearSection_ofPositiveDefiniteSection b.1 b.2)

@[simp]
theorem positiveDefiniteSectionEquiv_apply (g : ContMDiffRiemannianMetric IB n F V) :
    (positiveDefiniteSectionEquiv g).1 = g.toBilinearSection :=
  (rfl)

@[simp]
theorem positiveDefiniteSectionEquiv_symm_apply
    (b : positiveDefiniteBilinearSections IB n F V) :
    positiveDefiniteSectionEquiv.symm b = ofPositiveDefiniteSection b.1 b.2 :=
  (rfl)

/-- The image of the native metric carrier in the space of sections is the metric cone. -/
theorem range_toBilinearSection :
    Set.range (toBilinearSection (IB := IB) (n := n) (F := F) (V := V)) =
      positiveDefiniteBilinearSections IB n F V := by
  ext b
  constructor
  · rintro ⟨g, rfl⟩
    exact g.toBilinearSection_mem
  · intro hb
    exact ⟨ofPositiveDefiniteSection b hb, toBilinearSection_ofPositiveDefiniteSection b hb⟩

/-- A positive-definite section of the bundle of symmetric bilinear forms determines a native
Riemannian metric. -/
def ofPositiveDefiniteSymmetricSection
    (σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯)
    (hσ : σ ∈ positiveDefiniteSymmetricSections IB n F V) :
    ContMDiffRiemannianMetric IB n F V :=
  ofPositiveDefiniteSection (symmetricBilinearSectionEquiv IB n σ)
    ((symmetricBilinearSectionEquiv_mem_positiveDefiniteBilinearSections_iff σ).2 hσ)

@[simp]
theorem ofPositiveDefiniteSymmetricSection_inner
    (σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯)
    (hσ : σ ∈ positiveDefiniteSymmetricSections IB n F V) (x : B) :
    (ofPositiveDefiniteSymmetricSection σ hσ).inner x = (σ x : V x →L[ℝ] V x →L[ℝ] ℝ) := by
  ext v w
  simp [ofPositiveDefiniteSymmetricSection]

/-- Recovering a metric from its section of the symmetric bundle preserves the original
metric. -/
@[simp]
theorem ofPositiveDefiniteSymmetricSection_toSymmetricSection
    (g : ContMDiffRiemannianMetric IB n F V) :
    ofPositiveDefiniteSymmetricSection g.toSymmetricSection g.toSymmetricSection_mem = g := by
  ext x v w
  simp

/-- Recovering a metric from a positive-definite section of the symmetric bundle preserves that
section. -/
@[simp]
theorem toSymmetricSection_ofPositiveDefiniteSymmetricSection
    (σ : Cₛ^n⟮IB; symmetricBilinearMaps ℝ F ℝ, fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ⟯)
    (hσ : σ ∈ positiveDefiniteSymmetricSections IB n F V) :
    (ofPositiveDefiniteSymmetricSection σ hσ).toSymmetricSection = σ := by
  ext x : 1
  apply Subtype.ext
  simp

/-- Native finite-rank `C^n` metrics are exactly the positive-definite `C^n` sections of the
bundle of symmetric bilinear forms. -/
def positiveDefiniteSymmetricSectionEquiv : ContMDiffRiemannianMetric IB n F V ≃
    positiveDefiniteSymmetricSections IB n F V where
  toFun g := ⟨g.toSymmetricSection, g.toSymmetricSection_mem⟩
  invFun σ := ofPositiveDefiniteSymmetricSection σ.1 σ.2
  left_inv := ofPositiveDefiniteSymmetricSection_toSymmetricSection
  right_inv σ := Subtype.ext (toSymmetricSection_ofPositiveDefiniteSymmetricSection σ.1 σ.2)

@[simp]
theorem positiveDefiniteSymmetricSectionEquiv_apply (g : ContMDiffRiemannianMetric IB n F V) :
    (positiveDefiniteSymmetricSectionEquiv g).1 = g.toSymmetricSection :=
  (rfl)

@[simp]
theorem positiveDefiniteSymmetricSectionEquiv_symm_apply
    (σ : positiveDefiniteSymmetricSections IB n F V) :
    positiveDefiniteSymmetricSectionEquiv.symm σ = ofPositiveDefiniteSymmetricSection σ.1 σ.2 :=
  (rfl)

/-- The image of the native metric carrier in the sections of the symmetric bundle is the
positive-definite cone. -/
theorem range_toSymmetricSection :
    Set.range (toSymmetricSection (IB := IB) (n := n) (F := F) (V := V)) =
      positiveDefiniteSymmetricSections IB n F V := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    exact g.toSymmetricSection_mem
  · intro hσ
    exact ⟨ofPositiveDefiniteSymmetricSection σ hσ,
      toSymmetricSection_ofPositiveDefiniteSymmetricSection σ hσ⟩

end Bundle.ContMDiffRiemannianMetric
