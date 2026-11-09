/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.Topology.VectorBundle.Orientation.Prod
public import TauCeti.Topology.VectorBundle.RestrictScalars

/-!
# The canonical orientation of a complex vector bundle

A complex vector bundle `E → B` with finite-dimensional model fibre `F` is canonically oriented as
a real vector bundle: every fibre `E b` carries the canonical real orientation
`TauCeti.complexOrientation (E b)` of a complex vector space, the orientation of the real basis
`(v₁, i v₁, …, v_r, i v_r)` for any complex basis `(v₁, …, v_r)`. A complex-linear trivialization
reads each of these fibre orientations as the canonical orientation of `F`
(`Bundle.Trivialization.mapOrientation_complexOrientation`), so they are constant in every
trivialization of the atlas and form an orientation `TauCeti.VectorBundleOrientation.complex F E`
of the underlying real bundle, indexed by `Fin (2 * finrank ℂ F)`.

The real structure of the fibres is an ambient one compatible with the complex structure
(`IsScalarTower ℝ ℂ`), and the real vector bundle structure is the one obtained by restricting
scalars (`VectorBundle.restrictScalars`); since a vector bundle structure is a proposition, every
real vector bundle structure on `E` agrees with it.

The canonical orientation is natural under pullback
(`TauCeti.VectorBundleOrientation.complex_pullback`), is the constant canonical orientation on a
trivial bundle (`TauCeti.VectorBundleOrientation.complex_trivial`), and on a direct sum it is the
direct-sum orientation of the canonical orientations of the summands, up to the identification of
index types `2 * r₁ + 2 * r₂ = 2 * (r₁ + r₂)` (`TauCeti.VectorBundleOrientation.prod_complex`).

## Main definitions

* `TauCeti.VectorBundleOrientation.complex`: the canonical orientation of a complex vector bundle.

## Main results

* `Bundle.Trivialization.mapOrientation_complexOrientation`: a complex-linear trivialization reads
  the canonical orientation of a fibre as the canonical orientation of the model fibre.
* `TauCeti.VectorBundleOrientation.complex_pullback`: the canonical orientation of a pullback
  bundle is the pullback of the canonical orientation.
* `TauCeti.VectorBundleOrientation.complex_trivial`: the canonical orientation of the trivial
  bundle `B × F` is the constant orientation `complexOrientation F`.
* `TauCeti.VectorBundleOrientation.prod_complex`: the direct-sum orientation of the canonical
  orientations is the canonical orientation of the direct sum.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the canonical orientation of a complex vector bundle).
-/

public section

noncomputable section

open Bundle Filter Module

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]

/-- A complex-linear trivialization reads the canonical real orientation of a fibre as the canonical
real orientation of the model fibre, after identifying the index types with `Fin n`. -/
theorem mapOrientation_complexOrientation (e : Trivialization F (π F E)) [e.IsLinear ℂ]
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) [FiniteDimensional ℂ (E b)] {n : ℕ}
    (hE : 2 * finrank ℂ (E b) = n) (hF : 2 * finrank ℂ F = n) :
    e.mapOrientation (Fin n) hb
        (Orientation.reindex ℝ (E b) (finCongr hE) (TauCeti.complexOrientation (E b))) =
      Orientation.reindex ℝ F (finCongr hF) (TauCeti.complexOrientation F) := by
  have he : e.linearEquivAt ℝ b hb = (e.linearEquivAt ℂ b hb).restrictScalars ℝ :=
    LinearEquiv.ext fun _ ↦ rfl
  rw [mapOrientation_apply, Orientation.map_reindex, he, LinearEquiv.map_complexOrientation,
    ← Orientation.reindex_trans]
  rfl

end Bundle.Trivialization

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]

local instance : VectorBundle ℝ F E := VectorBundle.restrictScalars ℝ ℂ F E

/-- **The canonical orientation of a complex vector bundle**: every fibre `E b` of the underlying
real bundle is oriented by its canonical real orientation `complexOrientation (E b)`, the
orientation of `(v₁, i v₁, …, v_r, i v_r)` for any complex basis `(v₁, …, v_r)` of `E b`. -/
def complex : VectorBundleOrientation F E (Fin (2 * finrank ℂ F)) :=
  haveI : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  haveI := fun b ↦ VectorBundle.finiteDimensional ℂ F E b
  ofEventually (by rw [Fintype.card_fin, finrank_real_eq_two_mul_finrank_complex])
    (fun b ↦ Orientation.reindex ℝ (E b) (finCongr (by rw [VectorBundle.finrank_eq ℂ F E b]))
      (complexOrientation (E b)))
    (fun b ↦ trivializationAt F E b) (fun b ↦ FiberBundle.mem_baseSet_trivializationAt' b)
    (fun _ ↦ Eventually.of_forall fun _ _ ↦ by
      rw [Trivialization.mapOrientation_complexOrientation _ _ _ rfl,
        Trivialization.mapOrientation_complexOrientation _ _ _ rfl])

/-- The canonical orientation of each fibre is its canonical real orientation as a complex vector
space. -/
theorem complex_apply (b : B) :
    haveI := VectorBundle.finiteDimensional ℂ F E b
    complex F E b = Orientation.reindex ℝ (E b)
      (finCongr (by rw [VectorBundle.finrank_eq ℂ F E b])) (complexOrientation (E b)) := by
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  unfold complex
  exact congrFun (coe_ofEventually _ _ _ _ _) b

/-- A complex-linear trivialization of the atlas reads the canonical orientation of every fibre
over its base set as the canonical orientation of the model fibre. -/
theorem mapOrientation_complex (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {b : B}
    (hb : b ∈ e.baseSet) :
    e.mapOrientation _ hb (complex F E b) = complexOrientation F := by
  have := VectorBundle.finiteDimensional ℂ F E b
  rw [complex_apply, Trivialization.mapOrientation_complexOrientation _ _ _ rfl, finCongr_refl,
    Orientation.reindex_refl, Equiv.refl_apply]

/-- **Naturality of the canonical orientation.** The canonical orientation of the pullback `f*E` of
a complex vector bundle along a continuous map `f` is the pullback of the canonical orientation
of `E`. -/
@[simp]
theorem complex_pullback {B' : Type*} [TopologicalSpace B'] (f : C(B', B)) :
    (complex F E).pullback f = complex F ((⇑f) *ᵖ E) := by
  ext b
  rw [pullback_apply, complex_apply, complex_apply]
  rfl

/-- The canonical orientation of the trivial bundle `B × F` is the constant orientation given by
the canonical orientation of `F`. -/
@[simp]
theorem complex_trivial : complex F (Bundle.Trivial B F) = trivial B (complexOrientation F) := by
  ext b
  rw [complex_apply, finCongr_refl, Orientation.reindex_refl, Equiv.refl_apply, trivial_apply]

section Prod

variable {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedSpace ℂ F₁]
  [IsScalarTower ℝ ℂ F₁] [FiniteDimensional ℂ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedSpace ℂ F₂]
  [IsScalarTower ℝ ℂ F₂] [FiniteDimensional ℂ F₂]
  {E₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommGroup (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, IsScalarTower ℝ ℂ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁]
  {E₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommGroup (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, IsScalarTower ℝ ℂ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℂ F₂ E₂]

local instance : VectorBundle ℝ F₁ E₁ := VectorBundle.restrictScalars ℝ ℂ F₁ E₁
local instance : VectorBundle ℝ F₂ E₂ := VectorBundle.restrictScalars ℝ ℂ F₂ E₂
local instance : FiniteDimensional ℝ F₁ := Module.Finite.trans ℂ F₁
local instance : FiniteDimensional ℝ F₂ := Module.Finite.trans ℂ F₂

/-- **The canonical orientation of a direct sum** of complex vector bundles is the direct-sum
orientation of the canonical orientations of the summands, `E₁` before `E₂`, after identifying the
index types through `2 * r₁ + 2 * r₂ = 2 * (r₁ + r₂)`. -/
theorem prod_complex (b : B) :
    prod (complex F₁ E₁) (complex F₂ E₂) finrank_real_eq_two_mul_finrank_complex
        finrank_real_eq_two_mul_finrank_complex b =
      Orientation.reindex ℝ (E₁ b × E₂ b) (finCongr (by rw [finrank_prod]; ring))
        (complex (F₁ × F₂) (E₁ ×ᵇ E₂) b) := by
  have := VectorBundle.finiteDimensional ℂ F₁ E₁ b
  have := VectorBundle.finiteDimensional ℂ F₂ E₂ b
  have : Module.Finite ℝ (E₁ b) := Module.Finite.trans ℂ (E₁ b)
  have : Module.Finite ℝ (E₂ b) := Module.Finite.trans ℂ (E₂ b)
  rw [prod_apply, complex_apply, complex_apply, complex_apply, Orientation.prod_reindex_finCongr,
    prod_complexOrientation, ← Orientation.reindex_trans, ← Orientation.reindex_trans]
  rfl

end Prod

end TauCeti.VectorBundleOrientation
