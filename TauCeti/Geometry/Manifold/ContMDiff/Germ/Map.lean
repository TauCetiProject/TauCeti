/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Order.Filter.Germ.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Defs

/-!
# Germs of analytic maps between charted spaces

We define `TauCeti.AnalyticMapGerm I J x y`, the type of germs along `𝓝 x` of maps `X → Y` that
are `C^ω` near `x` and send `x` to `y`. Neither boundarylessness of the models nor any manifold
regularity assumption on `X` or `Y` is required.

## Main definitions

* `TauCeti.AnalyticMapGerm`: germs along `𝓝 x` of maps `X → Y` analytic near `x` with `f x = y`.
* `TauCeti.AnalyticMapGerm.mk`: bundle a locally analytic map `f` with `f x = y` as an
  `AnalyticMapGerm`.
* `TauCeti.AnalyticMapGerm.id`: identity analytic map germ at `x`.
* `TauCeti.AnalyticMapGerm.comp`: composition of analytic map germs.

## Main results

* `TauCeti.AnalyticMapGerm.mk_eq_mk`: equality of `AnalyticMapGerm.mk` germs is `=ᶠ[𝓝 x]`.
* `TauCeti.AnalyticMapGerm.exists_mk`: every `AnalyticMapGerm` is represented by
  `AnalyticMapGerm.mk`.
* `TauCeti.AnalyticMapGerm.tendsto`: convergence `F.val.Tendsto (𝓝 y)` along `𝓝 x`.
* `TauCeti.AnalyticMapGerm.id_def`, `TauCeti.AnalyticMapGerm.id_comp`,
  `TauCeti.AnalyticMapGerm.comp_id`, `TauCeti.AnalyticMapGerm.comp_assoc`: unfolding and
  categorical laws for identity and composition.
-/

public section

open Filter Topology
open scoped ContDiff

namespace TauCeti

section AnalyticMapGerm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]

/-- The type of germs along `𝓝 x` of maps `X → Y` that are analytic near `x` and send `x` to `y`. -/
abbrev AnalyticMapGerm (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (x : X) (y : Y) :=
  {F : Germ (𝓝 x) Y //
    ∃ f : X → Y, (f : Germ (𝓝 x) Y) = F ∧ f x = y ∧ ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w}

/-- Construct an `AnalyticMapGerm` from a map `f : X → Y` analytic near `x` with `f x = y`. -/
def AnalyticMapGerm.mk {x : X} {y : Y} (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) : AnalyticMapGerm I J x y :=
  ⟨(f : Germ (𝓝 x) Y), ⟨f, rfl, hfx, hf⟩⟩

/-- The underlying `Germ (𝓝 x) Y` of `AnalyticMapGerm.mk f hf hfx` is `(f : Germ (𝓝 x) Y)`. -/
@[simp]
theorem AnalyticMapGerm.val_mk {x : X} {y : Y} (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    (AnalyticMapGerm.mk f hf hfx).val = (f : Germ (𝓝 x) Y) := (rfl)

/-- Two `AnalyticMapGerm.mk` germs are equal if and only if their representatives agree near `x`. -/
@[simp]
theorem AnalyticMapGerm.mk_eq_mk {x : X} {y : Y} {f₁ f₂ : X → Y}
    (hf₁ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₁ w) (hfx₁ : f₁ x = y)
    (hf₂ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₂ w) (hfx₂ : f₂ x = y) :
    AnalyticMapGerm.mk f₁ hf₁ hfx₁ = AnalyticMapGerm.mk f₂ hf₂ hfx₂ ↔ f₁ =ᶠ[𝓝 x] f₂ := by
  rw [Subtype.ext_iff, AnalyticMapGerm.val_mk, AnalyticMapGerm.val_mk, Germ.coe_eq]

/-- Every `AnalyticMapGerm` is represented by `AnalyticMapGerm.mk` of a locally analytic map. -/
theorem AnalyticMapGerm.exists_mk {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    ∃ (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y),
      AnalyticMapGerm.mk f hf hfx = F :=
  let ⟨f, hF, hfx, hf⟩ := F.property; ⟨f, hf, hfx, Subtype.ext hF⟩

/-- Every analytic map germ `(X, x) → (Y, y)` tends to `𝓝 y` along `𝓝 x`. -/
theorem AnalyticMapGerm.tendsto {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    F.val.Tendsto (𝓝 y) := by
  obtain ⟨f, hF, hfx, hf⟩ := F.property
  exact hF ▸ Germ.coe_tendsto.2 (hfx ▸ hf.self_of_nhds.continuousAt.tendsto)

/-- The identity analytic map germ at `x`. -/
def AnalyticMapGerm.id (I : ModelWithCorners 𝕜 E H) (x : X) : AnalyticMapGerm I I x x :=
  AnalyticMapGerm.mk _root_.id (Eventually.of_forall fun _ ↦ contMDiffAt_id) rfl

/-- The underlying `Germ (𝓝 x) X` of `AnalyticMapGerm.id I x` is the germ of `id`. -/
@[simp]
theorem AnalyticMapGerm.val_id (I : ModelWithCorners 𝕜 E H) (x : X) :
    (AnalyticMapGerm.id I x).val = ((_root_.id : X → X) : Germ (𝓝 x) X) := (rfl)

/-- Unfolding rule for `AnalyticMapGerm.id` in terms of `AnalyticMapGerm.mk`. -/
theorem AnalyticMapGerm.id_def (I : ModelWithCorners 𝕜 E H) (x : X) :
    AnalyticMapGerm.id I x =
      AnalyticMapGerm.mk _root_.id (Eventually.of_forall fun _ ↦ contMDiffAt_id) rfl := by
  rw [Subtype.ext_iff, AnalyticMapGerm.val_id, AnalyticMapGerm.val_mk]

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {Z : Type*} [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- Composition of analytic map germs `(X, x) → (Y, y)` and `(Y, y) → (Z, z)`. -/
def AnalyticMapGerm.comp {x : X} {y : Y} {z : Z}
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) : AnalyticMapGerm I K x z :=
  ⟨G.val.compTendsto' F.val F.tendsto, by
    obtain ⟨g, hG, hgy, hg⟩ := G.property; obtain ⟨f, hF, hfx, hf⟩ := F.property
    exact ⟨g ∘ f, by simp [← hG, ← hF], (congrArg g hfx).trans hgy,
      eventually_contMDiffAt_comp hg hf hfx⟩⟩

/-- The underlying filter germ of `G.comp F` is `G.val.compTendsto' F.val F.tendsto`. -/
@[simp]
theorem AnalyticMapGerm.val_comp {x : X} {y : Y} {z : Z}
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    (G.comp F).val = G.val.compTendsto' F.val F.tendsto := (rfl)

/-- Composing `AnalyticMapGerm.mk` representatives produces `AnalyticMapGerm.mk (g ∘ f) _ _`. -/
@[simp]
theorem AnalyticMapGerm.comp_mk {x : X} {y : Y} {z : Z}
    (g : Y → Z) (hg : ∀ᶠ v in 𝓝 y, ContMDiffAt J K ω g v) (hgy : g y = z)
    (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    (AnalyticMapGerm.mk g hg hgy).comp (AnalyticMapGerm.mk f hf hfx) =
      AnalyticMapGerm.mk (g ∘ f) (eventually_contMDiffAt_comp hg hf hfx)
        ((congrArg g hfx).trans hgy) := by
  exact Subtype.ext ((Germ.compTendsto'_coe (g : Germ (𝓝 y) Z)
    (hfx ▸ hf.self_of_nhds.continuousAt.tendsto)).trans (Germ.coe_compTendsto _ _))

/-- Left composition with `AnalyticMapGerm.id` is the identity. -/
@[simp]
theorem AnalyticMapGerm.id_comp {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    (AnalyticMapGerm.id J y).comp F = F := by
  obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk
  rw [AnalyticMapGerm.id_def, AnalyticMapGerm.comp_mk, AnalyticMapGerm.mk_eq_mk]
  exact Eventually.of_forall fun _ ↦ rfl

/-- Right composition with `AnalyticMapGerm.id` is the identity. -/
@[simp]
theorem AnalyticMapGerm.comp_id {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    F.comp (AnalyticMapGerm.id I x) = F := by
  obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk
  rw [AnalyticMapGerm.id_def, AnalyticMapGerm.comp_mk, AnalyticMapGerm.mk_eq_mk]
  exact Eventually.of_forall fun _ ↦ rfl

/-- Composition of analytic map germs is associative. -/
theorem AnalyticMapGerm.comp_assoc {E''' : Type*} [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
    {H''' : Type*} [TopologicalSpace H'''] {L : ModelWithCorners 𝕜 E''' H'''}
    {W : Type*} [TopologicalSpace W] [ChartedSpace H''' W] {x : X} {y : Y} {z : Z} {w : W}
    (H : AnalyticMapGerm K L z w) (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    (H.comp G).comp F = H.comp (G.comp F) := by
  obtain ⟨h, hh, hhz, rfl⟩ := H.exists_mk
  obtain ⟨g, hg, hgy, rfl⟩ := G.exists_mk
  obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk
  rw [AnalyticMapGerm.comp_mk, AnalyticMapGerm.comp_mk, AnalyticMapGerm.comp_mk,
    AnalyticMapGerm.comp_mk, AnalyticMapGerm.mk_eq_mk]
  exact Eventually.of_forall fun _ ↦ rfl

end AnalyticMapGerm

end TauCeti
