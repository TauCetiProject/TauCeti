/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.MeasureTheory.RadonNikodymL2

/-!
# Composing `L²` classes with a measure-preserving map

For a measure-preserving `f : α → β` the map `F ↦ F ∘ f` is a linear isometry
`L²(ν) →ₗᵢ[ℂ] L²(μ)`, and it **commutes with multiplication operators**: the symbol `G` on the
target becomes the symbol `G ∘ f` on the source.  When `f` has a measure-preserving
almost-everywhere inverse the isometry is a unitary.

Mathlib supplies the underlying additive map as `MeasureTheory.Lp.compMeasurePreserving`
together with `MeasureTheory.Lp.norm_compMeasurePreserving`; what is added here is the
`ℂ`-linear isometry packaging, the two-sided-inverse criterion, and the intertwining law with
`TauCeti.mulLp`.

## Why this is the shape spectral multiplicity theory needs

A multiplication model is a *measure* together with the coordinate symbol, so the two ways a
model can be changed without changing the operator are: replacing the measure by an equivalent
one (`ForTauCeti/MeasureTheory/RadonNikodymL2.lean`), and **relabelling the underlying space by
a measurable map that fixes the symbol**.  The second is this file.  Together they are exactly
the moves used to bring a direct sum of multiplication models into multiplicity normal form:
the relabelling permutes the fibres of the index coordinate and leaves the spectral coordinate
alone, so `G ∘ f = G` and the intertwining law becomes a plain commutation.

## Main results

* `TauCeti.compLp`: the linear isometry `L²(ν) →ₗᵢ[ℂ] L²(μ)`.
* `TauCeti.compLpEquiv`: the unitary, from a two-sided almost-everywhere inverse.
* `TauCeti.compLp_mulLp`: **the intertwining law**.
* `TauCeti.mulLp_congr_ae`: the multiplication operator only depends on the symbol almost
  everywhere -- needed because two models may present the same operator with symbols truncated
  at different bounds.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {f : α → β}

section Congr

/-- **The multiplication operator depends on its symbol only almost everywhere.**

Two symbols that agree `ρ`-almost everywhere -- for instance the same function truncated at two
different bounds, both larger than the essential supremum -- define the same bounded operator on
`L²(ρ)`. -/
theorem mulLp_congr_ae (ρ : Measure α) {g g' : α → ℂ} (hg : Measurable g) (hg' : Measurable g')
    {C C' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (hgC' : ∀ x, ‖g' x‖ ≤ C') (h : g =ᵐ[ρ] g') :
    mulLp ρ hg hgC = mulLp ρ hg' hgC' := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hg hgC F, coeFn_mulLp ρ hg' hgC' F, h] with x h1 h2 h3
  rw [h1, h2, h3]

end Congr

section Comp

/-- **Composition with a measure-preserving map, as a linear isometry** `L²(ν) →ₗᵢ[ℂ] L²(μ)`.

Mathlib's `MeasureTheory.Lp.compMeasurePreserving` is an `AddMonoidHom`; this adds
`ℂ`-homogeneity and the norm identity. -/
noncomputable def compLp (f : α → β) (hf : MeasurePreserving f μ ν) :
    Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := Lp.compMeasurePreserving f hf
  map_add' F G := map_add (Lp.compMeasurePreserving (E := ℂ) (p := 2) f hf) F G
  map_smul' c F := by
    simp only [RingHom.id_apply]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • F) hf,
      Lp.coeFn_smul c (Lp.compMeasurePreserving (E := ℂ) (p := 2) f hf F),
      Lp.coeFn_compMeasurePreserving F hf,
      hf.quasiMeasurePreserving.ae (Lp.coeFn_smul c F)] with x h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3]
    exact h4
  norm_map' F := Lp.norm_compMeasurePreserving F hf

/-- The composition isometry, on representatives. -/
theorem coeFn_compLp (hf : MeasurePreserving f μ ν) (F : Lp ℂ 2 ν) :
    (compLp f hf F : α → ℂ) =ᵐ[μ] fun x => F (f x) :=
  Lp.coeFn_compMeasurePreserving F hf

/-- **Composition with an almost-everywhere two-sided inverse undoes the composition.** -/
theorem compLp_compLp {g : β → α} (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g ν μ)
    (hgf : ∀ᵐ y ∂ν, f (g y) = y) (F : Lp ℂ 2 ν) :
    compLp g hg (compLp f hf F) = F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_compLp hg (compLp f hf F),
    hg.quasiMeasurePreserving.ae (coeFn_compLp hf F), hgf] with y h1 h2 h3
  rw [h1, h2, h3]

/-- **The composition unitary.**  A measurable map with a measure-preserving almost-everywhere
two-sided inverse induces a unitary of the `L²` spaces.

Neither map need be injective: what is required is only that the two composites agree with the
identity almost everywhere, which is what an essentially bijective relabelling supplies. -/
-- Exposed: `compLpEquiv_apply` below is `rfl`, and that lemma is what lets every intertwining
-- law proved for the isometry transfer to the unitary without unfolding at the call site.
@[expose]
noncomputable def compLpEquiv (f : α → β) (g : β → α) (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g ν μ) (hfg : ∀ᵐ x ∂μ, g (f x) = x) (hgf : ∀ᵐ y ∂ν, f (g y) = y) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := compLp f hf
  invFun := compLp g hg
  left_inv F := compLp_compLp hf hg hgf F
  right_inv G := compLp_compLp hg hf hfg G
  map_add' := (compLp f hf).map_add
  map_smul' := (compLp f hf).map_smul
  norm_map' := (compLp f hf).norm_map

/-- The composition unitary is the composition isometry; stated so that the intertwining law
proved for the isometry transfers to the unitary without unfolding. -/
@[simp]
theorem compLpEquiv_apply (f : α → β) (g : β → α) (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g ν μ) (hfg : ∀ᵐ x ∂μ, g (f x) = x) (hgf : ∀ᵐ y ∂ν, f (g y) = y)
    (F : Lp ℂ 2 ν) : compLpEquiv f g hf hg hfg hgf F = compLp f hf F := rfl

/-- A measurable map is measure preserving onto its own pushforward.  Named so that the
pushforward unitary below has a stable proof term to refer to. -/
theorem measurePreserving_of_measurableEmbedding {e : α → β} (he : MeasurableEmbedding e)
    (ρ : Measure α) : MeasurePreserving e ρ (Measure.map e ρ) :=
  ⟨he.measurable, rfl⟩

/-- Composition with a measurable embedding is surjective onto `L²` of the source: every
square-integrable class extends measurably to the target. -/
theorem surjective_compLp_of_measurableEmbedding {e : α → β} (he : MeasurableEmbedding e)
    (ρ : Measure α) :
    Function.Surjective (compLp e (measurePreserving_of_measurableEmbedding he ρ)) := by
  have hpres : MeasurePreserving e ρ (Measure.map e ρ) :=
    measurePreserving_of_measurableEmbedding he ρ
  intro F
  obtain ⟨f, hfmeas, hfae⟩ : ∃ f : α → ℂ, Measurable f ∧ (F : α → ℂ) =ᵐ[ρ] f :=
    ⟨(Lp.aestronglyMeasurable F).mk (F : α → ℂ),
      (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable,
      (Lp.aestronglyMeasurable F).ae_eq_mk⟩
  have hge : (Function.extend e f (0 : β → ℂ)) ∘ e = f :=
    funext fun x => he.injective.extend_apply f 0 x
  have hgmem : MemLp (Function.extend e f (0 : β → ℂ)) 2 (Measure.map e ρ) := by
    rw [he.memLp_map_measure_iff, hge]
    exact (Lp.memLp F).ae_eq hfae
  refine ⟨hgmem.toLp (Function.extend e f (0 : β → ℂ)), Lp.ext ?_⟩
  filter_upwards [coeFn_compLp hpres (hgmem.toLp (Function.extend e f (0 : β → ℂ))),
    hpres.quasiMeasurePreserving.ae (MemLp.coeFn_toLp hgmem), hfae] with x h1 h2 h3
  rw [h1, h2, h3]
  simpa using congrFun hge x

/-- **Transport along a measurable embedding.**  For a measurable embedding `e`, composition with
`e` is a unitary `L²(map e ρ) ≃ₗᵢ[ℂ] L²(ρ)`.

Injectivity is what makes it surjective: a square-integrable class on the source extends to the
target by `Function.extend`, measurably, because a measurable embedding carries measurable sets
to measurable sets.  This is the form used to move the scalar spectral measures off the
`spectrum` subtype and onto `ℂ`, where the models of two different operators can be compared. -/
-- Exposed for the same reason as `compLpEquiv`: `embLpEquiv_apply` is `rfl`.
@[expose]
noncomputable def embLpEquiv {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α) :
    Lp ℂ 2 (Measure.map e ρ) ≃ₗᵢ[ℂ] Lp ℂ 2 ρ :=
  LinearIsometryEquiv.ofSurjective (compLp e (measurePreserving_of_measurableEmbedding he ρ))
    (surjective_compLp_of_measurableEmbedding he ρ)

/-- The pushforward unitary is composition with the embedding; stated for the same reason as
`compLpEquiv_apply`. -/
@[simp]
theorem embLpEquiv_apply {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 (Measure.map e ρ)) :
    embLpEquiv he ρ F = compLp e (measurePreserving_of_measurableEmbedding he ρ) F := rfl

/-- **The intertwining law.**  Composition with `f` carries multiplication by `G` on `L²(ν)` to
multiplication by `G ∘ f` on `L²(μ)`.

When `f` fixes the coordinate the symbol is unchanged -- `G ∘ f = G` -- and the law becomes the
statement that the unitary commutes with the multiplication operator. -/
theorem compLp_mulLp (hf : MeasurePreserving f μ ν) {G : β → ℂ} (hG : Measurable G) {C : ℝ}
    (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 ν) :
    compLp f hf (mulLp ν hG hGC F)
      = mulLp μ (hG.comp hf.measurable) (fun x => hGC (f x)) (compLp f hf F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_compLp hf (mulLp ν hG hGC F),
    hf.quasiMeasurePreserving.ae (coeFn_mulLp ν hG hGC F),
    coeFn_mulLp μ (hG.comp hf.measurable) (fun x => hGC (f x)) (compLp f hf F),
    coeFn_compLp hf F] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4]

/-- **The pushforward unitary intertwines the multiplication operators.**  The symbol on the
source is the symbol on the target composed with the embedding. -/
theorem embLpEquiv_mulLp {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α) {G : β → ℂ}
    (hG : Measurable G) {C : ℝ} (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 (Measure.map e ρ)) :
    embLpEquiv he ρ (mulLp (Measure.map e ρ) hG hGC F)
      = mulLp ρ (hG.comp he.measurable) (fun x => hGC (e x)) (embLpEquiv he ρ F) :=
  compLp_mulLp (measurePreserving_of_measurableEmbedding he ρ) hG hGC F

/-- The inverse of the pushforward unitary intertwines the multiplication operators the other
way. -/
theorem embLpEquiv_symm_mulLp {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    {G : β → ℂ} (hG : Measurable G) {C : ℝ} (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 ρ) :
    (embLpEquiv he ρ).symm (mulLp ρ (hG.comp he.measurable) (fun x => hGC (e x)) F)
      = mulLp (Measure.map e ρ) hG hGC ((embLpEquiv he ρ).symm F) := by
  refine (embLpEquiv he ρ).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, embLpEquiv_mulLp,
    LinearIsometryEquiv.apply_symm_apply]

end Comp

section Star

/-- **Relabelling is `star`-equivariant.**  Composition acts on the argument and `star` acts on
the value, so the two commute with nothing to prove beyond moving the representatives past each
other.

This is what carries the real (`star`-fixed) part of an `L²` space along the relabelling step of
the multiplicity model: `TauCeti.starFixedSubmodule` is a `star`-fixed set, so an equivariant
isometry maps it into the corresponding one. -/
theorem star_compLp (hf : MeasurePreserving f μ ν) (F : Lp ℂ 2 ν) :
    star (compLp f hf F) = compLp f hf (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (compLp f hf F), coeFn_compLp hf F,
    coeFn_compLp hf (star F), hf.quasiMeasurePreserving.ae (Lp.coeFn_star F)] with x h1 h2 h3 h4
  calc ((star (compLp f hf F) : Lp ℂ 2 μ) : α → ℂ) x
      = star ((F : β → ℂ) (f x)) := by rw [h1, Pi.star_apply, h2]
    _ = ((star F : Lp ℂ 2 ν) : β → ℂ) (f x) := by rw [h4, Pi.star_apply]
    _ = ((compLp f hf (star F) : Lp ℂ 2 μ) : α → ℂ) x := h3.symm

/-- **The pushforward unitary is `star`-equivariant.** -/
theorem star_embLpEquiv {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 (Measure.map e ρ)) :
    star (embLpEquiv he ρ F) = embLpEquiv he ρ (star F) :=
  star_compLp (measurePreserving_of_measurableEmbedding he ρ) F

/-- **The inverse of the pushforward unitary is `star`-equivariant**, which follows from
`star_embLpEquiv` by applying the unitary to both sides. -/
theorem star_embLpEquiv_symm {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 ρ) :
    star ((embLpEquiv he ρ).symm F) = (embLpEquiv he ρ).symm (star F) := by
  refine (embLpEquiv he ρ).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, ← star_embLpEquiv,
    LinearIsometryEquiv.apply_symm_apply]

end Star

end TauCeti
