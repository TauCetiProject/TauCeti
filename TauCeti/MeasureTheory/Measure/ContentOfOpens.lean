/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Content

/-!
# The content of a set function on open sets

Let `Ω` be an open set of a Hausdorff space `X` and let `m` assign a value in `[0, ∞]` to every
open set of `X`. Suppose that `m` is monotone, subadditive and additive on disjoint pairs of open
subsets of `Ω`, and finite on a neighbourhood of every compact subset of `Ω`. Then its outer
approximation `K ↦ inf { m V | K ⊆ V ⊆ Ω, V open }` on the compact subsets of `Ω` is a
`MeasureTheory.Content` (`TauCeti.contentOfOpens`). The value of the induced measure on an open
set `U` is `m U` as soon as `m U` is approximated from inside by compact sets
(`TauCeti.contentOfOpens_measure_preimage_coe`).

This is the De Giorgi–Letta criterion in the form of Mathlib's contents. It is the common step of
the constructions of measures from functionals: the variation measure of a function of locally
bounded variation and the mass measure of a current of locally finite mass.

## Main declarations

* `TauCeti.opensInf m Ω K`: the outer approximation of `m` on a set `K` of `Ω`.
* `TauCeti.contentOfOpens`: the content on `Ω` given by the outer approximation of `m`.
* `TauCeti.contentOfOpens_measure_preimage_coe`: its measure agrees with `m` on open sets which
  are approximated from inside by compact sets.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §1.5 (the De Giorgi–Letta criterion).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] (m : Opens X → ℝ≥0∞) {Ω V : Opens X}

/-- The outer approximation of a set function `m` on open sets at a set `K` of `Ω`: the infimum
of `m V` over the open sets `V ⊆ Ω` containing `K`. -/
def opensInf (Ω : Opens X) (K : Set Ω) : ℝ≥0∞ :=
  ⨅ V : {V : Opens X // (↑) '' K ⊆ (V : Set X) ∧ V ≤ Ω}, m V

variable {m}

theorem opensInf_le {K : Set Ω} (hKV : (↑) '' K ⊆ (V : Set X)) (hV : V ≤ Ω) :
    opensInf m Ω K ≤ m V :=
  iInf_le_of_le ⟨V, hKV, hV⟩ le_rfl

theorem le_opensInf {K : Set Ω} {c : ℝ≥0∞}
    (h : ∀ V : Opens X, (↑) '' K ⊆ (V : Set X) → V ≤ Ω → c ≤ m V) : c ≤ opensInf m Ω K :=
  le_iInf fun V => h V V.2.1 V.2.2

theorem opensInf_mono {K₁ K₂ : Set Ω} (h : K₁ ⊆ K₂) : opensInf m Ω K₁ ≤ opensInf m Ω K₂ :=
  le_opensInf fun _ hV hVΩ => opensInf_le ((image_mono h).trans hV) hVΩ

/-- The outer approximation of `m` is finite on compact sets if `m` is finite on a neighbourhood
of every compact subset of `Ω`. -/
theorem opensInf_ne_top (hmono : Monotone m)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens X, K ⊆ (U : Set X) ∧ m U ≠ ∞)
    {K : Set Ω} (hK : IsCompact K) : opensInf m Ω K ≠ ∞ := by
  obtain ⟨U, hKU, hU⟩ := hfin _ (hK.image continuous_subtype_val) (Subtype.coe_image_subset _ _)
  refine ne_top_of_le_ne_top hU ((opensInf_le (V := U ⊓ Ω) ?_ inf_le_right).trans
    (hmono inf_le_left))
  rw [Opens.coe_inf]
  exact subset_inter hKU (Subtype.coe_image_subset _ _)

/-- The outer approximation of a subadditive set function is subadditive. -/
theorem opensInf_union_le (hsub : ∀ U V : Opens X, U ≤ Ω → V ≤ Ω → m (U ⊔ V) ≤ m U + m V)
    (K₁ K₂ : Set Ω) : opensInf m Ω (K₁ ∪ K₂) ≤ opensInf m Ω K₁ + opensInf m Ω K₂ :=
  ENNReal.le_iInf_add_iInf fun ⟨V₁, hKV₁, hV₁⟩ ⟨V₂, hKV₂, hV₂⟩ => by
    refine (opensInf_le (V := V₁ ⊔ V₂) ?_ (sup_le hV₁ hV₂)).trans (hsub V₁ V₂ hV₁ hV₂)
    simpa [image_union] using union_subset_union hKV₁ hKV₂

/-- The outer approximation of a set function which is additive on disjoint open sets is
superadditive on disjoint compact sets, since these are separated by disjoint open sets. -/
theorem opensInf_add_le_union [T2Space X] (hmono : Monotone m)
    (hadd : ∀ U V : Opens X, U ≤ Ω → V ≤ Ω → Disjoint U V → m U + m V ≤ m (U ⊔ V))
    {K₁ K₂ : Set Ω} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (h : Disjoint K₁ K₂) :
    opensInf m Ω K₁ + opensInf m Ω K₂ ≤ opensInf m Ω (K₁ ∪ K₂) := by
  -- Separate the two compact sets by disjoint open sets `W₁` and `W₂`.
  obtain ⟨W₁, W₂, hW₁, hW₂, hKW₁, hKW₂, hW⟩ := SeparatedNhds.of_isCompact_isCompact
    (hK₁.image continuous_subtype_val) (hK₂.image continuous_subtype_val)
    ((disjoint_image_iff Subtype.val_injective).2 h)
  refine le_opensInf fun V hKV hVΩ => ?_
  have hKV' : (↑) '' K₁ ⊆ (V : Set X) ∧ (↑) '' K₂ ⊆ (V : Set X) := by
    simpa [image_union] using hKV
  let V₁ : Opens X := V ⊓ ⟨W₁, hW₁⟩
  let V₂ : Opens X := V ⊓ ⟨W₂, hW₂⟩
  have hV₁ : V₁ ≤ Ω := inf_le_left.trans hVΩ
  have hV₂ : V₂ ≤ Ω := inf_le_left.trans hVΩ
  have hdisj : Disjoint V₁ V₂ := by
    rw [← Opens.coe_disjoint]
    exact hW.mono inter_subset_right inter_subset_right
  calc opensInf m Ω K₁ + opensInf m Ω K₂
      ≤ m V₁ + m V₂ :=
        add_le_add (opensInf_le (subset_inter hKV'.1 hKW₁) hV₁)
          (opensInf_le (subset_inter hKV'.2 hKW₂) hV₂)
    _ ≤ m (V₁ ⊔ V₂) := hadd V₁ V₂ hV₁ hV₂ hdisj
    _ ≤ m V := hmono (sup_le inf_le_left inf_le_left)

variable [T2Space X] (hmono : Monotone m)
  (hsub : ∀ U V : Opens X, U ≤ Ω → V ≤ Ω → m (U ⊔ V) ≤ m U + m V)
  (hadd : ∀ U V : Opens X, U ≤ Ω → V ≤ Ω → Disjoint U V → m U + m V ≤ m (U ⊔ V))
  (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens X, K ⊆ (U : Set X) ∧ m U ≠ ∞)
include hmono hsub hadd hfin

/-- The content on the compact subsets of `Ω` given by the outer approximation `opensInf m Ω` of
a monotone set function `m` on open sets which is subadditive, additive on disjoint pairs of open
subsets of `Ω`, and finite on a neighbourhood of every compact subset of `Ω`. -/
def contentOfOpens : Content Ω where
  toFun K := (opensInf m Ω K).toNNReal
  mono' K₁ K₂ h := ENNReal.toNNReal_mono (opensInf_ne_top hmono hfin K₂.isCompact)
    (opensInf_mono h)
  sup_disjoint' K₁ K₂ h _ _ := by
    rw [Compacts.coe_sup, ← ENNReal.toNNReal_add (opensInf_ne_top hmono hfin K₁.isCompact)
      (opensInf_ne_top hmono hfin K₂.isCompact)]
    exact congrArg ENNReal.toNNReal (le_antisymm (opensInf_union_le hsub _ _)
      (opensInf_add_le_union hmono hadd K₁.isCompact K₂.isCompact h))
  sup_le' K₁ K₂ := by
    rw [Compacts.coe_sup, ← ENNReal.toNNReal_add (opensInf_ne_top hmono hfin K₁.isCompact)
      (opensInf_ne_top hmono hfin K₂.isCompact)]
    exact ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨opensInf_ne_top hmono hfin K₁.isCompact,
      opensInf_ne_top hmono hfin K₂.isCompact⟩) (opensInf_union_le hsub _ _)

theorem contentOfOpens_apply (K : Compacts Ω) :
    contentOfOpens hmono hsub hadd hfin K = opensInf m Ω K := by
  simp [contentOfOpens, ENNReal.coe_toNNReal (opensInf_ne_top hmono hfin K.isCompact)]

/-- **The measure of an open set.** The measure induced by `contentOfOpens` gives an open set `U`
of `X` the value `m U`, provided `m U` is approximated from inside by the outer approximations of
the compact subsets of `Ω ∩ U`. -/
theorem contentOfOpens_measure_preimage_coe [MeasurableSpace X] [BorelSpace X] {U : Opens X}
    (hinner : m U ≤ ⨆ (K : Compacts Ω) (_ : (K : Set Ω) ⊆ (↑) ⁻¹' (U : Set X)), opensInf m Ω K) :
    (contentOfOpens hmono hsub hadd hfin).measure ((↑) ⁻¹' (U : Set X)) = m U := by
  have hU : IsOpen ((↑) ⁻¹' (U : Set X) : Set Ω) := U.isOpen.preimage continuous_subtype_val
  rw [Content.measure_apply _ hU.measurableSet, Content.outerMeasure_of_isOpen _ _ hU]
  simp only [Content.innerContent, contentOfOpens_apply, Opens.coe_mk]
  refine le_antisymm (iSup₂_le fun K hK => ?_) hinner
  -- A compact subset of `Ω ∩ U` is tested on the open set `U ⊓ Ω`.
  refine (opensInf_le (V := U ⊓ Ω) ?_ inf_le_right).trans (hmono inf_le_left)
  rw [Opens.coe_inf]
  exact subset_inter (image_subset_iff.2 hK) (Subtype.coe_image_subset _ _)

end TauCeti
