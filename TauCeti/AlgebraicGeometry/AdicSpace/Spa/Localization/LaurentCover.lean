/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
public import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial
public import TauCeti.RingTheory.Huber.StronglyNoetherian

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.FaithfullyFlat
import TauCeti.RingTheory.Huber.LocalizationTopology.Quotient
import TauCeti.RingTheory.Huber.LocalizationTopology.StronglyNoetherian
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Laurent.Cover
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Ideal.Operations

/-!
# Exactness for a two-piece Laurent cover

Let `A` be a complete Hausdorff strongly noetherian Tate ring and `f ∈ A`. The rational subsets

```text
U₁ = R({f, 1}/1) = {|f| ≤ 1},      U₂ = R({1}/f) = {|f| ≥ 1},      U₁ ∩ U₂ = R({f², f, 1}/(1 · f))
```

cover `Spa(A, A⁺)`; the presentation of `U₁ ∩ U₂` is the one `rationalSubset_inter` produces.
**Wedhorn's Lemma 8.33** says that the augmented Čech complex of the structure presheaf on this
cover is exact:

```text
0 → A → A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩ → 0,      a ↦ (a, a),      (x, y) ↦ x|U₁∩U₂ - y|U₁∩U₂.
```

Here `A⟨U⟩` is the completed rational localisation `UniformSpace.Completion S` of a presentation,
the first map is the product of the structure maps `toCompletionLoc`, and the restrictions are the
maps `restrictionRingHom` of the refinements `1 · f = 1 · f` (cofactor `f`) and `1 · f = f · 1`
(cofactor `1`). Each presentation carries its own localisation `S`, but only `U₂` needs a
`HasDenominatorPower` hypothesis: the one for `U₁` is automatic at the denominator `1`
(`TauCeti.Huber.PairOfDefinition.hasDenominatorPower_denom_one`), and the one for `U₁ ∩ U₂` is
built from those two by `TauCeti.Huber.PairOfDefinition.hasDenominatorPower_mul`.

## Main results

* `TauCeti.ValuationSpectrum.laurentCover_injective`: `A → A⟨U₁⟩ × A⟨U₂⟩` is injective.
* `TauCeti.ValuationSpectrum.laurentCover_exact`: the kernel of the difference of restrictions
  `A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩` is the image of `A`.
* `TauCeti.ValuationSpectrum.laurentCover_surjective`: the difference of restrictions is
  surjective.
* `TauCeti.ValuationSpectrum.spa_subset_iUnion_laurentCover`: the geometric half — the two
  pieces really do cover `Spa(A, A⁺)`.

## Implementation notes

As in Wedhorn's (8.2.1), the coordinate rings are presented as quotients of restricted power
series by `TauCeti.Huber.PairOfDefinition.rationalQuotientRingEquiv`, for `U₂` at the single
numerator `1` over the denominator `f`:

```text
A⟨U₁⟩ = A⟨X⟩ ⧸ (f - X),   A⟨U₂⟩ = A⟨Y⟩ ⧸ (1 - f Y),   A⟨U₁ ∩ U₂⟩ = A⟨X, Y⟩ ⧸ (f² - f X, 1 - f Y).
```

The last ideal lies in `(f - X, 1 - XY)`, and under these presentations the two restriction maps
are induced by the embeddings `A⟨T⟩ → A⟨X, Y⟩`, `T ↦ X` and `T ↦ Y`. The diagram chase then
reduces surjectivity to `TauCeti.Huber.laurentDiff_surjective` on `A⟨ζ, ζ⁻¹⟩ = A⟨X, Y⟩ ⧸ (1 - XY)`,
and exactness to `TauCeti.Huber.exact_algebraMap_laurentCoverDiff` on the quotient presentations
of the cover. Transporting the latter needs only that the presentation maps factor through those
quotients, which is what the relation hypotheses say; no isomorphism between them is required.
Injectivity is Corollary 8.32 for the pair `(A, A°)`.

The numerator sets are `Finset` literals, so writing them down needs decidable equality on `A`.
That is an artefact of the notation rather than a hypothesis of the mathematics, so the public
results take their instance from `Classical.decEq` instead of assuming `DecidableEq A`; the
private helpers below stay polymorphic in the instance.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), (8.2.1) and Lemma 8.33.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, branch `dev/adic-spaces`, commit `37bbdaeb9`,
Apache-2.0), `projects/AdicSpaces/Adic spaces/LaurentCoverExact.lean`, proves the lemma for its
quotient rings `B₁_gen f = A⟨X⟩ ⧸ (f - X)`, `B₂_gen f = A⟨X⟩ ⧸ (1 - f X)` and
`B₁₂_gen f = A⟨ζ, ζ⁻¹⟩ ⧸ (f - ζ)`, over its own `TateAlgebra` and
`LaurentTateAlgebra A = TateAlgebra₂ A ⧸ (XY - 1)`. The exactness and surjectivity are
`ker_deltaMap_gen_le_range_epsilonHom_gen` and `deltaMap_gen_surjective` (bundled in `row3_exact`),
by a chase through `ker_lambdaMap_le_range_iotaHom` (`row2_exact_at_middle`) and
`lambdaMap_surjective`; its injectivity, `epsilonHom_gen_injective`, is proved for a noetherian
domain and a non-unit `f` by the Krull intersection theorem. The chase here has the same shape.
The statements differ: they concern the completed rational localisations and their restriction
maps, reached through Example 6.38, and injectivity comes from Corollary 8.32 without a domain
hypothesis. No AINTLIB code is copied.
-/

open scoped Uniformity

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

/-! ### The diagram chase -/

section Square

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

-- A continuous ring homomorphism out of `A⟨T⟩` is determined by constants and the variable, so a
-- square with the renaming `A⟨T⟩ → A⟨X, Y⟩` commutes once it does on those.
private theorem apply_eq_apply_weightedRename {B B' : Type*} [Semiring B] [TopologicalSpace B]
    [Semiring B'] [TopologicalSpace B'] [T2Space B'] {e : Fin 1 ↪ Fin 2}
    {π : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B}
    {π' : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      B'} {ρ : B →+* B'} (hρ : Continuous ρ) (hπ : Continuous π) (hπ' : Continuous π')
    (hC : ∀ a, ρ (π (weightedC _ isWeightFamily_one_weight a)) =
      π' (weightedC _ isWeightFamily_one_weight a))
    (hX : ∀ i, ρ (π (weightedX _ isWeightFamily_one_weight i)) =
      π' (weightedX _ isWeightFamily_one_weight (e i)))
    (g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ρ (π g) = π' (weightedRename e _ _ (fun _ ↦ subset_rfl) g) := by
  have key : ρ.comp π = π'.comp (weightedRename e _ _ (fun _ ↦ subset_rfl)) :=
    weightedRestrictedSubring_ringHom_ext_of_continuous _ (hρ.comp hπ)
      (hπ'.comp (continuous_weightedRename _ _ _ _)) (fun a ↦ by simp [hC]) (fun i ↦ by simp [hX])
  exact DFunLike.congr_fun key g

end Square

section Chase

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A] {B₁ B₂ B₁₂ : Type*} [CommRing B₁] [CommRing B₂] [CommRing B₁₂]
  {π₁ : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B₁}
  {π₂ : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B₂}
  {π₁₂ : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
    B₁₂}
  {ρ₁ : B₁ →+* B₁₂} {ρ₂ : B₂ →+* B₁₂}

-- Surjectivity of `(x₁, x₂) ↦ ρ₁ x₁ - ρ₂ x₂`: as `π₁₂` kills `1 - XY` it factors through
-- `A⟨ζ, ζ⁻¹⟩ = A⟨X, Y⟩ ⧸ (1 - XY)`, where `laurentDiff` is already known to be surjective.
private theorem exists_sub_eq_of_surjective (hπ₁₂ : Function.Surjective π₁₂)
    (hsq₁ : ∀ g, ρ₁ (π₁ g) = π₁₂ (weightedRename Fin.castSuccEmb _ _ (fun _ ↦ subset_rfl) g))
    (hsq₂ : ∀ h, ρ₂ (π₂ h) = π₁₂ (weightedRename (Fin.succEmb 1) _ _ (fun _ ↦ subset_rfl) h))
    (hXY : π₁₂ (1 - weightedX _ isWeightFamily_one_weight 0 *
      weightedX _ isWeightFamily_one_weight 1) = 0) (y : B₁₂) :
    ∃ (x₁ : B₁) (x₂ : B₂), ρ₁ x₁ - ρ₂ x₂ = y := by
  obtain ⟨u, rfl⟩ := hπ₁₂ y
  obtain ⟨⟨g, h⟩, hgh⟩ := laurentDiff_surjective A (Ideal.Quotient.mk (laurentIdeal A) u)
  rw [laurentDiff_apply, Ideal.Quotient.eq, mem_laurentIdeal] at hgh
  obtain ⟨w, hw⟩ := hgh
  exact ⟨π₁ g, π₂ h, by
    rw [hsq₁, hsq₂, ← map_sub, ← sub_eq_zero, ← map_sub, hw, map_mul, hXY, zero_mul]⟩

-- Transport the exact Laurent-cover row through three quotient presentations. The overlap kernel
-- identifies the two restrictions in the algebraic overlap quotient; exactness there produces a
-- constant, and the two piece relations descend that constant to `B₁` and `B₂`.
private theorem exists_eq_weightedC_of_apply_eq (f : A) (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂)
    (hf₁ : π₁ (weightedX _ isWeightFamily_one_weight 0) = π₁ (weightedC _ _ f))
    (hf₂ : π₂ (weightedC _ _ f) * π₂ (weightedX _ isWeightFamily_one_weight 0) = 1)
    (hsq₁ : ∀ g, ρ₁ (π₁ g) = π₁₂ (weightedRename Fin.castSuccEmb _ _ (fun _ ↦ subset_rfl) g))
    (hsq₂ : ∀ h, ρ₂ (π₂ h) = π₁₂ (weightedRename (Fin.succEmb 1) _ _ (fun _ ↦ subset_rfl) h))
    (hker : ∀ u, π₁₂ u = 0 → u ∈ Ideal.span
      {weightedC _ isWeightFamily_one_weight f - weightedX _ isWeightFamily_one_weight 0,
        1 - weightedX _ isWeightFamily_one_weight 0 * weightedX _ isWeightFamily_one_weight 1})
    (x₁ : B₁) (x₂ : B₂) (h : ρ₁ x₁ = ρ₂ x₂) :
    ∃ c : A, π₁ (weightedC _ _ c) = x₁ ∧ π₂ (weightedC _ _ c) = x₂ := by
  obtain ⟨G, rfl⟩ := hπ₁ x₁
  obtain ⟨H, rfl⟩ := hπ₂ x₂
  have hzero : π₁₂ (weightedRename Fin.castSuccEmb _ _ (fun _ ↦ subset_rfl) G -
      weightedRename (Fin.succEmb 1) _ _ (fun _ ↦ subset_rfl) H) = 0 := by
    rw [map_sub, ← hsq₁, ← hsq₂, h, sub_self]
  have hcover : laurentCoverDiff A f
      (Ideal.Quotient.mk (laurentCoverLeIdeal A f) G,
        Ideal.Quotient.mk (laurentCoverGeIdeal A f) H) = 0 := by
    rw [laurentCoverDiff_mk, Ideal.Quotient.eq_zero_iff_mem, laurentCoverOverlapIdeal_def,
      Ideal.mem_span_singleton']
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hker _ hzero)
    refine ⟨Ideal.Quotient.mk (laurentIdeal A) u, ?_⟩
    rw [laurentDiff_apply, ← huv, map_add, map_mul, map_mul]
    have hxy_zero : Ideal.Quotient.mk (laurentIdeal A)
        (1 - weightedX _ isWeightFamily_one_weight 0 *
          weightedX _ isWeightFamily_one_weight 1) = 0 := by
      simp only [map_sub, map_one, map_mul, mk_weightedX_zero_mul_mk_weightedX_one, sub_self]
    rw [hxy_zero]
    simp only [mul_zero, add_zero, map_sub, ← algebraMap_weightedRestrictedSubring,
      Ideal.Quotient.mk_algebraMap]
  obtain ⟨c, hc⟩ := (exact_algebraMap_laurentCoverDiff A f _).1 hcover
  have hc₁ : Ideal.Quotient.mk (laurentCoverLeIdeal A f)
      (weightedC _ isWeightFamily_one_weight c) =
        Ideal.Quotient.mk (laurentCoverLeIdeal A f) G := by
    simpa only [Prod.algebraMap_apply, ← algebraMap_weightedRestrictedSubring,
      Ideal.Quotient.mk_algebraMap] using congrArg Prod.fst hc
  have hc₂ : Ideal.Quotient.mk (laurentCoverGeIdeal A f)
      (weightedC _ isWeightFamily_one_weight c) =
        Ideal.Quotient.mk (laurentCoverGeIdeal A f) H := by
    simpa only [Prod.algebraMap_apply, ← algebraMap_weightedRestrictedSubring,
      Ideal.Quotient.mk_algebraMap] using congrArg Prod.snd hc
  rw [Ideal.Quotient.eq, laurentCoverLeIdeal_def, Ideal.mem_span_singleton'] at hc₁
  rw [Ideal.Quotient.eq, laurentCoverGeIdeal_def, Ideal.mem_span_singleton'] at hc₂
  obtain ⟨u, hu⟩ := hc₁
  obtain ⟨v, hv⟩ := hc₂
  refine ⟨c, ?_, ?_⟩
  · rw [← sub_eq_zero, ← map_sub, ← hu, map_mul, map_sub, hf₁, sub_self, mul_zero]
  · rw [← sub_eq_zero, ← map_sub, ← hv, map_mul, map_sub, map_one, map_mul, hf₂, sub_self,
      mul_zero]

end Chase

/-! ### The three presentations of the Laurent cover -/

section Presentations

variable {A : Type*} [CommRing A] (f : A)

-- `R({1}/f)`, with the single numerator `1` listed.
private theorem mem_numerators_inv : ∀ _ : Fin 1, (1 : A) ∈ ({1} : Finset A) :=
  fun _ ↦ Finset.mem_singleton_self 1

private theorem eq_denom_or_mem_range_inv :
    ∀ u ∈ ({1} : Finset A), u = f ∨ u ∈ Set.range fun _ : Fin 1 ↦ (1 : A) := by
  simp

variable [DecidableEq A]

-- `R({f, 1}/1)`, with the numerator `f` listed.
private theorem mem_numerators_plus : ∀ _ : Fin 1, f ∈ ({f, 1} : Finset A) :=
  fun _ ↦ Finset.mem_insert_self f _

private theorem eq_denom_or_mem_range_plus :
    ∀ u ∈ ({f, 1} : Finset A), u = 1 ∨ u ∈ Set.range fun _ : Fin 1 ↦ f := by
  simp

-- `R({f * f, f, 1}/(1 * f))`, with the numerators `f * f` and `1` listed.
private theorem mem_numerators_inter : ∀ i, ![f * f, 1] i ∈ ({f * f, f, 1} : Finset A) := by simp

private theorem eq_denom_or_mem_range_inter :
    ∀ u ∈ ({f * f, f, 1} : Finset A), u = 1 * f ∨ u ∈ Set.range ![f * f, 1] := by
  simp

end Presentations

/-! ### The coordinate rings of the Laurent cover as quotients -/

section Pieces

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStronglyNoetherian A] (P : PairOfDefinition A)
  (f : A)

section Inverse

variable (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (hden₂ : HasDenominatorPower P {1} f S₂)

-- `A⟨X⟩ → A⟨X⟩ ⧸ (1 - f X) ≃ A⟨1/f⟩`.
private noncomputable def laurentHom₂ :
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      UniformSpace.Completion S₂ :=
  rationalQuotientHom P {1} f S₂ hden₂ _ mem_numerators_inv (eq_denom_or_mem_range_inv f)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one)
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _)

private theorem laurentHom₂_surjective :
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    Function.Surjective (laurentHom₂ P f S₂ hden₂) :=
  rationalQuotientHom_surjective P {1} f S₂ hden₂ _ _ _ _ _

private theorem continuous_laurentHom₂ :
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    Continuous (laurentHom₂ P f S₂ hden₂) :=
  continuous_rationalQuotientHom P {1} f S₂ hden₂ _ _ _ _ _

private theorem laurentHom₂_weightedC (a : A) :
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    laurentHom₂ P f S₂ hden₂ (weightedC _ isWeightFamily_one_weight a) =
      toCompletionLoc P {1} f S₂ hden₂ a :=
  rationalQuotientHom_weightedC P {1} f S₂ hden₂ _ _ _ _ _ a

private theorem laurentHom₂_weightedC_mul_weightedX_eq_one :
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    laurentHom₂ P f S₂ hden₂ (weightedC _ isWeightFamily_one_weight f) *
      laurentHom₂ P f S₂ hden₂ (weightedX _ isWeightFamily_one_weight 0) = 1 := by
  let _ := locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  have h := rationalQuotientHom_weightedC_mul_weightedX P {1} f S₂ hden₂ _ mem_numerators_inv
    (eq_denom_or_mem_range_inv f)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one)
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _) 0
  rwa [map_one, map_one] at h

end Inverse

variable [DecidableEq A]

section Plus

variable (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (hden₁ : HasDenominatorPower P {f, 1} 1 S₁)

-- `A⟨X⟩ → A⟨X⟩ ⧸ (f - X) ≃ A⟨f/1⟩`.
private noncomputable def laurentHom₁ :
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      UniformSpace.Completion S₁ :=
  rationalQuotientHom P {f, 1} 1 S₁ hden₁ _ (mem_numerators_plus f) (eq_denom_or_mem_range_plus f)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one)
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _)

private theorem laurentHom₁_surjective :
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    Function.Surjective (laurentHom₁ P f S₁ hden₁) :=
  rationalQuotientHom_surjective P {f, 1} 1 S₁ hden₁ _ _ _ _ _

private theorem continuous_laurentHom₁ :
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    Continuous (laurentHom₁ P f S₁ hden₁) :=
  continuous_rationalQuotientHom P {f, 1} 1 S₁ hden₁ _ _ _ _ _

private theorem laurentHom₁_weightedC (a : A) :
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    laurentHom₁ P f S₁ hden₁ (weightedC _ isWeightFamily_one_weight a) =
      toCompletionLoc P {f, 1} 1 S₁ hden₁ a :=
  rationalQuotientHom_weightedC P {f, 1} 1 S₁ hden₁ _ _ _ _ _ a

private theorem laurentHom₁_weightedX :
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    laurentHom₁ P f S₁ hden₁ (weightedX _ isWeightFamily_one_weight 0) =
      laurentHom₁ P f S₁ hden₁ (weightedC _ isWeightFamily_one_weight f) := by
  let _ := locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  have h := rationalQuotientHom_weightedC_mul_weightedX P {f, 1} 1 S₁ hden₁ _
    (mem_numerators_plus f) (eq_denom_or_mem_range_plus f)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one)
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _) 0
  rwa [map_one, map_one, one_mul] at h

end Plus

section Inter

variable (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂]
  (hden₁₂ : HasDenominatorPower P {f * f, f, 1} (1 * f) S₁₂)

-- `A⟨X, Y⟩ → A⟨X, Y⟩ ⧸ (f² - f X, 1 - f Y) ≃ A⟨{f², f, 1}/(1 · f)⟩`.
private noncomputable def laurentHom₁₂ :
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      UniformSpace.Completion S₁₂ :=
  rationalQuotientHom P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ _ (mem_numerators_inter f)
    (eq_denom_or_mem_range_inter f)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one)
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _)

private theorem laurentHom₁₂_surjective :
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    Function.Surjective (laurentHom₁₂ P f S₁₂ hden₁₂) :=
  rationalQuotientHom_surjective P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ _ _ _ _ _

private theorem continuous_laurentHom₁₂ :
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    Continuous (laurentHom₁₂ P f S₁₂ hden₁₂) :=
  continuous_rationalQuotientHom P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ _ _ _ _ _

private theorem laurentHom₁₂_weightedC (a : A) :
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    laurentHom₁₂ P f S₁₂ hden₁₂ (weightedC _ isWeightFamily_one_weight a) =
      toCompletionLoc P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ a :=
  rationalQuotientHom_weightedC P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ _ _ _ _ _ a

-- `Y` is an inverse of `f`.
private theorem laurentHom₁₂_weightedC_mul_weightedX_eq_one :
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    laurentHom₁₂ P f S₁₂ hden₁₂ (weightedC _ isWeightFamily_one_weight f) *
      laurentHom₁₂ P f S₁₂ hden₁₂ (weightedX _ isWeightFamily_one_weight 1) = 1 := by
  let _ := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have h := rationalQuotientHom_weightedC_mul_weightedX P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ _
    (mem_numerators_inter f) (eq_denom_or_mem_range_inter f)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one)
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _) 1
  simp only [one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_one] at h
  exact h

-- `X` is `f`, since `f X = f²` and `f` is a unit.
private theorem laurentHom₁₂_weightedX_zero :
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    laurentHom₁₂ P f S₁₂ hden₁₂ (weightedX _ isWeightFamily_one_weight 0) =
      laurentHom₁₂ P f S₁₂ hden₁₂ (weightedC _ isWeightFamily_one_weight f) := by
  let _ := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have h := rationalQuotientHom_weightedC_mul_weightedX P {f * f, f, 1} (1 * f) S₁₂ hden₁₂ _
    (mem_numerators_inter f) (eq_denom_or_mem_range_inter f)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one)
    (Ideal.isClosed_weightedRestrictedSubring_one_weight _) 0
  simp only [one_mul, Matrix.cons_val_zero, map_mul] at h
  exact (IsUnit.of_mul_eq_one _
    (laurentHom₁₂_weightedC_mul_weightedX_eq_one P f S₁₂ hden₁₂)).mul_left_cancel h

-- The kernel is `(f² - f X, 1 - f Y) ⊆ (f - X, 1 - XY)`.
private theorem mem_span_of_laurentHom₁₂_eq_zero
    (u : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight)
    (hu : letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
      letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
      letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
      laurentHom₁₂ P f S₁₂ hden₁₂ u = 0) : u ∈ Ideal.span
      {weightedC _ isWeightFamily_one_weight f - weightedX _ isWeightFamily_one_weight 0,
        1 - weightedX _ isWeightFamily_one_weight 0 * weightedX _ isWeightFamily_one_weight 1} := by
  have hmem := (rationalQuotientHom_eq_zero_iff_mem P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    _ _ _ _ _).1 hu
  rw [rationalRelationIdeal_def] at hmem
  refine Ideal.span_le.2 (Set.range_subset_iff.2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)) hmem
  · refine Ideal.mem_span_pair.2 ⟨weightedC _ _ f, 0, ?_⟩
    simp only [Matrix.cons_val_zero, map_mul, map_one]
    ring
  · refine Ideal.mem_span_pair.2 ⟨-weightedX _ _ 1, 1, ?_⟩
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, map_mul, map_one]
    ring

end Inter

variable (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂]
  (hden₁ : HasDenominatorPower P {f, 1} 1 S₁) (hden₂ : HasDenominatorPower P {1} f S₂)
  (hden₁₂ : HasDenominatorPower P {f * f, f, 1} (1 * f) S₁₂)

-- Restricting from `A⟨f/1⟩` to the overlap corresponds to `A⟨T⟩ → A⟨X, Y⟩`, `T ↦ X`.
private theorem restrictionRingHom_laurentHom₁
    (g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    restrictionRingHom P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl (by simp)
        (laurentHom₁ P f S₁ hden₁ g) = laurentHom₁₂ P f S₁₂ hden₁₂
        (weightedRename Fin.castSuccEmb _ _ (fun _ ↦ subset_rfl) g) := by
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  refine apply_eq_apply_weightedRename (continuous_restrictionRingHom ..)
    (continuous_laurentHom₁ P f S₁ hden₁) (continuous_laurentHom₁₂ P f S₁₂ hden₁₂) (fun _ ↦ ?_)
    (fun i ↦ ?_) g
  -- on constants, and on `T`, which goes to `f` on both sides
  · rw [laurentHom₁_weightedC, laurentHom₁₂_weightedC, ← RingHom.comp_apply,
      restrictionRingHom_comp_toCompletionLoc]
  · rw [Subsingleton.elim i 0, laurentHom₁_weightedX, laurentHom₁_weightedC, Fin.coe_castSuccEmb,
      Fin.castSucc_zero, laurentHom₁₂_weightedX_zero, laurentHom₁₂_weightedC, ← RingHom.comp_apply,
      restrictionRingHom_comp_toCompletionLoc]

-- Restricting from `A⟨1/f⟩` to the overlap corresponds to `A⟨T⟩ → A⟨X, Y⟩`, `T ↦ Y`.
private theorem restrictionRingHom_laurentHom₂
    (h : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f) (by simp)
        (laurentHom₂ P f S₂ hden₂ h) = laurentHom₁₂ P f S₁₂ hden₁₂
        (weightedRename (Fin.succEmb 1) _ _ (fun _ ↦ subset_rfl) h) := by
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have hC (a : A) : restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1
      (mul_comm 1 f) (by simp) (laurentHom₂ P f S₂ hden₂ (weightedC _ _ a)) =
        laurentHom₁₂ P f S₁₂ hden₁₂ (weightedC _ _ a) := by
    rw [laurentHom₂_weightedC, laurentHom₁₂_weightedC, ← RingHom.comp_apply,
      restrictionRingHom_comp_toCompletionLoc]
  refine apply_eq_apply_weightedRename (continuous_restrictionRingHom ..)
    (continuous_laurentHom₂ P f S₂ hden₂) (continuous_laurentHom₁₂ P f S₁₂ hden₁₂) hC (fun i ↦ ?_) h
  -- on `T`: both sides are inverses of `f`
  rw [Subsingleton.elim i 0, Fin.coe_succEmb, Fin.succ_zero_eq_one]
  exact inv_unique (by rw [← hC, ← map_mul, laurentHom₂_weightedC_mul_weightedX_eq_one, map_one])
    (laurentHom₁₂_weightedC_mul_weightedX_eq_one P f S₁₂ hden₁₂)

end Pieces

/-! ### Exactness -/

section Differential

variable {B₁ B₂ B₁₂ : Type*} [CommRing B₁] [CommRing B₂] [CommRing B₁₂]

-- The difference of restrictions on a pair.
private theorem restriction_sub_apply (ρ₁ : B₁ →+* B₁₂) (ρ₂ : B₂ →+* B₁₂) (x₁ : B₁) (x₂ : B₂) :
    (ρ₁.toAddMonoidHom.comp (AddMonoidHom.fst B₁ B₂) -
      ρ₂.toAddMonoidHom.comp (AddMonoidHom.snd B₁ B₂)) (x₁, x₂) = ρ₁ x₁ - ρ₂ x₂ := rfl

end Differential

section LaurentCover

-- The only use of decidable equality is to spell the concrete numerator sets `{f, 1}`, `{1}` and
-- `{f * f, f, 1}`, so it is supplied classically instead of being assumed of `A`.
attribute [local instance] Classical.decEq

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStronglyNoetherian A]
  (P : PairOfDefinition A) (f : A)
  (S₁ : Type*) [CommRing S₁] [Algebra A S₁] [IsLocalization.Away (1 : A) S₁]
  (S₂ : Type*) [CommRing S₂] [Algebra A S₂] [IsLocalization.Away f S₂]
  (S₁₂ : Type*) [CommRing S₁₂] [Algebra A S₁₂] [IsLocalization.Away (1 * f) S₁₂]
  (hden₂ : HasDenominatorPower P {1} f S₂)

/-- **Wedhorn's Lemma 8.33, exactness in the middle.** Let `A` be a complete Hausdorff strongly
noetherian Tate ring and `f ∈ A`, and let `U₁ = R({f, 1}/1)`, `U₂ = R({1}/f)` and
`U₁ ∩ U₂ = R({f², f, 1}/(1 · f))`. In

```text
A → A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩,      a ↦ (a, a),      (x, y) ↦ x|U₁∩U₂ - y|U₁∩U₂,
```

the kernel of the second map is the image of the first. The restriction maps are those of the
refinements with cofactors `f` and `1`. The first map is injective (`laurentCover_injective`) and
the second surjective (`laurentCover_surjective`). Only `U₂` comes with a standing hypothesis: the
one for `U₁` is automatic at the denominator `1`
(`TauCeti.Huber.PairOfDefinition.hasDenominatorPower_denom_one`), and the one for `U₁ ∩ U₂` is
built from those two by `TauCeti.Huber.PairOfDefinition.hasDenominatorPower_mul`. -/
theorem laurentCover_exact :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
      (by simp) (by simp) hden₁ hden₂
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    Function.Exact
      (RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁) (toCompletionLoc P {1} f S₂ hden₂))
      ((restrictionRingHom P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.fst (UniformSpace.Completion S₁) (UniformSpace.Completion S₂)) -
        (restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f)
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.snd (UniformSpace.Completion S₁) (UniformSpace.Completion S₂))) := by
  have hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  have hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
    (by simp) (by simp) hden₁ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  rintro ⟨x₁, x₂⟩
  rw [restriction_sub_apply]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨c, h₁, h₂⟩ := exists_eq_weightedC_of_apply_eq f (laurentHom₁_surjective P f S₁ hden₁)
      (laurentHom₂_surjective P f S₂ hden₂) (laurentHom₁_weightedX P f S₁ hden₁)
      (laurentHom₂_weightedC_mul_weightedX_eq_one P f S₂ hden₂)
      (restrictionRingHom_laurentHom₁ P f S₁ S₁₂ hden₁ hden₁₂)
      (restrictionRingHom_laurentHom₂ P f S₂ S₁₂ hden₂ hden₁₂)
      (mem_span_of_laurentHom₁₂_eq_zero P f S₁₂ hden₁₂) x₁ x₂ <| sub_eq_zero.1 h
    simp only [laurentHom₁_weightedC, laurentHom₂_weightedC] at h₁ h₂
    exact ⟨c, Prod.ext h₁ h₂⟩
  · rintro ⟨a, rfl, rfl⟩
    simp only [← RingHom.comp_apply, restrictionRingHom_comp_toCompletionLoc, sub_self]

/-- **Wedhorn's Lemma 8.33, surjectivity.** In the notation of `laurentCover_exact`, the
difference of restrictions

```text
A⟨U₁⟩ × A⟨U₂⟩ → A⟨U₁ ∩ U₂⟩,      (x, y) ↦ x|U₁∩U₂ - y|U₁∩U₂
```

is surjective. As in `laurentCover_exact`, only `U₂` comes with a standing hypothesis: the one for
`U₁` is automatic at the denominator `1` and the one for `U₁ ∩ U₂` is built from those two.
Exactness in the middle and injectivity of `a ↦ (a, a)` are `laurentCover_exact` and
`laurentCover_injective`. -/
theorem laurentCover_surjective :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
      (by simp) (by simp) hden₁ hden₂
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    letI := locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    letI := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
    Function.Surjective
      ((restrictionRingHom P {f, 1} 1 S₁ hden₁ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ f rfl
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.fst (UniformSpace.Completion S₁) (UniformSpace.Completion S₂)) -
        (restrictionRingHom P {1} f S₂ hden₂ {f * f, f, 1} (1 * f) S₁₂ hden₁₂ 1 (mul_comm 1 f)
          (by simp)).toAddMonoidHom.comp
          (AddMonoidHom.snd (UniformSpace.Completion S₁) (UniformSpace.Completion S₂))) := by
  have hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  have hden₁₂ := hasDenominatorPower_mul P {f, 1} {1} {f * f, f, 1} 1 f S₁ S₂ S₁₂
    (by simp) (by simp) hden₁ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
  have _ := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
  have _ := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
  have _ := isUniformAddGroup_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  have _ := isTopologicalRing_locUniformSpace P {f * f, f, 1} (1 * f) S₁₂ hden₁₂
  intro y
  obtain ⟨x₁, x₂, h⟩ := exists_sub_eq_of_surjective (laurentHom₁₂_surjective P f S₁₂ hden₁₂)
    (restrictionRingHom_laurentHom₁ P f S₁ S₁₂ hden₁ hden₁₂)
    (restrictionRingHom_laurentHom₂ P f S₂ S₁₂ hden₂ hden₁₂)
    (by simp [laurentHom₁₂_weightedX_zero, laurentHom₁₂_weightedC_mul_weightedX_eq_one]) y
  exact ⟨(x₁, x₂), (restriction_sub_apply _ _ _ _).trans h⟩

end LaurentCover

/-! ### Injectivity -/

section Cover

-- As in `laurentCover_exact`, decidable equality is only needed for the numerator sets `{f, 1}`
-- and `{1}`, so it is supplied classically instead of being assumed of `A`.
attribute [local instance] Classical.decEq

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **The two Laurent pieces cover the adic spectrum.** For `f ∈ A`, every point of
`Spa(A, A⁺)` lies in `U₁ = R({f, 1}/1)` or in `U₂ = R({1}/f)`, indexed here by `Bool` so that
the two pieces form a single family. Every point lies in `R({f, 1}/f)` or in `R({f, 1}/1)`, and
the first of these lies in `R({1}/f)`.

This is the geometric half of the two-piece Laurent cover; `laurentCover_exact`,
`laurentCover_surjective` and `laurentCover_injective` are the algebraic half. -/
theorem spa_subset_iUnion_laurentCover (Aplus : Subring A) (f : A) :
    spa Aplus ⊆ ⋃ b : Bool, rationalSubset Aplus (cond b {f, 1} {1}) (cond b 1 f) := by
  intro v hv
  have hspan : Ideal.span (({f, 1} : Finset A) : Set A) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one
  obtain ⟨s, hs, hvs⟩ := mem_rationalSubset_of_span_eq_top_of_mem_spa Aplus hspan hv
  rcases Finset.mem_insert.1 hs with rfl | hs
  · refine Set.mem_iUnion.2 ⟨false, ?_⟩
    rw [mem_rationalSubset_iff] at hvs ⊢
    exact ⟨hvs.1, fun t ht ↦ hvs.2.1 t (by simp_all), hvs.2.2⟩
  · rw [Finset.mem_singleton.1 hs] at hvs
    exact Set.mem_iUnion.2 ⟨true, hvs⟩

end Cover

section Injective

universe v

-- As in `laurentCover_exact`, decidable equality is only needed for the numerator sets `{f, 1}`
-- and `{1}`, so it is supplied classically instead of being assumed of `A`.
attribute [local instance] Classical.decEq

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsStronglyNoetherian A]

/-- **Wedhorn's Lemma 8.33, injectivity.** Let `A` be a complete Hausdorff strongly noetherian
Tate ring and `f ∈ A`. The map `A → A⟨U₁⟩ × A⟨U₂⟩`, `a ↦ (a, a)`, into the coordinate rings of
`U₁ = R({f, 1}/1)` and `U₂ = R({1}/f)` is injective. Unlike the other two results of this file it
needs no presentation of `U₁ ∩ U₂`, and no ring of integral elements has to be chosen. The two
localisations are asked to lie in one universe, as for the family in
`pi_toCompletionLoc_injective`. Exactness in the middle and surjectivity are `laurentCover_exact`
and `laurentCover_surjective`. -/
theorem laurentCover_injective (P : PairOfDefinition A) (f : A) (S₁ S₂ : Type v) [CommRing S₁]
    [Algebra A S₁] [IsLocalization.Away (1 : A) S₁] [CommRing S₂] [Algebra A S₂]
    [IsLocalization.Away f S₂] (hden₂ : HasDenominatorPower P {1} f S₂) :
    letI hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
    letI := locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isUniformAddGroup_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := isTopologicalRing_locUniformSpace P {f, 1} 1 S₁ hden₁
    letI := locUniformSpace P {1} f S₂ hden₂
    letI := isUniformAddGroup_locUniformSpace P {1} f S₂ hden₂
    letI := isTopologicalRing_locUniformSpace P {1} f S₂ hden₂
    Function.Injective
      (RingHom.prod (toCompletionLoc P {f, 1} 1 S₁ hden₁) (toCompletionLoc P {1} f S₂ hden₂)) := by
  have hden₁ := hasDenominatorPower_denom_one P {f, 1} S₁
  -- the cover as a family indexed by `Bool`, `true` for `R({f, 1}/1)` and `false` for `R({1}/f)`
  let S : Bool → Type v := fun b ↦ cond b S₁ S₂
  let _ : ∀ b, CommRing (S b) := fun b ↦ b.casesOn ‹CommRing S₂› ‹CommRing S₁›
  let _ : ∀ b, Algebra A (S b) := fun b ↦ b.casesOn ‹Algebra A S₂› ‹Algebra A S₁›
  have _ : ∀ b, IsLocalization.Away (cond b 1 f) (S b) := fun b ↦ b.casesOn ‹_› ‹_›
  have hinj := pi_toCompletionLoc_injective P _ (Pair.powerBounded A).isRingOfIntegralElements
    (Pair.powerBounded_plus (A := A) ▸ P.le_powerBoundedSubring) _ _ S
    (fun b ↦ b.casesOn hden₂ hden₁) (spa_subset_iUnion_laurentCover _ f)
  exact fun a b hab ↦ hinj (funext (Bool.rec (congrArg Prod.snd hab) (congrArg Prod.fst hab)))

end Injective

end TauCeti.ValuationSpectrum

end
