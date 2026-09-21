/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Laurent.Basic

import Mathlib.RingTheory.Ideal.Prod
import Mathlib.Tactic.LinearCombination

/-!
# The two-piece Laurent cover

Let `A` be a complete separated nonarchimedean ring and let `f : A`.  The two Laurent pieces and
their overlap have the presentations

```text
A⟨X⟩/(f-X),   A⟨Y⟩/(1-fY),   A⟨X,Y⟩/(1-XY, f-X).
```

This file descends the exact Laurent row from
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Laurent.Basic` to these presentations.  The
difference of the two restriction maps is surjective, and its kernel consists exactly of pairs of
equal constants.  This is the algebraic exactness assertion for the two-piece Laurent cover in
Wedhorn's Lemma 8.33.

The proof uses the decomposition of every restricted Laurent series as a series in `X` plus `Y`
times a series in `Y`.  Multiplying that decomposition by `f-X` expresses an arbitrary element of
the overlap relation ideal as the image of the two piece relation ideals.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.33, p. 84.

## Provenance

AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `37bbdaeb9`,
`projects/AdicSpaces/Adic spaces/LaurentCoverExact.lean`, treats the same cover.  Its complete
exactness theorem is for the discrete case; its general section stops before constructing the
difference map.  The quotient descent below instead uses Tau Ceti's exact Laurent row and its
restricted-series decomposition.
-/

public section

namespace TauCeti.Huber

variable (A : Type*) [CommRing A]

section Topological

variable [TopologicalSpace A] [NonarchimedeanRing A]

local notation "R₁" =>
  weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight

local notation "R₂" =>
  weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight

local notation "R±" => R₂ ⧸ laurentIdeal A

/-- The relation ideal `(f-X)` defining the Laurent piece `{|f| ≤ 1}`. -/
noncomputable def laurentCoverLeIdeal (f : A) : Ideal R₁ :=
  Ideal.span {weightedC _ isWeightFamily_one_weight f - weightedX _ isWeightFamily_one_weight 0}

/-- The defining presentation of `laurentCoverLeIdeal`. -/
theorem laurentCoverLeIdeal_def (f : A) :
    laurentCoverLeIdeal A f =
      Ideal.span {weightedC _ isWeightFamily_one_weight f -
        weightedX _ isWeightFamily_one_weight 0} :=
  by rfl

/-- Membership in the principal relation ideal defining the piece `{|f| ≤ 1}`. -/
theorem mem_laurentCoverLeIdeal_iff (f : A) {a : R₁} :
    a ∈ laurentCoverLeIdeal A f ↔
      ∃ b, b * (weightedC _ isWeightFamily_one_weight f -
        weightedX _ isWeightFamily_one_weight 0) = a := by
  rw [laurentCoverLeIdeal_def, Ideal.mem_span_singleton']

/-- The relation ideal `(1-fY)` defining the Laurent piece `{|f| ≥ 1}`. -/
noncomputable def laurentCoverGeIdeal (f : A) : Ideal R₁ :=
  Ideal.span {1 - weightedC _ isWeightFamily_one_weight f * weightedX _ isWeightFamily_one_weight 0}

/-- The defining presentation of `laurentCoverGeIdeal`. -/
theorem laurentCoverGeIdeal_def (f : A) :
    laurentCoverGeIdeal A f =
      Ideal.span {1 - weightedC _ isWeightFamily_one_weight f *
        weightedX _ isWeightFamily_one_weight 0} :=
  by rfl

/-- Membership in the principal relation ideal defining the piece `{|f| ≥ 1}`. -/
theorem mem_laurentCoverGeIdeal_iff (f : A) {a : R₁} :
    a ∈ laurentCoverGeIdeal A f ↔
      ∃ b, b * (1 - weightedC _ isWeightFamily_one_weight f *
        weightedX _ isWeightFamily_one_weight 0) = a := by
  rw [laurentCoverGeIdeal_def, Ideal.mem_span_singleton']

/-- The relation ideal `(f-X)` in `A⟨X, X⁻¹⟩`; quotienting by it defines the overlap of the
two Laurent pieces. -/
noncomputable def laurentCoverOverlapIdeal (f : A) : Ideal R± :=
  Ideal.span {algebraMap A R± f -
    Ideal.Quotient.mk (laurentIdeal A) (weightedX _ isWeightFamily_one_weight 0)}

/-- The defining presentation of `laurentCoverOverlapIdeal`. -/
theorem laurentCoverOverlapIdeal_def (f : A) :
    laurentCoverOverlapIdeal A f =
      Ideal.span {algebraMap A R± f -
        Ideal.Quotient.mk (laurentIdeal A) (weightedX _ isWeightFamily_one_weight 0)} :=
  by rfl

/-- Membership in the principal relation ideal defining the overlap. -/
theorem mem_laurentCoverOverlapIdeal_iff (f : A) {a : R±} :
    a ∈ laurentCoverOverlapIdeal A f ↔
      ∃ b, b * (algebraMap A R± f -
        Ideal.Quotient.mk (laurentIdeal A)
          (weightedX _ isWeightFamily_one_weight 0)) = a := by
  rw [laurentCoverOverlapIdeal_def, Ideal.mem_span_singleton']

/-- The coordinate ring of the Laurent piece `{|f| ≤ 1}`. -/
noncomputable abbrev laurentCoverLe (f : A) := R₁ ⧸ laurentCoverLeIdeal A f

/-- The coordinate ring of the Laurent piece `{|f| ≥ 1}`. -/
noncomputable abbrev laurentCoverGe (f : A) := R₁ ⧸ laurentCoverGeIdeal A f

/-- The coordinate ring of the overlap `{|f| = 1}` of the two Laurent pieces. -/
noncomputable abbrev laurentCoverOverlap (f : A) :=
  R± ⧸ laurentCoverOverlapIdeal A f

/-- In the overlap ring the class of `X` is the image of `f`. -/
@[simp]
theorem mk_weightedC_eq_mk_weightedX_in_laurentCoverOverlap (f : A) :
    Ideal.Quotient.mk (laurentCoverOverlapIdeal A f)
        (Ideal.Quotient.mk (laurentIdeal A) (weightedC _ isWeightFamily_one_weight f)) =
      Ideal.Quotient.mk (laurentCoverOverlapIdeal A f)
        (Ideal.Quotient.mk (laurentIdeal A) (weightedX _ isWeightFamily_one_weight 0)) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    laurentCoverOverlapIdeal]
  apply Ideal.subset_span
  rw [← algebraMap_weightedRestrictedSubring, Ideal.Quotient.mk_algebraMap]
  exact Set.mem_singleton _

private noncomputable def laurentCoverLeMap (f : A) :
    R₁ →ₐ[A] laurentCoverOverlap A f :=
  (Ideal.Quotient.mkₐ A (laurentCoverOverlapIdeal A f)).comp <|
    (Ideal.Quotient.mkₐ A (laurentIdeal A)).comp <|
      weightedRenameAlgHom Fin.castSuccEmb isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ subset_rfl)

private noncomputable def laurentCoverGeMap (f : A) :
    R₁ →ₐ[A] laurentCoverOverlap A f :=
  (Ideal.Quotient.mkₐ A (laurentCoverOverlapIdeal A f)).comp <|
    (Ideal.Quotient.mkₐ A (laurentIdeal A)).comp <|
      weightedRenameAlgHom (Fin.succEmb 1) isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ subset_rfl)

private theorem laurentCoverLeIdeal_le_ker (f : A) :
    laurentCoverLeIdeal A f ≤ RingHom.ker (laurentCoverLeMap A f) := by
  rw [laurentCoverLeIdeal, Ideal.span_le]
  rintro _ rfl
  apply (RingHom.mem_ker).2
  simp only [laurentCoverLeMap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    weightedRenameAlgHom_apply, map_sub, weightedRename_weightedC, weightedRename_weightedX]
  rw [Fin.castSuccEmb_apply, Fin.castSucc_zero',
    mk_weightedC_eq_mk_weightedX_in_laurentCoverOverlap, sub_self]

private theorem laurentCoverGeIdeal_le_ker (f : A) :
    laurentCoverGeIdeal A f ≤ RingHom.ker (laurentCoverGeMap A f) := by
  rw [laurentCoverGeIdeal, Ideal.span_le]
  rintro _ rfl
  apply (RingHom.mem_ker).2
  simp only [laurentCoverGeMap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    weightedRenameAlgHom_apply, map_sub, map_one, map_mul, weightedRename_weightedC,
    weightedRename_weightedX]
  rw [Fin.coe_succEmb, Fin.succ_zero_eq_one',
    mk_weightedC_eq_mk_weightedX_in_laurentCoverOverlap, ← map_mul,
    mk_weightedX_zero_mul_mk_weightedX_one A, map_one, sub_self]

/-- The restriction from the piece `{|f| ≤ 1}` to the overlap. -/
noncomputable def laurentCoverLeToOverlap (f : A) :
    laurentCoverLe A f →ₐ[A] laurentCoverOverlap A f :=
  Ideal.Quotient.liftₐ (laurentCoverLeIdeal A f) (laurentCoverLeMap A f)
    (laurentCoverLeIdeal_le_ker A f)

/-- The restriction from the piece `{|f| ≥ 1}` to the overlap. -/
noncomputable def laurentCoverGeToOverlap (f : A) :
    laurentCoverGe A f →ₐ[A] laurentCoverOverlap A f :=
  Ideal.Quotient.liftₐ (laurentCoverGeIdeal A f) (laurentCoverGeMap A f)
    (laurentCoverGeIdeal_le_ker A f)

/-- The restriction from `{|f| ≤ 1}` sends a representative to the same series in the overlap. -/
@[simp]
theorem laurentCoverLeToOverlap_mk (f : A) (a : R₁) :
    laurentCoverLeToOverlap A f (Ideal.Quotient.mk (laurentCoverLeIdeal A f) a) =
      Ideal.Quotient.mk (laurentCoverOverlapIdeal A f)
        (Ideal.Quotient.mk (laurentIdeal A)
          (weightedRename Fin.castSuccEmb isWeightFamily_one_weight
            isWeightFamily_one_weight (fun _ ↦ subset_rfl) a)) :=
  by
    have h := DFunLike.congr_fun
      (Ideal.Quotient.liftₐ_comp (laurentCoverLeIdeal A f) (laurentCoverLeMap A f)
        (fun _ ha ↦ (RingHom.mem_ker).1 (laurentCoverLeIdeal_le_ker A f ha))) a
    have h' : laurentCoverLeToOverlap A f
        (Ideal.Quotient.mk (laurentCoverLeIdeal A f) a) = laurentCoverLeMap A f a := by
      simpa only [laurentCoverLeToOverlap, AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk] using h
    rw [h']
    simp only [laurentCoverLeMap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      weightedRenameAlgHom_apply]

/-- The restriction from `{|f| ≥ 1}` sends a representative to the same series in the overlap. -/
@[simp]
theorem laurentCoverGeToOverlap_mk (f : A) (a : R₁) :
    laurentCoverGeToOverlap A f (Ideal.Quotient.mk (laurentCoverGeIdeal A f) a) =
      Ideal.Quotient.mk (laurentCoverOverlapIdeal A f)
        (Ideal.Quotient.mk (laurentIdeal A)
          (weightedRename (Fin.succEmb 1) isWeightFamily_one_weight
            isWeightFamily_one_weight (fun _ ↦ subset_rfl) a)) :=
  by
    have h := DFunLike.congr_fun
      (Ideal.Quotient.liftₐ_comp (laurentCoverGeIdeal A f) (laurentCoverGeMap A f)
        (fun _ ha ↦ (RingHom.mem_ker).1 (laurentCoverGeIdeal_le_ker A f ha))) a
    have h' : laurentCoverGeToOverlap A f
        (Ideal.Quotient.mk (laurentCoverGeIdeal A f) a) = laurentCoverGeMap A f a := by
      simpa only [laurentCoverGeToOverlap, AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk] using h
    rw [h']
    simp only [laurentCoverGeMap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      weightedRenameAlgHom_apply]

/-- The Čech differential for the two-piece Laurent cover: the difference of the two
restrictions to the overlap. -/
noncomputable def laurentCoverDiff (f : A) :
    (laurentCoverLe A f × laurentCoverGe A f) →ₗ[A] laurentCoverOverlap A f :=
  (laurentCoverLeToOverlap A f).toLinearMap.comp (LinearMap.fst A _ _) -
    (laurentCoverGeToOverlap A f).toLinearMap.comp (LinearMap.snd A _ _)

/-- The Čech differential sends a pair of sections to the difference of their restrictions. -/
@[simp]
theorem laurentCoverDiff_apply (f : A) (x : laurentCoverLe A f) (y : laurentCoverGe A f) :
    laurentCoverDiff A f (x, y) =
      laurentCoverLeToOverlap A f x - laurentCoverGeToOverlap A f y := by
  rfl

/-- On quotient representatives, the Čech differential is represented by `laurentDiff A (a, b)`
in the overlap quotient. -/
theorem laurentCoverDiff_mk (f : A) (a b : R₁) :
    laurentCoverDiff A f
        (Ideal.Quotient.mk (laurentCoverLeIdeal A f) a,
          Ideal.Quotient.mk (laurentCoverGeIdeal A f) b) =
      Ideal.Quotient.mk (laurentCoverOverlapIdeal A f) (laurentDiff A (a, b)) := by
  rw [laurentCoverDiff_apply, laurentCoverLeToOverlap_mk, laurentCoverGeToOverlap_mk]
  simp only [laurentDiff_apply, map_sub]

end Topological

section Complete

variable [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
  [T0Space A]

local notation "R₁" =>
  weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight

local notation "R₂" =>
  weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight

local notation "R±" => R₂ ⧸ laurentIdeal A

/-- The Čech differential of the two-piece Laurent cover is surjective. -/
theorem laurentCoverDiff_surjective (f : A) : Function.Surjective (laurentCoverDiff A f) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, rfl⟩ := laurentDiff_surjective A z
  exact ⟨(Ideal.Quotient.mk (laurentCoverLeIdeal A f) p.1,
    Ideal.Quotient.mk (laurentCoverGeIdeal A f) p.2), laurentCoverDiff_mk A f p.1 p.2⟩

private theorem laurentDiff_pieceRelations (f : A) (u : R₂) :
    ∃ c d : R₁,
      laurentDiff A
          ((weightedC _ isWeightFamily_one_weight f - weightedX _ isWeightFamily_one_weight 0) * c,
            (1 - weightedC _ isWeightFamily_one_weight f *
              weightedX _ isWeightFamily_one_weight 0) * d) =
        (algebraMap A R± f -
            Ideal.Quotient.mk (laurentIdeal A) (weightedX _ isWeightFamily_one_weight 0)) *
          Ideal.Quotient.mk (laurentIdeal A) u := by
  obtain ⟨c, d, w, hu⟩ :=
    exists_eq_weightedRename_add_weightedX_mul_weightedRename_add_one_sub_mul u
  refine ⟨c, d, ?_⟩
  rw [laurentDiff_apply]
  simp only [map_mul, map_sub, map_one, weightedRename_weightedC, weightedRename_weightedX]
  rw [Fin.castSuccEmb_apply, Fin.castSucc_zero', Fin.coe_succEmb, Fin.succ_zero_eq_one']
  have hu' : Ideal.Quotient.mk (laurentIdeal A) u =
      Ideal.Quotient.mk (laurentIdeal A)
        (weightedRename Fin.castSuccEmb isWeightFamily_one_weight isWeightFamily_one_weight
            (fun _ ↦ subset_rfl) c +
          weightedX _ isWeightFamily_one_weight 1 *
            weightedRename (Fin.succEmb 1) isWeightFamily_one_weight
              isWeightFamily_one_weight (fun _ ↦ subset_rfl) d) := by
    rw [Ideal.Quotient.eq, mem_laurentIdeal]
    refine ⟨w, ?_⟩
    rw [hu]
    ring
  rw [hu']
  simp only [map_add, map_mul]
  have hXY := mk_weightedX_zero_mul_mk_weightedX_one A
  ring_nf at hXY ⊢
  linear_combination hXY *
    Ideal.Quotient.mk (laurentIdeal A)
      (weightedRename (Fin.succEmb 1) isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ subset_rfl) d)

/-- **Wedhorn's Lemma 8.33, exactness in the middle.** For the two Laurent pieces
`{|f| ≤ 1}` and `{|f| ≥ 1}`, a pair of sections has equal restrictions to the overlap exactly
when it is a pair of equal constants. -/
theorem exact_algebraMap_laurentCoverDiff (f : A) :
    Function.Exact
      (algebraMap A (laurentCoverLe A f × laurentCoverGe A f))
      (laurentCoverDiff A f) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  constructor
  · intro h
    rw [laurentCoverDiff_mk, Ideal.Quotient.eq_zero_iff_mem,
      laurentCoverOverlapIdeal, Ideal.mem_span_singleton'] at h
    obtain ⟨q, hq⟩ := h
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨c, d, hcd⟩ := laurentDiff_pieceRelations A f u
    have hab : laurentDiff A
        ((weightedC _ isWeightFamily_one_weight f - weightedX _ isWeightFamily_one_weight 0) * c,
          (1 - weightedC _ isWeightFamily_one_weight f *
            weightedX _ isWeightFamily_one_weight 0) * d) = laurentDiff A (a, b) := by
      rw [hcd, mul_comm, hq]
    have hz : laurentDiff A
        (a - (weightedC _ isWeightFamily_one_weight f -
            weightedX _ isWeightFamily_one_weight 0) * c,
          b - (1 - weightedC _ isWeightFamily_one_weight f *
            weightedX _ isWeightFamily_one_weight 0) * d) = 0 := by
      rw [← Prod.mk_sub_mk, map_sub, hab, sub_self]
    obtain ⟨z, hz⟩ := (exact_algebraMap_laurentDiff A _).mp hz
    refine ⟨z, Prod.ext ?_ ?_⟩
    · have hz₁ : weightedC _ isWeightFamily_one_weight z =
          a - (weightedC _ isWeightFamily_one_weight f -
            weightedX _ isWeightFamily_one_weight 0) * c := by
        simpa only [Prod.algebraMap_apply, algebraMap_weightedRestrictedSubring] using
          congrArg Prod.fst hz
      -- Expose the product algebra map to compare its first component in the quotient.
      change Ideal.Quotient.mk (laurentCoverLeIdeal A f)
        (weightedC _ isWeightFamily_one_weight z) =
          Ideal.Quotient.mk (laurentCoverLeIdeal A f) a
      rw [hz₁, map_sub, sub_eq_self, Ideal.Quotient.eq_zero_iff_mem]
      rw [laurentCoverLeIdeal]
      exact Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self _)
    · have hz₂ : weightedC _ isWeightFamily_one_weight z =
          b - (1 - weightedC _ isWeightFamily_one_weight f *
            weightedX _ isWeightFamily_one_weight 0) * d := by
        simpa only [Prod.algebraMap_apply, algebraMap_weightedRestrictedSubring] using
          congrArg Prod.snd hz
      -- Expose the product algebra map to compare its second component in the quotient.
      change Ideal.Quotient.mk (laurentCoverGeIdeal A f)
        (weightedC _ isWeightFamily_one_weight z) =
          Ideal.Quotient.mk (laurentCoverGeIdeal A f) b
      rw [hz₂, map_sub, sub_eq_self, Ideal.Quotient.eq_zero_iff_mem]
      rw [laurentCoverGeIdeal]
      exact Ideal.mul_mem_right d _ (Ideal.mem_span_singleton_self _)
  · rintro ⟨z, hz⟩
    rw [← hz]
    -- Expose the product algebra map; both restrictions of a constant are equal.
    change laurentCoverDiff A f
      (Ideal.Quotient.mk (laurentCoverLeIdeal A f)
          (weightedC _ isWeightFamily_one_weight z),
        Ideal.Quotient.mk (laurentCoverGeIdeal A f)
          (weightedC _ isWeightFamily_one_weight z)) = 0
    rw [laurentCoverDiff_mk, laurentDiff_apply]
    simp

end Complete

end TauCeti.Huber

end
