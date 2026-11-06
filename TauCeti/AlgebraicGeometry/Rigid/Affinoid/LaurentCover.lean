/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Laurent
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Laurent.Cover
import TauCeti.RingTheory.Affinoid.Subdomain.Flat

/-!
# The classical two-piece Laurent cover

For an affinoid algebra `A` and `f : A`, the domains `|f| ≤ 1` and `|f| ≥ 1`
cover the classical spectrum. Their coordinate algebras and the overlap retain all
nilpotents. The difference of restrictions, with sign second minus first, is surjective;
its kernel is the image of `A`.

We compare the native Gauss-normed Laurent fractions with the quotient presentations
in `TauCeti.Huber.exact_algebraMap_laurentCoverDiff`. Thus the classical exact sequence
uses the same algebraic Laurent-series decomposition as the adic theory.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§8.2.1–8.2.2.
* T. Wedhorn, *Adic Spaces*, Lemma 8.33.
-/

public section

namespace TauCeti.LaurentCover

open _root_.MvPowerSeries TauCeti.MvPowerSeries TauCeti.Huber

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A]

local notation "T(" n ")" => IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1)
local notation "W(" n ")" =>
  weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set A)) isWeightFamily_one_weight
local notation "X₀" => (Subtype.mk (X 0) (isRestricted_X _ 0) : T(2))
local notation "X₁" => (Subtype.mk (X 1) (isRestricted_X _ 1) : T(2))

private noncomputable def gaussAlgEquiv (n : ℕ) : W(n) ≃ₐ[A] T(n) :=
  AlgEquiv.ofRingEquiv (f := restrictedMvPowerSeriesGaussEquiv)
    (fun a ↦ restrictedMvPowerSeriesGaussEquiv_weightedC a)

private theorem leIdeal_eq (f : A) :
    laurentFractionIdeal (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A) =
      (laurentCoverLeIdeal A f).map (gaussAlgEquiv 1) := by
  simp [laurentFractionIdeal_def, laurentCoverLeIdeal_def, Ideal.map_span,
    gaussAlgEquiv, Set.range_unique, Fin.default_eq_zero]
  simpa only [neg_sub] using (Ideal.span_singleton_neg
    (algebraMap A T(1) f - ⟨X 0, isRestricted_X _ 0⟩))

private theorem geIdeal_eq (f : A) :
    laurentFractionIdeal (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f) =
      (laurentCoverGeIdeal A f).map (gaussAlgEquiv 1) := by
  simp [laurentFractionIdeal_def, laurentCoverGeIdeal_def, Ideal.map_span,
    gaussAlgEquiv, Set.range_unique, Fin.default_eq_zero]
  simpa only [neg_sub] using (Ideal.span_singleton_neg
    (1 - algebraMap A T(1) f * ⟨X 0, isRestricted_X _ 0⟩))

/-- The Huber quotient presentation of the lower Laurent piece is its native Gauss-normed
Laurent fraction algebra, compatibly with the ambient algebra. -/
noncomputable def huberLeAlgEquiv (f : A) :
    laurentCoverLe A f ≃ₐ[A] LaurentFraction (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A) :=
  Ideal.quotientEquivAlg _ _ (gaussAlgEquiv 1) (leIdeal_eq f)

/-- The Huber quotient presentation of the upper Laurent piece is its native Gauss-normed
Laurent fraction algebra, compatibly with the ambient algebra. -/
noncomputable def huberGeAlgEquiv (f : A) :
    laurentCoverGe A f ≃ₐ[A] LaurentFraction (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f) :=
  Ideal.quotientEquivAlg _ _ (gaussAlgEquiv 1) (geIdeal_eq f)

private theorem overlapIdeal_eq (f : A) :
    laurentFractionIdeal (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f) =
      Ideal.span {1 - X₀ * X₁, algebraMap A T(2) f - X₀} := by
  have hL : laurentFractionIdeal (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f) =
      Ideal.span {X₀ - algebraMap A T(2) f, algebraMap A T(2) f * X₁ - 1} := by
    simp [laurentFractionIdeal_def, Set.range_unique, Fin.default_eq_zero, Ideal.span_insert]
  rw [hL]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ (rfl | rfl)
    · simpa only [SetLike.mem_coe, neg_sub] using
        (Ideal.span {1 - X₀ * X₁, algebraMap A T(2) f - X₀}).neg_mem
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · exact Ideal.mem_span_pair.mpr ⟨-1, X₁, by ring⟩
  · apply Ideal.span_le.mpr
    rintro _ (rfl | rfl)
    · exact Ideal.mem_span_pair.mpr ⟨-X₁, -1, by ring⟩
    · simpa only [SetLike.mem_coe, neg_sub] using
        (Ideal.span {X₀ - algebraMap A T(2) f, algebraMap A T(2) f * X₁ - 1}).neg_mem
          (Ideal.subset_span (Set.mem_insert _ _))

private noncomputable def overlapRelation (f : A) : Ideal (W(2)) :=
  Ideal.span {(weightedC (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight f -
    weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 0)}

private theorem overlapRelation_eq_map (f : A) :
    laurentCoverOverlapIdeal A f =
      (overlapRelation f).map (Ideal.Quotient.mk (laurentIdeal A)) := by
  simp [overlapRelation, laurentCoverOverlapIdeal_def, Ideal.map_span,
    ← algebraMap_weightedRestrictedSubring, Ideal.Quotient.mk_algebraMap]

private theorem map_overlapIdeal (f : A) :
    laurentFractionIdeal (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f) =
      (laurentIdeal A ⊔ overlapRelation f).map (gaussAlgEquiv 2) := by
  have hI : laurentIdeal A = Ideal.span
      {1 - weightedX _ isWeightFamily_one_weight (0 : Fin 2) *
        weightedX _ isWeightFamily_one_weight 1} := by
    ext x
    rw [mem_laurentIdeal, Ideal.mem_span_singleton]
    rfl
  rw [overlapIdeal_eq, Ideal.map_sup, hI, overlapRelation, Ideal.map_span, Ideal.map_span]
  simp [gaussAlgEquiv, ← Ideal.span_insert]

/-- The Huber double-quotient presentation of the overlap is the native Laurent fraction
algebra with relations `X = f` and `fY = 1`, compatibly with the ambient algebra. -/
noncomputable def huberOverlapAlgEquiv (f : A) :
    laurentCoverOverlap A f ≃ₐ[A]
      LaurentFraction (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f) := by
  exact (Ideal.quotientEquivAlgOfEq A (overlapRelation_eq_map f)).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ A (laurentIdeal A) (overlapRelation f)).trans
      (Ideal.quotientEquivAlg _ _ (gaussAlgEquiv 2) (map_overlapIdeal f)))

/-- The lower-piece comparison preserves every restricted-series representative. -/
@[simp]
theorem huberLeAlgEquiv_mk (f : A) (g : W(1)) :
    huberLeAlgEquiv f (Ideal.Quotient.mk (laurentCoverLeIdeal A f) g) =
      Ideal.Quotient.mk (laurentFractionIdeal (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A))
        (restrictedMvPowerSeriesGaussEquiv g) :=
  Ideal.quotientEquivAlg_mk _ _ _ _

/-- The upper-piece comparison preserves every restricted-series representative. -/
@[simp]
theorem huberGeAlgEquiv_mk (f : A) (g : W(1)) :
    huberGeAlgEquiv f (Ideal.Quotient.mk (laurentCoverGeIdeal A f) g) =
      Ideal.Quotient.mk (laurentFractionIdeal (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f))
        (restrictedMvPowerSeriesGaussEquiv g) :=
  Ideal.quotientEquivAlg_mk _ _ _ _

/-- The overlap comparison preserves the two-variable series underlying a double quotient. -/
@[simp]
theorem huberOverlapAlgEquiv_mk_mk (f : A) (g : W(2)) :
    huberOverlapAlgEquiv f (Ideal.Quotient.mk (laurentCoverOverlapIdeal A f)
      (Ideal.Quotient.mk (laurentIdeal A) g)) =
      Ideal.Quotient.mk (laurentFractionIdeal (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f))
        (restrictedMvPowerSeriesGaussEquiv g) := by
  simp only [huberOverlapAlgEquiv]
  exact (Ideal.quotientEquivAlg _ _ (gaussAlgEquiv 2) (map_overlapIdeal f)).toRingEquiv.congr_arg
    (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk (laurentIdeal A) (overlapRelation f) g)

local notation "L(" f ")" => LaurentFraction (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A)
local notation "G(" f ")" => LaurentFraction (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f)
local notation "O(" f ")" => LaurentFraction (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f)

/-- Restriction from the piece `|f| ≤ 1` to `|f| = 1`, as a map of native Laurent
fraction algebras. It is the identity on the ambient algebra. -/
noncomputable def leToOverlap (f : A) : L(f) →ₐ[A] O(f) :=
  (huberOverlapAlgEquiv f).toAlgHom.comp
    ((laurentCoverLeToOverlap A f).comp (huberLeAlgEquiv f).symm.toAlgHom)

/-- Restriction from the piece `|f| ≥ 1` to `|f| = 1`, as a map of native Laurent
fraction algebras. It is the identity on the ambient algebra. -/
noncomputable def geToOverlap (f : A) : G(f) →ₐ[A] O(f) :=
  (huberOverlapAlgEquiv f).toAlgHom.comp
    ((laurentCoverGeToOverlap A f).comp (huberGeAlgEquiv f).symm.toAlgHom)

/-- The lower-piece restriction commutes with the Huber quotient comparisons. -/
@[simp]
theorem leToOverlap_huberLeAlgEquiv (f : A) (u : laurentCoverLe A f) :
    leToOverlap f (huberLeAlgEquiv f u) =
      huberOverlapAlgEquiv f (laurentCoverLeToOverlap A f u) := by
  simp [leToOverlap]

/-- The upper-piece restriction commutes with the Huber quotient comparisons. -/
@[simp]
theorem geToOverlap_huberGeAlgEquiv (f : A) (v : laurentCoverGe A f) :
    geToOverlap f (huberGeAlgEquiv f v) =
      huberOverlapAlgEquiv f (laurentCoverGeToOverlap A f v) := by
  simp [geToOverlap]

/-- The differential for the classical two-piece Laurent cover, with sign second
restriction minus first restriction. -/
noncomputable def diff (f : A) : (L(f) × G(f)) →ₗ[A] O(f) :=
  (geToOverlap f).toLinearMap.comp (LinearMap.snd A _ _) -
    (leToOverlap f).toLinearMap.comp (LinearMap.fst A _ _)

@[simp]
theorem diff_apply (f : A) (u : L(f)) (v : G(f)) :
    diff f (u, v) = geToOverlap f v - leToOverlap f u := (rfl)

/-- The quotient comparisons intertwine the classical differential with the negative of
the Huber differential, whose convention is first minus second. -/
theorem diff_comparison (f : A) (u : laurentCoverLe A f) (v : laurentCoverGe A f) :
    diff f (huberLeAlgEquiv f u, huberGeAlgEquiv f v) =
      -huberOverlapAlgEquiv f (laurentCoverDiff A f (u, v)) := by
  simp [laurentCoverDiff_apply, neg_sub]

variable [CompleteSpace A]

/-- **Surjectivity in the classical Laurent sequence.** Every section on the overlap
is a difference of restrictions of sections on the two Laurent pieces. No affinoidness
hypothesis is needed for this algebraic assertion. -/
theorem diff_surjective (f : A) : Function.Surjective (diff f) := by
  intro w
  obtain ⟨⟨u, v⟩, huv⟩ :=
    laurentCoverDiff_surjective A f ((huberOverlapAlgEquiv f).symm (-w))
  refine ⟨(huberLeAlgEquiv f u, huberGeAlgEquiv f v), ?_⟩
  rw [diff_comparison, huv, AlgEquiv.apply_symm_apply, neg_neg]

/-- **Exactness in the classical Laurent sequence.** Sections on the two pieces with
equal restrictions to the overlap are precisely the restrictions of one element of `A`.
The statement applies to complete ultrametric normed rings, including the zero ring. -/
theorem exact_algebraMap_diff (f : A) :
    Function.Exact (algebraMap A (L(f) × G(f))) (diff f) := by
  rintro ⟨u, v⟩
  obtain ⟨u, rfl⟩ := (huberLeAlgEquiv f).surjective u
  obtain ⟨v, rfl⟩ := (huberGeAlgEquiv f).surjective v
  rw [diff_comparison, neg_eq_zero, EmbeddingLike.map_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (exact_algebraMap_laurentCoverDiff A f (u, v)).mp h
    exact ⟨a, Prod.ext
      (by simpa using congrArg (huberLeAlgEquiv f) (congrArg Prod.fst ha))
      (by simpa using congrArg (huberGeAlgEquiv f) (congrArg Prod.snd ha))⟩
  · rintro ⟨a, ha⟩
    apply (exact_algebraMap_laurentCoverDiff A f (u, v)).mpr
    refine ⟨a, Prod.ext ((huberLeAlgEquiv f).injective ?_) ((huberGeAlgEquiv f).injective ?_)⟩
    · simpa using congrArg Prod.fst ha
    · simpa using congrArg Prod.snd ha

section Affinoid

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra K A] (hA : IsAffinoidAlgebra K A)

include hA in
/-- **Injectivity in the classical Laurent sequence.** The restrictions to `|f| ≤ 1`
and `|f| ≥ 1` jointly detect every element, including nilpotents. -/
theorem injective_algebraMap (f : A) :
    Function.Injective (algebraMap A (L(f) × G(f))) := by
  let B : Bool → Type _ := fun b ↦ if b then G(f) else L(f)
  let : (b : Bool) → CommRing (B b) := fun b ↦ by cases b <;> dsimp [B] <;> infer_instance
  let : (b : Bool) → Algebra K (B b) := fun b ↦ by cases b <;> dsimp [B] <;> infer_instance
  let φ : (b : Bool) → A →ₐ[K] B b := fun b ↦ by
    cases b
    · exact IsScalarTower.toAlgHom K A (L(f))
    · exact IsScalarTower.toAlgHom K A (G(f))
  let U : Bool → Set (MaximalSpectrum A) := fun b ↦ if b then
    laurentDomain K (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f) else
    laurentDomain K (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A)
  have hφ : ∀ b, IsAffinoidSubdomainMap (φ b) (U b) := by
    intro b
    cases b <;> exact LaurentFraction.isAffinoidSubdomainMap hA
  have hcover : ∀ x : MaximalSpectrum A, ∃ b, x ∈ U b := by
    intro x
    rcases le_total (pointNorm K x f) 1 with hx | hx
    · exact ⟨false, by simpa [U, mem_laurentDomain] using hx⟩
    · exact ⟨true, by simpa [U, mem_laurentDomain] using hx⟩
  have hinj := (IsAffinoidSubdomainMap.faithfullyFlat_pi hφ hA hcover).injective
  intro a b hab
  apply hinj
  funext i
  cases i
  · exact congrArg Prod.fst hab
  · exact congrArg Prod.snd hab

include hA in
/-- **Gluing on the classical two-piece Laurent cover.** A compatible pair of sections
comes from a unique element of the ambient affinoid algebra. -/
theorem existsUnique_gluing (f : A) (u : L(f)) (v : G(f))
    (h : leToOverlap f u = geToOverlap f v) :
    ∃! a : A, algebraMap A (L(f)) a = u ∧ algebraMap A (G(f)) a = v := by
  obtain ⟨a, ha⟩ := (exact_algebraMap_diff f (u, v)).mp (by simp [diff_apply, h])
  refine ⟨a, ⟨congrArg Prod.fst ha, congrArg Prod.snd ha⟩, ?_⟩
  intro b hb
  exact injective_algebraMap hA f (Prod.ext (hb.1.trans (congrArg Prod.fst ha).symm)
    (hb.2.trans (congrArg Prod.snd ha).symm))

end Affinoid

end TauCeti.LaurentCover
