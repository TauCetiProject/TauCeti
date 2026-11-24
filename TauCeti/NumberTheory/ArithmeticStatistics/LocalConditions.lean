/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Families defined by local conditions

A specification chooses an allowed subset in each local space. The resulting global family
is the intersection of their inverse images. Finiteness concerns the number of nontrivial
conditions, whereas largeness concerns the closures of the images of the *global* family.
Local masses use supplied measures and do not require those closures to equal the allowed sets.

The conventions for regularity and largeness follow Bhargava and Shankar,
*Binary quartic forms having bounded invariants, and the boundedness of the average rank of
elliptic curves*, §§2.5 and 3 (arXiv:1006.1002v3).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- A local specification for fixed localization maps. Fixing the maps as a parameter allows
conditions on the same spaces to be combined without any choice of transport. -/
@[ext]
structure LocalConditions {ι P : Type*} {X : P → Type*} (loc : (v : P) → ι → X v) where
  /-- The allowed subset at each place. -/
  cond : (v : P) → Set (X v)

namespace LocalConditions

variable {ι P : Type*} {X : P → Type*} {loc : (v : P) → ι → X v}
variable (σ τ : LocalConditions loc)

/-- The global objects satisfying every local condition. -/
def family : Set ι := {i | ∀ v, loc v i ∈ σ.cond v}

/-- Global membership means satisfying every allowed local subset. -/
@[simp, grind =]
theorem mem_family {i : ι} : i ∈ σ.family ↔ ∀ v, loc v i ∈ σ.cond v := (Iff.rfl)

/-- The image of the global family at a place is contained in the allowed subset there. -/
theorem image_family_subset_cond (v : P) : loc v '' σ.family ⊆ σ.cond v := by
  rintro _ ⟨i, hi, rfl⟩
  exact (σ.mem_family.mp hi) v

/-- Enlarging the allowed subsets can only enlarge the global family. -/
theorem family_mono (h : ∀ v, σ.cond v ⊆ τ.cond v) : σ.family ⊆ τ.family := by
  simp only [subset_def, mem_family]
  exact fun _ hi v ↦ h v (hi v)

/-- Impose both specifications at each place. -/
def inf : LocalConditions loc := ⟨fun v ↦ σ.cond v ∩ τ.cond v⟩

/-- The combined condition at a place is the intersection of its two allowed subsets. -/
@[simp]
theorem cond_inf (v : P) : (σ.inf τ).cond v = σ.cond v ∩ τ.cond v := (rfl)

/-- Simultaneous local conditions define the intersection of the two global families. -/
@[simp]
theorem family_inf : (σ.inf τ).family = σ.family ∩ τ.family := by
  ext i
  simp only [mem_family, cond_inf, mem_inter_iff, forall_and]

/-- The specification with no restrictions at any place. -/
def univ (loc : (v : P) → ι → X v) : LocalConditions loc := ⟨fun _ ↦ Set.univ⟩

/-- The unrestricted specification allows the whole local space at each place. -/
@[simp]
theorem cond_univ (v : P) : (univ loc).cond v = Set.univ := (rfl)

/-- The unrestricted specification selects every global object. -/
@[simp]
theorem family_eq_univ : (univ loc).family = Set.univ := by
  ext i
  simp

/-- Only finitely many places impose a nontrivial condition. -/
def FinitelyMany : Prop := ∀ᶠ v in cofinite, σ.cond v = Set.univ

/-- Finiteness means the places carrying proper subsets form a finite set. -/
theorem finitelyMany_iff : σ.FinitelyMany ↔ {v | σ.cond v ≠ Set.univ}.Finite :=
  Filter.eventually_cofinite

/-- A specification with finitely many conditions can be evaluated by testing a finite list
of places. The list may be empty, in which case the family is unrestricted. -/
theorem FinitelyMany.exists_finset_family_eq {σ : LocalConditions loc} (h : σ.FinitelyMany) :
    ∃ s : Finset P, σ.family = ⋂ v ∈ s, loc v ⁻¹' σ.cond v := by
  classical
  let hs := σ.finitelyMany_iff.mp h
  refine ⟨hs.toFinset, ?_⟩
  ext i
  simp only [mem_family, mem_iInter, Set.Finite.mem_toFinset, mem_ofPred_eq, mem_preimage]
  refine ⟨fun hi v _ ↦ hi v, fun hi v ↦ ?_⟩
  by_cases hv : σ.cond v = Set.univ
  · simp [hv]
  · exact hi v hv

/-- The unrestricted specification imposes no nontrivial conditions. -/
@[simp]
theorem finitelyMany_univ : (univ loc).FinitelyMany := by
  simp [FinitelyMany]

/-- Imposing both specifications is finite exactly when each specification is finite. -/
@[simp]
theorem finitelyMany_inf : (σ.inf τ).FinitelyMany ↔ σ.FinitelyMany ∧ τ.FinitelyMany := by
  simp only [FinitelyMany, cond_inf, ← top_eq_univ, inf_eq_top_iff, eventually_and]

section Measure

variable [∀ v, MeasurableSpace (X v)]

/-- The mass of the allowed subset, with respect to the specified local measure. -/
def localDensity (μ : (v : P) → Measure (X v)) (v : P) : ℝ≥0∞ := μ v (σ.cond v)

/-- Compute the local density by measuring the allowed subset. -/
@[simp]
theorem localDensity_apply (μ : (v : P) → Measure (X v)) (v : P) :
    σ.localDensity μ v = μ v (σ.cond v) := (rfl)

variable [∀ v, TopologicalSpace (X v)] (μ : (v : P) → Measure (X v))

/-- Each allowed subset is measurable and has boundary of measure zero. -/
def IsRegular : Prop := ∀ v, MeasurableSet (σ.cond v) ∧ μ v (frontier (σ.cond v)) = 0

/-- Regularity can be checked separately at each place. -/
theorem isRegular_iff : σ.IsRegular μ ↔
    ∀ v, MeasurableSet (σ.cond v) ∧ μ v (frontier (σ.cond v)) = 0 := (Iff.rfl)

/-- The unrestricted specification is regular for every choice of local measures. -/
@[simp]
theorem isRegular_univ : (univ loc).IsRegular μ := by
  simp [isRegular_iff]

/-- In particular, clopen residue conditions are regular whenever open sets are measurable. -/
theorem IsRegular.of_isClopen [∀ v, OpensMeasurableSpace (X v)]
    (h : ∀ v, IsClopen (σ.cond v)) : σ.IsRegular μ :=
  (σ.isRegular_iff μ).2 fun v ↦ ⟨(h v).2.measurableSet, by simp [(h v).frontier_eq]⟩

/-- Taking the intersection preserves regularity for the same local measures. -/
theorem IsRegular.inf {σ τ : LocalConditions loc} {μ : (v : P) → Measure (X v)}
    (hσ : σ.IsRegular μ) (hτ : τ.IsRegular μ) : (σ.inf τ).IsRegular μ := by
  rw [isRegular_iff] at hσ hτ ⊢
  simpa only [cond_inf] using fun v ↦
    ⟨(hσ v).1.inter (hτ v).1, null_frontier_inter (hσ v).2 (hτ v).2⟩

end Measure

section Topology

variable [∀ v, TopologicalSpace (X v)]

/-- The global family is locally dense off the bad loci at all but finitely many places.
The closure is taken after forming the global family. -/
def IsLargeRel (B : (v : P) → Set (X v)) : Prop :=
  ∀ᶠ v in cofinite, (B v)ᶜ ⊆ closure (loc v '' σ.family)

/-- The largeness test uses the closure of the image of the actual global family. -/
theorem isLargeRel_iff (B : (v : P) → Set (X v)) : σ.IsLargeRel B ↔
    ∀ᶠ v in cofinite, (B v)ᶜ ⊆ closure (loc v '' σ.family) := (Iff.rfl)

/-- Relaxing the local conditions preserves largeness relative to the same bad loci. -/
theorem IsLargeRel.mono {σ τ : LocalConditions loc} {B : (v : P) → Set (X v)}
    (hσ : σ.IsLargeRel B) (h : ∀ v, σ.cond v ⊆ τ.cond v) : τ.IsLargeRel B :=
  (τ.isLargeRel_iff B).2 <| ((σ.isLargeRel_iff B).1 hσ).mono fun _ hv ↦
    hv.trans (closure_mono (image_mono (σ.family_mono τ h)))

/-- At places where the specified set is closed, it must contain the good locus eventually
if the family is large. The converse need not hold: the imposed conditions can be incompatible. -/
theorem IsLargeRel.eventually_compl_subset_cond {σ : LocalConditions loc}
    {B : (v : P) → Set (X v)} (hσ : σ.IsLargeRel B)
    (hclosed : ∀ᶠ v in cofinite, IsClosed (σ.cond v)) :
    ∀ᶠ v in cofinite, (B v)ᶜ ⊆ σ.cond v :=
  (((σ.isLargeRel_iff B).1 hσ).and hclosed).mono fun v ⟨hv, hc⟩ ↦
    hv.trans (closure_minimal (σ.image_family_subset_cond v) hc)

/-- For the unrestricted family, largeness reduces to the good loci lying in the closures
of the ranges of the localization maps at almost all places. -/
@[simp]
theorem isLargeRel_univ_iff (B : (v : P) → Set (X v)) : (univ loc).IsLargeRel B ↔
    ∀ᶠ v in cofinite, (B v)ᶜ ⊆ closure (range (loc v)) := by
  simp only [isLargeRel_iff, family_eq_univ, image_univ]

end Topology

end LocalConditions
end TauCeti
