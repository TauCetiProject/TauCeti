/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Open-box topological basis and second countability of restricted products

When the reference sets `A i ⊆ R i` of a restricted product `Πʳ i, [R i, A i]` over the cofinite
filter are open, every principal stage `Πʳ i, [R i, A i]_[𝓟 S]` with `S` cofinite embeds as an open
subspace (`RestrictedProduct.isOpenEmbedding_inclusion_principal`), carrying the subspace topology
from the full product `∀ i, R i`. Two structural consequences follow:

* **Open-box basis:** Without any countability assumption on `ι`, the open cofinite boxes
  `{x : Πʳ i, [R i, A i] | ∀ i, x i ∈ C i}` with `C i` open in `R i` and `C i = A i` for all but
  finitely many `i` form a topological basis (`TauCeti.isTopologicalBasis_restrictedProduct`).
* **Second countability:** When `ι` is countable and each `R i` is second countable, every
  principal stage `Πʳ i, [R i, A i]_[𝓟 S]` embeds into `∀ i, R i` and is therefore second countable
  without openness hypotheses (`RestrictedProduct.instSecondCountableTopologyPrincipal`). When the
  reference sets `A i` are moreover open, the open stages indexed by complements `(F : Set ι)ᶜ` of
  finite sets `F : Finset ι` form a countable open cover of `Πʳ i, [R i, A i]` by second-countable
  subspaces, making `Πʳ i, [R i, A i]` second countable
  (`TauCeti.secondCountableTopology_restrictedProduct_of_isOpen`,
  `RestrictedProduct.instSecondCountableTopology`).

## Main results

* `TauCeti.isOpen_setOf_forall_mem_restrictedProduct`: a coordinate box `{x | ∀ i, x i ∈ C i}` is
  open in `Πʳ i, [R i, A i]` whenever every `C i` is open and `A i ⊆ C i` cofinitely.
* `TauCeti.isCompact_setOf_forall_mem_restrictedProduct`: `{x | ∀ i, x i ∈ C i}` is compact in
  `Πʳ i, [R i, A i]` whenever every `C i` is compact and `C i ⊆ A i` cofinitely.
* `TauCeti.isTopologicalBasis_restrictedProduct`: open cofinite boxes `{x | ∀ i, x i ∈ C i}` with
  `C i = A i` cofinitely form a topological basis when every `A i` is open.
* `RestrictedProduct.instSecondCountableTopologyPrincipal`: principal stages over a countable index
  type with second-countable factors are second countable.
* `TauCeti.secondCountableTopology_restrictedProduct_of_isOpen` and
  `RestrictedProduct.instSecondCountableTopology`: second countability of `Πʳ i, [R i, A i]` over a
  countable index type when the reference sets are open.
* `TauCeti.exists_countable_openBox_cover_subset_compact`: countable cover of a weakly locally
  compact second-countable restricted product by open cofinite boxes contained in compact sets.

The set-level openness and compactness criteria `TauCeti.isOpen_setOf_forall_mem_restrictedProduct`
and `TauCeti.isCompact_setOf_forall_mem_restrictedProduct` generalize the subgroup statements in
`TauCeti.Topology.Algebra.RestrictedProduct.Basic`, which were adapted from the FLT project
(`ImperialCollegeLondon/FLT`, `TopologicalSpace.lean`, commit
`bc2fe8ff7396469a16c2a6d51d6117f5825d93a0`, FLT PR #1088, Apache 2.0).

## References

* N. Bourbaki, *General Topology*, Chapters I and III.
* D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, Graduate Texts in
  Mathematics 186, Springer (1999), Chapter 5, §5.1.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- Any principal stage `Πʳ i, [R i, A i]_[𝓟 S]` over a countable index type with second-countable
factors is second countable. -/
instance instSecondCountableTopologyPrincipal [Countable ι] [∀ i, SecondCountableTopology (R i)]
    {S : Set ι} : SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 S]) :=
  isEmbedding_coe_of_principal.secondCountableTopology

end RestrictedProduct

namespace TauCeti

variable {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- A coordinate box `{x | ∀ i, x i ∈ C i}` in `Πʳ i, [R i, A i]` is open whenever every `C i` is
open and `A i ⊆ C i` for all but finitely many `i`. -/
theorem isOpen_setOf_forall_mem_restrictedProduct {C : ∀ i, Set (R i)}
    (hC : ∀ i, IsOpen (C i)) (hAC : ∀ᶠ i in cofinite, A i ⊆ C i) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ C i} := by
  simp_rw +instances [RestrictedProduct.topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff,
    isOpen_coinduced]
  intro T hT
  have hfin : ({i | A i ⊆ C i} ∩ T)ᶜ.Finite := mem_cofinite.mp (hAC.and (le_principal_iff.mp hT))
  convert (isOpen_set_pi hfin fun i _ ↦ hC i).preimage RestrictedProduct.continuous_coe using 1
  ext y
  simp only [mem_preimage, mem_ofPred_eq, Set.mem_pi]
  refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
  by_cases hi : i ∈ {i | A i ⊆ C i} ∩ T
  · exact hi.1 (y.2 hi.2)
  · exact h i hi

/-- A coordinate box `{x | ∀ i, x i ∈ C i}` in `Πʳ i, [R i, A i]` is compact whenever every `C i`
is compact and `C i ⊆ A i` for all but finitely many `i`. -/
theorem isCompact_setOf_forall_mem_restrictedProduct {C : ∀ i, Set (R i)}
    (hC : ∀ i, IsCompact (C i)) (hCA : ∀ᶠ i in cofinite, C i ⊆ A i) :
    IsCompact {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ C i} := by
  let S : Set ι := {i | C i ⊆ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr hCA
  have hK : IsCompact (((↑) : Πʳ i, [R i, A i]_[𝓟 S] → ∀ i, R i) ⁻¹' univ.pi C) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage'
      (isCompact_univ_pi hC) ?_
    rw [RestrictedProduct.range_coe_principal]
    exact fun x hx i hi ↦ hi (hx i trivial)
  convert hK.image (RestrictedProduct.continuous_inclusion hS) using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, mem_preimage, mem_univ_pi]
  refine ⟨fun hx ↦ ⟨⟨x, eventually_principal.2 fun i hi ↦ hi (hx i)⟩, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact hy

/-- **Topological basis of open cofinite boxes.** When every reference set `A i` is open in `R i`,
the boxes `{x : Πʳ i, [R i, A i] | ∀ i, x i ∈ C i}` with each `C i` open and `C i = A i` for all
but finitely many `i` form a topological basis of `Πʳ i, [R i, A i]`. -/
theorem isTopologicalBasis_restrictedProduct (hA : ∀ i, IsOpen (A i)) :
    TopologicalSpace.IsTopologicalBasis
      {s : Set (Πʳ i, [R i, A i]) | ∃ C : ∀ i, Set (R i),
        (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧ s = {x | ∀ i, x i ∈ C i}} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨C, hCopen, hCA, rfl⟩
    exact isOpen_setOf_forall_mem_restrictedProduct hCopen (hCA.mono fun _ h ↦ h.symm.subset)
  · intro x U hxU hU
    classical
    set S : Set ι := {i | x i ∈ A i}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
    obtain ⟨x', hxx'⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually R A hS fun _ hi ↦ hi
    rw [← hxx'] at hxU ⊢
    have hpre : IsOpen (RestrictedProduct.inclusion R A hS ⁻¹' U) :=
      hU.preimage (RestrictedProduct.continuous_inclusion hS)
    obtain ⟨t, ht_open, htU⟩ :=
      RestrictedProduct.isEmbedding_coe_of_principal.isOpen_iff.1 hpre
    have hx't : (x' : ∀ i, R i) ∈ t := by rwa [← mem_preimage, htU]
    obtain ⟨I, u, hu, hIt⟩ := isOpen_pi_iff.1 ht_open x' hx't
    -- Keep `u i` (intersected with `A i` when `i ∈ S`) on `I`, and `A i` on `S \ I`.
    let C : ∀ i, Set (R i) := fun i ↦
      if i ∈ I then (if i ∈ S then u i ∩ A i else u i) else if i ∈ S then A i else univ
    have hCopen : ∀ i, IsOpen (C i) := fun i ↦ by
      by_cases hiI : i ∈ I <;> by_cases hiS : i ∈ S <;> simp only [C, hiI, hiS, ↓reduceIte]
      exacts [(hu i hiI).1.inter (hA i), (hu i hiI).1, hA i, isOpen_univ]
    have hCA : ∀ᶠ i in cofinite, C i = A i :=
      (I.eventually_cofinite_notMem.and x.2).mono fun i ⟨hiI, hiS⟩ ↦ by
        have hiS' : i ∈ S := hiS
        simp [C, hiI, hiS']
    refine ⟨{y | ∀ i, y i ∈ C i}, ⟨C, hCopen, hCA, rfl⟩, fun i ↦ ?_, fun y hy ↦ ?_⟩
    · by_cases hiI : i ∈ I <;> by_cases hiS : i ∈ S <;> simp only [C, hiI, hiS, ↓reduceIte]
      exacts [⟨(hu i hiI).2, x'.2 hiS⟩, (hu i hiI).2, x'.2 hiS, trivial]
    · have hyS : ∀ i ∈ S, y i ∈ A i := fun i hiS ↦ by
        have hyi : y i ∈ C i := hy i
        by_cases hiI : i ∈ I <;> simp only [C, hiI, hiS, ↓reduceIte] at hyi
        exacts [hyi.2, hyi]
      obtain ⟨y', hyy'⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually R A hS hyS
      rw [← hyy', ← mem_preimage, ← htU]
      refine hIt fun i hiI ↦ ?_
      have hyi : y i ∈ C i := hy i
      rw [← hyy'] at hyi
      by_cases hiS : i ∈ S <;> simp only [C, Finset.mem_coe.mp hiI, hiS, ↓reduceIte] at hyi
      exacts [hyi.1, hyi]

/-- **Second countability of a restricted product.** If `ι` is countable, each `R i` is second
countable, and every reference set `A i` is open, then `Πʳ i, [R i, A i]` has a second-countable
topology. -/
theorem secondCountableTopology_restrictedProduct_of_isOpen [Countable ι]
    [∀ i, SecondCountableTopology (R i)] (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hF (F : Finset ι) : (cofinite : Filter ι) ≤ 𝓟 (F : Set ι)ᶜ :=
    le_principal_iff.mpr F.finite_toSet.compl_mem_cofinite
  let U : Finset ι → Set (Πʳ i, [R i, A i]) := fun F ↦
    range (RestrictedProduct.inclusion R A (hF F))
  have hU_open (F : Finset ι) : IsOpen (U F) :=
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hF F)).isOpen_range
  have (F : Finset ι) : SecondCountableTopology (U F) :=
    (RestrictedProduct.isEmbedding_inclusion_principal (R := R) (A := A)
      (hF F)).toHomeomorph.symm.isEmbedding.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover hU_open
    (eq_univ_of_forall fun x ↦ ?_)
  classical
  refine mem_iUnion.mpr ⟨x.2.toFinset, ?_⟩
  dsimp only [U]
  rw [RestrictedProduct.range_inclusion]
  intro i hi
  exact by_contra fun hx ↦ hi (x.2.mem_toFinset.mpr hx)

/-- **Countable cover by open cofinite boxes contained in compact sets.** When `ι` is countable,
each `R i` is second countable and weakly locally compact, and the open reference sets `A i` are
compact for all but finitely many `i`, `Πʳ i, [R i, A i]` is covered by countably many open
cofinite boxes, each contained in a compact subset of `Πʳ i, [R i, A i]`. -/
theorem exists_countable_openBox_cover_subset_compact [Countable ι]
    [∀ i, SecondCountableTopology (R i)] [∀ i, WeaklyLocallyCompactSpace (R i)]
    (hA : ∀ i, IsOpen (A i)) (hAcompact : ∀ᶠ i in cofinite, IsCompact (A i)) :
    ∃ T : Set (Set (Πʳ i, [R i, A i])), T.Countable ∧ ⋃₀ T = univ ∧
      (∀ s ∈ T, ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧
        s = {x | ∀ i, x i ∈ C i}) ∧
      ∀ s ∈ T, ∃ K : Set (Πʳ i, [R i, A i]), IsCompact K ∧ s ⊆ K := by
  classical
  let ℬ (i : ι) : Set (Set (R i)) :=
    {b ∈ TopologicalSpace.countableBasis (R i) | ∃ K, IsCompact K ∧ b ⊆ K}
  have (i : ι) : Countable (ℬ i) :=
    ((TopologicalSpace.countable_countableBasis (R i)).mono (sep_subset _ _)).to_subtype
  have hℬ_cov (i : ι) (y : R i) : ∃ b : ℬ i, y ∈ (b : Set (R i)) := by
    obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
    obtain ⟨b, hb, hyb, hbK⟩ := TopologicalSpace.isBasis_countableBasis (R i)
      |>.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.mpr hKy) isOpen_interior
    exact ⟨⟨b, hb, K, hK, hbK.trans interior_subset⟩, hyb⟩
  let Idx := Σ F : {F : Finset ι // ∀ i ∉ F.1, IsCompact (A i)}, ∀ i : F.1, ℬ i.1
  let C_of (p : Idx) (i : ι) : Set (R i) :=
    if hi : i ∈ p.1.1 then (p.2 ⟨i, hi⟩ : Set (R i)) else A i
  let boxOf (p : Idx) : Set (Πʳ i, [R i, A i]) := {x | ∀ i, x i ∈ C_of p i}
  refine ⟨range boxOf, countable_range boxOf, eq_univ_of_forall fun x ↦ ?_,
    fun _ ⟨p, hp⟩ ↦ hp ▸ ⟨C_of p, fun i ↦ ?_,
      p.1.1.eventually_cofinite_notMem.mono fun i hi ↦ dite_eq_right hi, rfl⟩,
    fun _ ⟨p, hp⟩ ↦ hp ▸ ?_⟩
  · let F : Finset ι := hAcompact.toFinset ∪ x.2.toFinset
    have hFc : ∀ i ∉ F, IsCompact (A i) := fun i hi ↦
      by_contra fun hnc ↦ hi (Finset.mem_union_left _ (hAcompact.mem_toFinset.mpr hnc))
    choose b hb using fun i : F ↦ hℬ_cov i.1 (x i.1)
    refine mem_sUnion.mpr ⟨boxOf ⟨⟨F, hFc⟩, b⟩, ⟨⟨⟨F, hFc⟩, b⟩, rfl⟩, fun i ↦ ?_⟩
    by_cases hi : i ∈ F <;> simp only [C_of, hi, ↓reduceDIte]
    · exact hb ⟨i, hi⟩
    · exact by_contra fun hx ↦ hi (Finset.mem_union_right _ (x.2.mem_toFinset.mpr hx))
  · by_cases hi : i ∈ p.1.1 <;> simp only [C_of, hi, ↓reduceDIte]
    · exact TopologicalSpace.isOpen_of_mem_countableBasis (p.2 ⟨i, hi⟩).2.1
    · exact hA i
  · let K (i : ι) : Set (R i) :=
      if hi : i ∈ p.1.1 then (p.2 ⟨i, hi⟩).2.2.choose else A i
    have hK_comp (i : ι) : IsCompact (K i) := by
      by_cases hi : i ∈ p.1.1 <;> simp only [K, hi, ↓reduceDIte]
      · exact (p.2 ⟨i, hi⟩).2.2.choose_spec.1
      · exact p.1.2 i hi
    refine ⟨{x | ∀ i, x i ∈ K i}, isCompact_setOf_forall_mem_restrictedProduct hK_comp
      (p.1.1.eventually_cofinite_notMem.mono fun i hi ↦ by simp [K, hi]), fun x hx i ↦ ?_⟩
    have hxi := hx i
    by_cases hi : i ∈ p.1.1 <;> simp only [C_of, K, hi, ↓reduceDIte] at hxi ⊢
    · exact (p.2 ⟨i, hi⟩).2.2.choose_spec.2 hxi
    · exact hxi

end TauCeti

namespace RestrictedProduct

/-- Typeclass instance for second countability of `Πʳ i, [R i, A i]` over a countable index type
when `[Fact (∀ i, IsOpen (A i))]` is available. -/
instance instSecondCountableTopology {ι : Type*} {R : ι → Type*} {A : ∀ i, Set (R i)}
    [Countable ι] [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    [hA : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  TauCeti.secondCountableTopology_restrictedProduct_of_isOpen hA.out

end RestrictedProduct
