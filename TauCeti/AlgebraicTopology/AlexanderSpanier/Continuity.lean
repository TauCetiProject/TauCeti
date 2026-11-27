/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Defs
public import TauCeti.AlgebraicTopology.AlexanderSpanier.Basic
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.AlgebraicTopology.AlexanderSpanier.Homotopy
import TauCeti.AlgebraicTopology.AlexanderSpanier.Relative
import TauCeti.Topology.UniformSpace.Compact

/-!
# Continuity of Alexander–Spanier cohomology for compact subsets

Let `S` be a compact subset of a uniform space `X`, for instance of a metric space. A class of the
Alexander–Spanier cohomology `H^n(X; M)` that restricts to zero on `S` already restricts to zero on
a neighbourhood of `S`
(`TauCeti.AlexanderSpanier.exists_mem_nhdsSet_cohomologyMap_subtypeVal_apply_eq_zero`), hence on
every smaller set containing `S`, such as a closed neighbourhood inside it
(`TauCeti.AlexanderSpanier.eventually_smallSets_cohomologyMap_subtypeVal_apply_eq_zero`). Applied
with a neighbourhood of `S` in place of `X`, this is the injectivity half of the tautness of compact
subsets: a class on a neighbourhood of `S` that vanishes on `S` vanishes on a smaller
neighbourhood.

Consequently, if a class restricts to zero on the intersection of a directed family of compact
closed sets, it restricts to zero on one member of the family
(`TauCeti.AlexanderSpanier.exists_cohomologyMap_subtypeVal_apply_eq_zero_of_directed`). This is how
vanishing on the intersection `⋂ₜ Nₜ` of a decreasing family of compact sets passes to some `Nₜ`,
as in the cohomological index arguments of Conley and Zehnder for maximal invariant sets of flows.

## Implementation notes

Represent the class by a function `φ` on `(n + 1)`-tuples of `X` whose coboundary `δφ` is locally
zero. Its restriction to `S` is a coboundary `δψ` up to a function `η` that is locally zero on `S`
(in degree zero, `φ` itself is locally zero on `S`). Choose a map `r` from a neighbourhood `U` of
`S` into `S` that is close to the identity relative to the neighbourhoods on which `δφ` and `η`
vanish (`IsCompact.exists_mem_nhdsSet_mapsTo_forall_exists_nhds`); it need not be continuous.
The prism operator `P` of `r` and of the inclusion `U → X` (`TauCeti.AlexanderSpanier.prism`)
satisfies, on tuples of `U`,

`φ - φ ∘ r = δ (P φ) + P (δφ)`,

and `φ ∘ r = δ (ψ ∘ r) + η ∘ r`. Both `P (δφ)` and `η ∘ r` are locally zero on `U` by the choice of
`r`, so on `U` the function `φ` is the coboundary of `P φ + ψ ∘ r` up to a locally zero function.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Section 6.6.
* C. C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Inventiones Mathematicae 73 (1983), 33–49.
-/

public section

noncomputable section

open CategoryTheory Filter Set Topology

universe w u v

namespace TauCeti.AlexanderSpanier

variable {R : Type w} [Ring R] {M : Type v} [AddCommGroup M] [Module R M] {X : Type u}

section Uniform

variable [UniformSpace X] {S : Set X}

/-- The local step of the continuity theorem. Let `φ` be a function on `(k + 1)`-tuples of `X`
with locally zero coboundary, and `η` a locally zero function on `(k + 1)`-tuples of a compact set
`S`. There are a neighbourhood `U` of `S` and a map `ρ : U → S` for which the prism of the
coboundary of `φ`, between `ρ` and the inclusion, and the pullback of `η` along `ρ` are locally zero
on `U`. -/
private lemma exists_mem_nhdsSet_isLocallyZero_prism (hS : IsCompact S) {k : ℕ}
    {φ : (Fin (k + 1) → X) → M}
    (hφ : IsLocallyZero fun y : Fin (k + 2) → X ↦
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i))
    {η : (Fin (k + 1) → S) → M} (hη : IsLocallyZero η) :
    ∃ U ∈ 𝓝ˢ S, ∃ ρ : U → S,
      IsLocallyZero (prism R M (Subtype.val ∘ ρ) Subtype.val k fun y : Fin (k + 2) → X ↦
        ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i)) ∧
      IsLocallyZero fun y : Fin (k + 1) → U ↦ η (ρ ∘ y) := by
  -- Neighbourhoods of the points of `S` on which the coboundary of `φ` and `η` vanish.
  have hW (s : S) : ∃ W ∈ 𝓝 (s : X), ∀ y : Fin (k + 2) → X, (∀ i, y i ∈ W) →
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) = 0 :=
    isLocallyZero_iff.1 hφ s
  have hT (s : S) : ∃ T ∈ 𝓝 (s : X), ∀ y : Fin (k + 1) → S, (∀ i, (y i : X) ∈ T) → η y = 0 := by
    obtain ⟨T, hT, hηT⟩ := isLocallyZero_iff.1 hη s
    obtain ⟨T', hT', hT'T⟩ := (mem_nhds_subtype S s T).1 hT
    exact ⟨T', hT', fun y hy ↦ hηT y fun i ↦ hT'T (hy i)⟩
  choose W hW hWη using hW
  choose T hT hTη using hT
  obtain ⟨U, hU, r, hrU, hr⟩ := hS.exists_mem_nhdsSet_mapsTo_forall_exists_nhds
    (G := fun s ↦ W s ∩ T s) fun s ↦ inter_mem (hW s) (hT s)
  refine ⟨U, hU, fun x ↦ ⟨r x, hrU x.property⟩, isLocallyZero_prism fun x ↦ ?_,
    isLocallyZero_iff.2 fun x ↦ ?_⟩
  · obtain ⟨s, V, hV, hVG, hrV⟩ := hr x x.property
    refine ⟨Subtype.val ⁻¹' V, continuous_subtypeVal.continuousAt.preimage_mem_nhds hV,
      fun y hy ↦ hWη s y fun i ↦ ?_⟩
    rcases hy i with ⟨z, hz, hzy⟩ | ⟨z, hz, hzy⟩ <;> rw [← hzy]
    exacts [(hrV ⟨hz, z.property⟩).1, (hVG hz).1]
  · obtain ⟨s, V, hV, -, hrV⟩ := hr x x.property
    exact ⟨Subtype.val ⁻¹' V, continuous_subtypeVal.continuousAt.preimage_mem_nhds hV,
      fun y hy ↦ hTη s _ fun i ↦ (hrV ⟨hy i, (y i).property⟩).2⟩

/-- Continuity on cochains in degree zero. Let `φ` be a function on points of `X` with locally
zero coboundary, that is, a locally constant function, which is locally zero on a compact set `S`.
Then `φ` is locally zero on a neighbourhood of `S`. -/
private lemma exists_mem_nhdsSet_isLocallyZero_zero (hS : IsCompact S) {φ : (Fin 1 → X) → M}
    (hφ : IsLocallyZero fun y : Fin 2 → X ↦
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i))
    (hφS : IsLocallyZero fun y : Fin 1 → S ↦ φ (Subtype.val ∘ y)) :
    ∃ U ∈ 𝓝ˢ S, IsLocallyZero fun y : Fin 1 → U ↦ φ (Subtype.val ∘ y) := by
  obtain ⟨U, hU, ρ, hP, hρ⟩ := exists_mem_nhdsSet_isLocallyZero_prism (R := ℤ) hS hφ hφS
  refine ⟨U, hU, ?_⟩
  -- On `U`, `φ = P (δφ) + φ ∘ ρ`.
  convert hP.add hρ using 1
  funext y
  rw [Pi.add_apply, prism_zero_apply_coboundary, Function.comp_assoc, sub_add_cancel]

/-- Continuity on cochains in positive degree. Let `φ` be a function on `(m + 2)`-tuples of `X`
with locally zero coboundary, whose restriction to a compact set `S` is the coboundary of a
function `ψ` up to a locally zero function. Then on a neighbourhood `U` of `S` the restriction of
`φ` is the coboundary of some function `χ` up to a locally zero function. -/
private lemma exists_mem_nhdsSet_isLocallyZero_succ (hS : IsCompact S) {m : ℕ}
    {φ : (Fin (m + 2) → X) → M}
    (hφ : IsLocallyZero fun y : Fin (m + 3) → X ↦
      ∑ i : Fin (m + 3), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i))
    {ψ : (Fin (m + 1) → S) → M}
    (hψ : IsLocallyZero ((fun y : Fin (m + 2) → S ↦ φ (Subtype.val ∘ y)) - fun y ↦
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • ψ (y ∘ Fin.succAbove i))) :
    ∃ U ∈ 𝓝ˢ S, ∃ χ : (Fin (m + 1) → U) → M,
      IsLocallyZero ((fun y : Fin (m + 2) → U ↦
        ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • χ (y ∘ Fin.succAbove i)) - fun y ↦
          φ (Subtype.val ∘ y)) := by
  obtain ⟨U, hU, ρ, hP, hρ⟩ := exists_mem_nhdsSet_isLocallyZero_prism (R := ℤ) hS hφ hψ
  -- On `U`, `φ` is the coboundary of `P φ + ψ ∘ ρ` up to `P (δφ)` and the pullback of `η`.
  refine ⟨U, hU, prism ℤ M (Subtype.val ∘ ρ) Subtype.val m φ + fun y ↦ ψ (ρ ∘ y), ?_⟩
  convert (hP.add hρ).smul (-1 : ℤ) using 1
  funext y
  have key := coboundary_prism_add_prism_coboundary_apply (R := ℤ) (Subtype.val ∘ ρ)
    Subtype.val φ y
  rw [eq_sub_iff_add_eq] at key
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib,
    Function.comp_assoc] at key ⊢
  rw [← key]
  abel

variable (R M) in
/-- **Continuity of Alexander–Spanier cohomology for compact subsets.** Let `S` be a compact
subset of a uniform space `X`. A class of `H^n(X; M)` that restricts to zero on `S` restricts to
zero on a neighbourhood of `S`. -/
theorem exists_mem_nhdsSet_cohomologyMap_subtypeVal_apply_eq_zero (hS : IsCompact S) {n : ℕ}
    (c : cohomology R X M n)
    (hc : (cohomologyMap R M (ContinuousMap.subtypeVal S) n).hom c = 0) :
    ∃ U ∈ 𝓝ˢ S, (cohomologyMap R M (ContinuousMap.subtypeVal U) n).hom c = 0 := by
  obtain ⟨z, rfl⟩ := (cochainComplex R X M).moduleCat_homologyπ_surjective n c
  obtain ⟨φ, hφ⟩ := cochainClass_surjective (R := R) n (((cochainComplex R X M).iCycles n).hom z)
  -- The coboundary of the cocycle `φ` is locally zero.
  have hδ : IsLocallyZero fun y : Fin (n + 2) → X ↦
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (y ∘ Fin.succAbove i) := by
    rw [← cochainClass_eq_zero_iff (R := R), ← cochainComplex_d_cochainClass, hφ,
      HomologicalComplex.moduleCat_d_iCycles_apply]
  -- Restricting the class of `z` to a subspace `A` gives the class of the restriction of `φ`.
  have hres (A : Set X) :
      (cohomologyMap R M (ContinuousMap.subtypeVal A) n).hom
          (((cochainComplex R X M).homologyπ n).hom z) =
        ((cochainComplex R A M).homologyπ n).hom
          (HomologicalComplex.cyclesMap (restriction R M A) n z) :=
    HomologicalComplex.moduleCat_homologyMap_homologyπ _ n z
  have hresi (A : Set X) : ((cochainComplex R A M).iCycles n).hom
      (HomologicalComplex.cyclesMap (restriction R M A) n z) =
        cochainClass R A M n fun y ↦ φ (Subtype.val ∘ y) := by
    rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, ← hφ, restriction_f_cochainClass]
  rw [hres] at hc
  simp_rw [hres]
  cases n with
  | zero =>
    -- In degree zero there are no coboundaries: the restriction of `φ` to `S` is locally zero.
    have h0 (A : Set X) : HomologicalComplex.cyclesMap (restriction R M A) 0 z = 0 ↔
        IsLocallyZero fun y : Fin 1 → A ↦ φ (Subtype.val ∘ y) := by
      rw [← (HomologicalComplex.moduleCat_iCycles_injective _ 0).eq_iff, hresi, map_zero,
        cochainClass_eq_zero_iff]
    have hn : ¬ (ComplexShape.up ℕ).Rel ((ComplexShape.up ℕ).prev 0) 0 := by simp
    obtain ⟨U, hU, hU0⟩ := exists_mem_nhdsSet_isLocallyZero_zero hS hδ
      ((h0 S).1 (HomologicalComplex.moduleCat_eq_zero_of_homologyπ_eq_zero _ hn _ hc))
    exact ⟨U, hU, by rw [(h0 U).2 hU0, map_zero]⟩
  | succ m =>
    -- The restriction of `φ` to `S` is a coboundary `δψ` up to a locally zero function.
    obtain ⟨y, hy⟩ := ((cochainComplex R S M).moduleCat_homologyπ_eq_zero_iff
      (m := m) (by simp) _).1 hc
    obtain ⟨ψ, rfl⟩ := cochainClass_surjective (R := R) m y
    have hψ : cochainClass R S M (m + 1) (fun y ↦ φ (Subtype.val ∘ y)) =
        cochainClass R S M (m + 1) fun y ↦
          ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • ψ (y ∘ Fin.succAbove i) := by
      rw [← hresi, ← hy, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
        cochainComplex_d_cochainClass]
    obtain ⟨U, hU, χ, hχ⟩ := exists_mem_nhdsSet_isLocallyZero_succ hS hδ
      (cochainClass_eq_cochainClass_iff.1 hψ)
    refine ⟨U, hU, ((cochainComplex R U M).moduleCat_homologyπ_eq_zero_iff (m := m) (by simp) _).2
      ⟨cochainClass R U M m χ, ?_⟩⟩
    rwa [← (HomologicalComplex.moduleCat_iCycles_injective _ _).eq_iff,
      HomologicalComplex.moduleCat_iCycles_toCycles_apply, cochainComplex_d_cochainClass, hresi,
      cochainClass_eq_cochainClass_iff]

variable (R M) in
/-- **Continuity of Alexander–Spanier cohomology for compact subsets**, for all small
neighbourhoods. Let `S` be a compact subset of a uniform space `X`. A class of `H^n(X; M)` that
restricts to zero on `S` restricts to zero on every subset of some neighbourhood of `S`, for
instance on a closed neighbourhood of `S` inside it. -/
theorem eventually_smallSets_cohomologyMap_subtypeVal_apply_eq_zero (hS : IsCompact S) {n : ℕ}
    (c : cohomology R X M n)
    (hc : (cohomologyMap R M (ContinuousMap.subtypeVal S) n).hom c = 0) :
    ∀ᶠ N in (𝓝ˢ S).smallSets, (cohomologyMap R M (ContinuousMap.subtypeVal N) n).hom c = 0 :=
  (eventually_smallSets' fun _ _ hNU ↦ cohomologyMap_subtypeVal_apply_eq_zero_of_subset R M hNU).2
    (exists_mem_nhdsSet_cohomologyMap_subtypeVal_apply_eq_zero R M hS c hc)

variable (R M) in
/-- **Continuity along a decreasing family of compact sets.** Let `K i` be a directed family of
compact closed subsets of a uniform space `X`, decreasing in the sense that any two members contain
a third. A class of `H^n(X; M)` that restricts to zero on the intersection `⋂ i, K i` restricts to
zero on some `K i`. -/
theorem exists_cohomologyMap_subtypeVal_apply_eq_zero_of_directed {ι : Type*} [Nonempty ι]
    {K : ι → Set X} (hK : Directed (· ⊇ ·) K) (hKc : ∀ i, IsCompact (K i))
    (hKcl : ∀ i, IsClosed (K i)) {n : ℕ} (c : cohomology R X M n)
    (hc : (cohomologyMap R M (ContinuousMap.subtypeVal (⋂ i, K i)) n).hom c = 0) :
    ∃ i, (cohomologyMap R M (ContinuousMap.subtypeVal (K i)) n).hom c = 0 := by
  obtain ⟨U, hU, hcU⟩ := exists_mem_nhdsSet_cohomologyMap_subtypeVal_apply_eq_zero R M
    ((hKc (Classical.arbitrary ι)).of_isClosed_subset (isClosed_iInter hKcl)
      (iInter_subset _ _)) c hc
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact' hK hKc hKcl hU
  exact ⟨i, cohomologyMap_subtypeVal_apply_eq_zero_of_subset R M hi hcU⟩

end Uniform

end TauCeti.AlexanderSpanier
