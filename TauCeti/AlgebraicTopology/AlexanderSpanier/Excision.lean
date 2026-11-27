/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.AlexanderSpanier.Relative

/-!
# Excision in Alexander–Spanier cohomology

Let `A` and `B` be subsets of a topological space `X`. The inclusion `B → X` is a map of pairs
`(B, B ∩ A) → (X, A)`, so it restricts relative Alexander–Spanier cochains of `(X, A)` to relative
cochains of `(B, B ∩ A)`. This is the **excision map**
`C^*(X, A; M) ⟶ C^*(B, B ∩ A; M)` (`TauCeti.AlexanderSpanier.excisionMap`); in this file the
subset `B ∩ A` of `B` is written `B ↓∩ A`.

The excision map is an isomorphism of cochain complexes when `A` is closed and the interiors of `A`
and `B` cover `X` (`TauCeti.AlexanderSpanier.isIso_excisionMap`), so it induces isomorphisms
`H^n(X, A; M) ≅ H^n(B, B ∩ A; M)` of relative Alexander–Spanier cohomology
(`TauCeti.AlexanderSpanier.excisionIso`). The two halves hold separately under weaker hypotheses.

* It is injective in every degree as soon as `interior A ∪ interior B = X`
  (`TauCeti.AlexanderSpanier.excisionMap_f_injective`). A function `φ` on `X^{n+1}` whose
  restrictions to `A^{n+1}` and to `B^{n+1}` are locally zero is locally zero, since every point of
  `X` has `A` or `B` as a neighbourhood and being locally zero is a local property
  (`TauCeti.AlexanderSpanier.isLocallyZero_of_forall_nhds`).
* It is surjective in every degree as soon as `B ∩ A` is closed in `B`
  (`TauCeti.AlexanderSpanier.excisionMap_f_surjective`). If `ψ` is a function on `B^{n+1}` whose
  restriction to `(B ∩ A)^{n+1}` is locally zero, then the function on `X^{n+1}` equal to `ψ` on the
  tuples of points of `B` that are not all in `A`, and to `0` elsewhere, vanishes on `A^{n+1}` and
  differs from `ψ` on `B^{n+1}` only on `(B ∩ A)^{n+1}`. Near a point of `B ∩ A` that difference is
  zero on small tuples because `ψ` is locally zero there, and a point of `B` outside `A` has a
  neighbourhood in `B` that misses `B ∩ A`.

Unlike singular cochains, Alexander–Spanier cochains need no subdivision here: the isomorphism
holds already for the cochain complexes.

For a cover `X = A ∪ B` by two closed sets the interiors need not cover `X`. If `N` is a closed
neighbourhood of `A`, however, then `X = interior N ∪ interior B`, since `X \ A` is an open subset
of `B`, so the theorem applies to the pair `(X, N)`. Excision for closed covers of compact
Hausdorff spaces follows from this case by tautness, letting `N` shrink to `A`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6, Sections 6.4–6.6.
-/

public section

noncomputable section

open CategoryTheory Topology
open scoped Set.Notation

universe w u v

namespace TauCeti.AlexanderSpanier

variable (R : Type w) [Ring R] {X : Type u} [TopologicalSpace X] (M : Type v) [AddCommGroup M]
  [Module R M] (A B : Set X)

/-- The **excision map** `C^*(X, A; M) ⟶ C^*(B, B ∩ A; M)`: the restriction of relative
Alexander–Spanier cochains along the map of pairs `(B, B ∩ A) → (X, A)` given by the inclusion of
`B`. -/
abbrev excisionMap : relativeCochainComplex R M A ⟶ relativeCochainComplex R M (B ↓∩ A) :=
  relativeCochainComplexMap R M A (B ↓∩ A) (ContinuousMap.subtypeVal B) fun _ h ↦ h

variable {R M A B}

/-- A relative cochain of `(X, A)` restricted to `(B, B ∩ A)` by the excision map, viewed as an
absolute cochain of `B`, is the restriction to `B` of the underlying absolute cochain of `X`. -/
lemma relativeCochainComplexι_f_excisionMap_f_apply (n : ℕ)
    (c : (relativeCochainComplex R M A).X n) :
    ((relativeCochainComplexι R M (B ↓∩ A)).f n).hom (((excisionMap R M A B).f n).hom c) =
      ((restriction R M B).f n).hom (((relativeCochainComplexι R M A).f n).hom c) :=
  relativeCochainComplexι_f_relativeCochainComplexMap_f_apply R M A _ _ _ n c

/-- The excision map is **injective** in every degree when the interiors of `A` and `B` cover
`X`: a relative cochain of `(X, A)` whose restriction to `B` is locally zero on `B` is itself
locally zero. -/
theorem excisionMap_f_injective (hAB : interior A ∪ interior B = Set.univ) (n : ℕ) :
    Function.Injective ((excisionMap R M A B).f n).hom := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨φ, hφ⟩ := cochainClass_surjective n (((relativeCochainComplexι R M A).f n).hom c)
  have hφA : IsLocallyZero fun y : Fin (n + 1) → A ↦ φ (Subtype.val ∘ y) :=
    mem_range_relativeCochainComplexι_f_iff.1 (hφ ▸ LinearMap.mem_range_self _ c)
  have hφB : IsLocallyZero fun y : Fin (n + 1) → B ↦ φ (Subtype.val ∘ y) := by
    have := congrArg ((relativeCochainComplexι R M (B ↓∩ A)).f n).hom hc
    rwa [relativeCochainComplexι_f_excisionMap_f_apply, ← hφ, restriction_f_cochainClass,
      map_zero, cochainClass_eq_zero_iff] at this
  have hφX : IsLocallyZero φ := isLocallyZero_of_forall_nhds fun x ↦ by
    have hx : x ∈ interior A ∪ interior B := hAB ▸ Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨A, mem_interior_iff_mem_nhds.1 hx, hφA⟩
    · exact ⟨B, mem_interior_iff_mem_nhds.1 hx, hφB⟩
  refine relativeCochainComplexι_f_injective R M A n ?_
  rwa [map_zero, ← hφ, cochainClass_eq_zero_iff]

/-- The excision map is **surjective** in every degree when `B ∩ A` is closed in `B`: every
relative cochain of `(B, B ∩ A)` is the restriction of a cochain of `X` that vanishes on
`A^{n+1}`. -/
theorem excisionMap_f_surjective (hA : IsClosed (B ↓∩ A)) (n : ℕ) :
    Function.Surjective ((excisionMap R M A B).f n).hom := by
  classical
  intro c'
  obtain ⟨ψ, hψ⟩ :=
    cochainClass_surjective n (((relativeCochainComplexι R M (B ↓∩ A)).f n).hom c')
  have hψA : IsLocallyZero fun y : Fin (n + 1) → (B ↓∩ A) ↦ ψ (Subtype.val ∘ y) :=
    mem_range_relativeCochainComplexι_f_iff.1 (hψ ▸ LinearMap.mem_range_self _ c')
  -- The extension of `ψ` by zero, made to vanish on the tuples of points of `A`.
  let φ : (Fin (n + 1) → X) → M := fun y ↦
    if h : (∀ i, y i ∈ B) ∧ ¬ ∀ i, y i ∈ A then ψ fun i ↦ ⟨y i, h.1 i⟩ else 0
  have hφA : (fun y : Fin (n + 1) → A ↦ φ (Subtype.val ∘ y)) = 0 :=
    funext fun y ↦ by simp [φ]
  obtain ⟨c, hc⟩ := (mem_range_relativeCochainComplexι_f_iff (R := R)).2
    (hφA ▸ isLocallyZero_zero)
  refine ⟨c, relativeCochainComplexι_f_injective R M _ n ?_⟩
  rw [relativeCochainComplexι_f_excisionMap_f_apply, hc, ← hψ, restriction_f_cochainClass,
    cochainClass_eq_cochainClass_iff, isLocallyZero_iff]
  intro b
  by_cases hb : (b : X) ∈ A
  · obtain ⟨V, hV, hψV⟩ := isLocallyZero_iff.1 hψA ⟨b, hb⟩
    obtain ⟨U, hU, hUV⟩ := (mem_nhds_subtype _ _ V).1 hV
    refine ⟨U, hU, fun y hy ↦ ?_⟩
    by_cases hyA : ∀ i, (y i : X) ∈ A
    · have hψy : ψ y = 0 := hψV (fun i ↦ ⟨y i, hyA i⟩) fun i ↦ hUV (hy i)
      simp [φ, hyA, hψy]
    · simp [φ, not_forall.1 hyA]
  · refine ⟨_, hA.isOpen_compl.mem_nhds hb, fun y hy ↦ ?_⟩
    have hyA : ∃ i, (y i : X) ∉ A := ⟨0, hy 0⟩
    simp [φ, hyA]

/-- **Excision for Alexander–Spanier cochains.** If `A` is closed and the interiors of `A` and `B`
cover `X`, restriction along the inclusion `(B, B ∩ A) → (X, A)` is an isomorphism of relative
cochain complexes `C^*(X, A; M) ≅ C^*(B, B ∩ A; M)`. -/
theorem isIso_excisionMap (hA : IsClosed A) (hAB : interior A ∪ interior B = Set.univ) :
    IsIso (excisionMap R M A B) :=
  have (n : ℕ) : IsIso ((excisionMap R M A B).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨excisionMap_f_injective hAB n,
        excisionMap_f_surjective (hA.preimage continuous_subtypeVal) n⟩
  HomologicalComplex.Hom.isIso_of_components _

variable (R M) in
/-- **Excision in Alexander–Spanier cohomology.** If `A` is closed and the interiors of `A` and
`B` cover `X`, restriction along the inclusion `(B, B ∩ A) → (X, A)` is an isomorphism
`H^n(X, A; M) ≅ H^n(B, B ∩ A; M)`. -/
def excisionIso (hA : IsClosed A) (hAB : interior A ∪ interior B = Set.univ) (n : ℕ) :
    relativeCohomology R M A n ≅ relativeCohomology R M (B ↓∩ A) n :=
  have := isIso_excisionMap (R := R) (M := M) hA hAB
  asIso (HomologicalComplex.homologyMap (excisionMap R M A B) n)

variable (R M) in
/-- The excision isomorphism is the map induced in relative cohomology by the excision map. -/
@[simp]
lemma excisionIso_hom (hA : IsClosed A) (hAB : interior A ∪ interior B = Set.univ) (n : ℕ) :
    (excisionIso R M hA hAB n).hom = HomologicalComplex.homologyMap (excisionMap R M A B) n :=
  (rfl)

end TauCeti.AlexanderSpanier
