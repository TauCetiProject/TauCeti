/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Projective

/-!
# Resolving subcategories of exact categories

Let `E` be an exact structure on an additive category `C`. An object property `P` is resolving
for `E` when it contains a zero object, is closed under binary direct sums and extensions, is
closed under kernels of deflations between `P`-objects, and every object of `C` admits a finite
`P`-resolution.

This file packages those hypotheses as `TauCeti.ExactStructure.IsResolving`. The full subcategory
on a resolving property inherits the exact structure induced from `E`; its inclusion preserves
and reflects conflations. These are the exact-category data used by the general resolution
theorem. Repleteness is derived from zero and binary-product closure rather than stored as a
redundant field.

The property of all objects is resolving. More substantially, the relatively projective objects
are resolving whenever every object admits a finite projective resolution. For the latter
example, kernel closure follows because a conflation with projective quotient splits, making its
kernel a retract of the projective middle term.

Finally, the resolving hypotheses control `P`-dimension along conflations with a resolving term.
The proofs use only pullbacks of deflations and the Noether conflation of a composite deflation,
never a splitting, and are what make the Euler class of a finite resolution well defined in
`TauCeti/CategoryTheory/GrothendieckGroup/Resolving.lean`.

## Main definitions

* `TauCeti.ExactStructure.IsResolving`: the resolving hypotheses for an object property.
* `TauCeti.ExactStructure.resolvingSubcategory`: the induced exact structure on the full
  subcategory.

## Main results

* `TauCeti.ExactStructure.IsResolving.prop_X₁`: closure under kernels of admissible deflations.
* `TauCeti.ExactStructure.IsResolving.isConflationExact_ι` and
  `TauCeti.ExactStructure.IsResolving.reflectsConflations_ι`: the inclusion preserves and
  reflects conflations.
* `TauCeti.ExactStructure.isResolving_top`: the full category is resolving.
* `TauCeti.ExactStructure.isResolving_isProjective`: finite projective resolutions make the
  relatively projective objects a resolving subcategory.
* `TauCeti.ExactStructure.IsResolving.exists_finiteResolution_X₁_length_le_of_prop_X₂`:
  **dimension shifting**. If `K ↪ Q ↠ X` is a conflation with `Q` resolving and `X` has
  `P`-dimension at most `n + 1`, then `K` has `P`-dimension at most `n`.
* `TauCeti.ExactStructure.IsResolving.exists_finiteResolution_X₂_length_le_of_prop_X₃` and
  `TauCeti.ExactStructure.IsResolving.exists_finiteResolution_X₁_length_le_of_prop_X₃`: extensions
  of a resolving object, and kernels of deflations onto one, do not raise `P`-dimension.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Section 7, especially Theorem II.7.6.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C) (P : ObjectProperty C)

/-- An object property is **resolving** for an exact structure when it is additive and extension
closed, is closed under kernels of deflations between its objects, and gives a finite resolution
of every ambient object.

The first two fields imply that `P` is closed under isomorphisms, so repleteness is exposed as a
derived theorem rather than duplicated in the structure. -/
class IsResolving : Prop extends P.ContainsZero, P.IsClosedUnderBinaryProducts where
  /-- Extensions of two resolving objects are resolving. -/
  isExtensionClosed : E.IsExtensionClosed P
  /-- The kernel term of a conflation is resolving when its middle and quotient terms are. -/
  prop_X₁ {S : ShortComplex C} (hS : E.Conflation S) (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.X₁
  /-- Every object admits a finite resolution by resolving objects. -/
  finiteResolution (X : C) : E.admitsFiniteResolution P X

/-- The exact structure on the full subcategory of resolving objects induced from the ambient
exact structure. Its conflations are precisely the ambient conflations whose three terms satisfy
`P`. It is by definition `TauCeti.ExactStructure.fullSubcategory`, so the Grothendieck-group
API of induced structures applies to it unchanged. -/
noncomputable abbrev resolvingSubcategory [E.IsResolving P] : ExactStructure P.FullSubcategory :=
  E.fullSubcategory P IsResolving.isExtensionClosed

/-- The inclusion of a resolving subcategory preserves conflations. -/
theorem IsResolving.isConflationExact_ι [E.IsResolving P] :
    (E.resolvingSubcategory P).IsConflationExact E P.ι where
  map_conflation hS := (E.fullSubcategory_conflation_iff IsResolving.isExtensionClosed _).mp hS

/-- The inclusion of a resolving subcategory reflects conflations. -/
theorem IsResolving.reflectsConflations_ι [E.IsResolving P] :
    (E.resolvingSubcategory P).ReflectsConflations E P.ι where
  reflects_conflation hS :=
    (E.fullSubcategory_conflation_iff IsResolving.isExtensionClosed _).mpr hS

/-- The property of all objects is resolving for every exact structure. -/
instance isResolving_top : E.IsResolving (⊤ : ObjectProperty C) where
  isExtensionClosed := ⟨fun _ _ _ => trivial⟩
  prop_X₁ _ _ _ := trivial
  finiteResolution _ := (E.admitsFiniteResolution_iff _).mpr ⟨.base trivial⟩

/-- If every object admits a finite resolution by relative projectives, then the relative
projectives form a resolving subcategory.

Extension closure follows because an extension with projective quotient splits. For kernel
closure, a conflation with projective quotient identifies its middle term with the biproduct of
its kernel and quotient; hence the kernel is a retract of the projective middle term. -/
theorem isResolving_isProjective
    (hfinite : ∀ X : C, E.admitsFiniteResolution E.isProjective X) :
    E.IsResolving E.isProjective where
  isExtensionClosed := E.isExtensionClosed_of_le_isProjective le_rfl
  prop_X₁ {S} hS h₂ h₃ := by
    let s := E.splittingOfProjective hS h₃
    have hbiprod : E.isProjective (S.X₁ ⊞ S.X₃) :=
      E.isProjective.prop_of_iso s.isoBinaryBiproduct h₂
    exact ObjectProperty.IsStableUnderRetracts.of_biprod_left E.isProjective hbiprod
  finiteResolution := hfinite

section DimensionShifting

variable {E P} [E.IsResolving P]

/-- Every object of a category with a resolving property `P` is the quotient of a conflation
`K ↪ Q ↠ X` whose middle term satisfies `P` and whose kernel again admits a finite
`P`-resolution. -/
theorem IsResolving.exists_conflation (X : C) :
    ∃ (K Q : C) (i : K ⟶ Q) (p : Q ⟶ X) (hip : i ≫ p = 0), P Q ∧
      E.Conflation (ShortComplex.mk i p hip) ∧ E.admitsFiniteResolution P K := by
  have : P.IsClosedUnderIsomorphisms := ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P
  obtain ⟨r⟩ := (E.admitsFiniteResolution_iff P).mp (IsResolving.finiteResolution X)
  obtain ⟨K, Q, i, p, hip, hQ, hc, s, -⟩ :=
    E.exists_conflation_of_exists_finiteResolution_length_le_succ (n := r.length) ⟨r, by omega⟩
  exact ⟨K, Q, i, p, hip, hQ, hc, (E.admitsFiniteResolution_iff P).mpr ⟨s⟩⟩

/-- The kernel of a deflation from an object of `P`-dimension at most `n` onto an object of `P`
has `P`-dimension at most `n`. -/
theorem IsResolving.exists_finiteResolution_X₁_length_le_of_prop_X₃ {n : ℕ}
    {S : ShortComplex C} (hS : E.Conflation S) (h₃ : P S.X₃)
    (h₂ : ∃ r : E.FiniteResolution P S.X₂, r.length ≤ n) :
    ∃ r : E.FiniteResolution P S.X₁, r.length ≤ n := by
  have : P.IsClosedUnderIsomorphisms := ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P
  cases n with
  | zero =>
      obtain ⟨r, hr⟩ := h₂
      have hX₂ : P S.X₂ := by simpa using r.prop_syzygy hr
      exact ⟨.base (IsResolving.prop_X₁ hS hX₂ h₃), by simp⟩
  | succ n =>
      obtain ⟨K, Q, i, a, hia, hQ, hc, s, hs⟩ :=
        E.exists_conflation_of_exists_finiteResolution_length_le_succ h₂
      -- The kernel `L` of the composite deflation `Q ↠ X₂ ↠ X₃` satisfies `P`, and `K ↪ L ↠ X₁`.
      obtain ⟨L, c, α, β, hc', hβ, hL, hKL, -, -⟩ := E.exists_conflation_comp' hS hc
      exact ⟨.step (IsResolving.prop_X₁ (S := ShortComplex.mk c (a ≫ S.g) hc') hL hQ h₃)
        β α hβ hKL s, by simpa using hs⟩

/-- The two halves of the dimension-shifting induction: at level `n`, an extension of an object
of `P` by an object of `P`-dimension at most `n` has `P`-dimension at most `n`, and a kernel of a
deflation from an object of `P` onto an object of `P`-dimension at most `n + 1` has
`P`-dimension at most `n`. -/
private theorem dimension_shift_aux (n : ℕ) :
    (∀ {S : ShortComplex C}, E.Conflation S → P S.X₃ →
      (∃ r : E.FiniteResolution P S.X₁, r.length ≤ n) →
      ∃ r : E.FiniteResolution P S.X₂, r.length ≤ n) ∧
    (∀ {S : ShortComplex C}, E.Conflation S → P S.X₂ →
      (∃ r : E.FiniteResolution P S.X₃, r.length ≤ n + 1) →
      ∃ r : E.FiniteResolution P S.X₁, r.length ≤ n) := by
  have : P.IsClosedUnderIsomorphisms := ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P
  -- The kernel statement at level `n` follows from the extension statement at level `n`, by
  -- pulling back the given deflation along the first step of a short resolution.
  have kernel : ∀ n : ℕ, (∀ {S : ShortComplex C}, E.Conflation S → P S.X₃ →
      (∃ r : E.FiniteResolution P S.X₁, r.length ≤ n) →
      ∃ r : E.FiniteResolution P S.X₂, r.length ≤ n) →
      ∀ {S : ShortComplex C}, E.Conflation S → P S.X₂ →
        (∃ r : E.FiniteResolution P S.X₃, r.length ≤ n + 1) →
        ∃ r : E.FiniteResolution P S.X₁, r.length ≤ n := by
    intro n ext S hS h₂ h₃
    obtain ⟨K₀, Q₀, i₀, p₀, h₀, hQ₀, hc₀, hK₀⟩ :=
      E.exists_conflation_of_exists_finiteResolution_length_le_succ h₃
    have : HasPullback S.g p₀ :=
      E.hasPullbacks_deflations.hasPullback p₀ (E.isDeflation_g hS)
    have sq : IsPullback (pullback.fst S.g p₀) (pullback.snd S.g p₀) S.g p₀ :=
      IsPullback.of_hasPullback _ _
    have hY₁ := E.conflation_baseChange hS sq
    rw [baseChange_def] at hY₁
    let T₁ := ShortComplex.mk (baseChangeι S sq) (pullback.snd S.g p₀)
      (baseChangeι_snd S sq)
    change E.Conflation T₁ at hY₁
    have hY₂ := E.conflation_baseChange hc₀ sq.flip
    rw [baseChange_def] at hY₂
    let T₂ := ShortComplex.mk (baseChangeι (ShortComplex.mk i₀ p₀ h₀) sq.flip)
      (pullback.fst S.g p₀) (baseChangeι_snd (ShortComplex.mk i₀ p₀ h₀) sq.flip)
    change E.Conflation T₂ at hY₂
    exact IsResolving.exists_finiteResolution_X₁_length_le_of_prop_X₃
      (S := T₁) hY₁ hQ₀ (ext (S := T₂) hY₂ h₂ hK₀)
  induction n with
  | zero =>
      have ext : ∀ {S : ShortComplex C}, E.Conflation S → P S.X₃ →
          (∃ r : E.FiniteResolution P S.X₁, r.length ≤ 0) →
          ∃ r : E.FiniteResolution P S.X₂, r.length ≤ 0 := by
        rintro S hS h₃ ⟨r, hr⟩
        have hX₁ : P S.X₁ := by simpa using r.prop_syzygy hr
        exact ⟨.base (IsResolving.isExtensionClosed.prop_X₂ hS hX₁ h₃), by simp⟩
      exact ⟨ext, kernel 0 ext⟩
  | succ n ih =>
      -- Cover `X₂` by an object `Q` of `P`; the kernel `L` of `Q ↠ X₂ ↠ X₃` satisfies `P`, and
      -- the kernel of `Q ↠ X₂` is a kernel of `L ↠ X₁`, of `P`-dimension at most `n`.
      have ext : ∀ {S : ShortComplex C}, E.Conflation S → P S.X₃ →
          (∃ r : E.FiniteResolution P S.X₁, r.length ≤ n + 1) →
          ∃ r : E.FiniteResolution P S.X₂, r.length ≤ n + 1 := by
        intro S hS h₃ h₁
        obtain ⟨K, Q, i, a, hia, hQ, hc, -⟩ :=
          IsResolving.exists_conflation (E := E) (P := P) S.X₂
        obtain ⟨L, c, α, β, hc', hβ, hL, hKL, -, -⟩ := E.exists_conflation_comp' hS hc
        obtain ⟨t, ht⟩ := ih.2 (S := ShortComplex.mk β α hβ) hKL
          (IsResolving.prop_X₁ (S := ShortComplex.mk c (a ≫ S.g) hc') hL hQ h₃) h₁
        exact ⟨.step hQ i a hia hc t, by simpa using ht⟩
      exact ⟨ext, kernel (n + 1) ext⟩

/-- An extension of an object of `P` by an object of `P`-dimension at most `n` has
`P`-dimension at most `n`. -/
theorem IsResolving.exists_finiteResolution_X₂_length_le_of_prop_X₃ {n : ℕ}
    {S : ShortComplex C} (hS : E.Conflation S) (h₃ : P S.X₃)
    (h₁ : ∃ r : E.FiniteResolution P S.X₁, r.length ≤ n) :
    ∃ r : E.FiniteResolution P S.X₂, r.length ≤ n :=
  (dimension_shift_aux n).1 hS h₃ h₁

/-- **Dimension shifting.** If `K ↪ Q ↠ X` is a conflation with `Q` in the resolving
subcategory and `X` has `P`-dimension at most `n + 1`, then `K` has `P`-dimension at most `n`,
whichever first step `Q ↠ X` is chosen. -/
theorem IsResolving.exists_finiteResolution_X₁_length_le_of_prop_X₂ {n : ℕ}
    {S : ShortComplex C} (hS : E.Conflation S) (h₂ : P S.X₂)
    (h₃ : ∃ r : E.FiniteResolution P S.X₃, r.length ≤ n + 1) :
    ∃ r : E.FiniteResolution P S.X₁, r.length ≤ n :=
  (dimension_shift_aux n).2 hS h₂ h₃

end DimensionShifting

end ExactStructure

end TauCeti
