/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Translate
public import TauCeti.CategoryTheory.AlmostSplit.Sequence
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.LeftAlmostSplit
import TauCeti.CategoryTheory.AlmostSplit.Minimal
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Existence of almost-split sequences over a finite-dimensional algebra

Let `A` be a finite-dimensional algebra over a field `k`. This file proves the existence half of
the Auslander–Reiten theorem: every finitely generated indecomposable non-projective `A`-module
`M` ends an almost-split sequence

`0 → τ M → E → M → 0`,

whose left-hand end is the Auslander–Reiten translate `τ M = ModuleCat.arTranslate k M` and whose
middle term is finitely generated (`ModuleCat.exists_isAlmostSplit_arTranslate`). Dually, every
finitely generated indecomposable non-injective module starts an almost-split sequence with
finitely generated middle term and right-hand end
(`ModuleCat.exists_isAlmostSplit_of_not_injective`).

Both lifting properties hold in the category of *all* `A`-modules, not only the finitely
generated ones, and the field is arbitrary. A finitely generated module therefore ends an
almost-split sequence exactly when it is indecomposable and non-projective, and starts one exactly
when it is indecomposable and non-injective.

By `CategoryTheory.ShortComplex.IsAlmostSplit.nonempty_iso`, the sequence ending at `M` is unique
up to isomorphism among the almost-split sequences ending at `M` whose left-hand end has a local
endomorphism ring, for instance a finitely generated one.

The sequence is obtained from a minimal projective presentation `P₁ → P₀ → M → 0`: the
Auslander–Reiten translate of the presentation starts a short exact sequence ending at
`P₀ ⧸ im(P₁)` whose first map is left almost split
(`LinearMap.exists_isLeftAlmostSplit_translate`). Since `M` has a local endomorphism ring, a
non-split sequence with left almost-split first map is almost split
(`CategoryTheory.ShortComplex.ShortExact.isAlmostSplit_iff_isLeftAlmostSplit`).

## References

* M. Auslander, I. Reiten, *Representation theory of Artin algebras III: almost split
  sequences*, Comm. Algebra 3 (1975), 239–294.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti
open scoped ModuleCat.Algebra

universe u v w

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **The Auslander–Reiten theorem, existence.** Over a finite-dimensional algebra, a finitely
generated indecomposable non-projective module `M` ends an almost-split sequence
`0 → τ M → E → M → 0` of `A`-modules whose left-hand end is the translate `τ M` and whose middle
term is finitely generated. -/
theorem exists_isAlmostSplit_arTranslate (M : ModuleCat.{max u v w} A) [Module.Finite A M]
    (hiM : Indecomposable M) (hpM : ¬ Projective M) :
    ∃ (E : ModuleCat.{max u v w} A) (i : arTranslate k M ⟶ E) (p : E ⟶ M) (h : i ≫ p = 0),
      Module.Finite A E ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- Compute the translate from a minimal presentation `P`.
  obtain ⟨P, hP⟩ := FiniteProjectivePresentation.exists_isMinimal (M := M)
  obtain ⟨e⟩ := nonempty_iso_arTranslate k M P hP
  have : IsLocalRing (End (ModuleCat.of A (AuslanderReitenTranslate k P.p))) :=
    isLocalRing_end_of_indecomposable (R := k)
      (((indecomposable_arTranslate_iff k M hiM).mpr hpM).of_iso e)
  have hinj : ¬ Injective (ModuleCat.of A (AuslanderReitenTranslate k P.p)) := fun h ↦
    hpM ((injective_arTranslate_iff k M).mp (Injective.of_iso e.symm h))
  obtain ⟨E, i, p, h, hS, hE, hi⟩ := P.p.exists_isLeftAlmostSplit_translate (k := k) hinj
  -- Replace the ends by `τ M` and by `M ≅ P₀ ⧸ im(P₁)`.
  let c : ModuleCat.of A (P.P₀ ⧸ LinearMap.range P.p) ≅ M :=
    (P.exact.linearEquivOfSurjective P.surjective).toModuleIso
  have hS' : (ShortComplex.mk (e.hom ≫ i) (p ≫ c.hom) (by simp [reassoc_of% h])).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk i p h)
      (ShortComplex.isoMk e.symm (Iso.refl _) c) hS
  have : IsLocalRing (End M) := isLocalRing_end_of_indecomposable (R := k) hiM
  exact ⟨E, e.hom ≫ i, p ≫ c.hom, _, hE,
    hS'.isAlmostSplit_iff_isLeftAlmostSplit.mpr (hi.iso_comp e)⟩

include k in
/-- Over a finite-dimensional algebra, a finitely generated module ends an almost-split sequence
of `A`-modules exactly when it is indecomposable and non-projective. -/
theorem exists_isAlmostSplit_X₃_eq_iff (M : ModuleCat.{max u v w} A) [Module.Finite A M] :
    (∃ S : ShortComplex (ModuleCat.{max u v w} A), S.X₃ = M ∧ S.IsAlmostSplit) ↔
      Indecomposable M ∧ ¬ Projective M := by
  refine ⟨?_, fun ⟨hiM, hpM⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isRightAlmostSplit_g.indecomposable, hS.not_projective_X₃⟩
  · obtain ⟨E, i, p, h, -, hS⟩ := exists_isAlmostSplit_arTranslate k M hiM hpM
    exact ⟨_, rfl, hS⟩

include k in
/-- **The Auslander–Reiten theorem, existence on the left.** Over a finite-dimensional algebra, a
finitely generated indecomposable non-injective module `N` starts an almost-split sequence
`0 → N → E → M → 0` of `A`-modules with `E` and `M` finitely generated. -/
theorem exists_isAlmostSplit_of_not_injective (N : ModuleCat.{max u v w} A) [Module.Finite A N]
    (hiN : Indecomposable N) (hinj : ¬ Injective N) :
    ∃ (E M : ModuleCat.{max u v w} A) (i : N ⟶ E) (p : E ⟶ M) (h : i ≫ p = 0),
      Module.Finite A E ∧ Module.Finite A M ∧ (ShortComplex.mk i p h).IsAlmostSplit := by
  obtain ⟨M, _, hiM, hpM, ⟨e⟩⟩ := exists_nonempty_iso_arTranslate k N hiN hinj
  obtain ⟨E, i, p, h, hE, hS⟩ := exists_isAlmostSplit_arTranslate k M hiM hpM
  exact ⟨E, M, e.inv ≫ i, p, by simp [h], hE, inferInstance,
    ShortComplex.isAlmostSplit_of_iso (S₁ := ShortComplex.mk i p h)
      (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)) hS⟩

include k in
/-- Over a finite-dimensional algebra, a finitely generated module starts an almost-split
sequence of `A`-modules exactly when it is indecomposable and non-injective. -/
theorem exists_isAlmostSplit_X₁_eq_iff (N : ModuleCat.{max u v w} A) [Module.Finite A N] :
    (∃ S : ShortComplex (ModuleCat.{max u v w} A), S.X₁ = N ∧ S.IsAlmostSplit) ↔
      Indecomposable N ∧ ¬ Injective N := by
  refine ⟨?_, fun ⟨hiN, hinj⟩ ↦ ?_⟩
  · rintro ⟨S, rfl, hS⟩
    exact ⟨hS.isLeftAlmostSplit_f.indecomposable, hS.not_injective_X₁⟩
  · obtain ⟨E, M, i, p, h, -, -, hS⟩ := exists_isAlmostSplit_of_not_injective k N hiN hinj
    exact ⟨_, rfl, hS⟩

end ModuleCat
