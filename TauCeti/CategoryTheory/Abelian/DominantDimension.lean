/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import TauCeti.CategoryTheory.Abelian.Injective.MinimalCoresolution
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# Dominant dimension

An object `X` of an abelian category has a *projective-injective coresolution with `n` terms* when
there is an exact sequence `0 → X → I⁰ → ⋯ → Iⁿ⁻¹`, exact at `X` and at `I⁰, …, Iⁿ⁻²`, whose terms
are projective and injective (`CategoryTheory.HasProjectiveInjectiveCoresolution`). The **dominant
dimension** `dom.dim X ∈ ℕ∞` is the supremum of such `n` (`CategoryTheory.dominantDimension`). For
`n = 0` the condition always holds, so `dom.dim X ≥ 0`, and `dom.dim X = ⊤` when `X` is itself
projective and injective, through `0 → X → X → 0 → 0 → ⋯`.

For the module category of an Artin algebra this is the dominant dimension of [ARS, §VI.5]: it is
read off the minimal injective coresolution, whose first `n` terms are projective exactly when
`n ≤ dom.dim X`
(`CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.natCast_le_dominantDimension_iff`).
For modules over other rings it is a different number from the established one, which asks the
terms of the minimal injective coresolution to be flat rather than projective (Hoshino; Xi calls
this the *flat-dominant dimension*). The flat version is not defined here.

Since projective-injective coresolutions are closed under extensions and retracts
(`CategoryTheory.HasCoresolution.of_shortExact`, `CategoryTheory.HasCoresolution.of_retract`), the
dominant dimension of a retract is at least that of the whole object, and that of a biproduct is
the minimum, in every abelian category.

## Main definitions

* `CategoryTheory.HasProjectiveInjectiveCoresolution X n`: `X` has a projective-injective
  coresolution with `n` terms.
* `CategoryTheory.dominantDimension X`: the dominant dimension of `X`, in `ℕ∞`.

## Main results

* `CategoryTheory.natCast_le_dominantDimension_iff`: `n ≤ dom.dim X` exactly when `X` has a
  projective-injective coresolution with `n` terms.
* `CategoryTheory.two_le_dominantDimension_iff`: `dom.dim X ≥ 2` exactly when `X` has an injective
  copresentation `0 → X → I⁰ → I¹` by projective-injective objects.
* `CategoryTheory.dominantDimension_eq_top`: a projective and injective object has dominant
  dimension `⊤`.
* `CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.natCast_le_dominantDimension_iff`:
  `n ≤ dom.dim X` exactly when the first `n` terms of a minimal injective coresolution are
  projective.
* `CategoryTheory.Retract.dominantDimension_le`: the dominant dimension of a retract is at least
  that of the whole object.
* `CategoryTheory.dominantDimension_biprod`: the dominant dimension of `X ⊞ Y` is the minimum of
  those of `X` and `Y`; `CategoryTheory.iInf_dominantDimension_le_dominantDimension_biproduct` for
  finite biproducts.
* `CategoryTheory.Equivalence.dominantDimension_functor_obj`: equivalences preserve the dominant
  dimension.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5, p. 211.
* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280.
* C. Xi, *Frobenius bimodules and flat-dominant dimensions*, arXiv:1903.07921v1, §1.
-/

public section

universe v v' u u' w

namespace CategoryTheory

open Limits TauCeti ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- `X` has a **projective-injective coresolution with `n` terms**: an exact sequence
`0 → X → I⁰ → ⋯ → Iⁿ⁻¹`, exact at `X` and at `I⁰, …, Iⁿ⁻²`, with every `Iⁱ` projective and
injective. For `n = 0` this always holds. -/
def HasProjectiveInjectiveCoresolution (X : C) (n : ℕ) : Prop :=
  HasCoresolution (fun Y ↦ Projective Y ∧ Injective Y) X n

theorem hasProjectiveInjectiveCoresolution_iff_hasCoresolution {X : C} {n : ℕ} :
    HasProjectiveInjectiveCoresolution X n ↔
      HasCoresolution (fun Y ↦ Projective Y ∧ Injective Y) X n :=
  Iff.rfl

theorem hasProjectiveInjectiveCoresolution_iff {X : C} {n : ℕ} :
    HasProjectiveInjectiveCoresolution X n ↔ ∃ S : ComposableArrows C (n + 1),
      S.IsCoresolution ∧ Nonempty (S.obj' 1 ≅ X) ∧
        ∀ (i : ℕ) (hi : i < n), Projective (S.obj' (i + 2)) ∧ Injective (S.obj' (i + 2)) :=
  hasCoresolution_iff

/-- The **dominant dimension** `dom.dim X` of an object of an abelian category: the supremum in
`ℕ∞` of the `n` for which `X` has a projective-injective coresolution with `n` terms.

For a module over an Artin algebra this is the dominant dimension of [ARS, §VI.5]. Over other
rings the established notion asks the terms of the minimal injective coresolution to be flat
(Hoshino), which can give a different number: for `ℤ` this one is `0` while the flat one is `1`. -/
noncomputable def dominantDimension (X : C) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : HasProjectiveInjectiveCoresolution X n), (n : ℕ∞)

@[simp]
theorem hasProjectiveInjectiveCoresolution_zero (X : C) : HasProjectiveInjectiveCoresolution X 0 :=
  hasCoresolution_zero X

theorem HasProjectiveInjectiveCoresolution.of_le {X : C} {m n : ℕ}
    (h : HasProjectiveInjectiveCoresolution X n) (hmn : m ≤ n) :
    HasProjectiveInjectiveCoresolution X m :=
  HasCoresolution.of_le h hmn

theorem HasProjectiveInjectiveCoresolution.of_iso {X Y : C} {n : ℕ}
    (h : HasProjectiveInjectiveCoresolution X n) (e : X ≅ Y) :
    HasProjectiveInjectiveCoresolution Y n :=
  HasCoresolution.of_iso h e

/-- Projective-injective objects are closed under binary biproducts. -/
private theorem projective_and_injective_biprod (A B : C) (hA : Projective A ∧ Injective A)
    (hB : Projective B ∧ Injective B) : Projective (A ⊞ B) ∧ Injective (A ⊞ B) := by
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  exact ⟨inferInstance, inferInstance⟩

/-- Projective-injective coresolutions of a retract: if `Y` has one with `n` terms, so does every
retract of `Y`. -/
theorem HasProjectiveInjectiveCoresolution.of_retract {X Y : C} {n : ℕ} (r : Retract X Y)
    (h : HasProjectiveInjectiveCoresolution Y n) : HasProjectiveInjectiveCoresolution X n :=
  HasCoresolution.of_retract (fun _ h ↦ h.2) projective_and_injective_biprod r h

/-- **`n ≤ dom.dim X` exactly when `X` has a projective-injective coresolution with `n` terms.**
Coresolutions can be truncated, so the set of such `n` is downward closed. -/
theorem natCast_le_dominantDimension_iff {X : C} {n : ℕ} :
    (n : ℕ∞) ≤ dominantDimension X ↔ HasProjectiveInjectiveCoresolution X n := by
  refine ⟨fun hn ↦ ?_, fun h ↦ le_iSup₂ (f := fun (m : ℕ) _ ↦ (m : ℕ∞)) n h⟩
  by_contra h
  have h0 : n ≠ 0 := by
    rintro rfl
    exact h (hasProjectiveInjectiveCoresolution_zero X)
  have : dominantDimension X ≤ ((n - 1 : ℕ) : ℕ∞) := by
    refine iSup₂_le fun m hm ↦ ?_
    have : m < n := by
      by_contra hmn
      exact h (hm.of_le (by omega))
    exact_mod_cast (by omega : m ≤ n - 1)
  have := hn.trans this
  norm_cast at this
  omega

theorem dominantDimension_eq_top_iff {X : C} :
    dominantDimension X = ⊤ ↔ ∀ n : ℕ, HasProjectiveInjectiveCoresolution X n := by
  simp only [← natCast_le_dominantDimension_iff]
  exact ENat.eq_top_iff_forall_ge

/-- **The case `dom.dim X ≥ 2`.** It holds exactly when `X` has an injective copresentation
`0 → X → I⁰ → I¹` by projective-injective objects. -/
theorem two_le_dominantDimension_iff {X : C} :
    2 ≤ dominantDimension X ↔
      ∃ (I₀ I₁ : C) (f : X ⟶ I₀) (g : I₀ ⟶ I₁) (w : f ≫ g = 0), Mono f ∧
        (ShortComplex.mk f g w).Exact ∧ (Projective I₀ ∧ Injective I₀) ∧
          (Projective I₁ ∧ Injective I₁) := by
  rw [← Nat.cast_ofNat, natCast_le_dominantDimension_iff, HasProjectiveInjectiveCoresolution,
    hasCoresolution_two_iff]

/-- A zero object has projective-injective coresolutions of every length. -/
theorem Limits.IsZero.hasProjectiveInjectiveCoresolution {Z : C} (hZ : IsZero Z) (n : ℕ) :
    HasProjectiveInjectiveCoresolution Z n := by
  induction n generalizing Z with
  | zero => exact hasProjectiveInjectiveCoresolution_zero Z
  | succ n ih =>
    exact hasCoresolution_succ_iff.2 ⟨Z, 𝟙 Z, inferInstance, ⟨hZ.projective, hZ.injective⟩,
      ih (isZero_cokernel_of_epi _)⟩

/-- **A projective and injective object has dominant dimension `⊤`**, through the coresolution
`0 → X → X → 0 → 0 → ⋯`. In particular a left self-injective ring has dominant dimension `⊤`. -/
theorem dominantDimension_eq_top (X : C) [Projective X] [Injective X] :
    dominantDimension X = ⊤ := by
  refine dominantDimension_eq_top_iff.2 fun n ↦ ?_
  cases n with
  | zero => exact hasProjectiveInjectiveCoresolution_zero X
  | succ n =>
    exact hasCoresolution_succ_iff.2 ⟨X, 𝟙 X, inferInstance, ⟨inferInstance, inferInstance⟩,
      (isZero_cokernel_of_epi (𝟙 X)).hasProjectiveInjectiveCoresolution n⟩

/-- A zero object has dominant dimension `⊤`. -/
theorem Limits.IsZero.dominantDimension_eq_top {Z : C} (hZ : IsZero Z) :
    dominantDimension Z = ⊤ :=
  dominantDimension_eq_top_iff.2 hZ.hasProjectiveInjectiveCoresolution

theorem dominantDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    dominantDimension X = dominantDimension Y := by
  refine le_antisymm (iSup₂_le fun n hn ↦ natCast_le_dominantDimension_iff.2 (hn.of_iso e))
    (iSup₂_le fun n hn ↦ natCast_le_dominantDimension_iff.2 (hn.of_iso e.symm))

namespace ComposableArrows.IsMinimalInjectiveCoresolution

/-- **The dominant dimension from the minimal injective coresolution.** If `E` is a minimal
injective coresolution of `X` with `n` terms, then `n ≤ dom.dim X` exactly when the terms of `E`
are projective. The minimal coresolution is a termwise retract of every injective coresolution
(`CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_retract_obj'`), and
retracts of projective objects are projective. -/
theorem natCast_le_dominantDimension_iff {n : ℕ} {E : ComposableArrows C (n + 1)}
    (hE : E.IsMinimalInjectiveCoresolution) {X : C} (e : E.obj' 1 ≅ X) :
    (n : ℕ∞) ≤ dominantDimension X ↔ ∀ (i : ℕ) (hi : i < n), Projective (E.obj' (i + 2)) := by
  rw [CategoryTheory.natCast_le_dominantDimension_iff]
  constructor
  · rintro h i hi
    obtain ⟨S, hS, ⟨e'⟩, hP⟩ := hasProjectiveInjectiveCoresolution_iff.1 h
    have hS' : S.IsInjectiveCoresolution := ⟨hS, fun i hi ↦ (hP i hi).2⟩
    obtain ⟨r⟩ := hE.nonempty_retract_obj' hS' (Retract.ofIso (e ≪≫ e'.symm)) i hi
    have := (hP i hi).1
    exact r.projective
  · intro h
    exact hasProjectiveInjectiveCoresolution_iff.2
      ⟨E, hE.toIsCoresolution, ⟨e⟩, fun i hi ↦ ⟨h i hi, hE.injective i hi⟩⟩

end ComposableArrows.IsMinimalInjectiveCoresolution

/-- **Retracts.** If `X` is a retract of `Y`, then `dom.dim Y ≤ dom.dim X`: projective-injective
coresolutions pass to retracts (`CategoryTheory.HasProjectiveInjectiveCoresolution.of_retract`). -/
theorem Retract.dominantDimension_le {X Y : C} (r : Retract X Y) :
    dominantDimension Y ≤ dominantDimension X :=
  iSup₂_le fun _ hn ↦ natCast_le_dominantDimension_iff.2 (hn.of_retract r)

/-- **Biproducts.** The dominant dimension of `X ⊞ Y` is at least the minimum of those of `X` and
`Y`. -/
theorem min_dominantDimension_le_dominantDimension_biprod (X Y : C) :
    min (dominantDimension X) (dominantDimension Y) ≤ dominantDimension (X ⊞ Y) := by
  refine ENat.forall_natCast_le_iff_le.1 fun n hn ↦ ?_
  rw [le_min_iff, natCast_le_dominantDimension_iff, natCast_le_dominantDimension_iff] at hn
  exact natCast_le_dominantDimension_iff.2
    (HasCoresolution.biprod projective_and_injective_biprod hn.1 hn.2)

/-- **Biproducts, exactly.** The dominant dimension of `X ⊞ Y` is the minimum of those of `X` and
`Y`. -/
theorem dominantDimension_biprod (X Y : C) :
    dominantDimension (X ⊞ Y) = min (dominantDimension X) (dominantDimension Y) :=
  le_antisymm (le_min (Retract.dominantDimension_le ⟨biprod.inl, biprod.fst, by simp⟩)
    (Retract.dominantDimension_le ⟨biprod.inr, biprod.snd, by simp⟩))
    (min_dominantDimension_le_dominantDimension_biprod X Y)

/-- **Finite biproducts.** The dominant dimension of a finite biproduct is at least the infimum of
those of its summands. -/
theorem iInf_dominantDimension_le_dominantDimension_biproduct [HasFiniteBiproducts C]
    {J : Type w} [Finite J] (f : J → C) :
    (⨅ j, dominantDimension (f j)) ≤ dominantDimension (⨁ f) := by
  -- Induction on the finite index type, through `Option`.
  refine Finite.induction_empty_option (P := fun J ↦ ∀ [Finite J] (f : J → C),
    (⨅ j, dominantDimension (f j)) ≤ dominantDimension (⨁ f)) ?_ ?_ ?_ J f
  · intro J K e h hK f
    have : Finite J := Finite.of_equiv K e.symm
    rw [← e.iInf_comp, dominantDimension_eq_of_iso
      (biproduct.whiskerEquiv e (fun j ↦ Iso.refl (f (e j)))).symm]
    exact h (f ∘ e)
  · intro _ f
    rw [(isZero_biproduct_of_isEmpty f).dominantDimension_eq_top]
    exact le_top
  · intro J _ h _ f
    rw [iInf_option, dominantDimension_eq_of_iso (biproductOptionIso f)]
    exact (min_le_min_left _ (h _)).trans
      (min_dominantDimension_le_dominantDimension_biprod _ _)

section Equivalence

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An exact functor sending projective-injective objects to projective-injective objects carries
projective-injective coresolutions to projective-injective coresolutions. -/
theorem HasProjectiveInjectiveCoresolution.map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesHomology]
    (hF : ∀ Y : C, Projective Y → Injective Y → Projective (F.obj Y) ∧ Injective (F.obj Y))
    {X : C} {n : ℕ} (h : HasProjectiveInjectiveCoresolution X n) :
    HasProjectiveInjectiveCoresolution (F.obj X) n :=
  HasCoresolution.map F (fun Y hY ↦ hF Y hY.1 hY.2) h

/-- An equivalence sends projective-injective objects to projective-injective objects. -/
private theorem Equivalence.projective_and_injective_functor_obj {C D : Type*} [Category* C]
    [Category* D] [Abelian C] [Abelian D] (F : C ≌ D) (Y : C) (hP : Projective Y)
    (hI : Injective Y) : Projective (F.functor.obj Y) ∧ Injective (F.functor.obj Y) :=
  ⟨(F.map_projective_iff _).2 hP, (F.map_injective_iff _).2 hI⟩

/-- **Equivalences preserve the dominant dimension.** -/
@[simp]
theorem Equivalence.dominantDimension_functor_obj (F : C ≌ D) (X : C) :
    dominantDimension (F.functor.obj X) = dominantDimension X := by
  refine le_antisymm (iSup₂_le fun n hn ↦ natCast_le_dominantDimension_iff.2 ?_)
    (iSup₂_le fun n hn ↦ natCast_le_dominantDimension_iff.2
      (hn.map F.functor (Equivalence.projective_and_injective_functor_obj F)))
  exact (hn.map F.inverse (Equivalence.projective_and_injective_functor_obj F.symm)).of_iso
    (F.unitIso.app X).symm

end Equivalence

end CategoryTheory
