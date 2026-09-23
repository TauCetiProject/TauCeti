/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import TauCeti.Algebra.Lie.Quotient

/-!
# Solvability along Lie homomorphisms, and the radical of a quotient

Mathlib transports solvability of a Lie algebra along injective and surjective homomorphisms and
shows that a sum of two solvable ideals is solvable, but it does not record the third and most
frequently used closure property: solvability is an *extension* property.  A Lie algebra with a
solvable ideal whose quotient is solvable is itself solvable.  This file proves that, in the
sharper form that an ideal is solvable as soon as its image under some homomorphism is solvable
and the part of it inside the kernel is, and draws the consequence that the solvable radical is
carried onto the solvable radical by a surjective homomorphism with solvable kernel.

The headline corollary is that the quotient of a Noetherian Lie algebra by its radical has
trivial radical, so that the radical is the unique solvable ideal with that property.  In
characteristic zero, where `LieAlgebra.HasTrivialRadical` is Cartan's criterion for
semisimplicity, this is the statement that `L ⧸ radical R L` is semisimple: the first step of the
structure theory, and the missing input for identifying the radical of a scalar extension of `L`
with the scalar extension of its radical.

Everything is phrased through `LieAlgebra.derivedSeriesOfIdeal`, the derived series of an ideal
computed inside the ambient algebra, because the type `↥I` makes images and preimages awkward.
Mathlib already relates the two readings through `LieIdeal.derivedSeries_eq_bot_iff`, and the
two new transport lemmas below are the exact analogues for a general starting ideal of Mathlib's
`LieIdeal.derivedSeries_map_le` and `LieIdeal.derivedSeries_map_eq`, which treat the case of the
whole algebra.

## Main statements

* `LieIdeal.derivedSeriesOfIdeal_map_le` and `LieIdeal.derivedSeriesOfIdeal_map_eq`: the derived
  series of an ideal maps into, and for a surjective homomorphism onto, the derived series of the
  image.
* `LieIdeal.isSolvable_map`: the image of a solvable ideal under a surjective homomorphism is
  solvable.
* `LieIdeal.isSolvable_of_isSolvable_map`: solvability descends from the image together with the
  part of the ideal lying in the kernel.
* `LieAlgebra.isSolvable_of_isSolvable_ker_of_surjective` and
  `LieAlgebra.isSolvable_iff_ideal_quotient`: solvability is an extension property.
* `LieIdeal.radical_map_eq`: a surjective homomorphism with solvable kernel carries the radical
  onto the radical.
* `LieAlgebra.hasTrivialRadical_of_equiv`: triviality of the radical transfers along an
  isomorphism of Lie algebras.
* `LieAlgebra.hasTrivialRadical_quotient_radical`: **the quotient of a Noetherian Lie algebra by
  its radical has trivial radical**, with `LieAlgebra.radical_le_of_hasTrivialRadical_quotient`
  and `LieAlgebra.hasTrivialRadical_quotient_iff`: the radical is the smallest ideal, and the
  only solvable one, whose quotient has trivial radical.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1-3*][bourbaki1975], Chapter I, §5.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter III.
-/

public section

open LieAlgebra

namespace LieIdeal

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L)

/-- The image of the `k`-th term of the derived series of an ideal is contained in the `k`-th term
of the derived series of the image.

This is `LieIdeal.derivedSeries_map_le` with `⊤` replaced by an arbitrary ideal. -/
theorem derivedSeriesOfIdeal_map_le (k : ℕ) :
    (derivedSeriesOfIdeal R L k I).map f ≤ derivedSeriesOfIdeal R L' k (I.map f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ]
    exact (map_bracket_le f).trans (LieSubmodule.mono_lie ih ih)

/-- A surjective Lie homomorphism carries the derived series of an ideal onto the derived series
of the image.

This is `LieIdeal.derivedSeries_map_eq` with `⊤` replaced by an arbitrary ideal. -/
theorem derivedSeriesOfIdeal_map_eq (h : Function.Surjective f) (k : ℕ) :
    (derivedSeriesOfIdeal R L k I).map f = derivedSeriesOfIdeal R L' k (I.map f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, map_bracket_eq f h, ih]

/-- The image of a solvable ideal under a surjective Lie homomorphism is solvable. -/
theorem isSolvable_map (h : Function.Surjective f) [IsSolvable ↥I] : IsSolvable ↥(I.map f) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable (R := R) (L := ↥I)
  rw [derivedSeries_eq_bot_iff] at hk
  refine IsSolvable.mk (R := R) (k := k) ?_
  rw [derivedSeries_eq_bot_iff, ← derivedSeriesOfIdeal_map_eq f I h, map_eq_bot_iff, hk]
  exact bot_le

/-- **Solvability descends along a Lie homomorphism.** An ideal is solvable as soon as its image
is solvable and the part of it lying in the kernel is.

Taking `f` to be the quotient map by a solvable ideal and `I` to be `⊤` recovers the statement
that an extension of a solvable Lie algebra by a solvable ideal is solvable, which is
`LieAlgebra.isSolvable_of_isSolvable_ker_of_surjective` below. -/
theorem isSolvable_of_isSolvable_map (h₁ : IsSolvable ↥(I ⊓ f.ker))
    (h₂ : IsSolvable ↥(I.map f)) : IsSolvable ↥I := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable (R := R) (L := ↥(I.map f))
  obtain ⟨l, hl⟩ := IsSolvable.solvable (R := R) (L := ↥(I ⊓ f.ker))
  rw [derivedSeries_eq_bot_iff] at hk hl
  -- After `k` steps the derived series of `I` has died in the image, so it lies in the kernel.
  have hle : derivedSeriesOfIdeal R L k I ≤ I ⊓ f.ker :=
    le_inf (derivedSeriesOfIdeal_le_self I k)
      (map_eq_bot_iff.mp (le_bot_iff.mp ((derivedSeriesOfIdeal_map_le f I k).trans hk.le)))
  refine IsSolvable.mk (R := R) (k := l + k) ?_
  rw [derivedSeries_eq_bot_iff, derivedSeriesOfIdeal_add]
  exact le_bot_iff.mp ((derivedSeriesOfIdeal_mono hle l).trans hl.le)

/-- A surjective Lie homomorphism with solvable kernel carries the solvable radical onto the
solvable radical. -/
theorem radical_map_eq [IsNoetherian R L] (h : Function.Surjective f)
    (hker : IsSolvable ↥f.ker) : (radical R L).map f = radical R L' := by
  have hL' : IsNoetherian R L' :=
    isNoetherian_of_surjective f.toLinearMap (LinearMap.range_eq_top.mpr h)
  have hmap : ∀ J : LieIdeal R L', (J.comap f).map f = J := fun J => by
    rw [map_comap_eq (f.isIdealMorphism_of_surjective h),
      f.idealRange_eq_top_of_surjective h, top_inf_eq]
  refine le_antisymm ((LieIdeal.solvable_iff_le_radical R L' _).mp (isSolvable_map f _ h)) ?_
  have hcomap : IsSolvable ↥((radical R L').comap f) :=
    isSolvable_of_isSolvable_map f _ (le_solvable_ideal_solvable inf_le_right hker)
      (by rw [hmap]; infer_instance)
  calc radical R L' = ((radical R L').comap f).map f := (hmap _).symm
    _ ≤ (radical R L).map f := map_mono ((LieIdeal.solvable_iff_le_radical R L _).mp hcomap)

end LieIdeal

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- **An extension of a solvable Lie algebra by a solvable ideal is solvable.** -/
theorem isSolvable_of_isSolvable_ker_of_surjective {f : L →ₗ⁅R⁆ L'} (h : Function.Surjective f)
    (h₁ : IsSolvable ↥f.ker) (h₂ : IsSolvable L') : IsSolvable L := by
  have h₃ : IsSolvable ↥(⊤ : LieIdeal R L) := by
    refine LieIdeal.isSolvable_of_isSolvable_map f ⊤
      (le_solvable_ideal_solvable inf_le_right h₁) ?_
    rw [← LieHom.idealRange_eq_map, f.idealRange_eq_top_of_surjective h]
    exact (solvable_iff_equiv_solvable LieIdeal.topEquiv).mpr h₂
  exact (solvable_iff_equiv_solvable LieIdeal.topEquiv).mp h₃

/-- **Solvability is an extension property**: a Lie algebra is solvable exactly when both an ideal
and the quotient by it are. -/
theorem isSolvable_iff_ideal_quotient (I : LieIdeal R L) :
    IsSolvable L ↔ IsSolvable ↥I ∧ IsSolvable (L ⧸ I) := by
  refine ⟨fun _ => ⟨inferInstance, I.mkQ_surjective.lieAlgebra_isSolvable⟩, fun h => ?_⟩
  obtain ⟨h₁, h₂⟩ := h
  exact isSolvable_of_isSolvable_ker_of_surjective I.mkQ_surjective (by rwa [I.ker_mkQ]) h₂

/-- **Triviality of the radical transfers along an isomorphism of Lie algebras.**  A solvable
ideal of the source is carried to a solvable ideal of the target, which vanishes, and the
isomorphism is injective.

Nothing is assumed of the coefficients: the statement is about solvable ideals one at a time, so
it does not go through the radical itself and needs no Noetherian hypothesis. -/
theorem hasTrivialRadical_of_equiv (e : L ≃ₗ⁅R⁆ L') [HasTrivialRadical R L'] :
    HasTrivialRadical R L :=
  hasTrivialRadical_of_no_solvable_ideals fun I hI => by
    have _ : IsSolvable ↥I := hI
    have hbot : I.map (e : L →ₗ⁅R⁆ L') = ⊥ :=
      HasTrivialRadical.eq_bot_of_isSolvable
        (hI := LieIdeal.isSolvable_map _ _ e.surjective) _
    have hker : (e : L →ₗ⁅R⁆ L').ker = ⊥ := (LieHom.ker_eq_bot _).mpr e.injective
    rw [LieIdeal.map_eq_bot_iff, hker, le_bot_iff] at hbot
    exact hbot

variable (R L)

/-- **The quotient of a Noetherian Lie algebra by its solvable radical has trivial radical.**

Over a field of characteristic zero, where `LieAlgebra.HasTrivialRadical` is equivalent to
semisimplicity by Cartan's criterion, this says that `L ⧸ radical R L` is semisimple. -/
instance hasTrivialRadical_quotient_radical [IsNoetherian R L] :
    HasTrivialRadical R (L ⧸ radical R L) where
  radical_eq_bot := by
    rw [← LieIdeal.radical_map_eq (radical R L).mkQ (radical R L).mkQ_surjective
        (by rw [LieIdeal.ker_mkQ]; infer_instance),
      LieIdeal.map_eq_bot_iff, LieIdeal.ker_mkQ]

variable {R L}

/-- **The radical is the smallest ideal whose quotient has trivial radical.**  Its image in such a
quotient is a solvable ideal, hence trivial. -/
theorem radical_le_of_hasTrivialRadical_quotient [IsNoetherian R L] (I : LieIdeal R L)
    [HasTrivialRadical R (L ⧸ I)] : radical R L ≤ I := by
  have hbot : (radical R L).map I.mkQ = ⊥ :=
    HasTrivialRadical.eq_bot_of_isSolvable
      (hI := LieIdeal.isSolvable_map I.mkQ _ I.mkQ_surjective) _
  rwa [LieIdeal.map_eq_bot_iff, I.ker_mkQ] at hbot

/-- **The radical is the unique solvable ideal whose quotient has trivial radical.** -/
@[simp]
theorem hasTrivialRadical_quotient_iff [IsNoetherian R L] (I : LieIdeal R L) [IsSolvable ↥I] :
    HasTrivialRadical R (L ⧸ I) ↔ I = radical R L :=
  ⟨fun _ => le_antisymm ((LieIdeal.solvable_iff_le_radical R L I).mp ‹_›)
      (radical_le_of_hasTrivialRadical_quotient I),
    fun h => h ▸ hasTrivialRadical_quotient_radical R L⟩

end LieAlgebra
