/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.RingTheory.Idempotents.Semiperfect
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Krull-Schmidt categories and semiperfect endomorphism rings

An additive category is Krull-Schmidt exactly when its idempotents split and the endomorphism ring
of every object is semiperfect (Krause, Corollary 4.4). Both directions go through the ring
characterization of semiperfect rings (Lam (23.6),
`TauCeti.isSemiperfectRing_iff_exists_completeOrthogonalIdempotents_isLocalRing_corner`): `End X`
is semiperfect exactly when `𝟙 X` is a sum of orthogonal idempotents with local corners.

* If idempotents split, such idempotents `eᵢ` split through objects `Xᵢ` whose endomorphism rings
  are the corners `eᵢ (End X) eᵢ` (`TauCeti.cornerRingEquivEnd`), and `X ≅ ⨁ Xᵢ`.
* Conversely, a decomposition `X ≅ ⨁ Pᵢ` with local `End Pᵢ` gives such idempotents, the
  projections onto the summands.

Over a commutative Artinian ring `R`, the endomorphism ring of an object with `X ⟶ X` finite over
`R` is semiperfect, which gives the summand decomposition of such an object and recognizes
Hom-finite idempotent-complete categories with finite biproducts as Krull-Schmidt.

## Main results

* `TauCeti.cornerRingEquivEnd`: the corner of `End X` at a split idempotent is the endomorphism
  ring of its image.
* `TauCeti.isKrullSchmidt_iff_isIdempotentComplete_and_isSemiperfectRing_end`: **Krause's
  criterion**, a category with finite biproducts is Krull-Schmidt exactly when idempotents split
  and every endomorphism ring is semiperfect.
* `TauCeti.exists_completeOrthogonalIdempotents_isLocalRing_corner_end`: the summand
  decomposition, `𝟙 X` is a sum of orthogonal idempotents with local corners when `X ⟶ X` is
  finite over a commutative Artinian ring.
* `TauCeti.isKrullSchmidt_of_module_finite`: an idempotent-complete category with finite
  biproducts that is Hom-finite over a commutative Artinian ring is Krull-Schmidt.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Corollary 4.4.
* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001),
  Theorem (23.6).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

/-- **The corner of `End X` at a split idempotent is the endomorphism ring of its image**: if
`e = p ≫ i` with `i ≫ p = 𝟙 Y`, then `g ↦ p ≫ g ≫ i` identifies `End Y` with `e (End X) e`. -/
noncomputable def cornerRingEquivEnd {X Y : C} {e : End X} (he : IsIdempotentElem e)
    (i : Y ⟶ X) (p : X ⟶ Y) (hip : i ≫ p = 𝟙 Y) (hpi : p ≫ i = e.asHom) :
    End Y ≃+* he.Corner where
  toFun g := ⟨End.of (p ≫ g.asHom ≫ i), by
    refine (Subsemigroup.mem_corner_iff he).2 ⟨End.ext ?_, End.ext ?_⟩ <;>
      simp [← hpi, reassoc_of% hip]⟩
  invFun c := End.of (i ≫ c.1.asHom ≫ p)
  left_inv g := End.ext (by simp [reassoc_of% hip, hip])
  right_inv c := by
    obtain ⟨c, hc⟩ := c
    obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff he).1 hc
    have hl' : c.asHom ≫ e.asHom = c.asHom := by simpa using congrArg End.asHom hl
    have hr' : e.asHom ≫ c.asHom = c.asHom := by simpa using congrArg End.asHom hr
    refine Subtype.ext (End.ext ?_)
    change p ≫ (i ≫ c.asHom ≫ p) ≫ i = c.asHom
    calc p ≫ (i ≫ c.asHom ≫ p) ≫ i = (p ≫ i) ≫ c.asHom ≫ (p ≫ i) := by simp only [Category.assoc]
      _ = c.asHom := by rw [hpi, hl', hr']
  map_mul' g h := by
    apply Subtype.ext
    change End.of (p ≫ (g * h).asHom ≫ i) = End.of (p ≫ g.asHom ≫ i) * End.of (p ≫ h.asHom ≫ i)
    ext
    simp [reassoc_of% hip]
  map_add' g h := by
    apply Subtype.ext
    change End.of (p ≫ (g + h).asHom ≫ i) = End.of (p ≫ g.asHom ≫ i) + End.of (p ≫ h.asHom ≫ i)
    ext
    simp

variable [HasFiniteBiproducts C]

/-- **Decomposition along local idempotents**: if idempotents split and `𝟙 X` is a sum of
orthogonal idempotents with local corners, then `X` is a finite biproduct of objects with local
endomorphism rings. -/
theorem exists_iso_biproduct_of_isLocalRing_corner [IsIdempotentComplete C] {X : C} {n : ℕ}
    {f : Fin n → End X} (hf : CompleteOrthogonalIdempotents f)
    (hloc : ∀ i, IsLocalRing (hf.idem i).Corner) :
    ∃ P : Fin n → C, (∀ i, IsLocalRing (End (P i))) ∧ Nonempty (X ≅ ⨁ P) := by
  classical
  choose P ι π hιπ hπι using fun i ↦
    IsIdempotentComplete.idempotents_split X (f i).asHom (congrArg End.asHom (hf.idem i).eq)
  refine ⟨P, fun i ↦ ?_, ⟨?_⟩⟩
  · have := hloc i
    let φ := cornerRingEquivEnd (hf.idem i) (ι i) (π i) (hιπ i) (hπι i)
    have : Nontrivial (End (P i)) := φ.symm.injective.nontrivial
    exact IsLocalRing.of_surjective' φ.symm.toRingHom φ.symm.surjective
  -- `ι a ≫ π b = ι a ≫ (fₐ ≫ f_b) ≫ π b = 0` for `a ≠ b`.
  have key (a b : Fin n) (hab : a ≠ b) : ι a ≫ π b = 0 := by
    have h0 : (π a ≫ ι a) ≫ (π b ≫ ι b) = 0 := by
      rw [hπι, hπι]
      simpa using congrArg End.asHom (hf.ortho hab.symm)
    have : ι a ≫ π b = ι a ≫ ((π a ≫ ι a) ≫ (π b ≫ ι b)) ≫ π b := by
      simp [reassoc_of% (hιπ a), hιπ b]
    rw [this, h0, zero_comp, comp_zero]
  -- `X ≅ ⨁ Pᵢ`, with components `π i` and `ι i`.
  refine ⟨biproduct.lift π, biproduct.desc ι, ?_, ?_⟩
  · have := congrArg End.asHom hf.complete
    simpa [biproduct.lift_desc, End.sum_asHom, hπι] using this
  · ext j k
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π, Category.id_comp,
      biproduct.ι_π]
    split_ifs with h
    · subst h
      simp [hιπ]
    · exact key _ _ h

/-- **Split idempotents and semiperfect endomorphism rings give a Krull-Schmidt category**
(Krause, Corollary 4.4, "if"): `𝟙 X` is a sum of orthogonal idempotents with local corners
(`TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner`), which split
(`TauCeti.exists_iso_biproduct_of_isLocalRing_corner`). -/
theorem isKrullSchmidt_of_isSemiperfectRing_end [IsIdempotentComplete C]
    (h : ∀ X : C, IsSemiperfectRing (End X)) : IsKrullSchmidt C where
  exists_iso_biproduct X := by
    have := h X
    obtain ⟨n, f, hf, hloc⟩ :=
      IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner (A := End X)
    obtain ⟨P, hP, e⟩ := exists_iso_biproduct_of_isLocalRing_corner hf hloc
    exact ⟨n, P, hP, e⟩

/-- **The endomorphism rings of a Krull-Schmidt category are semiperfect** (Krause, Corollary 4.4,
"only if"): a decomposition `X ≅ ⨁ Pᵢ` with local `End Pᵢ` writes `𝟙 X` as the sum of the
projections onto the summands, orthogonal idempotents whose corners are the rings `End Pᵢ`, so
`End X` is semiperfect by Lam (23.6) (`TauCeti.IsSemiperfectRing.of_isLocalRing_corner`). -/
instance IsKrullSchmidt.isSemiperfectRing_end [IsKrullSchmidt C] (X : C) :
    IsSemiperfectRing (End X) := by
  classical
  obtain ⟨n, P, hP, ⟨φ⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
  let f : Fin n → End X := fun i ↦ End.of (φ.hom ≫ biproduct.π P i ≫ biproduct.ι P i ≫ φ.inv)
  have hf : CompleteOrthogonalIdempotents f :=
    { idem := fun i ↦ End.ext (by simp [f])
      ortho := fun i j hij ↦ End.ext (by simp [f, biproduct.ι_π_ne_assoc _ hij.symm])
      complete := End.ext (by
        have : ∑ j, biproduct.π P j ≫ biproduct.ι P j ≫ φ.inv =
            (∑ j, biproduct.π P j ≫ biproduct.ι P j) ≫ φ.inv := by
          rw [Preadditive.sum_comp]
          simp only [Category.assoc]
        simp only [End.sum_asHom, f, End.one_asHom]
        rw [← Preadditive.comp_sum, this, biproduct.total]
        simp) }
  refine IsSemiperfectRing.of_isLocalRing_corner hf fun i ↦ ?_
  -- The corner at the projection onto `Pᵢ` is `End Pᵢ`.
  have := hP i
  let ψ := cornerRingEquivEnd (hf.idem i) (biproduct.ι P i ≫ φ.inv) (φ.hom ≫ biproduct.π P i)
    (by simp) (by simp [f])
  have : Nontrivial (hf.idem i).Corner := ψ.injective.nontrivial
  exact IsLocalRing.of_surjective' ψ.toRingHom ψ.surjective

/-- **Krause's criterion**: a category with finite biproducts is Krull-Schmidt exactly when
idempotents split and the endomorphism ring of every object is semiperfect. -/
theorem isKrullSchmidt_iff_isIdempotentComplete_and_isSemiperfectRing_end :
    IsKrullSchmidt C ↔ IsIdempotentComplete C ∧ ∀ X : C, IsSemiperfectRing (End X) :=
  ⟨fun _ ↦ ⟨inferInstance, fun _ ↦ inferInstance⟩,
    fun ⟨_, h⟩ ↦ isKrullSchmidt_of_isSemiperfectRing_end h⟩

end TauCeti

namespace TauCeti

open CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C] (R : Type*) [CommRing R] [IsArtinianRing R]
  [Linear R C]

/-- **Summand decomposition**: if `X ⟶ X` is finite over a commutative Artinian ring `R`, then
`𝟙 X` is a sum of orthogonal idempotents whose corners are local rings, as the Artin `R`-algebra
`End X` is semiperfect. -/
theorem exists_completeOrthogonalIdempotents_isLocalRing_corner_end (X : C)
    [Module.Finite R (X ⟶ X)] :
    ∃ (n : ℕ) (f : Fin n → End X) (hf : CompleteOrthogonalIdempotents f),
      ∀ i, IsLocalRing (hf.idem i).Corner :=
  have : Module.Finite R (End X) := Module.Finite.equiv End.linearEquiv.symm
  have := IsSemiperfectRing.of_finite R (End X)
  IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner

/-- **Recognition of Krull-Schmidt categories**: an idempotent-complete category with finite
biproducts whose endomorphisms are finite over a commutative Artinian ring is Krull-Schmidt. -/
theorem isKrullSchmidt_of_module_finite [Limits.HasFiniteBiproducts C] [IsIdempotentComplete C]
    [∀ X : C, Module.Finite R (X ⟶ X)] : IsKrullSchmidt C :=
  isKrullSchmidt_of_isSemiperfectRing_end fun X ↦
    have : Module.Finite R (End X) := Module.Finite.equiv End.linearEquiv.symm
    IsSemiperfectRing.of_finite R (End X)

end TauCeti
