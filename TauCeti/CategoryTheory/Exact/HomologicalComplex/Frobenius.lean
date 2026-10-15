/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import TauCeti.Algebra.Homology.HomotopyCofiber
public import TauCeti.CategoryTheory.Exact.Frobenius
public import TauCeti.CategoryTheory.Exact.HomologicalComplex

/-!
# Complexes with the componentwise split exact structure are Frobenius

Let `C` be an additive category and `c` a complex shape. The componentwise split exact structure
`(ExactStructure.split C).homologicalComplex c` on `HomologicalComplex C c` has as conflations the
short complexes of complexes which split in every degree, not necessarily compatibly with the
differentials. This file proves that it is a Frobenius exact structure whose projective and
injective objects are exactly the contractible complexes, those `K` with a homotopy
`Homotopy (𝟙 K) 0`, as soon as every index of `c` is both the source and the target of a
relation. This holds for cochain and chain complexes indexed by `ℤ` and for the `n`-periodic
complexes indexed by `ComplexShape.up (ZMod n)`.

These results are what the stable-category machinery needs to apply to complexes. The
projective stable category `((split C).homologicalComplex c).ProjectiveStableCategory` kills the
morphisms factoring through a contractible complex, which are the null-homotopic ones, so it is a
model of the homotopy category of complexes of shape `c`. Being Frobenius, it is triangulated by
Happel's theorem `TauCeti.ExactStructure.IsFrobenius.stableIsTriangulated`. In particular this
covers the homotopy categories of `ℤ`-indexed and of `n`-periodic complexes. The comparison with
Mathlib's `HomotopyCategory C c` is not part of this file.

The hypotheses on the shape are needed: for `ℕ`-indexed chain complexes, a nonzero object
placed in degree `0` is relatively projective but not relatively injective.

## Main results

* `TauCeti.ExactStructure.homologicalComplex_split_isInjective_iff` and
  `TauCeti.ExactStructure.homologicalComplex_split_isProjective_iff`: the relatively injective
  and relatively projective complexes are the contractible ones.
* `TauCeti.ExactStructure.homologicalComplex_split_isFrobenius`: the componentwise split exact
  structure on complexes is Frobenius.
* `TauCeti.ExactStructure.homologicalComplex_split_up'_isFrobenius` and
  `TauCeti.ExactStructure.homologicalComplex_split_down'_isFrobenius`: the special cases of the
  shapes `ComplexShape.up' a` and `ComplexShape.down' a` over an additive group. These include
  `ComplexShape.up ℤ`, `ComplexShape.down ℤ` and the periodic shapes
  `ComplexShape.up (ZMod n)`.

## References

* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1, where the category of complexes with the componentwise split
  exact structure is shown to be Frobenius with the contractible complexes as its
  projective-injective objects.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 3.
* Torkil Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters
  **25** (2018), 199–236, Section 3, for the periodic case.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject

universe v u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {ι : Type u'} {c : ComplexShape ι}

namespace ExactStructure

/-- A contractible complex is relatively injective for the componentwise split exact
structure, for every complex shape. -/
theorem homologicalComplex_split_isInjective_of_homotopy {K : HomologicalComplex C c}
    (h : Homotopy (𝟙 K) 0) : ((split C).homologicalComplex c).isInjective K := by
  refine isInjective_iff.2 fun A B i hi g => ?_
  -- The retractions of the components of `i` need not commute with the differentials.
  have r n : SplitMono (i.f n) :=
    (isSplitMono_of_split_isInflation
      ((homologicalComplex_isInflation_iff _ _ i).1 hi n)).exists_splitMono.some
  -- `g` extends along `i` by the null-homotopic map built from the components of a
  -- contraction of `K`, precomposed with these retractions.
  refine ⟨Homotopy.nullHomotopicMap fun p q => (r p).retraction ≫ g.f p ≫ h.hom p q, ?_⟩
  rw [Homotopy.comp_nullHomotopicMap]
  simp_rw [SplitMono.id_assoc]
  rw [← Homotopy.comp_nullHomotopicMap, ← h.sub_eq_nullHomotopicMap, sub_zero, Category.comp_id]

/-- A contractible complex is relatively projective for the componentwise split exact
structure, for every complex shape. -/
theorem homologicalComplex_split_isProjective_of_homotopy {K : HomologicalComplex C c}
    (h : Homotopy (𝟙 K) 0) : ((split C).homologicalComplex c).isProjective K := by
  refine isProjective_iff.2 fun A B p hp g => ?_
  -- The sections of the components of `p` need not commute with the differentials.
  have s n : SplitEpi (p.f n) :=
    (isSplitEpi_of_split_isDeflation
      ((homologicalComplex_isDeflation_iff _ _ p).1 hp n)).exists_splitEpi.some
  -- `g` lifts along `p` by the null-homotopic map built from the components of a
  -- contraction of `K`, postcomposed with these sections.
  refine ⟨Homotopy.nullHomotopicMap fun i j => h.hom i j ≫ g.f j ≫ (s j).section_, ?_⟩
  rw [Homotopy.nullHomotopicMap_comp]
  simp_rw [Category.assoc, SplitEpi.id, Category.comp_id]
  rw [← Homotopy.nullHomotopicMap_comp, ← h.sub_eq_nullHomotopicMap, sub_zero, Category.id_comp]

/-- The inclusion of a complex into the mapping cone of a morphism is a componentwise split
inflation: in degree `i` it is the inclusion of the summand `G.X i` of
`F.X j ⊞ G.X i` for `c.Rel i j`, and an isomorphism when `i` is the source of no relation. -/
theorem homologicalComplex_split_isInflation_inr [DecidableRel c.Rel]
    {F G : HomologicalComplex C c} (φ : F ⟶ G) :
    ((split C).homologicalComplex c).IsInflation (homotopyCofiber.inr φ) := by
  refine (homologicalComplex_isInflation_iff _ _ _).2 fun n => (split_isInflation_iff _).2 ?_
  by_cases hn : c.Rel n (c.next n)
  · exact ⟨F.X (c.next n), homotopyCofiber.XIsoBiprod φ n _ hn ≪≫ biprod.braiding _ _,
      by ext <;> simp⟩
  · exact ⟨0, homotopyCofiber.XIso φ n hn ≪≫ isoBiprodZero (isZero_zero C),
      by simp [homotopyCofiber.inrX, hn]⟩

/-- Every complex is a componentwise split subobject of a contractible one, the mapping cone of
its identity. -/
theorem homologicalComplex_split_enoughInjectives (hc : ∀ j, ∃ i, c.Rel i j) :
    ((split C).homologicalComplex c).EnoughInjectives := by
  classical
  refine ⟨fun K => ?_⟩
  obtain ⟨Z, p, zero, hS⟩ :=
    (ConflationClass.isInflation_iff _ _).1 (homologicalComplex_split_isInflation_inr (𝟙 K))
  exact ⟨⟨_, Z, _, p, zero, hS, homologicalComplex_split_isInjective_of_homotopy
    (homotopyCofiber.homotopyToZeroOfId K hc)⟩⟩

/-- For every complex `K` there is a contractible complex with a componentwise split deflation
onto `K`. It is the unopposite of the mapping cone of the identity of `K.op` in `Cᵒᵖ`, whose
existence needs every index of `c` to be the source of a relation. -/
private theorem exists_homologicalComplex_split_isDeflation (hc : ∀ i, ∃ j, c.Rel i j)
    (K : HomologicalComplex C c) :
    ∃ (P : HomologicalComplex C c) (p : P ⟶ K),
      ((split C).homologicalComplex c).IsDeflation p ∧ Nonempty (Homotopy (𝟙 P) 0) := by
  classical
  let inr := homotopyCofiber.inr (𝟙 K.op)
  -- In degree `n`, `p` is the unopposite of the inclusion of `K.op` into the cone.
  let p : (homotopyCofiber (𝟙 K.op)).unopSymm ⟶ K :=
    { f n := (inr.f n).unop
      -- The opposite of the commutation square of `p` is the reversed square of `inr`.
      comm' i j _ := Quiver.Hom.op_inj (inr.comm j i).symm }
  have h := homotopyCofiber.homotopyToZeroOfId K.op hc
  refine ⟨_, p, (homologicalComplex_isDeflation_iff _ _ _).2 fun n =>
    (split_isInflation_iff_isDeflation_unop _).1
      ((homologicalComplex_isInflation_iff _ _ _).1
        (homologicalComplex_split_isInflation_inr (𝟙 K.op)) n), ⟨?_⟩⟩
  exact
    { hom i j := (h.hom j i).unop
      zero i j hij := Quiver.Hom.op_inj (h.zero _ _ hij)
      comm n := by
        have := congrArg Quiver.Hom.unop (h.comm n)
        simp only [dNext, prevD, AddMonoidHom.mk'_apply] at this ⊢
        simp only [id_f, unop_id, unop_add, unop_comp, zero_f, add_zero,
          HomologicalComplex.unopSymm_d] at this ⊢
        rw [add_comm]
        -- `c.symm.next n` and `c.symm.prev n` unfold to `c.prev n` and `c.next n`.
        exact this }

/-- Every complex is a componentwise split quotient of a contractible one. -/
theorem homologicalComplex_split_enoughProjectives (hc : ∀ i, ∃ j, c.Rel i j) :
    ((split C).homologicalComplex c).EnoughProjectives := by
  refine ⟨fun K => ?_⟩
  obtain ⟨P, p, hp, ⟨h⟩⟩ := exists_homologicalComplex_split_isDeflation hc K
  obtain ⟨Z, i, zero, hS⟩ := (ConflationClass.isDeflation_iff _ _).1 hp
  exact ⟨⟨Z, _, i, p, zero, hS, homologicalComplex_split_isProjective_of_homotopy h⟩⟩

/-- **The relatively injective complexes are the contractible ones.** For the componentwise
split exact structure, and when every index of the shape is the target of a relation, a
complex is relatively injective exactly when its identity is null-homotopic. -/
theorem homologicalComplex_split_isInjective_iff (hc : ∀ j, ∃ i, c.Rel i j)
    (K : HomologicalComplex C c) :
    ((split C).homologicalComplex c).isInjective K ↔ Nonempty (Homotopy (𝟙 K) 0) := by
  classical
  refine ⟨fun hK => ?_, fun ⟨h⟩ => homologicalComplex_split_isInjective_of_homotopy h⟩
  -- `K` is a retract of the mapping cone of its identity, which is contractible.
  obtain ⟨r, hr⟩ := isInjective_iff.1 hK (homologicalComplex_split_isInflation_inr (𝟙 K)) (𝟙 K)
  exact ⟨(Homotopy.ofEq (by simp [hr])).trans
    ((((homotopyCofiber.homotopyToZeroOfId K hc).compRight r).compLeft
      (homotopyCofiber.inr (𝟙 K))).trans (Homotopy.ofEq (by simp)))⟩

/-- **The relatively projective complexes are the contractible ones.** For the componentwise
split exact structure, and when every index of the shape is the source of a relation, a
complex is relatively projective exactly when its identity is null-homotopic. -/
theorem homologicalComplex_split_isProjective_iff (hc : ∀ i, ∃ j, c.Rel i j)
    (K : HomologicalComplex C c) :
    ((split C).homologicalComplex c).isProjective K ↔ Nonempty (Homotopy (𝟙 K) 0) := by
  refine ⟨fun hK => ?_, fun ⟨h⟩ => homologicalComplex_split_isProjective_of_homotopy h⟩
  -- `K` is a retract of a contractible complex covering it.
  obtain ⟨P, p, hp, ⟨h⟩⟩ := exists_homologicalComplex_split_isDeflation hc K
  obtain ⟨s, hs⟩ := isProjective_iff.1 hK hp (𝟙 K)
  exact ⟨(Homotopy.ofEq (by simp [hs])).trans
    (((h.compRight p).compLeft s).trans (Homotopy.ofEq (by simp)))⟩

/-- **Complexes form a Frobenius exact category.** If every index of the complex shape `c` is
both the source and the target of a relation, the componentwise split exact structure on
`HomologicalComplex C c` is Frobenius, and its projective-injective objects are the contractible
complexes (`homologicalComplex_split_isProjective_iff`). -/
theorem homologicalComplex_split_isFrobenius (hc : ∀ j, ∃ i, c.Rel i j)
    (hc' : ∀ i, ∃ j, c.Rel i j) : ((split C).homologicalComplex c).IsFrobenius where
  enoughProjectives := homologicalComplex_split_enoughProjectives hc'
  enoughInjectives := homologicalComplex_split_enoughInjectives hc
  projective_iff_injective K := by
    rw [homologicalComplex_split_isProjective_iff hc', homologicalComplex_split_isInjective_iff hc]

/-- Complexes of shape `ComplexShape.up' a` over an additive group, such as cochain complexes
indexed by `ℤ` and periodic complexes indexed by `ZMod n`, form a Frobenius exact category for
the componentwise split exact structure. -/
theorem homologicalComplex_split_up'_isFrobenius {α : Type*} [AddGroup α] (a : α) :
    ((split C).homologicalComplex (ComplexShape.up' a)).IsFrobenius :=
  homologicalComplex_split_isFrobenius (fun j => ⟨j - a, sub_add_cancel j a⟩)
    (fun i => ⟨i + a, rfl⟩)

/-- Complexes of shape `ComplexShape.down' a` over an additive group, such as chain complexes
indexed by `ℤ`, form a Frobenius exact category for the componentwise split exact structure. -/
theorem homologicalComplex_split_down'_isFrobenius {α : Type*} [AddGroup α] (a : α) :
    ((split C).homologicalComplex (ComplexShape.down' a)).IsFrobenius :=
  homologicalComplex_split_isFrobenius (fun j => ⟨j + a, rfl⟩)
    (fun i => ⟨i - a, sub_add_cancel i a⟩)

end ExactStructure

end TauCeti
