/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.IsPerfect
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyThree
import Mathlib.Tactic.Abel

/-!
# Perfectness of the five Mathieu presentations

The exact presentations of `M₁₁`, `M₁₂`, `M₂₂`, `M₂₃`, and `M₂₄` are perfect. Every
homomorphism to a commutative group kills both generators: the exponent-sum rows of the
defining relators span `ℤ²`. Applying this to the abelianization map proves perfectness.

These are basic properties for milestone P1 of
`TauCetiRoadmap/CFSGBasicProperties/README.md`. They do not establish finiteness, orders,
or simplicity of the presented groups.
-/

public section

namespace TauCeti.Sporadic.Mathieu

private theorem map_transcribed_eq_one {P : GroupPresentation} {G : Type*} [Group G]
    (f : P.Group →* G) :
    ∀ t ∈ P.transcribed, f (PresentedGroup.mk P.relatorSet t.toFreeGroup) = 1 := by
  intro t ht
  rw [PresentedGroup.one_of_mem ((P.mem_relatorSet_iff _).mpr ⟨t, ht, rfl⟩), map_one]

/-- Every homomorphism from the transcribed `M₁₁` presentation to a commutative group is trivial. -/
theorem m11_hom_eq_one {G : Type*} [CommGroup G] (f : m11Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m11Presentation_transcribed] at h
  simp only [List.forall_mem_cons,
    Relator.toFreeGroup_mul, Relator.toFreeGroup_inv, Relator.toFreeGroup_gen,
    Relator.toFreeGroup_pow, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  change b + 3 • (-a) + b + -a + 3 • b = 0 at h₁'
  change b + a + -b + -a + -b + -a + b + a + -b + a = 0 at h₂'
  have hr₁ : (-4 : ℤ) • a + 5 • b = 0 := by
    calc
      _ = b + 3 • (-a) + b + -a + 3 • b := by abel
      _ = 0 := h₁'
  have hr₂ : a - b = 0 := by
    calc
      _ = b + a + -b + -a + -b + -a + b + a + -b + a := by abel
      _ = 0 := h₂'
  have ha : a = 0 := by
    calc
      a = ((-4 : ℤ) • a + 5 • b) + 5 • (a - b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  have hb : b = 0 := by
    calc
      b = ((-4 : ℤ) • a + 5 • b) + 4 • (a - b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m11Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₁₁` presentation equals its commutator subgroup. -/
theorem m11_isPerfect : Group.IsPerfect m11Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m11_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

/-- Every homomorphism from the transcribed `M₁₂` presentation to a commutative group is trivial. -/
theorem m12_hom_eq_one {G : Type*} [CommGroup G] (f : m12Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m12Presentation_transcribed] at h
  simp only [List.forall_mem_cons, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, h₃, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  have h₃' := congrArg Additive.ofMul h₃
  change 3 • (-b + a) = 0 at h₁'
  change 5 • a + 6 • b = 0 at h₂'
  change a + 2 • b + a + -b + 2 • a + b + 2 • a + 2 • b = 0 at h₃'
  have hr₁ : (3 : ℤ) • a - 3 • b = 0 := by
    calc
      _ = 3 • (-b + a) := by abel
      _ = 0 := h₁'
  have hr₃ : (6 : ℤ) • a + 4 • b = 0 := by
    calc
      _ = a + 2 • b + a + -b + 2 • a + b + 2 • a + 2 • b := by abel
      _ = 0 := h₃'
  -- Integer combinations (6, 11, -12) and (-5, -9, 10) recover the two generators.
  have ha : a = 0 := by
    calc
      a = 6 • ((3 : ℤ) • a - 3 • b) + 11 • (5 • a + 6 • b) -
          12 • ((6 : ℤ) • a + 4 • b) := by abel
      _ = 0 := by rw [hr₁, h₂', hr₃]; simp
  have hb : b = 0 := by
    calc
      b = -5 • ((3 : ℤ) • a - 3 • b) - 9 • (5 • a + 6 • b) +
          10 • ((6 : ℤ) • a + 4 • b) := by abel
      _ = 0 := by rw [hr₁, h₂', hr₃]; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m12Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₁₂` presentation equals its commutator subgroup. -/
theorem m12_isPerfect : Group.IsPerfect m12Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m12_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

/-- Every homomorphism from the transcribed `M₂₂` presentation to a commutative group is trivial. -/
theorem m22_hom_eq_one {G : Type*} [CommGroup G] (f : m22Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m22Presentation_transcribed] at h
  simp only [List.forall_mem_cons, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  change 4 • a + b + -a + b + -a + b = 0 at h₁'
  change 2 • a + b + -a + -b + a + 2 • b + -a + -b = 0 at h₂'
  have hr₁ : (2 : ℤ) • a + 3 • b = 0 := by
    calc
      _ = 4 • a + b + -a + b + -a + b := by abel
      _ = 0 := h₁'
  have hr₂ : a + b = 0 := by
    calc
      _ = 2 • a + b + -a + -b + a + 2 • b + -a + -b := by abel
      _ = 0 := h₂'
  -- The first two relators suffice; the relation b¹¹ = 1 is not needed here.
  have ha : a = 0 := by
    calc
      a = -((2 : ℤ) • a + 3 • b) + 3 • (a + b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  have hb : b = 0 := by
    calc
      b = ((2 : ℤ) • a + 3 • b) - 2 • (a + b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m22Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₂₂` presentation equals its commutator subgroup. -/
theorem m22_isPerfect : Group.IsPerfect m22Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m22_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

/-- Every homomorphism from the transcribed `M₂₃` presentation to a commutative group is trivial. -/
theorem m23_hom_eq_one {G : Type*} [CommGroup G] (f : m23Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m23Presentation_transcribed] at h
  simp only [List.forall_mem_cons, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, Relator.toFreeGroup_comm,
    commutatorElement_def, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, h₃, _, _, _, h₇, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  have h₃' := congrArg Additive.ofMul h₃
  have h₇' := congrArg Additive.ofMul h₇
  change 2 • a = 0 at h₁'
  change 4 • b = 0 at h₂'
  change 23 • (a + b) = 0 at h₃'
  change 3 • (a + b) + (a + -b) + (a + 2 • b) +
    2 • ((a + b) + (a + -b)) + 3 • (a + b) + 3 • (a + -b) = 0 at h₇'
  have hr₇ : (15 : ℤ) • a + 4 • b = 0 := by
    calc
      _ = 3 • (a + b) + (a + -b) + (a + 2 • b) +
          2 • ((a + b) + (a + -b)) + 3 • (a + b) + 3 • (a + -b) := by abel
      _ = 0 := h₇'
  -- The seventh relator kills the possible order-two abelian quotient.
  have ha : a = 0 := by
    calc
      a = 8 • (2 • a) + 4 • b - ((15 : ℤ) • a + 4 • b) := by abel
      _ = 0 := by rw [hr₇, h₁', h₂']; simp
  have hb : b = 0 := by
    calc
      b = 6 • (4 • b) - 23 • (a + b) + 23 • a := by abel
      _ = 0 := by rw [h₂', h₃', ha]; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m23Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₂₃` presentation equals its commutator subgroup. -/
theorem m23_isPerfect : Group.IsPerfect m23Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m23_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

/-- Every homomorphism from the transcribed `M₂₄` presentation to a commutative group is trivial. -/
theorem m24_hom_eq_one {G : Type*} [CommGroup G] (f : m24Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m24Presentation_transcribed] at h
  simp only [List.forall_mem_cons, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, Relator.toFreeGroup_comm,
    commutatorElement_def, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, h₃, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  have h₃' := congrArg Additive.ofMul h₃
  change 2 • a = 0 at h₁'
  change 3 • b = 0 at h₂'
  change 23 • (a + b) = 0 at h₃'
  -- The first three exponent-sum rows already span the full generator lattice.
  have ha : a = 0 := by
    calc
      a = 35 • (2 • a) + 23 • (3 • b) - 3 • (23 • (a + b)) := by abel
      _ = 0 := by rw [h₁', h₂', h₃']; simp
  have hb : b = 0 := by
    calc
      b = -23 • (2 • a) - 15 • (3 • b) + 2 • (23 • (a + b)) := by abel
      _ = 0 := by rw [h₁', h₂', h₃']; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m24Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₂₄` presentation equals its commutator subgroup. -/
theorem m24_isPerfect : Group.IsPerfect m24Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m24_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

end TauCeti.Sporadic.Mathieu
