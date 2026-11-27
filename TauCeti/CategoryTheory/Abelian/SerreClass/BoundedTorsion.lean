/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.GroupTheory.Exponent
public import TauCeti.Algebra.Category.Grp.Preadditive
public import TauCeti.CategoryTheory.ObjectProperty.KilledBy

/-!
# Objects of bounded torsion

In a preadditive category, an object `Z` has *bounded torsion* when a single nonzero natural
number kills it: `e • 𝟙 Z = 0` for some `e ≠ 0`. This file shows that these objects form a Serre
class in every abelian category. The Serre localization of the category of sheaves of abelian
groups on a space at this class is the *isogeny category* of Chatzistamatiou–Rülling, in which
a map of sheaves becomes invertible exactly when its kernel and cokernel are killed by a nonzero
integer; Mathlib's `ObjectProperty.isZero_obj_iff` then says that a sheaf becomes zero there
exactly when it has bounded torsion. This is the rationalization used to state that higher
direct images of Witt vector sheaves vanish up to a uniform power of `p`.

Bounded torsion is stronger than torsion: on a point, the sheaf `⨁_{n ≥ 1} ℤ/pⁿ` is torsion,
hence zero after tensoring with `ℚ`, but no single integer kills it.

## Main definitions and results

* `CategoryTheory.ObjectProperty.isKilledBy_mul_of_exact`: in an exact sequence
  `X₁ → X₂ → X₃`, if `a` kills `X₁` and `b` kills `X₃`, then `a * b` kills `X₂`.
* `CategoryTheory.ObjectProperty.isBoundedTorsion`: the objects killed by a nonzero natural
  number, with its `IsSerreClass` instance in an abelian category.
* `CategoryTheory.ObjectProperty.isBoundedTorsion_iff_exists_isKilledBy_pow`: if every integer
  prime to a prime `p` acts on `Z` by an epimorphism (for instance, on sheaves of modules over
  Witt vectors of an `𝔽_p`-algebra), then `Z` has bounded torsion exactly when a power of `p`
  kills it.
* `AddCommGrpCat.prop_isBoundedTorsion_iff_exponentExists`: an abelian group has bounded torsion
  exactly when it has an exponent.
* `AddCommGrpCat.prop_isBoundedTorsion_iff_exists_pow_nsmul_eq_zero`: if every natural number
  prime to `p` acts surjectively on an abelian group, it has bounded torsion exactly when a power
  of `p` kills it.
* `CategoryTheory.Sheaf.prop_isBoundedTorsion_iff`: a sheaf of abelian groups has bounded torsion
  exactly when one nonzero natural number kills all of its sections.

## References

* A. Chatzistamatiou and K. Rülling, *Hodge–Witt cohomology and Witt-rational singularities*,
  Doc. Math. 17 (2012), §3.7.
* Y. Gongyo, Y. Nakamura and H. Tanaka, *Rational points on log Fano threefolds over a finite
  field*, J. Eur. Math. Soc. 21 (2019), §2.5 and Remark 2.17.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

/-- In an exact sequence `X₁ → X₂ → X₃`, if `a` kills `X₁` and `b` kills `X₃`, then `a * b`
kills `X₂`. -/
theorem isKilledBy_mul_of_exact {S : ShortComplex C} (hS : S.Exact)
    {a b : ℕ} (h₁ : isKilledBy C a S.X₁) (h₃ : isKilledBy C b S.X₃) :
    isKilledBy C (a * b) S.X₂ := by
  -- `b • 𝟙 X₂` lands in the cycles, which are a quotient of `X₁` and hence killed by `a`.
  have hb : (b • 𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Preadditive.nsmul_comp, Category.id_comp, ← Category.comp_id S.g,
      ← Preadditive.comp_nsmul, (prop_isKilledBy_iff b S.X₃).1 h₃, comp_zero]
  have := hS.hasHomology
  have := hS.epi_toCycles
  have hcycles : isKilledBy C a S.cycles := (isKilledBy C a).prop_of_epi S.toCycles h₁
  rw [prop_isKilledBy_iff, mul_comm, mul_nsmul, ← S.liftCycles_i _ hb, ← Preadditive.comp_nsmul,
    nsmul_eq_zero_of_isKilledBy hcycles, comp_zero]

variable (C) in
/-- The objects of *bounded torsion*: those killed by some nonzero natural number. -/
def isBoundedTorsion : ObjectProperty C := fun Z ↦ ∃ e : ℕ, e ≠ 0 ∧ isKilledBy C e Z

/-- An object has bounded torsion exactly when some nonzero natural number kills it. -/
lemma prop_isBoundedTorsion_iff_exists_isKilledBy (Z : C) :
    isBoundedTorsion C Z ↔ ∃ e : ℕ, e ≠ 0 ∧ isKilledBy C e Z :=
  Iff.rfl

/-- An object has bounded torsion exactly when `e • 𝟙 Z = 0` for some nonzero `e`. -/
@[simp]
lemma prop_isBoundedTorsion_iff (Z : C) :
    isBoundedTorsion C Z ↔ ∃ e : ℕ, e ≠ 0 ∧ e • 𝟙 Z = 0 := by
  simp only [prop_isBoundedTorsion_iff_exists_isKilledBy, prop_isKilledBy_iff]

/-- An object killed by a nonzero natural number has bounded torsion. -/
lemma isKilledBy_le_isBoundedTorsion {e : ℕ} (he : e ≠ 0) :
    isKilledBy C e ≤ isBoundedTorsion C :=
  fun _ hZ ↦ ⟨e, he, hZ⟩

/-- Zero objects have bounded torsion. -/
instance [HasZeroObject C] : (isBoundedTorsion C).ContainsZero :=
  ⟨_, isZero_zero C, 1, one_ne_zero, prop_of_isZero _ (isZero_zero C)⟩

/-- A subobject of an object of bounded torsion has bounded torsion. -/
instance : (isBoundedTorsion C).IsClosedUnderSubobjects where
  prop_of_mono f _ := fun ⟨e, he, hW⟩ ↦ ⟨e, he, (isKilledBy C e).prop_of_mono f hW⟩

/-- A quotient of an object of bounded torsion has bounded torsion. -/
instance : (isBoundedTorsion C).IsClosedUnderQuotients where
  prop_of_epi f _ := fun ⟨e, he, hZ⟩ ↦ ⟨e, he, (isKilledBy C e).prop_of_epi f hZ⟩

/-- An extension of objects of bounded torsion has bounded torsion. -/
instance : (isBoundedTorsion C).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS := fun ⟨a, ha, h₁⟩ ⟨b, hb, h₃⟩ ↦
    ⟨a * b, mul_ne_zero ha hb, isKilledBy_mul_of_exact hS.exact h₁ h₃⟩

/-- In an abelian category, the objects of bounded torsion form a Serre class. -/
instance {C : Type*} [Category* C] [Abelian C] : (isBoundedTorsion C).IsSerreClass where

/-- If every natural number prime to `p` acts on `Z` by an epimorphism, then `Z` has bounded
torsion exactly when some power of `p` kills it. -/
theorem isBoundedTorsion_iff_exists_isKilledBy_pow {p : ℕ} (hp : p.Prime) {Z : C}
    (h : ∀ m : ℕ, m.Coprime p → Epi (m • 𝟙 Z)) :
    isBoundedTorsion C Z ↔ ∃ n : ℕ, isKilledBy C (p ^ n) Z := by
  rw [prop_isBoundedTorsion_iff_exists_isKilledBy]
  refine ⟨fun ⟨e, he, hZ⟩ ↦ ⟨e.factorization p, ?_⟩,
    fun ⟨n, hZ⟩ ↦ ⟨p ^ n, pow_ne_zero n hp.ne_zero, hZ⟩⟩
  -- Split `e` as its `p`-part times a factor prime to `p`, which acts epimorphically.
  have := h _ (Nat.coprime_ordCompl hp he).symm
  rw [← Nat.ordProj_mul_ordCompl_eq_self e p, mul_comm] at hZ
  exact isKilledBy_of_mul_of_epi hZ

end Preadditive

section Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- An additive functor sends objects of bounded torsion to objects of bounded torsion. In
particular, every right derived functor of an additive functor does, since it is additive
(`CategoryTheory.Functor.additive_rightDerived` in
`TauCeti.CategoryTheory.Abelian.RightDerived`). -/
theorem isBoundedTorsion_le_inverseImage (F : C ⥤ D) [F.Additive] :
    isBoundedTorsion C ≤ (isBoundedTorsion D).inverseImage F :=
  fun X hX ↦ by
    obtain ⟨e, he, hX⟩ := (prop_isBoundedTorsion_iff_exists_isKilledBy X).1 hX
    exact (prop_isBoundedTorsion_iff_exists_isKilledBy (F.obj X)).2
      ⟨e, he, isKilledBy_le_inverseImage F e _ hX⟩

end Functor

end CategoryTheory.ObjectProperty

namespace AddCommGrpCat

open CategoryTheory.ObjectProperty

/-- An abelian group has bounded torsion exactly when it has an exponent. -/
theorem prop_isBoundedTorsion_iff_exponentExists (M : AddCommGrpCat) :
    isBoundedTorsion AddCommGrpCat M ↔ AddMonoid.ExponentExists M := by
  simp only [prop_isBoundedTorsion_iff, nsmul_id_eq_zero_iff, AddMonoid.ExponentExists,
    Nat.pos_iff_ne_zero]

/-- If multiplication by every natural number prime to a prime `p` is surjective on an abelian
group `M`, for instance when `M` is a module over a ring in which those numbers are units, then `M`
has bounded torsion exactly when a power of `p` kills every element. -/
theorem prop_isBoundedTorsion_iff_exists_pow_nsmul_eq_zero {p : ℕ} (hp : p.Prime)
    {M : AddCommGrpCat} (h : ∀ m : ℕ, m.Coprime p → Function.Surjective fun x : M ↦ m • x) :
    isBoundedTorsion AddCommGrpCat M ↔ ∃ n : ℕ, ∀ x : M, p ^ n • x = 0 := by
  rw [isBoundedTorsion_iff_exists_isKilledBy_pow hp fun m hm ↦ ?_]
  · simp only [prop_isKilledBy_iff, nsmul_id_eq_zero_iff]
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨x, rfl⟩ := h m hm y
    exact ⟨x, by simp⟩

end AddCommGrpCat

namespace CategoryTheory.Sheaf

open ObjectProperty

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- A natural number kills a sheaf exactly when it kills each of its sections. -/
theorem prop_isKilledBy_iff {A : Type*} [Category* A] [Preadditive A] (e : ℕ) (F : Sheaf J A) :
    isKilledBy (Sheaf J A) e F ↔ ∀ U, isKilledBy A e (F.obj.obj U) := by
  rw [← inverseImage_isKilledBy (sheafToPresheaf J A), prop_inverseImage_iff,
    prop_isKilledBy_functor_iff, ObjectProperty.ι_obj]

/-- A sheaf of abelian groups has bounded torsion exactly when one nonzero natural number
annihilates all of its sections. -/
theorem prop_isBoundedTorsion_iff (F : Sheaf J AddCommGrpCat) :
    isBoundedTorsion (Sheaf J AddCommGrpCat) F ↔
      ∃ e : ℕ, e ≠ 0 ∧ ∀ U (x : F.obj.obj U), e • x = 0 := by
  simp only [prop_isBoundedTorsion_iff_exists_isKilledBy, prop_isKilledBy_iff]
  simp only [ObjectProperty.prop_isKilledBy_iff, AddCommGrpCat.nsmul_id_eq_zero_iff]

end CategoryTheory.Sheaf
