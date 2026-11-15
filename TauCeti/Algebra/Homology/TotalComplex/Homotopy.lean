/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.Abel

/-!
# Homotopies on total complexes

A horizontal homotopy between bicomplex maps induces a homotopy between their total maps,
for any compatible total complex shapes. On bidegree `(p,q)` its component is the original
homotopy evaluated at `q`, multiplied by the horizontal totalization sign at `(c₁.prev p,q)`.
For integer-graded cochain bicomplexes this sign is one: with the native differential
`D = d₁ + (-1)^p d₂`, the vertical contributions cancel because the homotopy lowers `p`.

This applies, for example, to refinement prism homotopies in Čech double complexes and hence
shows that homotopic refinements act identically on the cohomology of their totals. Only the
existence of the coproducts defining the two totals is assumed; no unbounded product
totalization is involved.

The construction and its summandwise proof are adapted from Joël Riou's Mathlib construction
`HomologicalComplex.mapBifunctorMapHomotopy₁`, without requiring the bicomplexes to arise from
applying a bifunctor to two complexes.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex₂
open scoped ComplexShape

namespace Homotopy

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K L : HomologicalComplex₂ C c₁ c₂} {f g : K ⟶ L} (h : Homotopy f g)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [K.HasTotal c] [L.HasTotal c]

/-- The signed component of the total homotopy, extended by zero to all pairs of degrees. -/
private def totalHom (n m : J) : (K.total c).X n ⟶ (L.total c).X m :=
  K.totalDesc fun p q _ ↦ ComplexShape.ε₁ c₁ c₂ c (c₁.prev p, q) •
    ((h.hom p (c₁.prev p)).f q ≫ L.ιTotalOrZero c (c₁.prev p) q m)

@[reassoc]
private lemma ι_totalHom (p p' : I₁) (q : I₂) (n m : J)
    (hpq : ComplexShape.π c₁ c₂ c (p, q) = n) (hp : c₁.prev p = p') :
    K.ιTotal c p q n hpq ≫ totalHom h c n m =
      ComplexShape.ε₁ c₁ c₂ c (p', q) •
        ((h.hom p p').f q ≫ L.ιTotalOrZero c p' q m) := by
  subst hp
  simp [totalHom]

private lemma totalHom_zero (n m : J) (hnm : ¬ c.Rel m n) :
    totalHom h c n m = 0 := by
  refine total.hom_ext _ fun p q hpq ↦ ?_
  rw [ι_totalHom h c p _ q n m hpq rfl, comp_zero]
  by_cases hp : c₁.Rel (c₁.prev p) p
  · rw [L.ιTotalOrZero_eq_zero, comp_zero, smul_zero]
    intro hm
    exact hnm (by simpa only [hpq, hm] using ComplexShape.rel_π₁ c₂ c hp q)
  · simp [h.zero _ _ hp]

/-- The horizontal outgoing term of the original homotopy equation on a total summand. -/
private lemma totalHom_dNext (p : I₁) (q : I₂) (n : J)
    (hpq : ComplexShape.π c₁ c₂ c (p, q) = n) :
    (dNext p h.hom).f q ≫ L.ιTotal c p q n hpq =
      K.d₁ c p q (c.next n) ≫ totalHom h c (c.next n) n := by
  by_cases hp : c₁.Rel p (c₁.next p)
  · rw [dNext_eq _ hp, HomologicalComplex.comp_f,
      K.d₁_eq c hp q _ (by rw [← hpq, ComplexShape.next_π₁ c₂ c hp])]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [ι_totalHom h c _ p q _ n _ (c₁.prev_eq' hp)]
    simp [Linear.comp_units_smul, smul_smul, L.ιTotalOrZero_eq c p q n hpq]
  · simp [dNext_eq_zero _ _ hp, K.d₁_eq_zero c p q (c.next n) hp]

/-- The horizontal incoming term of the original homotopy equation on a total summand. -/
private lemma totalHom_prevD (p : I₁) (q : I₂) (n : J)
    (hpq : ComplexShape.π c₁ c₂ c (p, q) = n) :
    (prevD p h.hom).f q ≫ L.ιTotal c p q n hpq =
      K.ιTotal c p q n hpq ≫ totalHom h c n (c.prev n) ≫ L.D₁ c (c.prev n) n := by
  rw [ι_totalHom_assoc h c p _ q n _ hpq rfl]
  by_cases hp : c₁.Rel (c₁.prev p) p
  · rw [prevD_eq _ hp, HomologicalComplex.comp_f,
      L.ιTotalOrZero_eq c _ q _ (by rw [← ComplexShape.prev_π₁ c₂ c hp, hpq])]
    simp only [Linear.units_smul_comp, Category.assoc, ι_D₁]
    rw [L.d₁_eq c hp q n hpq]
    simp [Linear.comp_units_smul, smul_smul]
  · simp [prevD_eq_zero _ _ hp, h.zero _ _ hp]

/-- The two vertical contributions have opposite signs. -/
private lemma totalHom_vertical_of_rel {p p' : I₁} (hp : c₁.Rel p p')
    {q q' : I₂} (hq : c₂.Rel q q') (n : J)
    (hpq : ComplexShape.π c₁ c₂ c (p', q) = n) :
    ComplexShape.ε₁ c₁ c₂ c (p, q) • (h.hom p' p).f q ≫ L.d₂ c p q n =
      -(K.d₂ c p' q (c.next n) ≫ totalHom h c (c.next n) n) := by
  have hpq' : ComplexShape.π c₁ c₂ c (p, q') = n := by
    rw [← hpq, ← ComplexShape.next_π₂ c₁ c p hq, ComplexShape.next_π₁ c₂ c hp]
  rw [L.d₂_eq c p hq n hpq',
    K.d₂_eq c p' hq _ (by rw [← hpq, ComplexShape.next_π₂ c₁ c p' hq]),
    Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ι_totalHom h c _ p q' _ n _ (c₁.prev_eq' hp), L.ιTotalOrZero_eq c p q' n hpq']
  simp [Linear.comp_units_smul, smul_smul,
    ComplexShape.ε₁_ε₂ c hp hq, HomologicalComplex.Hom.comm_assoc]

private lemma totalHom_vertical (p : I₁) (q : I₂) (n : J)
    (hpq : ComplexShape.π c₁ c₂ c (p, q) = n) :
    K.ιTotal c p q n hpq ≫ totalHom h c n (c.prev n) ≫ L.D₂ c (c.prev n) n =
      -(K.d₂ c p q (c.next n) ≫ totalHom h c (c.next n) n) := by
  rw [ι_totalHom_assoc h c p _ q n _ hpq rfl]
  by_cases hp : c₁.Rel (c₁.prev p) p
  · rw [L.ιTotalOrZero_eq c _ q _ (by rw [← ComplexShape.prev_π₁ c₂ c hp, hpq]),
      Linear.units_smul_comp, Category.assoc, ι_D₂]
    by_cases hq : c₂.Rel q (c₂.next q)
    · exact totalHom_vertical_of_rel h c hp hq n hpq
    · simp [L.d₂_eq_zero c _ q n hq, K.d₂_eq_zero c p q (c.next n) hq]
  · simp only [h.zero _ _ hp, HomologicalComplex.zero_f, zero_comp, smul_zero, zero_eq_neg]
    by_cases hq : c₂.Rel q (c₂.next q)
    · rw [K.d₂_eq c p hq _ (by rw [← hpq, ComplexShape.next_π₂ c₁ c p hq]),
        Linear.units_smul_comp, Category.assoc, ι_totalHom h c _ _ _ _ _ _ rfl]
      simp [h.zero _ _ hp]
    · simp [K.d₂_eq_zero c p q (c.next n) hq]

private lemma totalHom_comm (n : J) :
    (total.map f c).f n =
      (K.total c).d n (c.next n) ≫ totalHom h c (c.next n) n +
        totalHom h c n (c.prev n) ≫ (L.total c).d (c.prev n) n +
          (total.map g c).f n := by
  refine total.hom_ext _ fun p q hpq ↦ ?_
  simp only [Preadditive.comp_add, ιTotal_map, total_d, Preadditive.add_comp,
    ι_D₁_assoc, ι_D₂_assoc]
  rw [congrArg (fun k ↦ k.f q) (h.comm p)]
  simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp, add_left_inj]
  rw [totalHom_dNext h c p q n hpq, totalHom_prevD h c p q n hpq,
    totalHom_vertical h c p q n hpq]
  abel

/-- A horizontal homotopy of bicomplex maps induces a homotopy of total maps, with the
horizontal totalization sign evaluated at the target bidegree. -/
def totalMap : Homotopy (total.map f c) (total.map g c) where
  hom := totalHom h c
  zero := totalHom_zero h c
  comm := totalHom_comm h c

/-- The total homotopy on a summand is the signed horizontal homotopy, extended by zero. -/
@[reassoc (attr := simp)]
lemma ι_totalMap_hom (p : I₁) (q : I₂) (n m : J)
    (hpq : ComplexShape.π c₁ c₂ c (p, q) = n) :
    K.ιTotal c p q n hpq ≫ (h.totalMap c).hom n m =
      ComplexShape.ε₁ c₁ c₂ c (c₁.prev p, q) •
        ((h.hom p (c₁.prev p)).f q ≫ L.ιTotalOrZero c (c₁.prev p) q m) := by
  rw [totalMap, ι_totalHom h c p _ q n m hpq rfl]

/-- For integer-graded cochain bicomplexes, the total homotopy has no extra sign. -/
-- The general summand formula already simplifies this left-hand side.
@[reassoc]
lemma ι_totalMap_hom_up_int
    {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    {f g : K ⟶ L} (h : Homotopy f g) (p q n : ℤ) (hpq : p + q = n) :
    K.ιTotal (ComplexShape.up ℤ) p q n hpq ≫
        (h.totalMap (ComplexShape.up ℤ)).hom n (n - 1) =
      (h.hom p (p - 1)).f q ≫
        L.ιTotal (ComplexShape.up ℤ) (p - 1) q (n - 1)
          (by omega : p - 1 + q = n - 1) := by
  have hp : (ComplexShape.up ℤ).prev p = p - 1 :=
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk (p - 1) p (by omega))
  rw [ι_totalMap_hom, hp, L.ιTotalOrZero_eq _ _ _ _ (by dsimp; omega)]
  simp [ComplexShape.ε₁, ComplexShape.ε₁_def]

end Homotopy

namespace HomotopyEquiv

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K L : HomologicalComplex₂ C c₁ c₂} (c : ComplexShape J)
  [TotalComplexShape c₁ c₂ c] [DecidableEq J] [K.HasTotal c] [L.HasTotal c]

/-- A horizontal homotopy equivalence of bicomplexes induces a homotopy equivalence of
native total complexes, without any boundedness assumption. -/
def totalMap (e : HomotopyEquiv K L) : HomotopyEquiv (K.total c) (L.total c) where
  hom := total.map e.hom c
  inv := total.map e.inv c
  homotopyHomInvId :=
    (Homotopy.ofEq (total.map_comp e.hom e.inv c).symm).trans
      ((e.homotopyHomInvId.totalMap c).trans (Homotopy.ofEq (total.map_id K c)))
  homotopyInvHomId :=
    (Homotopy.ofEq (total.map_comp e.inv e.hom c).symm).trans
      ((e.homotopyInvHomId.totalMap c).trans (Homotopy.ofEq (total.map_id L c)))

/-- The forward map of the total homotopy equivalence is the native total map. -/
@[simp]
lemma totalMap_hom (e : HomotopyEquiv K L) :
    (e.totalMap c).hom = total.map e.hom c :=
  (rfl)

/-- The inverse map of the total homotopy equivalence is the native total map of the inverse. -/
@[simp]
lemma totalMap_inv (e : HomotopyEquiv K L) :
    (e.totalMap c).inv = total.map e.inv c :=
  (rfl)

end HomotopyEquiv
