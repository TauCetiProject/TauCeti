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
# Homotopies on total cochain complexes

A homotopy between morphisms of cochain complexes of cochain complexes induces a homotopy
between the morphisms of their total complexes. With the native differential
`D = d₁ + (-1)^p d₂`, the induced homotopy on the summand in bidegree `(p,q)` is the original
homotopy in horizontal degree `p`, evaluated in vertical degree `q`. There is no extra sign:
the vertical contributions cancel because the homotopy lowers `p` by one.

This applies, for example, to refinement prism homotopies in Čech double complexes and hence
shows that homotopic refinements act identically on the cohomology of their totals. Only the
existence of the coproducts defining the two totals is assumed; no unbounded product
totalization is involved.

The construction follows the summandwise method of Mathlib's
`HomologicalComplex.mapBifunctorMapHomotopy₁`, without requiring the bicomplexes to arise from
applying a bifunctor to two complexes.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex₂
open scoped ComplexShape

namespace Homotopy

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
  {f g : K ⟶ L} (h : Homotopy f g)

/-- The component of the induced total homotopy, extended by zero away from degree minus one. -/
private def totalHom (n m : ℤ) :
    (K.total (ComplexShape.up ℤ)).X n ⟶ (L.total (ComplexShape.up ℤ)).X m :=
  K.totalDesc fun p q _ ↦ (h.hom p (p - 1)).f q ≫
    L.ιTotalOrZero (ComplexShape.up ℤ) (p - 1) q m

@[reassoc]
private lemma ι_totalHom (p q n m : ℤ) (hpq : p + q = n) :
    K.ιTotal (ComplexShape.up ℤ) p q n hpq ≫ totalHom h n m =
      (h.hom p (p - 1)).f q ≫ L.ιTotalOrZero (ComplexShape.up ℤ) (p - 1) q m := by
  simp [totalHom]

private lemma totalHom_zero (n m : ℤ) (hnm : ¬ (ComplexShape.up ℤ).Rel m n) :
    totalHom h n m = 0 := by
  refine total.hom_ext _ fun p q hpq ↦ ?_
  rw [ι_totalHom, L.ιTotalOrZero_eq_zero, comp_zero, comp_zero]
  have hpq' : p + q = n := hpq
  have hnm' : m + 1 ≠ n := hnm
  have : p - 1 + q ≠ m := by omega
  exact this

private lemma totalHom_comm (n : ℤ) :
    (total.map f (ComplexShape.up ℤ)).f n =
      (K.total (ComplexShape.up ℤ)).d n (n + 1) ≫ totalHom h (n + 1) n +
        totalHom h n (n - 1) ≫ (L.total (ComplexShape.up ℤ)).d (n - 1) n +
          (total.map g (ComplexShape.up ℤ)).f n := by
  refine total.hom_ext _ fun p q hpq ↦ ?_
  have hpq' : p + q = n := hpq
  have h₁ : (p + 1) + q = n + 1 := by omega
  have h₂ : p + (q + 1) = n + 1 := by omega
  have h₃ : (p - 1) + q = n - 1 := by omega
  have h₄ : (p - 1) + (q + 1) = n := by omega
  simp only [Preadditive.comp_add, ιTotal_map, total_d, Preadditive.add_comp,
    ι_D₁_assoc, ι_D₂_assoc]
  rw [K.d₁_eq _ (ComplexShape.up_mk p (p + 1) rfl) q _ h₁,
    K.d₂_eq _ p (ComplexShape.up_mk q (q + 1) rfl) _ h₂,
    ι_totalHom_assoc]
  simp only [ComplexShape.ε₁, Linear.units_smul_comp, Category.assoc,
    ι_totalHom_assoc, L.ιTotalOrZero_eq (ComplexShape.up ℤ) (p - 1) q (n - 1) h₃,
    ι_D₁, ι_D₂]
  rw [L.d₁_eq _ (ComplexShape.up_mk (p - 1) p (by omega)) q _ hpq',
    L.d₂_eq _ (p - 1) (ComplexShape.up_mk q (q + 1) rfl) _ h₄]
  simp only [ComplexShape.ε₁, ComplexShape.ε₂, Linear.comp_units_smul, ι_totalHom,
    L.ιTotalOrZero_eq (ComplexShape.up ℤ) (p - 1) (q + 1) n h₄]
  have hc := congrArg (fun k ↦ k.f q) (h.comm p)
  rw [dNext_eq _ (ComplexShape.up_mk p (p + 1) rfl),
    prevD_eq _ (ComplexShape.up_mk (p - 1) p (by omega))] at hc
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] at hc
  rw [hc]
  simp only [Preadditive.add_comp, Category.assoc]
  have hs : (p - 1).negOnePow = -p.negOnePow := by
    simp [Int.negOnePow_sub]
  have hp : p + 1 - 1 = p := by omega
  -- The two vertical terms have opposite signs, since the homotopy lowers the first degree.
  simp only [ComplexShape.ε₁_def, one_smul, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
    HomologicalComplex.Hom.comm_assoc, add_left_inj]
  simp only [hs, Units.neg_smul]
  -- The index in the component of `h.hom` is hidden behind the bicomplex wrappers;
  -- `erw` exposes those wrappers to replace `(p + 1) - 1` by `p`.
  erw [hp, L.ιTotalOrZero_eq (ComplexShape.up ℤ) p q n hpq']
  abel

/-- A homotopy of bicomplex maps induces a homotopy of total maps. Its component on bidegree
`(p,q)` is the degree-`q` component of the original horizontal homotopy, with no extra sign. -/
def totalMap : Homotopy (total.map f (ComplexShape.up ℤ))
    (total.map g (ComplexShape.up ℤ)) where
  hom := totalHom h
  zero := totalHom_zero h
  comm n := by
    simpa only [dNext_eq _ (ComplexShape.up_mk n (n + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk (n - 1) n (by omega))] using
      totalHom_comm h n

/-- The total homotopy on a summand of bidegree `(p,q)` is the original homotopy evaluated in
vertical degree `q`. This formula fixes its sign. -/
@[reassoc (attr := simp)]
lemma ι_totalMap_hom (p q n : ℤ) (hpq : p + q = n) :
    K.ιTotal (ComplexShape.up ℤ) p q n hpq ≫ (h.totalMap.hom n (n - 1)) =
      (h.hom p (p - 1)).f q ≫
        L.ιTotal (ComplexShape.up ℤ) (p - 1) q (n - 1)
          (by omega : p - 1 + q = n - 1) := by
  rw [totalMap, ι_totalHom, L.ιTotalOrZero_eq]

end Homotopy

namespace HomotopyEquiv

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]

/-- A horizontal homotopy equivalence of cochain bicomplexes induces a homotopy equivalence
of their total complexes, without requiring either bicomplex to be bounded. -/
def totalMap (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.total (ComplexShape.up ℤ)) (L.total (ComplexShape.up ℤ)) where
  hom := total.map e.hom _
  inv := total.map e.inv _
  homotopyHomInvId :=
    (Homotopy.ofEq (total.map_comp e.hom e.inv _).symm).trans
      (e.homotopyHomInvId.totalMap.trans (Homotopy.ofEq (total.map_id K _)))
  homotopyInvHomId :=
    (Homotopy.ofEq (total.map_comp e.inv e.hom _).symm).trans
      (e.homotopyInvHomId.totalMap.trans (Homotopy.ofEq (total.map_id L _)))

/-- The forward map of the total homotopy equivalence is the native total map. -/
@[simp]
lemma totalMap_hom (e : HomotopyEquiv K L) :
    e.totalMap.hom = total.map e.hom (ComplexShape.up ℤ) :=
  (rfl)

/-- The inverse map of the total homotopy equivalence is the native total map of the inverse. -/
@[simp]
lemma totalMap_inv (e : HomotopyEquiv K L) :
    e.totalMap.inv = total.map e.inv (ComplexShape.up ℤ) :=
  (rfl)

end HomotopyEquiv
