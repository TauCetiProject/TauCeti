/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Shift
public import TauCeti.CategoryTheory.DG.CochainComplex.Basic
public import TauCeti.CategoryTheory.DG.ShiftClosure.Basic

/-!
# Formal shifts of cochain complexes are cochain shifts

Cochain complexes in an `R`-linear preadditive category form a differential graded category, and
so do the formal shifts `K[r]` of its shift closure `TauCeti.DGShiftClosure`.  This file
evaluates the formal shifts: it constructs the DG functor
`TauCeti.DGShiftClosure.toCochainComplex` sending `K[r]` to Mathlib's shifted complex `K⟦r⟧`,
and proves it is an isomorphism on Hom complexes.

On morphisms it is the normalized identification `Hom(K, L)[s - r] ≅ Hom(K⟦r⟧, L⟦s⟧)`: a cochain
`z` of degree `p + s - r` from `K` to `L` goes to the cochain of degree `p` from `K⟦r⟧` to
`L⟦s⟧` whose component `K⟦r⟧^i ⟶ L⟦s⟧^j` is `(-1)^(r * p)` times the component
`K^(i + r) ⟶ L^(j + s)` of `z` (`TauCeti.DGShiftClosure.shiftCochainEquiv_v`).  That this is a
DG functor is a check of every sign in `TauCeti/CategoryTheory/DG/ShiftClosure/Basic.lean`
against Mathlib's shift: the shift closure differential `(-1)^(s - r) d` matches the differential
`δ` of cochains between shifted complexes, and the shift closure composition sign
`(-1)^((t - s) * (p + s - r))` matches the Koszul-signed composition of cochains.

The identification is the general normalized identification of cochains between shifted
complexes, `TauCeti.cochainShiftLinearEquiv`, precomposed with the defining identification
`TauCeti.DGShiftClosure.dgHomEquiv` of the Hom complexes of the shift closure.

## Main definitions

* `TauCeti.DGShiftClosure.shiftCochainEquiv`: the normalized identification
  `Hom(K, L)[s - r] ≅ Hom(K⟦r⟧, L⟦s⟧)` in each degree.
* `TauCeti.DGShiftClosure.toCochainComplex`: the DG functor `K[r] ↦ K⟦r⟧`.

## Main results

* `TauCeti.DGShiftClosure.shiftCochainEquiv_v`: the identification multiplies the underlying
  cochain by `(-1)^(r * p)`.
* `TauCeti.DGShiftClosure.isIso_toCochainComplex_map`: `K[r] ↦ K⟦r⟧` is an isomorphism on Hom
  complexes.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory CochainComplex.HomComplex

namespace TauCeti

namespace DGShiftClosure

universe v u

variable (R : Type v) [CommRing R] {V : Type u} [Category.{v} V] [Preadditive V] [Linear R V]

/-- The **normalized identification** `Hom(K, L)[s - r] ≅ Hom(K⟦r⟧, L⟦s⟧)` in degree `n`: a
morphism `K[r] ⟶ L[s]` of degree `n` in the shift closure, that is, a cochain `z` of degree
`n + (s - r)` from `K` to `L`, goes to the cochain from `K⟦r⟧` to `L⟦s⟧` with components
`(-1)^(r * n) • z^(i + r, j + s)`. -/
noncomputable def shiftCochainEquiv (X Y : DGShiftClosure (CochainComplex V ℤ)) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n (X.obj⟦X.shift⟧) (Y.obj⟦Y.shift⟧) :=
  (dgHomEquiv R X Y n).trans (cochainShiftLinearEquiv R X.obj Y.obj X.shift Y.shift n)

/-- The normalized identification multiplies the underlying cochain by `(-1)^(r * n)`: its
component `K⟦r⟧^i ⟶ L⟦s⟧^j` is `(-1)^(r * n)` times the component `K^(i + r) ⟶ L^(j + s)`. -/
@[simp]
theorem shiftCochainEquiv_v {X Y : DGShiftClosure (CochainComplex V ℤ)} {n : ℤ}
    (f : DGHom R n X Y) (i j : ℤ) (hij : i + n = j) :
    (shiftCochainEquiv R X Y n f : Cochain (X.obj⟦X.shift⟧) (Y.obj⟦Y.shift⟧) n).v i j hij =
      (X.shift * n).negOnePow • (dgHomEquiv R X Y n f :
        Cochain X.obj Y.obj (n + (Y.shift - X.shift))).v (i + X.shift) (j + Y.shift)
          (by omega) :=
  cochainShiftLinearEquiv_v R _ _ _ _ _ _ i j hij

private theorem δ_shiftCochainEquiv {X Y : DGShiftClosure (CochainComplex V ℤ)} {n : ℤ}
    (f : DGHom R n X Y) :
    (shiftCochainEquiv R X Y (n + 1) (dgDifferential R n f) :
        Cochain (X.obj⟦X.shift⟧) (Y.obj⟦Y.shift⟧) (n + 1)) =
      δ n (n + 1) (shiftCochainEquiv R X Y n f : Cochain (X.obj⟦X.shift⟧) (Y.obj⟦Y.shift⟧) n) :=
  (congrArg (cochainShiftLinearEquiv R X.obj Y.obj X.shift Y.shift (n + 1))
    (dgHomEquiv_dgDifferential R n f)).trans
      (δ_cochainShiftLinearEquiv R _ _ _ _ _ _ rfl _).symm

/-- The DG functor `K[r] ↦ K⟦r⟧` evaluating the formal shifts of cochain complexes, acting on
morphisms by the normalized identification `TauCeti.DGShiftClosure.shiftCochainEquiv`. -/
-- The body is exposed so that `(toCochainComplex R).obj X` is definitionally `X.obj⟦X.shift⟧`, as
-- for `CategoryTheory.EnrichedFunctor.ofDGMap`.
@[expose]
noncomputable def toCochainComplex :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (DGShiftClosure (CochainComplex V ℤ))
      (CochainComplex V ℤ) :=
  EnrichedFunctor.ofDGMap (fun X ↦ X.obj⟦X.shift⟧)
    (fun {X Y} n ↦ (shiftCochainEquiv R X Y n).toLinearMap)
    (fun {X Y} n f ↦ by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, dgDifferential_linearHomComplex]
      exact δ_shiftCochainEquiv R f)
    (fun X ↦ by
      rw [LinearEquiv.coe_coe, dgId_linearHomComplex]
      refine Cochain.ext _ _ fun i j hij ↦ ?_
      obtain rfl : j = i := by omega
      rw [shiftCochainEquiv_v, dgHomEquiv_dgId, xIsoOfEq_hom_v, dgId_linearHomComplex]
      simp)
    (fun {X Y Z p q n} f g h ↦ by
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.coe_coe]
      refine Cochain.ext _ _ fun i j hij ↦ ?_
      rw [shiftCochainEquiv_v, dgHomEquiv_dgComp]
      refine (congrArg _ (Cochain.units_smul_v _ _ _ _ _)).trans ?_
      rw [dgComp_v R _ _ _ (i + X.shift) (i + p + Y.shift) (j + Z.shift) (by omega) (by omega),
        dgComp_v R _ _ h i (i + p) j rfl (by omega), shiftCochainEquiv_v, shiftCochainEquiv_v]
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add]
      congr 1
      rw [Int.negOnePow_eq_iff]
      subst h
      exact ⟨(Z.shift - Y.shift) * (p + (Y.shift - X.shift)), by ring⟩)

/-- The formal shift `K[r]` goes to the shifted complex `K⟦r⟧`. -/
@[simp]
theorem toCochainComplex_obj (X : DGShiftClosure (CochainComplex V ℤ)) :
    (toCochainComplex R).obj X = X.obj⟦X.shift⟧ :=
  rfl

/-- The functor `K[r] ↦ K⟦r⟧` acts on morphisms by the normalized identification. -/
theorem dgMap_toCochainComplex {X Y : DGShiftClosure (CochainComplex V ℤ)} {n : ℤ}
    (f : DGHom R n X Y) : (toCochainComplex R).dgMap n f = shiftCochainEquiv R X Y n f :=
  (EnrichedFunctor.dgMap_apply _ f).trans rfl

/-- **Formal shifts of cochain complexes are cochain shifts**: the DG functor `K[r] ↦ K⟦r⟧` is
an isomorphism on Hom complexes, so the shift-closure signs agree with Mathlib's cochain
shifts. -/
instance isIso_toCochainComplex_map (X Y : DGShiftClosure (CochainComplex V ℤ)) :
    IsIso ((toCochainComplex R).map X Y) :=
  have (n : ℤ) : IsIso (((toCochainComplex R).map X Y).f n) :=
    (shiftCochainEquiv R X Y n).toModuleIso.isIso_hom
  HomologicalComplex.Hom.isIso_of_components _

end DGShiftClosure

end TauCeti
