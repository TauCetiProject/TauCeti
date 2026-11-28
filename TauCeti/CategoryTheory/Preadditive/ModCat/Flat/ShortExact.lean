/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Basic

import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-!
# Flatness in short exact sequences of modules over preadditive categories

If the last term of a short exact sequence is flat, the first term is flat if and only if
the middle term is flat. This is the equational form of Mitchell's Corollary 10.4b for
contravariant functors, using the flatness criterion of Oberst and Röhrl's Theorem 3.2 (4).
The argument works in independent object, morphism and value universes.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, Corollary 10.4b.
* U. Oberst and H. Röhrl, *Flat and coherent functors*, J. Algebra 14 (1970), 91–105,
  Theorem 3.2.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

section

variable {S : ShortComplex (ModCat.{w} C)}
  (hinj : ∀ X : C, Function.Injective (S.f.hom.app (op X)))
  (hsurj : ∀ X : C, Function.Surjective (S.g.hom.app (op X)))
  (hex : ∀ X : C, Function.Exact (S.f.hom.app (op X)) (S.g.hom.app (op X)))

include hinj hsurj hex in
private theorem flat_middle [S.X₁.Flat] [S.X₃.Flat] : S.X₂.Flat where
  isTrivialRelation {X n Y} β y h := by
    have hquot : ∑ j, S.X₃.obj.map (β j).op (S.g.hom.app (op (Y j)) (y j)) = 0 := by
      simpa only [map_sum, S.g.hom.naturality_apply, map_zero] using
        congrArg (S.g.hom.app (op X)) h
    obtain ⟨m, Z, z, α, hy, hα⟩ := isTrivialRelation_def.mp (Flat.isTrivialRelation β _ hquot)
    choose lift hlift using fun i ↦ hsurj (Z i) (z i)
    let y' (j : Fin n) := ∑ i, S.X₂.obj.map (α i j).op (lift i)
    have h' : S.X₂.IsTrivialRelation β y' :=
      isTrivialRelation_def.mpr ⟨m, Z, lift, α, fun _ ↦ rfl, hα⟩
    -- Remove the lifted trivial relation, leaving a relation in the kernel.
    have hker (j : Fin n) : S.g.hom.app (op (Y j)) (y j - y' j) = 0 := by
      simp only [map_sub, y', map_sum, S.g.hom.naturality_apply, hlift, hy j, sub_self]
    choose a ha using fun j ↦ (hex (Y j) _).1 (hker j)
    have hrel : ∑ j, S.X₁.obj.map (β j).op (a j) = 0 := by
      apply hinj X
      simp only [map_sum, S.f.hom.naturality_apply, ha, map_sub, Finset.sum_sub_distrib,
        h, h'.sum_eq_zero, sub_self, map_zero]
    obtain ⟨m', Z', a', α', ha', hα'⟩ :=
      isTrivialRelation_def.mp (Flat.isTrivialRelation β a hrel)
    let Witness := Σ W : C, S.X₂.obj.obj (op W) × (∀ j, Y j ⟶ W)
    let fromKernel (i : Fin m') : Witness := ⟨Z' i, S.f.hom.app (op (Z' i)) (a' i), α' i⟩
    let fromQuotient (i : Fin m) : Witness := ⟨Z i, lift i, α i⟩
    let witnesses := Fin.append fromKernel fromQuotient
    let eval (j : Fin n) (d : Witness) := S.X₂.obj.map (d.2.2 j).op d.2.1
    let annihilates (d : Witness) := ∑ j, β j ≫ d.2.2 j = 0
    refine isTrivialRelation_def.mpr
      ⟨m' + m, fun i ↦ (witnesses i).1, fun i ↦ (witnesses i).2.1,
        fun i ↦ (witnesses i).2.2, ?_, ?_⟩
    · intro j
      have hsum : y j - y' j = ∑ i, eval j (fromKernel i) := by
        simpa only [ha j, map_sum, S.f.hom.naturality_apply] using
          congrArg (S.f.hom.app (op (Y j))) (ha' j)
      calc
        y j = (∑ i, eval j (fromKernel i)) + ∑ i, eval j (fromQuotient i) :=
          sub_eq_iff_eq_add.mp hsum
        _ = ∑ i, eval j (witnesses i) := by
          simp only [Fin.sum_univ_add, witnesses, Fin.append_left, Fin.append_right]
    · refine Fin.addCases (motive := fun i ↦ annihilates (witnesses i)) ?_ ?_
      · simpa only [witnesses, Fin.append_left] using hα'
      · simpa only [witnesses, Fin.append_right] using hα

include hinj hsurj hex in
private theorem flat_left [S.X₂.Flat] [S.X₃.Flat] : S.X₁.Flat where
  isTrivialRelation {X n Y} β y h := by
    have hmid : ∑ j, S.X₂.obj.map (β j).op (S.f.hom.app (op (Y j)) (y j)) = 0 := by
      simpa only [map_sum, S.f.hom.naturality_apply, map_zero] using
        congrArg (S.f.hom.app (op X)) h
    obtain ⟨m, Z, z, α, hy, hα⟩ := isTrivialRelation_def.mp (Flat.isTrivialRelation β _ hmid)
    -- The images of the middle-term witnesses satisfy all the rows of α in the quotient.
    have hquot (j : Fin n) : ∑ i, S.X₃.obj.map (α i j).op (S.g.hom.app (op (Z i)) (z i)) = 0 := by
      simpa only [map_sum, S.g.hom.naturality_apply, (hex (Y j)).apply_apply_eq_zero] using
        (congrArg (S.g.hom.app (op (Y j))) (hy j)).symm
    obtain ⟨k, W, t, γ, hz, hγ⟩ :=
      Flat.exists_factorization_of_sum_eq_zero (fun j i ↦ α i j) _ hquot
    choose lift hlift using fun l ↦ hsurj (W l) (t l)
    let z' (i : Fin m) := ∑ l, S.X₂.obj.map (γ l i).op (lift l)
    have hzero (j : Fin n) : ∑ i, S.X₂.obj.map (α i j).op (z' i) = 0 :=
      (isTrivialRelation_def.mpr ⟨k, W, lift, γ, fun _ ↦ rfl, hγ j⟩ :
        S.X₂.IsTrivialRelation (fun i ↦ α i j) z').sum_eq_zero
    have hker (i : Fin m) : S.g.hom.app (op (Z i)) (z i - z' i) = 0 := by
      simp only [map_sub, z', map_sum, S.g.hom.naturality_apply, hlift, hz i, sub_self]
    choose a ha using fun i ↦ (hex (Z i) _).1 (hker i)
    refine isTrivialRelation_def.mpr ⟨m, Z, a, α, fun j ↦ hinj (Y j) ?_, hα⟩
    simp only [map_sum, S.f.hom.naturality_apply, ha, map_sub, Finset.sum_sub_distrib,
      hzero j, sub_zero, hy j]

end

/-- In a short exact sequence of modules over a preadditive category, if the last term is flat,
the middle term is flat if and only if the first term is flat. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.modCat_flat_iff
    {S : ShortComplex (ModCat.{w} C)} (hS : S.ShortExact) [S.X₃.Flat] : S.X₂.Flat ↔ S.X₁.Flat := by
  let : (additiveFunctor Cᵒᵖ AddCommGrpCat.{w}).IsClosedUnderFiniteLimits := {}
  let : (additiveFunctor Cᵒᵖ AddCommGrpCat.{w}).IsClosedUnderFiniteColimits := {}
  have h (X : C) := hS.map_of_exact
    ((additiveFunctor Cᵒᵖ AddCommGrpCat.{w}).ι ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op X))
  have hinj (X : C) : Function.Injective (S.f.hom.app (op X)) :=
    (AddCommGrpCat.mono_iff_injective _).1 (h X).mono_f
  have hsurj (X : C) : Function.Surjective (S.g.hom.app (op X)) :=
    (AddCommGrpCat.epi_iff_surjective _).1 (h X).epi_g
  have hex (X : C) : Function.Exact (S.f.hom.app (op X)) (S.g.hom.app (op X)) :=
    (ShortComplex.ab_exact_iff_function_exact _).1 (h X).exact
  exact ⟨fun _ ↦ flat_left hinj hsurj hex, fun _ ↦ flat_middle hinj hsurj hex⟩

end TauCeti.ModCat
