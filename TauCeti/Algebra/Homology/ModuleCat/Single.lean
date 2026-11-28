/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Single complexes of modules on a directed union of submodules

Let `N i` be a directed family of submodules of a module `B` with `⨆ i, N i = ⊤`. Then every
element of every term of the single complex `B[j]` with `B` in degree `j` comes from the single
complex `(N i)[j]` for some `i` (`HomologicalComplex.exists_single_map_subtype_f_apply_eq`).

For a complex shape on `ℤ`, the identification `HomologicalComplex.singleObjXSelf` of the term of
degree `0` of `A[0]` with a module `A` is the identity on elements
(`HomologicalComplex.singleObjXSelf_inv_apply`).

For a module `X`, the identification of `X` with the degree `0` cycles of the cochain complex
`X[0]` sends an element `x` to the cycle `x` (`CochainComplex.iCycles_singleObjCyclesSelfIso_inv`).
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι' : Type*} [DecidableEq ι'] (c : ComplexShape ι')
  {ι : Type*} [Nonempty ι] {B : ModuleCat R} (N : ι → Submodule R B)

/-- For a directed family of submodules `N i` exhausting `B`, every element of a term of the
single complex `B[j]` comes from `(N i)[j]` for some `i`. -/
lemma exists_single_map_subtype_f_apply_eq (j : ι') (hN : Directed (· ≤ ·) N)
    (htop : ⨆ i, N i = ⊤) (k : ι') (y : ((single (ModuleCat R) c j).obj B).X k) :
    ∃ i y', ((single (ModuleCat R) c j).map (X := ModuleCat.of R (N i)) (Y := B)
      (ModuleCat.ofHom (N i).subtype)).f k y' = y := by
  by_cases hk : k = j
  · subst hk
    have hy : (singleObjXSelf c k B).hom y ∈ ⨆ i, N i := htop ▸ Submodule.mem_top
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed N hN).1 hy
    refine ⟨i, (singleObjXSelf c k (ModuleCat.of R (N i))).inv ⟨_, hi⟩, ?_⟩
    rw [single_map_f_self]
    simp
  · have := ModuleCat.subsingleton_of_isZero (isZero_single_obj_X c j B k hk)
    exact ⟨Classical.arbitrary ι, 0, Subsingleton.elim _ _⟩

end HomologicalComplex

namespace HomologicalComplex

variable {R : Type*} [Ring R]

/-- For every complex shape on `ℤ`, the cochain shape `up ℤ` as well as the chain shape `down ℤ`,
the identification `singleObjXSelf` of the term of degree `0` of the single complex on a module
`A` with `A` is the identity on elements: by definition of `single`, that term is `A` itself.
The degree is the numeral `0` because for a variable degree `j` the decision `j = j` inside
`single` does not reduce, so `a` is not an element of that term by definition. It is not a
`simp` lemma: the degree-zero lemmas of units such as `TauCeti.linearHomComplexUnit_f_zero_apply`
are stated on `(singleObjXSelf _ 0 _).inv r`, which it would rewrite. -/
lemma singleObjXSelf_inv_apply (c : ComplexShape ℤ) (A : ModuleCat R) (a : A) :
    (singleObjXSelf c 0 A).inv a = a :=
  (rfl)

end HomologicalComplex

namespace CochainComplex

variable {R : Type*} [Ring R]

/-- The degree `0` cycle of the single cochain complex `X[0]` corresponding to an element `x` of a
module `X` is `x` itself. -/
lemma iCycles_singleObjCyclesSelfIso_inv (X : ModuleCat R) (x : X) :
    ((single₀ (ModuleCat R)).obj X).iCycles 0
        ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 X).inv x) = x := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles,
    single₀ObjXSelf, Iso.refl_inv]
  exact ConcreteCategory.id_apply x

end CochainComplex
