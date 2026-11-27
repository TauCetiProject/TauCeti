/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.SheafH.Basic

/-!
# Boundaries of torsor classes along abelian extensions

Let `0 → E.X₁ → E.X₂ → E.X₃ → 0` be a short exact sequence of abelian sheaves on a site. A torsor
under `E.X₃`, viewed as a sheaf of groups, has a boundary in `H²(E.X₁)`: identify its class with
a class in `H¹(E.X₃)` by `CategoryTheory.Sheaf.NonabelianH1.equivSheafH` (Stacks, Lemma 21.4.3
(03AJ)) and apply the connecting map `δ : H¹(E.X₃) → H²(E.X₁)` of the long exact cohomology
sequence (Stacks, Section 21.3 (071J)). The boundary vanishes exactly on the classes of torsors
obtained from `E.X₂`-torsors by extending the structure group along `E.X₂ → E.X₃`, and it is
natural in morphisms of short exact sequences.

Only abelian middle sheaves are treated here; boundaries along general central extensions of
sheaves of groups are not.

## Main declarations

* `CategoryTheory.Sheaf.NonabelianH1.abelianBoundary hE`: the boundary of a torsor class.
* `CategoryTheory.Sheaf.NonabelianH1.abelianBoundary_eq_zero_iff`: the boundary vanishes exactly
  on the classes that lift to torsor classes of the middle sheaf.
* `CategoryTheory.Sheaf.NonabelianH1.abelianBoundary_naturality`: compatibility with a morphism
  of short exact sequences.
* `CategoryTheory.Sheaf.NonabelianH1.abelianBoundary_eq_zero_of_isSplitEpi`: the boundary vanishes
  when the projection is a split epimorphism.

## References

* [The Stacks project, Section 21.3 (071J)](https://stacks.math.columbia.edu/tag/071J).
* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG).
-/

public noncomputable section

open CategoryTheory

universe w' w v u

namespace CategoryTheory.Sheaf.NonabelianH1

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- The boundary in `H²(E.X₁)` of a torsor class of `E.X₃`, for a short exact sequence
`0 → E.X₁ → E.X₂ → E.X₃ → 0` of abelian sheaves: the connecting map `δ : H¹(E.X₃) → H²(E.X₁)`
applied to the class in `H¹(E.X₃)` corresponding to the torsor under `equivSheafH`. -/
def abelianBoundary {E : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hE : E.ShortExact)
    (x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj E.X₃)) : H E.X₁ 2 :=
  H.δ hE 1 2 rfl (equivSheafH E.X₃ x)

variable {E : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hE : E.ShortExact)

/-- The boundary of a torsor class is the connecting map of sheaf cohomology applied to its
class in `H¹`. -/
lemma abelianBoundary_def (x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj E.X₃)) :
    abelianBoundary hE x = H.δ hE 1 2 rfl (equivSheafH E.X₃ x) :=
  (rfl)

/-- The class of the trivial torsor has zero boundary. -/
@[simp]
lemma abelianBoundary_one : abelianBoundary hE 1 = 0 := by
  rw [abelianBoundary_def, equivSheafH_one, map_zero]

/-- The boundary of the class corresponding to `z ∈ H¹(E.X₃)` is `δ z`. -/
@[simp]
lemma abelianBoundary_equivSheafH_symm (z : H E.X₃ 1) :
    abelianBoundary hE ((equivSheafH E.X₃).symm z) = H.δ hE 1 2 rfl z := by
  rw [abelianBoundary_def, Equiv.apply_symm_apply]

/-- If the projection `E.X₂ → E.X₃` is a split epimorphism, every torsor class of `E.X₃` has zero
boundary. -/
@[simp]
theorem abelianBoundary_eq_zero_of_isSplitEpi [IsSplitEpi E.g]
    (x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj E.X₃)) : abelianBoundary hE x = 0 := by
  rw [abelianBoundary_def]
  refine (H.exact_map_δ hE 1 2 rfl _).2 ⟨H.map (section_ E.g) 1 (equivSheafH E.X₃ x), ?_⟩
  rw [← H.map_comp_apply, IsSplitEpi.id, H.map_id_apply]

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- A torsor class of `E.X₃` has zero boundary if and only if it is obtained from a torsor class
of `E.X₂` by extending the structure group along `E.X₂ → E.X₃`. -/
theorem abelianBoundary_eq_zero_iff (x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj E.X₃)) :
    abelianBoundary hE x = 0 ↔ x ∈ Set.range (map ((abelianSheafToGrpSheaf J).map E.g)) := by
  rw [abelianBoundary_def, H.exact_map_δ hE 1 2 rfl]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(equivSheafH E.X₂).symm y, (equivSheafH E.X₃).injective ?_⟩
    rw [equivSheafH_map, Equiv.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨equivSheafH E.X₂ y, (equivSheafH_map _ _).symm⟩

/-- The boundary of the class of a torsor obtained from an `E.X₂`-torsor is zero. -/
@[simp]
lemma abelianBoundary_map_g (y : NonabelianH1 ((abelianSheafToGrpSheaf J).obj E.X₂)) :
    abelianBoundary hE (map ((abelianSheafToGrpSheaf J).map E.g) y) = 0 :=
  (abelianBoundary_eq_zero_iff hE _).2 ⟨y, rfl⟩

/-- The boundary is natural in morphisms of short exact sequences: for `φ : E ⟶ E'`, the
boundary of the image of a torsor class along `φ.τ₃` is the image under `φ.τ₁` of its
boundary. -/
theorem abelianBoundary_naturality {E' : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hE' : E'.ShortExact) (φ : E ⟶ E') (x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj E.X₃)) :
    abelianBoundary hE' (map ((abelianSheafToGrpSheaf J).map φ.τ₃) x) =
      H.map φ.τ₁ 2 (abelianBoundary hE x) := by
  rw [abelianBoundary_def, abelianBoundary_def, equivSheafH_map,
    H.δ_naturality 1 2 rfl hE hE']

end CategoryTheory.Sheaf.NonabelianH1
