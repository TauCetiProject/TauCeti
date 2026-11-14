/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import TauCeti.Algebra.Homology.Homotopy

/-!
# Chain maps from a projective object placed in one degree

Let `P` be a projective object of an abelian category, placed in degree `n` of a cochain complex,
and let `L` be any cochain complex. Chain maps from `P` placed in degree `n` to `L` are determined
up to homotopy by their effect on `Hⁿ`:

* every morphism `P ⟶ Hⁿ(L)` is the cohomology of such a chain map
  (`CochainComplex.exists_homologyMap_eq_of_projective`);
* such a chain map which vanishes on `Hⁿ` is null-homotopic
  (`CochainComplex.nonempty_homotopy_zero_of_homologyMap_eq_zero`).

Both statements lift along the epimorphisms `Zⁿ(L) ⟶ Hⁿ(L)` and `Lⁿ⁻¹ ⟶ Bⁿ(L)` from the
projective `P`. No boundedness of `L` is needed.
-/

public section

open CategoryTheory Limits HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {P : C} [Projective P]
  {L : CochainComplex C ℤ} {n : ℤ}

/-- Every morphism from a projective object `P` to `Hⁿ(L)` is the cohomology of a chain map from
`P` placed in degree `n` to `L`, up to the identification `Hⁿ(P[-n]) ≅ P`. -/
lemma exists_homologyMap_eq_of_projective (α : P ⟶ L.homology n) :
    ∃ g : (singleFunctor C n).obj P ⟶ L,
      homologyMap g n = (singleObjHomologySelfIso _ n P).hom ≫ α := by
  obtain ⟨β, hβ⟩ : ∃ β, β ≫ L.homologyπ n = α :=
    ⟨Projective.factorThru α (L.homologyπ n), Projective.factorThru_comp _ _⟩
  refine ⟨mkHomFromSingle (β ≫ L.iCycles n) (by rintro k rfl; simp), ?_⟩
  have hc : cyclesMap (mkHomFromSingle (β ≫ L.iCycles n) (by rintro k rfl; simp)) n =
      (singleObjCyclesSelfIso _ n P).hom ≫ β := by
    rw [← cancel_mono (L.iCycles n), cyclesMap_i, mkHomFromSingle_f, singleObjCyclesSelfIso_hom]
    simp
  rw [← cancel_epi (((single C _ n).obj P).homologyπ n), homologyπ_naturality, hc,
    homologyπ_singleObjHomologySelfIso_hom_assoc, Category.assoc, hβ]

/-- A chain map from a projective object `P` placed in degree `n` which vanishes on `Hⁿ` is
null-homotopic. -/
lemma nonempty_homotopy_zero_of_homologyMap_eq_zero
    (g : (singleFunctor C n).obj P ⟶ L) (hg : homologyMap g n = 0) :
    Nonempty (Homotopy g 0) := by
  -- `g` is given by `γ : P ⟶ Zⁿ(L)`, whose image in `Hⁿ(L)` vanishes.
  let γ : P ⟶ L.cycles n :=
    L.liftCycles ((singleObjXSelf _ n P).inv ≫ g.f n) (n + 1) (by simp) (by simp)
  have hγ : γ ≫ L.homologyπ n = 0 := by
    have h := homologyπ_naturality g n
    rw [hg, comp_zero] at h
    have hc : cyclesMap g n = (singleObjCyclesSelfIso _ n P).hom ≫ γ := by
      rw [← cancel_mono (L.iCycles n), cyclesMap_i, singleObjCyclesSelfIso_hom]
      simp [γ]
    rw [hc, Category.assoc] at h
    rw [← cancel_epi (singleObjCyclesSelfIso _ n P).hom, comp_zero]
    exact h.symm
  -- So `γ` lifts along `Lⁿ⁻¹ ⟶ Zⁿ(L)`, which gives a null-homotopy of `g`.
  have hex : (ShortComplex.mk (L.toCycles (n - 1) n) (L.homologyπ n)
      (L.toCycles_comp_homologyπ _ _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (L.homologyIsCokernel (n - 1) n (by simp))
  refine (nonempty_homotopy_zero_iff_of_single L (sub_add_cancel n 1) g).2
    ⟨hex.liftFromProjective γ hγ, ?_⟩
  have := hex.liftFromProjective_comp γ hγ
  dsimp at this
  rw [← L.toCycles_i, ← Category.assoc, this]
  simp [γ]

end CochainComplex
