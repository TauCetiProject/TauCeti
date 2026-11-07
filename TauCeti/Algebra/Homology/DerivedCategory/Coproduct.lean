/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.Algebra.Homology.Homotopy

/-!
# Maps out of a coproduct placed in one degree

Let `C` be an abelian category with K-injective resolutions, `N` an object of its derived category
and `(Xᵢ)` a family of objects of `C` with a coproduct `∐ Xᵢ`. If every map from each `Xᵢ` placed
in degree `n` to `N` vanishes, then so does every map from `∐ Xᵢ` placed in degree `n`
(`DerivedCategory.singleFunctor_hom_eq_zero_of_isColimit`). No exactness of coproducts in `C` is
assumed.

Represent `N` by a K-injective complex `L`. Maps from `X` placed in degree `n` to `L` in the
derived category are homotopy classes of chain maps, that is, maps `X ⟶ Lⁿ` killed by the
differential, modulo those factoring through the differential `Lⁿ⁻¹ ⟶ Lⁿ`
(`CochainComplex.nonempty_homotopy_zero_iff_of_single`). A factorization through the differential
can be chosen on each summand and glued along the coproduct.
-/

public section

noncomputable section

open CategoryTheory Limits DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [TauCeti.HasKInjectiveResolutions C]

namespace DerivedCategory

open CochainComplex in
/-- If every map from each `Xᵢ` placed in degree `n` to `N` vanishes, then so does every map from
their coproduct placed in degree `n`. -/
lemma singleFunctor_hom_eq_zero_of_isColimit {ι : Type*} {X : ι → C} {c : Cofan X}
    (hc : IsColimit c) {n : ℤ} {N : DerivedCategory C}
    (h : ∀ i (φ : (singleFunctor C n).obj (X i) ⟶ N), φ = 0)
    (φ : (singleFunctor C n).obj c.pt ⟶ N) : φ = 0 := by
  obtain ⟨L, i, _, _⟩ :=
    TauCeti.HasKInjectiveResolutions.exists_quasiIso_isKInjective (Q.objPreimage N)
  let e : N ≅ Q.obj L := (Q.objObjPreimageIso N).symm ≪≫ asIso (Q.map i)
  rw [← cancel_mono e.hom, zero_comp]
  obtain ⟨χ, hχ⟩ := IsKInjective.Q_map_surjective _ L (φ ≫ e.hom)
  rw [← hχ, IsKInjective.Q_map_eq_zero_iff,
    nonempty_homotopy_zero_iff_of_single L (sub_add_cancel n 1)]
  -- On each summand the composite vanishes, so its component factors through the differential.
  have (j : ι) : ∃ g : X j ⟶ L.X (n - 1), g ≫ L.d (n - 1) n =
      (HomologicalComplex.singleObjXSelf (.up ℤ) n (X j)).inv ≫
        ((HomologicalComplex.single C _ n).map (c.inj j) ≫ χ).f n := by
    rw [← nonempty_homotopy_zero_iff_of_single L (sub_add_cancel n 1),
      ← IsKInjective.Q_map_eq_zero_iff, Functor.map_comp, hχ, Q_map_single_map, ← Category.assoc]
    have := h j ((singleFunctor C n).map (c.inj j) ≫ φ)
    rw [this, zero_comp]
  choose g hg using this
  refine ⟨Cofan.IsColimit.desc hc g, Cofan.IsColimit.hom_ext hc _ _ fun j ↦ ?_⟩
  rw [Cofan.IsColimit.fac_assoc, hg]
  simp [HomologicalComplex.single_map_f_self]

end DerivedCategory
