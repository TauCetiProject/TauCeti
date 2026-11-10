/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.Algebra.Homology.DerivedCategory.Singularity.Syzygy
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.RingTheory.GlobalDimension

/-!
# Objects of finite projective dimension are perfect

Let `C` be an abelian category with enough projectives. An object `X` of `C` of finite projective
dimension, placed in any degree, is a perfect object of `Dᵇ(C)`. The proof is by induction on the
projective dimension: a short exact sequence `0 ⟶ K ⟶ P ⟶ X ⟶ 0` with `P` projective gives a
distinguished triangle `K ⟶ P ⟶ X ⟶ K[1]`, the kernel `K` has smaller projective dimension, and the
perfect objects form a triangulated subcategory.

Consequently, when every object of `C` has finite projective dimension, the singularity category
`D_sg(C)` is zero, since every object of `D_sg(C)` is an object of `C` placed in some degree
(`TauCeti.SingularityCategory.exists_iso_Q_obj_singleFunctor_obj`). This applies to a left
noetherian ring of finite global dimension.

## Main results

* `TauCeti.DerivedCategory.Bounded.perfect_singleFunctor_obj_of_hasProjectiveDimensionLT`: an
  object of finite projective dimension, placed in any degree, is perfect.
* `TauCeti.SingularityCategory.isZero_of_forall_hasProjectiveDimensionLT`: if every object of `C`
  has finite projective dimension, every object of the singularity category is zero.
* `TauCeti.ModuleCat.SingularityCategory.isZero_of_globalDimension_le`: the singularity category of
  a left noetherian ring of finite global dimension is zero.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 1.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory.Bounded

/-- An object of projective dimension `< n + 1`, placed in degree zero, is perfect. -/
private theorem perfect_singleFunctor_zero_obj_of_hasProjectiveDimensionLT [EnoughProjectives C]
    (n : ℕ) : ∀ (X : C) [HasProjectiveDimensionLT X (n + 1)],
      perfect C ((singleFunctor C 0).obj X) := by
  induction n with
  | zero =>
    intro X hX
    have : HasProjectiveDimensionLT X 1 := hX
    exact perfect_singleFunctor_obj C 0 (projective_iff_hasProjectiveDimensionLT_one.2 this)
  | succ n ih =>
    intro X _
    -- The short exact sequence `0 ⟶ K ⟶ P ⟶ X ⟶ 0` with `P` projective.
    let S := Projective.kernelShortComplex X
    have hS : S.ShortExact := Projective.kernelShortComplex_shortExact X
    have : HasProjectiveDimensionLT S.X₁ (n + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).1 inferInstance
    exact (perfect C).ext_of_isTriangulatedClosed₃ _ hS.boundedSingleTriangle_distinguished
      (ih S.X₁) (perfect_singleFunctor_obj C 0 inferInstance)

/-- **Objects of finite projective dimension are perfect**: in an abelian category with enough
projectives, an object of finite projective dimension, placed in any degree, is a perfect object
of the bounded derived category. -/
theorem perfect_singleFunctor_obj_of_hasProjectiveDimensionLT [EnoughProjectives C] (m : ℤ)
    (X : C) (n : ℕ) [HasProjectiveDimensionLT X n] : perfect C ((singleFunctor C m).obj X) := by
  have : HasProjectiveDimensionLT X (n + 1) := hasProjectiveDimensionLT_of_ge X n (n + 1) (by lia)
  -- The degree-zero object is perfect; shifting by `-m` moves it to degree `m`.
  exact (perfect C).prop_of_iso (((singleFunctors C).shiftIso (-m) m 0 (by lia)).app X)
    ((perfect C).le_shift (-m) _ (perfect_singleFunctor_zero_obj_of_hasProjectiveDimensionLT n X))

end DerivedCategory.Bounded

namespace SingularityCategory

/-- An object of finite projective dimension, placed in any degree, vanishes in the singularity
category. -/
theorem isZero_Q_obj_singleFunctor_obj_of_hasProjectiveDimensionLT [EnoughProjectives C]
    (m : ℤ) (X : C) (n : ℕ) [HasProjectiveDimensionLT X n] :
    IsZero ((Q C).obj ((DerivedCategory.Bounded.singleFunctor C m).obj X)) :=
  isZero_Q_obj_of_perfect
    (DerivedCategory.Bounded.perfect_singleFunctor_obj_of_hasProjectiveDimensionLT m X n)

/-- **The singularity category vanishes in finite projective dimension**: if every object of an
abelian category with enough projectives has finite projective dimension, every object of the
singularity category is zero. -/
theorem isZero_of_forall_hasProjectiveDimensionLT [EnoughProjectives C]
    (h : ∀ X : C, ∃ n : ℕ, HasProjectiveDimensionLT X n) (Y : SingularityCategory C) :
    IsZero Y := by
  let := HasExt.standard C
  have := Localization.essSurj (Q C) (DerivedCategory.Bounded.perfect C).trW
  -- Every object of the singularity category is an object of `C` placed in some degree.
  obtain ⟨M, m, -, ⟨e⟩⟩ := exists_iso_Q_obj_singleFunctor_obj_isSyzygy ((Q C).objPreimage Y) 0
  obtain ⟨n, _⟩ := h M
  exact (isZero_Q_obj_singleFunctor_obj_of_hasProjectiveDimensionLT m M n).of_iso
    (((Q C).objObjPreimageIso Y).symm ≪≫ e)

end SingularityCategory

/-- **A ring of finite global dimension has zero singularity category**: for a left noetherian
ring `A` of finite global dimension, every object of `D_sg(A) = Dᵇ(mod-A) / Kᵇ(proj-A)` is zero. -/
theorem ModuleCat.SingularityCategory.isZero_of_globalDimension_le (A : Type u) [Ring A]
    [IsNoetherianRing A] [HasDerivedCategory.{w} (FGModuleCat.{u} A)] (n : ℕ)
    (h : globalDimension.{u} A ≤ n) (Y : ModuleCat.SingularityCategory A) : IsZero Y :=
  -- Every finitely generated module has finite projective dimension in `FGModuleCat A`.
  SingularityCategory.isZero_of_forall_hasProjectiveDimensionLT (fun X ↦ ⟨n + 1,
    FGModuleCat.hasProjectiveDimensionLE_of_forget₂ n X
      ((globalDimension_le_iff_hasProjectiveDimensionLE A n).1 h _)⟩) Y

end TauCeti
