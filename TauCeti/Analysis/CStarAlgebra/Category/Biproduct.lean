/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.CategoryTheory.Dagger.Biproduct
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Orthogonal sums in C*-categories

In a C*-category every finite biproduct can be made orthogonal without changing its point. For a
finite bicone `c` of a family `F`, the endomorphism `h = ∑ j, π_j† π_j` of `c.pt` (in categorical
order `∑ j, c.π j ≫ dagger (c.π j)`) is positive in the C*-algebra `End c.pt`. With `u` its
positive square root, the inclusions `c.ι j ≫ u` and the projections `u ≫ dagger (c.ι j)` form an
orthogonal bicone `c.orthogonalize` on the same point. When `c` is a limit bicone, `h` is
invertible with inverse `∑ j, ι_j ι_j†`, and `c.orthogonalize` is again a limit bicone.

Hence a finite family of objects of a C*-category has an orthogonal sum exactly when it has a
native biproduct (`TauCeti.CStarCategory.hasOrthogonalBiproduct_iff`), and by
`CategoryTheory.Limits.Bicone.IsOrthogonal.isUnitary_conePointUniqueUpToIso_hom` this orthogonal
sum is unique up to a unitary isomorphism. An orthogonal bicone is left unchanged by the
construction (`CategoryTheory.Limits.Bicone.orthogonalize_eq_self`).

## Main declarations

* `CategoryTheory.Limits.Bicone.orthogonalize`: the orthogonal bicone on the point of a finite
  bicone in a C*-category.
* `CategoryTheory.Limits.Bicone.isBilimitOrthogonalize`: it is a limit bicone when the original
  bicone is.
* `TauCeti.CStarCategory.hasOrthogonalBiproduct_iff`: orthogonal sums and native biproducts of
  finite families exist together; in particular a finite family with a biproduct has an
  orthogonal sum, as an instance.
* `TauCeti.CStarCategory.hasFiniteOrthogonalBiproducts_iff`: a C*-category has finite orthogonal
  sums exactly when it has finite biproducts, again with the corresponding instance.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109.
-/

public section

noncomputable section

open CategoryTheory Limits TauCeti

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]

namespace CategoryTheory.Limits.Bicone

variable {J : Type w} [Fintype J] {F : J → C}

/-- The positive endomorphism `∑ j, π_j† π_j` of the point of a finite bicone, written
`∑ j, c.π j ≫ dagger (c.π j)` in categorical order. -/
private def gram (c : Bicone F) : End c.pt :=
  ∑ j, End.of (c.π j ≫ dagger (c.π j))

omit [Linear ℂ C] [DaggerPreadditive C] [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)]
  [CStarCategory C] in
private theorem gram_asHom (c : Bicone F) :
    (gram c).asHom = ∑ j, c.π j ≫ dagger (c.π j) := by
  simp [gram, End.sum_asHom]

private theorem gram_nonneg (c : Bicone F) : 0 ≤ gram c :=
  Finset.sum_nonneg fun j _ => End.self_comp_dagger_nonneg (c.π j)

omit [Linear ℂ C] [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] in
/-- The endomorphism `∑ j, π_j† π_j` sends the adjoint of an inclusion to the corresponding
projection: `(∑ j, c.π j ≫ dagger (c.π j)) ≫ dagger (c.ι k) = c.π k`. -/
@[reassoc]
private theorem gram_asHom_comp_dagger_ι (c : Bicone F) (k : J) :
    (gram c).asHom ≫ dagger (c.ι k) = c.π k := by
  classical
  rw [gram_asHom, Preadditive.sum_comp, Finset.sum_eq_single k]
  · rw [Category.assoc, ← dagger_comp, bicone_ι_π_self, dagger_id, Category.comp_id]
  · intro l _ hl
    rw [Category.assoc, ← dagger_comp, bicone_ι_π_ne c (Ne.symm hl), dagger_zero,
      Limits.comp_zero]
  · simp

/-- The adjoint form of `gram_asHom_comp_dagger_ι`: `c.ι k ≫ ∑ j, c.π j ≫ dagger (c.π j)` is
`dagger (c.π k)`. -/
private theorem ι_comp_gram_asHom (c : Bicone F) (k : J) :
    c.ι k ≫ (gram c).asHom = dagger (c.π k) := by
  rw [← dagger_dagger (c.ι k ≫ _), dagger_comp, ← End.star_asHom,
    (gram_nonneg c).isSelfAdjoint.star_eq, gram_asHom_comp_dagger_ι]

/-- The positive square root of `∑ j, π_j† π_j`, an automorphism of the point when `c` is a
limit bicone, used to make `c` orthogonal. -/
private def sqrtGram (c : Bicone F) : End c.pt :=
  CFC.sqrt (gram c)

private theorem dagger_sqrtGram_asHom (c : Bicone F) :
    dagger (sqrtGram c).asHom = (sqrtGram c).asHom := by
  rw [← End.star_asHom, sqrtGram, (CFC.sqrt_nonneg (gram c)).isSelfAdjoint.star_eq]

@[reassoc]
private theorem sqrtGram_asHom_comp_sqrtGram_asHom (c : Bicone F) :
    (sqrtGram c).asHom ≫ (sqrtGram c).asHom = (gram c).asHom := by
  rw [← End.mul_asHom, sqrtGram, CFC.sqrt_mul_sqrt_self _ (gram_nonneg c)]

/-- The square root `CFC.sqrt (∑ k, End.of (c.π k ≫ dagger (c.π k)))` in the definition of
`orthogonalize` is `sqrtGram c`. -/
private theorem sqrt_sum_eq_sqrtGram (c : Bicone F) :
    CFC.sqrt (∑ k, End.of (c.π k ≫ dagger (c.π k))) = sqrtGram c :=
  rfl

/-- The orthogonal bicone on the point of a finite bicone `c` of a C*-category. With `u` the
positive square root of `∑ j, π_j† π_j`, its inclusions are `c.ι j ≫ u` and its projections are
their daggers `u ≫ dagger (c.ι j)`. It is a limit bicone when `c` is
(`CategoryTheory.Limits.Bicone.isBilimitOrthogonalize`). -/
@[expose]
def orthogonalize (c : Bicone F) : Bicone F where
  pt := c.pt
  π j := (CFC.sqrt (∑ k, End.of (c.π k ≫ dagger (c.π k)))).asHom ≫ dagger (c.ι j)
  ι j := c.ι j ≫ (CFC.sqrt (∑ k, End.of (c.π k ≫ dagger (c.π k)))).asHom
  ι_π j k := by
    rw [sqrt_sum_eq_sqrtGram, Category.assoc, sqrtGram_asHom_comp_sqrtGram_asHom_assoc,
      gram_asHom_comp_dagger_ι, c.ι_π]

/-- The orthogonalization of a bicone has the same point. -/
@[simp] theorem orthogonalize_pt (c : Bicone F) : c.orthogonalize.pt = c.pt := (rfl)

/-- The inclusions of the orthogonalization of `c` are `c.ι j ≫ u`, with `u` the positive square
root of `∑ k, c.π k ≫ dagger (c.π k)` in the C*-algebra `End c.pt`. -/
@[simp, reassoc]
theorem orthogonalize_ι (c : Bicone F) (j : J) :
    c.orthogonalize.ι j = c.ι j ≫ (CFC.sqrt (∑ k, End.of (c.π k ≫ dagger (c.π k)))).asHom :=
  (rfl)

/-- The projections of the orthogonalization of `c` are `u ≫ dagger (c.ι j)`, with `u` the
positive square root of `∑ k, c.π k ≫ dagger (c.π k)` in the C*-algebra `End c.pt`. -/
@[simp, reassoc]
theorem orthogonalize_π (c : Bicone F) (j : J) :
    c.orthogonalize.π j = (CFC.sqrt (∑ k, End.of (c.π k ≫ dagger (c.π k)))).asHom ≫
      dagger (c.ι j) :=
  (rfl)

/-- The orthogonalization of a finite bicone in a C*-category is orthogonal. -/
theorem isOrthogonal_orthogonalize (c : Bicone F) : c.orthogonalize.IsOrthogonal :=
  (isOrthogonal_iff _).mpr fun j => by
    rw [orthogonalize_π, orthogonalize_ι, sqrt_sum_eq_sqrtGram]
    -- `rw [dagger_comp]` fails here: the point `c.orthogonalize.pt` is only definitionally `c.pt`.
    exact (dagger_comp _ _).trans <| by
      rw [dagger_dagger]
      exact congrArg (c.ι j ≫ ·) (dagger_sqrtGram_asHom c)

/-- The endomorphism `∑ j, ι_j ι_j†` of the point of a finite bicone, written
`∑ j, dagger (c.ι j) ≫ c.ι j` in categorical order. -/
private def coGram (c : Bicone F) : End c.pt :=
  ∑ j, End.of (dagger (c.ι j) ≫ c.ι j)

/-- For a limit bicone, `∑ j, ι_j ι_j†` is a two-sided inverse of `∑ j, π_j† π_j`. -/
private theorem gram_mul_coGram (c : Bicone F) (hc : c.IsBilimit) :
    gram c * coGram c = 1 ∧ coGram c * gram c = 1 := by
  constructor
  · ext
    -- `∑ j, dagger (c.ι j) ≫ c.ι j ≫ h` is the dagger of `∑ j, c.π j ≫ c.ι j = 𝟙 c.pt`.
    simp only [End.mul_asHom, End.one_asHom, coGram, End.sum_asHom, Preadditive.sum_comp,
      Category.assoc, ι_comp_gram_asHom, ← dagger_comp, ← dagger_sum, IsBilimit.total hc, dagger_id]
  · ext
    simp only [End.mul_asHom, End.one_asHom, coGram, End.sum_asHom, Preadditive.comp_sum,
      gram_asHom_comp_dagger_ι_assoc, IsBilimit.total hc]

/-- The orthogonalization of a finite limit bicone in a C*-category is a limit bicone. -/
def isBilimitOrthogonalize {c : Bicone F} (hc : c.IsBilimit) : c.orthogonalize.IsBilimit :=
  isBilimitOfTotal _ <| by
    -- With `u = √h` and `g = h⁻¹ = ∑ j, ι_j ι_j†`, the total is `u g u = g h = 1`.
    obtain ⟨hg, gh⟩ := gram_mul_coGram c hc
    have hu : Commute (sqrtGram c) (coGram c) := Commute.cfcₙ_nnreal (hg.trans gh.symm) _
    have key : sqrtGram c * coGram c * sqrtGram c = 1 := by
      rw [hu.eq, mul_assoc, sqrtGram, CFC.sqrt_mul_sqrt_self _ (gram_nonneg c), gh]
    have := congrArg End.asHom key
    simp only [coGram, End.mul_asHom, End.sum_asHom, End.one_asHom, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc] at this
    simp only [orthogonalize_π, orthogonalize_ι, sqrt_sum_eq_sqrtGram]
    exact .trans (Finset.sum_congr rfl fun j _ => Category.assoc _ _ _) this

/-- An orthogonal bicone is its own orthogonalization. -/
theorem orthogonalize_eq_self {c : Bicone F} (hc : c.IsOrthogonal) : c.orthogonalize = c := by
  -- For orthogonal `c`, `h = ∑ j, π_j† π_j` is the projection `∑ j, ι_j ι_j†`, which fixes each
  -- inclusion, so `√h = h`.
  have hι (j : J) : c.ι j ≫ (gram c).asHom = c.ι j := by rw [ι_comp_gram_asHom, hc.dagger_π]
  have hπ (j : J) : (gram c).asHom ≫ c.π j = c.π j := by
    simpa only [hc.dagger_ι] using gram_asHom_comp_dagger_ι c j
  have hsqrt : sqrtGram c = gram c := by
    rw [sqrtGram, CFC.sqrt_eq_iff _ _ (gram_nonneg c) (gram_nonneg c)]
    ext
    rw [End.mul_asHom]
    conv_lhs => arg 2; rw [gram_asHom]
    simp only [Preadditive.comp_sum, reassoc_of% hπ]
    exact (gram_asHom c).symm
  have hι' (j : J) : c.orthogonalize.ι j = c.ι j := by
    rw [orthogonalize_ι, sqrt_sum_eq_sqrtGram, hsqrt, hι]
  have hπ' (j : J) : c.orthogonalize.π j = c.π j := by
    rw [orthogonalize_π, sqrt_sum_eq_sqrtGram, hsqrt, hc.dagger_ι, hπ]
  -- `c.orthogonalize` has the point of `c`, so it is determined by its projections and inclusions.
  calc c.orthogonalize = ⟨c.pt, c.orthogonalize.π, c.orthogonalize.ι, c.orthogonalize.ι_π⟩ := rfl
    _ = c := by
      cases c
      congr 1
      exacts [funext hπ', funext hι']

end CategoryTheory.Limits.Bicone

namespace TauCeti.CStarCategory

variable {J : Type w} [Finite J] {F : J → C}

/-- A finite family of objects of a C*-category has an orthogonal sum exactly when it has a
biproduct. -/
theorem hasOrthogonalBiproduct_iff : HasOrthogonalBiproduct F ↔ HasBiproduct F := by
  refine ⟨fun _ => HasOrthogonalBiproduct.hasBiproduct F, fun _ => ?_⟩
  have := Fintype.ofFinite J
  exact ⟨⟨⟨_, Bicone.isBilimitOrthogonalize (biproduct.isBilimit F)⟩,
    (biproduct.bicone F).isOrthogonal_orthogonalize⟩⟩

/-- A finite family of objects of a C*-category with a biproduct has an orthogonal sum. -/
instance [HasBiproduct F] : HasOrthogonalBiproduct F :=
  hasOrthogonalBiproduct_iff.mpr ‹_›

variable (C) in
/-- A C*-category has finite orthogonal sums exactly when it has finite biproducts. -/
theorem hasFiniteOrthogonalBiproducts_iff :
    HasFiniteOrthogonalBiproducts C ↔ HasFiniteBiproducts C :=
  ⟨fun _ => HasFiniteOrthogonalBiproducts.hasFiniteBiproducts C,
    fun _ => ⟨fun _ _ => inferInstance⟩⟩

/-- A C*-category with finite biproducts has finite orthogonal sums. -/
instance [HasFiniteBiproducts C] : HasFiniteOrthogonalBiproducts C :=
  (hasFiniteOrthogonalBiproducts_iff C).mpr ‹_›

end TauCeti.CStarCategory
