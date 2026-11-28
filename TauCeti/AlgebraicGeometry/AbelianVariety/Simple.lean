/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.DimensionZero
public import TauCeti.AlgebraicGeometry.AbelianVariety.Product
import TauCeti.AlgebraicGeometry.IdealSheaf.Section

/-!
# Simple abelian varieties

A simple abelian variety has positive dimension and has only the zero and whole abelian
subvarieties over the ground field. A proper closed abelian subvariety has strictly smaller
dimension. Consequently every abelian variety of dimension one is simple, whereas a product of
two positive-dimensional abelian varieties contains a proper positive-dimensional factor.

## References

* J. S. Milne, [*Abelian Varieties*, Chapter I, §10](https://www.jmilne.org/math/CourseNotes/AV.pdf).
-/

public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace TauCeti.AlgebraicGeometry.AbelianVariety

open scoped Hom

variable {K : Type u} [Field K] {A B : AbelianVariety K}

/-- An abelian variety is simple over its ground field if it has nonzero dimension and its only
closed abelian subvarieties are the zero variety and itself. -/
structure IsSimple (A : AbelianVariety K) : Prop where
  /-- A simple abelian variety has nonzero dimension. -/
  dim_ne_zero : A.dim ≠ 0
  /-- Every closed abelian subvariety of a simple abelian variety has dimension zero or is the
  whole variety. -/
  dim_eq_zero_or_isIso {B : AbelianVariety K} (i : B ⟶ A) :
    IsClosedImmersion (Hom.toSchemeHom i) → B.dim = 0 ∨ IsIso i

/-- A proper closed abelian subvariety has strictly smaller dimension. -/
theorem dim_lt_of_isClosedImmersion_of_not_isIso (i : B ⟶ A)
    [IsClosedImmersion (Hom.toSchemeHom i)]
    (hi : ¬ IsIso i) : B.dim < A.dim := by
  have he := (Hom.toSchemeHom i).isClosedEmbedding
  have hd : ¬ DenseRange (Hom.toSchemeHom i) := by
    intro hd
    have hs : Surjective (Hom.toSchemeHom i) := by
      rw [surjective_iff, ← Set.range_eq_univ, ← he.isClosed_range.closure_eq]
      exact hd.closure_range
    have hIso := isIso_of_isClosedImmersion_of_surjective (Hom.toSchemeHom i)
    exact hi (isIso_of_isIso_toSchemeHom i)
  apply he.isInducing.topologicalKrullDim_lt hd
  rw [← dim_def, ← finrank_tangentSpace_eq_dim B]
  exact WithBot.coe_eq_top.not.mpr (ENat.natCast_ne_top _)

/-- Simplicity is preserved by isomorphisms over the ground field. -/
theorem IsSimple.of_iso (hA : IsSimple A) (e : A ≅ B) : IsSimple B := by
  refine ⟨dim_eq_of_iso e ▸ hA.dim_ne_zero, fun i hi ↦ ?_⟩
  have hcomp : IsClosedImmersion (Hom.toSchemeHom (i ≫ e.inv)) := by
    rw [Hom.toSchemeHom_comp, ← isoToScheme_inv]
    infer_instance
  rcases hA.dim_eq_zero_or_isIso (i ≫ e.inv) hcomp with h | h
  · exact Or.inl h
  · exact Or.inr ((isIso_comp_right_iff i e.inv).mp h)

/-- Isomorphic abelian varieties are simple simultaneously. -/
theorem isSimple_iff_of_iso (e : A ≅ B) : IsSimple A ↔ IsSimple B :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Every abelian variety of dimension one is simple. -/
theorem isSimple_of_dim_eq_one (hA : A.dim = 1) : IsSimple A := by
  refine ⟨hA ▸ one_ne_zero, fun {B} i hi ↦ ?_⟩
  by_cases h : IsIso i
  · exact Or.inr h
  · left
    have hB := dim_lt_of_isClosedImmersion_of_not_isIso i h
    rw [hA, ← finrank_tangentSpace_eq_dim B] at hB
    norm_cast at hB
    rw [← finrank_tangentSpace_eq_dim B, Nat.lt_one_iff.mp hB]
    norm_num

/-- The product of two nonzero abelian varieties has a proper positive-dimensional abelian
subvariety given by its first factor. -/
theorem not_isSimple_prod (hA : A.dim ≠ 0) (hB : B.dim ≠ 0) : ¬ IsSimple (A.prod B) := by
  let i : A ⟶ A.prod B := prod.lift (𝟙 A) 1
  let p : A.prod B ⟶ A := prod.fst A B
  have hip : i ≫ p = 𝟙 A := prod.lift_fst _ _
  have hp : IsSeparated (Hom.toSchemeHom p) := by
    dsimp only [p, Hom.toSchemeHom]
    rw [prod.toOverHom_fst, Over.comp_left, Over.fst_left]
    infer_instance
  have hclosed : IsClosedImmersion (Hom.toSchemeHom i) := by
    apply Scheme.Hom.isClosedImmersion_of_comp_eq_id _ (f := Hom.toSchemeHom p)
    rw [← Hom.toSchemeHom_comp, hip, Hom.toSchemeHom_id]
  intro h
  rcases h.dim_eq_zero_or_isIso i hclosed with hz | hi
  · exact hA hz
  · have hd := dim_eq_of_iso (asIso i)
    rw [dim_prod, ← finrank_tangentSpace_eq_dim A, ← finrank_tangentSpace_eq_dim B] at hd
    norm_cast at hd
    have hfin : Module.finrank K B.TangentSpace = 0 := by omega
    apply hB
    rw [← finrank_tangentSpace_eq_dim B, hfin]
    norm_num

end TauCeti.AlgebraicGeometry.AbelianVariety
