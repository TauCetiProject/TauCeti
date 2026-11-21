/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# The de Rham complex extended by zero to negative degrees

The de Rham complex `TauCeti.deRhamComplex I M` is indexed by `ℕ`. Extending it by zero along
`ComplexShape.embeddingUpNat` gives a `ℤ`-indexed cochain complex, as needed to form mapping cones
and cocones of de Rham complexes. This file gives coordinates on the extended complex: in degree
`p = k` its object is the space of smooth `k`-forms (`TauCeti.deRhamComplex.extendXEquiv`), and in
these coordinates the differential is the exterior derivative and the extension of the cochain map
induced by a smooth map is pullback of forms. The extended complex vanishes in negative degrees,
and in every degree when the manifold is empty.
-/

public section

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

namespace deRhamComplex

section Coordinates

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- The degree-`p` object of the extended de Rham complex is the space of smooth `k`-forms when
`p = k`. -/
def extendXEquiv (p : ℤ) (k : ℕ) (hk : (k : ℤ) = p) :
    ((deRhamComplex I M).extend ComplexShape.embeddingUpNat).X p ≃ₗ[ℝ] SmoothForm I M ℝ k :=
  ((deRhamComplex I M).extendXIso ComplexShape.embeddingUpNat hk ≪≫
    deRhamComplexXIso I k).toLinearEquiv

/-- The inverse of `TauCeti.deRhamComplex.extendXEquiv` through the canonical isomorphisms. -/
theorem extendXEquiv_symm_apply (p : ℤ) (k : ℕ) (hk : (k : ℤ) = p) (α : SmoothForm I M ℝ k) :
    (extendXEquiv I M p k hk).symm α =
      ((deRhamComplex I M).extendXIso ComplexShape.embeddingUpNat hk).inv
        ((deRhamComplexXIso I k).inv α) :=
  (rfl)

/-- The extended de Rham complex vanishes in negative degrees. -/
theorem subsingleton_extend_X {p : ℤ} (hp : p < 0) :
    Subsingleton (((deRhamComplex I M).extend ComplexShape.embeddingUpNat).X p) :=
  ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_extend_X _ _ p fun k hk ↦ by
    simp only [ComplexShape.embeddingUpNat_f] at hk
    omega)

/-- In coordinates, the differential of the extended de Rham complex is the exterior derivative. -/
theorem extend_d_extendXEquiv_symm (p p' : ℤ) (k : ℕ) (hk : (k : ℤ) = p)
    (hk' : ((k + 1 : ℕ) : ℤ) = p') (α : SmoothForm I M ℝ k) :
    ((deRhamComplex I M).extend ComplexShape.embeddingUpNat).d p p'
        ((extendXEquiv I M p k hk).symm α) =
      (extendXEquiv I M p' (k + 1) hk').symm (mextDerivₗ I (F := ℝ) k α) := by
  rw [HomologicalComplex.extend_d_eq _ _ hk hk', extendXEquiv_symm_apply,
    extendXEquiv_symm_apply]
  simp [deRhamComplex_d_apply]

/-- The extended de Rham complex of an empty manifold vanishes in every degree. -/
theorem subsingleton_extend_X_of_isEmpty [IsEmpty M] (p : ℤ) :
    Subsingleton (((deRhamComplex I M).extend ComplexShape.embeddingUpNat).X p) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact subsingleton_extend_X I M hp
  · lift p to ℕ using hp
    have : Subsingleton (SmoothForm I M ℝ p) :=
      ⟨fun φ ψ ↦ SmoothBundleForm.ext fun x ↦ isEmptyElim x⟩
    exact (extendXEquiv I M p p rfl).toEquiv.subsingleton

end Coordinates

section Map

universe u v

variable {E E' : Type u} {H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M M' : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']

/-- In coordinates, the extension of the cochain map induced by a smooth map is pullback of
forms. -/
theorem extendMap_map_f_extendXEquiv_symm (f : M → M') (hf : ContMDiff I I' ∞ f) (p : ℤ)
    (k : ℕ) (hk : (k : ℤ) = p) (α : SmoothForm I' M' ℝ k) :
    (HomologicalComplex.extendMap (map f hf) ComplexShape.embeddingUpNat).f p
        ((extendXEquiv I' M' p k hk).symm α) =
      (extendXEquiv I M p k hk).symm (SmoothForm.mpullback f hf α) := by
  rw [HomologicalComplex.extendMap_f _ _ hk, extendXEquiv_symm_apply, extendXEquiv_symm_apply]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  exact congrArg _ (map_f_inv_apply _ _ k α)

end Map

end deRhamComplex

end TauCeti
