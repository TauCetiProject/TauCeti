/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.Regular
public import TauCeti.Algebra.Lie.Pi
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Centralizers and regular elements in products

The centralizer of an element of a product Lie algebra is the product of its coordinate
centralizers. In finite dimension its dimension is the sum of their dimensions. Consequently
an element of a finite product is regular in the minimal-centralizer sense exactly when every
coordinate is regular. This is the linear algebra behind the regular locus of a semisimple
product and its nonregular complement. The empty product is included, and no simplicity,
semisimplicity, algebraic closure or characteristic assumption is required.

We use `LieAlgebra.IsCentralizerRegular`, which minimizes the dimension of `ker (ad x)`,
rather than Mathlib's Engel-subalgebra notion `LieAlgebra.IsRegular`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, Chapter 4.
-/

public section

open LinearMap Module

namespace LieAlgebra

section Binary

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

/-- The adjoint endomorphism in a binary product acts separately on the two factors. -/
theorem ad_prod (x : L × L') :
    ad R (L × L') x = (ad R L x.1).prodMap (ad R L' x.2) := by
  ext y <;> rfl

/-- The centralizer of an element of a binary product is the product of its centralizers. -/
@[simp]
theorem ker_ad_prod (x : L × L') :
    ker (ad R (L × L') x) = (ker (ad R L x.1)).prod (ker (ad R L' x.2)) := by
  rw [ad_prod, ker_prodMap]

end Binary

section BinaryDimension

variable {K L L' : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieRing L'] [LieAlgebra K L'] [FiniteDimensional K L] [FiniteDimensional K L']

/-- Centralizer dimensions add in a binary product. -/
@[simp]
theorem finrank_ker_ad_prod (x : L × L') :
    finrank K (ker (ad K (L × L') x)) =
      finrank K (ker (ad K L x.1)) + finrank K (ker (ad K L' x.2)) := by
  rw [ker_ad_prod, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- A pair is regular exactly when both its coordinates are regular. -/
@[simp]
theorem isCentralizerRegular_prod_iff (x : L × L') :
    IsCentralizerRegular K x ↔ IsCentralizerRegular K x.1 ∧ IsCentralizerRegular K x.2 := by
  simp only [isCentralizerRegular_iff_forall_finrank_ker_le, finrank_ker_ad_prod]
  refine ⟨fun h ↦ ⟨fun y ↦ ?_, fun y ↦ ?_⟩, fun h y ↦ Nat.add_le_add (h.1 y.1) (h.2 y.2)⟩
  · exact Nat.le_of_add_le_add_right (h (y, x.2))
  · exact Nat.le_of_add_le_add_left (h (x.1, y))

end BinaryDimension

section Pi

variable {R ι : Type*} {L : ι → Type*} [CommRing R] [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra R (L i)]

/-- The adjoint endomorphism of a product is the coordinatewise product of adjoint maps. -/
theorem ad_pi (x : ∀ i, L i) :
    ad R (∀ i, L i) x = LinearMap.piMap (fun i ↦ ad R (L i) (x i)) := by
  ext y i
  rfl

/-- The centralizer in a dependent product is the product submodule of the centralizers. -/
@[simp]
theorem ker_ad_pi (x : ∀ i, L i) :
    ker (ad R (∀ i, L i) x) = Submodule.pi Set.univ (fun i ↦ ker (ad R (L i) (x i))) := by
  ext y
  simp [mem_ker, ad_apply, funext_iff]

/-- Coordinate projections identify a product centralizer with the product of its factors. -/
def kerAdPiEquiv (x : ∀ i, L i) :
    ker (ad R (∀ i, L i) x) ≃ₗ[R] ∀ i, ker (ad R (L i) (x i)) where
  toFun y i := ⟨y.val i, by
    have hy : (y : ∀ i, L i) ∈
        Submodule.pi Set.univ (fun j ↦ ker (ad R (L j) (x j))) := by
      simpa only [ker_ad_pi] using y.property
    exact hy i (Set.mem_univ i)⟩
  invFun y := ⟨fun i ↦ (y i).val, by
    rw [ker_ad_pi]
    exact fun i _ ↦ (y i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The centralizer product equivalence is coordinate evaluation. -/
@[simp]
theorem kerAdPiEquiv_apply (x : ∀ i, L i) (y : ker (ad R (∀ i, L i) x)) (i : ι) :
    ((kerAdPiEquiv x y i : ker (ad R (L i) (x i))) : L i) = (y : ∀ i, L i) i := (rfl)

/-- The inverse centralizer product equivalence assembles the coordinate vectors. -/
@[simp]
theorem kerAdPiEquiv_symm_apply (x : ∀ i, L i) (y : ∀ i, ker (ad R (L i) (x i))) (i : ι) :
    ((kerAdPiEquiv x).symm y : ∀ i, L i) i = (y i : L i) := (rfl)

end Pi

section PiDimension

variable {K ι : Type*} {L : ι → Type*} [Field K] [Fintype ι] [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra K (L i)] [∀ i, FiniteDimensional K (L i)]

/-- The centralizer dimension in a finite product is the sum of the coordinate dimensions. -/
@[simp]
theorem finrank_ker_ad_pi (x : ∀ i, L i) :
    finrank K (ker (ad K (∀ i, L i) x)) = ∑ i, finrank K (ker (ad K (L i) (x i))) := by
  rw [(kerAdPiEquiv x).finrank_eq, Module.finrank_pi_fintype]

omit [Fintype ι] in
/-- An element of a finite product is regular exactly when every coordinate is regular.
In the empty product this includes the unique element of the zero Lie algebra. -/
@[simp]
theorem isCentralizerRegular_pi_iff [Finite ι] (x : ∀ i, L i) :
    IsCentralizerRegular K x ↔ ∀ i, IsCentralizerRegular K (x i) := by
  classical
  let := Fintype.ofFinite ι
  simp only [isCentralizerRegular_iff_forall_finrank_ker_le, finrank_ker_ad_pi]
  refine ⟨fun h i y ↦ ?_, fun h y ↦ Finset.sum_le_sum fun i _ ↦ h i (y i)⟩
  have hi := h (Function.update x i y)
  -- Separate the changed coordinate from the unchanged sum, then cancel that sum.
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hi
  have heq : (∑ j ∈ Finset.univ.erase i,
      finrank K (ker (ad K (L j) (Function.update x i y j)))) =
      ∑ j ∈ Finset.univ.erase i, finrank K (ker (ad K (L j) (x j))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [heq] at hi
  have hupdate : Function.update x i y i = y := Function.update_self i y x
  rw [hupdate] at hi
  exact Nat.le_of_add_le_add_left hi

end PiDimension

end LieAlgebra
