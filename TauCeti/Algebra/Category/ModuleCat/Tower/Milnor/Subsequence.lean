/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality
public import TauCeti.Algebra.Category.ModuleCat.Tower.Subsequence

/-!
# Cofinal restriction of limit complexes

Sampling a tower of complexes along a cofinal monotone sequence leaves its limit complex
unchanged, up to the canonical isomorphism given by restriction of compatible families.
The isomorphism commutes with the actual projections and is natural in maps of towers.
On homology it commutes with the Milnor projection to the inverse limit of homology.

The statements apply to every complex shape, including integer-graded chains and cochains.
They require no surjectivity of the transitions: these comparisons concern ordinary limits
and the projection in the Milnor sequence, not its connecting map from `lim¹`.

The construction uses `ComplexTower.isLimitLimComplexCone` and Mathlib's
`Functor.Initial.isLimitWhiskerEquiv`; the module-valued comparison is
`ModuleTower.limSubsequenceEquiv`.

## References

* C. A. Weibel, *An introduction to homological algebra*, §3.5.
* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
-/

public section

noncomputable section

namespace TauCeti.ComplexTower

open CategoryTheory Limits Opposite

universe v u w

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}

/-- The tower of complexes sampled along a monotone sequence of indices. -/
abbrev subsequence (C : ComplexTower.{v} R c) (φ : ℕ →o ℕ) : ComplexTower.{v} R c :=
  φ.monotone.functor.op ⋙ C

variable (C : ComplexTower.{v} R c) (φ : ℕ →o ℕ) (hφ : ∀ n, ∃ m, n ≤ φ m)

/-- Restriction to cofinally many levels is an isomorphism of limit complexes. -/
def limComplexSubsequenceIso : C.limComplex ≅ (C.subsequence φ).limComplex :=
  (C.isLimitLimComplexCone.whiskerOfCofinal φ hφ).conePointUniqueUpToIso
    (C.subsequence φ).isLimitLimComplexCone

/-- The restriction isomorphism commutes with each selected projection. -/
@[reassoc (attr := simp)]
theorem limComplexSubsequenceIso_hom_comp_π (n : ℕ) :
    (C.limComplexSubsequenceIso φ hφ).hom ≫ (C.subsequence φ).limComplexπ n =
      C.limComplexπ (φ n) := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (C.isLimitLimComplexCone.whiskerOfCofinal φ hφ)
    (C.subsequence φ).isLimitLimComplexCone (op n)
  simp only [Cone.whisker_π, Functor.whiskerLeft_app] at h
  -- The cone point is definitionally the concrete limit complex.
  erw [(C.subsequence φ).limComplexCone_π_app n, C.limComplexCone_π_app (φ n)] at h
  exact h

/-- In each degree, restriction of limit complexes is the module-level cofinal comparison. -/
@[simp]
theorem limComplexSubsequenceIso_hom_f_hom (i : ι) :
    ((C.limComplexSubsequenceIso φ hφ).hom.f i).hom =
      ((C.term i).limSubsequenceEquiv φ hφ).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  have h := congrArg (fun f ↦ (f.f i).hom x)
    (C.limComplexSubsequenceIso_hom_comp_π φ hφ n)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, limComplexπ_f_hom] at h
  -- Degree objects are concrete module limits; erw aligns their dependent source types.
  erw [LinearMap.comp_apply, ModuleTower.limπ_apply, ModuleTower.limπ_apply] at h
  erw [ModuleTower.coe_limSubsequenceEquiv_apply]
  exact h

/-- In each degree, reconstruction of limit complexes is the inverse module comparison. -/
@[simp]
theorem limComplexSubsequenceIso_inv_f_hom (i : ι) :
    ((C.limComplexSubsequenceIso φ hφ).inv.f i).hom =
      ((C.term i).limSubsequenceEquiv φ hφ).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply ((C.term i).limSubsequenceEquiv φ hφ).eq_symm_apply.mpr
  have h := congrArg (fun f ↦ (f.f i).hom x) (C.limComplexSubsequenceIso φ hφ).inv_hom_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    ModuleCat.hom_id, LinearMap.id_apply, limComplexSubsequenceIso_hom_f_hom] at h
  -- As in the forward formula, evaluation aligns the dependent degree objects.
  erw [LinearMap.comp_apply] at h
  exact h

/-- Reconstruction commutes with the projections at the selected indices. -/
@[reassoc (attr := simp)]
theorem limComplexSubsequenceIso_inv_comp_π (n : ℕ) :
    (C.limComplexSubsequenceIso φ hφ).inv ≫ C.limComplexπ (φ n) =
      (C.subsequence φ).limComplexπ n := by
  rw [← C.limComplexSubsequenceIso_hom_comp_π φ hφ n, Iso.inv_hom_id_assoc]

/-- The inverse comparison at any original index is transition from any later selected
index. Thus the inverse requires neither a section of a transition nor a choice of index. -/
@[reassoc]
theorem limComplexSubsequenceIso_inv_comp_π_eq {n m : ℕ} (hnm : n ≤ φ m) :
    (C.limComplexSubsequenceIso φ hφ).inv ≫ C.limComplexπ n =
      (C.subsequence φ).limComplexπ m ≫ C.map (homOfLE hnm).op := by
  rw [← C.limComplexπ_comp_map (homOfLE hnm).op, ← Category.assoc,
    limComplexSubsequenceIso_inv_comp_π]

variable {C} {D : ComplexTower.{v} R c}

/-- Cofinal restriction of limit complexes is natural in maps of towers. -/
@[reassoc]
theorem limComplexSubsequenceIso_hom_naturality (f : C ⟶ D) :
    limComplexMap f ≫ (D.limComplexSubsequenceIso φ hφ).hom =
      (C.limComplexSubsequenceIso φ hφ).hom ≫
        limComplexMap (Functor.whiskerLeft φ.monotone.functor.op f) := by
  apply (D.subsequence φ).isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  rw [limComplexCone_π_app]
  -- State the sources as named limit complexes so simp can infer the category instances
  -- without unfolding the cone point, as in limComplexMap_id.
  have h : (limComplexMap f ≫ (D.limComplexSubsequenceIso φ hφ).hom) ≫
        (D.subsequence φ).limComplexπ n =
      ((C.limComplexSubsequenceIso φ hφ).hom ≫
        limComplexMap (Functor.whiskerLeft φ.monotone.functor.op f)) ≫
          (D.subsequence φ).limComplexπ n := by simp
  exact h

variable (C)

/-- Cofinal restriction commutes with the Milnor projection from limit-complex homology
to the limit of homology modules. This holds without the surjectivity assumptions used
to extend that projection to a short exact Milnor sequence. -/
theorem homologyToLim_limComplexSubsequenceIso (j : ι) :
    (C.subsequence φ).homologyToLim j ∘ₗ
        (HomologicalComplex.homologyMap (C.limComplexSubsequenceIso φ hφ).hom j).hom =
      ((C.homology j).limSubsequenceEquiv φ hφ).toLinearMap ∘ₗ C.homologyToLim j := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  simp only [LinearMap.comp_apply, coe_homologyToLim_apply,
    LinearEquiv.coe_coe, ModuleTower.coe_limSubsequenceEquiv_apply]
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp,
    limComplexSubsequenceIso_hom_comp_π]

end TauCeti.ComplexTower
