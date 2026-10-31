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
def limComplexSubsequenceIso : C.limComplex ≅ (C.subsequence φ).limComplex := by
  letI : φ.monotone.functor.Final := φ.monotone.final_functor_iff.mpr hφ
  exact ((Functor.Initial.isLimitWhiskerEquiv φ.monotone.functor.op C.limComplexCone).symm
    C.isLimitLimComplexCone).conePointUniqueUpToIso (C.subsequence φ).isLimitLimComplexCone

/-- The restriction isomorphism commutes with each selected projection. -/
@[reassoc (attr := simp)]
theorem limComplexSubsequenceIso_hom_comp_π (n : ℕ) :
    (C.limComplexSubsequenceIso φ hφ).hom ≫ (C.subsequence φ).limComplexπ n =
      C.limComplexπ (φ n) := by
  let : φ.monotone.functor.Final := φ.monotone.final_functor_iff.mpr hφ
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    ((Functor.Initial.isLimitWhiskerEquiv φ.monotone.functor.op C.limComplexCone).symm
      C.isLimitLimComplexCone) (C.subsequence φ).isLimitLimComplexCone (op n)

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
  -- Use the named projections to avoid unfolding the limit-cone implementation.
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
