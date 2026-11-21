/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Product
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Disk

/-!
# The cup product on the two-torus

Let `k` be a commutative ring and `T² = S¹ × S¹` the product of two copies of the circle
`TopCat.sphere 1`. Let `θ ∈ H¹(S¹; k)` be the class dual to the standard generator of `H₁(S¹; k)`
(`TauCeti.singularCohomologyTopCatSphereGenerator`), and put `α = pr₁^* θ` and `β = pr₂^* θ` in
`H¹(T²; k)` (`TauCeti.singularCohomologyTorusFst`, `TauCeti.singularCohomologyTorusSnd`). This file
computes the cup product `H¹(T²; k) × H¹(T²; k) → H²(T²; k)`:

* `H¹(T²; k)` is free on `α` and `β`: `(a, b) ↦ a α + b β` is a linear equivalence
  `k × k ≃ H¹(T²; k)` (`TauCeti.singularCohomologyTorusOneEquiv`);
* `H²(T²; k)` is free on `α ⌣ β`: `c ↦ c (α ⌣ β)` is a linear equivalence `k ≃ H²(T²; k)`
  (`TauCeti.singularCohomologyTorusTwoEquiv`);
* `α ⌣ α = 0`, `β ⌣ β = 0` and `β ⌣ α = -(α ⌣ β)`, so the cup product of two classes of degree
  one is their determinant, `(a α + b β) ⌣ (a' α + b' β) = (a b' - b a') (α ⌣ β)`
  (`TauCeti.singularCup_singularCohomologyTorusOneEquiv`).

Both equivalences come from the decomposition of the cohomology of a product with a sphere by
slant products (`TopCat.singularCohomologySphereProdSlantEquiv`), with `H⁰(S¹; k) ≅ k`
(`TauCeti.singularCohomologyZeroEvalEquiv`), `H¹(S¹; k) ≅ k`
(`TauCeti.singularCohomologyTopCatSphereEquiv`) and `H²(S¹; k) = 0`.

The torus is the basic example on which the graded commutativity of the cup product,
`b ⌣ a = (-1)^(|a| |b|) a ⌣ b` (`TopCat.singularCup_gradedComm_tensorUnit`), is not an
identity between commuting classes: for `k` nontrivial `α ⌣ β ≠ 0`
(`TauCeti.singularCup_singularCohomologyTorusFst_singularCohomologyTorusSnd_ne_zero`), and when
`2 ≠ 0` in `k` the two products of `α` and `β` differ
(`TauCeti.singularCup_singularCohomologyTorusSnd_singularCohomologyTorusFst_ne`). The torus is
also symplectically aspherical, so its Hamiltonian Floer cohomology needs no Novikov coefficients;
through the PSS isomorphism these two classes of odd degree are the basic example in which the
sign `(-1)^(a b)` of the graded commutativity of the pair-of-pants product is `-1` on a nonzero
product.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the cup product structure of closed orientable surfaces and of tori, and
  Theorem 3.11 (graded commutativity).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe w

namespace TauCeti

variable (k : Type w) [CommRing k]

/-- The class `α = pr₁^* θ ∈ H¹(S¹ × S¹; k)`, pulled back from the first circle factor of the
generator `θ` of `H¹(S¹; k)`. -/
def singularCohomologyTorusFst :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 1 :=
  TopCat.singularCohomologyMap (fst _ _) 1 (singularCohomologyTopCatSphereGenerator k 0)

/-- The class `β = pr₂^* θ ∈ H¹(S¹ × S¹; k)`, pulled back from the second circle factor of the
generator `θ` of `H¹(S¹; k)`. -/
def singularCohomologyTorusSnd :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 1 :=
  TopCat.singularCohomologyMap (snd _ _) 1 (singularCohomologyTopCatSphereGenerator k 0)

/-- `α = pr₁^* θ`: the class `TauCeti.singularCohomologyTorusFst` is the pullback of the generator
of `H¹(S¹; k)` along the first projection. -/
theorem singularCohomologyTorusFst_def :
    singularCohomologyTorusFst k =
      TopCat.singularCohomologyMap (fst _ _) 1 (singularCohomologyTopCatSphereGenerator k 0) :=
  (rfl)

/-- `β = pr₂^* θ`: the class `TauCeti.singularCohomologyTorusSnd` is the pullback of the generator
of `H¹(S¹; k)` along the second projection. -/
theorem singularCohomologyTorusSnd_def :
    singularCohomologyTorusSnd k =
      TopCat.singularCohomologyMap (snd _ _) 1 (singularCohomologyTopCatSphereGenerator k 0) :=
  (rfl)

/-- `α ⌣ α = 0`, since `θ ⌣ θ = 0` on the circle. -/
@[simp]
theorem singularCup_singularCohomologyTorusFst_self :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
      (singularCohomologyTorusFst k) (singularCohomologyTorusFst k) = 0 := by
  rw [singularCohomologyTorusFst, TopCat.singularCup_naturality]
  -- `θ ⌣ θ = 0` is stated in degrees `0 + 1` and `0 + 1 + (0 + 1)`, definitionally `1` and `2`.
  erw [TopCat.singularCup_singularCohomologyTopCatSphereGenerator_self]
  exact map_zero _

/-- `β ⌣ β = 0`, since `θ ⌣ θ = 0` on the circle. -/
@[simp]
theorem singularCup_singularCohomologyTorusSnd_self :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
      (singularCohomologyTorusSnd k) (singularCohomologyTorusSnd k) = 0 := by
  rw [singularCohomologyTorusSnd, TopCat.singularCup_naturality]
  -- `θ ⌣ θ = 0` is stated in degrees `0 + 1` and `0 + 1 + (0 + 1)`, definitionally `1` and `2`.
  erw [TopCat.singularCup_singularCohomologyTopCatSphereGenerator_self]
  exact map_zero _

/-- **The odd exchange on the torus**: `β ⌣ α = -(α ⌣ β)`, the graded commutativity of the cup
product for two classes of degree one. -/
@[simp]
theorem singularCup_singularCohomologyTorusSnd_singularCohomologyTorusFst :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
        (singularCohomologyTorusSnd k) (singularCohomologyTorusFst k) =
      -(TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
        (singularCohomologyTorusFst k) (singularCohomologyTorusSnd k) := by
  rw [TopCat.singularCup_gradedComm_tensorUnit _ k (μ := (λ_ _).hom) (IsCommMonObj.mul_comm _)
    (show 1 + 1 = 2 from rfl) (singularCohomologyTorusFst k) (singularCohomologyTorusSnd k)]
  simp

/-- **The first cohomology of the torus**: `(a, b) ↦ a α + b β` is a linear equivalence
`k × k ≃ H¹(S¹ × S¹; k)` (`TauCeti.singularCohomologyTorusOneEquiv_apply`). -/
def singularCohomologyTorusOneEquiv :
    (k × k) ≃ₗ[k] (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCohomology
      (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 1 :=
  LinearEquiv.prodComm k k k ≪≫ₗ
    ((singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) 0).symm.prodCongr
      (singularCohomologyZeroEvalEquiv
        (PathConnectedSpace.nonempty (X := TopCat.sphere.{w} 1)).some).symm) ≪≫ₗ
    (TopCat.singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) (TopCat.sphere.{w} 1)
      (PathConnectedSpace.nonempty (X := TopCat.sphere.{w} 1)).some 0).symm

/-- The equivalence `k × k ≃ H¹(S¹ × S¹; k)` sends `(a, b)` to `a α + b β`. -/
@[simp]
theorem singularCohomologyTorusOneEquiv_apply (p : k × k) :
    singularCohomologyTorusOneEquiv k p =
      p.1 • singularCohomologyTorusFst k + p.2 • singularCohomologyTorusSnd k := by
  simp only [singularCohomologyTorusOneEquiv, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply,
    LinearEquiv.prodCongr_apply, Prod.fst_swap, Prod.snd_swap,
    singularCohomologyZeroEvalEquiv_symm_apply, singularCohomologyTopCatSphereEquiv_symm_eq_smul]
  -- The slant decomposition writes the degree `1` of `H¹(S¹ × S¹; k)` as `0 + (0 + 1)`.
  erw [TopCat.singularCohomologySphereProdSlantEquiv_symm_apply]
  simp only [map_smul, singularCohomologyMap_singularCohomologyZeroOne]
  -- The slant decomposition writes the degrees as `0 + 1` and `0 + (0 + 1)`, definitionally `1`.
  erw [TopCat.singularCup_singularCohomologyZeroOne_right]
  exact add_comm _ _

/-- The inverse of the equivalence `k × k ≃ H¹(S¹ × S¹; k)` sends `α` to `(1, 0)`. -/
@[simp]
theorem singularCohomologyTorusOneEquiv_symm_singularCohomologyTorusFst :
    (singularCohomologyTorusOneEquiv k).symm (singularCohomologyTorusFst k) = (1, 0) := by
  rw [LinearEquiv.symm_apply_eq, singularCohomologyTorusOneEquiv_apply, one_smul, zero_smul,
    add_zero]

/-- The inverse of the equivalence `k × k ≃ H¹(S¹ × S¹; k)` sends `β` to `(0, 1)`. -/
@[simp]
theorem singularCohomologyTorusOneEquiv_symm_singularCohomologyTorusSnd :
    (singularCohomologyTorusOneEquiv k).symm (singularCohomologyTorusSnd k) = (0, 1) := by
  rw [LinearEquiv.symm_apply_eq, singularCohomologyTorusOneEquiv_apply, one_smul, zero_smul,
    zero_add]

/-- **The second cohomology of the torus**: `c ↦ c (α ⌣ β)` is a linear equivalence
`k ≃ H²(S¹ × S¹; k)` (`TauCeti.singularCohomologyTorusTwoEquiv_apply`). -/
def singularCohomologyTorusTwoEquiv :
    k ≃ₗ[k] (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCohomology
      (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 2 :=
  haveI : Unique ((TopCat.sphere.{w} 1).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) (1 + (0 + 1))) :=
    { default := 0
      uniq := fun _ ↦ (ModuleCat.subsingleton_of_isZero
        (isZero_singularCohomology_topCatSphere_of_ne k (𝟙_ (ModuleCat.{w} k)) 1 1
          (by omega))).elim _ _ }
  (singularCohomologyTopCatSphereEquiv k (𝟙_ (ModuleCat.{w} k)) 0).symm ≪≫ₗ
    LinearEquiv.uniqueProd.symm ≪≫ₗ
    (TopCat.singularCohomologySphereProdSlantEquiv (𝟙_ (ModuleCat.{w} k)) (TopCat.sphere.{w} 1)
      (PathConnectedSpace.nonempty (X := TopCat.sphere.{w} 1)).some 1).symm

/-- The equivalence `k ≃ H²(S¹ × S¹; k)` sends `c` to `c (α ⌣ β)`. -/
@[simp]
theorem singularCohomologyTorusTwoEquiv_apply (c : k) :
    singularCohomologyTorusTwoEquiv k c =
      c • (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2
        rfl (singularCohomologyTorusFst k) (singularCohomologyTorusSnd k) := by
  simp only [singularCohomologyTorusTwoEquiv, LinearEquiv.trans_apply,
    LinearEquiv.uniqueProd_symm_apply]
  -- The slant decomposition writes the degrees as `0 + 1` and `1 + (0 + 1)`, definitionally `1`
  -- and `2`, and the first component is the unique class of `H²(S¹; k) = 0`, definitionally `0`;
  -- the last step unfolds the definitions of `α` and `β`.
  erw [TopCat.singularCohomologySphereProdSlantEquiv_symm_apply, map_zero, zero_add]
  rw [singularCohomologyTopCatSphereEquiv_symm_eq_smul, map_smul, map_smul]
  rfl

/-- The inverse of the equivalence `k ≃ H²(S¹ × S¹; k)` sends `α ⌣ β` to `1`. -/
@[simp]
theorem singularCohomologyTorusTwoEquiv_symm_singularCup :
    (singularCohomologyTorusTwoEquiv k).symm
        ((TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2
          rfl (singularCohomologyTorusFst k) (singularCohomologyTorusSnd k)) = 1 := by
  rw [LinearEquiv.symm_apply_eq, singularCohomologyTorusTwoEquiv_apply, one_smul]

/-- **The cup product on `H¹` of the torus is the determinant**:
`(a α + b β) ⌣ (a' α + b' β) = (a b' - b a') (α ⌣ β)`. -/
theorem singularCup_singularCohomologyTorusOneEquiv (p q : k × k) :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
        (singularCohomologyTorusOneEquiv k p) (singularCohomologyTorusOneEquiv k q) =
      singularCohomologyTorusTwoEquiv k (p.1 * q.2 - p.2 * q.1) := by
  rw [singularCohomologyTorusOneEquiv_apply, singularCohomologyTorusOneEquiv_apply,
    singularCohomologyTorusTwoEquiv_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    singularCup_singularCohomologyTorusFst_self, singularCup_singularCohomologyTorusSnd_self,
    singularCup_singularCohomologyTorusSnd_singularCohomologyTorusFst]
  module

/-- The class `α ⌣ β` generates `H²(S¹ × S¹; k)`, so it is nonzero over a nontrivial ring. -/
theorem singularCup_singularCohomologyTorusFst_singularCohomologyTorusSnd_ne_zero
    [Nontrivial k] :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
      (singularCohomologyTorusFst k) (singularCohomologyTorusSnd k) ≠ 0 := by
  have h := (singularCohomologyTorusTwoEquiv k).map_ne_zero_iff.2 (one_ne_zero (α := k))
  rwa [singularCohomologyTorusTwoEquiv_apply, one_smul] at h

/-- **The odd exchange is visible on the torus**: when `2 ≠ 0` in `k`, the two cup products of
`α` and `β` differ, `β ⌣ α ≠ α ⌣ β`. -/
theorem singularCup_singularCohomologyTorusSnd_singularCohomologyTorusFst_ne
    (h2 : (2 : k) ≠ 0) :
    (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
        (singularCohomologyTorusSnd k) (singularCohomologyTorusFst k) ≠
      (TopCat.sphere.{w} 1 ⊗ TopCat.sphere.{w} 1).singularCup k (λ_ _).inv (λ_ _).hom 1 1 2 rfl
        (singularCohomologyTorusFst k) (singularCohomologyTorusSnd k) := by
  rw [singularCup_singularCohomologyTorusSnd_singularCohomologyTorusFst, ne_eq,
    neg_eq_iff_add_eq_zero, ← two_smul k, ← singularCohomologyTorusTwoEquiv_apply,
    LinearEquiv.map_eq_zero_iff]
  exact h2

end TauCeti
