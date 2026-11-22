/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Topology.Category.TopCat.Monoidal
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic

/-!
# The cohomology of `S⁰ × Y`

The zero-sphere `S⁰` (`TopCat.sphere 0`) is the finite discrete two-point space
`{sphereZeroMinus, sphereZeroPlus}` (`TauCeti.sphereZeroMinus`, `TauCeti.sphereZeroPlus`), so
discrete-product additivity (`TopCat.singularCohomology_prod_ext_of_discreteTopology`, via
`TopCat.sigmaConstIsoProd` and `TauCeti.isLimitFanSingularCohomology`) detects classes of
`Hⁿ(S⁰ × Y; R, M)` in any abelian category by their restrictions to the two poles
(`TopCat.singularCohomology_sphereZeroProd_ext`).

Over a commutative ring `k`, let `θ₀ ∈ H⁰(S⁰; k)` be the idempotent indicator class taking value
`1` at `TauCeti.sphereZeroPlus` and `0` at `TauCeti.sphereZeroMinus`
(`TauCeti.singularCohomologyTopCatSphereZeroClass`,
`TauCeti.singularCup_singularCohomologyTopCatSphereZeroClass_self`). For any `k`-module `M`,
`φ ↦ (ι₋^* φ, ι₊^* φ - ι₋^* φ)` and `(b, c) ↦ pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c` form mutually inverse
`k`-linear maps `Hⁿ(S⁰ × Y; M) ≃ₗ[k] Hⁿ(Y; M) × Hⁿ(Y; M)`
(`TopCat.singularCohomologySphereZeroProdEquiv`), the `d = 0` counterpart of
`TopCat.singularCohomologySphereProdSlantEquiv`.

## Main definitions and results

* `TopCat.singularCohomology_sphereZeroProd_ext`: pole restrictions determine classes of
  `Hⁿ(S⁰ × Y)`.
* `TauCeti.singularCohomologyTopCatSphereZeroClass`: the indicator class `θ₀ ∈ H⁰(S⁰; k)`.
* `TopCat.singularCohomologySphereZeroProdEquiv`: `Hⁿ(S⁰ × Y; M) ≃ₗ[k] Hⁿ(Y; M) × Hⁿ(Y; M)`.

## References

* S. Eilenberg, N. Steenrod, *Foundations of Algebraic Topology*, Chapter I, §3.
* A. Hatcher, *Algebraic Topology*, §3.2 and §4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace TopCat

/-- **Classes of `S⁰ × Y` are determined by their restrictions to the two poles.** -/
theorem singularCohomology_sphereZeroProd_ext {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C} (Y : TopCat.{w}) {n : ℕ}
    {φ ψ : (sphere.{w} 0 ⊗ Y).singularCohomology R k M n}
    (hplus : TopCat.singularCohomologyMap
      (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroPlus) n φ =
      TopCat.singularCohomologyMap
        (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroPlus) n ψ)
    (hminus : TopCat.singularCohomologyMap
      (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroMinus) n φ =
      TopCat.singularCohomologyMap
        (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroMinus) n ψ) : φ = ψ := by
  have : Countable (sphere.{w} 0) := Finite.to_countable
  have : Small.{v} (sphere.{w} 0) := Countable.toSmall (sphere.{w} 0)
  refine singularCohomology_prod_ext_of_discreteTopology (sphere.{w} 0) Y fun x ↦ ?_
  rcases TauCeti.eq_sphereZeroMinus_or_eq_sphereZeroPlus x with rfl | rfl
  · exact hminus
  · exact hplus

end TopCat

namespace TauCeti

open scoped Classical in
private theorem exists_sphereZeroClass (k : Type w) [CommRing k] :
    ∃ u : (_root_.TopCat.sphere.{w} 0).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) 0,
      ∀ x : _root_.TopCat.sphere.{w} 0,
        singularCohomologyZeroEval x u = if x = sphereZeroPlus.{w} then (1 : k) else 0 :=
  exists_singularCohomologyZeroEval_eq (X := _root_.TopCat.sphere.{w} 0)
    (fun x ↦ if x = sphereZeroPlus.{w} then (1 : k) else 0) fun _ _ ⟨γ⟩ ↦
      congrArg (fun z : _root_.TopCat.sphere.{w} 0 ↦
        if z = sphereZeroPlus.{w} then (1 : k) else 0)
        (γ.source.symm.trans ((γ.continuous.isConst_of_preconnectedSpace 0 1).trans γ.target))

/-- **The indicator class of the positive pole of `S⁰`**: the degree-zero cohomology class
`θ₀ ∈ H⁰(TopCat.sphere 0; k)` taking value `1` at `TauCeti.sphereZeroPlus` and `0` at
`TauCeti.sphereZeroMinus`. -/
def singularCohomologyTopCatSphereZeroClass (k : Type w) [CommRing k] :
    (_root_.TopCat.sphere.{w} 0).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0 :=
  (exists_sphereZeroClass k).choose

/-- `TauCeti.singularCohomologyTopCatSphereZeroClass` evaluates to `1` at
`TauCeti.sphereZeroPlus`. -/
@[simp]
theorem singularCohomologyZeroEval_sphereZeroPlus_singularCohomologyTopCatSphereZeroClass
    (k : Type w) [CommRing k] :
    singularCohomologyZeroEval sphereZeroPlus.{w}
      (singularCohomologyTopCatSphereZeroClass k) = 1 :=
  ((exists_sphereZeroClass k).choose_spec sphereZeroPlus).trans (by simp)

/-- `TauCeti.singularCohomologyTopCatSphereZeroClass` evaluates to `0` at
`TauCeti.sphereZeroMinus`. -/
@[simp]
theorem singularCohomologyZeroEval_sphereZeroMinus_singularCohomologyTopCatSphereZeroClass
    (k : Type w) [CommRing k] :
    singularCohomologyZeroEval sphereZeroMinus.{w}
      (singularCohomologyTopCatSphereZeroClass k) = 0 :=
  ((exists_sphereZeroClass k).choose_spec sphereZeroMinus).trans
    (by simp [sphereZeroMinus_ne_sphereZeroPlus])

/-- The indicator class `θ₀ ∈ H⁰(S⁰; k)` is idempotent for the cup product: `θ₀ ⌣ θ₀ = θ₀`. -/
@[simp]
theorem singularCup_singularCohomologyTopCatSphereZeroClass_self {k : Type w} [CommRing k] :
    (_root_.TopCat.sphere.{w} 0).singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl
      (singularCohomologyTopCatSphereZeroClass k) (singularCohomologyTopCatSphereZeroClass k) =
    singularCohomologyTopCatSphereZeroClass k := by
  refine singularCohomologyZero_ext fun x ↦ ?_
  rcases eq_sphereZeroMinus_or_eq_sphereZeroPlus x with rfl | rfl <;> simp

end TauCeti

namespace TopCat

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

/-- **The cohomology of `S⁰ × Y`**: `φ ↦ (ι₋^* φ, ι₊^* φ - ι₋^* φ)` is a `k`-linear equivalence
`Hⁿ(S⁰ × Y; M) ≃ₗ[k] Hⁿ(Y; M) × Hⁿ(Y; M)` with inverse `(b, c) ↦ pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`,
where `θ₀ ∈ H⁰(S⁰; k)` is `TauCeti.singularCohomologyTopCatSphereZeroClass`. -/
def singularCohomologySphereZeroProdEquiv (Y : TopCat.{w}) (n : ℕ) :
    (sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n where
  toFun φ :=
    (TopCat.singularCohomologyMap (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroMinus)
        n φ,
      TopCat.singularCohomologyMap (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroPlus) n φ
        - TopCat.singularCohomologyMap
            (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroMinus) n φ)
  map_add' _ _ := by ext <;> simp [sub_add_sub_comm]
  map_smul' _ _ := by ext <;> simp [smul_sub]
  invFun bc := TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
    (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 0 n n (zero_add n)
      (TopCat.singularCohomologyMap (fst _ Y) 0 (TauCeti.singularCohomologyTopCatSphereZeroClass k))
      (TopCat.singularCohomologyMap (snd _ Y) n bc.2)
  left_inv φ := by
    refine singularCohomology_sphereZeroProd_ext Y ?_ ?_ <;>
    · rw [singularCohomologyMap_prodFiberInclusion_add_singularCup]
      simp
  right_inv bc := by
    ext <;> simp [singularCohomologyMap_prodFiberInclusion_add_singularCup]

/-- `TopCat.singularCohomologySphereZeroProdEquiv` sends `φ` to `(ι₋^* φ, ι₊^* φ - ι₋^* φ)`. -/
@[simp]
theorem singularCohomologySphereZeroProdEquiv_apply (Y : TopCat.{w}) (n : ℕ)
    (φ : (sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    singularCohomologySphereZeroProdEquiv M Y n φ =
      (TopCat.singularCohomologyMap (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroMinus)
          n φ,
        TopCat.singularCohomologyMap (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroPlus)
            n φ -
          TopCat.singularCohomologyMap (prodFiberInclusion (sphere.{w} 0) Y TauCeti.sphereZeroMinus)
            n φ) := (rfl)

/-- The inverse of `TopCat.singularCohomologySphereZeroProdEquiv` sends `(b, c)` to
`pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`. -/
@[simp]
theorem singularCohomologySphereZeroProdEquiv_symm_apply (Y : TopCat.{w}) (n : ℕ)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    (singularCohomologySphereZeroProdEquiv M Y n).symm bc =
      TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
        (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 0 n n
          (zero_add n) (TopCat.singularCohomologyMap (fst _ Y) 0
            (TauCeti.singularCohomologyTopCatSphereZeroClass k))
          (TopCat.singularCohomologyMap (snd _ Y) n bc.2) := (rfl)

end TopCat

end
