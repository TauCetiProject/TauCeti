/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import TauCeti.AlgebraicTopology.Disk
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic

/-!
# The cohomology of `S⁰ × Y`

The zero-sphere `S⁰` (`TopCat.sphere 0`) is the discrete two-point space `{sphereMinus, spherePlus}`
(`TauCeti.sphereMinus`, `TauCeti.spherePlus`), so `S⁰ × Y` is the disjoint union of two copies of
`Y` embedded at the poles (`TopCat.sphereZeroProdPlusι`, `TopCat.sphereZeroProdMinusι`,
`TopCat.sigmaSphereZeroProdIso`). Additivity (`TauCeti.isLimitFanSingularCohomology`) therefore
detects classes of `Hⁿ(S⁰ × Y; R, M)` in any abelian category by their restrictions to the two poles
(`TopCat.eq_of_sphereZeroProd_restrict_eq`).

Over a commutative ring `k`, let `θ₀ ∈ H⁰(S⁰; k)` be the idempotent indicator class taking value
`1` at `TauCeti.spherePlus` and `0` at `TauCeti.sphereMinus`
(`TauCeti.singularCohomologyTopCatSphereZeroClass`). For any `k`-module `M`,
`φ ↦ (ι₋^* φ, ι₊^* φ - ι₋^* φ)` and `(b, c) ↦ pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c` form mutually inverse
`k`-linear maps `Hⁿ(S⁰ × Y; M) ≃ₗ[k] Hⁿ(Y; M) × Hⁿ(Y; M)`
(`TopCat.singularCohomologySphereZeroProdEquiv`), the `d = 0` counterpart of
`TopCat.singularCohomologySphereProdSlantEquiv`.

## Main definitions and results

* `TopCat.eq_of_sphereZeroProd_restrict_eq`: pole restrictions determine classes of `Hⁿ(S⁰ × Y)`.
* `TauCeti.singularCohomologyTopCatSphereZeroClass`: the indicator class `θ₀ ∈ H⁰(S⁰; k)`.
* `TopCat.singularCohomologyMap_sphereZeroProdPlusι_add_singularCup`,
  `TopCat.singularCohomologyMap_sphereZeroProdMinusι_add_singularCup`: pole restrictions of
  `pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`.
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
theorem eq_of_sphereZeroProd_restrict_eq {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
    [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C} (Y : TopCat.{w}) {n : ℕ}
    {φ ψ : (sphere.{w} 0 ⊗ Y).singularCohomology R k M n}
    (hplus : TopCat.singularCohomologyMap (sphereZeroProdPlusι Y) n φ =
      TopCat.singularCohomologyMap (sphereZeroProdPlusι Y) n ψ)
    (hminus : TopCat.singularCohomologyMap (sphereZeroProdMinusι Y) n φ =
      TopCat.singularCohomologyMap (sphereZeroProdMinusι Y) n ψ) : φ = ψ := by
  have : Small.{v} (ULift.{w} Bool) := ⟨⟨ULift.{v} Bool, ⟨Equiv.ulift.trans Equiv.ulift.symm⟩⟩⟩
  have : PreservesLimitsOfShape (Discrete (ULift.{w} Bool)) (forget (ModuleCat.{v} k)) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink.{v} (ULift.{w} Bool))).symm _
  let e := sigmaSphereZeroProdIso Y
  let L := TauCeti.isLimitFanSingularCohomology (fun _ : ULift.{w} Bool ↦ Y) C R k M n
  have heq : TopCat.singularCohomologyMap e.hom n φ = TopCat.singularCohomologyMap e.hom n ψ :=
    Concrete.isLimit_ext _ L _ _ fun ⟨⟨b⟩⟩ ↦ by
      dsimp only [Fan.mk_pt, Fan.mk_π_app]
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp]
      cases b
      · rwa [sigmaι_false_comp_sigmaSphereZeroProdIso_hom]
      · rwa [sigmaι_true_comp_sigmaSphereZeroProdIso_hom]
  have hinv (z : (sphere.{w} 0 ⊗ Y).singularCohomology R k M n) :
      TopCat.singularCohomologyMap e.inv n (TopCat.singularCohomologyMap e.hom n z) = z := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, Iso.inv_hom_id,
      TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  rw [← hinv φ, ← hinv ψ, heq]

end TopCat

namespace TauCeti

open scoped Classical in
private theorem exists_sphereZeroClass (k : Type w) [CommRing k] :
    ∃ u : (_root_.TopCat.sphere.{w} 0).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) 0,
      ∀ x : _root_.TopCat.sphere.{w} 0,
        singularCohomologyZeroEval x u = if x.down = spherePlus.{w}.down then (1 : k) else 0 :=
  exists_singularCohomologyZeroEval_eq (X := _root_.TopCat.sphere.{w} 0)
    (fun x ↦ if x.down = spherePlus.{w}.down then (1 : k) else 0) fun _ _ ⟨γ⟩ ↦
      congrArg (fun z : _root_.TopCat.sphere.{w} 0 ↦
        if z.down = spherePlus.{w}.down then (1 : k) else 0)
        (γ.source.symm.trans ((γ.continuous.isConst_of_preconnectedSpace 0 1).trans γ.target))

/-- **The indicator class of the positive pole of `S⁰`**: the degree-zero cohomology class
`θ₀ ∈ H⁰(TopCat.sphere 0; k)` taking value `1` at `TauCeti.spherePlus` and `0` at
`TauCeti.sphereMinus`. -/
def singularCohomologyTopCatSphereZeroClass (k : Type w) [CommRing k] :
    (_root_.TopCat.sphere.{w} 0).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0 :=
  (exists_sphereZeroClass k).choose

/-- `TauCeti.singularCohomologyTopCatSphereZeroClass` evaluates to `1` at `TauCeti.spherePlus`. -/
@[simp]
theorem singularCohomologyZeroEval_spherePlus_singularCohomologyTopCatSphereZeroClass
    (k : Type w) [CommRing k] :
    singularCohomologyZeroEval (spherePlus : _root_.TopCat.sphere.{w} 0)
      (singularCohomologyTopCatSphereZeroClass k) = 1 :=
  ((exists_sphereZeroClass k).choose_spec spherePlus).trans (by simp)

/-- `TauCeti.singularCohomologyTopCatSphereZeroClass` evaluates to `0` at `TauCeti.sphereMinus`. -/
@[simp]
theorem singularCohomologyZeroEval_sphereMinus_singularCohomologyTopCatSphereZeroClass
    (k : Type w) [CommRing k] :
    singularCohomologyZeroEval (sphereMinus : _root_.TopCat.sphere.{w} 0)
      (singularCohomologyTopCatSphereZeroClass k) = 0 :=
  ((exists_sphereZeroClass k).choose_spec sphereMinus).trans
    (by simp [mt ULift.ext sphereMinus_ne_spherePlus.{w}])

end TauCeti

namespace TopCat

variable {k : Type w} [CommRing k]

/-- The indicator class `θ₀ ∈ H⁰(S⁰; k)` is idempotent for the cup product: `θ₀ ⌣ θ₀ = θ₀`. -/
@[simp]
theorem singularCup_singularCohomologyTopCatSphereZeroClass_self :
    (sphere.{w} 0).singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl
      (TauCeti.singularCohomologyTopCatSphereZeroClass k)
      (TauCeti.singularCohomologyTopCatSphereZeroClass k) =
    TauCeti.singularCohomologyTopCatSphereZeroClass k := by
  refine TauCeti.singularCohomologyZero_ext fun x ↦ ?_
  rw [TauCeti.singularCohomologyZeroEval_singularCup]
  rcases TauCeti.eq_sphereMinus_or_eq_spherePlus x with hx | hx
  · simp [(congrArg (TauCeti.singularCohomologyZeroEval · _) hx).trans
      (TauCeti.singularCohomologyZeroEval_sphereMinus_singularCohomologyTopCatSphereZeroClass k)]
  · simp [(congrArg (TauCeti.singularCohomologyZeroEval · _) hx).trans
      (TauCeti.singularCohomologyZeroEval_spherePlus_singularCohomologyTopCatSphereZeroClass k)]

variable (M : ModuleCat.{w} k)

/-- Restricting `pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c` to the positive pole of `S⁰ × Y` yields `b + c`. -/
theorem singularCohomologyMap_sphereZeroProdPlusι_add_singularCup (Y : TopCat.{w}) (n : ℕ)
    (b c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (sphereZeroProdPlusι Y) n
        (TopCat.singularCohomologyMap (snd _ Y) n b +
          (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 0 n n
            (zero_add n) (TopCat.singularCohomologyMap (fst _ Y) 0
              (TauCeti.singularCohomologyTopCatSphereZeroClass k))
            (TopCat.singularCohomologyMap (snd _ Y) n c)) = b + c := by
  let p : sphere.{w} 0 := TauCeti.spherePlus
  have hfst : sphereZeroProdPlusι Y ≫ fst (sphere.{w} 0) Y = TopCat.const p :=
    sphereZeroProdPlusι_fst Y
  have heval : TauCeti.singularCohomologyZeroEval p
      (TauCeti.singularCohomologyTopCatSphereZeroClass k) = 1 :=
    TauCeti.singularCohomologyZeroEval_spherePlus_singularCohomologyTopCatSphereZeroClass k
  rw [map_add, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    sphereZeroProdPlusι_snd, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    ← TopCat.singularCup_naturality, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, hfst,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, sphereZeroProdPlusι_snd,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    TauCeti.singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, heval, one_smul,
    TopCat.singularCohomologyZeroOne_def,
    Y.singularCup_constSingularCocycle_left k (η := 𝟙 _) (by monoidal) (by monoidal) (zero_add n)]

/-- Restricting `pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c` to the negative pole of `S⁰ × Y` yields `b`. -/
theorem singularCohomologyMap_sphereZeroProdMinusι_add_singularCup (Y : TopCat.{w}) (n : ℕ)
    (b c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (sphereZeroProdMinusι Y) n
        (TopCat.singularCohomologyMap (snd _ Y) n b +
          (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 0 n n
            (zero_add n) (TopCat.singularCohomologyMap (fst _ Y) 0
              (TauCeti.singularCohomologyTopCatSphereZeroClass k))
            (TopCat.singularCohomologyMap (snd _ Y) n c)) = b := by
  let p : sphere.{w} 0 := TauCeti.sphereMinus
  have hfst : sphereZeroProdMinusι Y ≫ fst (sphere.{w} 0) Y = TopCat.const p :=
    sphereZeroProdMinusι_fst Y
  have heval : TauCeti.singularCohomologyZeroEval p
      (TauCeti.singularCohomologyTopCatSphereZeroClass k) = 0 :=
    TauCeti.singularCohomologyZeroEval_sphereMinus_singularCohomologyTopCatSphereZeroClass k
  rw [map_add, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    sphereZeroProdMinusι_snd, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    ← TopCat.singularCup_naturality, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, hfst,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, sphereZeroProdMinusι_snd,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    TauCeti.singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, heval,
    zero_smul, map_zero, LinearMap.zero_apply, add_zero]

/-- **The cohomology of `S⁰ × Y`**: `φ ↦ (ι₋^* φ, ι₊^* φ - ι₋^* φ)` is a `k`-linear equivalence
`Hⁿ(S⁰ × Y; M) ≃ₗ[k] Hⁿ(Y; M) × Hⁿ(Y; M)` with inverse `(b, c) ↦ pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`,
where `θ₀ ∈ H⁰(S⁰; k)` is `TauCeti.singularCohomologyTopCatSphereZeroClass`. -/
def singularCohomologySphereZeroProdEquiv (Y : TopCat.{w}) (n : ℕ) :
    (sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n where
  toFun φ := (TopCat.singularCohomologyMap (sphereZeroProdMinusι Y) n φ,
    TopCat.singularCohomologyMap (sphereZeroProdPlusι Y) n φ -
      TopCat.singularCohomologyMap (sphereZeroProdMinusι Y) n φ)
  map_add' _ _ := by ext <;> simp [sub_add_sub_comm]
  map_smul' _ _ := by ext <;> simp [smul_sub]
  invFun bc := TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
    (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom 0 n n (zero_add n)
      (TopCat.singularCohomologyMap (fst _ Y) 0 (TauCeti.singularCohomologyTopCatSphereZeroClass k))
      (TopCat.singularCohomologyMap (snd _ Y) n bc.2)
  left_inv φ := by
    refine eq_of_sphereZeroProd_restrict_eq Y ?_
      (singularCohomologyMap_sphereZeroProdMinusι_add_singularCup M Y n _ _)
    rw [singularCohomologyMap_sphereZeroProdPlusι_add_singularCup, add_sub_cancel]
  right_inv bc := by
    ext
    · exact singularCohomologyMap_sphereZeroProdMinusι_add_singularCup M Y n bc.1 bc.2
    · dsimp only
      rw [singularCohomologyMap_sphereZeroProdPlusι_add_singularCup,
        singularCohomologyMap_sphereZeroProdMinusι_add_singularCup, add_sub_cancel_left]

/-- `TopCat.singularCohomologySphereZeroProdEquiv` sends `φ` to `(ι₋^* φ, ι₊^* φ - ι₋^* φ)`. -/
@[simp]
theorem singularCohomologySphereZeroProdEquiv_apply (Y : TopCat.{w}) (n : ℕ)
    (φ : (sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    singularCohomologySphereZeroProdEquiv M Y n φ =
      (TopCat.singularCohomologyMap (sphereZeroProdMinusι Y) n φ,
        TopCat.singularCohomologyMap (sphereZeroProdPlusι Y) n φ -
          TopCat.singularCohomologyMap (sphereZeroProdMinusι Y) n φ) := (rfl)

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
