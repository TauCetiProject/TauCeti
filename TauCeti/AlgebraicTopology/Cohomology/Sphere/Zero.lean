/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Sphere.Zero

/-!
# The cohomology of `S⁰ × Y`

Let `k` be a commutative ring and `M` a `k`-module, and write `Hⁿ(Z; M)` for the singular
cohomology of `Z` with coefficients in `M`, computed from the singular chains with coefficients in
`k`. The zero-sphere `S⁰` (`TopCat.sphere 0`) is the discrete two-point space consisting of the
positive pole `1` (`TopCat.sphereZeroPosPole`) and the negative pole `-1`
(`TopCat.sphereZeroNegPole`). Let `θ₀ ∈ H⁰(S⁰; k)` be the indicator class with value `1` at the
positive pole and `0` at the negative pole (`TauCeti.singularCohomologyTopCatSphereZeroClass`).

For every space `Y` and every degree `n`, `S⁰ × Y` is the disjoint union of the two copies of `Y`
embedded at the poles (`TopCat.sphereZeroProdPosι`, `TopCat.sphereZeroProdNegι`). Additivity of
singular cohomology (`TauCeti.isLimitFanSingularCohomology`) therefore detects classes of
`Hⁿ(S⁰ × Y; M)` by their restrictions to the two poles (`TopCat.eq_of_sphereZeroProd_restrict_eq`),
and `(b, c) ↦ pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c` is inverse to `φ ↦ (ι₋^* φ, ι₊^* φ - ι₋^* φ)`, giving
a `k`-linear equivalence `Hⁿ(S⁰ × Y; M) ≃ Hⁿ(Y; M) × Hⁿ(Y; M)`
(`TopCat.singularCohomologySphereZeroProdEquiv`). This is the `d = 0` counterpart of
`TopCat.singularCohomologySphereProdSlantEquiv`.

## Main definitions and results

* `TopCat.sphereZeroPosPole`, `TopCat.sphereZeroNegPole`: the two poles `±1` of `TopCat.sphere 0`.
* `TauCeti.singularCohomologyTopCatSphereZeroClass`: the indicator class `θ₀ ∈ H⁰(S⁰; k)`, taking
  value `1` at `1` and `0` at `-1`.
* `TopCat.eq_of_sphereZeroProd_restrict_eq`: classes of `Hⁿ(S⁰ × Y; R, M)` are determined by their
  restrictions to the two poles.
* `TopCat.singularCohomologySphereZeroProdEquiv`: `Hⁿ(S⁰ × Y; M) ≃ Hⁿ(Y; M) × Hⁿ(Y; M)`, whose
  inverse sends `(b, c)` to `pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`.

## References

* S. Eilenberg, N. Steenrod, *Foundations of Algebraic Topology*, Chapter I, Section 3 (additivity).
* A. Hatcher, *Algebraic Topology*, Section 3.2 (cup products in degree zero) and Section 4.D,
  Theorem 4D.10 (the rank-one product bundle).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe w

namespace TopCat

/-- The positive pole `1` of the zero-sphere `TopCat.sphere 0`. -/
def sphereZeroPosPole : sphere.{w} 0 :=
  ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The negative pole `-1` of the zero-sphere `TopCat.sphere 0`. -/
def sphereZeroNegPole : sphere.{w} 0 :=
  ULift.up ⟨-EuclideanSpace.single 0 1, by simp⟩

/-- The two poles of `TopCat.sphere 0` are distinct. -/
theorem sphereZeroPosPole_ne_negPole :
    (sphereZeroPosPole : sphere.{w} 0) ≠ sphereZeroNegPole := by
  intro h
  have h0 := congrFun
    (congrArg (fun x : sphere.{w} 0 ↦ (x.down : EuclideanSpace ℝ (Fin 1)).ofLp) h) 0
  simp [sphereZeroPosPole, sphereZeroNegPole] at h0
  linarith

/-- Every point of `TopCat.sphere 0` is either the positive pole or the negative pole. -/
theorem sphereZero_eq_pos_or_neg (x : sphere.{w} 0) :
    x = sphereZeroPosPole ∨ x = sphereZeroNegPole := by
  have hx : (x.down : EuclideanSpace ℝ (Fin 1)) ∈
      ({EuclideanSpace.single 0 1, -EuclideanSpace.single 0 1} :
        Set (EuclideanSpace ℝ (Fin 1))) := by
    have hsp := TauCeti.sphere_eq_pair_of_finrank_eq_one
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1)
      (r := 1) (p := EuclideanSpace.single 0 1) (by simp)
    exact hsp ▸ x.down.2
  rcases hx with hx | hx
  · exact Or.inl (ULift.ext (Subtype.ext hx))
  · exact Or.inr (ULift.ext (Subtype.ext hx))

/-- The zero-sphere `TopCat.sphere 0` has the discrete topology. -/
instance discreteTopology_sphereZero : DiscreteTopology (sphere.{w} 0) := by
  have : DiscreteTopology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    TauCeti.discreteTopology_sphere_of_finrank_eq_one (by simp) 0 1
  exact Homeomorph.ulift.symm.discreteTopology

open scoped Classical in
/-- The homeomorphism `ULift Bool ≃ₜ TopCat.sphere 0` sending `true` to the positive pole and
`false` to the negative pole. -/
private def uliftBoolHomeomorphSphereZero : ULift.{w} Bool ≃ₜ sphere.{w} 0 where
  toFun b := cond b.down sphereZeroPosPole sphereZeroNegPole
  invFun x := ULift.up (decide (x = sphereZeroPosPole))
  left_inv := fun ⟨b⟩ ↦ by
    cases b <;> simp [sphereZeroPosPole_ne_negPole.symm]
  right_inv x := by
    rcases sphereZero_eq_pos_or_neg x with rfl | rfl <;>
      simp [sphereZeroPosPole_ne_negPole.symm]
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- The inclusion `Y ⟶ S⁰ × Y` at the positive pole `y ↦ (1, y)`. -/
def sphereZeroProdPosι (Y : TopCat.{w}) : Y ⟶ sphere.{w} 0 ⊗ Y :=
  lift (TopCat.const sphereZeroPosPole) (𝟙 Y)

/-- The inclusion `Y ⟶ S⁰ × Y` at the negative pole `y ↦ (-1, y)`. -/
def sphereZeroProdNegι (Y : TopCat.{w}) : Y ⟶ sphere.{w} 0 ⊗ Y :=
  lift (TopCat.const sphereZeroNegPole) (𝟙 Y)

/-- Composing `TopCat.sphereZeroProdPosι` with the first projection gives the constant map at the
positive pole. -/
@[reassoc (attr := simp)]
theorem sphereZeroProdPosι_fst (Y : TopCat.{w}) :
    sphereZeroProdPosι Y ≫ fst _ Y = TopCat.const sphereZeroPosPole :=
  lift_fst _ _

/-- Composing `TopCat.sphereZeroProdPosι` with the second projection is the identity. -/
@[reassoc (attr := simp)]
theorem sphereZeroProdPosι_snd (Y : TopCat.{w}) :
    sphereZeroProdPosι Y ≫ snd _ Y = 𝟙 Y :=
  lift_snd _ _

/-- Composing `TopCat.sphereZeroProdNegι` with the first projection gives the constant map at the
negative pole. -/
@[reassoc (attr := simp)]
theorem sphereZeroProdNegι_fst (Y : TopCat.{w}) :
    sphereZeroProdNegι Y ≫ fst _ Y = TopCat.const sphereZeroNegPole :=
  lift_fst _ _

/-- Composing `TopCat.sphereZeroProdNegι` with the second projection is the identity. -/
@[reassoc (attr := simp)]
theorem sphereZeroProdNegι_snd (Y : TopCat.{w}) :
    sphereZeroProdNegι Y ≫ snd _ Y = 𝟙 Y :=
  lift_snd _ _

/-- The isomorphism `(Σ _ : ULift Bool, Y) ≅ S⁰ × Y` in `TopCat` identifying `S⁰ × Y` with the
disjoint union of two copies of `Y`. -/
private def sigmaSphereZeroProdIso (Y : TopCat.{w}) :
    TopCat.of (Σ _ : ULift.{w} Bool, Y) ≅ sphere.{w} 0 ⊗ Y where
  hom := ConcreteCategory.ofHom <| ContinuousMap.mk
    (fun p ↦ (uliftBoolHomeomorphSphereZero p.1, p.2))
    (continuous_sigma_iff.2 fun _ ↦ by fun_prop)
  inv := ConcreteCategory.ofHom <| ContinuousMap.mk
    (fun q ↦ ⟨uliftBoolHomeomorphSphereZero.symm q.1, q.2⟩)
    (continuous_prod_of_discrete_left.2 fun a ↦
      (ContinuousMap.sigmaMk (X := fun _ : ULift.{w} Bool ↦ (Y : Type w))
        (uliftBoolHomeomorphSphereZero.symm a)).continuous)
  hom_inv_id := TopCat.ext fun ⟨b, _⟩ ↦ by
    dsimp
    exact Sigma.ext (uliftBoolHomeomorphSphereZero.symm_apply_apply b) .rfl
  inv_hom_id := TopCat.ext fun ⟨a, _⟩ ↦
    Prod.ext (uliftBoolHomeomorphSphereZero.apply_symm_apply a) rfl

private theorem sigmaι_true_comp_sigmaSphereZeroProdIso (Y : TopCat.{w}) :
    sigmaι (fun _ : ULift.{w} Bool ↦ Y) ⟨true⟩ ≫ (sigmaSphereZeroProdIso Y).hom =
      sphereZeroProdPosι Y :=
  TopCat.ext fun y ↦ by
    simp [sigmaSphereZeroProdIso, sphereZeroProdPosι, uliftBoolHomeomorphSphereZero]
    rfl

private theorem sigmaι_false_comp_sigmaSphereZeroProdIso (Y : TopCat.{w}) :
    sigmaι (fun _ : ULift.{w} Bool ↦ Y) ⟨false⟩ ≫ (sigmaSphereZeroProdIso Y).hom =
      sphereZeroProdNegι Y :=
  TopCat.ext fun y ↦ by
    simp [sigmaSphereZeroProdIso, sphereZeroProdNegι, uliftBoolHomeomorphSphereZero]
    rfl

/-- **Classes of `S⁰ × Y` are determined by their restrictions to the two poles.** -/
theorem eq_of_sphereZeroProd_restrict_eq {k : Type w} [CommRing k] {R M : ModuleCat.{w} k}
    (Y : TopCat.{w}) {n : ℕ}
    {φ ψ : (sphere.{w} 0 ⊗ Y).singularCohomology R k M n}
    (hpos : TopCat.singularCohomologyMap (sphereZeroProdPosι Y) n φ =
      TopCat.singularCohomologyMap (sphereZeroProdPosι Y) n ψ)
    (hneg : TopCat.singularCohomologyMap (sphereZeroProdNegι Y) n φ =
      TopCat.singularCohomologyMap (sphereZeroProdNegι Y) n ψ) :
    φ = ψ := by
  let e := sigmaSphereZeroProdIso Y
  let L := TauCeti.isLimitFanSingularCohomology (fun _ : ULift.{w} Bool ↦ Y)
    (ModuleCat.{w} k) R k M n
  let φ' := TopCat.singularCohomologyMap e.hom n φ
  let ψ' := TopCat.singularCohomologyMap e.hom n ψ
  have hL : ModuleCat.ofHom (LinearMap.toSpanSingleton k _ φ') =
      ModuleCat.ofHom (LinearMap.toSpanSingleton k _ ψ') := by
    refine L.hom_ext fun ⟨⟨b⟩⟩ ↦ ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    cases b
    · dsimp only [Fan.proj, Fan.mk_pt, Fan.mk_π_app, φ', ψ', e]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        LinearMap.toSpanSingleton_apply, one_smul,
        ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        LinearMap.toSpanSingleton_apply, one_smul,
        ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, sigmaι_false_comp_sigmaSphereZeroProdIso]
      exact hneg
    · dsimp only [Fan.proj, Fan.mk_pt, Fan.mk_π_app, φ', ψ', e]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        LinearMap.toSpanSingleton_apply, one_smul,
        ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        LinearMap.toSpanSingleton_apply, one_smul,
        ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, sigmaι_true_comp_sigmaSphereZeroProdIso]
      exact hpos
  have heq : φ' = ψ' := by
    have h1 := congrArg (fun f ↦ f.hom (1 : k)) hL
    simpa [LinearMap.toSpanSingleton_apply] using h1
  have hinv : ∀ z : (sphere.{w} 0 ⊗ Y).singularCohomology R k M n,
      TopCat.singularCohomologyMap e.inv n (TopCat.singularCohomologyMap e.hom n z) = z := by
    intro z
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, Iso.inv_hom_id,
      TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  rw [← hinv φ, ← hinv ψ]
  exact congrArg (TopCat.singularCohomologyMap e.inv n) heq

end TopCat

namespace TauCeti

open scoped Classical in
private theorem exists_sphereZeroClass (k : Type w) [CommRing k] :
    ∃ u : (_root_.TopCat.sphere.{w} 0).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) 0,
      ∀ x : _root_.TopCat.sphere.{w} 0,
        singularCohomologyZeroEval x u =
          if x = _root_.TopCat.sphereZeroPosPole then (1 : k) else 0 :=
  exists_singularCohomologyZeroEval_eq (X := _root_.TopCat.sphere.{w} 0)
    (fun x ↦ if x = _root_.TopCat.sphereZeroPosPole then (1 : k) else 0)
    fun x y h ↦ by
      have hxy : x = y :=
        ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace (Quotient.sound h)
      rw [hxy]

/-- **The indicator class of the positive pole of `S⁰`**: the degree-zero cohomology class
`θ₀ ∈ H⁰(TopCat.sphere 0; k)` taking value `1` at `TopCat.sphereZeroPosPole` and `0` at
`TopCat.sphereZeroNegPole`. -/
def singularCohomologyTopCatSphereZeroClass (k : Type w) [CommRing k] :
    (_root_.TopCat.sphere.{w} 0).singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0 :=
  (exists_sphereZeroClass k).choose

/-- `TauCeti.singularCohomologyTopCatSphereZeroClass` evaluates to `1` at the positive pole. -/
@[simp]
theorem singularCohomologyZeroEval_singularCohomologyTopCatSphereZeroClass_pos
    (k : Type w) [CommRing k] :
    singularCohomologyZeroEval _root_.TopCat.sphereZeroPosPole
      (singularCohomologyTopCatSphereZeroClass k) = 1 := by
  classical
  simpa [singularCohomologyTopCatSphereZeroClass] using
    (exists_sphereZeroClass k).choose_spec _root_.TopCat.sphereZeroPosPole

/-- `TauCeti.singularCohomologyTopCatSphereZeroClass` evaluates to `0` at the negative pole. -/
@[simp]
theorem singularCohomologyZeroEval_singularCohomologyTopCatSphereZeroClass_neg
    (k : Type w) [CommRing k] :
    singularCohomologyZeroEval _root_.TopCat.sphereZeroNegPole
      (singularCohomologyTopCatSphereZeroClass k) = 0 := by
  classical
  simpa [singularCohomologyTopCatSphereZeroClass,
    _root_.TopCat.sphereZeroPosPole_ne_negPole.symm] using
    (exists_sphereZeroClass k).choose_spec _root_.TopCat.sphereZeroNegPole

end TauCeti

namespace TopCat

variable {k : Type w} [CommRing k] (M : ModuleCat.{w} k)

private theorem singularCohomologyMap_sphereZeroProdPosι_cup (Y : TopCat.{w}) (n : ℕ)
    (b c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (sphereZeroProdPosι Y) n
        (TopCat.singularCohomologyMap (snd _ Y) n b +
          (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
            0 n n (zero_add n)
            (TopCat.singularCohomologyMap (fst _ Y) 0
              (TauCeti.singularCohomologyTopCatSphereZeroClass k))
            (TopCat.singularCohomologyMap (snd _ Y) n c)) =
      b + c := by
  rw [map_add, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    sphereZeroProdPosι_snd, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    ← TopCat.singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, sphereZeroProdPosι_fst,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, sphereZeroProdPosι_snd,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    TauCeti.singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
    TauCeti.singularCohomologyZeroEval_singularCohomologyTopCatSphereZeroClass_pos, one_smul,
    TopCat.singularCohomologyZeroOne_def,
    Y.singularCup_constSingularCocycle_left k (η := 𝟙 _) (by monoidal) (by monoidal) (zero_add n)]

private theorem singularCohomologyMap_sphereZeroProdNegι_cup (Y : TopCat.{w}) (n : ℕ)
    (b c : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    TopCat.singularCohomologyMap (sphereZeroProdNegι Y) n
        (TopCat.singularCohomologyMap (snd _ Y) n b +
          (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
            0 n n (zero_add n)
            (TopCat.singularCohomologyMap (fst _ Y) 0
              (TauCeti.singularCohomologyTopCatSphereZeroClass k))
            (TopCat.singularCohomologyMap (snd _ Y) n c)) =
      b := by
  rw [map_add, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    sphereZeroProdNegι_snd, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    ← TopCat.singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, sphereZeroProdNegι_fst,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, sphereZeroProdNegι_snd,
    TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
    TauCeti.singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul,
    TauCeti.singularCohomologyZeroEval_singularCohomologyTopCatSphereZeroClass_neg, zero_smul,
    map_zero, LinearMap.zero_apply, add_zero]

/-- **The cohomology of `S⁰ × Y`**: restricting to the negative pole and taking the difference of
restrictions to the positive and negative poles gives a `k`-linear equivalence
`Hⁿ(S⁰ × Y; M) ≃ Hⁿ(Y; M) × Hⁿ(Y; M)`. Its inverse sends `(b, c)` to
`pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`, where `θ₀ ∈ H⁰(S⁰; k)` is the indicator class of the positive pole
(`TauCeti.singularCohomologyTopCatSphereZeroClass`). -/
def singularCohomologySphereZeroProdEquiv (Y : TopCat.{w}) (n : ℕ) :
    (sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ≃ₗ[k]
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
        Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n where
  toFun φ :=
    (TopCat.singularCohomologyMap (sphereZeroProdNegι Y) n φ,
      TopCat.singularCohomologyMap (sphereZeroProdPosι Y) n φ -
        TopCat.singularCohomologyMap (sphereZeroProdNegι Y) n φ)
  map_add' φ ψ := by
    ext <;> simp [sub_add_sub_comm]
  map_smul' r φ := by
    ext <;> simp [smul_sub]
  invFun bc :=
    TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
      (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
        0 n n (zero_add n)
        (TopCat.singularCohomologyMap (fst _ Y) 0
          (TauCeti.singularCohomologyTopCatSphereZeroClass k))
        (TopCat.singularCohomologyMap (snd _ Y) n bc.2)
  left_inv φ := by
    apply eq_of_sphereZeroProd_restrict_eq Y
    · rw [singularCohomologyMap_sphereZeroProdPosι_cup, add_sub_cancel]
    · rw [singularCohomologyMap_sphereZeroProdNegι_cup]
  right_inv bc := by
    dsimp only
    ext
    · exact singularCohomologyMap_sphereZeroProdNegι_cup M Y n bc.1 bc.2
    · rw [singularCohomologyMap_sphereZeroProdPosι_cup,
        singularCohomologyMap_sphereZeroProdNegι_cup, add_sub_cancel_left]

/-- `TopCat.singularCohomologySphereZeroProdEquiv` sends `φ` to `(ι₋^* φ, ι₊^* φ - ι₋^* φ)`. -/
@[simp]
theorem singularCohomologySphereZeroProdEquiv_apply (Y : TopCat.{w}) (n : ℕ)
    (φ : (sphere.{w} 0 ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    singularCohomologySphereZeroProdEquiv M Y n φ =
      (TopCat.singularCohomologyMap (sphereZeroProdNegι Y) n φ,
        TopCat.singularCohomologyMap (sphereZeroProdPosι Y) n φ -
          TopCat.singularCohomologyMap (sphereZeroProdNegι Y) n φ) :=
  (rfl)

/-- The inverse of `TopCat.singularCohomologySphereZeroProdEquiv` sends `(b, c)` to
`pr₂^* b + pr₁^* θ₀ ⌣ pr₂^* c`. -/
@[simp]
theorem singularCohomologySphereZeroProdEquiv_symm_apply (Y : TopCat.{w}) (n : ℕ)
    (bc : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n ×
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k M n) :
    (singularCohomologySphereZeroProdEquiv M Y n).symm bc =
      TopCat.singularCohomologyMap (snd _ Y) n bc.1 +
        (sphere.{w} 0 ⊗ Y).singularCup k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ M).hom
          0 n n (zero_add n)
          (TopCat.singularCohomologyMap (fst _ Y) 0
            (TauCeti.singularCohomologyTopCatSphereZeroClass k))
          (TopCat.singularCohomologyMap (snd _ Y) n bc.2) :=
  (rfl)

end TopCat
