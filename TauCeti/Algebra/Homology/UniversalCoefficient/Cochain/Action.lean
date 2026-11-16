/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Ext.WithAction
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
public import TauCeti.CategoryTheory.Preadditive.Endomorphism
public import TauCeti.CategoryTheory.Preadditive.HomWithAction
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Target scalar actions on `linearHomComplex` and the `R`-linear universal coefficient theorem

Let `C` be a `k`-linear category, `K : CochainComplex C ℤ`, and `Y : C` an object with an action
`ρ : R →+* End Y` of a semiring `R`. Postcomposition with `(ρ r).asHom` induces compatible left
`R`-actions on degree-`i` cochains into `Y[0]` (`TauCeti.CochainSingle₀WithAction`, identified
`R`-linearly with `TauCeti.HomWithAction ρ (K.X (-i))` by `TauCeti.toSingleLinearEquivWithAction`,
assembling for a ring `R` into `TauCeti.linearHomComplexSingle₀WithAction` in `ModuleCat R`), on
cohomology `Hⁱ(Hom(K, Y[0]))` (`TauCeti.HomologySingle₀WithAction`, identified `R`-linearly with
`(linearHomComplexSingle₀WithAction k K ρ).homology i` by
`TauCeti.linearHomComplexSingle₀WithActionHomologyEquiv`), and on `Ext¹(Hʲ(K), Y)`
(`TauCeti.Abelian.ExtWithAction`).

When `C` is abelian with `HasExt C`, `k` is commutative, `i + j = 1`, `K.cycles j` is projective,
and `K.iCycles j` and `K.iCycles (-i)` split, naturality of `cochainKronecker`,
`cochainKroneckerSection`, and `cochainExtToHomology` in `Y` upgrades the universal coefficient
decomposition `R`-linearly to
`HomologySingle₀WithAction k K ρ i ≃ₗ[R] ExtWithAction ρ (K.homology j) 1 ×
  HomWithAction ρ (K.homology (-i))`
(`TauCeti.cochainUniversalCoefficientEquivWithAction`).

## Main definitions and results

* `TauCeti.linearHomComplexSingle₀Action`, `TauCeti.CochainSingle₀WithAction`,
  `TauCeti.toSingleLinearEquivWithAction`, `TauCeti.linearHomComplexSingle₀WithAction`,
  `TauCeti.linearHomComplexSingle₀WithActionHomologyEquiv`, `TauCeti.HomologySingle₀WithAction`,
  and `HomologySingle₀WithAction.precompLinearMap`.
* `TauCeti.cochainKroneckerWithAction`, `TauCeti.cochainKroneckerEquivWithAction`,
  `TauCeti.cochainKroneckerEquivOfProjectiveHomologyWithAction`,
  `TauCeti.cochainKroneckerSectionWithAction`, `TauCeti.cochainExtToHomologyWithAction`, and
  `TauCeti.cochainUniversalCoefficientEquivWithAction`.

## Implementation notes

The `@[expose]` target-action type-synonym pattern used by `TauCeti.CochainSingle₀WithAction` and
`TauCeti.HomologySingle₀WithAction` (as well as `TauCeti.HomWithAction` in
`TauCeti/CategoryTheory/Preadditive/HomWithAction.lean`) adapts the design of
`TauCeti.Abelian.ExtWithAction` in `TauCeti/Algebra/Homology/DerivedCategory/Ext/WithAction.lean`
(Axel Delaval, Jie Xu, Shitan Xu).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex Opposite
  Abelian

universe w v u

namespace TauCeti

open TauCeti.Abelian

section ComplexAction

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {k : Type*} [Ring k] [Linear k C]
  {R : Type*} [Semiring R] {Y : C}

variable (k) in
/-- The ring homomorphism `R →+* End (linearHomComplex k K ((singleFunctor C 0).obj Y))` induced by
`ρ : R →+* End Y` through functorial postcomposition. -/
def linearHomComplexSingle₀Action (K : CochainComplex C ℤ) (ρ : R →+* End Y) :
    R →+* End (linearHomComplex k K ((singleFunctor C 0).obj Y)) :=
  ((singleFunctor C 0 ⋙ (linearHomComplexFunctor k).obj (op K)).mapEndRingHom Y).comp ρ

@[simp]
lemma linearHomComplexSingle₀Action_apply_asHom (K : CochainComplex C ℤ)
    (ρ : R →+* End Y) (r : R) :
    (linearHomComplexSingle₀Action k K ρ r).asHom =
      linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom) :=
  Functor.mapEndRingHom_apply_asHom
    (singleFunctor C 0 ⋙ (linearHomComplexFunctor k).obj (op K)) Y (ρ r)

variable (k) in
/-- `(linearHomComplex k K ((singleFunctor C 0).obj Y)).X i` with the left `R`-module structure
induced by `ρ : R →+* End Y`. -/
-- Expose the synonym so cochain operations compute directly on the underlying carrier.
@[expose]
def CochainSingle₀WithAction (K : CochainComplex C ℤ) (_ρ : R →+* End Y) (i : ℤ) : Type v :=
  (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i

namespace CochainSingle₀WithAction

instance (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    AddCommGroup (CochainSingle₀WithAction k K ρ i) :=
  inferInstanceAs (AddCommGroup ((linearHomComplex k K ((singleFunctor C 0).obj Y)).X i))

variable (k) in
/-- The action of `R` on degree-`i` cochains into `Y[0]` induced by `ρ`, as a ring homomorphism to
`k`-linear endomorphisms. -/
def smulEnd (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    R →+* Module.End k (Cochain K ((singleFunctor C 0).obj Y) i) :=
  (ModuleCat.endRingEquiv _).toRingHom.comp
    (((HomologicalComplex.eval _ _ i).mapEndRingHom _).comp
      (linearHomComplexSingle₀Action k K ρ))

@[simp]
lemma smulEnd_apply {K : CochainComplex C ℤ} (ρ : R →+* End Y) (i : ℤ) (r : R) :
    smulEnd k K ρ i r =
      ((linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).f i).hom := by
  simp only [smulEnd, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, ModuleCat.endRingEquiv_apply,
    Functor.mapEndRingHom_apply_asHom, linearHomComplexSingle₀Action_apply_asHom,
    HomologicalComplex.eval_map]

instance (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    Module R (CochainSingle₀WithAction k K ρ i) :=
  Module.compHom (Cochain K ((singleFunctor C 0).obj Y) i) (smulEnd k K ρ i)

/-- The underlying additive equivalence `CochainSingle₀WithAction k K ρ i ≃+ Cochain K Y[0] i`. -/
def toCochain {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ} :
    CochainSingle₀WithAction k K ρ i ≃+ Cochain K ((singleFunctor C 0).obj Y) i :=
  AddEquiv.refl _

@[simp]
lemma toCochain_smul {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ}
    (r : R) (z : CochainSingle₀WithAction k K ρ i) :
    toCochain ρ (r • z) =
      ((linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).f i).hom
        (toCochain ρ z) :=
  LinearMap.congr_fun (smulEnd_apply (k := k) ρ i r) (toCochain ρ z)

end CochainSingle₀WithAction

variable (k) in
/-- **Degreewise `R`-linear identification of cochains into `Y[0]`**: under
`Cochain.toSingleEquiv (neg_add_cancel i)`, the postcomposition `R`-action agrees with
`HomWithAction ρ (K.X (-i))`. -/
def toSingleLinearEquivWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    CochainSingle₀WithAction k K ρ i ≃ₗ[R] HomWithAction ρ (K.X (-i)) where
  toFun z := (HomWithAction.toHom ρ).symm <|
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
      (CochainSingle₀WithAction.toCochain ρ z)
  invFun f := (CochainSingle₀WithAction.toCochain ρ).symm <|
    (Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)).symm
      (HomWithAction.toHom ρ f)
  left_inv z := by
    simp only [AddEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  right_inv f := by
    simp only [AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  map_add' z₁ z₂ := by simp only [map_add]
  map_smul' r z := (HomWithAction.toHom ρ).injective <| by
    simpa only [AddEquiv.apply_symm_apply, RingHom.id_apply, HomWithAction.toHom_smul,
      CochainSingle₀WithAction.toCochain_smul] using
      toSingleLinearEquiv_linearHomComplexPostcomp_f_apply (k := k) K (ρ r).asHom i
        (CochainSingle₀WithAction.toCochain ρ z)

@[simp]
lemma toHom_toSingleLinearEquivWithAction {K : CochainComplex C ℤ} (ρ : R →+* End Y)
    {i : ℤ} (z : CochainSingle₀WithAction k K ρ i) :
    HomWithAction.toHom ρ (toSingleLinearEquivWithAction k K ρ i z) =
      Cochain.toSingleEquiv (neg_add_cancel i) (CochainSingle₀WithAction.toCochain ρ z) := by
  simp [toSingleLinearEquivWithAction, Cochain.toSingleLinearEquiv]

@[simp]
lemma toCochain_toSingleLinearEquivWithAction_symm {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i : ℤ} (f : HomWithAction ρ (K.X (-i))) :
    CochainSingle₀WithAction.toCochain ρ ((toSingleLinearEquivWithAction k K ρ i).symm f) =
      Cochain.toSingleMk (HomWithAction.toHom ρ f) (neg_add_cancel i) := by
  apply (Cochain.toSingleEquiv (neg_add_cancel i)).injective
  rw [← toHom_toSingleLinearEquivWithAction (k := k) ρ, LinearEquiv.apply_symm_apply,
    Cochain.toSingleEquiv_toSingleMk]

variable (k) in
/-- The `R`-linear differential on `CochainSingle₀WithAction` induced by `linearHomComplex`. -/
def CochainSingle₀WithAction.differential (K : CochainComplex C ℤ)
    (ρ : R →+* End Y) (i j : ℤ) :
    CochainSingle₀WithAction k K ρ i →ₗ[R] CochainSingle₀WithAction k K ρ j where
  toFun z := (CochainSingle₀WithAction.toCochain ρ).symm <|
    ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i j).hom
      (CochainSingle₀WithAction.toCochain ρ z)
  map_add' z₁ z₂ := map_add ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i j).hom
    (CochainSingle₀WithAction.toCochain ρ z₁) (CochainSingle₀WithAction.toCochain ρ z₂)
  map_smul' r z := (CochainSingle₀WithAction.toCochain ρ).injective <| by
    have hcomm := congrArg (fun φ ↦ φ.hom (CochainSingle₀WithAction.toCochain ρ z))
      ((linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).comm i j)
    simpa only [AddEquiv.apply_symm_apply, RingHom.id_apply,
      CochainSingle₀WithAction.toCochain_smul, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, LinearMap.comp_apply] using hcomm

@[simp]
lemma CochainSingle₀WithAction.toCochain_differential_apply {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (z : CochainSingle₀WithAction k K ρ i) :
    CochainSingle₀WithAction.toCochain ρ (CochainSingle₀WithAction.differential k K ρ i j z) =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i j).hom
        (CochainSingle₀WithAction.toCochain ρ z) := (rfl)

lemma CochainSingle₀WithAction.differential_shape (K : CochainComplex C ℤ)
    (ρ : R →+* End Y) (i j : ℤ) (hij : ¬ (ComplexShape.up ℤ).Rel i j) :
    CochainSingle₀WithAction.differential k K ρ i j = 0 := by
  ext z
  apply (CochainSingle₀WithAction.toCochain (k := k) ρ).injective
  simp only [CochainSingle₀WithAction.toCochain_differential_apply (k := k),
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).shape i j hij,
    ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

lemma CochainSingle₀WithAction.differential_comp_differential (K : CochainComplex C ℤ)
    (ρ : R →+* End Y) (i j m : ℤ) :
    (CochainSingle₀WithAction.differential k K ρ j m).comp
      (CochainSingle₀WithAction.differential k K ρ i j) = 0 := by
  ext z
  apply (CochainSingle₀WithAction.toCochain (k := k) ρ).injective
  simp only [LinearMap.comp_apply, CochainSingle₀WithAction.toCochain_differential_apply (k := k),
    ← ModuleCat.comp_apply, HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply,
    map_zero]

variable (k) in
-- The terms must reduce to cochain modules to typecheck `linearHomComplexSingle₀WithAction_d`.
/-- When `R` is a ring, `CochainSingle₀WithAction k K ρ` assembles into a cochain complex in
`ModuleCat R`. -/
@[expose]
def linearHomComplexSingle₀WithAction (K : CochainComplex C ℤ) {R : Type*} [Ring R]
    (ρ : R →+* End Y) : CochainComplex (ModuleCat.{v} R) ℤ where
  X i := ModuleCat.of R (CochainSingle₀WithAction k K ρ i)
  d i j := ModuleCat.ofHom (CochainSingle₀WithAction.differential k K ρ i j)
  shape i j hij := by
    rw [CochainSingle₀WithAction.differential_shape (k := k) K ρ i j hij, ModuleCat.ofHom_zero]
  d_comp_d' i j m _ _ := by
    rw [← ModuleCat.ofHom_comp,
      CochainSingle₀WithAction.differential_comp_differential (k := k) K ρ i j m,
      ModuleCat.ofHom_zero]

@[simp]
lemma linearHomComplexSingle₀WithAction_X {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).X i =
      ModuleCat.of R (CochainSingle₀WithAction k K ρ i) := (rfl)

@[simp]
lemma linearHomComplexSingle₀WithAction_d {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i j : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).d i j =
      ModuleCat.ofHom (CochainSingle₀WithAction.differential k K ρ i j) := (rfl)

variable (k) in
/-- `(linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i` with the left `R`-module
structure induced by `ρ : R →+* End Y` through postcomposition. -/
-- Expose the synonym so cohomology operations compute directly on the underlying carrier.
@[expose]
def HomologySingle₀WithAction (K : CochainComplex C ℤ) (_ρ : R →+* End Y) (i : ℤ) : Type v :=
  (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i

namespace HomologySingle₀WithAction

instance (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    AddCommGroup (HomologySingle₀WithAction k K ρ i) :=
  inferInstanceAs (AddCommGroup ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i))

variable (k) in
/-- The action of `R` on `(linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i` induced by
`ρ`, as a ring homomorphism to `k`-linear endomorphisms. -/
def smulEnd (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    R →+* Module.End k ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :=
  (ModuleCat.endRingEquiv
    ((HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.up ℤ) i).obj
      (linearHomComplex k K ((singleFunctor C 0).obj Y)))).toRingHom.comp
    (((HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.up ℤ) i).mapEndRingHom
      (linearHomComplex k K ((singleFunctor C 0).obj Y))).comp
      (linearHomComplexSingle₀Action k K ρ))

@[simp]
lemma smulEnd_apply {K : CochainComplex C ℤ} (ρ : R →+* End Y) (i : ℤ) (r : R) :
    smulEnd k K ρ i r =
      (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)) i).hom := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.up ℤ) i
  have h : ((ModuleCat.endRingEquiv
      (F.obj (linearHomComplex k K ((singleFunctor C 0).obj Y)))).toRingHom.comp
        ((F.mapEndRingHom (linearHomComplex k K ((singleFunctor C 0).obj Y))).comp
          (linearHomComplexSingle₀Action k K ρ))) r =
      (F.map (linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom))).hom := by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      ModuleCat.endRingEquiv_apply, Functor.mapEndRingHom_apply_asHom]
    exact congrArg (fun φ ↦ (F.map φ).hom) (linearHomComplexSingle₀Action_apply_asHom K ρ r)
  exact h

instance (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    Module R (HomologySingle₀WithAction k K ρ i) :=
  Module.compHom ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) (smulEnd k K ρ i)

/-- The underlying additive equivalence from `HomologySingle₀WithAction k K ρ i` to
`(linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i`. -/
def toHomology {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ} :
    HomologySingle₀WithAction k K ρ i ≃+
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  AddEquiv.refl _

@[simp]
lemma toHomology_smul {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ}
    (r : R) (x : HomologySingle₀WithAction k K ρ i) :
    toHomology ρ (r • x) =
      (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)) i).hom
        (toHomology ρ x) :=
  LinearMap.congr_fun (smulEnd_apply (k := k) ρ i r) (toHomology ρ x)

variable (k) in
/-- Contravariant functoriality of `HomologySingle₀WithAction` along `φ : K₁ ⟶ K₂` is
`R`-linear. -/
def precompLinearMap (ρ : R →+* End Y) {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (i : ℤ) :
    HomologySingle₀WithAction k K₂ ρ i →ₗ[R] HomologySingle₀WithAction k K₁ ρ i where
  toFun x := (toHomology ρ).symm <|
    (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom (toHomology ρ x)
  map_add' x y := map_add
    (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom
    (toHomology ρ x) (toHomology ρ y)
  map_smul' r x := (toHomology ρ).injective <| by
    have hcomm := congrArg
      (fun (ψ : linearHomComplex k K₂ ((singleFunctor C 0).obj Y) ⟶
          linearHomComplex k K₁ ((singleFunctor C 0).obj Y)) ↦
        (homologyMap ψ i).hom (toHomology ρ x))
      (linearHomComplexPrecomp_postcomp_comm k φ ((singleFunctor C 0).map (ρ r).asHom))
    simpa only [AddEquiv.apply_symm_apply, toHomology_smul, RingHom.id_apply,
      HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] using
      hcomm.symm

@[simp]
lemma toHomology_precompLinearMap (ρ : R →+* End Y) {K₁ K₂ : CochainComplex C ℤ}
    (φ : K₁ ⟶ K₂) (i : ℤ) (x : HomologySingle₀WithAction k K₂ ρ i) :
    toHomology ρ (precompLinearMap k ρ φ i x) =
      (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom
        (toHomology ρ x) := (rfl)

end HomologySingle₀WithAction

section ComplexHomologyComparison

variable (k) in
private def toCochainX {K : CochainComplex C ℤ} {R : Type*} [Ring R] (ρ : R →+* End Y) {i : ℤ} :
    (linearHomComplexSingle₀WithAction k K ρ).X i ≃+
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i :=
  CochainSingle₀WithAction.toCochain (k := k) ρ

private lemma toCochainX_d_apply {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) {i j : ℤ} (x : (linearHomComplexSingle₀WithAction k K ρ).X i) :
    toCochainX k ρ ((linearHomComplexSingle₀WithAction k K ρ).d i j x) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).d i j (toCochainX k ρ x) :=
  CochainSingle₀WithAction.toCochain_differential_apply (k := k) ρ x

private lemma toCochainX_smul {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) {i : ℤ} (r : R) (x : (linearHomComplexSingle₀WithAction k K ρ).X i) :
    toCochainX k ρ (r • x) =
      (linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).f i (toCochainX k ρ x) :=
  CochainSingle₀WithAction.toCochain_smul (k := k) ρ r x

variable (k) in
private def toUnderlyingCycle {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i : ℤ)
    (z : (linearHomComplexSingle₀WithAction k K ρ).cycles i) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i :=
  (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCatCyclesMk
    (toCochainX k ρ ((linearHomComplexSingle₀WithAction k K ρ).iCycles i z))
    (i + 1) (by simp) <| by
      rw [← toCochainX_d_apply (k := k) ρ]
      exact (congrArg (toCochainX k ρ)
        ((linearHomComplexSingle₀WithAction k K ρ).moduleCat_d_iCycles_apply i (i + 1) z)).trans
        (map_zero (toCochainX k ρ))

private lemma iCycles_toUnderlyingCycle {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i : ℤ)
    (z : (linearHomComplexSingle₀WithAction k K ρ).cycles i) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i
        (toUnderlyingCycle k ρ i z) =
      toCochainX k ρ ((linearHomComplexSingle₀WithAction k K ρ).iCycles i z) :=
  (linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles_moduleCatCyclesMk i _ _ _ _

variable (k) in
private def linearHomComplexSingle₀WithActionCyclesToHomology (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).cycles i →ₗ[R] HomologySingle₀WithAction k K ρ i where
  toFun z := (HomologySingle₀WithAction.toHomology (k := k) ρ).symm <|
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i (toUnderlyingCycle k ρ i z)
  map_add' z₁ z₂ := (HomologySingle₀WithAction.toHomology (k := k) ρ).injective <| by
    simp only [AddEquiv.apply_symm_apply, map_add]
    rw [← map_add]
    congr 1
    apply (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_iCycles_injective i
    rw [map_add, iCycles_toUnderlyingCycle, iCycles_toUnderlyingCycle, iCycles_toUnderlyingCycle,
      map_add, map_add]
  map_smul' r z := (HomologySingle₀WithAction.toHomology (k := k) ρ).injective <| by
    simp only [AddEquiv.apply_symm_apply, RingHom.id_apply,
      HomologySingle₀WithAction.toHomology_smul, ModuleCat.Hom.hom]
    rw [HomologicalComplex.moduleCat_homologyMap_homologyπ]
    congr 1
    apply (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_iCycles_injective i
    rw [HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
      iCycles_toUnderlyingCycle, iCycles_toUnderlyingCycle, map_smul, toCochainX_smul]

variable (k) in
private lemma linearHomComplexSingle₀WithActionCyclesToHomology_toCycles (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).toCycles (i - 1) i ≫
        ModuleCat.ofHom (linearHomComplexSingle₀WithActionCyclesToHomology k K ρ i) = 0 := by
  let L := linearHomComplex k K ((singleFunctor C 0).obj Y)
  let L' := linearHomComplexSingle₀WithAction k K ρ
  ext y
  apply (HomologySingle₀WithAction.toHomology (k := k) ρ).injective
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero, linearHomComplexSingle₀WithActionCyclesToHomology,
    LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.apply_symm_apply]
  have hcyc : toUnderlyingCycle k ρ i (L'.toCycles (i - 1) i y) =
      L.toCycles (i - 1) i (toCochainX k ρ y) := by
    apply L.moduleCat_iCycles_injective i
    rw [iCycles_toUnderlyingCycle, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
      HomologicalComplex.moduleCat_iCycles_toCycles_apply]
    exact toCochainX_d_apply (k := k) ρ y
  rw [hcyc, L.moduleCat_homologyπ_eq_zero_iff (m := i - 1) (by simp)]
  exact ⟨toCochainX k ρ y, rfl⟩

variable (k) in
private def linearHomComplexSingle₀WithActionHomologyMap (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).homology i ⟶
      ModuleCat.of R (HomologySingle₀WithAction k K ρ i) :=
  (CokernelCofork.IsColimit.desc'
    ((linearHomComplexSingle₀WithAction k K ρ).homologyIsCokernel (i - 1) i (by simp))
    (ModuleCat.ofHom (linearHomComplexSingle₀WithActionCyclesToHomology k K ρ i))
    (linearHomComplexSingle₀WithActionCyclesToHomology_toCycles k K ρ i)).1

variable (k) in
private lemma homologyπ_linearHomComplexSingle₀WithActionHomologyMap (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).homologyπ i ≫
        linearHomComplexSingle₀WithActionHomologyMap k K ρ i =
      ModuleCat.ofHom (linearHomComplexSingle₀WithActionCyclesToHomology k K ρ i) :=
  (CokernelCofork.IsColimit.desc'
    ((linearHomComplexSingle₀WithAction k K ρ).homologyIsCokernel (i - 1) i (by simp))
    (ModuleCat.ofHom (linearHomComplexSingle₀WithActionCyclesToHomology k K ρ i))
    (linearHomComplexSingle₀WithActionCyclesToHomology_toCycles k K ρ i)).2

variable (k) in
private lemma linearHomComplexSingle₀WithActionHomologyMap_bijective (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    Function.Bijective (linearHomComplexSingle₀WithActionHomologyMap k K ρ i).hom := by
  let L := linearHomComplex k K ((singleFunctor C 0).obj Y)
  let L' := linearHomComplexSingle₀WithAction k K ρ
  let f := linearHomComplexSingle₀WithActionHomologyMap k K ρ i
  have hfπ : L'.homologyπ i ≫ f =
      ModuleCat.ofHom (linearHomComplexSingle₀WithActionCyclesToHomology k K ρ i) :=
    homologyπ_linearHomComplexSingle₀WithActionHomologyMap k K ρ i
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := L'.moduleCat_homologyπ_surjective i x
    have h0 : (linearHomComplexSingle₀WithActionCyclesToHomology k K ρ i) z = 0 := by
      have := congrArg (fun g ↦ g z) hfπ
      simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom] using this.symm.trans hx
    have h0' : L.homologyπ i (toUnderlyingCycle k ρ i z) = 0 := by
      simpa only [linearHomComplexSingle₀WithActionCyclesToHomology, LinearMap.coe_mk,
        AddHom.coe_mk, AddEquiv.apply_symm_apply, map_zero] using
        congrArg (HomologySingle₀WithAction.toHomology (k := k) ρ) h0
    obtain ⟨y, hy⟩ := (L.moduleCat_homologyπ_eq_zero_iff (m := i - 1) (by simp) _).1 h0'
    rw [L'.moduleCat_homologyπ_eq_zero_iff (m := i - 1) (by simp)]
    refine ⟨(toCochainX k ρ).symm y, L'.moduleCat_iCycles_injective i ?_⟩
    apply (toCochainX k ρ).injective
    have hy' := congrArg (L.iCycles i) hy
    rw [HomologicalComplex.moduleCat_iCycles_toCycles_apply, iCycles_toUnderlyingCycle] at hy'
    rw [HomologicalComplex.moduleCat_iCycles_toCycles_apply, toCochainX_d_apply (k := k) ρ,
      AddEquiv.apply_symm_apply]
    exact hy'
  · intro x
    obtain ⟨w, hw⟩ := L.moduleCat_homologyπ_surjective i
      (HomologySingle₀WithAction.toHomology (k := k) ρ x)
    let x' : L'.X i := (toCochainX k ρ).symm (L.iCycles i w)
    have hdz : L'.d i (i + 1) x' = 0 := by
      apply (toCochainX k ρ).injective
      rw [toCochainX_d_apply (k := k) ρ, AddEquiv.apply_symm_apply, map_zero]
      exact L.moduleCat_d_iCycles_apply i (i + 1) w
    let z := L'.moduleCatCyclesMk x' (i + 1) (by simp) hdz
    refine ⟨L'.homologyπ i z, (HomologySingle₀WithAction.toHomology (k := k) ρ).injective ?_⟩
    have hcomp := congrArg (fun g ↦ g.hom z) hfπ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      ModuleCat.Hom.hom] at hcomp
    simp only [ModuleCat.Hom.hom]
    rw [hcomp]
    simp only [linearHomComplexSingle₀WithActionCyclesToHomology, LinearMap.coe_mk, AddHom.coe_mk,
      AddEquiv.apply_symm_apply]
    rw [← hw]
    congr 1
    apply L.moduleCat_iCycles_injective i
    rw [iCycles_toUnderlyingCycle]
    have hiz : L'.iCycles i z = x' := L'.iCycles_moduleCatCyclesMk i x' (i + 1) (by simp) hdz
    exact (congrArg (toCochainX k ρ) hiz).trans (AddEquiv.apply_symm_apply _ _)

variable (k) in
/-- **Canonical `R`-linear cohomology comparison** between the `ModuleCat R` cochain complex
`linearHomComplexSingle₀WithAction k K ρ` and `HomologySingle₀WithAction k K ρ i`: taking
cohomology in `ModuleCat R` agrees with equipping the `ModuleCat k` cohomology with the
postcomposition `R`-action. -/
def linearHomComplexSingle₀WithActionHomologyEquiv (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).homology i ≃ₗ[R]
      HomologySingle₀WithAction k K ρ i :=
  LinearEquiv.ofBijective (linearHomComplexSingle₀WithActionHomologyMap k K ρ i).hom
    (linearHomComplexSingle₀WithActionHomologyMap_bijective k K ρ i)

/-- `linearHomComplexSingle₀WithActionHomologyEquiv` sends the cohomology class of a cocycle `z` in
`linearHomComplexSingle₀WithAction` to the cohomology class of the matching cocycle `w` in
`linearHomComplex`. -/
lemma toHomology_linearHomComplexSingle₀WithActionHomologyEquiv_homologyπ
    {K : CochainComplex C ℤ} {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ)
    (z : (linearHomComplexSingle₀WithAction k K ρ).cycles i)
    (w : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hzw : CochainSingle₀WithAction.toCochain (k := k) ρ
        ((linearHomComplexSingle₀WithAction k K ρ).iCycles i z) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i w) :
    HomologySingle₀WithAction.toHomology (k := k) ρ
        (linearHomComplexSingle₀WithActionHomologyEquiv k K ρ i
          ((linearHomComplexSingle₀WithAction k K ρ).homologyπ i z)) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i w := by
  have hcomp := congrArg (fun g ↦ g z)
    (homologyπ_linearHomComplexSingle₀WithActionHomologyMap k K ρ i)
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom] at hcomp
  rw [linearHomComplexSingle₀WithActionHomologyEquiv, LinearEquiv.ofBijective_apply]
  simp only [ModuleCat.Hom.hom, hcomp, linearHomComplexSingle₀WithActionCyclesToHomology,
    LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.apply_symm_apply]
  congr 1
  apply (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_iCycles_injective i
  rw [iCycles_toUnderlyingCycle]
  exact hzw

/-- The inverse of `linearHomComplexSingle₀WithActionHomologyEquiv` sends the cohomology class of a
cocycle `w` in `linearHomComplex` to the cohomology class of the matching cocycle `z` in
`linearHomComplexSingle₀WithAction`. -/
lemma linearHomComplexSingle₀WithActionHomologyEquiv_symm_homologyπ
    {K : CochainComplex C ℤ} {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ)
    (z : (linearHomComplexSingle₀WithAction k K ρ).cycles i)
    (w : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hzw : CochainSingle₀WithAction.toCochain (k := k) ρ
        ((linearHomComplexSingle₀WithAction k K ρ).iCycles i z) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i w) :
    (linearHomComplexSingle₀WithActionHomologyEquiv k K ρ i).symm
        ((HomologySingle₀WithAction.toHomology (k := k) ρ).symm
          ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i w)) =
      (linearHomComplexSingle₀WithAction k K ρ).homologyπ i z := by
  apply (linearHomComplexSingle₀WithActionHomologyEquiv k K ρ i).injective
  apply (HomologySingle₀WithAction.toHomology (k := k) ρ).injective
  rw [LinearEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    toHomology_linearHomComplexSingle₀WithActionHomologyEquiv_homologyπ ρ i z w hzw]

end ComplexHomologyComparison

end ComplexAction

section UniversalCoefficientWithAction

variable {C : Type u} [Category.{v} C] [Abelian C]
  {k : Type*} [Ring k] [Linear k C]
  {R : Type*} [Semiring R] {Y : C}

variable (k) in
/-- **The `R`-linear Kronecker evaluation** for `linearHomComplex` into a target `Y` with
`R`-action `ρ : R →+* End Y`. -/
def cochainKroneckerWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    HomologySingle₀WithAction k K ρ i →ₗ[R] HomWithAction ρ (K.homology (-i)) where
  toFun x := (HomWithAction.toHom ρ).symm <|
    cochainKronecker k K Y i (HomologySingle₀WithAction.toHomology ρ x)
  map_add' x y := by simp only [map_add]
  map_smul' r x := (HomWithAction.toHom ρ).injective <| by
    simp only [AddEquiv.apply_symm_apply, HomWithAction.toHom_smul, RingHom.id_apply,
      HomologySingle₀WithAction.toHomology_smul]
    exact cochainKronecker_coefficient_naturality (ρ r).asHom i _

@[simp]
lemma toHom_cochainKroneckerWithAction {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ}
    (x : HomologySingle₀WithAction k K ρ i) :
    HomWithAction.toHom ρ (cochainKroneckerWithAction k K ρ i x) =
      cochainKronecker k K Y i (HomologySingle₀WithAction.toHomology ρ x) := by
  simp [cochainKroneckerWithAction]

/-- Naturality of `cochainKroneckerWithAction` in the cochain complex `K`. -/
theorem cochainKroneckerWithAction_naturality (ρ : R →+* End Y)
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (i : ℤ)
    (x : HomologySingle₀WithAction k K₂ ρ i) :
    cochainKroneckerWithAction k K₁ ρ i
        (HomologySingle₀WithAction.precompLinearMap k ρ φ i x) =
      HomWithAction.precompLinearMap ρ (homologyMap φ (-i))
        (cochainKroneckerWithAction k K₂ ρ i x) :=
  (HomWithAction.toHom ρ).injective <| by
    simpa only [toHom_cochainKroneckerWithAction, HomWithAction.toHom_precompLinearMap,
      HomologySingle₀WithAction.toHomology_precompLinearMap] using
      cochainKronecker_naturality φ i (HomologySingle₀WithAction.toHomology ρ x)

variable (k) in
/-- When `Y` is injective, `cochainKroneckerWithAction` is an `R`-linear equivalence. -/
def cochainKroneckerEquivWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y)
    [Injective Y] (i : ℤ) :
    HomologySingle₀WithAction k K ρ i ≃ₗ[R] HomWithAction ρ (K.homology (-i)) :=
  LinearEquiv.ofBijective (cochainKroneckerWithAction k K ρ i) <|
    (HomWithAction.toHom ρ).symm.bijective.comp <|
      (cochainKronecker_bijective (k := k) (K := K) (Y := Y) i).comp
        (HomologySingle₀WithAction.toHomology (k := k) ρ).bijective

@[simp]
lemma cochainKroneckerEquivWithAction_apply {K : CochainComplex C ℤ} (ρ : R →+* End Y)
    [Injective Y] (i : ℤ) (x : HomologySingle₀WithAction k K ρ i) :
    cochainKroneckerEquivWithAction k K ρ i x = cochainKroneckerWithAction k K ρ i x := (rfl)

variable (k) in
/-- When `K.homology j` (`i + j = 1`) is projective and the cycle inclusions in degrees `-i` and
`j` split, `cochainKroneckerWithAction` is an `R`-linear equivalence. -/
def cochainKroneckerEquivOfProjectiveHomologyWithAction (K : CochainComplex C ℤ)
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.homology j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] :
    HomologySingle₀WithAction k K ρ i ≃ₗ[R] HomWithAction ρ (K.homology (-i)) :=
  LinearEquiv.ofBijective (cochainKroneckerWithAction k K ρ i) <|
    (HomWithAction.toHom ρ).symm.bijective.comp <|
      (cochainKronecker_bijective_of_projective_homology (k := k) (K := K) (Y := Y) hij).comp
        (HomologySingle₀WithAction.toHomology (k := k) ρ).bijective

@[simp]
lemma cochainKroneckerEquivOfProjectiveHomologyWithAction_apply {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.homology j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (x : HomologySingle₀WithAction k K ρ i) :
    cochainKroneckerEquivOfProjectiveHomologyWithAction k K ρ hij x =
      cochainKroneckerWithAction k K ρ i x := (rfl)

variable (k) in
/-- **The `R`-linear section of `cochainKroneckerWithAction`** associated to a retraction of
`K.iCycles (-i)`. -/
def cochainKroneckerSectionWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    HomWithAction ρ (K.homology (-i)) →ₗ[R] HomologySingle₀WithAction k K ρ i where
  toFun g := (HomologySingle₀WithAction.toHomology ρ).symm <|
    cochainKroneckerSection k K Y i (HomWithAction.toHom ρ g)
  map_add' g₁ g₂ := by simp only [map_add]
  map_smul' r g := (HomologySingle₀WithAction.toHomology ρ).injective <| by
    simp only [AddEquiv.apply_symm_apply, HomologySingle₀WithAction.toHomology_smul,
      RingHom.id_apply, HomWithAction.toHom_smul]
    exact (cochainKroneckerSection_coefficient_naturality (ρ r).asHom i _).symm

@[simp]
lemma toHomology_cochainKroneckerSectionWithAction {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i : ℤ} [IsSplitMono (K.iCycles (-i))]
    (g : HomWithAction ρ (K.homology (-i))) :
    HomologySingle₀WithAction.toHomology ρ (cochainKroneckerSectionWithAction k K ρ i g) =
      cochainKroneckerSection k K Y i (HomWithAction.toHom ρ g) := (rfl)

@[simp]
lemma cochainKroneckerWithAction_cochainKroneckerSectionWithAction {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i : ℤ} [IsSplitMono (K.iCycles (-i))]
    (g : HomWithAction ρ (K.homology (-i))) :
    cochainKroneckerWithAction k K ρ i (cochainKroneckerSectionWithAction k K ρ i g) = g :=
  (HomWithAction.toHom ρ).injective <| by
    simpa only [toHom_cochainKroneckerWithAction,
      toHomology_cochainKroneckerSectionWithAction] using
      cochainKronecker_cochainKroneckerSection (k := k) i (HomWithAction.toHom ρ g)

end UniversalCoefficientWithAction

section ExtWithAction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {k : Type*} [CommRing k] [Linear k C]
  {R : Type*} [Semiring R] {Y : C}

variable (k) in
/-- **The `R`-linear `Ext` inclusion** `Ext¹(Hʲ(K), Y) →ₗ[R] Hⁱ(Hom(K, Y[0]))` (`i + j = 1`) for a
target `Y` with action `ρ : R →+* End Y`, assuming `K.cycles j` is projective and `K.iCycles j`
splits. -/
def cochainExtToHomologyWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y)
    {i j : ℤ} (hij : i + j = 1) [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    ExtWithAction.{w} ρ (K.homology j) 1 →ₗ[R] HomologySingle₀WithAction k K ρ i where
  toFun e := (HomologySingle₀WithAction.toHomology ρ).symm <|
    cochainExtToHomology k K Y hij (ExtWithAction.toExt ρ e)
  map_add' e₁ e₂ := (HomologySingle₀WithAction.toHomology ρ).injective <| by
    simp only [map_add, AddEquiv.apply_symm_apply]
  map_smul' r e := (HomologySingle₀WithAction.toHomology ρ).injective <| by
    simp only [AddEquiv.apply_symm_apply, HomologySingle₀WithAction.toHomology_smul,
      RingHom.id_apply, ExtWithAction.toExt_smul]
    exact cochainExtToHomology_coefficient_naturality (ρ r).asHom hij (ExtWithAction.toExt ρ e)

@[simp]
lemma toHomology_cochainExtToHomologyWithAction {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    (e : ExtWithAction.{w} ρ (K.homology j) 1) :
    HomologySingle₀WithAction.toHomology ρ (cochainExtToHomologyWithAction k K ρ hij e) =
      cochainExtToHomology k K Y hij (ExtWithAction.toExt ρ e) := (rfl)

/-- `cochainExtToHomologyWithAction` is injective. -/
theorem cochainExtToHomologyWithAction_injective {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    Function.Injective (cochainExtToHomologyWithAction.{w} k K ρ hij) := fun e₁ e₂ h ↦
  (ExtWithAction.toExt ρ).injective <|
    cochainExtToHomology_injective (k := k) (K := K) (Y := Y) hij <|
      by simpa only [← toHomology_cochainExtToHomologyWithAction] using
        congrArg (HomologySingle₀WithAction.toHomology ρ) h

/-- Middle exactness of the `R`-linear universal coefficient sequence: the image of
`cochainExtToHomologyWithAction` is the kernel of `cochainKroneckerWithAction`. -/
theorem exact_cochainExtToHomologyWithAction_cochainKroneckerWithAction
    {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    Function.Exact (cochainExtToHomologyWithAction.{w} k K ρ hij)
      (cochainKroneckerWithAction k K ρ i) :=
  Function.Exact.of_ladder_addEquiv_of_exact
    (f₁₂ := (cochainExtToHomology.{w} k K Y hij).toAddMonoidHom)
    (f₂₃ := (cochainKronecker k K Y i).toAddMonoidHom)
    (g₁₂ := (cochainExtToHomologyWithAction.{w} k K ρ hij).toAddMonoidHom)
    (g₂₃ := (cochainKroneckerWithAction k K ρ i).toAddMonoidHom)
    (ExtWithAction.toExt ρ).symm
    (HomologySingle₀WithAction.toHomology ρ).symm
    (HomWithAction.toHom ρ).symm
    (AddMonoidHom.ext fun e ↦ (HomologySingle₀WithAction.toHomology ρ).injective <| by
      simp [AddMonoidHom.comp_apply])
    (AddMonoidHom.ext fun x ↦ (HomWithAction.toHom ρ).injective <| by
      simp [AddMonoidHom.comp_apply])
    (exact_cochainExtToHomology_cochainKronecker (k := k) (K := K) (Y := Y) hij)

/-- Naturality of `cochainExtToHomologyWithAction` in the cochain complex `K`. -/
theorem cochainExtToHomologyWithAction_naturality (ρ : R →+* End Y)
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) {i j : ℤ} (hij : i + j = 1)
    [Projective (K₁.cycles j)] [IsSplitMono (K₁.iCycles j)]
    [Projective (K₂.cycles j)] [IsSplitMono (K₂.iCycles j)]
    (e : ExtWithAction.{w} ρ (K₂.homology j) 1) :
    cochainExtToHomologyWithAction k K₁ ρ hij
        (ExtWithAction.precompLinearMap ρ (Ext.mk₀ (homologyMap φ j)) (zero_add 1) e) =
      HomologySingle₀WithAction.precompLinearMap k ρ φ i
        (cochainExtToHomologyWithAction k K₂ ρ hij e) :=
  (HomologySingle₀WithAction.toHomology ρ).injective <| by
    simpa only [toHomology_cochainExtToHomologyWithAction, ExtWithAction.toExt_precompLinearMap,
      HomologySingle₀WithAction.toHomology_precompLinearMap] using
      cochainExtToHomology_naturality (k := k) φ hij (ExtWithAction.toExt ρ e)

variable (k) in
/-- **The `R`-linear split universal coefficient decomposition** for `linearHomComplex` into a
degree-zero target `Y` with action `ρ : R →+* End Y`: when `i + j = 1`, `K.cycles j` is projective,
and `K.iCycles j` and `K.iCycles (-i)` split, cohomology in degree `i` decomposes `R`-linearly as
`Ext¹(Hʲ(K), Y) × (H⁻ⁱ(K) ⟶ Y)`. -/
def cochainUniversalCoefficientEquivWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y)
    {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] :
    HomologySingle₀WithAction k K ρ i ≃ₗ[R]
      ExtWithAction.{w} ρ (K.homology j) 1 × HomWithAction ρ (K.homology (-i)) :=
  let e : (ExtWithAction.{w} ρ (K.homology j) 1 × HomWithAction ρ (K.homology (-i))) ≃ₗ[R]
      HomologySingle₀WithAction k K ρ i :=
    { toFun p := (HomologySingle₀WithAction.toHomology ρ).symm <|
        (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm
          (ExtWithAction.toExt ρ p.1, HomWithAction.toHom ρ p.2)
      invFun x :=
        ((ExtWithAction.toExt ρ).symm
            ((cochainUniversalCoefficientEquiv.{w} k K Y hij
              (HomologySingle₀WithAction.toHomology ρ x)).1),
          (HomWithAction.toHom ρ).symm
            ((cochainUniversalCoefficientEquiv.{w} k K Y hij
              (HomologySingle₀WithAction.toHomology ρ x)).2))
      left_inv p := by
        ext <;> simp only [AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
          AddEquiv.symm_apply_apply]
      right_inv x := by
        simp only [AddEquiv.apply_symm_apply, Prod.mk.eta, LinearEquiv.symm_apply_apply,
          AddEquiv.symm_apply_apply]
      map_add' p q := (HomologySingle₀WithAction.toHomology ρ).injective <| by
        simp only [AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, map_add, ← Prod.mk_add_mk]
      map_smul' r p := (HomologySingle₀WithAction.toHomology ρ).injective <| by
        simp only [AddEquiv.apply_symm_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
          HomologySingle₀WithAction.toHomology_smul, ExtWithAction.toExt_smul,
          HomWithAction.toHom_smul, cochainUniversalCoefficientEquiv_symm_apply, map_add,
          cochainExtToHomology_coefficient_naturality,
          cochainKroneckerSection_coefficient_naturality] }
  e.symm

@[simp]
lemma cochainUniversalCoefficientEquivWithAction_symm_apply {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (e : ExtWithAction.{w} ρ (K.homology j) 1) (g : HomWithAction ρ (K.homology (-i))) :
    (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm (e, g) =
      cochainExtToHomologyWithAction k K ρ hij e +
        cochainKroneckerSectionWithAction k K ρ i g :=
  (HomologySingle₀WithAction.toHomology ρ).injective <| by
    simpa only [cochainUniversalCoefficientEquivWithAction, LinearEquiv.symm_symm,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.apply_symm_apply, map_add,
      toHomology_cochainExtToHomologyWithAction, toHomology_cochainKroneckerSectionWithAction] using
      cochainUniversalCoefficientEquiv_symm_apply (k := k) (K := K) (Y := Y) hij
        (ExtWithAction.toExt ρ e) (HomWithAction.toHom ρ g)

@[simp]
lemma cochainUniversalCoefficientEquivWithAction_apply_snd {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (x : HomologySingle₀WithAction k K ρ i) :
    (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij x).2 =
      cochainKroneckerWithAction k K ρ i x := by
  have hx : (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm
      ((cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij x).1,
        (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij x).2) = x :=
    (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm_apply_apply x
  have := congrArg (cochainKroneckerWithAction k K ρ i) hx
  simpa only [cochainUniversalCoefficientEquivWithAction_symm_apply, map_add,
    (exact_cochainExtToHomologyWithAction_cochainKroneckerWithAction ρ hij).apply_apply_eq_zero,
    zero_add, cochainKroneckerWithAction_cochainKroneckerSectionWithAction] using this

end ExtWithAction

end TauCeti
