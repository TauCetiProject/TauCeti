/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Single.Basic
public import TauCeti.CategoryTheory.Preadditive.HomWithAction
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# Target scalar actions on `linearHomComplex` into a degree-zero object

Let `C` be a `k`-linear preadditive category with a zero object, `K : CochainComplex C ℤ`, and
`Y : C` an object equipped with a semiring action `ρ : R →+* End Y`. Postcomposition with
`(ρ r).asHom` induces compatible left `R`-actions on:

* the cochain complex `linearHomComplex k K Y[0]` (`TauCeti.linearHomComplexSingle₀Action`);
* degree-`i` cochains into `Y[0]` (`TauCeti.CochainSingle₀WithAction`), identified `R`-linearly
  with `TauCeti.HomWithAction ρ (K.X (-i))` by `TauCeti.toSingleLinearEquivWithAction`, and
  assembling for a ring `R` into a cochain complex `TauCeti.linearHomComplexSingle₀WithAction` in
  `ModuleCat R`;
* cohomology `Hⁱ(Hom(K, Y[0]))` (`TauCeti.HomologySingle₀WithAction`), with contravariant
  `R`-linear functoriality (`TauCeti.HomologySingle₀WithAction.precompLinearMap`) and canonical
  `R`-linear comparison `TauCeti.linearHomComplexSingle₀WithActionHomologyEquiv` identifying
  `(linearHomComplexSingle₀WithAction k K ρ).homology i` with `HomologySingle₀WithAction k K ρ i`.

## Main definitions and results

* `TauCeti.linearHomComplexSingle₀Action`, `TauCeti.CochainSingle₀WithAction`,
  `TauCeti.toSingleLinearEquivWithAction`, `TauCeti.CochainSingle₀WithAction.differential`, and
  `TauCeti.linearHomComplexSingle₀WithAction`.
* `TauCeti.HomologySingle₀WithAction`, `TauCeti.HomologySingle₀WithAction.precompLinearMap`, and
  `TauCeti.linearHomComplexSingle₀WithActionHomologyEquiv`.

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

universe v u

namespace TauCeti

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
/-- Degreewise additive identification of the terms of `linearHomComplexSingle₀WithAction` with
those of `linearHomComplex`. -/
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
/-- Additive equivalence between the degree-`i` cocycles of `linearHomComplexSingle₀WithAction` and
those of `linearHomComplex`, characterized by intertwining `iCycles` with `toCochainX`. -/
private def cyclesToUnderlyingEquiv (K : CochainComplex C ℤ) {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).cycles i ≃+
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i where
  toFun z := (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCatCyclesMk
    (toCochainX k ρ ((linearHomComplexSingle₀WithAction k K ρ).iCycles i z))
    (i + 1) (by simp) <| by
      rw [← toCochainX_d_apply (k := k) ρ]
      exact (congrArg (toCochainX k ρ)
        ((linearHomComplexSingle₀WithAction k K ρ).moduleCat_d_iCycles_apply i (i + 1) z)).trans
        (map_zero (toCochainX k ρ))
  invFun w := (linearHomComplexSingle₀WithAction k K ρ).moduleCatCyclesMk
    ((toCochainX k ρ).symm ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i w))
    (i + 1) (by simp) <| by
      apply (toCochainX k ρ).injective
      rw [toCochainX_d_apply (k := k) ρ, AddEquiv.apply_symm_apply, map_zero]
      exact (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_d_iCycles_apply i
        (i + 1) w
  left_inv z := by
    apply (linearHomComplexSingle₀WithAction k K ρ).moduleCat_iCycles_injective i
    rw [HomologicalComplex.iCycles_moduleCatCyclesMk, HomologicalComplex.iCycles_moduleCatCyclesMk,
      AddEquiv.symm_apply_apply]
  right_inv w := by
    apply (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_iCycles_injective i
    rw [HomologicalComplex.iCycles_moduleCatCyclesMk, HomologicalComplex.iCycles_moduleCatCyclesMk,
      AddEquiv.apply_symm_apply]
  map_add' z₁ z₂ := by
    apply (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_iCycles_injective i
    rw [HomologicalComplex.iCycles_moduleCatCyclesMk, map_add, map_add, map_add,
      HomologicalComplex.iCycles_moduleCatCyclesMk, HomologicalComplex.iCycles_moduleCatCyclesMk]

private lemma iCycles_cyclesToUnderlyingEquiv {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i : ℤ)
    (z : (linearHomComplexSingle₀WithAction k K ρ).cycles i) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i
        (cyclesToUnderlyingEquiv k K ρ i z) =
      toCochainX k ρ ((linearHomComplexSingle₀WithAction k K ρ).iCycles i z) :=
  (linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles_moduleCatCyclesMk i _ _ _ _

private lemma cyclesToUnderlyingEquiv_smul {K : CochainComplex C ℤ} {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i : ℤ) (r : R)
    (z : (linearHomComplexSingle₀WithAction k K ρ).cycles i) :
    cyclesToUnderlyingEquiv k K ρ i (r • z) =
      cyclesMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)) i
        (cyclesToUnderlyingEquiv k K ρ i z) := by
  apply (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_iCycles_injective i
  rw [iCycles_cyclesToUnderlyingEquiv, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply,
    iCycles_cyclesToUnderlyingEquiv, map_smul, toCochainX_smul]

/-- Boundary compatibility of `cyclesToUnderlyingEquiv`: coboundaries in
`linearHomComplexSingle₀WithAction` match coboundaries in `linearHomComplex` via `toCochainX`. -/
private lemma cyclesToUnderlyingEquiv_toCycles (K : CochainComplex C ℤ) {R : Type*} [Ring R]
    (ρ : R →+* End Y) (i : ℤ) (y : (linearHomComplexSingle₀WithAction k K ρ).X (i - 1)) :
    cyclesToUnderlyingEquiv k K ρ i
        ((linearHomComplexSingle₀WithAction k K ρ).toCycles (i - 1) i y) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).toCycles (i - 1) i
        (toCochainX k ρ y) := by
  apply (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_iCycles_injective i
  rw [iCycles_cyclesToUnderlyingEquiv, HomologicalComplex.moduleCat_iCycles_toCycles_apply,
    HomologicalComplex.moduleCat_iCycles_toCycles_apply, toCochainX_d_apply]

/-- A cocycle of `linearHomComplexSingle₀WithAction` represents zero in cohomology if and only if
its corresponding cocycle in `linearHomComplex` represents zero in cohomology. -/
private lemma homologyπ_cyclesToUnderlyingEquiv_eq_zero_iff (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ)
    (z : (linearHomComplexSingle₀WithAction k K ρ).cycles i) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i
        (cyclesToUnderlyingEquiv k K ρ i z) = 0 ↔
      (linearHomComplexSingle₀WithAction k K ρ).homologyπ i z = 0 := by
  rw [(linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_homologyπ_eq_zero_iff
      (m := i - 1) (by simp),
    (linearHomComplexSingle₀WithAction k K ρ).moduleCat_homologyπ_eq_zero_iff
      (m := i - 1) (by simp)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(toCochainX k ρ).symm y, (cyclesToUnderlyingEquiv k K ρ i).injective ?_⟩
    rw [cyclesToUnderlyingEquiv_toCycles, AddEquiv.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨toCochainX k ρ y, (cyclesToUnderlyingEquiv_toCycles K ρ i y).symm⟩

variable (k) in
private def linearHomComplexSingle₀WithActionCyclesToHomology (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).cycles i →ₗ[R] HomologySingle₀WithAction k K ρ i where
  toFun z := (HomologySingle₀WithAction.toHomology (k := k) ρ).symm <|
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i
      (cyclesToUnderlyingEquiv k K ρ i z)
  map_add' z₁ z₂ := by simp only [map_add]
  map_smul' r z := (HomologySingle₀WithAction.toHomology (k := k) ρ).injective <| by
    simp only [AddEquiv.apply_symm_apply, RingHom.id_apply,
      HomologySingle₀WithAction.toHomology_smul, ModuleCat.Hom.hom,
      cyclesToUnderlyingEquiv_smul]
    exact (HomologicalComplex.moduleCat_homologyMap_homologyπ _ i _).symm

variable (k) in
private lemma linearHomComplexSingle₀WithActionCyclesToHomology_toCycles (K : CochainComplex C ℤ)
    {R : Type*} [Ring R] (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).toCycles (i - 1) i ≫
        ModuleCat.ofHom (linearHomComplexSingle₀WithActionCyclesToHomology k K ρ i) = 0 := by
  ext y
  apply (HomologySingle₀WithAction.toHomology (k := k) ρ).injective
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero, linearHomComplexSingle₀WithActionCyclesToHomology,
    LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.apply_symm_apply,
    cyclesToUnderlyingEquiv_toCycles]
  rw [(linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_homologyπ_eq_zero_iff
    (m := i - 1) (by simp)]
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
  have hfπ (z : L'.cycles i) :
      HomologySingle₀WithAction.toHomology (k := k) ρ
          ((linearHomComplexSingle₀WithActionHomologyMap k K ρ i).hom (L'.homologyπ i z)) =
        L.homologyπ i (cyclesToUnderlyingEquiv k K ρ i z) := by
    have hcomp := congrArg (fun g ↦ g z)
      (homologyπ_linearHomComplexSingle₀WithActionHomologyMap k K ρ i)
    simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_ofHom,
      linearHomComplexSingle₀WithActionCyclesToHomology, LinearMap.coe_mk, AddHom.coe_mk,
      AddEquiv.apply_symm_apply] using
      congrArg (HomologySingle₀WithAction.toHomology (k := k) ρ) hcomp
  refine ⟨?_, ?_⟩
  · -- Injectivity: lift to a cocycle and apply the coboundary equivalence.
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := L'.moduleCat_homologyπ_surjective i x
    exact (homologyπ_cyclesToUnderlyingEquiv_eq_zero_iff K ρ i z).1 <| by
      rw [← hfπ z, hx, map_zero]
  · -- Surjectivity: lift to a cocycle in `L` and transport back via `cyclesToUnderlyingEquiv.symm`.
    intro x
    obtain ⟨w, hw⟩ := L.moduleCat_homologyπ_surjective i
      (HomologySingle₀WithAction.toHomology (k := k) ρ x)
    refine ⟨L'.homologyπ i ((cyclesToUnderlyingEquiv k K ρ i).symm w),
      (HomologySingle₀WithAction.toHomology (k := k) ρ).injective ?_⟩
    rw [hfπ, AddEquiv.apply_symm_apply, hw]

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
  rw [iCycles_cyclesToUnderlyingEquiv]
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

end TauCeti
