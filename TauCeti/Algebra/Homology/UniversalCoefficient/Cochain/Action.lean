/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Ext.WithAction
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
public import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# Target scalar actions on `linearHomComplex` and the `R`-linear universal coefficient theorem

Let `C` be a `k`-linear category, `K : CochainComplex C ℤ`, and `Y : C` an object carrying an
action `ρ : R →+* End Y` of a semiring `R`. Postcomposition with `ρ(r)` induces compatible left
`R`-actions on:

* morphism groups `X ⟶ Y` (`TauCeti.Abelian.HomWithAction`), via `r • f = f ≫ (ρ r).asHom`;
* degree-`i` cochains into `Y[0]` (`TauCeti.CochainSingle₀WithAction`), identified `R`-linearly
  with `HomWithAction ρ (K.X (-i))` by `Cochain.toSingleEquiv (neg_add_cancel i)`
  (`TauCeti.toSingleLinearEquivWithAction`), and assembling for a ring `R` into a cochain complex
  `TauCeti.linearHomComplexSingle₀WithAction` in `ModuleCat R`;
* cohomology `Hⁱ(Hom(K, Y[0]))` (`TauCeti.HomologySingle₀WithAction`);
* `Ext¹(Hʲ(K), Y)` (`TauCeti.Abelian.ExtWithAction`, from
  `TauCeti.Algebra.Homology.DerivedCategory.Ext.WithAction`).

For instance, when `C = ModuleCat ℤ` and `Y = ModuleCat.of ℤ R` for a commutative ring `R`, an
integral cochain complex `K` dualized into `R` has `R`-module cochain and cohomology groups even
though `K` itself is only a complex of abelian groups (`ModuleCat.endRingHomOfModule` and
`TauCeti.Abelian.HomWithAction.moduleCatLinearEquiv`).

Because `cochainKronecker`, `cochainKroneckerSection`, and `cochainExtToHomology` are all natural
in the coefficient object `Y`
(`TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic`), every map and splitting in the
cochain universal coefficient sequence upgrades to an `R`-linear map, giving an `R`-linear
split universal coefficient isomorphism
`HomologySingle₀WithAction k K ρ i ≃ₗ[R] ExtWithAction ρ (K.homology j) 1 ×
  HomWithAction ρ (K.homology (-i))`
(`TauCeti.cochainUniversalCoefficientEquivWithAction`) for `i + j = 1`.

## Main definitions and results

* `TauCeti.Abelian.HomWithAction`: `X ⟶ Y` as a left `R`-module via `ρ : R →+* End Y`, with
  `HomWithAction.precompLinearMap`, `HomWithAction.precompLinearEquiv`, and
  `HomWithAction.moduleCatLinearEquiv`.
* `TauCeti.linearHomComplexSingle₀Action`: the induced ring homomorphism
  `R →+* End (linearHomComplex k K ((singleFunctor C 0).obj Y))`.
* `TauCeti.CochainSingle₀WithAction`, `TauCeti.toSingleLinearEquivWithAction`, and
  `TauCeti.linearHomComplexSingle₀WithAction`: the `R`-module of degree-`i` cochains into `Y[0]`,
  its `R`-linear identification with `HomWithAction ρ (K.X (-i))`, and the resulting cochain
  complex in `ModuleCat R`.
* `TauCeti.HomologySingle₀WithAction` and `TauCeti.HomologySingle₀WithAction.precompLinearMap`:
  cohomology of `linearHomComplex k K ((singleFunctor C 0).obj Y)` with its `R`-module structure
  and contravariant `R`-linear functoriality in `K`.
* `TauCeti.cochainKroneckerWithAction`, `TauCeti.cochainKroneckerEquivWithAction`,
  `TauCeti.cochainKroneckerEquivOfProjectiveHomologyWithAction`,
  `TauCeti.cochainKroneckerSectionWithAction`, `TauCeti.cochainExtToHomologyWithAction`, and
  `TauCeti.cochainUniversalCoefficientEquivWithAction`: the `R`-linear universal coefficient maps,
  exactness, section, and direct-product decomposition.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex Opposite
  Abelian

universe w v u

namespace TauCeti.Abelian

section HomWithAction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type*} [Semiring R] {Y : C} (ρ : R →+* End Y)

/-- `X ⟶ Y` equipped with the left `R`-module structure induced by an action `ρ : R →+* End Y` on
the target object: `r • f = f ≫ (ρ r).asHom`. -/
-- Expose the synonym so additive and scalar instances share the `X ⟶ Y` carrier.
@[expose]
def HomWithAction (_ρ : R →+* End Y) (X : C) : Type v := X ⟶ Y

namespace HomWithAction

instance (X : C) : AddCommGroup (HomWithAction ρ X) :=
  inferInstanceAs (AddCommGroup (X ⟶ Y))

instance (X : C) : Module R (HomWithAction ρ X) :=
  Module.compHom (X ⟶ Y) ρ

/-- The underlying additive equivalence `HomWithAction ρ X ≃+ (X ⟶ Y)`. -/
def toHom {X : C} : HomWithAction ρ X ≃+ (X ⟶ Y) :=
  AddEquiv.refl _

@[simp]
lemma toHom_smul {X : C} (r : R) (f : HomWithAction ρ X) :
    toHom ρ (r • f) = toHom ρ f ≫ (ρ r).asHom :=
  (rfl)

@[simp]
lemma toHom_symm_comp_asHom {X : C} (r : R) (f : X ⟶ Y) :
    (toHom ρ).symm (f ≫ (ρ r).asHom) = r • (toHom ρ).symm f :=
  (rfl)

/-- Precomposition with `φ : X ⟶ X'` is `R`-linear on `HomWithAction ρ`. -/
def precompLinearMap {X X' : C} (φ : X ⟶ X') :
    HomWithAction ρ X' →ₗ[R] HomWithAction ρ X where
  toFun f := (toHom ρ).symm (φ ≫ toHom ρ f)
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _
  map_smul' r f := (Category.assoc φ (toHom ρ f) (ρ r).asHom).symm

@[simp]
lemma toHom_precompLinearMap {X X' : C} (φ : X ⟶ X') (f : HomWithAction ρ X') :
    toHom ρ (precompLinearMap ρ φ f) = φ ≫ toHom ρ f :=
  (rfl)

/-- Precomposition with an isomorphism `e : X ≅ X'` as an `R`-linear equivalence on
`HomWithAction ρ`. -/
def precompLinearEquiv {X X' : C} (e : X ≅ X') :
    HomWithAction ρ X' ≃ₗ[R] HomWithAction ρ X :=
  LinearEquiv.ofLinearMap (precompLinearMap ρ e.hom) (precompLinearMap ρ e.inv)
    (LinearMap.ext fun f ↦ by
      -- Unfold the transported module synonym to check the categorical inverse law on `X ⟶ Y`.
      change e.hom ≫ e.inv ≫ toHom ρ f = toHom ρ f
      rw [e.hom_inv_id_assoc])
    (LinearMap.ext fun f ↦ by
      -- Unfold the transported module synonym to check the categorical inverse law on `X' ⟶ Y`.
      change e.inv ≫ e.hom ≫ toHom ρ f = toHom ρ f
      rw [e.inv_hom_id_assoc])

@[simp]
lemma toHom_precompLinearEquiv {X X' : C} (e : X ≅ X') (f : HomWithAction ρ X') :
    toHom ρ (precompLinearEquiv ρ e f) = e.hom ≫ toHom ρ f :=
  (rfl)

@[simp]
lemma toHom_precompLinearEquiv_symm {X X' : C} (e : X ≅ X') (f : HomWithAction ρ X) :
    toHom ρ ((precompLinearEquiv ρ e).symm f) = e.inv ≫ toHom ρ f :=
  (rfl)

end HomWithAction

end HomWithAction

end TauCeti.Abelian

namespace ModuleCat

/-- A commuting `R`-module structure on a `k`-module `Y : ModuleCat k` induces a ring homomorphism
`R →+* End Y` sending `r` to scalar multiplication by `r`. -/
def endRingHomOfModule (k R : Type*) [Ring k] [Semiring R] (Y : ModuleCat.{v} k)
    [Module R Y] [SMulCommClass k R Y] : R →+* End Y where
  toFun r := End.of (ModuleCat.ofHom
    { toFun y := r • y
      map_add' := smul_add r
      map_smul' c y := (smul_comm c r y).symm })
  map_one' := by ext y; exact one_smul R y
  map_mul' r s := by ext y; exact mul_smul r s y
  map_zero' := by ext y; exact zero_smul R y
  map_add' r s := by ext y; exact add_smul r s y

@[simp]
lemma endRingHomOfModule_apply_asHom_apply {k R : Type*} [Ring k] [Semiring R]
    (Y : ModuleCat.{v} k) [Module R Y] [SMulCommClass k R Y] (r : R) (y : Y) :
    (endRingHomOfModule k R Y r).asHom.hom y = r • y :=
  (rfl)

end ModuleCat

namespace TauCeti.Abelian.HomWithAction

/-- For `X Y : ModuleCat k` with a commuting `R`-action on `Y`, `HomWithAction` for
`ModuleCat.endRingHomOfModule k R Y` agrees `R`-linearly with `X →ₗ[k] Y` equipped with its
pointwise `R`-action. -/
def moduleCatLinearEquiv {k R : Type*} [Ring k] [Semiring R] (X Y : ModuleCat.{v} k)
    [Module R Y] [SMulCommClass k R Y] :
    HomWithAction (ModuleCat.endRingHomOfModule k R Y) X ≃ₗ[R] (X →ₗ[k] Y) where
  toAddEquiv := (toHom (ModuleCat.endRingHomOfModule k R Y)).trans
    (ModuleCat.homLinearEquiv (S := R)).toAddEquiv
  map_smul' _ _ := by
    ext x
    rfl

@[simp]
lemma moduleCatLinearEquiv_apply {k R : Type*} [Ring k] [Semiring R] {X Y : ModuleCat.{v} k}
    [Module R Y] [SMulCommClass k R Y]
    (f : HomWithAction (ModuleCat.endRingHomOfModule k R Y) X) :
    moduleCatLinearEquiv X Y f = (toHom (ModuleCat.endRingHomOfModule k R Y) f).hom :=
  (rfl)

@[simp]
lemma moduleCatLinearEquiv_symm_apply {k R : Type*} [Ring k] [Semiring R] {X Y : ModuleCat.{v} k}
    [Module R Y] [SMulCommClass k R Y] (f : X →ₗ[k] Y) :
    toHom (ModuleCat.endRingHomOfModule k R Y) ((moduleCatLinearEquiv X Y).symm f) =
      ModuleCat.ofHom f :=
  (rfl)

end TauCeti.Abelian.HomWithAction

namespace TauCeti

open TauCeti.Abelian

section ComplexAction

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {k : Type*} [Ring k] [Linear k C]
  {R : Type*} [Semiring R] {Y : C}

variable (k) in
/-- The ring homomorphism `R →+* End (linearHomComplex k K ((singleFunctor C 0).obj Y))` induced by
`ρ : R →+* End Y` through functorial postcomposition in the target. -/
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
/-- The degree-`i` cochain group `(linearHomComplex k K ((singleFunctor C 0).obj Y)).X i` equipped
with the left `R`-module structure induced by `ρ : R →+* End Y`. -/
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
    R →+* Module.End k ((linearHomComplex k K ((singleFunctor C 0).obj Y)).X i) where
  toFun r := ((linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).f i).hom
  map_one' := by
    ext z
    simp
  map_mul' r s := by
    ext z
    simp [End.mul_asHom]
  map_zero' := by
    ext z
    simp
  map_add' r s := by
    ext z
    simp

instance (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    Module R (CochainSingle₀WithAction k K ρ i) :=
  Module.compHom ((linearHomComplex k K ((singleFunctor C 0).obj Y)).X i) (smulEnd k K ρ i)

/-- The underlying additive equivalence from `CochainSingle₀WithAction k K ρ i` to the degree-`i`
cochain group `Cochain K ((singleFunctor C 0).obj Y) i`. -/
def toCochain {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ} :
    CochainSingle₀WithAction k K ρ i ≃+
      Cochain K ((singleFunctor C 0).obj Y) i :=
  AddEquiv.refl _

@[simp]
lemma toCochain_smul {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ}
    (r : R) (z : CochainSingle₀WithAction k K ρ i) :
    toCochain ρ (r • z) =
      ((linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).f i).hom
        (toCochain ρ z) :=
  (rfl)

end CochainSingle₀WithAction

variable (k) in
/-- **Degreewise `R`-linear identification of cochains into `Y[0]`**: under
`Cochain.toSingleEquiv (neg_add_cancel i)`, the postcomposition `R`-action on degree-`i` cochains
agrees with the postcomposition `R`-action `HomWithAction ρ (K.X (-i))`. -/
def toSingleLinearEquivWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    CochainSingle₀WithAction k K ρ i ≃ₗ[R] HomWithAction ρ (K.X (-i)) where
  toAddEquiv := (CochainSingle₀WithAction.toCochain ρ).trans <|
    (Cochain.toSingleEquiv (neg_add_cancel i)).trans (HomWithAction.toHom ρ).symm
  map_smul' r z := by
    apply (HomWithAction.toHom ρ).injective
    apply (Cochain.toSingleEquiv (neg_add_cancel i)).symm.injective
    let z' : ModuleCat.of k (Cochain K ((singleFunctor C 0).obj Y) i) :=
      CochainSingle₀WithAction.toCochain ρ z
    have hz : Cochain.toSingleMk (Cochain.toSingleEquiv (neg_add_cancel i) z')
        (neg_add_cancel i) = z' :=
      Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z'
    -- Unfold the composed additive equivalences and both transported `R`-actions into `Cochain`.
    change Cochain.toSingleMk (Cochain.toSingleEquiv (neg_add_cancel i)
        (((linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).f i).hom z'))
          (neg_add_cancel i) =
      Cochain.toSingleMk (Cochain.toSingleEquiv (neg_add_cancel i) z' ≫ (ρ r).asHom)
        (neg_add_cancel i)
    rw [Cochain.toSingleMk_toSingleEquiv, linearHomComplexPostcomp_f_apply,
      Cochain.toSingleMk_postcomp, hz]

@[simp]
lemma toHom_toSingleLinearEquivWithAction {K : CochainComplex C ℤ} (ρ : R →+* End Y)
    {i : ℤ} (z : CochainSingle₀WithAction k K ρ i) :
    HomWithAction.toHom ρ (toSingleLinearEquivWithAction k K ρ i z) =
      Cochain.toSingleEquiv (neg_add_cancel i) (CochainSingle₀WithAction.toCochain ρ z) :=
  (rfl)

@[simp]
lemma toCochain_toSingleLinearEquivWithAction_symm {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i : ℤ} (f : HomWithAction ρ (K.X (-i))) :
    CochainSingle₀WithAction.toCochain ρ ((toSingleLinearEquivWithAction k K ρ i).symm f) =
      Cochain.toSingleMk (HomWithAction.toHom ρ f) (neg_add_cancel i) :=
  (rfl)

variable (k) in
/-- The `R`-linear differential `CochainSingle₀WithAction k K ρ i →ₗ[R]
CochainSingle₀WithAction k K ρ j` induced by the differential of `linearHomComplex`. -/
def CochainSingle₀WithAction.differential (K : CochainComplex C ℤ) {R : Type v} [Ring R]
    (ρ : R →+* End Y) (i j : ℤ) :
    CochainSingle₀WithAction k K ρ i →ₗ[R] CochainSingle₀WithAction k K ρ j where
  toFun z := (CochainSingle₀WithAction.toCochain ρ).symm <|
    ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i j).hom
      (CochainSingle₀WithAction.toCochain ρ z)
  map_add' z₁ z₂ := map_add ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i j).hom
    (CochainSingle₀WithAction.toCochain ρ z₁) (CochainSingle₀WithAction.toCochain ρ z₂)
  map_smul' r z := by
    apply (CochainSingle₀WithAction.toCochain ρ).injective
    -- Postcomposition is a chain map, so it commutes with the differential of
    -- `linearHomComplex`.
    have hcomm := congrArg (fun φ ↦ φ.hom (CochainSingle₀WithAction.toCochain ρ z))
      ((linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)).comm i j)
    simpa only [AddEquiv.apply_symm_apply, RingHom.id_apply,
      CochainSingle₀WithAction.toCochain_smul, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, LinearMap.comp_apply] using hcomm

@[simp]
lemma CochainSingle₀WithAction.toCochain_differential_apply {K : CochainComplex C ℤ} {R : Type v}
    [Ring R] (ρ : R →+* End Y) {i j : ℤ} (z : CochainSingle₀WithAction k K ρ i) :
    CochainSingle₀WithAction.toCochain ρ (CochainSingle₀WithAction.differential k K ρ i j z) =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i j).hom
        (CochainSingle₀WithAction.toCochain ρ z) :=
  (rfl)

lemma CochainSingle₀WithAction.differential_shape (K : CochainComplex C ℤ) {R : Type v} [Ring R]
    (ρ : R →+* End Y) (i j : ℤ) (hij : ¬ (ComplexShape.up ℤ).Rel i j) :
    (ModuleCat.ofHom (CochainSingle₀WithAction.differential k K ρ i j) :
      ModuleCat.of R (CochainSingle₀WithAction k K ρ i) ⟶
        ModuleCat.of R (CochainSingle₀WithAction k K ρ j)) = 0 := by
  ext z
  apply (CochainSingle₀WithAction.toCochain (k := k) ρ).injective
  rw [ModuleCat.ofHom_apply, CochainSingle₀WithAction.toCochain_differential_apply (k := k),
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).shape i j hij]
  rfl

lemma CochainSingle₀WithAction.differential_comp_differential (K : CochainComplex C ℤ)
    {R : Type v} [Ring R] (ρ : R →+* End Y) (i j m : ℤ) :
    (ModuleCat.ofHom (CochainSingle₀WithAction.differential k K ρ i j) :
      ModuleCat.of R (CochainSingle₀WithAction k K ρ i) ⟶
        ModuleCat.of R (CochainSingle₀WithAction k K ρ j)) ≫
      ModuleCat.ofHom (CochainSingle₀WithAction.differential k K ρ j m) = 0 := by
  ext z
  apply (CochainSingle₀WithAction.toCochain (k := k) ρ).injective
  rw [ModuleCat.comp_apply, ModuleCat.ofHom_apply, ModuleCat.ofHom_apply,
    CochainSingle₀WithAction.toCochain_differential_apply (k := k),
    CochainSingle₀WithAction.toCochain_differential_apply (k := k), ← ModuleCat.comp_apply,
    HomologicalComplex.d_comp_d]
  rfl

variable (k) in
-- The terms must reduce to cochain modules to typecheck `linearHomComplexSingle₀WithAction_d`.
/-- When `R` is a ring, the `R`-actions on `CochainSingle₀WithAction k K ρ i` commute with the
cochain differential and assemble into a cochain complex in `ModuleCat R`. -/
@[expose]
def linearHomComplexSingle₀WithAction (K : CochainComplex C ℤ) {R : Type v} [Ring R]
    (ρ : R →+* End Y) : CochainComplex (ModuleCat.{v} R) ℤ where
  X i := ModuleCat.of R (CochainSingle₀WithAction k K ρ i)
  d i j := ModuleCat.ofHom (CochainSingle₀WithAction.differential k K ρ i j)
  shape i j hij := CochainSingle₀WithAction.differential_shape (k := k) K ρ i j hij
  d_comp_d' i j m _ _ :=
    CochainSingle₀WithAction.differential_comp_differential (k := k) K ρ i j m

@[simp]
lemma linearHomComplexSingle₀WithAction_X {K : CochainComplex C ℤ} {R : Type v} [Ring R]
    (ρ : R →+* End Y) (i : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).X i =
      ModuleCat.of R (CochainSingle₀WithAction k K ρ i) :=
  (rfl)

@[simp]
lemma linearHomComplexSingle₀WithAction_d {K : CochainComplex C ℤ} {R : Type v} [Ring R]
    (ρ : R →+* End Y) (i j : ℤ) :
    (linearHomComplexSingle₀WithAction k K ρ).d i j =
      ModuleCat.ofHom (CochainSingle₀WithAction.differential k K ρ i j) :=
  (rfl)

variable (k) in
/-- Cohomology `(linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i` equipped with the
left `R`-module structure induced by `ρ : R →+* End Y` through postcomposition. -/
-- Expose the synonym so cohomology operations compute directly on the underlying carrier.
@[expose]
def HomologySingle₀WithAction (K : CochainComplex C ℤ) (_ρ : R →+* End Y) (i : ℤ) :
    Type v :=
  (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i

namespace HomologySingle₀WithAction

instance (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    AddCommGroup (HomologySingle₀WithAction k K ρ i) :=
  inferInstanceAs (AddCommGroup ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i))

variable (k) in
/-- The action of `R` on `(linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i` induced by
`ρ`, as a ring homomorphism to `k`-linear endomorphisms. -/
def smulEnd (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ) :
    R →+* Module.End k ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) where
  toFun r :=
    (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map (ρ r).asHom)) i).hom
  map_one' := by
    ext x
    simp
  map_mul' r s := by
    ext x
    simp [End.mul_asHom, HomologicalComplex.homologyMap_comp]
  map_zero' := by
    ext x
    simp
  map_add' r s := by
    ext x
    simp [HomologicalComplex.homologyMap_add]

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
  (rfl)

variable (k) in
/-- Contravariant functoriality of `HomologySingle₀WithAction` along a chain map `φ : K₁ ⟶ K₂` is
`R`-linear. -/
def precompLinearMap (ρ : R →+* End Y) {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂)
    (i : ℤ) :
    HomologySingle₀WithAction k K₂ ρ i →ₗ[R] HomologySingle₀WithAction k K₁ ρ i where
  toFun x := (toHomology ρ).symm <|
    (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom (toHomology ρ x)
  map_add' x y := map_add
    (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom
    (toHomology ρ x) (toHomology ρ y)
  map_smul' r x := by
    apply (toHomology ρ).injective
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
        (toHomology ρ x) :=
  (rfl)

end HomologySingle₀WithAction

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
  map_add' x y := map_add (cochainKronecker k K Y i)
    (HomologySingle₀WithAction.toHomology ρ x) (HomologySingle₀WithAction.toHomology ρ y)
  map_smul' r x := by
    apply (HomWithAction.toHom ρ).injective
    simp only [AddEquiv.apply_symm_apply, HomWithAction.toHom_smul, RingHom.id_apply,
      HomologySingle₀WithAction.toHomology_smul]
    exact cochainKronecker_coefficient_naturality (ρ r).asHom i _

@[simp]
lemma toHom_cochainKroneckerWithAction {K : CochainComplex C ℤ} (ρ : R →+* End Y) {i : ℤ}
    (x : HomologySingle₀WithAction k K ρ i) :
    HomWithAction.toHom ρ (cochainKroneckerWithAction k K ρ i x) =
      cochainKronecker k K Y i (HomologySingle₀WithAction.toHomology ρ x) :=
  (rfl)

/-- Naturality of `cochainKroneckerWithAction` in the cochain complex `K`. -/
theorem cochainKroneckerWithAction_naturality (ρ : R →+* End Y)
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (i : ℤ)
    (x : HomologySingle₀WithAction k K₂ ρ i) :
    cochainKroneckerWithAction k K₁ ρ i
        (HomologySingle₀WithAction.precompLinearMap k ρ φ i x) =
      HomWithAction.precompLinearMap ρ (homologyMap φ (-i))
        (cochainKroneckerWithAction k K₂ ρ i x) := by
  apply (HomWithAction.toHom ρ).injective
  exact cochainKronecker_naturality φ i (HomologySingle₀WithAction.toHomology ρ x)

variable (k) in
/-- When `Y` is injective, `cochainKroneckerWithAction` is an `R`-linear equivalence. -/
def cochainKroneckerEquivWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y)
    [Injective Y] (i : ℤ) :
    HomologySingle₀WithAction k K ρ i ≃ₗ[R] HomWithAction ρ (K.homology (-i)) :=
  LinearEquiv.ofBijective (cochainKroneckerWithAction k K ρ i)
    (cochainKronecker_bijective (k := k) (K := K) (Y := Y) i)

@[simp]
lemma cochainKroneckerEquivWithAction_apply {K : CochainComplex C ℤ} (ρ : R →+* End Y)
    [Injective Y] (i : ℤ) (x : HomologySingle₀WithAction k K ρ i) :
    cochainKroneckerEquivWithAction k K ρ i x = cochainKroneckerWithAction k K ρ i x :=
  (rfl)

variable (k) in
/-- When `K.homology j` (`i + j = 1`) is projective and the cycle inclusions in degrees `-i` and
`j` split, `cochainKroneckerWithAction` is an `R`-linear equivalence over any ring `k` and
semiring `R`. -/
def cochainKroneckerEquivOfProjectiveHomologyWithAction (K : CochainComplex C ℤ)
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.homology j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] :
    HomologySingle₀WithAction k K ρ i ≃ₗ[R] HomWithAction ρ (K.homology (-i)) :=
  LinearEquiv.ofBijective (cochainKroneckerWithAction k K ρ i)
    (cochainKronecker_bijective_of_projective_homology (k := k) (K := K) (Y := Y) hij)

@[simp]
lemma cochainKroneckerEquivOfProjectiveHomologyWithAction_apply {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.homology j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (x : HomologySingle₀WithAction k K ρ i) :
    cochainKroneckerEquivOfProjectiveHomologyWithAction k K ρ hij x =
      cochainKroneckerWithAction k K ρ i x :=
  (rfl)

variable (k) in
/-- **The `R`-linear section of `cochainKroneckerWithAction`** associated to a retraction of
`K.iCycles (-i)`. -/
def cochainKroneckerSectionWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    HomWithAction ρ (K.homology (-i)) →ₗ[R] HomologySingle₀WithAction k K ρ i where
  toFun g := (HomologySingle₀WithAction.toHomology ρ).symm <|
    cochainKroneckerSection k K Y i (HomWithAction.toHom ρ g)
  map_add' g₁ g₂ := map_add (cochainKroneckerSection k K Y i)
    (HomWithAction.toHom ρ g₁) (HomWithAction.toHom ρ g₂)
  map_smul' r g := by
    apply (HomologySingle₀WithAction.toHomology ρ).injective
    simp only [AddEquiv.apply_symm_apply, HomologySingle₀WithAction.toHomology_smul,
      RingHom.id_apply, HomWithAction.toHom_smul]
    exact (cochainKroneckerSection_coefficient_naturality (ρ r).asHom i _).symm

@[simp]
lemma toHomology_cochainKroneckerSectionWithAction {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i : ℤ} [IsSplitMono (K.iCycles (-i))]
    (g : HomWithAction ρ (K.homology (-i))) :
    HomologySingle₀WithAction.toHomology ρ (cochainKroneckerSectionWithAction k K ρ i g) =
      cochainKroneckerSection k K Y i (HomWithAction.toHom ρ g) :=
  (rfl)

@[simp]
lemma cochainKroneckerWithAction_cochainKroneckerSectionWithAction {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i : ℤ} [IsSplitMono (K.iCycles (-i))]
    (g : HomWithAction ρ (K.homology (-i))) :
    cochainKroneckerWithAction k K ρ i (cochainKroneckerSectionWithAction k K ρ i g) = g := by
  apply (HomWithAction.toHom ρ).injective
  exact cochainKronecker_cochainKroneckerSection (k := k) i (HomWithAction.toHom ρ g)

end UniversalCoefficientWithAction

section ExtWithAction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {k : Type*} [CommRing k] [Linear k C]
  {R : Type*} [Semiring R] {Y : C}

variable (k) in
/-- **The `R`-linear `Ext` inclusion** `Ext¹(Hʲ(K), Y) →ₗ[R] Hⁱ(Hom(K, Y[0]))` (`i + j = 1`) for a
target `Y` carrying an action `ρ : R →+* End Y`. -/
def cochainExtToHomologyWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y)
    {i j : ℤ} (hij : i + j = 1) [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    ExtWithAction.{w} ρ (K.homology j) 1 →ₗ[R] HomologySingle₀WithAction k K ρ i where
  toFun e := (HomologySingle₀WithAction.toHomology ρ).symm <|
    cochainExtToHomology k K Y hij (ExtWithAction.toExt ρ e)
  map_add' e₁ e₂ := by
    apply (HomologySingle₀WithAction.toHomology ρ).injective
    simp only [map_add, AddEquiv.apply_symm_apply]
  map_smul' r e := by
    apply (HomologySingle₀WithAction.toHomology ρ).injective
    simp only [AddEquiv.apply_symm_apply, HomologySingle₀WithAction.toHomology_smul,
      RingHom.id_apply, ExtWithAction.toExt_smul]
    exact cochainExtToHomology_coefficient_naturality (ρ r).asHom hij (ExtWithAction.toExt ρ e)

@[simp]
lemma toHomology_cochainExtToHomologyWithAction {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    (e : ExtWithAction.{w} ρ (K.homology j) 1) :
    HomologySingle₀WithAction.toHomology ρ (cochainExtToHomologyWithAction k K ρ hij e) =
      cochainExtToHomology k K Y hij (ExtWithAction.toExt ρ e) :=
  (rfl)

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
      (cochainKroneckerWithAction k K ρ i) := by
  intro x
  have hkr : cochainKroneckerWithAction k K ρ i x = 0 ↔
      cochainKronecker k K Y i (HomologySingle₀WithAction.toHomology ρ x) = 0 :=
    (HomWithAction.toHom ρ).injective.eq_iff' (map_zero _)|>.symm
  rw [hkr, exact_cochainExtToHomology_cochainKronecker (k := k) (K := K) (Y := Y) hij]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(ExtWithAction.toExt ρ).symm e, ?_⟩
    apply (HomologySingle₀WithAction.toHomology ρ).injective
    simpa only [toHomology_cochainExtToHomologyWithAction, AddEquiv.apply_symm_apply] using he
  · rintro ⟨e, rfl⟩
    exact ⟨ExtWithAction.toExt ρ e, rfl⟩

/-- Naturality of `cochainExtToHomologyWithAction` in the cochain complex `K`. -/
theorem cochainExtToHomologyWithAction_naturality (ρ : R →+* End Y)
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) {i j : ℤ} (hij : i + j = 1)
    [Projective (K₁.cycles j)] [IsSplitMono (K₁.iCycles j)]
    [Projective (K₂.cycles j)] [IsSplitMono (K₂.iCycles j)]
    (e : ExtWithAction.{w} ρ (K₂.homology j) 1) :
    cochainExtToHomologyWithAction k K₁ ρ hij
        (ExtWithAction.precompLinearMap ρ (Ext.mk₀ (homologyMap φ j)) (zero_add 1) e) =
      HomologySingle₀WithAction.precompLinearMap k ρ φ i
        (cochainExtToHomologyWithAction k K₂ ρ hij e) := by
  apply (HomologySingle₀WithAction.toHomology ρ).injective
  simpa only [toHomology_cochainExtToHomologyWithAction, ExtWithAction.toExt_precompLinearMap,
    HomologySingle₀WithAction.toHomology_precompLinearMap] using
    cochainExtToHomology_naturality (k := k) φ hij (ExtWithAction.toExt ρ e)

variable (k) in
/-- **The `R`-linear split universal coefficient decomposition** for `linearHomComplex` into a
degree-zero target `Y` carrying an action `ρ : R →+* End Y`: for `i + j = 1`, cohomology in
degree `i` decomposes `R`-linearly as `Ext¹(Hʲ(K), Y) × (H⁻ⁱ(K) ⟶ Y)`. -/
def cochainUniversalCoefficientEquivWithAction (K : CochainComplex C ℤ) (ρ : R →+* End Y)
    {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] :
    HomologySingle₀WithAction k K ρ i ≃ₗ[R]
      ExtWithAction.{w} ρ (K.homology j) 1 × HomWithAction ρ (K.homology (-i)) :=
  ((exact_cochainExtToHomologyWithAction_cochainKroneckerWithAction.{w}
    (k := k) (K := K) ρ hij).splitSurjectiveEquiv
      (cochainExtToHomologyWithAction_injective (k := k) ρ hij)
      ⟨cochainKroneckerSectionWithAction k K ρ i,
        LinearMap.ext (cochainKroneckerWithAction_cochainKroneckerSectionWithAction ρ)⟩).1

@[simp]
lemma cochainUniversalCoefficientEquivWithAction_symm_apply {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (e : ExtWithAction.{w} ρ (K.homology j) 1)
    (g : HomWithAction ρ (K.homology (-i))) :
    (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm (e, g) =
      cochainExtToHomologyWithAction k K ρ hij e +
        cochainKroneckerSectionWithAction k K ρ i g := by
  let S := (exact_cochainExtToHomologyWithAction_cochainKroneckerWithAction.{w}
    (k := k) (K := K) ρ hij).splitSurjectiveEquiv
      (cochainExtToHomologyWithAction_injective (k := k) ρ hij)
  let sec : { s // (cochainKroneckerWithAction k K ρ i).comp s = LinearMap.id } :=
    ⟨cochainKroneckerSectionWithAction k K ρ i,
      LinearMap.ext (cochainKroneckerWithAction_cochainKroneckerSectionWithAction ρ)⟩
  have he : (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm (e, 0) =
      cochainExtToHomologyWithAction k K ρ hij e :=
    (LinearMap.congr_fun (S sec).property.left e).symm
  have hg : (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm (0, g) =
      cochainKroneckerSectionWithAction k K ρ i g :=
    LinearMap.congr_fun (congrArg Subtype.val (S.left_inv sec)) g
  calc
    (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm (e, g) =
        (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm (e, 0) +
          (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij).symm (0, g) := by
      rw [← map_add]; simp
    _ = _ := by rw [he, hg]

@[simp]
lemma cochainUniversalCoefficientEquivWithAction_apply_snd {K : CochainComplex C ℤ}
    (ρ : R →+* End Y) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (x : HomologySingle₀WithAction k K ρ i) :
    (cochainUniversalCoefficientEquivWithAction.{w} k K ρ hij x).2 =
      cochainKroneckerWithAction k K ρ i x :=
  (LinearMap.congr_fun
    ((exact_cochainExtToHomologyWithAction_cochainKroneckerWithAction.{w}
      (k := k) (K := K) ρ hij).splitSurjectiveEquiv
        (cochainExtToHomologyWithAction_injective (k := k) ρ hij) _).property.right x).symm

end ExtWithAction

end TauCeti
