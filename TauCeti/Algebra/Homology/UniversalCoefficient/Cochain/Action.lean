/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Ext.WithAction
public import TauCeti.Algebra.Homology.LinearHomComplex.Single.Action
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic

/-!
# The `R`-linear cochain universal coefficient theorem for target scalar actions

Let `C` be a `k`-linear abelian category, `K : CochainComplex C ℤ`, and `Y : C` an object with a
semiring action `ρ : R →+* End Y`. Building on the target-action structures on `Hom(-, Y)`
(`TauCeti.CategoryTheory.Preadditive.HomWithAction`), on `Hⁱ(Hom(K, Y[0]))`
(`TauCeti.Algebra.Homology.LinearHomComplex.Single.Action`), and on `Ext¹(Hʲ(K), Y)`
(`TauCeti.Abelian.ExtWithAction`), naturality of `cochainKronecker`, `cochainKroneckerSection`, and
`cochainExtToHomology` in `Y` upgrades the universal coefficient sequence `R`-linearly.

When `C` has `HasExt C`, `k` is commutative, `i + j = 1`, `K.cycles j` is projective, and
`K.iCycles j` and `K.iCycles (-i)` split, cohomology decomposes `R`-linearly as
`HomologySingle₀WithAction k K ρ i ≃ₗ[R] ExtWithAction ρ (K.homology j) 1 ×
  HomWithAction ρ (K.homology (-i))`
(`TauCeti.cochainUniversalCoefficientEquivWithAction`).

## Main definitions and results

* `TauCeti.cochainKroneckerWithAction`, `TauCeti.cochainKroneckerWithAction_naturality`,
  `TauCeti.cochainKroneckerEquivWithAction`,
  `TauCeti.cochainKroneckerEquivOfProjectiveHomologyWithAction`, and
  `TauCeti.cochainKroneckerSectionWithAction`.
* `TauCeti.cochainExtToHomologyWithAction`, `TauCeti.cochainExtToHomologyWithAction_injective`,
  `TauCeti.exact_cochainExtToHomologyWithAction_cochainKroneckerWithAction`,
  `TauCeti.cochainExtToHomologyWithAction_naturality`, and
  `TauCeti.cochainUniversalCoefficientEquivWithAction`.

## Implementation notes

The `@[expose]` target-action type-synonym interface used across `HomWithAction`,
`HomologySingle₀WithAction`, and `ExtWithAction` adapts the design of
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
      cochainKroneckerSection k K Y i (HomWithAction.toHom ρ g) := by
  simp [cochainKroneckerSectionWithAction]

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
      cochainExtToHomology k K Y hij (ExtWithAction.toExt ρ e) := by
  simp [cochainExtToHomologyWithAction]

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
