/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Basic

/-!
# The universal property of the graded symmetric algebra

For a quasicoherent sheaf `F` on a scheme `X` and a graded quasicoherent algebra `A = ⨁ₙ Aₙ`,
a morphism of quasicoherent sheaves `φ : F ⟶ A₁` extends uniquely to a morphism of graded
quasicoherent algebras `Sym F ⟶ A`. In other words, the graded symmetric algebra functor is left
adjoint to the degree-one functor:

`gradedSymmetricAlgebraAdjunction X : gradedSymmetricAlgebra X ⊣ degreeOne`.

Its unit is the identification `F ≅ Sym¹ F` (`gradedSymmetricAlgebraAdjunction_unit`), an
isomorphism, matching the fact that `gradedSymmetricAlgebra X` is fully faithful: it identifies
quasicoherent sheaves with its essential image, the graded quasicoherent algebras freely
generated in degree one. Under graded relative `Spec` these are the coordinate algebras of the
linear schemes `Spec_X Sym F` over `X`.

The extension `Symⁿ F ⟶ Aₙ` is built over each open `U` from the universal property of the
symmetric algebra of the `Γ(X, U)`-module `Γ(F, U)`, with values in the graded ring
`⨁ n, Γ(Aₙ, U)` of sections of `A`, and then sheafified; its compatibility with the unit and
the multiplication is checked on sections and transported along the monoidal sheafification
adjunction. Uniqueness holds because `Sym F` is generated in degree one: its unit and its
multiplications are epimorphisms (`epi_one_gradedSymmetricAlgebra`,
`epi_mul_gradedSymmetricAlgebra`).

## Main declarations

* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraLift`: the morphism `Sym F ⟶ A` of graded
  quasicoherent algebras extending `φ : F ⟶ A₁`, characterized by
  `gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift`;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebra_hom_ext`: morphisms out of `Sym F` are
  determined in degree one;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraAdjunction`: the adjunction
  `gradedSymmetricAlgebra X ⊣ degreeOne`, whose unit is an isomorphism
  (`isIso_gradedSymmetricAlgebraAdjunction_unit`).

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
-/

public section

open CategoryTheory MonoidalCategory Opposite DirectSum

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory.CommMon GradedQuasicoherentAlgebra

universe u

noncomputable section

section Transport

/-! ### Sheafifying sectionwise maps out of symmetric powers -/

open TauCeti.SheafOfModules (ringCatSheaf sheafificationIso)

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}} {M : _root_.SheafOfModules.{u} (ringCatSheaf R)}
  {B : ℕ → _root_.SheafOfModules.{u} (ringCatSheaf R)}
  (ψ : ∀ n, (PresheafOfModulesOfCommRing.symmetricPower n).obj M.val ⟶ (B n).val)

/-- The transpose along sheafification of a family of sectionwise maps `ψ n : Symⁿ M.val ⟶ Bₙ`
out of the presheaf symmetric powers of `M`: a morphism `Symⁿ M ⟶ Bₙ` of sheaves of modules. -/
private abbrev sheafifiedLift (n : ℕ) : (_root_.SheafOfModules.symmetricPower R n).obj M ⟶ B n :=
  (_root_.SheafOfModules.symmetricPowerIso n M).hom ≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map (ψ n) ≫
      (sheafificationIso _ (B n)).hom

/-- Sectionwise maps compatible with the multiplications sheafify to maps compatible with the
multiplications. -/
private lemma sheafifiedLift_mul (mul : ∀ i j, B i ⊗ B j ⟶ B (i + j))
    (h : ∀ i j, (ψ i ⊗ₘ ψ j) ≫
      Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) (B i) (B j) ≫
        (mul i j).val = PresheafOfModulesOfCommRing.symmetricPowerMul M.val i j ≫ ψ (i + j))
    (i j : ℕ) :
    (sheafifiedLift ψ i ⊗ₘ sheafifiedLift ψ j) ≫ mul i j =
      _root_.SheafOfModules.symmetricPowerMul M i j ≫ sheafifiedLift ψ (i + j) := by
  refine GradedObject.map_mul_of_laxMonoidal
    (F := PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj))
    (e := fun n ↦ _root_.SheafOfModules.symmetricPowerIso n M) _ _
    (_root_.SheafOfModules.symmetricPowerMul_def M)
    (e' := fun n ↦ (sheafificationIso _ (B n)).symm)
    (fun i j ↦ Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) (B i) (B j) ≫
      (mul i j).val) mul (fun i j ↦ ?_) ψ (sheafifiedLift ψ) (fun n ↦ rfl) h i j
  have h : ((TauCeti.SheafOfModules.sheafificationForgetAdjunction R).homEquiv _ _).symm
      (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) (B i) (B j) ≫
        (mul i j).val) = ((B i).tensorUnderlyingIso (B j)).inv ≫ mul i j :=
    (Equiv.symm_apply_eq _).2 (TauCeti.SheafOfModules.forget_μ_comp_map (mul i j))
  rw [Adjunction.homEquiv_counit,
    TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app] at h
  rw [Iso.symm_hom, Iso.symm_hom, Iso.symm_inv]
  -- `h` displays the source of the sheafified map as `forget.obj (B i) ⊗ forget.obj (B j)`, the
  -- goal as `(B i).val ⊗ (B j).val`; these agree only up to unfolding `forget`.
  erw [h]
  rw [← Category.assoc, ← _root_.SheafOfModules.tensorUnderlyingIso_hom, Iso.hom_inv_id_assoc]

/-- Sectionwise maps compatible with the units sheafify to maps compatible with the units. -/
private lemma sheafifiedLift_one (one : _root_.SheafOfModules.unit (ringCatSheaf R) ⟶ B 0)
    (h : (PresheafOfModulesOfCommRing.symmetricPowerZeroIso R.obj).inv.app M.val ≫ ψ 0 =
      one.val) :
    (_root_.SheafOfModules.symmetricPowerZeroIso R).inv.app M ≫ sheafifiedLift ψ 0 = one := by
  rw [_root_.SheafOfModules.symmetricPowerZeroIso_inv_app]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- The sheafified presheaf maps are composable only up to the identification of
  -- `PresheafOfModulesOfCommRing R.obj` with presheaves over `(ringCatSheaf R).obj`.
  erw [← Functor.map_comp_assoc, h]
  rw [TauCeti.SheafOfModules.sheafificationIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- Sectionwise maps restricting to `φ` on `Sym¹ M.val ≅ M.val` sheafify to maps restricting to
`φ` on `Sym¹ M ≅ M`. -/
private lemma sheafifiedLift_degreeOne (φ : M ⟶ B 1)
    (h : (PresheafOfModulesOfCommRing.symmetricPowerOneIso R.obj).inv.app M.val ≫ ψ 1 = φ.val) :
    (_root_.SheafOfModules.symmetricPowerOneIso R).inv.app M ≫ sheafifiedLift ψ 1 = φ := by
  have h' : ψ 1 = (PresheafOfModulesOfCommRing.symmetricPowerOneIso R.obj).hom.app M.val ≫
      φ.val := by
    rw [← h]
    exact (Iso.hom_inv_id_app_assoc _ _ _).symm
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom,
    _root_.SheafOfModules.symmetricPowerOneIso_hom_app]
  dsimp only [sheafifiedLift]
  -- As in `sheafifiedLift_one`, `ψ 1` and its rewrite live over definitionally equal but
  -- syntactically different presheaf categories.
  erw [h', Functor.map_comp]
  rw [Category.assoc, TauCeti.SheafOfModules.sheafificationIso_hom_naturality]
  simp only [Category.assoc]

end Transport

section Sections

/-! ### The extension on sections -/

variable {X : Scheme.{u}} {F : X.Modules} {A : CommMon (GradedObject ℕ X.Modules)}

/-- Over an open `U`, the algebra map `Sym Γ(F, U) → ⨁ n, Γ(Aₙ, U)` extending the sections
`Γ(F, U) → Γ(A₁, U)` of `φ` into degree one. -/
private def sectionsLift (φ : F ⟶ A.X 1) (U : X.Opens) :
    SymmetricAlgebra Γ(X, U) (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U))
      →ₐ[Γ(X, U)] ⨁ n, Γ(A.X n, U) :=
  SymmetricAlgebra.lift ((DirectSum.lof Γ(X, U) ℕ (fun n ↦ Γ(A.X n, U)) 1) ∘ₗ
    ((Scheme.Modules.sectionsFunctor U).map φ).hom)

private lemma sectionsLift_ι (φ : F ⟶ A.X 1) (U : X.Opens)
    (m : PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) :
    sectionsLift φ U (SymmetricAlgebra.ι _ _ m) =
      DirectSum.of (fun n ↦ Γ(A.X n, U)) 1 (φ.app U m) :=
  SymmetricAlgebra.lift_ι_apply _ m

private lemma eq_of_eq_of {U : X.Opens} {z : ⨁ n, Γ(A.X n, U)} {k : ℕ} {w : Γ(A.X k, U)}
    (h : z = DirectSum.of _ k w) : z = DirectSum.of _ k (z k) := by
  subst h
  rw [DirectSum.of_eq_same]

/-- The extension on sections sends homogeneous elements of degree `n` into degree `n`. -/
private lemma sectionsLift_homogeneous (φ : F ⟶ A.X 1) (U : X.Opens) {n : ℕ}
    {x : SymmetricAlgebra Γ(X, U)
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U))}
    (hx : x ∈ SymmetricAlgebra.homogeneousSubmodule _ _ n) :
    sectionsLift φ U x = DirectSum.of _ n (sectionsLift φ U x n) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    refine eq_of_eq_of (w := GAlgebra.toFun (A := fun n ↦ Γ(A.X n, U)) r) ?_
    rw [AlgHom.commutes, DirectSum.algebraMap_apply]
  | add x y _ _ _ hx hy =>
    rw [map_add, hx, hy, DirectSum.add_apply, DirectSum.of_eq_same, DirectSum.of_eq_same,
      map_add]
  | mem_mul m hm i x _ ih =>
    obtain ⟨y, rfl⟩ := hm
    rw [show i.succ = 1 + i from Nat.succ_eq_one_add i]
    refine eq_of_eq_of (w := GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.X n, U)) (φ.app U y)
      (sectionsLift φ U x i)) ?_
    rw [map_mul, ih, sectionsLift_ι, DirectSum.of_mul_of, DirectSum.of_eq_same]

/-- The degree-`n` part `Symⁿ Γ(F, U) → Γ(Aₙ, U)` of the extension on sections. -/
private def presheafLiftApp (φ : F ⟶ A.X 1) (n : ℕ) (U : X.Opens) :
    (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)).symmetricPower n ⟶
      (Scheme.Modules.sectionsFunctor U).obj (A.X n) :=
  ConcreteCategory.ofHom (C := ModuleCat (X.presheaf.obj (op U)))
    (DirectSum.component (X.presheaf.obj (op U)) ℕ (fun n ↦ Γ(A.X n, U)) n ∘ₗ
    (sectionsLift φ U).toLinearMap ∘ₗ
      (SymmetricAlgebra.homogeneousSubmodule Γ(X, U)
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) n).subtype)

private lemma presheafLiftApp_apply (φ : F ⟶ A.X 1) (n : ℕ) (U : X.Opens)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)).symmetricPower n) :
    presheafLiftApp φ n U x = sectionsLift φ U x.1 n :=
  (rfl)

/-- The extension on sections commutes with restriction. -/
private lemma sectionsLift_restrict (φ : F ⟶ A.X 1) {U V : X.Opens} (f : V ⟶ U) :
    (sectionsLift φ V : SymmetricAlgebra Γ(X, V)
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op V)) →+* _).comp
      (SymmetricAlgebra.mapₛₗ
        ((ModuleCat.semilinearMapAddEquiv (X.presheaf.map f.op).hom _ _).symm
          (PresheafOfModulesOfCommRing.map (R := X.presheaf) F.val f.op))) =
      (A.restrictGradedSections f).comp (sectionsLift φ U : SymmetricAlgebra Γ(X, U)
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val (op U)) →+* _) := by
  refine SymmetricAlgebra.ringHom_ext (RingHom.ext fun r ↦ ?_) fun m ↦ ?_
  · simp
  · simp only [RingHom.comp_apply, SymmetricAlgebra.mapₛₗ_ι]
    -- The restricted generator lives in the sections over `V` written through the semilinear
    -- restriction map; `sectionsLift_ι` sees them only up to unfolding that map.
    erw [sectionsLift_ι, sectionsLift_ι, restrictGradedSections_of]
    exact congrArg _ (PresheafOfModules.naturality_apply φ.val f.op m)

/-- The degree-`n` part of the extension, as a morphism of presheaves of modules
`Symⁿ F.val ⟶ Aₙ.val` out of the presheaf symmetric power. -/
private def presheafLift (φ : F ⟶ A.X 1) (n : ℕ) :
    (PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj F.val ⟶ (A.X n).val :=
  PresheafOfModulesOfCommRing.homMk (fun U ↦ presheafLiftApp φ n U.unop)
    (fun {U V} f ↦ by
      ext x
      -- Restriction of scalars and the sections of the presheaves are `rfl`-wrappers that `rw`
      -- does not see through.
      erw [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply, ModuleCat.comp_apply,
        presheafLiftApp_apply, presheafLiftApp_apply,
        PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply]
      exact (congrArg (· n) (RingHom.congr_fun (sectionsLift_restrict φ f.unop) x.1)).trans
        (A.restrictGradedSections_apply f.unop _ n))

private lemma presheafLift_app_apply (φ : F ⟶ A.X 1) (n : ℕ) (U : X.Opensᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val U).symmetricPower n) :
    (presheafLift φ n).app U x = sectionsLift φ U.unop x.1 n :=
  (rfl)

variable (X) in
/-- The inclusion of `𝒪_X`-modules into presheaves of modules over the commutative structure
presheaf, the form in which its lax monoidal structure is used here. -/
private abbrev forgetPresheaf : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
  SheafOfModules.forget _

private instance : (forgetPresheaf X).LaxMonoidal :=
  TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf

/-- The extension is multiplicative on sections. -/
private lemma presheafLift_mul (φ : F ⟶ A.X 1) (i j : ℕ) :
    (presheafLift φ i ⊗ₘ presheafLift φ j) ≫
        Functor.LaxMonoidal.μ (forgetPresheaf X) (A.X i) (A.X j) ≫
          (forgetPresheaf X).map (A.toMon.mul i j) =
      PresheafOfModulesOfCommRing.symmetricPowerMul F.val i j ≫ presheafLift φ (i + j) := by
  ext1 U
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ ?_
  have hx := sectionsLift_homogeneous φ U.unop x.2
  have hy := sectionsLift_homogeneous φ U.unop y.2
  -- The left side is the homogeneous product of the two degree components (by definition of the
  -- tensor maps involved), and the right side is the degree-`(i + j)` component of the image of
  -- the product `x * y`.
  refine Eq.trans (b := (A.toMon.mul i j).app U.unop
      (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U.unop) _ _
        (sectionsLift φ U.unop x.1 i ⊗ₜ sectionsLift φ U.unop y.1 j))) (rfl) ?_
  refine Eq.trans ?_ (presheafLift_app_apply φ (i + j) U
    ((PresheafOfModulesOfCommRing.symmetricPowerMul F.val i j).app U (x ⊗ₜ y))).symm
  rw [← sections_gMul_def]
  -- The sections of the presheaf symmetric power are those of `ModuleCat.symmetricPower` only up
  -- to `rfl`.
  erw [PresheafOfModulesOfCommRing.symmetricPowerMul_app, ModuleCat.symmetricPower.coe_mul_tmul,
    map_mul, hx, hy, DirectSum.of_mul_of]
  simp only [DirectSum.of_eq_same]
  -- The two sides differ only in how the homogeneous components are typed.
  rfl

/-- The extension is unital on sections. -/
private lemma presheafLift_one (φ : F ⟶ A.X 1) :
    (PresheafOfModulesOfCommRing.symmetricPowerZeroIso X.presheaf).inv.app F.val ≫
        presheafLift φ 0 =
      A.toMon.one.val := by
  ext1 U
  -- `PresheafOfModulesOfCommRing.symmetricPowerZeroIso` is stated over `X.presheaf`, the
  -- composite over the ring presheaf of `X.ringCatSheaf`.
  erw [PresheafOfModules.comp_app, PresheafOfModulesOfCommRing.symmetricPowerZeroIso_inv_app_app]
  ext
  refine Eq.trans (presheafLift_app_apply φ 0 U _) ?_
  refine (congrArg (fun z ↦ sectionsLift φ U.unop z 0)
    (ModuleCat.symmetricPower.coe_iso₀_inv_apply _ 1)).trans ?_
  rw [map_one, map_one, DirectSum.one_def, DirectSum.of_eq_same, sections_gOne_def,
    Scheme.Modules.sectionsFunctor_ε]
  -- Both sides are the unit of `A` applied to `1`, read through the sections functor.
  rfl

/-- In degree one, the extension restricts to `φ` along `Sym¹ F.val ≅ F.val`. -/
private lemma presheafLift_degreeOne (φ : F ⟶ A.X 1) :
    (PresheafOfModulesOfCommRing.symmetricPowerOneIso X.presheaf).inv.app F.val ≫
        presheafLift φ 1 = φ.val := by
  ext1 U
  -- As in `presheafLift_one`.
  erw [PresheafOfModules.comp_app, PresheafOfModulesOfCommRing.symmetricPowerOneIso_inv_app_app]
  ext m
  refine Eq.trans (presheafLift_app_apply φ 1 U _) ?_
  refine (congrArg (fun z ↦ sectionsLift φ U.unop z 1)
    (ModuleCat.symmetricPower.coe_iso₁_inv_apply
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf) F.val U) m)).trans ?_
  refine (congrArg (· 1) (sectionsLift_ι φ U.unop m)).trans ?_
  rw [DirectSum.of_eq_same]
  -- Both sides are the sections of `φ` applied to `m`.
  rfl

variable (F) in
/-- The symmetric power `Symⁿ F`, typed as an `𝒪_X`-module so that the monoidal structure of
`X.Modules` applies to it. -/
private abbrev symPow (n : ℕ) : X.Modules :=
  (SheafOfModules.symmetricPower X.sheaf n).obj F

variable (F) in
/-- The multiplication `Symⁱ F ⊗ Symʲ F ⟶ Symⁱ⁺ʲ F`, typed in `X.Modules`. -/
private abbrev symPowMul (i j : ℕ) : symPow F i ⊗ symPow F j ⟶ symPow F (i + j) :=
  SheafOfModules.symmetricPowerMul F i j

/-- The degree-`n` component `Symⁿ F ⟶ Aₙ` of the extension of `φ`. -/
private def liftDegree (φ : F ⟶ A.X 1) (n : ℕ) : symPow F n ⟶ A.X n :=
  sheafifiedLift (R := X.sheaf) (B := A.X) (presheafLift φ) n

private lemma liftDegree_mul (φ : F ⟶ A.X 1) (i j : ℕ) :
    (liftDegree φ i ⊗ₘ liftDegree φ j) ≫ A.toMon.mul i j =
      symPowMul F i j ≫ liftDegree φ (i + j) :=
  sheafifiedLift_mul (R := X.sheaf) (presheafLift φ) A.toMon.mul (presheafLift_mul φ) i j

private lemma liftDegree_one (φ : F ⟶ A.X 1) :
    ((SheafOfModules.symmetricPowerZeroIso X.sheaf).inv.app F : 𝟙_ X.Modules ⟶ symPow F 0) ≫
      liftDegree φ 0 = A.toMon.one :=
  sheafifiedLift_one (R := X.sheaf) (presheafLift φ) A.toMon.one (presheafLift_one φ)

private lemma liftDegree_degreeOne (φ : F ⟶ A.X 1) :
    ((SheafOfModules.symmetricPowerOneIso X.sheaf).inv.app F : F ⟶ symPow F 1) ≫
      liftDegree φ 1 = φ :=
  sheafifiedLift_degreeOne (R := X.sheaf) (presheafLift φ) φ (presheafLift_degreeOne φ)

end Sections

/-! ### The universal property -/

variable {X : Scheme.{u}}

/-- Morphisms of graded quasicoherent algebras out of the graded symmetric algebra `Sym F` are
determined by their degree-one components. -/
theorem gradedSymmetricAlgebra_hom_ext {F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} {f g : (gradedSymmetricAlgebra X).obj F ⟶ A}
    (h : degreeOne.map f = degreeOne.map g) :
    f = g := by
  refine hom_ext_of_epi_mul ?_
  have h' := congrArg (fun f ↦ f.hom) h
  simp only [degree_map_hom] at h'
  exact (Iso.cancel_iso_hom_right _ _ (eqToIso (degree_obj_obj A 1).symm)).1
    ((Iso.cancel_iso_hom_left (eqToIso (degree_obj_obj ((gradedSymmetricAlgebra X).obj F) 1))
      _ _).1 h')

/-- The morphism of graded quasicoherent algebras `Sym F ⟶ A` extending a morphism
`φ : F ⟶ A₁` of quasicoherent sheaves into the degree-one component of `A`
(`gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift`). -/
def gradedSymmetricAlgebraLift {F : QuasicoherentSheaf X} {A : GradedQuasicoherentAlgebra X}
    (φ : F ⟶ degreeOne.obj A) : (gradedSymmetricAlgebra X).obj F ⟶ A :=
  homMkOfEq (funext (gradedSymmetricAlgebra_obj_obj_X F)) rfl (one_gradedSymmetricAlgebra F)
    (Category.comp_id _).symm (mul_gradedSymmetricAlgebra F)
    (fun i j ↦ by
      rw [eqToHom_refl, eqToHom_refl, Category.id_comp]
      exact (Category.comp_id _).symm)
    (liftDegree (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1)))
    (liftDegree_one _) (liftDegree_mul _)

/-- The degree-one component of `gradedSymmetricAlgebraLift φ` is `φ`, through the
identification `F ≅ Sym¹ F`. -/
@[reassoc (attr := simp)]
theorem gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift
    {F : QuasicoherentSheaf X} {A : GradedQuasicoherentAlgebra X} (φ : F ⟶ degreeOne.obj A) :
    (gradedSymmetricAlgebraDegreeOneIso X).inv.app F ≫
      degreeOne.map (gradedSymmetricAlgebraLift φ) = φ := by
  ext1
  have h1 := liftDegree_degreeOne (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1))
  have hL : (gradedSymmetricAlgebraLift φ).hom.hom.hom 1 =
      eqToHom (gradedSymmetricAlgebra_obj_obj_X F 1) ≫
        liftDegree (A := A.obj) (φ.hom ≫ eqToHom (degree_obj_obj A 1)) 1 ≫ eqToHom rfl :=
    homMkOfEq_hom_hom_hom _ _ _ _ _ _ _ _ _ 1
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    gradedSymmetricAlgebraDegreeOneIso_inv_app_hom, degree_map_hom, hL, Category.assoc]
  -- The transports between the components of `Sym F` and the symmetric powers are composed partly
  -- in `SheafOfModules (ringCatSheaf X.sheaf)` and partly in `X.Modules`, whose instances `simp`
  -- does not identify, so they are removed up to heterogeneous equality.
  refine eq_of_heq ((heq_comp rfl rfl (degree_obj_obj A 1) HEq.rfl ?_).trans
    ((heq_of_eq h1).trans (comp_eqToHom_heq _ _)))
  exact (eqToHom_comp_heq _ _).trans ((eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))))

variable (X) in
/-- The graded symmetric algebra functor is left adjoint to the degree-one functor: morphisms of
graded quasicoherent algebras `Sym F ⟶ A` correspond to morphisms of quasicoherent sheaves
`F ⟶ A₁`, by restriction to degree one along `F ≅ Sym¹ F` and by `gradedSymmetricAlgebraLift`. -/
def gradedSymmetricAlgebraAdjunction :
    gradedSymmetricAlgebra X ⊣ (degreeOne : GradedQuasicoherentAlgebra X ⥤ QuasicoherentSheaf X) :=
  Adjunction.mkOfHomEquiv
    { homEquiv F A :=
        { toFun f := (gradedSymmetricAlgebraDegreeOneIso X).inv.app F ≫ degreeOne.map f
          invFun := gradedSymmetricAlgebraLift
          left_inv f := gradedSymmetricAlgebra_hom_ext (by
            rw [← cancel_epi ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F),
              gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift])
          right_inv := gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift }
      homEquiv_naturality_left_symm {F' F A} g φ := by
        refine gradedSymmetricAlgebra_hom_ext ?_
        simp only [Equiv.coe_fn_symm_mk]
        rw [← cancel_epi ((gradedSymmetricAlgebraDegreeOneIso X).inv.app F'),
          gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift, Functor.map_comp,
          ← Functor.comp_map, ← NatTrans.naturality_assoc, Functor.id_map,
          gradedSymmetricAlgebraDegreeOneIso_inv_app_comp_degreeOne_map_lift]
      homEquiv_naturality_right f g := by
        simp only [Equiv.coe_fn_mk, Functor.map_comp, Category.assoc] }

/-- The bijection of `gradedSymmetricAlgebraAdjunction` restricts a morphism `Sym F ⟶ A` to
degree one. -/
@[simp]
theorem gradedSymmetricAlgebraAdjunction_homEquiv_apply {F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} (f : (gradedSymmetricAlgebra X).obj F ⟶ A) :
    (gradedSymmetricAlgebraAdjunction X).homEquiv F A f =
      (gradedSymmetricAlgebraDegreeOneIso X).inv.app F ≫ degreeOne.map f := by
  simp only [gradedSymmetricAlgebraAdjunction, Adjunction.mkOfHomEquiv_homEquiv, Equiv.coe_fn_mk]

/-- The inverse bijection of `gradedSymmetricAlgebraAdjunction` is `gradedSymmetricAlgebraLift`. -/
@[simp]
theorem gradedSymmetricAlgebraAdjunction_homEquiv_symm_apply {F : QuasicoherentSheaf X}
    {A : GradedQuasicoherentAlgebra X} (φ : F ⟶ degreeOne.obj A) :
    ((gradedSymmetricAlgebraAdjunction X).homEquiv F A).symm φ = gradedSymmetricAlgebraLift φ := by
  simp only [gradedSymmetricAlgebraAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    Equiv.coe_fn_symm_mk]

variable (X) in
/-- The unit of `gradedSymmetricAlgebraAdjunction` is the identification `F ≅ Sym¹ F`. -/
theorem gradedSymmetricAlgebraAdjunction_unit :
    (gradedSymmetricAlgebraAdjunction X).unit = (gradedSymmetricAlgebraDegreeOneIso X).inv := by
  ext F : 2
  rw [← Adjunction.homEquiv_id, gradedSymmetricAlgebraAdjunction_homEquiv_apply,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The unit of `gradedSymmetricAlgebraAdjunction` is an isomorphism. -/
instance isIso_gradedSymmetricAlgebraAdjunction_unit :
    IsIso (gradedSymmetricAlgebraAdjunction X).unit := by
  rw [gradedSymmetricAlgebraAdjunction_unit]
  infer_instance

end

end TauCeti.AlgebraicGeometry
