/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorProduct
public import TauCeti.AlgebraicGeometry.Modules.Algebra.Pushforward
public import TauCeti.AlgebraicGeometry.Modules.GradedAlgebra.Sections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic
public import TauCeti.RingTheory.ReesAlgebra.Grading

/-!
# The Rees algebra of an ideal sheaf

Let `I ⊆ 𝒪_X` be an ideal sheaf on a scheme `X`. Its *Rees algebra* is the graded
`𝒪_X`-algebra

`𝒪_X ⊕ I ⊕ I² ⊕ ⋯ = ⨁ₙ Iⁿ`,

whose degree-`n` component is the ideal sheaf `Iⁿ` and whose multiplication `Iⁱ ⊗ Iʲ ⟶ Iⁱ⁺ʲ`
multiplies local functions. It is the graded subalgebra of the polynomial algebra `𝒪_X[t]` with
`Iⁿ tⁿ` in degree `n`. Every ideal sheaf is quasi-coherent
(`Scheme.IdealSheafData.isQuasicoherent_sheaf`), so the Rees algebra is a graded quasi-coherent
algebra, and its relative `Proj` over `X` is the blowup of `X` along the closed subscheme `V(I)`.
Over an affine open `U` its sections in degree `n` are the ideal `I(U)ⁿ`
(`Scheme.IdealSheafData.range_sheafι_app_pow`).

The homogeneous multiplication is `Scheme.IdealSheafData.sheafMul` for the ideal sheaves `Iⁱ` and
`Iʲ`, read through `Iⁱ * Iʲ = Iⁱ⁺ʲ`, and the unit is the identification `𝒪_X = I⁰`. Each `Iⁿ`
includes into `𝒪_X` by a monomorphism, under which the multiplication becomes the multiplication
`𝒪_X ⊗ 𝒪_X ≅ 𝒪_X` of the structure sheaf (`Scheme.IdealSheafData.reesMul_sheafι`). The graded
unit, associativity and commutativity laws are therefore those of the commutative monoid `𝒪_X`
in the symmetric monoidal category of `𝒪_X`-modules.

Over an affine open `U`, the graded ring of sections `⨁ n, Γ(Iⁿ, U)` of the Rees algebra is the
Rees algebra `Γ(X, U)[I(U)t] ⊆ Γ(X, U)[t]` of the ideal `I(U) ⊆ Γ(X, U)`
(`Scheme.IdealSheafData.reesAlgebraSectionsEquiv`): reading sections of `Iⁿ` as regular functions,
a section `x` of `Iⁿ` corresponds to the monomial `x tⁿ`. This identifies the affine charts of the
relative `Proj` of the Rees algebra with the blowups of affine schemes.

## Main definitions

* `Scheme.IdealSheafData.reesComponent I n`: the homogeneous component `Iⁿ`.
* `Scheme.IdealSheafData.reesMul I i j`: the multiplication `Iⁱ ⊗ Iʲ ⟶ Iⁱ⁺ʲ`.
* `Scheme.IdealSheafData.reesOne I`: the unit `𝒪_X ⟶ I⁰`.
* `Scheme.IdealSheafData.reesAlgebra I`: the Rees algebra `⨁ₙ Iⁿ`, as a graded quasi-coherent
  `𝒪_X`-algebra.
* `Scheme.IdealSheafData.reesAlgebraSectionsEquiv I hU`: over an affine open `U`, the isomorphism
  of `Γ(X, U)`-algebras from `⨁ n, Γ(Iⁿ, U)` to the Rees algebra `Γ(X, U)[I(U)t]`.

## Main results

* `Scheme.IdealSheafData.reesMul_sheafι` and `Scheme.IdealSheafData.reesOne_sheafι`: the
  multiplication and the unit are the restrictions of those of `𝒪_X`.
* `Scheme.IdealSheafData.reesAlgebra_obj_X`, `Scheme.IdealSheafData.mul_reesAlgebra` and
  `Scheme.IdealSheafData.one_reesAlgebra`: the homogeneous components, multiplication and unit of
  the Rees algebra.
* `Scheme.IdealSheafData.coe_reesAlgebraSectionsEquiv_of` and
  `Scheme.IdealSheafData.reesAlgebraSectionsEquiv_mem_grade_iff`: the isomorphism
  `reesAlgebraSectionsEquiv` sends a section `x` of `Iⁿ` to `x tⁿ`, and matches the gradings.

## Implementation notes

The Rees algebra is built from the named family `Scheme.IdealSheafData.reesComponent I`, not
from `fun n ↦ (I ^ n).sheaf`. `GradedQuasicoherentAlgebra.ofHomogeneous` states its unit,
associativity and commutativity laws through the family applied to degrees, and the kernel
instantiates them without beta-reducing, so with a `fun` it must match each law against
beta-redexes. Where the monoidal structure of `X.Modules` can be unfolded, as when a non-module
file or the API documentation asks for the equation lemma of `reesAlgebra`, the kernel unfolds
that structure instead and does not finish. With the named family, each law is literally the
hypothesis it discharges.

## References

* [The Stacks Project, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF): the blowing up of a
  quasi-coherent sheaf of ideals is the relative `Proj` of `⨁ₙ Iⁿ`.
* R. Hartshorne, *Algebraic Geometry*, Section II.7, *Blowing up*.
-/

public section

open CategoryTheory MonoidalCategory DirectSum Polynomial

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The homogeneous component `Iⁿ` of the Rees algebra of `I`: the ideal sheaf `Iⁿ`, as an
`𝒪_X`-module. -/
abbrev reesComponent (n : ℕ) : X.Modules :=
  (I ^ n).sheaf

/-- The inclusion `I ⟶ 𝒪_X`, read as a morphism to the monoidal unit of `X.Modules`, so that
composites with morphisms out of tensor products are formed in a single category. -/
private def sheafιUnit (J : X.IdealSheafData) : J.sheaf ⟶ 𝟙_ X.Modules :=
  J.sheafι

private instance (J : X.IdealSheafData) : Mono J.sheafιUnit :=
  inferInstanceAs (Mono J.sheafι)

/-- Transport along an equality of ideal sheaves commutes with the inclusions into `𝒪_X`. -/
@[reassoc]
private lemma eqToHom_sheafιUnit {J K : X.IdealSheafData} (h : J = K) :
    eqToHom (congrArg sheaf h) ≫ K.sheafιUnit = J.sheafιUnit := by
  subst h
  exact Category.id_comp _

/-- Transport along an equality of exponents commutes with the inclusions of the powers of `I`
into `𝒪_X`. The equality of exponents is a side condition, so that `simp` can apply this to any
transport between powers of `I`. -/
@[reassoc]
private lemma eqToHom_pow_sheafιUnit {m n : ℕ} (h : m = n) (h' : (I ^ m).sheaf = (I ^ n).sheaf) :
    eqToHom h' ≫ (I ^ n).sheafιUnit = (I ^ m).sheafιUnit := by
  subst h
  exact Category.id_comp _

/-- The multiplication `Iⁱ ⊗ Iʲ ⟶ Iⁱ⁺ʲ` of the Rees algebra of `I`: multiplication of local
functions, through `Iⁱ * Iʲ = Iⁱ⁺ʲ`. -/
def reesMul (i j : ℕ) : I.reesComponent i ⊗ I.reesComponent j ⟶ I.reesComponent (i + j) :=
  sheafMul (I ^ i) (I ^ j) ≫ eqToHom (congrArg sheaf (pow_add I i j).symm)

/-- The multiplication of the Rees algebra, followed by the inclusion `Iⁱ⁺ʲ ⟶ 𝒪_X`, is the
inclusion `Iⁱ ⊗ Iʲ ⟶ 𝒪_X ⊗ 𝒪_X` followed by the multiplication of `𝒪_X`. -/
@[reassoc]
theorem reesMul_sheafι (i j : ℕ) :
    I.reesMul i j ≫ (I ^ (i + j)).sheafι =
      ((I ^ i).sheafι ⊗ₘ (I ^ j).sheafι) ≫ (λ_ (𝟙_ X.Modules)).hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (sheafMul (I ^ i) (I ^ j) ≫ ·) (eqToHom_sheafιUnit (pow_add I i j).symm)).trans
      (sheafMul_sheafι (I ^ i) (I ^ j)))

/-- `reesMul_sheafι`, stated with the inclusions read as morphisms to the monoidal unit. -/
@[reassoc]
private lemma reesMul_sheafιUnit (i j : ℕ) :
    I.reesMul i j ≫ (I ^ (i + j)).sheafιUnit =
      ((I ^ i).sheafιUnit ⊗ₘ (I ^ j).sheafιUnit) ≫ (λ_ (𝟙_ X.Modules)).hom :=
  I.reesMul_sheafι i j

/-- The unit `𝒪_X ⟶ I⁰` of the Rees algebra of `I`: every regular function is a section of
`I⁰ = 𝒪_X`. -/
def reesOne : 𝟙_ X.Modules ⟶ I.reesComponent 0 :=
  (I ^ 0).sheafLift (𝟙 _) fun U _ ↦ by
    rw [pow_zero, one_eq_top, sections_top]
    trivial

/-- The unit of the Rees algebra, followed by the inclusion `I⁰ ⟶ 𝒪_X`, is the identity. -/
@[simp, reassoc]
theorem reesOne_sheafι : I.reesOne ≫ (I ^ 0).sheafι = 𝟙 _ :=
  sheafLift_ι _ _ _

/-- `reesOne_sheafι`, stated with the inclusion read as a morphism to the monoidal unit. -/
@[reassoc]
private lemma reesOne_sheafιUnit : I.reesOne ≫ (I ^ 0).sheafιUnit = 𝟙 _ :=
  I.reesOne_sheafι

/-- The unit of the Rees algebra is a left identity for its multiplication. -/
private lemma reesOne_whiskerRight_reesMul (n : ℕ) :
    (I.reesOne ▷ I.reesComponent n) ≫ I.reesMul 0 n =
      (λ_ (I.reesComponent n)).hom ≫ eqToHom (congrArg I.reesComponent (zero_add n).symm) := by
  rw [← cancel_mono (I ^ (0 + n)).sheafιUnit]
  simp (disch := omega) only [Category.assoc, reesMul_sheafιUnit, eqToHom_pow_sheafιUnit,
    whiskerRight_comp_tensorHom_assoc, reesOne_sheafιUnit]
  monoidal

/-- The unit of the Rees algebra is a right identity for its multiplication. -/
private lemma whiskerLeft_reesOne_reesMul (n : ℕ) :
    (I.reesComponent n ◁ I.reesOne) ≫ I.reesMul n 0 =
      (ρ_ (I.reesComponent n)).hom ≫ eqToHom (congrArg I.reesComponent (add_zero n).symm) := by
  rw [← cancel_mono (I ^ (n + 0)).sheafιUnit]
  simp (disch := omega) only [Category.assoc, reesMul_sheafιUnit, eqToHom_pow_sheafιUnit,
    whiskerLeft_comp_tensorHom_assoc, reesOne_sheafιUnit]
  monoidal

/-- The multiplication of the Rees algebra is associative. -/
private lemma reesMul_assoc (i j k : ℕ) :
    (I.reesMul i j ▷ I.reesComponent k) ≫ I.reesMul (i + j) k =
      (α_ _ _ _).hom ≫ (I.reesComponent i ◁ I.reesMul j k) ≫ I.reesMul i (j + k) ≫
        eqToHom (congrArg I.reesComponent (add_assoc i j k).symm) := by
  rw [← cancel_mono (I ^ (i + j + k)).sheafιUnit]
  simp (disch := omega) only [Category.assoc, reesMul_sheafιUnit, eqToHom_pow_sheafιUnit,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  -- Both sides are `(Iⁱ ⊗ Iʲ) ⊗ Iᵏ ⟶ (𝒪_X ⊗ 𝒪_X) ⊗ 𝒪_X` followed by structural isomorphisms.
  monoidal

/-- The multiplication of the Rees algebra is commutative. -/
private lemma braiding_reesMul (i j : ℕ) :
    (β_ (I.reesComponent i) (I.reesComponent j)).hom ≫ I.reesMul j i =
      I.reesMul i j ≫ eqToHom (congrArg I.reesComponent (add_comm i j)) := by
  rw [← cancel_mono (I ^ (j + i)).sheafιUnit]
  simp (disch := omega) only [Category.assoc, reesMul_sheafιUnit, eqToHom_pow_sheafιUnit,
    ← BraidedCategory.braiding_naturality_assoc]
  -- The remaining identity is the commutativity of the multiplication of `𝒪_X`.
  exact congrArg (_ ≫ ·) (IsCommMonObj.mul_comm (𝟙_ X.Modules))

/-- The Rees algebra `⨁ₙ Iⁿ` of an ideal sheaf `I`, as a graded quasi-coherent `𝒪_X`-algebra.
Its degree-`n` component is the ideal sheaf `Iⁿ` (`reesAlgebra_obj_X`), its multiplication is
multiplication of local functions (`mul_reesAlgebra`, `reesMul_sheafι`) and its unit is the
identification `𝒪_X = I⁰` (`one_reesAlgebra`, `reesOne_sheafι`). -/
def reesAlgebra : GradedQuasicoherentAlgebra X :=
  GradedQuasicoherentAlgebra.ofHomogeneous I.reesComponent I.reesOne I.reesMul
    I.reesOne_whiskerRight_reesMul I.whiskerLeft_reesOne_reesMul I.reesMul_assoc
    I.braiding_reesMul

/-- The homogeneous components of the Rees algebra of `I` are the powers `Iⁿ`. -/
@[simp]
theorem reesAlgebra_obj_X : I.reesAlgebra.obj.X = fun n ↦ (I ^ n).sheaf :=
  GradedQuasicoherentAlgebra.ofHomogeneous_obj_X _ _ _ _ _ _ _

/-- The homogeneous multiplication of the Rees algebra of `I` is `reesMul`, up to the
identification `reesAlgebra_obj_X` of its components with the powers of `I`. -/
@[simp]
theorem mul_reesAlgebra (i j : ℕ) :
    I.reesAlgebra.obj.toMon.mul i j =
      (eqToHom (by rw [reesAlgebra_obj_X]) :
        I.reesAlgebra.obj.X i ⊗ I.reesAlgebra.obj.X j ⟶ _) ≫ I.reesMul i j ≫
        eqToHom (congrFun I.reesAlgebra_obj_X (i + j)).symm :=
  GradedQuasicoherentAlgebra.mul_ofHomogeneous _ _ _ _ _ _ _ i j

/-- The unit of the Rees algebra of `I` is `reesOne`, up to the identification
`reesAlgebra_obj_X` of its degree-zero component with `I⁰`. -/
@[simp]
theorem one_reesAlgebra :
    I.reesAlgebra.obj.toMon.one = I.reesOne ≫ eqToHom (congrFun I.reesAlgebra_obj_X 0).symm :=
  GradedQuasicoherentAlgebra.one_ofHomogeneous _ _ _ _ _ _ _

/-- The unit `𝒪_X ⟶ I⁰` of the Rees algebra is an isomorphism, inverse to the inclusion
`I⁰ ⟶ 𝒪_X` of the unit ideal sheaf. -/
instance isIso_reesOne : IsIso I.reesOne := by
  have : IsIso (I ^ 0).sheafι := by
    rw [pow_zero, one_eq_top]
    infer_instance
  have : IsIso (I.reesOne ≫ (I ^ 0).sheafι) := by
    rw [reesOne_sheafι]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (I ^ 0).sheafι

/-- The unit `𝒪_X ⟶ I⁰` of the Rees algebra, as a commutative monoid object, is an
isomorphism. -/
instance isIso_one_reesAlgebra : IsIso I.reesAlgebra.obj.toMon.one := by
  rw [one_reesAlgebra]
  exact (asIso I.reesOne ≪≫ eqToIso (congrFun I.reesAlgebra_obj_X 0).symm).isIso_hom

/-! ### The sections of the Rees algebra -/

section Sections

/-- The inclusion `Iⁿ ⟶ 𝒪_X` of the degree-`n` component of the Rees algebra of `I`. -/
private def reesι (n : ℕ) : I.reesAlgebra.obj.X n ⟶ 𝟙_ X.Modules :=
  eqToHom (congrFun I.reesAlgebra_obj_X n) ≫ (I ^ n).sheafι

/-- The multiplicativity of the inclusions `Iⁿ ⟶ 𝒪_X`, stated for an arbitrary family `M` of
modules identified with the powers of `I`, so that the identification can be eliminated. -/
private lemma eqToHom_comp_sheafι_mul {M : ℕ → X.Modules} (hM : M = fun n ↦ (I ^ n).sheaf)
    {i j : ℕ} {mul : M i ⊗ M j ⟶ M (i + j)}
    (hmul : mul = eqToHom (by rw [hM]) ≫ I.reesMul i j ≫ eqToHom (congrFun hM (i + j)).symm) :
    mul ≫ eqToHom (congrFun hM (i + j)) ≫ (I ^ (i + j)).sheafι =
      ((eqToHom (congrFun hM i) ≫ (I ^ i).sheafι) ⊗ₘ (eqToHom (congrFun hM j) ≫ (I ^ j).sheafι)) ≫
        (λ_ (𝟙_ X.Modules)).hom := by
  subst hM hmul
  simp only [eqToHom_refl]
  -- `erw`: the identities live in `X.Modules`, while `sheafι` is typed with codomain the unit
  -- sheaf of modules rather than `𝟙_ X.Modules`, so the identity laws only match up to unfolding
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id]
  exact I.reesMul_sheafι i j

/-- The inclusions of the components of the Rees algebra into `𝒪_X` are multiplicative. -/
private lemma reesι_mul (i j : ℕ) :
    I.reesAlgebra.obj.toMon.mul i j ≫ I.reesι (i + j) =
      (I.reesι i ⊗ₘ I.reesι j) ≫ (λ_ (𝟙_ X.Modules)).hom :=
  I.eqToHom_comp_sheafι_mul I.reesAlgebra_obj_X (I.mul_reesAlgebra i j)

/-- The unit law of the inclusion `I⁰ ⟶ 𝒪_X`, stated for an arbitrary family `M` of modules
identified with the powers of `I`, so that the identification can be eliminated. -/
private lemma one_comp_eqToHom_comp_sheafι {M : ℕ → X.Modules} (hM : M = fun n ↦ (I ^ n).sheaf)
    {one : 𝟙_ X.Modules ⟶ M 0} (hone : one = I.reesOne ≫ eqToHom (congrFun hM 0).symm) :
    one ≫ eqToHom (congrFun hM 0) ≫ (I ^ 0).sheafι = 𝟙 _ := by
  subst hM hone
  simp only [eqToHom_refl]
  -- `erw`: as in `eqToHom_comp_sheafι_mul`, the codomain of `sheafι` is the unit sheaf of modules
  erw [Category.id_comp, Category.comp_id]
  exact I.reesOne_sheafι

/-- The inclusion of the degree-zero component of the Rees algebra into `𝒪_X` is a left inverse
of its unit. -/
private lemma reesι_one : I.reesAlgebra.obj.toMon.one ≫ I.reesι 0 = 𝟙 _ :=
  I.one_comp_eqToHom_comp_sheafι I.reesAlgebra_obj_X I.one_reesAlgebra

variable (U : X.Opens)

/-- The inclusion `Iⁿ ⟶ 𝒪_X` on sections over `U`, with values in the regular functions
`Γ(X, U)`. -/
private def reesSec (n : ℕ) : Γ(I.reesAlgebra.obj.X n, U) →+ Γ(X, U) :=
  ((I.reesι n).app U).hom

/-- The inclusion `Iⁱ⁺ʲ ⟶ 𝒪_X` sends a product of sections of `Iⁱ` and `Iʲ` in the graded ring of
sections of the Rees algebra to the product of regular functions. -/
private lemma reesSec_gMul {i j : ℕ} (x : Γ(I.reesAlgebra.obj.X i, U))
    (y : Γ(I.reesAlgebra.obj.X j, U)) :
    I.reesSec U (i + j) (GradedMonoid.GMul.mul (A := fun n ↦ Γ(I.reesAlgebra.obj.X n, U)) x y) =
      I.reesSec U i x * I.reesSec U j y := by
  have h := ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · U) (I.reesι_mul i j))
    (Functor.LaxMonoidal.μ (Scheme.Modules.sectionsFunctor U) _ _ (x ⊗ₜ y))
  have hμ := ConcreteCategory.congr_hom (Functor.LaxMonoidal.μ_natural
    (Scheme.Modules.sectionsFunctor U) (I.reesι i) (I.reesι j)) (x ⊗ₜ y)
  rw [CommMon.sections_gMul_def]
  exact h.trans ((congrArg ((λ_ (𝟙_ X.Modules)).hom.app U) hμ.symm).trans
    (Scheme.leftUnitor_hom_app_μ_tmul U _ _))

/-- The inclusion `I⁰ ⟶ 𝒪_X` sends the structure map of the graded ring of sections of the Rees
algebra to the identity of `Γ(X, U)`. -/
private lemma reesSec_toFun (r : Γ(X, U)) :
    I.reesSec U 0
        (GAlgebra.toFun (R := Γ(X, U)) (A := fun n ↦ Γ(I.reesAlgebra.obj.X n, U)) r) = r := by
  have h := ConcreteCategory.congr_hom (congrArg (Scheme.Modules.Hom.app · U) I.reesι_one)
    (Functor.LaxMonoidal.ε (Scheme.Modules.sectionsFunctor U) r)
  rw [CommMon.gAlgebraSections_toFun]
  refine h.trans ?_
  rw [Scheme.Modules.sectionsFunctor_ε]
  rfl

/-- The inclusion `Iⁿ ⟶ 𝒪_X` is injective on sections. -/
private lemma reesSec_injective (n : ℕ) : Function.Injective (I.reesSec U n) := fun _ _ h ↦
  (ConcreteCategory.bijective_of_isIso
    ((eqToHom (congrFun I.reesAlgebra_obj_X n)).app U)).1 ((I ^ n).sheafι_app_injective U h)

/-- Over an affine open `U`, the sections of `Iⁿ` are the regular functions in `I(U)ⁿ`. -/
private lemma range_reesSec (U : X.affineOpens) (n : ℕ) :
    Set.range (I.reesSec U n) = ((I.ideal U ^ n : Ideal Γ(X, U)) : Set Γ(X, U)) := by
  rw [← range_sheafι_app_pow]
  exact (ConcreteCategory.bijective_of_isIso
    ((eqToHom (congrFun I.reesAlgebra_obj_X n)).app U)).2.range_comp _

/-- The inclusion `I⁰ ⟶ 𝒪_X` sends the unit of the graded ring of sections of the Rees algebra to
`1`. -/
private lemma reesSec_gOne :
    I.reesSec U 0 (GradedMonoid.GOne.one (A := fun n ↦ Γ(I.reesAlgebra.obj.X n, U))) = 1 := by
  have h := I.reesSec_toFun U 1
  rw [CommMon.gAlgebraSections_toFun] at h
  rwa [CommMon.sections_gOne_def]

end Sections

/-! ### The Rees algebra of the sections over an affine open -/

section Affine

variable (U : X.Opens)

/-- The ring homomorphism `⨁ n, Γ(Iⁿ, U) →+* Γ(X, U)[t]` sending a section `x` of `Iⁿ` to the
monomial `x tⁿ`. -/
private def toPolynomial : (⨁ n, Γ(I.reesAlgebra.obj.X n, U)) →+* Γ(X, U)[X] :=
  DirectSum.toSemiring (fun n ↦ (monomial n).toAddMonoidHom.comp (I.reesSec U n))
    ((congrArg (monomial 0) (I.reesSec_gOne U)).trans monomial_zero_one)
    (fun x y ↦ (congrArg (monomial _) (I.reesSec_gMul U x y)).trans
      (monomial_mul_monomial _ _ _ _).symm)

/-- `toPolynomial` sends a section `x` of `Iⁿ` to the monomial `x tⁿ`. -/
private lemma toPolynomial_of (n : ℕ) (x : Γ(I.reesAlgebra.obj.X n, U)) :
    I.toPolynomial U (DirectSum.of _ n x) = monomial n (I.reesSec U n x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The coefficient of `tⁿ` in the image under `toPolynomial` is the degree-`n` component. -/
private lemma coeff_toPolynomial (x : ⨁ n, Γ(I.reesAlgebra.obj.X n, U)) (n : ℕ) :
    (I.toPolynomial U x).coeff n = I.reesSec U n (x n) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of x]
  simp only [map_sum, toPolynomial_of, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
    DFinsupp.mem_support_toFun, ne_eq, ite_not]
  split_ifs with h
  · rw [h, map_zero]
  · rfl

/-- `toPolynomial` is a homomorphism of `Γ(X, U)`-algebras. -/
private lemma toPolynomial_algebraMap (r : Γ(X, U)) :
    I.toPolynomial U (algebraMap Γ(X, U) _ r) = C r := by
  rw [DirectSum.algebraMap_apply, toPolynomial_of, reesSec_toFun, monomial_zero_left]

variable {U} (hU : IsAffineOpen U)
include hU

/-- Over an affine open, `toPolynomial` takes values in the Rees algebra of `I(U)`. -/
private lemma toPolynomial_mem (x : ⨁ n, Γ(I.reesAlgebra.obj.X n, U)) :
    I.toPolynomial U x ∈ _root_.reesAlgebra (I.ideal ⟨U, hU⟩) := by
  refine (mem_reesAlgebra_iff _ _).mpr fun n ↦ ?_
  rw [coeff_toPolynomial, ← SetLike.mem_coe, ← range_reesSec I ⟨U, hU⟩]
  exact Set.mem_range_self _

/-- Over an affine open, `toPolynomial` is a bijection onto the Rees algebra of `I(U)`. -/
private lemma bijective_toPolynomial :
    Function.Bijective fun x ↦ (⟨I.toPolynomial U x, I.toPolynomial_mem hU x⟩ :
      _root_.reesAlgebra (I.ideal ⟨U, hU⟩)) := by
  classical
  refine ⟨fun x y h ↦ DFinsupp.ext fun n ↦ I.reesSec_injective U n ?_, fun f ↦ ?_⟩
  · rw [← coeff_toPolynomial, ← coeff_toPolynomial]
    exact congrArg (fun f : _root_.reesAlgebra (I.ideal ⟨U, hU⟩) ↦ (f : Γ(X, U)[X]).coeff n) h
  · -- each coefficient `fₙ ∈ I(U)ⁿ` is the image of a section of `Iⁿ`
    have hf (n : ℕ) : (f : Γ(X, U)[X]).coeff n ∈ Set.range (I.reesSec U n) := by
      rw [range_reesSec I ⟨U, hU⟩]
      exact (mem_reesAlgebra_iff _ _).mp f.2 n
    choose y hy using hf
    refine ⟨∑ n ∈ (f : Γ(X, U)[X]).support, DirectSum.of _ n (y n), Subtype.ext ?_⟩
    ext m
    simp only [map_sum, toPolynomial_of, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', hy]
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.mp h).symm

/-- **The sections of the Rees algebra over an affine open.** Over an affine open `U` of `X`, the
graded ring of sections `⨁ n, Γ(Iⁿ, U)` of the Rees algebra of `I` is the Rees algebra
`Γ(X, U)[I(U)t]` of the ideal `I(U)`: a section `x` of `Iⁿ` corresponds to the monomial `x tⁿ`
(`coe_reesAlgebraSectionsEquiv_of`), and this isomorphism matches the gradings
(`reesAlgebraSectionsEquiv_mem_grade_iff`). -/
def reesAlgebraSectionsEquiv :
    (⨁ n, Γ(I.reesAlgebra.obj.X n, U)) ≃ₐ[Γ(X, U)] _root_.reesAlgebra (I.ideal ⟨U, hU⟩) :=
  AlgEquiv.ofBijective
    { toFun x := ⟨I.toPolynomial U x, I.toPolynomial_mem hU x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x y)
      commutes' r := Subtype.ext <| by
        rw [Subalgebra.coe_algebraMap, algebraMap_eq]
        exact I.toPolynomial_algebraMap U r }
    (I.bijective_toPolynomial hU)

/-- The isomorphism `reesAlgebraSectionsEquiv` sends a section `x` of `Iⁿ` over `U` to the monomial
`x tⁿ`, where `x` is read as a regular function through the inclusion `Iⁿ ⟶ 𝒪_X`. -/
@[simp]
theorem coe_reesAlgebraSectionsEquiv_of (n : ℕ) (x : Γ(I.reesAlgebra.obj.X n, U)) :
    (I.reesAlgebraSectionsEquiv hU (DirectSum.of _ n x) : Γ(X, U)[X]) =
      monomial (R := Γ(X, U)) n
        ((I ^ n).sheafι.app U ((eqToHom (congrFun I.reesAlgebra_obj_X n)).app U x)) :=
  I.toPolynomial_of U n x

/-- The isomorphism `reesAlgebraSectionsEquiv` matches the grading of `⨁ n, Γ(Iⁿ, U)` by its
summands with the grading of the Rees algebra `Γ(X, U)[I(U)t]` by the power of `t`. -/
theorem reesAlgebraSectionsEquiv_mem_grade_iff {n : ℕ} {x : ⨁ n, Γ(I.reesAlgebra.obj.X n, U)} :
    I.reesAlgebraSectionsEquiv hU x ∈ reesAlgebra.grade (I.ideal ⟨U, hU⟩) n ↔
      x ∈ I.reesAlgebra.obj.gradedSectionsGrading U n := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨r, hr, hrx⟩ := reesAlgebra.mem_grade_iff.mp hx
    rw [← SetLike.mem_coe, ← range_reesSec I ⟨U, hU⟩] at hr
    obtain ⟨y, rfl⟩ := hr
    obtain rfl : DirectSum.of _ n y = x := (I.reesAlgebraSectionsEquiv hU).injective
      (Subtype.ext ((I.toPolynomial_of U n y).trans hrx))
    exact I.reesAlgebra.obj.of_mem_gradedSectionsGrading n y
  · obtain ⟨y, rfl⟩ := DirectSum.mem_summand.mp hx
    exact reesAlgebra.mem_grade_iff.mpr ⟨_, by
      rw [← SetLike.mem_coe, ← range_reesSec I ⟨U, hU⟩]; exact Set.mem_range_self y,
      (I.toPolynomial_of U n y).symm⟩

end Affine

end

end AlgebraicGeometry.Scheme.IdealSheafData
