/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence
public import TauCeti.AlgebraicGeometry.IdealSheaf.TensorProduct
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.Basic

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

## Main definitions

* `Scheme.IdealSheafData.reesMul I i j`: the multiplication `Iⁱ ⊗ Iʲ ⟶ Iⁱ⁺ʲ`.
* `Scheme.IdealSheafData.reesOne I`: the unit `𝒪_X ⟶ I⁰`.
* `Scheme.IdealSheafData.reesAlgebra I`: the Rees algebra `⨁ₙ Iⁿ`, as a graded quasi-coherent
  `𝒪_X`-algebra.

## Main results

* `Scheme.IdealSheafData.reesMul_sheafι` and `Scheme.IdealSheafData.reesOne_sheafι`: the
  multiplication and the unit are the restrictions of those of `𝒪_X`.
* `Scheme.IdealSheafData.reesAlgebra_obj_X`, `Scheme.IdealSheafData.mul_reesAlgebra` and
  `Scheme.IdealSheafData.one_reesAlgebra`: the homogeneous components, multiplication and unit of
  the Rees algebra.

## References

* [The Stacks Project, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF): the blowing up of a
  quasi-coherent sheaf of ideals is the relative `Proj` of `⨁ₙ Iⁿ`.
* R. Hartshorne, *Algebraic Geometry*, Section II.7, *Blowing up*.
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

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
def reesMul (i j : ℕ) : (I ^ i).sheaf ⊗ (I ^ j).sheaf ⟶ (I ^ (i + j)).sheaf :=
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
def reesOne : 𝟙_ X.Modules ⟶ (I ^ 0).sheaf :=
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
    (I.reesOne ▷ (I ^ n).sheaf) ≫ I.reesMul 0 n =
      (λ_ (I ^ n).sheaf).hom ≫ eqToHom (congrArg (fun k ↦ (I ^ k).sheaf) (zero_add n).symm) := by
  rw [← cancel_mono (I ^ (0 + n)).sheafιUnit]
  simp (disch := omega) only [Category.assoc, reesMul_sheafιUnit, eqToHom_pow_sheafιUnit,
    whiskerRight_comp_tensorHom_assoc, reesOne_sheafιUnit]
  monoidal

/-- The unit of the Rees algebra is a right identity for its multiplication. -/
private lemma whiskerLeft_reesOne_reesMul (n : ℕ) :
    ((I ^ n).sheaf ◁ I.reesOne) ≫ I.reesMul n 0 =
      (ρ_ (I ^ n).sheaf).hom ≫ eqToHom (congrArg (fun k ↦ (I ^ k).sheaf) (add_zero n).symm) := by
  rw [← cancel_mono (I ^ (n + 0)).sheafιUnit]
  simp (disch := omega) only [Category.assoc, reesMul_sheafιUnit, eqToHom_pow_sheafιUnit,
    whiskerLeft_comp_tensorHom_assoc, reesOne_sheafιUnit]
  monoidal

/-- The multiplication of the Rees algebra is associative. -/
private lemma reesMul_assoc (i j k : ℕ) :
    (I.reesMul i j ▷ (I ^ k).sheaf) ≫ I.reesMul (i + j) k =
      (α_ _ _ _).hom ≫ ((I ^ i).sheaf ◁ I.reesMul j k) ≫ I.reesMul i (j + k) ≫
        eqToHom (congrArg (fun k ↦ (I ^ k).sheaf) (add_assoc i j k).symm) := by
  rw [← cancel_mono (I ^ (i + j + k)).sheafιUnit]
  simp (disch := omega) only [Category.assoc, reesMul_sheafιUnit, eqToHom_pow_sheafιUnit,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  -- Both sides are `(Iⁱ ⊗ Iʲ) ⊗ Iᵏ ⟶ (𝒪_X ⊗ 𝒪_X) ⊗ 𝒪_X` followed by structural isomorphisms.
  monoidal

/-- The multiplication of the Rees algebra is commutative. -/
private lemma braiding_reesMul (i j : ℕ) :
    (β_ (I ^ i).sheaf (I ^ j).sheaf).hom ≫ I.reesMul j i =
      I.reesMul i j ≫ eqToHom (congrArg (fun k ↦ (I ^ k).sheaf) (add_comm i j)) := by
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
  GradedQuasicoherentAlgebra.ofHomogeneous (fun n ↦ (I ^ n).sheaf) I.reesOne I.reesMul
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

end

end AlgebraicGeometry.Scheme.IdealSheafData
