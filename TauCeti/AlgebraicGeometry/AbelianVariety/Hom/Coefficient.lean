/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.End.BaseChange
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Coefficient homomorphisms of abelian varieties

For a commutative ring `R`, `CoefficientHom R A B` is the tensor product over `ℤ` of `R`
with the additive group of homomorphisms of abelian varieties. Composition extends the native
composition by bilinearity. In particular `CoefficientHom ℚ A B` is the rational Hom space,
and every rational homomorphism admits an integral numerator with one nonzero denominator.

On endomorphisms, this composition agrees with multiplication in the tensor product algebra,
in the convention that the right-hand factor acts first. See Kisin, Madapusi Pera and Shin,
[*Honda–Tate theory for Shimura varieties*, §2.1.3](https://math.berkeley.edu/~swshin/HT.pdf)
for the use of the units of the rational endomorphism algebra.

The `R`-linear category `WithCoefficients R K` uses these Hom spaces, so invertible
coefficient homomorphisms are isomorphisms in the usual categorical sense.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u v

variable {K : Type u} [Field K]

open scoped Hom nonZeroDivisors

/-- Homomorphisms of abelian varieties with coefficients in `R`. The homomorphism group is
reindexed additively before tensoring, since the native pointwise group law is multiplicative. -/
abbrev CoefficientHom (R : Type v) [CommRing R] (A B : AbelianVariety K) :=
  R ⊗[ℤ] Additive (A ⟶ B)

/-- The rational endomorphism algebra of an abelian variety. -/
abbrev End0 (A : AbelianVariety K) := ℚ ⊗[ℤ] End A

namespace CoefficientHom

variable {R : Type v} [CommRing R]
variable {A B C D : AbelianVariety K}

noncomputable section

/-- Regard a native homomorphism as a homomorphism with coefficients via `f ↦ 1 ⊗ f`. -/
def ofHom (R : Type v) [CommRing R] (f : A ⟶ B) : CoefficientHom R A B :=
  1 ⊗ₜ[ℤ] Additive.ofMul f

/-- The coefficient homomorphism associated to an integral homomorphism is its tensor with one. -/
lemma ofHom_def (f : A ⟶ B) :
    ofHom R f = 1 ⊗ₜ[ℤ] Additive.ofMul f := (rfl)

/-- The identity for composition of coefficient homomorphisms. -/
def id (R : Type v) [CommRing R] (A : AbelianVariety K) : CoefficientHom R A A :=
  ofHom R (𝟙 A)

/-- The coefficient identity is induced by the identity of the abelian variety. -/
@[simp] lemma ofHom_id (A : AbelianVariety K) :
    ofHom R (𝟙 A) = id R A := (rfl)

/-- The pointwise identity in the integral homomorphism group maps to zero. -/
@[simp] lemma ofHom_one : ofHom R (1 : A ⟶ B) = 0 := by
  rw [ofHom_def, ofMul_one, tmul_zero]

/-- The pointwise group law on native homomorphisms becomes addition. -/
@[simp] lemma ofHom_mul (f g : A ⟶ B) : ofHom R (f * g) = ofHom R f + ofHom R g := by
  simp only [ofHom_def, ofMul_mul, tmul_add]

/-- The multiplication-by-integer map corresponds to that integer times the coefficient
identity. -/
@[simp] lemma ofHom_mulBy (A : AbelianVariety K) (n : ℤ) :
    ofHom R (mulBy A n) = n • id R A := by
  rw [mulBy_eq_zpow, ofHom_def, ofMul_zpow, tmul_smul, id, ofHom_def]

/-- Multiplying the image of an integral homomorphism by a coefficient gives the corresponding
pure tensor. -/
lemma smul_ofHom (r : R) (f : A ⟶ B) : r • ofHom R f = r ⊗ₜ[ℤ] Additive.ofMul f := by
  rw [ofHom_def, smul_tmul', smul_eq_mul, mul_one]

private def integralComp :
    Additive (A ⟶ B) →ₗ[ℤ] Additive (B ⟶ C) →ₗ[ℤ] Additive (A ⟶ C) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => (MonoidHom.toAdditive (Hom.leftComp C f.toMul)).toIntLinearMap
      map_zero' := LinearMap.ext fun g => by
        simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive, Function.comp_apply,
          toMul_zero, Hom.leftComp_apply, Hom.one_comp, ofMul_one, LinearMap.zero_apply]
      map_add' f g := LinearMap.ext fun h => by
        simp only [LinearMap.add_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
          Function.comp_apply, toMul_add, Hom.leftComp_apply, Hom.mul_comp, ofMul_mul] }

/-- Compose coefficient homomorphisms in categorical order, extending the native composition
linearly in both arguments. -/
def comp : CoefficientHom R A B →ₗ[R] CoefficientHom R B C →ₗ[R] CoefficientHom R A C :=
  TensorProduct.curry <|
    (TensorProduct.lift integralComp).baseChange R ∘ₗ
      (AlgebraTensorModule.distribBaseChange ℤ R
        (Additive (A ⟶ B)) (Additive (B ⟶ C))).symm.toLinearMap

/-- Composition on pure tensors multiplies the coefficients and composes the homomorphisms. -/
@[simp] lemma comp_tmul (r s : R) (f : A ⟶ B) (g : B ⟶ C) :
    comp (r ⊗ₜ[ℤ] Additive.ofMul f) (s ⊗ₜ[ℤ] Additive.ofMul g) =
      (r * s) ⊗ₜ[ℤ] Additive.ofMul (f ≫ g) := by
  simp only [comp, TensorProduct.curry_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.distribBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    TensorProduct.lift.tmul, integralComp, AddMonoidHom.coe_toIntLinearMap,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, MonoidHom.coe_toAdditive, Function.comp_apply,
    toMul_ofMul, Hom.leftComp_apply]

/-- The coefficient inclusion preserves native composition. -/
@[simp] lemma comp_ofHom (f : A ⟶ B) (g : B ⟶ C) :
    comp (ofHom R f) (ofHom R g) = ofHom R (f ≫ g) := by
  simp [ofHom_def]

/-- The coefficient identity is a left identity for composition. -/
@[simp] lemma id_comp (f : CoefficientHom R A B) : comp (id R A) f = f := by
  have h : comp (id R A) = (LinearMap.id : CoefficientHom R A B →ₗ[R] _) := by
    apply AlgebraTensorModule.ext
    intro r g
    simpa [id, ofHom_def] using comp_tmul (1 : R) r (𝟙 A) g.toMul
  exact LinearMap.congr_fun h f

/-- The coefficient identity is a right identity for composition. -/
@[simp] lemma comp_id (f : CoefficientHom R A B) : comp f (id R B) = f := by
  have h : (comp (R := R) (A := A) (B := B)).flip (id R B) =
      (LinearMap.id : CoefficientHom R A B →ₗ[R] _) := by
    apply AlgebraTensorModule.ext
    intro r g
    simpa [id, ofHom_def] using comp_tmul r (1 : R) g.toMul (𝟙 B)
  exact LinearMap.congr_fun h f

/-- Composition of coefficient homomorphisms is associative. -/
lemma comp_assoc (f : CoefficientHom R A B) (g : CoefficientHom R B C)
    (h : CoefficientHom R C D) :
    comp (comp f g) h = comp f (comp g h) := by
  induction f using TensorProduct.inductionOn with
  | tmul r f =>
    induction g using TensorProduct.inductionOn with
    | tmul s g =>
      induction h using TensorProduct.inductionOn with
      | tmul t h =>
        obtain ⟨f, rfl⟩ := Additive.ofMul.surjective f
        obtain ⟨g, rfl⟩ := Additive.ofMul.surjective g
        obtain ⟨h, rfl⟩ := Additive.ofMul.surjective h
        simp [mul_assoc, Category.assoc]
      | add h h' hh hh' => simp [hh, hh']
    | add g g' hg hg' => simp [hg, hg']
  | add f f' hf hf' => simp [hf, hf']

/-- Self-homomorphisms with coefficients identify with the scalar extension of the native
endomorphism ring. -/
def endEquiv (R : Type v) [CommRing R] (A : AbelianVariety K) :
    CoefficientHom R A A ≃ₗ[R] R ⊗[ℤ] End A :=
  AlgebraTensorModule.congr (.refl R R)
    ({ toFun := fun f => End.ofHom f.toMul
       invFun := fun x => Additive.ofMul x.toHom
       left_inv := fun f => by simp
       right_inv := fun x => by simp
       map_add' := fun f g => End.toHom_injective (by simp) } :
      Additive (A ⟶ A) ≃+ End A).toIntLinearEquiv

/-- The endomorphism comparison maps a pure tensor by its native endomorphism. -/
@[simp] lemma endEquiv_tmul (r : R) (f : A ⟶ A) :
    endEquiv R A (r ⊗ₜ[ℤ] Additive.ofMul f) = r ⊗ₜ[ℤ] End.ofHom f := by
  simp only [endEquiv, AlgebraTensorModule.congr_tmul]
  rfl

/-- The self-Hom comparison sends an integral endomorphism to its canonical scalar extension. -/
@[simp] lemma endEquiv_ofHom (f : A ⟶ A) :
    endEquiv R A (ofHom R f) =
      (Algebra.TensorProduct.includeRight : End A →ₐ[ℤ] R ⊗[ℤ] End A) (End.ofHom f) := by
  rw [ofHom_def, endEquiv_tmul, Algebra.TensorProduct.includeRight_apply]

/-- The coefficient identity corresponds to the unit of the endomorphism algebra. -/
@[simp] lemma endEquiv_id (A : AbelianVariety K) :
    endEquiv R A (id R A) = 1 := by
  rw [id, ofHom_def, endEquiv_tmul, ← End.toHom_one, End.ofHom_toHom]
  rfl

/-- The coefficient composition corresponds to multiplication in the endomorphism algebra,
with the second morphism multiplying on the left. -/
@[simp] lemma endEquiv_comp (f g : CoefficientHom R A A) :
    endEquiv R A (comp f g) = endEquiv R A g * endEquiv R A f := by
  let : Semiring (R ⊗[ℤ] End A) := inferInstance
  induction f using TensorProduct.inductionOn with
  | tmul r f =>
    induction g using TensorProduct.inductionOn with
    | tmul s g =>
      obtain ⟨f, rfl⟩ := Additive.ofMul.surjective f
      obtain ⟨g, rfl⟩ := Additive.ofMul.surjective g
      simp [Algebra.TensorProduct.tmul_mul_tmul, End.ofHom_comp, mul_comm r s]
    | add g g' hg hg' =>
      simp only [map_add, hg, hg', add_mul]
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, hf, hf', mul_add]

section Extend

variable {S : Type*} [CommRing S]

/-- Extend the coefficient ring along a ring homomorphism. The abelian varieties stay over
the same field. -/
def extend (φ : R →+* S) : CoefficientHom R A B →ₛₗ[φ] CoefficientHom S A B :=
  { TensorProduct.map φ.toIntAlgHom.toLinearMap (LinearMap.id :
      Additive (A ⟶ B) →ₗ[ℤ] Additive (A ⟶ B)) with
    map_smul' := fun r f => by
      induction f using TensorProduct.inductionOn with
      | tmul s f =>
        simp [smul_tmul', smul_eq_mul]
      | add f g hf hg =>
        simp only [LinearMap.toFun_eq_coe] at hf hg
        simp only [LinearMap.toFun_eq_coe, smul_add, map_add, hf, hg] }

/-- Extension of coefficients sends the scalar of a pure tensor through the ring map. -/
@[simp] lemma extend_tmul (φ : R →+* S) (r : R) (f : A ⟶ B) :
    extend φ (r ⊗ₜ[ℤ] Additive.ofMul f) = φ r ⊗ₜ[ℤ] Additive.ofMul f :=
  TensorProduct.map_tmul ..

/-- Extension of coefficients commutes with inclusion of native homomorphisms. -/
@[simp] lemma extend_ofHom (φ : R →+* S) (f : A ⟶ B) :
    extend φ (ofHom R f) = ofHom S f := by
  simp [ofHom_def]

/-- Extension of coefficients preserves identities. -/
@[simp] lemma extend_id (φ : R →+* S) (A : AbelianVariety K) :
    extend φ (id R A) = id S A :=
  extend_ofHom φ (𝟙 A)

/-- Extension of coefficients preserves composition. -/
@[simp] lemma extend_comp (φ : R →+* S) (f : CoefficientHom R A B) (g : CoefficientHom R B C) :
    extend φ (comp f g) = comp (extend φ f) (extend φ g) := by
  induction f using TensorProduct.inductionOn with
  | tmul r f =>
    induction g using TensorProduct.inductionOn with
    | tmul s g =>
      obtain ⟨f, rfl⟩ := Additive.ofMul.surjective f
      obtain ⟨g, rfl⟩ := Additive.ofMul.surjective g
      simp
    | add g g' hg hg' => simp [hg, hg']
  | add f f' hf hf' => simp [hf, hf']

end Extend

section FieldBaseChange

variable (L : Type u) [Field L] [Algebra K L]

/-- Base change of the ground field on coefficient homomorphisms. This is `R`-linear and is
induced by base change on the integral homomorphism groups. -/
def baseChange : CoefficientHom R A B →ₗ[R] CoefficientHom R (A.baseChange L) (B.baseChange L) :=
  (MonoidHom.toAdditive (Hom.baseChangeMonoidHom A B L)).toIntLinearMap.baseChange R

/-- Base change of the field applies to the integral homomorphism in a pure tensor. -/
@[simp] lemma baseChange_tmul (r : R) (f : A ⟶ B) :
    baseChange L (r ⊗ₜ[ℤ] Additive.ofMul f) = r ⊗ₜ[ℤ] Additive.ofMul (Hom.baseChange f L) := by
  simp only [baseChange, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
    MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul, Hom.baseChangeMonoidHom_apply]

/-- Base change commutes with inclusion of native homomorphisms. -/
@[simp] lemma baseChange_ofHom (f : A ⟶ B) :
    baseChange L (ofHom R f) = ofHom R (Hom.baseChange f L) := by
  simp [ofHom_def]

/-- Base change of the field preserves the coefficient identity. -/
@[simp] lemma baseChange_id (A : AbelianVariety K) :
    baseChange L (id R A) = id R (A.baseChange L) := by
  simpa only [Hom.baseChange_id, ofHom_id] using
    baseChange_ofHom (R := R) L (𝟙 A)

/-- Base change of the field preserves composition of coefficient homomorphisms. -/
@[simp] lemma baseChange_comp (f : CoefficientHom R A B) (g : CoefficientHom R B C) :
    baseChange L (comp f g) = comp (baseChange L f) (baseChange L g) := by
  induction f using TensorProduct.inductionOn with
  | tmul r f =>
    induction g using TensorProduct.inductionOn with
    | tmul s g =>
      obtain ⟨f, rfl⟩ := Additive.ofMul.surjective f
      obtain ⟨g, rfl⟩ := Additive.ofMul.surjective g
      simp
    | add g g' hg hg' => simp [hg, hg']
  | add f f' hf hf' => simp [hf, hf']

/-- The coefficient Hom base-change map on self-homomorphisms agrees with the extension of
the native endomorphism-ring map. -/
@[simp] lemma endEquiv_baseChange (f : CoefficientHom R A A) :
    endEquiv R (A.baseChange L) (baseChange L f) =
      Algebra.TensorProduct.map (AlgHom.id R R) (End.baseChange A L).toIntAlgHom
        (endEquiv R A f) := by
  induction f using TensorProduct.inductionOn with
  | tmul r f =>
    obtain ⟨f, rfl⟩ := Additive.ofMul.surjective f
    simp
  | add f g hf hg => simp [hf, hg]

end FieldBaseChange

/-- Coefficient homomorphisms for a rational algebra are obtained equally by extending the
rational Hom space. -/
def ratTensorEquiv (R : Type v) [CommRing R] [Algebra ℚ R] (A B : AbelianVariety K) :
    (R ⊗[ℚ] CoefficientHom ℚ A B) ≃ₗ[R] CoefficientHom R A B :=
  AlgebraTensorModule.cancelBaseChange ℤ ℚ R R (Additive (A ⟶ B))

/-- The comparison of coefficient Hom spaces multiplies the two scalar factors. -/
@[simp] lemma ratTensorEquiv_tmul [Algebra ℚ R] (r : R) (q : ℚ) (f : A ⟶ B) :
    ratTensorEquiv R A B (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] Additive.ofMul f)) =
      (q • r) ⊗ₜ[ℤ] Additive.ofMul f :=
  AlgebraTensorModule.cancelBaseChange_tmul ..

/-- Every rational homomorphism has a single nonzero integer denominator. -/
theorem exists_zsmul_eq_ofHom (f : CoefficientHom ℚ A B) :
    ∃ (n : ℤ) (g : A ⟶ B), n ≠ 0 ∧ n • f = ofHom ℚ g := by
  obtain ⟨⟨g, n⟩, h⟩ := IsLocalizedModule.surj ℤ⁰
    (TensorProduct.mk ℤ ℚ (Additive (A ⟶ B)) 1) f
  exact ⟨n, g.toMul, nonZeroDivisors.ne_zero n.property, h⟩

end

end CoefficientHom

/-- Abelian varieties over `K` with homomorphisms taken with coefficients in `R`. -/
@[ext]
structure WithCoefficients (R : Type v) [CommRing R] (K : Type u) [Field K] where
  /-- The underlying abelian variety over `K`. -/
  toAbelianVariety : AbelianVariety K

namespace WithCoefficients

variable {R : Type v} [CommRing R]

noncomputable section

instance : Category (WithCoefficients R K) where
  Hom A B := CoefficientHom R A.toAbelianVariety B.toAbelianVariety
  id A := CoefficientHom.id R A.toAbelianVariety
  comp f g := CoefficientHom.comp f g
  id_comp := CoefficientHom.id_comp
  comp_id := CoefficientHom.comp_id
  assoc f g h := CoefficientHom.comp_assoc f g h

instance : Preadditive (WithCoefficients R K) where
  homGroup A B := inferInstanceAs
    (AddCommGroup (CoefficientHom R A.toAbelianVariety B.toAbelianVariety))
  add_comp A B C f g h := by
    let c := CoefficientHom.comp (R := R) (A := A.toAbelianVariety)
      (B := B.toAbelianVariety) (C := C.toAbelianVariety)
    exact (c.flip h).map_add f g
  comp_add A B C f g h := by
    let c := CoefficientHom.comp (R := R) (A := A.toAbelianVariety)
      (B := B.toAbelianVariety) (C := C.toAbelianVariety)
    exact (c f).map_add g h

instance : Linear R (WithCoefficients R K) where
  homModule A B := inferInstanceAs
    (Module R (CoefficientHom R A.toAbelianVariety B.toAbelianVariety))
  smul_comp A B C r f g := by
    let c := CoefficientHom.comp (R := R) (A := A.toAbelianVariety)
      (B := B.toAbelianVariety) (C := C.toAbelianVariety)
    exact (c.flip g).map_smul r f
  comp_smul A B C f r g := by
    let c := CoefficientHom.comp (R := R) (A := A.toAbelianVariety)
      (B := B.toAbelianVariety) (C := C.toAbelianVariety)
    exact (c f).map_smul r g

/-- The hom-set of the coefficient category is the coefficient Hom space, with its
coefficient-module structure. -/
def homLinearEquiv (A B : WithCoefficients R K) :
    (A ⟶ B) ≃ₗ[R] CoefficientHom R A.toAbelianVariety B.toAbelianVariety :=
  LinearEquiv.refl R _

/-- The identity in the coefficient category corresponds to the coefficient identity. -/
@[simp] lemma homLinearEquiv_id (A : WithCoefficients R K) :
    homLinearEquiv A A (𝟙 A) = CoefficientHom.id R A.toAbelianVariety := (rfl)

/-- Composition in the coefficient category is bilinear extension of native composition. -/
@[simp] lemma homLinearEquiv_comp {A B C : WithCoefficients R K} (f : A ⟶ B) (g : B ⟶ C) :
    homLinearEquiv A C (f ≫ g) =
      CoefficientHom.comp (homLinearEquiv A B f) (homLinearEquiv B C g) := (rfl)

/-- The endomorphism algebra in the coefficient category is the scalar extension of the
native endomorphism ring. -/
def endAlgEquiv (A : WithCoefficients R K) :
    CategoryTheory.End A ≃ₐ[R] R ⊗[ℤ] End A.toAbelianVariety :=
  AlgEquiv.ofLinearEquiv
    ((CategoryTheory.End.linearEquiv.trans (homLinearEquiv A A)).trans
      (CoefficientHom.endEquiv R A.toAbelianVariety))
    (by exact CoefficientHom.endEquiv_id A.toAbelianVariety)
    (fun f g => by exact CoefficientHom.endEquiv_comp g.asHom f.asHom)

/-- The endomorphism algebra comparison acts on a categorical endomorphism by viewing it
as a coefficient homomorphism. -/
@[simp] lemma endAlgEquiv_apply (A : WithCoefficients R K) (f : CategoryTheory.End A) :
    endAlgEquiv A f = CoefficientHom.endEquiv R A.toAbelianVariety
      (homLinearEquiv A A f.asHom) := (rfl)

/-- A ring homomorphism extends coefficients functorially. -/
def extendFunctor {S : Type*} [CommRing S] (φ : R →+* S) :
    WithCoefficients R K ⥤ WithCoefficients S K where
  obj A := ⟨A.toAbelianVariety⟩
  map f := CoefficientHom.extend φ f
  map_id A := CoefficientHom.extend_id φ A.toAbelianVariety
  map_comp f g := CoefficientHom.extend_comp φ f g

/-- Extending the coefficient ring keeps the same underlying abelian variety. -/
@[simp] lemma extendFunctor_obj {S : Type*} [CommRing S] (φ : R →+* S)
    (A : WithCoefficients R K) : (extendFunctor φ).obj A = ⟨A.toAbelianVariety⟩ := (rfl)

/-- On Hom spaces the change-of-coefficients functor applies the ring map to the coefficients. -/
@[simp] lemma extendFunctor_map {S : Type*} [CommRing S] (φ : R →+* S)
    {A B : WithCoefficients R K} (f : A ⟶ B) : (extendFunctor φ).map f =
      eqToHom (extendFunctor_obj φ A) ≫
        (homLinearEquiv _ _).symm (CoefficientHom.extend φ (homLinearEquiv A B f)) ≫
        eqToHom (extendFunctor_obj φ B).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Extension of the ground field defines a functor on abelian varieties with coefficient
homomorphisms. -/
def baseChangeFunctor (L : Type u) [Field L] [Algebra K L] :
    WithCoefficients R K ⥤ WithCoefficients R L where
  obj A := ⟨A.toAbelianVariety.baseChange L⟩
  map f := CoefficientHom.baseChange L f
  map_id A := CoefficientHom.baseChange_id L A.toAbelianVariety
  map_comp f g := CoefficientHom.baseChange_comp L f g

/-- The ground-field extension sends each object to the base change of its abelian variety. -/
@[simp] lemma baseChangeFunctor_obj (L : Type u) [Field L] [Algebra K L]
    (A : WithCoefficients R K) : (baseChangeFunctor L).obj A =
      ⟨A.toAbelianVariety.baseChange L⟩ := (rfl)

/-- On Hom spaces the field-extension functor acts by base change of the field. -/
@[simp] lemma baseChangeFunctor_map (L : Type u) [Field L] [Algebra K L]
    {A B : WithCoefficients R K} (f : A ⟶ B) : (baseChangeFunctor L).map f =
      eqToHom (baseChangeFunctor_obj L A) ≫
        (homLinearEquiv _ _).symm (CoefficientHom.baseChange L (homLinearEquiv A B f)) ≫
        eqToHom (baseChangeFunctor_obj L B).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

end

end WithCoefficients

/-- The functor from native abelian varieties to abelian varieties with coefficient
homomorphisms sends each integral map to its tensor with one. -/
noncomputable def coefficientFunctor (R : Type v) [CommRing R] :
    AbelianVariety K ⥤ WithCoefficients R K where
  obj A := ⟨A⟩
  map f := CoefficientHom.ofHom R f
  map_id := CoefficientHom.ofHom_id
  map_comp f g := (CoefficientHom.comp_ofHom f g).symm

/-- The coefficient functor leaves the underlying abelian variety unchanged. -/
@[simp] lemma coefficientFunctor_obj (R : Type v) [CommRing R] (A : AbelianVariety K) :
    (coefficientFunctor R).obj A = ⟨A⟩ := (rfl)

/-- The coefficient functor sends a native morphism to its tensor with one. -/
@[simp] lemma coefficientFunctor_map (R : Type v) [CommRing R]
    {A B : AbelianVariety K} (f : A ⟶ B) : (coefficientFunctor R).map f =
      eqToHom (coefficientFunctor_obj R A) ≫
        (WithCoefficients.homLinearEquiv _ _).symm (CoefficientHom.ofHom R f) ≫
        eqToHom (coefficientFunctor_obj R B).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

end TauCeti.AlgebraicGeometry.AbelianVariety
