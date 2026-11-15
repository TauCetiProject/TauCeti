/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Extension.SquareZero.Basic
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Pullbacks of square-zero extensions and lifting obstructions

For an extension `E → B` with kernel `M` and an algebra map `T → B`, the fibre product
`E ×_B T → T` is a square-zero extension by `M`, with action restricted to `T`.
Its class is the obstruction to lifting `T → B` to `E`: it vanishes exactly when a lift exists.

The map `T → B` is represented by an algebra tower `A → T → B`; an arbitrary
`f : T →ₐ[A] B` supplies this structure via `f.toAlgebra`. The module action on `M` must
be the restricted action, expressed by `IsScalarTower T B M`.

`pullbackLift` and `pullback_hom_ext` give the fibre-product universal property.
`splittingPullbackEquiv` identifies splittings of the pullback with lifts of `T → B`.
Pullback respects morphisms of extensions, so its class depends only on the original class.
The fibre-product ring uses Mathlib's `AlgHom.equalizer` on the two maps from `E × T` to `B`.
No flatness or surjectivity hypothesis on `T → B` is required.

## References

* Stacks Project, Deformation Theory, Lemma 91.2.1, Tag 08S5, and Section 91.2, Tag 08S3.
-/

public section

noncomputable section

universe w u v t v' c

namespace TauCeti.SquareZeroExtension

open CategoryTheory

variable {A : Type u} {B : Type v} {M : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M]
  (E : SquareZeroExtension.{w} A B M)
  (T : Type v') [CommRing T] [Algebra A T] [Algebra T B] [IsScalarTower A T B]
  [Module T M] [IsScalarTower T B M]

/-- The pullback of `E → B` along `T → B`, with its restricted kernel action. -/
def pullback : SquareZeroExtension.{max w v'} A T M where
  Ring := AlgHom.equalizer (E.π.comp (AlgHom.fst A E.Ring T))
    ((IsScalarTower.toAlgHom A T B).comp (AlgHom.snd A E.Ring T))
  π := (AlgHom.snd A E.Ring T).comp (Subalgebra.val _)
  π_surjective a := by
    obtain ⟨x, hx⟩ := E.π_surjective (algebraMap T B a)
    exact ⟨⟨(x, a), hx⟩, rfl⟩
  ι :=
    { toFun m := ⟨(E.ι m, 0), by simp⟩
      map_zero' := Subtype.ext (Prod.ext (map_zero E.ι) rfl)
      map_add' m n := Subtype.ext (Prod.ext (map_add E.ι m n) (by simp)) }
  ι_injective := fun m n h ↦ E.ι_injective (congrArg (fun x ↦ x.val.1) h)
  exact x := by
    constructor
    · intro hx
      -- Inside the construction, use the equalizer and projection APIs directly;
      -- the pullback's own projection lemmas are only available after it is defined.
      have heq := (AlgHom.mem_equalizer _ _ _).mp x.property
      simp only [AlgHom.comp_apply, AlgHom.fst_apply, AlgHom.snd_apply,
        IsScalarTower.toAlgHom_apply] at heq
      simp only [AlgHom.comp_apply, Subalgebra.val_apply, AlgHom.snd_apply] at hx
      obtain ⟨m, hm⟩ := (E.exact x.val.1).mp (by rw [heq, hx, map_zero])
      exact ⟨m, Subtype.ext (Prod.ext hm hx.symm)⟩
    · rintro ⟨m, rfl⟩
      rfl
  mul_ι x m := by
    apply Subtype.ext
    have heq := (AlgHom.mem_equalizer _ _ _).mp x.property
    simp only [AlgHom.comp_apply, AlgHom.fst_apply, AlgHom.snd_apply,
      IsScalarTower.toAlgHom_apply] at heq
    exact Prod.ext ((E.mul_ι x.val.1 m).trans (by rw [heq, algebraMap_smul]; rfl)) (mul_zero _)

/-- The projection of the pullback to the original extension ring. -/
def pullbackFst : (E.pullback T).Ring →ₐ[A] E.Ring :=
  (AlgHom.fst A E.Ring T).comp (Subalgebra.val _)

/-- The defining commutative square of the pullback. -/
@[simp]
theorem π_pullbackFst (x : (E.pullback T).Ring) :
    E.π (E.pullbackFst T x) = algebraMap T B ((E.pullback T).π x) :=
  x.property

@[simp]
theorem pullbackFst_ι (m : M) :
    E.pullbackFst T ((E.pullback T).ι m) = E.ι m :=
  (rfl)

/-- Two elements of the pullback agree if their two projections agree. -/
@[ext]
theorem pullback_ext {x y : (E.pullback T).Ring}
    (h₁ : E.pullbackFst T x = E.pullbackFst T y)
    (h₂ : (E.pullback T).π x = (E.pullback T).π y) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- Two algebra maps to the pullback agree if their two projections agree. -/
@[ext]
theorem pullback_hom_ext {C : Type c} [CommRing C] [Algebra A C]
    {g h : C →ₐ[A] (E.pullback T).Ring}
    (h₁ : (E.pullbackFst T).comp g = (E.pullbackFst T).comp h)
    (h₂ : (E.pullback T).π.comp g = (E.pullback T).π.comp h) : g = h :=
  AlgHom.ext fun x ↦ E.pullback_ext T (AlgHom.congr_fun h₁ x) (AlgHom.congr_fun h₂ x)

/-- The algebra map into the pullback determined by a commuting pair of algebra maps. -/
def pullbackLift {C : Type c} [CommRing C] [Algebra A C]
    (g : C →ₐ[A] E.Ring) (h : C →ₐ[A] T)
    (comm : E.π.comp g = (IsScalarTower.toAlgHom A T B).comp h) :
    C →ₐ[A] (E.pullback T).Ring :=
  (g.prod h).codRestrict _ fun x ↦ AlgHom.congr_fun comm x

@[simp]
theorem pullbackFst_comp_pullbackLift {C : Type c} [CommRing C] [Algebra A C]
    (g : C →ₐ[A] E.Ring) (h : C →ₐ[A] T)
    (comm : E.π.comp g = (IsScalarTower.toAlgHom A T B).comp h) :
    (E.pullbackFst T).comp (E.pullbackLift T g h comm) = g :=
  (rfl)

@[simp]
theorem π_comp_pullbackLift {C : Type c} [CommRing C] [Algebra A C]
    (g : C →ₐ[A] E.Ring) (h : C →ₐ[A] T)
    (comm : E.π.comp g = (IsScalarTower.toAlgHom A T B).comp h) :
    (E.pullback T).π.comp (E.pullbackLift T g h comm) = h :=
  (rfl)

@[simp]
theorem pullbackFst_pullbackLift_apply {C : Type c} [CommRing C] [Algebra A C]
    (g : C →ₐ[A] E.Ring) (h : C →ₐ[A] T)
    (comm : E.π.comp g = (IsScalarTower.toAlgHom A T B).comp h) (x : C) :
    E.pullbackFst T (E.pullbackLift T g h comm x) = g x :=
  (rfl)

@[simp]
theorem π_pullbackLift_apply {C : Type c} [CommRing C] [Algebra A C]
    (g : C →ₐ[A] E.Ring) (h : C →ₐ[A] T)
    (comm : E.π.comp g = (IsScalarTower.toAlgHom A T B).comp h) (x : C) :
    (E.pullback T).π (E.pullbackLift T g h comm x) = h x :=
  (rfl)

/-- Splittings of the pullback are precisely lifts of `T → B` to the original extension ring. -/
def splittingPullbackEquiv :
    (E.pullback T).Splitting ≃
      {g : T →ₐ[A] E.Ring // E.π.comp g = IsScalarTower.toAlgHom A T B} where
  toFun s := ⟨(E.pullbackFst T).comp s.toAlgHom, by ext x; simp⟩
  invFun g :=
    { toAlgHom := E.pullbackLift T g.val (AlgHom.id A T) (by simpa using g.property)
      π_toAlgHom x := rfl }
  left_inv s := by
    apply Splitting.ext
    apply E.pullback_hom_ext T
    · simp
    · ext x
      exact (s.π_toAlgHom x).symm
  right_inv g := Subtype.ext (by simp)

@[simp]
theorem splittingPullbackEquiv_apply (s : (E.pullback T).Splitting) :
    (E.splittingPullbackEquiv T s).val = (E.pullbackFst T).comp s.toAlgHom :=
  (rfl)

@[simp]
theorem splittingPullbackEquiv_symm_apply
    (g : {g : T →ₐ[A] E.Ring // E.π.comp g = IsScalarTower.toAlgHom A T B}) :
    ((E.splittingPullbackEquiv T).symm g).toAlgHom =
      E.pullbackLift T g.val (AlgHom.id A T) (by simpa using g.property) :=
  (rfl)

variable {E}

/-- A splitting of the original extension induces a splitting after pullback. -/
def Splitting.pullback (s : E.Splitting) : (E.pullback T).Splitting :=
  (E.splittingPullbackEquiv T).symm
    ⟨s.toAlgHom.comp (IsScalarTower.toAlgHom A T B), by ext x; simp⟩

@[simp]
theorem Splitting.pullbackFst_comp_pullback_toAlgHom (s : E.Splitting) :
    (E.pullbackFst T).comp (s.pullback T).toAlgHom =
      s.toAlgHom.comp (IsScalarTower.toAlgHom A T B) :=
  (rfl)

@[simp]
theorem Splitting.pullbackFst_pullback_toAlgHom_apply (s : E.Splitting) (x : T) :
    E.pullbackFst T ((s.pullback T).toAlgHom x) = s.toAlgHom (algebraMap T B x) :=
  (rfl)

variable {F : SquareZeroExtension.{w} A B M}

/-- The morphism of pullbacks induced by a morphism of extensions. -/
def pullbackMap (g : E ⟶ F) : E.pullback T ⟶ F.pullback T where
  toAlgHom := F.pullbackLift T (g.toAlgHom.comp (E.pullbackFst T)) (E.pullback T).π
    (by ext x; simp)
  π_toAlgHom x := rfl
  toAlgHom_ι m := Subtype.ext (Prod.ext (g.toAlgHom_ι m) rfl)

@[simp]
theorem pullbackFst_comp_pullbackMap (g : E ⟶ F) :
    (F.pullbackFst T).comp (pullbackMap T g).toAlgHom = g.toAlgHom.comp (E.pullbackFst T) :=
  (rfl)

@[simp]
theorem pullbackFst_pullbackMap_apply (g : E ⟶ F) (x : (E.pullback T).Ring) :
    F.pullbackFst T ((pullbackMap T g).toAlgHom x) = g.toAlgHom (E.pullbackFst T x) :=
  (rfl)

@[simp]
theorem pullbackMap_id : pullbackMap T (𝟙 E) = 𝟙 (E.pullback T) := by
  apply Hom.toAlgHom_injective
  apply E.pullback_hom_ext T <;> ext x <;> simp

@[simp]
theorem pullbackMap_comp {G : SquareZeroExtension.{w} A B M} (g : E ⟶ F) (h : F ⟶ G) :
    pullbackMap T (g ≫ h) = pullbackMap T g ≫ pullbackMap T h := by
  apply Hom.toAlgHom_injective
  apply G.pullback_hom_ext T <;> ext x <;> simp

end TauCeti.SquareZeroExtension

namespace TauCeti

open CategoryTheory

variable {A : Type u} {B T : Type v} {M : Type t} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M] [CommRing T] [Algebra A T] [Algebra T B]
  [IsScalarTower A T B] [Module T M] [IsScalarTower T B M]

namespace SquareZeroExtension

/-- The obstruction to lifting `T → B` through `E → B`: the class of the pullback extension.
The source and quotient rings lie in the same universe so that the pullback has a class in
`Exal A T M`. -/
def morphismObstruction (E : SquareZeroExtension.{max v t} A B M) (T : Type v)
    [CommRing T] [Algebra A T] [Algebra T B] [IsScalarTower A T B]
    [Module T M] [IsScalarTower T B M] : Exal A T M :=
  (E.pullback T).extensionClass

variable (T)

/-- The obstruction is represented by the fibre-product extension. -/
theorem morphismObstruction_def (E : SquareZeroExtension.{max v t} A B M) :
    E.morphismObstruction T = (E.pullback T).extensionClass :=
  (rfl)

/-- The lifting obstruction is invariant under morphisms of extensions. -/
theorem morphismObstruction_eq_of_hom {E F : SquareZeroExtension.{max v t} A B M}
    (g : E ⟶ F) : E.morphismObstruction T = F.morphismObstruction T :=
  extensionClass_eq_extensionClass_iff.mpr ⟨pullbackMap T g⟩

variable [Module Tᵐᵒᵖ M] [IsCentralScalar T M] [Module A M] [IsScalarTower A T M]
  [IsScalarTower A Tᵐᵒᵖ M]

/-- The obstruction vanishes exactly when the algebra map `T → B` lifts through `E → B`. -/
theorem morphismObstruction_eq_zero_iff (E : SquareZeroExtension.{max v t} A B M) :
    E.morphismObstruction T = 0 ↔
      ∃ g : T →ₐ[A] E.Ring, E.π.comp g = IsScalarTower.toAlgHom A T B := by
  rw [morphismObstruction, extensionClass_eq_zero_iff]
  exact (E.splittingPullbackEquiv T).nonempty_congr.trans nonempty_subtype

end SquareZeroExtension

namespace Exal

variable (T)

/-- Pullback of extension classes along `T → B`. -/
def pullback : Exal A B M → Exal A T M :=
  lift (fun E ↦ E.morphismObstruction T) fun _ _ ⟨g⟩ ↦
    SquareZeroExtension.morphismObstruction_eq_of_hom T g

@[simp]
theorem pullback_extensionClass (E : SquareZeroExtension.{max v t} A B M) :
    pullback T E.extensionClass = E.morphismObstruction T := by
  rw [pullback, lift_extensionClass]

variable {T}

/-- Pullback along the identity leaves the extension class unchanged. -/
@[simp]
theorem pullback_self (x : Exal A B M) : pullback B x = x := by
  induction x using Exal.ind with
  | h E =>
    rw [pullback_extensionClass, SquareZeroExtension.morphismObstruction]
    apply SquareZeroExtension.extensionClass_eq_extensionClass_iff.mpr
    exact ⟨{
      toAlgHom := E.pullbackFst B
      π_toAlgHom x := by simp
      toAlgHom_ι m := by simp }⟩

/-- Successive pullbacks agree with pullback along the composite algebra map. -/
@[simp]
theorem pullback_pullback (U : Type v) [CommRing U] [Algebra A U] [Algebra U T]
    [Algebra U B] [IsScalarTower A U T] [IsScalarTower A U B] [IsScalarTower U T B]
    [Module U M] [IsScalarTower U T M] [IsScalarTower U B M] (x : Exal A B M) :
    pullback U (pullback T x) = pullback U x := by
  induction x using Exal.ind with
  | h E =>
    simp only [pullback_extensionClass, SquareZeroExtension.morphismObstruction]
    apply SquareZeroExtension.extensionClass_eq_extensionClass_iff.mpr
    let g := (E.pullback T).pullbackFst U
    exact ⟨{
      toAlgHom := E.pullbackLift U ((E.pullbackFst T).comp g) ((E.pullback T).pullback U).π
        (by ext y; simp [g, ← IsScalarTower.algebraMap_apply U T B])
      π_toAlgHom y := rfl
      toAlgHom_ι m := by
        apply E.pullback_ext U <;> simp [g] }⟩

/-- Pullback preserves the split class. -/
@[simp]
theorem pullback_zero [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module Tᵐᵒᵖ M] [IsCentralScalar T M] [Module A M] [IsScalarTower A B M]
    [IsScalarTower A Bᵐᵒᵖ M] [IsScalarTower A T M] [IsScalarTower A Tᵐᵒᵖ M] :
    pullback T (0 : Exal A B M) = 0 := by
  rw [← SquareZeroExtension.extensionClass_squareZero A B M, pullback_extensionClass,
    SquareZeroExtension.morphismObstruction, SquareZeroExtension.extensionClass_eq_zero_iff]
  exact ⟨(SquareZeroExtension.squareZeroSplitting A B M).pullback T⟩

end Exal

end TauCeti
