/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Square-zero extensions of algebras and their isomorphism classes

Let `A → B` be a map of commutative rings and `M` a `B`-module. A square-zero extension of `B`
by `M` over `A` is a surjective `A`-algebra map `π : E → B` together with an injective additive
map `ι : M → E` onto the kernel of `π`, such that `x * ι m = ι (π x • m)` for all `x ∈ E` and
`m ∈ M`. The kernel of `π` is then an ideal of square zero, and its `B`-module structure is the
given one on `M`. These extensions are the objects classified in degree one by the cotangent
complex, and the set `Exal_A(B, M)` of their isomorphism classes is the target of the
deformation-theoretic obstruction classes.

Morphisms of extensions are `A`-algebra maps compatible with the projections and the kernel
identifications. By the five lemma every such morphism is bijective, so square-zero extensions of
`B` by `M` form a groupoid; `Exal` is its set of isomorphism classes. The trivial extension
`TrivSqZeroExt B M`, with multiplication `(b, m) (b', m') = (b b', b m' + b' m)`, gives the zero
class, and an extension has the zero class exactly when its projection admits an `A`-algebra
section. Every extension of `A` itself splits, while `ℤ/4 → ℤ/2` does not.

## Main definitions

* `TauCeti.SquareZeroExtension A B M`: square-zero extensions of `B` by `M` over `A`.
* `TauCeti.SquareZeroExtension.Hom`: morphisms of extensions, and the groupoid structure.
* `TauCeti.SquareZeroExtension.Splitting`: `A`-algebra sections of the projection.
* `TauCeti.SquareZeroExtension.squareZero`: the trivial extension `TrivSqZeroExt B M`.
* `TauCeti.Exal A B M`: isomorphism classes of square-zero extensions, with `0` the class of
  the trivial extension.

## Main results

* `TauCeti.SquareZeroExtension.sq_ker_π`: the kernel of the projection has square zero.
* `TauCeti.SquareZeroExtension.Hom.bijective`: morphisms of extensions are bijective.
* `TauCeti.SquareZeroExtension.extensionClass_eq_zero_iff`: an extension has the zero class if
  and only if it splits.
* `TauCeti.Exal.subsingleton_self`: `Exal_A(A, M)` is zero.
* `TauCeti.SquareZeroExtension.zmodFour_extensionClass_ne_zero`: the extension `ℤ/4 → ℤ/2` has
  a nonzero class.

## References

* [Stacks Project, Deformation Theory, Section 2, Tag 08S3](https://stacks.math.columbia.edu/tag/08S3):
  square-zero extensions of algebras, their morphisms and `Exal_A(B, M)`.
-/

public section

universe w u v t

namespace TauCeti

open CategoryTheory TrivSqZeroExt

variable (A : Type u) (B : Type v) (M : Type t) [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M]

/-- A square-zero extension of the `A`-algebra `B` by the `B`-module `M`: a surjective
`A`-algebra map `π : E → B` and an injective additive map `ι : M → E` onto the kernel of `π`,
through which `E` acts on `M` by `x * ι m = ι (π x • m)`. In particular the kernel of `π` has
square zero (`TauCeti.SquareZeroExtension.sq_ker_π`). -/
structure SquareZeroExtension where
  /-- The ring `E` of the extension. -/
  Ring : Type w
  [commRing : CommRing Ring]
  [algebra : Algebra A Ring]
  /-- The projection `E → B`. -/
  π : Ring →ₐ[A] B
  π_surjective : Function.Surjective π
  /-- The identification of `M` with the kernel of the projection. -/
  ι : M →+ Ring
  ι_injective : Function.Injective ι
  exact : Function.Exact ι π
  mul_ι (x : Ring) (m : M) : x * ι m = ι (π x • m)

namespace SquareZeroExtension

attribute [instance] commRing algebra

attribute [simp] mul_ι

variable {A B M}
variable (E : SquareZeroExtension.{w} A B M)

@[simp]
theorem π_ι (m : M) : E.π (E.ι m) = 0 :=
  E.exact.apply_apply_eq_zero m

@[simp]
theorem ι_mul (m : M) (x : E.Ring) : E.ι m * x = E.ι (E.π x • m) := by
  rw [mul_comm, mul_ι]

theorem ι_mul_ι (m n : M) : E.ι m * E.ι n = 0 := by
  simp

@[simp]
theorem ι_eq_zero_iff (m : M) : E.ι m = 0 ↔ m = 0 :=
  map_eq_zero_iff E.ι E.ι_injective

/-- Scalars of `A` act on the kernel through `B`. -/
theorem ι_algebraMap_smul (a : A) (m : M) : E.ι (algebraMap A B a • m) = a • E.ι m := by
  rw [Algebra.smul_def, mul_ι, AlgHom.commutes]

/-- The kernel of the projection of a square-zero extension is an ideal of square zero. -/
theorem sq_ker_π : RingHom.ker E.π ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨m, rfl⟩ := (E.exact x).1 hx
  obtain ⟨n, rfl⟩ := (E.exact y).1 hy
  simp

/-- A morphism of square-zero extensions of `B` by `M`: an `A`-algebra map compatible with the
projections to `B` and the inclusions of `M`. Every morphism is bijective
(`TauCeti.SquareZeroExtension.Hom.bijective`). -/
structure Hom (E F : SquareZeroExtension.{w} A B M) where
  /-- The underlying `A`-algebra map. -/
  toAlgHom : E.Ring →ₐ[A] F.Ring
  π_toAlgHom (x : E.Ring) : F.π (toAlgHom x) = E.π x
  toAlgHom_ι (m : M) : toAlgHom (E.ι m) = F.ι m

attribute [simp] Hom.π_toAlgHom Hom.toAlgHom_ι

namespace Hom

variable {E} {F : SquareZeroExtension.{w} A B M}

theorem toAlgHom_injective : Function.Injective (toAlgHom : Hom E F → E.Ring →ₐ[A] F.Ring) := by
  rintro ⟨f, _, _⟩ ⟨g, _, _⟩ rfl
  rfl

/-- The five lemma for square-zero extensions: a morphism of extensions of `B` by `M` is
bijective. -/
theorem bijective (f : Hom E F) : Function.Bijective f.toAlgHom := by
  refine ⟨(injective_iff_map_eq_zero f.toAlgHom).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨m, rfl⟩ := (E.exact x).1 (by rw [← f.π_toAlgHom, hx, map_zero])
    rw [f.toAlgHom_ι, F.ι_eq_zero_iff] at hx
    simp [hx]
  · obtain ⟨x, hx⟩ := E.π_surjective (F.π y)
    obtain ⟨m, hm⟩ := (F.exact (y - f.toAlgHom x)).1 (by simp [hx])
    exact ⟨x + E.ι m, by simp [hm]⟩

/-- The `A`-algebra isomorphism underlying a morphism of square-zero extensions. -/
noncomputable def toAlgEquiv (f : Hom E F) : E.Ring ≃ₐ[A] F.Ring :=
  AlgEquiv.ofBijective f.toAlgHom f.bijective

@[simp]
theorem toAlgEquiv_apply (f : Hom E F) (x : E.Ring) : f.toAlgEquiv x = f.toAlgHom x :=
  (rfl)

end Hom

/-- The groupoid of square-zero extensions of `B` by `M`: every morphism of extensions is an
isomorphism by `TauCeti.SquareZeroExtension.Hom.bijective`. -/
noncomputable instance extensionCategory : Groupoid (SquareZeroExtension.{w} A B M) where
  Hom := Hom
  id E := ⟨AlgHom.id A E.Ring, fun _ ↦ rfl, fun _ ↦ rfl⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom, by simp, by simp⟩
  inv f :=
    { toAlgHom := f.toAlgEquiv.symm
      π_toAlgHom y := by
        simpa [← Hom.toAlgEquiv_apply] using (f.π_toAlgHom (f.toAlgEquiv.symm y)).symm
      toAlgHom_ι m := by simp [AlgEquiv.symm_apply_eq] }
  inv_comp f := Hom.toAlgHom_injective <| AlgHom.ext fun y ↦ by
    simp [← Hom.toAlgEquiv_apply]
  comp_inv f := Hom.toAlgHom_injective <| AlgHom.ext fun x ↦ by
    simp [← Hom.toAlgEquiv_apply]

variable {E} {F G : SquareZeroExtension.{w} A B M}

@[ext]
theorem hom_ext {f g : E ⟶ F} (h : ∀ x, f.toAlgHom x = g.toAlgHom x) : f = g :=
  Hom.toAlgHom_injective (AlgHom.ext h)

@[simp]
theorem id_toAlgHom : Hom.toAlgHom (𝟙 E) = AlgHom.id A E.Ring :=
  (rfl)

@[simp]
theorem comp_toAlgHom (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  (rfl)

@[simp]
theorem inv_toAlgHom_apply (f : E ⟶ F) (x : E.Ring) : (inv f).toAlgHom (f.toAlgHom x) = x := by
  rw [← AlgHom.comp_apply, ← comp_toAlgHom, IsIso.hom_inv_id, id_toAlgHom, AlgHom.id_apply]

@[simp]
theorem toAlgHom_inv_apply (f : E ⟶ F) (y : F.Ring) : f.toAlgHom ((inv f).toAlgHom y) = y := by
  rw [← AlgHom.comp_apply, ← comp_toAlgHom, IsIso.inv_hom_id, id_toAlgHom, AlgHom.id_apply]

variable (E) in
/-- A splitting of a square-zero extension: an `A`-algebra section of its projection. -/
structure Splitting where
  /-- The section `B → E`. -/
  toAlgHom : B →ₐ[A] E.Ring
  π_toAlgHom (b : B) : E.π (toAlgHom b) = b

attribute [simp] Splitting.π_toAlgHom

/-- A splitting transported along a morphism of square-zero extensions. -/
def Splitting.map (f : E ⟶ F) (s : E.Splitting) : F.Splitting where
  toAlgHom := f.toAlgHom.comp s.toAlgHom
  π_toAlgHom b := by simp

@[simp]
theorem Splitting.map_toAlgHom (f : E ⟶ F) (s : E.Splitting) :
    (s.map f).toAlgHom = f.toAlgHom.comp s.toAlgHom :=
  (rfl)

/-- Isomorphic square-zero extensions split together. -/
theorem nonempty_splitting_iff_of_isIsomorphic (h : IsIsomorphic E F) :
    Nonempty E.Splitting ↔ Nonempty F.Splitting :=
  ⟨fun ⟨s⟩ ↦ ⟨s.map h.some.hom⟩, fun ⟨s⟩ ↦ ⟨s.map h.some.inv⟩⟩

/-- Every square-zero extension of `A` itself splits, by the structure map of the algebra. -/
def algebraMapSplitting {N : Type t} [AddCommGroup N] [Module A N]
    (E : SquareZeroExtension.{w} A A N) : E.Splitting where
  toAlgHom := Algebra.ofId A E.Ring
  π_toAlgHom a := by simp

section Trivial

variable (A B M) [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module A M] [IsScalarTower A B M]
  [IsScalarTower A Bᵐᵒᵖ M]

/-- The trivial square-zero extension `TrivSqZeroExt B M → B` of `B` by `M`, with multiplication
`(b, m) (b', m') = (b b', b m' + b' m)`. -/
-- The body is exposed so that the ring of the extension is known to be `TrivSqZeroExt B M`.
@[expose] def squareZero : SquareZeroExtension.{max v t} A B M where
  Ring := TrivSqZeroExt B M
  π := fstHom A B M
  π_surjective b := ⟨inl b, fst_inl M b⟩
  ι := (inrHom B M).toAddMonoidHom
  ι_injective := inr_injective
  exact x := ⟨fun h ↦ ⟨x.snd, ext (by simpa using h.symm) rfl⟩, by rintro ⟨m, rfl⟩; simp⟩
  mul_ι x m := ext (by simp) (by simp)

@[simp]
theorem squareZero_π (x : TrivSqZeroExt B M) : (squareZero A B M).π x = x.fst :=
  rfl

@[simp]
theorem squareZero_ι (m : M) : (squareZero A B M).ι m = inr m :=
  rfl

/-- The trivial extension is split by the inclusion `b ↦ (b, 0)`. -/
def squareZeroSplitting : (squareZero A B M).Splitting where
  toAlgHom := inlAlgHom A B M
  π_toAlgHom b := fst_inl M b

variable {A B M} {E : SquareZeroExtension.{max v t} A B M}

/-- The `A`-algebra map `(b, m) ↦ s b + ι m` determined by a splitting `s`. -/
private noncomputable def Splitting.liftAlgHom (s : E.Splitting) :
    TrivSqZeroExt B M →ₐ[A] E.Ring :=
  TrivSqZeroExt.lift s.toAlgHom
    { toFun := E.ι
      map_add' := map_add E.ι
      map_smul' a m := by rw [RingHom.id_apply, ← algebraMap_smul B a m, E.ι_algebraMap_smul] }
    (fun m n ↦ E.ι_mul_ι m n) (fun b m ↦ by simp) (fun b m ↦ by simp [mul_comm])

private theorem Splitting.liftAlgHom_apply (s : E.Splitting) (x : TrivSqZeroExt B M) :
    s.liftAlgHom x = s.toAlgHom x.fst + E.ι x.snd := by
  rw [Splitting.liftAlgHom]
  exact TrivSqZeroExt.lift_def _ _ _ _ _ x

/-- The morphism `(b, m) ↦ s b + ι m` from the trivial extension determined by a splitting `s`. -/
noncomputable def Splitting.toHom (s : E.Splitting) : squareZero A B M ⟶ E where
  toAlgHom := s.liftAlgHom
  -- The ring of `squareZero A B M` is `TrivSqZeroExt B M` by its exposed definition; the two
  -- compatibilities are proved at that type and then applied.
  π_toAlgHom x := (by simp [s.liftAlgHom_apply] : ∀ x : TrivSqZeroExt B M,
    E.π (s.liftAlgHom x) = x.fst) x
  toAlgHom_ι m := (by simp [s.liftAlgHom_apply] : ∀ m : M, s.liftAlgHom (inr m) = E.ι m) m

@[simp]
theorem Splitting.toHom_toAlgHom_apply (s : E.Splitting) (x : TrivSqZeroExt B M) :
    s.toHom.toAlgHom x = s.toAlgHom x.fst + E.ι x.snd := by
  rw [Splitting.toHom]
  exact s.liftAlgHom_apply x

/-- A square-zero extension is isomorphic to the trivial one if and only if it splits. -/
theorem isIsomorphic_squareZero_iff :
    IsIsomorphic (squareZero A B M) E ↔ Nonempty E.Splitting :=
  ⟨fun h ↦ (nonempty_splitting_iff_of_isIsomorphic h).1 ⟨squareZeroSplitting A B M⟩,
    fun ⟨s⟩ ↦ Groupoid.isIsomorphic_iff_nonempty_hom.2 ⟨s.toHom⟩⟩

end Trivial

end SquareZeroExtension

/-- `Exal_A(B, M)`: the isomorphism classes of square-zero extensions of the `A`-algebra `B` by
the `B`-module `M`, whose rings lie in the universe of `B` and `M`. -/
def Exal : Type _ :=
  Quotient (isIsomorphicSetoid (SquareZeroExtension.{max v t} A B M))

namespace SquareZeroExtension

variable {A B M}

/-- The class in `Exal_A(B, M)` of a square-zero extension. -/
noncomputable def extensionClass (E : SquareZeroExtension.{max v t} A B M) : Exal A B M :=
  Quotient.mk _ E

theorem extensionClass_surjective :
    Function.Surjective (extensionClass : SquareZeroExtension.{max v t} A B M → Exal A B M) :=
  Quotient.mk_surjective

theorem extensionClass_eq_extensionClass_iff {E F : SquareZeroExtension.{max v t} A B M} :
    E.extensionClass = F.extensionClass ↔ Nonempty (E ⟶ F) :=
  Quotient.eq.trans Groupoid.isIsomorphic_iff_nonempty_hom

end SquareZeroExtension

namespace Exal

variable [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module A M] [IsScalarTower A B M]
  [IsScalarTower A Bᵐᵒᵖ M]

/-- The zero of `Exal_A(B, M)` is the class of the trivial extension. -/
noncomputable instance : Zero (Exal A B M) :=
  ⟨(SquareZeroExtension.squareZero A B M).extensionClass⟩

theorem zero_def : (0 : Exal A B M) = (SquareZeroExtension.squareZero A B M).extensionClass :=
  (rfl)

end Exal

namespace SquareZeroExtension

variable {A B M} [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module A M] [IsScalarTower A B M]
  [IsScalarTower A Bᵐᵒᵖ M]

/-- A square-zero extension has the zero class if and only if it splits. -/
theorem extensionClass_eq_zero_iff (E : SquareZeroExtension.{max v t} A B M) :
    E.extensionClass = 0 ↔ Nonempty E.Splitting := by
  rw [Exal.zero_def, eq_comm, ← isIsomorphic_squareZero_iff]
  exact Quotient.eq

end SquareZeroExtension

section Self

variable {A} {N : Type t} [AddCommGroup N] [Module A N] [Module Aᵐᵒᵖ N] [IsCentralScalar A N]
  [IsScalarTower A Aᵐᵒᵖ N]

/-- `Exal_A(A, N)` is zero: every square-zero extension of `A` itself splits. -/
instance Exal.subsingleton_self : Subsingleton (Exal A A N) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨E, rfl⟩ := SquareZeroExtension.extensionClass_surjective x
  obtain ⟨F, rfl⟩ := SquareZeroExtension.extensionClass_surjective y
  rw [E.extensionClass_eq_zero_iff.2 ⟨E.algebraMapSplitting⟩,
    F.extensionClass_eq_zero_iff.2 ⟨F.algebraMapSplitting⟩]

end Self

namespace SquareZeroExtension

/-- The square-zero extension `ℤ/4 → ℤ/2` of `ℤ/2` by `ℤ/2` over `ℤ`, whose kernel `2ℤ/4ℤ` is
identified with `ℤ/2` by `m ↦ 2m`. -/
@[expose] def zmodFour : SquareZeroExtension.{0} ℤ (ZMod 2) (ZMod 2) where
  Ring := ZMod 4
  π := (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toIntAlgHom
  π_surjective := by decide
  ι := AddMonoidHom.mk' (fun m ↦ 2 * (m.val : ZMod 4)) (by decide)
  ι_injective := by decide
  exact y := by
    rw [Set.mem_range]
    revert y
    decide
  mul_ι := by decide

/-- The extension `ℤ/4 → ℤ/2` does not split: there is no ring map `ℤ/2 → ℤ/4`. -/
theorem isEmpty_splitting_zmodFour : IsEmpty zmodFour.Splitting := by
  refine ⟨fun s ↦ ?_⟩
  have h := map_add s.toAlgHom 1 1
  rw [show (1 + 1 : ZMod 2) = 0 from rfl, map_zero, map_one] at h
  exact absurd h (by decide : (0 : ZMod 4) ≠ 1 + 1)

/-- The extension `ℤ/4 → ℤ/2` has a nonzero class in `Exal_ℤ(ℤ/2, ℤ/2)`. -/
theorem zmodFour_extensionClass_ne_zero : zmodFour.extensionClass ≠ 0 := by
  rw [Ne, extensionClass_eq_zero_iff, not_nonempty_iff]
  exact isEmpty_splitting_zmodFour

end SquareZeroExtension

end TauCeti
