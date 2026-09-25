/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.Algebra.Homology.GradedCochainComplex
public import TauCeti.CategoryTheory.DG.HomComplexData

/-!
# The one-object differential graded category of a differential graded algebra

A differential graded algebra `(A, d)` over `R` determines a differential graded category with a
single object: the Hom complex of that object is the underlying cochain complex of `A`, the
identity is `1`, and composition is multiplication.  This file constructs that
category, `TauCeti.DGSingleObj h`, for a DG algebra `h : IsDGAlgebra 𝒜 d`.

Multiplication is Keller-ordered composition: for homogeneous `a` and `b`, the product `a * b`
is `a ∘ b`, "first `b`, then `a`", so that the Leibniz rule
`d (a * b) = d a * b + (-1) ^ |a| • a * d b` is the Leibniz rule of Keller composition.
Composition in a `TauCeti.DGCategory` is in Mathlib's enriched factor order instead, and the
two orders differ by the Koszul sign: for `f` of degree `p` and `g` of degree `q`,

`dgComp f g = (-1) ^ (p * q) • (g * f)`.

This is `TauCeti.DGSingleObj.dgHomEquiv_dgComp`, the sign-bridge between the algebra and the
category conventions.

The degree-`n` morphisms of the single object are the degree-`n` part of `A`,
`TauCeti.DGSingleObj.dgHomEquiv`, and under this identification the differential, the identity
and composition are `d`, `1` and signed multiplication.  These are the public interface to the
construction.

## Main definitions

* `TauCeti.DGSingleObj`: the one-object differential graded category of a DG algebra.
* `TauCeti.DGSingleObj.star`: its unique object.
* `TauCeti.DGSingleObj.homComplexData`: its explicit Hom-complex data.
* `TauCeti.DGSingleObj.dgHomEquiv`: the degree-`n` morphisms are the degree-`n` part of `A`.

## Main results

* `TauCeti.DGSingleObj.dgHomComplex_eq`: the Hom complex is the underlying cochain complex of `A`.
* `TauCeti.DGSingleObj.dgHomEquiv_dgDifferential`: the differential of the category is `d`.
* `TauCeti.DGSingleObj.dgHomEquiv_dgId`: the identity is `1`.
* `TauCeti.DGSingleObj.dgHomEquiv_dgComp`: composition is multiplication in the reversed order,
  with the Koszul sign `(-1) ^ (p * q)`.

## References

* B. Keller, *Deriving DG categories*, Section 1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- The objects of the **one-object differential graded category** of a DG algebra
`h : IsDGAlgebra 𝒜 d`: a single object `TauCeti.DGSingleObj.star h`, whose Hom complex is the
underlying cochain complex of `A` and whose composition is multiplication.

The type is a structure indexed by `h`, so that objects of the categories of different DG
algebras are not interchangeable. -/
structure DGSingleObj (h : IsDGAlgebra 𝒜 d) : Type

namespace DGSingleObj

variable (h : IsDGAlgebra 𝒜 d)

/-- The unique object of the one-object differential graded category. -/
def star : DGSingleObj h := ⟨⟩

instance : Unique (DGSingleObj h) where
  default := star h
  uniq _ := rfl

/-! ### The Hom complex -/

/-- The underlying cochain complex of `A`: the degree-`n` term is `𝒜 n` and the differential is
the restriction of `d`. -/
private abbrev homComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  gradedCochainComplex 𝒜 d (LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha)
    fun _ x ↦ h.sq_zero x

/-- The degree-`n` term of the underlying complex is `𝒜 n`. -/
private noncomputable def homComplexXEquiv (n : ℤ) : (homComplex h).X n ≃ₗ[R] 𝒜 n :=
  (eqToIso (gradedCochainComplex_X n)).toLinearEquiv

private theorem homComplexXEquiv_d (n : ℤ) (x : (homComplex h).X n) :
    (homComplexXEquiv h (n + 1) (((homComplex h).d n (n + 1)).hom x) : A) =
      d (homComplexXEquiv h n x) := by
  have key := gradedCochainComplex_d_apply
    (hdeg := LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha)
    (hsq := fun _ x ↦ h.sq_zero x) n (homComplexXEquiv h n x)
  -- `homComplexXEquiv` is the `eqToHom` of `gradedCochainComplex_X`, whose inverse cancels it.
  rw [show (eqToHom (gradedCochainComplex_X n).symm) (homComplexXEquiv h n x) = x from
    (eqToIso (gradedCochainComplex_X n)).hom_inv_id_apply x] at key
  exact congrArg Subtype.val key

/-- Keller-ordered composition on the underlying complex: multiplication. -/
private noncomputable def kellerComp (q p n : ℤ) (hn : q + p = n) :
    (homComplex h).X q →ₗ[R] (homComplex h).X p →ₗ[R] (homComplex h).X n :=
  ((DirectSum.gMulLHom R (fun i ↦ 𝒜 i)).compl₁₂ (homComplexXEquiv h q).toLinearMap
    (homComplexXEquiv h p).toLinearMap).compr₂
      ((LinearEquiv.ofEq _ _ (congrArg 𝒜 hn)).trans (homComplexXEquiv h n).symm).toLinearMap

private theorem homComplexXEquiv_kellerComp (q p n : ℤ) (hn : q + p = n)
    (g : (homComplex h).X q) (f : (homComplex h).X p) :
    (homComplexXEquiv h n (kellerComp h q p n hn g f) : A) =
      homComplexXEquiv h q g * homComplexXEquiv h p f := by
  simp [kellerComp]

/-- The identity: the unit `1` in degree zero. -/
private noncomputable def one : (homComplex h).X 0 :=
  (homComplexXEquiv h 0).symm ⟨1, SetLike.one_mem_graded 𝒜⟩

private theorem homComplexXEquiv_one : (homComplexXEquiv h 0 (one h) : A) = 1 := by
  simp [one]

/-- The explicit Hom-complex data of the one-object differential graded category, from
Keller-ordered composition given by multiplication. -/
noncomputable def homComplexData : DGCategoryData R (DGSingleObj h) :=
  DGCategoryData.ofKeller (fun _ _ ↦ homComplex h) (fun q p n hn ↦ kellerComp h q p n hn)
    (fun _ ↦ one h)
    (fun {_ _ _ q p n} hn g f ↦ (homComplexXEquiv h (n + 1)).injective <| Subtype.ext <| by
      simpa only [map_add, Units.smul_def, map_zsmul, Submodule.coe_add,
        Submodule.coe_smul_of_tower, homComplexXEquiv_d, homComplexXEquiv_kellerComp] using
        h.leibniz (homComplexXEquiv h q g).2 (homComplexXEquiv h p f))
    (fun {_ _ _ _ r q p rq qp n} hrq hqp hn k g f ↦
      (homComplexXEquiv h n).injective <| Subtype.ext <| by
        simp only [homComplexXEquiv_kellerComp, mul_assoc])
    (fun {_ _ q} g ↦ (homComplexXEquiv h q).injective <| Subtype.ext <| by
      simp only [homComplexXEquiv_kellerComp, homComplexXEquiv_one, mul_one])
    (fun {_ _ p} f ↦ (homComplexXEquiv h p).injective <| Subtype.ext <| by
      simp only [homComplexXEquiv_kellerComp, homComplexXEquiv_one, one_mul])

/-- The one-object differential graded category of a DG algebra. -/
noncomputable instance : DGCategory R (DGSingleObj h) :=
  (homComplexData h).toDGCategory

/-! ### Morphisms, differential, identity and composition -/

variable {h}

/-- The Hom complex of the one-object differential graded category is the underlying cochain
complex of the algebra. -/
theorem dgHomComplex_eq (X Y : DGSingleObj h) :
    dgHomComplex R X Y =
      gradedCochainComplex 𝒜 d (LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha)
        fun _ x ↦ h.sq_zero x :=
  (rfl)

/-- The degree-`n` morphisms of the one-object differential graded category are the degree-`n`
part of the algebra. -/
noncomputable def dgHomEquiv (X Y : DGSingleObj h) (n : ℤ) : DGHom R n X Y ≃ₗ[R] 𝒜 n :=
  homComplexXEquiv h n

/-- The differential of the explicit Hom-complex data is the differential of the algebra. -/
@[simp]
private theorem homComplexData_d_apply {X Y : DGSingleObj h} (n : ℤ) (f : DGHom R n X Y) :
    (dgHomEquiv X Y (n + 1) ((((homComplexData h).hom X Y).d n (n + 1)).hom f) : A) =
      d (dgHomEquiv X Y n f) :=
  homComplexXEquiv_d h n f

/-- The identity of the explicit Hom-complex data is the unit of the algebra. -/
@[simp]
private theorem homComplexData_id (X : DGSingleObj h) :
    (dgHomEquiv X X 0 ((homComplexData h).id X) : A) = 1 :=
  homComplexXEquiv_one h

/-- The composition of the explicit Hom-complex data is multiplication in the reversed order,
with the Koszul sign `(-1) ^ (p * q)`. -/
@[simp]
private theorem homComplexData_comp {X Y Z : DGSingleObj h} {p q n : ℤ} (hpq : p + q = n)
    (f : DGHom R p X Y) (g : DGHom R q Y Z) :
    (dgHomEquiv X Z n ((homComplexData h).comp p q n hpq f g) : A) =
      (p * q).negOnePow • (dgHomEquiv Y Z q g * dgHomEquiv X Y p f) := by
  have hcomp : (homComplexData h).comp p q n hpq f g =
      (p * q).negOnePow • kellerComp h q p n (by omega) g f := by
    rfl
  rw [hcomp]
  exact (congrArg Subtype.val (map_zsmul_unit (homComplexXEquiv h n) _
    (kellerComp h q p n (by omega) g f))).trans
      (congrArg _ (homComplexXEquiv_kellerComp h q p n _ g f))

/-- The differential of the one-object differential graded category is the differential of the
algebra. -/
@[simp↓]
theorem dgHomEquiv_dgDifferential {X Y : DGSingleObj h} (n : ℤ) (f : DGHom R n X Y) :
    (dgHomEquiv X Y (n + 1) (dgDifferential R n f) : A) = d (dgHomEquiv X Y n f) := by
  rw [(homComplexData h).dgDifferential_toDGCategory n f]
  exact homComplexData_d_apply n f

/-- The identity of the one-object differential graded category is the unit of the algebra. -/
@[simp↓]
theorem dgHomEquiv_dgId (X : DGSingleObj h) : (dgHomEquiv X X 0 (dgId R X) : A) = 1 := by
  rw [(homComplexData h).dgId_toDGCategory X]
  exact homComplexData_id X

/-- **Composition in the one-object differential graded category is multiplication.**  Since
`dgComp f g` is `f` followed by `g` while `g * f` is the Keller composite "first `f`, then `g`",
the two differ by the Koszul sign `(-1) ^ (p * q)`. -/
@[simp↓]
theorem dgHomEquiv_dgComp {X Y Z : DGSingleObj h} {p q n : ℤ} (f : DGHom R p X Y)
    (g : DGHom R q Y Z) (hpq : p + q = n) :
    (dgHomEquiv X Z n (dgComp R f g hpq) : A) =
      (p * q).negOnePow • (dgHomEquiv Y Z q g * dgHomEquiv X Y p f) := by
  rw [(homComplexData h).dgComp_toDGCategory f g hpq]
  exact homComplexData_comp hpq f g

end DGSingleObj

end TauCeti
