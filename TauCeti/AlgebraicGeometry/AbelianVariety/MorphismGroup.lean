/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom

/-!
# The group of homomorphisms of abelian varieties

For abelian varieties `A B : AbelianVariety K`, the homomorphisms `A ⟶ B` form a commutative
group under the pointwise group law of the target: since the group scheme underlying `B` is
commutative, the pointwise product `f * g := lift f g ≫ μ[B]` of two homomorphisms is again a
homomorphism. This file transports Mathlib's group structure on morphisms into a commutative group
object (`CategoryTheory.MonObj.Hom.commGroup`, applied in the category of group objects over
`Spec K`) onto `A ⟶ B`, and records how the underlying morphism over `Spec K` interacts with the
group operations.

The group law is written **multiplicatively**, matching the multiplicative encoding
(`GrpObj`, `μ`, `η`, `ι`) of the group-object structure carried by an `AbelianVariety`; for the
Jacobian this pointwise product is the tensor product of line bundles.

* `AbelianVariety.Hom.instCommGroup`: the commutative group structure on `A ⟶ B`
  (a `scoped instance`);
* `AbelianVariety.Hom.grpEquiv` / `AbelianVariety.Hom.grpMulEquiv`: the identification of `A ⟶ B`
  with homomorphisms of the underlying commutative group objects, as an `Equiv` and as a
  multiplicative equivalence;
* `AbelianVariety.Hom.toOverHom_mul`, `toOverHom_one`, `toOverHom_inv`, `toOverHom_div`: the
  underlying morphism over `Spec K` is a homomorphism of these groups;
* `AbelianVariety.Hom.mul_comp` and `AbelianVariety.Hom.comp_mul`: composition is bimultiplicative,
  so `AbelianVariety K` behaves like a preadditive category with respect to this group law.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API", by supplying the group structure
on the homomorphism sets. Layer F's universal property produces a *unique* homomorphism of abelian
varieties; the group law here is the ambient structure in which that uniqueness and the Albanese
functoriality are expressed. No external mathematics is vendored; the group structure is transported
from Mathlib's `CategoryTheory.MonObj.Hom.commGroup` on morphisms into a commutative group object,
via the existing Tau Ceti abelian-variety homomorphism API.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

open scoped CategoryTheory.MonObj

noncomputable section

/-- A homomorphism of abelian varieties, viewed as a homomorphism of the underlying commutative
group objects over `Spec K`. -/
def Hom.grpEquiv (A B : AbelianVariety K) :
    (A ⟶ B) ≃ ((CommGrp.mk A.toOver).toGrp ⟶ (CommGrp.mk B.toOver).toGrp) :=
  InducedCategory.homEquiv.trans InducedCategory.homEquiv

/-- Homomorphisms of abelian varieties over `K` form a commutative group under the pointwise group
law of the target, transported from Mathlib's group structure on morphisms into a commutative group
object. -/
scoped instance Hom.instCommGroup (A B : AbelianVariety K) : CommGroup (A ⟶ B) :=
  (Hom.grpEquiv A B).commGroup

variable {A B : AbelianVariety K}

lemma Hom.grpEquiv_apply (f : A ⟶ B) :
    Hom.grpEquiv A B f = f.hom.hom := by
  unfold Hom.grpEquiv; rfl

lemma Hom.grpEquiv_mul (f g : A ⟶ B) :
    Hom.grpEquiv A B (f * g) = Hom.grpEquiv A B f * Hom.grpEquiv A B g :=
  (Hom.grpEquiv A B).apply_symm_apply _

lemma Hom.grpEquiv_one :
    Hom.grpEquiv A B (1 : A ⟶ B) = 1 :=
  (Hom.grpEquiv A B).apply_symm_apply _

lemma Hom.grpEquiv_inv (f : A ⟶ B) :
    Hom.grpEquiv A B f⁻¹ = (Hom.grpEquiv A B f)⁻¹ :=
  (Hom.grpEquiv A B).apply_symm_apply _

lemma Hom.grpEquiv_div (f g : A ⟶ B) :
    Hom.grpEquiv A B (f / g) = Hom.grpEquiv A B f / Hom.grpEquiv A B g :=
  (Hom.grpEquiv A B).apply_symm_apply _

/-- Identifying a homomorphism of abelian varieties with its underlying homomorphism of commutative
group objects is a group isomorphism onto the latter's group of homomorphisms. -/
def Hom.grpMulEquiv (A B : AbelianVariety K) :
    (A ⟶ B) ≃* ((CommGrp.mk A.toOver).toGrp ⟶ (CommGrp.mk B.toOver).toGrp) where
  __ := Hom.grpEquiv A B
  map_mul' := Hom.grpEquiv_mul

@[simp] lemma Hom.grpMulEquiv_apply (f : A ⟶ B) :
    Hom.grpMulEquiv A B f = f.hom.hom := by
  rw [show (Hom.grpMulEquiv A B f) = Hom.grpEquiv A B f from rfl, Hom.grpEquiv_apply]

/-- The underlying morphism over `Spec K` of a homomorphism of abelian varieties is the underlying
morphism of the corresponding commutative-group-object homomorphism. -/
lemma Hom.toOverHom_eq_grpEquiv (f : A ⟶ B) :
    Hom.toOverHom f = (Hom.grpEquiv A B f).hom.hom := by
  rw [Hom.grpEquiv_apply]; simp [Hom.toOverHom, Hom.toOverFunctor]

/-- The underlying morphism over `Spec K` sends the product of two homomorphisms to the pointwise
product. -/
@[simp] lemma Hom.toOverHom_mul (f g : A ⟶ B) :
    Hom.toOverHom (f * g) = Hom.toOverHom f * Hom.toOverHom g := by
  rw [Hom.toOverHom_eq_grpEquiv, Hom.toOverHom_eq_grpEquiv, Hom.toOverHom_eq_grpEquiv,
    Hom.grpEquiv_mul]
  simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul]

/-- The underlying morphism over `Spec K` sends the identity of the group of homomorphisms to the
identity element `toUnit A.toOver ≫ η[B.toOver]` (the constant homomorphism through the unit
section). -/
@[simp] lemma Hom.toOverHom_one :
    Hom.toOverHom (1 : A ⟶ B) = 1 := by
  rw [Hom.toOverHom_eq_grpEquiv, Hom.grpEquiv_one]
  simp only [Grp.Hom.hom_one, Mon.Hom.hom_one]

/-- The underlying morphism over `Spec K` sends the inverse of a homomorphism to the pointwise
inverse. -/
@[simp] lemma Hom.toOverHom_inv (f : A ⟶ B) :
    Hom.toOverHom f⁻¹ = (Hom.toOverHom f)⁻¹ := by
  rw [Hom.toOverHom_eq_grpEquiv, Hom.toOverHom_eq_grpEquiv, Hom.grpEquiv_inv]
  simp only [Grp.Hom.hom_hom_inv]

/-- The underlying morphism over `Spec K` sends the quotient of two homomorphisms to the pointwise
quotient. -/
@[simp] lemma Hom.toOverHom_div (f g : A ⟶ B) :
    Hom.toOverHom (f / g) = Hom.toOverHom f / Hom.toOverHom g := by
  rw [Hom.toOverHom_eq_grpEquiv, Hom.toOverHom_eq_grpEquiv, Hom.toOverHom_eq_grpEquiv,
    Hom.grpEquiv_div]
  simp only [Grp.Hom.hom_hom_div]

lemma Hom.toOverHom_injective (A B : AbelianVariety K) :
    Function.Injective (Hom.toOverHom : (A ⟶ B) → _) := fun _ _ h =>
  Hom.ext (congrArg Over.Hom.left h)

/-! ### Bilinearity of composition -/

/-- Composition of homomorphisms of abelian varieties distributes over the pointwise product on the
right: post-composition by a homomorphism is multiplicative. -/
@[reassoc] lemma Hom.mul_comp {A B C : AbelianVariety K} (f g : A ⟶ B) (h : B ⟶ C) :
    (f * g) ≫ h = f ≫ h * g ≫ h := by
  apply Hom.toOverHom_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_mul, MonObj.mul_comp]

/-- Composition of homomorphisms of abelian varieties distributes over the pointwise product on the
left: pre-composition by a homomorphism is multiplicative. -/
@[reassoc] lemma Hom.comp_mul {A B C : AbelianVariety K} (f : A ⟶ B) (g h : B ⟶ C) :
    f ≫ (g * h) = f ≫ g * f ≫ h := by
  apply Hom.toOverHom_injective
  simp only [Hom.toOverHom_comp, Hom.toOverHom_mul, MonObj.comp_mul]

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
