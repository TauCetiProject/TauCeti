/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.lpSpace
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.Normed.Lp.C0Ideal
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The bounded product of C⋆-algebras

For a family of nonzero unital C⋆-algebras `A i`, the bounded product `lp A ∞` is a unital
C⋆-algebra, `lp.inftyCStarAlgebra`. Mathlib provides the nonunital instance and the unital
commutative one; nontriviality of the factors makes the unit `(1)ᵢ` have norm one, and the unitary
group of `lp A ∞` is canonically isomorphic to the product `∀ i, unitary (A i)` (`lp.unitaryEquiv`).

With the closed filter-null ideals `lp.nullIdeal` and `lp.c0Ideal` of
`TauCeti.Analysis.Normed.Lp.C0Ideal`, the quotient `lp A ∞ ⧸ lp.nullIdeal A l` is a C⋆-algebra
(unital when the factors are nonzero unital C⋆-algebras) by
`TwoSidedIdeal.Quotient.nonUnitalCStarAlgebra` and `TwoSidedIdeal.Quotient.cstarAlgebra`.

For a family of possibly nonunital C⋆-algebras, `lp A ∞` is the product in the category of
C⋆-algebras: the coordinate projections `lp.evalNonUnitalStarAlgHom` are star homomorphisms, and
`lp.liftNonUnitalStarAlgHom` identifies star homomorphisms into `lp A ∞` with families of star
homomorphisms into the factors. Coordinatewise families of `⋆`-homomorphisms and `⋆`-isomorphisms
assemble into `lp.mapNonUnitalStarAlgHom`, `lp.mapStarAlgHom`, and `lp.mapStarAlgEquiv`.

For a concrete family, such as `A n = CStarMatrix (Fin (n + 1)) (Fin (n + 1)) ℂ`, instance search
does not find the C⋆-structure on `lp A ∞ ⧸ lp.c0Ideal A` within the default limits: matching
the generic quotient instances against the ring structure of `lp A ∞` requires synthesizing the
C⋆-structures of `lp A ∞` and of each `A n` as postponed subproblems, and for `CStarMatrix` over
`ℂ` these nest beyond the allowed depth. The type `lp.QuotientC0 A` is this quotient with its
unital C⋆-algebra structure `lp.QuotientC0.instCStarAlgebra` registered directly, so that instance
search only needs `CStarAlgebra (A i)` and `Nontrivial (A i)`; the structures below it, such as
the norm, the star and the `ℂ`-algebra structure, are its projections.

## Main definitions

* `lp.inftyCStarAlgebra`: the unital C⋆-algebra `lp A ∞`.
* `lp.unitaryEquiv`: canonical isomorphism `unitary (lp A ∞) ≃* ∀ i, unitary (A i)`.
* `lp.evalNonUnitalStarAlgHom`: the coordinate projections, star homomorphisms.
* `lp.piNonUnitalStarAlgHom`, `lp.liftNonUnitalStarAlgHom`: the star homomorphism into `lp A ∞`
  given by a bounded family of star homomorphisms into the factors.
* `lp.mapNonUnitalStarAlgHom`, `lp.mapStarAlgHom`, `lp.mapStarAlgEquiv`: coordinatewise functorial
  `⋆`-homomorphisms and `⋆`-isomorphisms on `lp _ ∞`.
* `lp.QuotientC0`: the quotient `lp A ∞ ⧸ lp.c0Ideal A`, a unital C⋆-algebra.
* `lp.QuotientC0.mk`: the quotient map, a unital `⋆`-algebra homomorphism.
* `lp.QuotientC0.lift`: the unital `⋆`-homomorphism out of `lp.QuotientC0 A` induced by one
  vanishing on the `c₀` ideal.
* `lp.QuotientC0.norm_mk`: the quotient norm is the limit superior of the coordinate norms.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open Filter
open scoped ENNReal

namespace TauCeti

/-- Any family of unitaries in unital C⋆-rings with `‖(1 : A i)‖ = 1` has coordinate norms bounded
by `1` and therefore belongs to `ℓ^∞`. -/
theorem memℓp_infty_unitary {ι : Type*} {A : ι → Type*} [∀ i, NormedRing (A i)]
    [∀ i, StarRing (A i)] [∀ i, CStarRing (A i)] [∀ i, NormOneClass (A i)]
    (u : ∀ i, unitary (A i)) : Memℓp (fun i ↦ (u i : A i)) ∞ :=
  ⟨1, by
    rintro _ ⟨i, rfl⟩
    calc ‖(u i : A i)‖ = ‖(u i : A i) * 1‖ := by rw [mul_one]
      _ = ‖(1 : A i)‖ := CStarRing.norm_coe_unitary_mul (u i) 1
      _ ≤ 1 := norm_one.le⟩

end TauCeti

namespace lp

section Product

section Eval

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalNormedRing (A i)] [∀ i, StarAddMonoid (A i)]
  [∀ i, NormedStarGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, IsBoundedSMul ℂ (A i)]

variable (A) in
/-- The coordinate projection of the bounded product `lp A ∞` onto its factor `A i`, as a star
homomorphism. -/
def evalNonUnitalStarAlgHom (i : ι) : lp A ∞ →⋆ₙₐ[ℂ] A i where
  toFun a := a i
  map_smul' c a := by simp [lp.coeFn_smul]
  map_zero' := by simp
  map_add' a b := by simp
  map_mul' a b := by simp [infty_coeFn_mul]
  map_star' a := lp.star_apply a i

/-- The coordinate projection evaluates a bounded family at an index. -/
@[simp]
theorem evalNonUnitalStarAlgHom_apply (i : ι) (a : lp A ∞) :
    evalNonUnitalStarAlgHom A i a = a i :=
  (rfl)

variable (A) in
/-- The coordinate projections of the bounded product are surjective. -/
theorem evalNonUnitalStarAlgHom_surjective (i : ι) :
    Function.Surjective (evalNonUnitalStarAlgHom A i) := by
  classical
  exact fun a ↦ ⟨lp.single ∞ i a, by simp⟩

/-- Two star homomorphisms into a bounded product agree when all their coordinates agree. -/
@[ext]
theorem nonUnitalStarAlgHom_ext {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B]
    [Star B] {φ ψ : B →⋆ₙₐ[ℂ] lp A ∞}
    (h : ∀ i, (evalNonUnitalStarAlgHom A i).comp φ = (evalNonUnitalStarAlgHom A i).comp ψ) :
    φ = ψ :=
  NonUnitalStarAlgHom.ext fun b ↦ lp.ext <| funext fun i ↦ by
    simpa using congr($(h i) b)

variable {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B] [Star B]

/-- A family of star homomorphisms `φ i : B → A i` that is bounded at every `b` gives the star
homomorphism `b ↦ (φ i b)ᵢ` into the bounded product. `B` needs no norm. -/
noncomputable def piNonUnitalStarAlgHom (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Memℓp (fun i ↦ φ i b) ∞) : B →⋆ₙₐ[ℂ] lp A ∞ where
  toFun b := ⟨fun i ↦ φ i b, hφ b⟩
  map_smul' c b := lp.ext <| funext fun i ↦ map_smul (φ i) c b
  map_zero' := lp.ext <| funext fun i ↦ map_zero (φ i)
  map_add' b b' := lp.ext <| funext fun i ↦ map_add (φ i) b b'
  map_mul' b b' := lp.ext <| funext fun i ↦ map_mul (φ i) b b'
  map_star' b := lp.ext <| funext fun i ↦ map_star (φ i) b

/-- The `i`-th coordinate of `lp.piNonUnitalStarAlgHom φ hφ b` is `φ i b`. -/
@[simp]
theorem piNonUnitalStarAlgHom_apply_apply (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Memℓp (fun i ↦ φ i b) ∞) (b : B) (i : ι) :
    piNonUnitalStarAlgHom φ hφ b i = φ i b :=
  (rfl)

end Eval

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]
variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- **The universal property of the bounded product**: star homomorphisms from a C⋆-algebra `B`
into `lp A ∞` are the families of star homomorphisms `B → A i`. The family `φ` is sent to
`lp.piNonUnitalStarAlgHom φ`, `b ↦ (φ i b)ᵢ`, which is bounded by `‖b‖` since star homomorphisms
between C⋆-algebras are contractive. -/
noncomputable def liftNonUnitalStarAlgHom : (∀ i, B →⋆ₙₐ[ℂ] A i) ≃ (B →⋆ₙₐ[ℂ] lp A ∞) where
  toFun φ := piNonUnitalStarAlgHom φ fun b ↦ memℓp_infty ⟨‖b‖, by
    rintro _ ⟨i, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le (φ i) b⟩
  invFun ψ i := (evalNonUnitalStarAlgHom A i).comp ψ
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

/-- The `i`-th coordinate of `lp.liftNonUnitalStarAlgHom φ b` is `φ i b`. -/
@[simp]
theorem liftNonUnitalStarAlgHom_apply_apply (φ : ∀ i, B →⋆ₙₐ[ℂ] A i) (b : B) (i : ι) :
    liftNonUnitalStarAlgHom φ b i = φ i b :=
  (rfl)

/-- The coordinates of `lp.liftNonUnitalStarAlgHom φ` are the members of the family `φ`. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_liftNonUnitalStarAlgHom (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (i : ι) : (evalNonUnitalStarAlgHom A i).comp (liftNonUnitalStarAlgHom φ) = φ i := by
  ext b
  simp

/-- The inverse of `lp.liftNonUnitalStarAlgHom` takes the coordinates of a star homomorphism. -/
@[simp]
theorem liftNonUnitalStarAlgHom_symm_apply (ψ : B →⋆ₙₐ[ℂ] lp A ∞) (i : ι) :
    liftNonUnitalStarAlgHom.symm ψ i = (evalNonUnitalStarAlgHom A i).comp ψ :=
  (rfl)

/-- A star homomorphism into the bounded product is the lift of its coordinates. -/
@[simp]
theorem liftNonUnitalStarAlgHom_evalNonUnitalStarAlgHom_comp (ψ : B →⋆ₙₐ[ℂ] lp A ∞) :
    liftNonUnitalStarAlgHom (fun i ↦ (evalNonUnitalStarAlgHom A i).comp ψ) = ψ :=
  liftNonUnitalStarAlgHom.apply_symm_apply ψ

variable (A) in
/-- The lift of the coordinate projections is the identity of the bounded product. -/
@[simp]
theorem liftNonUnitalStarAlgHom_evalNonUnitalStarAlgHom :
    liftNonUnitalStarAlgHom (evalNonUnitalStarAlgHom A) = NonUnitalStarAlgHom.id ℂ (lp A ∞) := by
  ext
  simp

/-- Precomposing a lift with a star homomorphism `g` lifts the precomposed family. -/
theorem liftNonUnitalStarAlgHom_comp {C : Type*} [NonUnitalCStarAlgebra C]
    (φ : ∀ i, B →⋆ₙₐ[ℂ] A i) (g : C →⋆ₙₐ[ℂ] B) :
    (liftNonUnitalStarAlgHom φ).comp g = liftNonUnitalStarAlgHom fun i ↦ (φ i).comp g := by
  ext
  simp

end Product

section CStarAlgebra

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The bounded product `lp A ∞` of nonzero unital C⋆-algebras is a unital C⋆-algebra. -/
noncomputable instance inftyCStarAlgebra : CStarAlgebra (lp A ∞) where

end CStarAlgebra

section Unitary

variable {ι : Type*} {A : ι → Type*} [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)]
  [∀ i, CStarRing (A i)] [∀ i, NormOneClass (A i)]

/-- The unitary group of `lp A ∞` is canonically isomorphic to the product `∀ i, unitary (A i)` of
the coordinate unitary groups. -/
noncomputable def unitaryEquiv : unitary (lp A ∞) ≃* ∀ i, unitary (A i) where
  toFun U i := ⟨(U : lp A ∞) i, Unitary.mem_iff.mpr
    ⟨by simpa only [lp.infty_coeFn_one, Pi.one_apply, lp.infty_coeFn_mul, Pi.mul_apply,
        lp.star_apply] using congrArg (fun x : lp A ∞ ↦ x i) (Unitary.coe_star_mul_self U),
     by simpa only [Unitary.coe_star, lp.infty_coeFn_one, Pi.one_apply, lp.infty_coeFn_mul,
        Pi.mul_apply, lp.star_apply] using
        congrArg (fun x : lp A ∞ ↦ x i) (Unitary.coe_mul_star_self U)⟩⟩
  invFun u := ⟨⟨fun i ↦ (u i : A i), TauCeti.memℓp_infty_unitary u⟩, Unitary.mem_iff.mpr
    ⟨by ext i; simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
        Pi.one_apply] using Unitary.coe_star_mul_self (u i),
     by ext i; simpa only [Unitary.coe_star, lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply,
        lp.infty_coeFn_one, Pi.one_apply] using Unitary.coe_mul_star_self (u i)⟩⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem coe_unitaryEquiv_apply (U : unitary (lp A ∞)) (i : ι) :
    (unitaryEquiv U i : A i) = (U : lp A ∞) i := (rfl)

@[simp]
theorem coe_unitaryEquiv_symm_apply (u : ∀ i, unitary (A i)) (i : ι) :
    (unitaryEquiv.symm u : lp A ∞) i = (u i : A i) := (rfl)

end Unitary

section Map

section NonUnital

variable {ι : Type*} {A B C : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]
  [∀ i, NonUnitalCStarAlgebra (B i)]

/-- Coordinatewise application of a family of non-unital `⋆`-homomorphisms between C⋆-algebras on
bounded products. -/
noncomputable def mapNonUnitalStarAlgHom (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) : lp A ∞ →⋆ₙₐ[ℂ] lp B ∞ :=
  liftNonUnitalStarAlgHom fun i ↦ (φ i).comp (evalNonUnitalStarAlgHom A i)

@[simp]
theorem mapNonUnitalStarAlgHom_apply (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) (a : lp A ∞) (i : ι) :
    mapNonUnitalStarAlgHom φ a i = φ i (a i) := (rfl)

@[simp]
theorem mapNonUnitalStarAlgHom_id :
    mapNonUnitalStarAlgHom (fun i ↦ NonUnitalStarAlgHom.id ℂ (A i)) =
      NonUnitalStarAlgHom.id ℂ (lp A ∞) := by ext; rfl

theorem mapNonUnitalStarAlgHom_comp [∀ i, NonUnitalCStarAlgebra (C i)]
    (ψ : ∀ i, B i →⋆ₙₐ[ℂ] C i) (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) :
    (mapNonUnitalStarAlgHom ψ).comp (mapNonUnitalStarAlgHom φ) =
      mapNonUnitalStarAlgHom (fun i ↦ (ψ i).comp (φ i)) := by ext; rfl

/-- If each coordinate `⋆`-homomorphism `φ i` is injective, then `lp.mapNonUnitalStarAlgHom φ` is
an isometry. -/
theorem isometry_mapNonUnitalStarAlgHom {φ : ∀ i, A i →⋆ₙₐ[ℂ] B i}
    (hφ : ∀ i, Function.Injective (φ i)) : Isometry (mapNonUnitalStarAlgHom φ) :=
  NonUnitalStarAlgHom.isometry _ fun _ _ hab ↦
    lp.ext <| funext fun i ↦ hφ i (congrArg (fun x : lp B ∞ ↦ x i) hab)

/-- Coordinatewise `⋆`-isomorphism of bounded products induced by a family of `⋆`-isomorphisms of
C⋆-algebras. -/
noncomputable def mapStarAlgEquiv (e : ∀ i, A i ≃⋆ₐ[ℂ] B i) : lp A ∞ ≃⋆ₐ[ℂ] lp B ∞ :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    (mapNonUnitalStarAlgHom fun i ↦ (e i).toNonUnitalStarAlgHom)
    (mapNonUnitalStarAlgHom fun i ↦ (e i).symm.toNonUnitalStarAlgHom)
    (by ext; simp) (by ext; simp)

@[simp]
theorem mapStarAlgEquiv_apply (e : ∀ i, A i ≃⋆ₐ[ℂ] B i) (a : lp A ∞) (i : ι) :
    mapStarAlgEquiv e a i = e i (a i) := (rfl)

@[simp]
theorem mapStarAlgEquiv_symm (e : ∀ i, A i ≃⋆ₐ[ℂ] B i) :
    (mapStarAlgEquiv e).symm = mapStarAlgEquiv (fun i ↦ (e i).symm) := (rfl)

end NonUnital

section Unital

variable {ι : Type*} {A B C : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
  [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)]

/-- Coordinatewise application of a family of unital `⋆`-homomorphisms between nonzero unital
C⋆-algebras on bounded products. -/
noncomputable def mapStarAlgHom (φ : ∀ i, A i →⋆ₐ[ℂ] B i) : lp A ∞ →⋆ₐ[ℂ] lp B ∞ where
  __ := mapNonUnitalStarAlgHom fun i ↦ (φ i).toNonUnitalStarAlgHom
  map_one' := by ext i; exact map_one (φ i)
  commutes' c := by ext i; exact (φ i).commutes c

@[simp]
theorem mapStarAlgHom_apply (φ : ∀ i, A i →⋆ₐ[ℂ] B i) (a : lp A ∞) (i : ι) :
    mapStarAlgHom φ a i = φ i (a i) := (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_mapStarAlgHom (φ : ∀ i, A i →⋆ₐ[ℂ] B i) :
    (mapStarAlgHom φ).toNonUnitalStarAlgHom =
      mapNonUnitalStarAlgHom (fun i ↦ (φ i).toNonUnitalStarAlgHom) := (rfl)

@[simp]
theorem mapStarAlgHom_id :
    mapStarAlgHom (fun i ↦ StarAlgHom.id ℂ (A i)) = StarAlgHom.id ℂ (lp A ∞) := by ext; rfl

theorem mapStarAlgHom_comp [∀ i, CStarAlgebra (C i)] [∀ i, Nontrivial (C i)]
    (ψ : ∀ i, B i →⋆ₐ[ℂ] C i) (φ : ∀ i, A i →⋆ₐ[ℂ] B i) :
    (mapStarAlgHom ψ).comp (mapStarAlgHom φ) = mapStarAlgHom (fun i ↦ (ψ i).comp (φ i)) := by
  ext; rfl

end Unital

end Map

end lp

namespace lp

variable {ι : Type*} (A : ι → Type*) [∀ i, CStarAlgebra (A i)]

/-- The quotient `lp A ∞ ⧸ lp.c0Ideal A` of the bounded product of a family of C⋆-algebras by its
`c₀` ideal. For nonzero unital factors it is a unital C⋆-algebra, `lp.QuotientC0.instCStarAlgebra`,
which instance search finds also for concrete families. -/
@[expose] def QuotientC0 : Type _ :=
  lp A ∞ ⧸ c0Ideal A

namespace QuotientC0

variable [∀ i, Nontrivial (A i)]

/-- The quotient of the bounded product of nonzero unital C⋆-algebras by its `c₀` ideal is a
unital C⋆-algebra. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (QuotientC0 A) :=
  TwoSidedIdeal.Quotient.cstarAlgebra (c0Ideal A)

/-- The quotient map `lp A ∞ →⋆ₐ[ℂ] lp.QuotientC0 A`. -/
noncomputable def mk : lp A ∞ →⋆ₐ[ℂ] QuotientC0 A :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (c0Ideal A)

/-- The quotient map sends `a` to its class in `lp A ∞ ⧸ c0Ideal A`. The lemmas below transfer
the quotient API to `lp.QuotientC0 A` through this equation. -/
theorem mk_apply (a : lp A ∞) :
    mk A a = (TwoSidedIdeal.Quotient.mk (c0Ideal A) a : lp A ∞ ⧸ c0Ideal A) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply (c0Ideal A) a

theorem mk_surjective : Function.Surjective (mk A) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_surjective (c0Ideal A)

variable {A}

@[simp]
theorem mk_eq_zero_iff {a : lp A ∞} : mk A a = 0 ↔ a ∈ c0Ideal A := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.eq_zero_iff_mem

theorem mk_eq_mk_iff {a b : lp A ∞} : mk A a = mk A b ↔ a - b ∈ c0Ideal A := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]

variable (A) in
@[simp]
theorem ker_mk : TwoSidedIdeal.ker (mk A) = c0Ideal A :=
  TwoSidedIdeal.Quotient.ker_mkUnitalStarAlgHom (c0Ideal A)

/-- The norm of `lp.QuotientC0 A` is the limit superior of the coordinate norms along the
cofinite filter. For a finite index type both sides are `0`. -/
theorem norm_mk (a : lp A ∞) :
    ‖mk A a‖ = limsup (fun i ↦ ‖a i‖) cofinite := by
  rw [mk_apply]
  exact norm_mk_c0Ideal a

variable {B : Type*} [CStarAlgebra B]

/-- Descend a unital `⋆`-algebra homomorphism `f : lp A ∞ →⋆ₐ[ℂ] B` vanishing on the `c₀` ideal
to `lp.QuotientC0 A →⋆ₐ[ℂ] B`. -/
noncomputable def lift (f : lp A ∞ →⋆ₐ[ℂ] B) (hf : ∀ a ∈ c0Ideal A, f a = 0) :
    QuotientC0 A →⋆ₐ[ℂ] B :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom (c0Ideal A) f hf

@[simp]
theorem lift_mk (f : lp A ∞ →⋆ₐ[ℂ] B) (hf : ∀ a ∈ c0Ideal A, f a = 0) (a : lp A ∞) :
    lift f hf (mk A a) = f a := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.liftUnitalStarAlgHom_mk (c0Ideal A) f hf a

@[simp]
theorem lift_comp_mk (f : lp A ∞ →⋆ₐ[ℂ] B) (hf : ∀ a ∈ c0Ideal A, f a = 0) :
    (lift f hf).comp (mk A) = f :=
  TwoSidedIdeal.Quotient.liftUnitalStarAlgHom_comp_mkUnitalStarAlgHom (c0Ideal A) f hf

/-- Two unital `⋆`-homomorphisms out of `lp.QuotientC0 A` agree when their compositions with
`lp.QuotientC0.mk A` agree. -/
@[ext 1100]
theorem hom_ext ⦃f g : QuotientC0 A →⋆ₐ[ℂ] B⦄ (h : f.comp (mk A) = g.comp (mk A)) : f = g := by
  ext x
  obtain ⟨a, rfl⟩ := mk_surjective A x
  exact DFunLike.congr_fun h a

end QuotientC0

end lp
