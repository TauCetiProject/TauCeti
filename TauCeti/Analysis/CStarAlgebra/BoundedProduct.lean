/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.lpSpace

/-!
# Bounded products of C⋆-algebras

For a family of nonzero unital C⋆-algebras `A i`, the bounded product `lp A ∞` is a unital
C⋆-algebra (`lp.inftyCStarAlgebra`). Mathlib provides the nonunital instance and the unital
commutative one; nontriviality of the factors makes the unit `(1)ᵢ` have norm one. With the closed
filter-null ideals `lp.nullIdeal` and `lp.c0Ideal` of `TauCeti.Analysis.Normed.Lp.C0Ideal`, the
quotient `lp A ∞ ⧸ lp.nullIdeal A l` is then a C⋆-algebra (unital when the factors are nonzero
unital C⋆-algebras) by `TwoSidedIdeal.Quotient.nonUnitalCStarAlgebra` and
`TwoSidedIdeal.Quotient.cstarAlgebra`.

We also record the coordinatewise characterizations of self-adjoint elements, idempotents, star
projections, and unitaries (`lp.isSelfAdjoint_iff`, `lp.isStarProjection_iff`, `lp.unitaryEquiv`),
together with the diagonal (`lp.constNonUnitalStarAlgHom`, `lp.constStarAlgHom`), coordinatewise
functorial (`lp.mapNonUnitalStarAlgHom`, `lp.mapStarAlgHom`, `lp.mapStarAlgEquiv`), and reindexing
(`lp.reindexNonUnitalStarAlgHom`, `lp.reindexStarAlgHom`) `⋆`-homomorphisms on `lp _ ∞`.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.
-/

public section

open scoped ENNReal

noncomputable section

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

section CStarAlgebra

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The bounded product `lp A ∞` of nonzero unital C⋆-algebras is a unital C⋆-algebra. -/
instance inftyCStarAlgebra : CStarAlgebra (lp A ∞) where

end CStarAlgebra

section Elements

variable {ι : Type*} {A : ι → Type*}

/-- An element of `lp A p` is self-adjoint if and only if each coordinate is self-adjoint. -/
@[simp]
theorem isSelfAdjoint_iff {p : ℝ≥0∞} [∀ i, NormedAddCommGroup (A i)] [∀ i, StarAddMonoid (A i)]
    [∀ i, NormedStarGroup (A i)] {a : lp A p} :
    IsSelfAdjoint a ↔ ∀ i, IsSelfAdjoint (a i) :=
  ⟨fun h i ↦ by
    simpa only [IsSelfAdjoint, lp.star_apply] using congrArg (fun x : lp A p ↦ x i) h.star_eq,
   fun h ↦ lp.ext (funext fun i ↦ by simpa only [lp.star_apply] using (h i).star_eq)⟩

section NonUnital

variable [∀ i, NonUnitalNormedRing (A i)]

/-- An element of `lp A ∞` is idempotent if and only if each coordinate is idempotent. -/
@[simp]
theorem isIdempotentElem_iff {a : lp A ∞} : IsIdempotentElem a ↔ ∀ i, IsIdempotentElem (a i) :=
  ⟨fun h i ↦ by
    simpa only [IsIdempotentElem, lp.infty_coeFn_mul, Pi.mul_apply] using
      congrArg (fun x : lp A ∞ ↦ x i) h.eq,
   fun h ↦ lp.ext (funext fun i ↦ by simpa only [lp.infty_coeFn_mul, Pi.mul_apply] using (h i).eq)⟩

variable [∀ i, StarAddMonoid (A i)] [∀ i, NormedStarGroup (A i)]

/-- An element of `lp A ∞` is a star projection if and only if each coordinate is a star
projection. -/
@[simp]
theorem isStarProjection_iff {a : lp A ∞} : IsStarProjection a ↔ ∀ i, IsStarProjection (a i) :=
  ⟨fun h i ↦ ⟨isIdempotentElem_iff.1 h.isIdempotentElem i, isSelfAdjoint_iff.1 h.isSelfAdjoint i⟩,
   fun h ↦ ⟨isIdempotentElem_iff.2 fun i ↦ (h i).isIdempotentElem,
     isSelfAdjoint_iff.2 fun i ↦ (h i).isSelfAdjoint⟩⟩

end NonUnital

section Unitary

variable [∀ i, NormedRing (A i)] [∀ i, StarRing (A i)] [∀ i, CStarRing (A i)]
  [∀ i, NormOneClass (A i)]

/-- The unitary group of `lp A ∞` is canonically isomorphic to the product `∀ i, unitary (A i)` of
the coordinate unitary groups. -/
def unitaryEquiv : unitary (lp A ∞) ≃* ∀ i, unitary (A i) where
  toFun U i :=
    ⟨(U : lp A ∞) i, Unitary.mem_iff.2
      ⟨by
        simpa only [lp.infty_coeFn_one, Pi.one_apply, lp.infty_coeFn_mul, Pi.mul_apply,
          lp.star_apply] using congrArg (fun x : lp A ∞ ↦ x i) (Unitary.coe_star_mul_self U),
       by
        simpa only [Unitary.coe_star, lp.infty_coeFn_one, Pi.one_apply, lp.infty_coeFn_mul,
          Pi.mul_apply, lp.star_apply] using
          congrArg (fun x : lp A ∞ ↦ x i) (Unitary.coe_mul_star_self U)⟩⟩
  invFun u :=
    ⟨⟨fun i ↦ (u i : A i), TauCeti.memℓp_infty_unitary u⟩, Unitary.mem_iff.2
      ⟨by
        ext i
        simpa only [lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, lp.infty_coeFn_one,
          Pi.one_apply] using Unitary.coe_star_mul_self (u i),
       by
        ext i
        simpa only [Unitary.coe_star, lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply,
          lp.infty_coeFn_one, Pi.one_apply] using Unitary.coe_mul_star_self (u i)⟩⟩
  left_inv U := by ext i; rfl
  right_inv u := by ext i; rfl
  map_mul' U V := by ext i; rfl

@[simp]
theorem coe_unitaryEquiv_apply (U : unitary (lp A ∞)) (i : ι) :
    (unitaryEquiv U i : A i) = (U : lp A ∞) i :=
  (rfl)

@[simp]
theorem coe_unitaryEquiv_symm_apply (u : ∀ i, unitary (A i)) (i : ι) :
    (unitaryEquiv.symm u : lp A ∞) i = (u i : A i) :=
  (rfl)

end Unitary

end Elements

section Hom

section Const

/-- The constant (diagonal) non-unital `⋆`-algebra homomorphism `A →⋆ₙₐ[𝕜] lp (fun _ : ι ↦ A) ∞`
sending `a` to the constant family `fun _ ↦ a`. -/
def constNonUnitalStarAlgHom (𝕜 ι A : Type*) [NormedRing 𝕜] [NonUnitalNormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A] :
    A →⋆ₙₐ[𝕜] lp (fun _ : ι ↦ A) ∞ where
  toFun a := ⟨fun _ ↦ a, memℓp_infty ⟨‖a‖, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩⟩
  map_smul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_star' _ := by ext; rfl

@[simp]
theorem constNonUnitalStarAlgHom_apply {𝕜 ι A : Type*} [NormedRing 𝕜] [NonUnitalNormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A] (a : A) (i : ι) :
    constNonUnitalStarAlgHom 𝕜 ι A a i = a :=
  (rfl)

/-- The constant non-unital `⋆`-algebra homomorphism into `lp (fun _ : ι ↦ A) ∞` is contractive. -/
theorem norm_constNonUnitalStarAlgHom_le {𝕜 ι A : Type*} [NormedRing 𝕜] [NonUnitalNormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A] (a : A) :
    ‖constNonUnitalStarAlgHom 𝕜 ι A a‖ ≤ ‖a‖ :=
  norm_le_of_forall_le (norm_nonneg a) fun _ ↦ le_rfl

/-- Over a nonempty index type, `lp.constNonUnitalStarAlgHom` preserves norms. -/
@[simp]
theorem norm_constNonUnitalStarAlgHom {𝕜 ι A : Type*} [NormedRing 𝕜] [NonUnitalNormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A] [Nonempty ι] (a : A) :
    ‖constNonUnitalStarAlgHom 𝕜 ι A a‖ = ‖a‖ := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact le_antisymm (norm_constNonUnitalStarAlgHom_le (𝕜 := 𝕜) (ι := ι) a)
    (norm_apply_le_norm ENNReal.top_ne_zero (constNonUnitalStarAlgHom 𝕜 ι A a) i₀)

/-- Over a nonempty index type, `lp.constNonUnitalStarAlgHom` is an isometry. -/
theorem isometry_constNonUnitalStarAlgHom {𝕜 ι A : Type*} [NormedRing 𝕜] [NonUnitalNormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A] [Nonempty ι] :
    Isometry (constNonUnitalStarAlgHom 𝕜 ι A) :=
  AddMonoidHomClass.isometry_of_norm _ norm_constNonUnitalStarAlgHom

/-- The constant (diagonal) unital `⋆`-algebra homomorphism `A →⋆ₐ[𝕜] lp (fun _ : ι ↦ A) ∞` on a
normed `⋆`-algebra with `‖(1 : A)‖ = 1`. -/
def constStarAlgHom (𝕜 ι A : Type*) [NormedField 𝕜] [NormedRing A] [StarAddMonoid A]
    [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A] :
    A →⋆ₐ[𝕜] lp (fun _ : ι ↦ A) ∞ where
  __ := constNonUnitalStarAlgHom 𝕜 ι A
  map_one' := by ext; rfl
  commutes' _ := by ext; rfl

@[simp]
theorem constStarAlgHom_apply {𝕜 ι A : Type*} [NormedField 𝕜] [NormedRing A] [StarAddMonoid A]
    [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A] (a : A) (i : ι) :
    constStarAlgHom 𝕜 ι A a i = a :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_constStarAlgHom {𝕜 ι A : Type*} [NormedField 𝕜]
    [NormedRing A] [StarAddMonoid A] [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A] :
    (constStarAlgHom 𝕜 ι A).toNonUnitalStarAlgHom = constNonUnitalStarAlgHom 𝕜 ι A :=
  (rfl)

end Const

section Map

variable {ι : Type*} {A B C : ι → Type*}

/-- Coordinatewise application of a family of non-unital `⋆`-homomorphisms between C⋆-algebras on
bounded products. No uniform norm hypothesis is needed because every `⋆`-homomorphism between
C⋆-algebras is automatically contractive. -/
def mapNonUnitalStarAlgHom [∀ i, NonUnitalCStarAlgebra (A i)] [∀ i, NonUnitalCStarAlgebra (B i)]
    (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) : lp A ∞ →⋆ₙₐ[ℂ] lp B ∞ where
  toFun a :=
    ⟨fun i ↦ φ i (a i), memℓp_infty ⟨‖a‖, by
      rintro _ ⟨i, rfl⟩
      exact (NonUnitalStarAlgHom.norm_apply_le (φ i) (a i)).trans
        (norm_apply_le_norm ENNReal.top_ne_zero a i)⟩⟩
  map_smul' c a := by ext i; exact map_smul (φ i) c (a i)
  map_zero' := by ext i; exact map_zero (φ i)
  map_add' a b := by ext i; exact map_add (φ i) (a i) (b i)
  map_mul' a b := by ext i; exact map_mul (φ i) (a i) (b i)
  map_star' a := by ext i; exact map_star (φ i) (a i)

@[simp]
theorem mapNonUnitalStarAlgHom_apply [∀ i, NonUnitalCStarAlgebra (A i)]
    [∀ i, NonUnitalCStarAlgebra (B i)] (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) (a : lp A ∞) (i : ι) :
    mapNonUnitalStarAlgHom φ a i = φ i (a i) :=
  (rfl)

@[simp]
theorem mapNonUnitalStarAlgHom_id [∀ i, NonUnitalCStarAlgebra (A i)] :
    mapNonUnitalStarAlgHom (fun i ↦ NonUnitalStarAlgHom.id ℂ (A i)) =
      NonUnitalStarAlgHom.id ℂ (lp A ∞) := by
  ext a i
  rfl

theorem mapNonUnitalStarAlgHom_comp [∀ i, NonUnitalCStarAlgebra (A i)]
    [∀ i, NonUnitalCStarAlgebra (B i)] [∀ i, NonUnitalCStarAlgebra (C i)]
    (ψ : ∀ i, B i →⋆ₙₐ[ℂ] C i) (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i) :
    (mapNonUnitalStarAlgHom ψ).comp (mapNonUnitalStarAlgHom φ) =
      mapNonUnitalStarAlgHom (fun i ↦ (ψ i).comp (φ i)) := by
  ext a i
  rfl

/-- If each coordinate `⋆`-homomorphism `φ i` is injective, then `lp.mapNonUnitalStarAlgHom φ` is
an isometry. -/
theorem isometry_mapNonUnitalStarAlgHom [∀ i, NonUnitalCStarAlgebra (A i)]
    [∀ i, NonUnitalCStarAlgebra (B i)] {φ : ∀ i, A i →⋆ₙₐ[ℂ] B i}
    (hφ : ∀ i, Function.Injective (φ i)) : Isometry (mapNonUnitalStarAlgHom φ) := by
  refine NonUnitalStarAlgHom.isometry (mapNonUnitalStarAlgHom φ)
    fun a b hab ↦ lp.ext (funext fun i ↦ ?_)
  exact hφ i (congrArg (fun x : lp B ∞ ↦ x i) hab)

/-- Coordinatewise application of a family of unital `⋆`-homomorphisms between nonzero unital
C⋆-algebras on bounded products. -/
def mapStarAlgHom [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
    [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)] (φ : ∀ i, A i →⋆ₐ[ℂ] B i) :
    lp A ∞ →⋆ₐ[ℂ] lp B ∞ where
  __ := mapNonUnitalStarAlgHom fun i ↦ (φ i).toNonUnitalStarAlgHom
  map_one' := by ext i; exact map_one (φ i)
  commutes' c := by ext i; exact (φ i).commutes c

@[simp]
theorem mapStarAlgHom_apply [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
    [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)] (φ : ∀ i, A i →⋆ₐ[ℂ] B i) (a : lp A ∞)
    (i : ι) : mapStarAlgHom φ a i = φ i (a i) :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_mapStarAlgHom [∀ i, CStarAlgebra (A i)]
    [∀ i, Nontrivial (A i)] [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)]
    (φ : ∀ i, A i →⋆ₐ[ℂ] B i) :
    (mapStarAlgHom φ).toNonUnitalStarAlgHom =
      mapNonUnitalStarAlgHom (fun i ↦ (φ i).toNonUnitalStarAlgHom) :=
  (rfl)

@[simp]
theorem mapStarAlgHom_id [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] :
    mapStarAlgHom (fun i ↦ StarAlgHom.id ℂ (A i)) = StarAlgHom.id ℂ (lp A ∞) := by
  ext a i
  rfl

theorem mapStarAlgHom_comp [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
    [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)] [∀ i, CStarAlgebra (C i)]
    [∀ i, Nontrivial (C i)] (ψ : ∀ i, B i →⋆ₐ[ℂ] C i) (φ : ∀ i, A i →⋆ₐ[ℂ] B i) :
    (mapStarAlgHom ψ).comp (mapStarAlgHom φ) = mapStarAlgHom (fun i ↦ (ψ i).comp (φ i)) := by
  ext a i
  rfl

/-- Coordinatewise `⋆`-isomorphism of bounded products induced by a family of `⋆`-isomorphisms of
C⋆-algebras. -/
def mapStarAlgEquiv [∀ i, NonUnitalCStarAlgebra (A i)] [∀ i, NonUnitalCStarAlgebra (B i)]
    (e : ∀ i, A i ≃⋆ₐ[ℂ] B i) : lp A ∞ ≃⋆ₐ[ℂ] lp B ∞ :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    (mapNonUnitalStarAlgHom fun i ↦ (e i).toNonUnitalStarAlgHom)
    (mapNonUnitalStarAlgHom fun i ↦ (e i).symm.toNonUnitalStarAlgHom)
    (by ext a i; exact (e i).symm_apply_apply (a i))
    (by ext b i; exact (e i).apply_symm_apply (b i))

@[simp]
theorem mapStarAlgEquiv_apply [∀ i, NonUnitalCStarAlgebra (A i)]
    [∀ i, NonUnitalCStarAlgebra (B i)] (e : ∀ i, A i ≃⋆ₐ[ℂ] B i) (a : lp A ∞) (i : ι) :
    mapStarAlgEquiv e a i = e i (a i) :=
  (rfl)

@[simp]
theorem mapStarAlgEquiv_symm [∀ i, NonUnitalCStarAlgebra (A i)]
    [∀ i, NonUnitalCStarAlgebra (B i)] (e : ∀ i, A i ≃⋆ₐ[ℂ] B i) :
    (mapStarAlgEquiv e).symm = mapStarAlgEquiv (fun i ↦ (e i).symm) :=
  (rfl)

end Map

section Reindex

/-- Reindexing `a ↦ a ∘ r` as a non-unital `⋆`-algebra homomorphism on bounded sequence spaces. -/
def reindexNonUnitalStarAlgHom (𝕜 : Type*) {ι ι' : Type*} (A : Type*) [NormedRing 𝕜]
    [NonUnitalNormedRing A] [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A]
    (r : ι' → ι) : lp (fun _ : ι ↦ A) ∞ →⋆ₙₐ[𝕜] lp (fun _ : ι' ↦ A) ∞ where
  toFun a :=
    ⟨fun j ↦ a (r j), memℓp_infty
      ⟨‖a‖, by rintro _ ⟨j, rfl⟩; exact norm_apply_le_norm ENNReal.top_ne_zero a (r j)⟩⟩
  map_smul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_star' _ := by ext; rfl

@[simp]
theorem reindexNonUnitalStarAlgHom_apply {𝕜 ι ι' A : Type*} [NormedRing 𝕜] [NonUnitalNormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A] (r : ι' → ι)
    (a : lp (fun _ : ι ↦ A) ∞) (j : ι') : reindexNonUnitalStarAlgHom 𝕜 A r a j = a (r j) :=
  (rfl)

@[simp]
theorem reindexNonUnitalStarAlgHom_id {𝕜 ι A : Type*} [NormedRing 𝕜] [NonUnitalNormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A] :
    reindexNonUnitalStarAlgHom 𝕜 A (id : ι → ι) =
      NonUnitalStarAlgHom.id 𝕜 (lp (fun _ : ι ↦ A) ∞) := by
  ext a i
  rfl

theorem reindexNonUnitalStarAlgHom_comp {𝕜 ι ι' ι'' A : Type*} [NormedRing 𝕜]
    [NonUnitalNormedRing A] [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A]
    (s : ι'' → ι') (r : ι' → ι) :
    (reindexNonUnitalStarAlgHom 𝕜 A s).comp (reindexNonUnitalStarAlgHom 𝕜 A r) =
      reindexNonUnitalStarAlgHom 𝕜 A (r ∘ s) := by
  ext a k
  rfl

@[simp]
theorem reindexNonUnitalStarAlgHom_comp_constNonUnitalStarAlgHom {𝕜 ι ι' A : Type*} [NormedRing 𝕜]
    [NonUnitalNormedRing A] [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A]
    (r : ι' → ι) :
    (reindexNonUnitalStarAlgHom 𝕜 A r).comp (constNonUnitalStarAlgHom 𝕜 ι A) =
      constNonUnitalStarAlgHom 𝕜 ι' A := by
  ext; rfl

/-- Reindexing bounded sequences along any map `r : ι' → ι` is contractive. -/
theorem norm_reindexNonUnitalStarAlgHom_le {𝕜 ι ι' A : Type*} [NormedRing 𝕜]
    [NonUnitalNormedRing A] [StarAddMonoid A] [NormedStarGroup A] [Module 𝕜 A] [IsBoundedSMul 𝕜 A]
    (r : ι' → ι) (a : lp (fun _ : ι ↦ A) ∞) : ‖reindexNonUnitalStarAlgHom 𝕜 A r a‖ ≤ ‖a‖ :=
  norm_le_of_forall_le (norm_nonneg a) fun j ↦ norm_apply_le_norm ENNReal.top_ne_zero a (r j)

/-- Reindexing `a ↦ a ∘ r` as a unital `⋆`-algebra homomorphism on bounded sequence spaces of a
normed `⋆`-algebra with `‖(1 : A)‖ = 1`. -/
def reindexStarAlgHom (𝕜 : Type*) {ι ι' : Type*} (A : Type*) [NormedField 𝕜] [NormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A] (r : ι' → ι) :
    lp (fun _ : ι ↦ A) ∞ →⋆ₐ[𝕜] lp (fun _ : ι' ↦ A) ∞ where
  __ := reindexNonUnitalStarAlgHom 𝕜 A r
  map_one' := by ext; rfl
  commutes' _ := by ext; rfl

@[simp]
theorem reindexStarAlgHom_apply {𝕜 ι ι' A : Type*} [NormedField 𝕜] [NormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A] (r : ι' → ι)
    (a : lp (fun _ : ι ↦ A) ∞) (j : ι') : reindexStarAlgHom 𝕜 A r a j = a (r j) :=
  (rfl)

@[simp]
theorem toNonUnitalStarAlgHom_reindexStarAlgHom {𝕜 ι ι' A : Type*} [NormedField 𝕜]
    [NormedRing A] [StarAddMonoid A] [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A]
    (r : ι' → ι) :
    (reindexStarAlgHom 𝕜 A r).toNonUnitalStarAlgHom = reindexNonUnitalStarAlgHom 𝕜 A r :=
  (rfl)

@[simp]
theorem reindexStarAlgHom_id {𝕜 ι A : Type*} [NormedField 𝕜] [NormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A] :
    reindexStarAlgHom 𝕜 A (id : ι → ι) = StarAlgHom.id 𝕜 (lp (fun _ : ι ↦ A) ∞) := by
  ext a i
  rfl

theorem reindexStarAlgHom_comp {𝕜 ι ι' ι'' A : Type*} [NormedField 𝕜] [NormedRing A]
    [StarAddMonoid A] [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A]
    (s : ι'' → ι') (r : ι' → ι) :
    (reindexStarAlgHom 𝕜 A s).comp (reindexStarAlgHom 𝕜 A r) =
      reindexStarAlgHom 𝕜 A (r ∘ s) := by
  ext a k
  rfl

@[simp]
theorem reindexStarAlgHom_comp_constStarAlgHom {𝕜 ι ι' A : Type*} [NormedField 𝕜]
    [NormedRing A] [StarAddMonoid A] [NormedStarGroup A] [NormOneClass A] [NormedAlgebra 𝕜 A]
    (r : ι' → ι) :
    (reindexStarAlgHom 𝕜 A r).comp (constStarAlgHom 𝕜 ι A) = constStarAlgHom 𝕜 ι' A := by
  ext; rfl

end Reindex

end Hom

end lp

end
