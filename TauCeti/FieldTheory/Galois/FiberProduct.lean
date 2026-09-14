/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.FixedField

/-!
# Galois groups of composita as fibre products

Let `E/F` be a finite Galois extension and let `K₁`, `K₂` be normal subextensions. Restricting
automorphisms of `E` gives a homomorphism `Gal(E/F) → Gal(K₁/F) × Gal(K₂/F)`. This file
identifies its image: a pair `(σ₁, σ₂)` comes from an automorphism of `E` exactly when `σ₁` and
`σ₂` agree on the elements that `K₁` and `K₂` have in common inside `E`. Consequently the map
is surjective exactly when `K₁` and `K₂` meet only in `F`.

For two finite Galois intermediate fields `K` and `L`, Mathlib's
`IntermediateField.restrictNormalHomSupProd` embeds the automorphism group of the compositum
`K ⊔ L` into `Gal(K/F) × Gal(L/F)`. Its range consists of the pairs with equal restrictions to
`K ⊓ L`, so `Gal(K ⊔ L / F)` is the fibre product `Gal(K/F) ×_{Gal(K ⊓ L / F)} Gal(L/F)`.

To name those restriction maps, `AlgHom.restrictNormalHom` restricts automorphisms along an
arbitrary embedding `f : M →ₐ[F] K` of a normal extension, generalizing Mathlib's
`AlgEquiv.restrictNormalHom`, which restricts along the algebra map of a scalar tower.

## Main definitions and results

* `AlgHom.restrictNormalHom`: restriction `Gal(K/F) →* Gal(M/F)` along `f : M →ₐ[F] K`.
* `AlgEquiv.mem_range_prod_restrictNormalHom_iff`: a pair of automorphisms of two normal
  subextensions of a finite Galois extension extends to the whole extension iff it agrees on
  common elements.
* `AlgEquiv.prod_restrictNormalHom_surjective_iff`: the joint restriction map is surjective iff
  the two subextensions meet in `F`.
* `IntermediateField.mem_range_restrictNormalHomSupProd_iff`: the Galois group of a compositum of
  two finite Galois intermediate fields is the fibre product over their intersection.

## References

* S. Lang, *Algebra*, Chapter VI, §1.
-/

public section

namespace TauCeti

open IntermediateField

section RestrictAlong

variable {F K M : Type*} [Field F] [Field K] [Field M] [Algebra F K] [Algebra F M]

/-- Restriction of automorphisms along an embedding `f : M →ₐ[F] K` of a normal extension `M/F`.
Every `σ : Gal(K/F)` maps the image of `f` to itself, and `f.restrictNormalHom σ` is the
automorphism of `M` it induces, so that `f (f.restrictNormalHom σ x) = σ (f x)`
(`AlgHom.restrictNormalHom_commutes`). For the algebra map of a scalar tower this is
`AlgEquiv.restrictNormalHom` (`AlgHom.restrictNormalHom_toAlgHom`). -/
noncomputable def _root_.AlgHom.restrictNormalHom (f : M →ₐ[F] K) [Normal F M] :
    Gal(K/F) →* Gal(M/F) :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormalHom M

@[simp]
theorem _root_.AlgHom.restrictNormalHom_commutes (f : M →ₐ[F] K) [Normal F M] (σ : Gal(K/F))
    (x : M) : f (f.restrictNormalHom σ x) = σ (f x) :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower F M K := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  AlgEquiv.restrictNormal_commutes σ M x

/-- `f.restrictNormalHom σ` is the unique automorphism of `M` intertwined with `σ` by `f`. -/
theorem _root_.AlgHom.restrictNormalHom_eq_iff (f : M →ₐ[F] K) [Normal F M] {σ : Gal(K/F)}
    {τ : Gal(M/F)} : f.restrictNormalHom σ = τ ↔ ∀ x, σ (f x) = f (τ x) := by
  refine ⟨fun h x ↦ by rw [← h, AlgHom.restrictNormalHom_commutes], fun h ↦ ?_⟩
  ext x
  exact f.injective ((f.restrictNormalHom_commutes σ x).trans (h x))

/-- For the algebra map of a scalar tower, restriction along it is Mathlib's
`AlgEquiv.restrictNormalHom`. -/
@[simp]
theorem _root_.AlgHom.restrictNormalHom_toAlgHom [Algebra M K] [IsScalarTower F M K]
    [Normal F M] :
    (IsScalarTower.toAlgHom F M K).restrictNormalHom = AlgEquiv.restrictNormalHom M :=
  MonoidHom.ext fun σ ↦ (IsScalarTower.toAlgHom F M K).restrictNormalHom_eq_iff.2
    fun y ↦ (AlgEquiv.restrictNormal_commutes σ M y).symm

end RestrictAlong

section FiberProduct

variable {F E K₁ K₂ : Type*} [Field F] [Field E] [Field K₁] [Field K₂]
  [Algebra F E] [Algebra F K₁] [Algebra F K₂] [Algebra K₁ E] [Algebra K₂ E]
  [IsScalarTower F K₁ E] [IsScalarTower F K₂ E] [Normal F K₁] [Normal F K₂]

/-- **Galois groups of composita as fibre products.** In a finite Galois extension `E/F` with
normal subextensions `K₁` and `K₂`, a pair `(σ₁, σ₂)` of automorphisms is the restriction of a
single automorphism of `E` if and only if `σ₁` and `σ₂` agree on the elements common to `K₁` and
`K₂` inside `E`. -/
theorem _root_.AlgEquiv.mem_range_prod_restrictNormalHom_iff [FiniteDimensional F E]
    [IsGalois F E] (σ₁ : Gal(K₁/F)) (σ₂ : Gal(K₂/F)) :
    (σ₁, σ₂) ∈ ((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) K₁).prod
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) K₂)).range ↔
      ∀ x₁ x₂, algebraMap K₁ E x₁ = algebraMap K₂ E x₂ →
        algebraMap K₁ E (σ₁ x₁) = algebraMap K₂ E (σ₂ x₂) := by
  constructor
  · rintro ⟨g, hg⟩ x₁ x₂ hx
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hg
    simpa only [MonoidHom.prod_apply, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
      AlgEquiv.restrictNormal_commutes] using congrArg g hx
  intro h
  obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K₁) E σ₁
  obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K₂) E σ₂
  -- `a⁻¹ * b` fixes the common part of `K₁` and `K₂`, so it factors through the two kernels.
  have hab : a⁻¹ * b ∈ (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) K₁).ker ⊔
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) K₂).ker := by
    rw [AlgEquiv.ker_restrictNormalHom, AlgEquiv.ker_restrictNormalHom, ← fixingSubgroup_inf,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    simp only [IntermediateField.mem_inf, AlgHom.mem_fieldRange, IsScalarTower.coe_toAlgHom'] at hx
    obtain ⟨⟨x₁, rfl⟩, ⟨x₂, hx⟩⟩ := hx
    have hb : b (algebraMap K₂ E x₂) = a (algebraMap K₁ E x₁) := by
      simpa only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
        AlgEquiv.restrictNormal_commutes] using (h _ _ hx.symm).symm
    calc (a⁻¹ * b) (algebraMap K₁ E x₁) = a⁻¹ (b (algebraMap K₂ E x₂)) := by
          rw [AlgEquiv.mul_apply, hx]
      _ = algebraMap K₁ E x₁ := by rw [hb, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hab
  refine ⟨a * y, Prod.ext ?_ ?_⟩
  · simp [(MonoidHom.mem_ker).1 hy]
  · have hyz' : a * y = b * z⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hyz, mul_inv_cancel_left]
    rw [hyz']
    simp [(MonoidHom.mem_ker).1 hz]

/-- The joint restriction map to two normal subextensions of a finite Galois extension is surjective
if and only if the two subextensions meet only in the base field. -/
theorem _root_.AlgEquiv.prod_restrictNormalHom_surjective_iff [FiniteDimensional F E]
    [IsGalois F E] :
    Function.Surjective ((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) K₁).prod
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) K₂)) ↔
      (IsScalarTower.toAlgHom F K₁ E).fieldRange ⊓ (IsScalarTower.toAlgHom F K₂ E).fieldRange =
        ⊥ := by
  rw [← MonoidHom.range_eq_top]
  constructor
  · intro htop
    refine eq_bot_iff.2 ?_
    intro x hx
    simp only [IntermediateField.mem_inf, AlgHom.mem_fieldRange, IsScalarTower.coe_toAlgHom'] at hx
    obtain ⟨⟨x₁, rfl⟩, ⟨x₂, hx⟩⟩ := hx
    -- The restriction of any `g` to `K₁` pairs with the identity of `K₂`, so `g` fixes the element.
    refine (IsGalois.mem_bot_iff_fixed _).2 fun g ↦ ?_
    have hg := (AlgEquiv.mem_range_prod_restrictNormalHom_iff
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) K₁ g) 1).1
        (htop ▸ Subgroup.mem_top _) x₁ x₂ hx.symm
    simpa only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
      AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply, hx] using hg
  · intro hbot
    refine eq_top_iff.2 fun ⟨σ₁, σ₂⟩ _ ↦ ?_
    refine (AlgEquiv.mem_range_prod_restrictNormalHom_iff σ₁ σ₂).2 fun x₁ x₂ hx ↦ ?_
    have hmem : algebraMap K₁ E x₁ ∈ (⊥ : IntermediateField F E) :=
      hbot ▸ ⟨⟨x₁, rfl⟩, ⟨x₂, hx.symm⟩⟩
    obtain ⟨c, hc⟩ := mem_bot.1 hmem
    have h₁ : x₁ = algebraMap F K₁ c :=
      (algebraMap K₁ E).injective (by rw [← hc, IsScalarTower.algebraMap_apply F K₁ E])
    have h₂ : x₂ = algebraMap F K₂ c :=
      (algebraMap K₂ E).injective (by rw [← hx, ← hc, IsScalarTower.algebraMap_apply F K₂ E])
    rw [h₁, h₂, AlgEquiv.commutes, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

end FiberProduct

section Compositum

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (K L : IntermediateField F E)
  [IsGalois F K] [IsGalois F L] [FiniteDimensional F K] [FiniteDimensional F L]

/-- **The Galois group of a compositum is a fibre product.** For finite Galois intermediate fields
`K` and `L`, the image of `Gal(K ⊔ L / F)` in `Gal(K/F) × Gal(L/F)` under
`IntermediateField.restrictNormalHomSupProd` consists of the pairs whose restrictions to `K ⊓ L`
agree. Since `restrictNormalHomSupProd` is injective, `Gal(K ⊔ L / F)` is the fibre product
`Gal(K/F) ×_{Gal(K ⊓ L / F)} Gal(L/F)`. -/
theorem _root_.IntermediateField.mem_range_restrictNormalHomSupProd_iff (σ : Gal(K/F))
    (τ : Gal(L/F)) :
    (σ, τ) ∈ (restrictNormalHomSupProd K L).range ↔
      (inclusion (inf_le_left : K ⊓ L ≤ K)).restrictNormalHom σ =
        (inclusion (inf_le_right : K ⊓ L ≤ L)).restrictNormalHom τ := by
  let : Algebra K ↑(K ⊔ L) := (inclusion le_sup_left).toAlgebra
  let : Algebra L ↑(K ⊔ L) := (inclusion le_sup_right).toAlgebra
  have : IsGalois F ↑(K ⊔ L) := ⟨⟩
  -- `restrictNormalHomSupProd K L` is the joint restriction map for the compositum `K ⊔ L`.
  refine (AlgEquiv.mem_range_prod_restrictNormalHom_iff σ τ).trans ?_
  have key₁ (x : ↥(K ⊓ L)) :
      (((inclusion (inf_le_left : K ⊓ L ≤ K)).restrictNormalHom σ x : ↥(K ⊓ L)) : E) =
        (σ (inclusion inf_le_left x) : E) :=
    congrArg Subtype.val ((inclusion (inf_le_left : K ⊓ L ≤ K)).restrictNormalHom_commutes σ x)
  have key₂ (x : ↥(K ⊓ L)) :
      (((inclusion (inf_le_right : K ⊓ L ≤ L)).restrictNormalHom τ x : ↥(K ⊓ L)) : E) =
        (τ (inclusion inf_le_right x) : E) :=
    congrArg Subtype.val ((inclusion (inf_le_right : K ⊓ L ≤ L)).restrictNormalHom_commutes τ x)
  constructor
  · intro h
    ext x
    rw [key₁, key₂]
    exact congrArg Subtype.val (h _ _ rfl)
  · intro h x₁ x₂ hx
    have hx' : (x₁ : E) = x₂ := congrArg Subtype.val hx
    -- `x₁` and `x₂` are the same element of `K ⊓ L`, seen in `K` and in `L`.
    let m : ↥(K ⊓ L) := ⟨x₁, x₁.2, hx' ▸ x₂.2⟩
    have hm₂ : inclusion (inf_le_right : K ⊓ L ≤ L) m = x₂ := Subtype.ext hx'
    have hm := key₁ m
    rw [h, key₂, hm₂] at hm
    exact Subtype.ext hm.symm

end Compositum

end TauCeti
