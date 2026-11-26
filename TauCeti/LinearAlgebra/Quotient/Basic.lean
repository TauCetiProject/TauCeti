/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Basic facts about quotient modules

A surjective linear map `f : M → M₂` sending `p` into `q` induces a surjective map
`M ⧸ p → M₂ ⧸ q`, and the induced map is injective exactly when `f⁻¹(q) ≤ p`. The quotient by a
submodule is torsion-free exactly when the submodule is saturated, that is, contains every element
of which it contains a multiple by a regular scalar.

## Main results

* `Submodule.mapQ_surjective`: induced maps on quotients preserve surjectivity.
* `Submodule.mapQ_injective_iff`: the map `M ⧸ p → M₂ ⧸ q` induced by `f` is injective exactly
  when `f⁻¹(q) ≤ p`.
* `Submodule.isTorsionFree_quotient_iff`: a submodule has torsion-free quotient if and only if
  it is saturated.
-/

public section

namespace Submodule

variable {R M R₂ M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [Ring R₂] [AddCommGroup M₂]
  [Module R₂ M₂] {τ₁₂ : R →+* R₂} (p : Submodule R M) (q : Submodule R₂ M₂)

/-- Surjectivity of a linear map implies surjectivity of the map it induces on quotients. -/
theorem mapQ_surjective (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) (hf : Function.Surjective f) :
    Function.Surjective (p.mapQ q f h) := by
  rintro ⟨y⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Quotient.mk x, rfl⟩

/-- The map `M ⧸ p → M₂ ⧸ q` induced by `f` is injective exactly when the inverse image of `q`
under `f` lies in `p`. -/
theorem mapQ_injective_iff (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) :
    Function.Injective (p.mapQ q f h) ↔ comap f q ≤ p := by
  rw [← LinearMap.ker_eq_bot, ker_mapQ, ← le_bot_iff, map_le_iff_le_comap, comap_bot, ker_mkQ]

/-- The quotient by a submodule is torsion-free if and only if the submodule contains every
element of which it contains a multiple by a regular scalar. Over a domain the regular scalars
are exactly the nonzero ones, see `isRegular_iff_ne_zero`. -/
theorem isTorsionFree_quotient_iff {S : Submodule R M} :
    Module.IsTorsionFree R (M ⧸ S) ↔ ∀ (c : R) (z : M), IsRegular c → c • z ∈ S → z ∈ S :=
  ⟨fun _ c _ hc ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem S c).mp hc.isSMulRegular _,
    fun hS ↦ ⟨fun c hc ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem S c).mpr (hS c · hc)⟩⟩

end Submodule

namespace LinearMap

open Function Set

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {σ : R →+* R}
  {F : M →ₛₗ[σ] M}

/-- The map induced by a semilinear endomorphism on the quotient of a stable submodule
`P` by its intersection with another stable submodule `Q`. -/
def subquotientMap (F : M →ₛₗ[σ] M) (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    (P ⧸ Q.comap P.subtype) →ₛₗ[σ] (P ⧸ Q.comap P.subtype) :=
  (Q.comap P.subtype).mapQ _ (F.restrict hP) fun x hx ↦ hQ (x := x.val) hx

/-- The stable subquotient map is the quotient map induced by the restriction to its numerator. -/
theorem subquotientMap_eq_mapQ (F : M →ₛₗ[σ] M) (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) :
    F.subquotientMap P Q hP hQ =
      (Q.comap P.subtype).mapQ (Q.comap P.subtype) (F.restrict hP)
        (fun x hx ↦ hQ (x := x.val) hx) :=
  (rfl)

/-- The stable subquotient map sends the class of a vector to the class of its image. -/
@[simp]
theorem subquotientMap_mk (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q) (x : P) :
    F.subquotientMap P Q hP hQ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.restrict hP x) :=
  (rfl)

/-- The induced map on a stable subquotient is bijective if the endomorphism is surjective
on the numerator and reflects membership in the denominator within the numerator. -/
theorem bijective_subquotientMap (P Q : Submodule R M)
    (hP : MapsTo F P P) (hQ : MapsTo F Q Q)
    (hs : SurjOn F P P) (hi : ∀ x ∈ P, F x ∈ Q → x ∈ Q) :
    Bijective (F.subquotientMap P Q hP hQ) := by
  refine ⟨(Submodule.mapQ_injective_iff _ _ _ _).mpr (fun x hx ↦ hi x x.property hx), ?_⟩
  apply Submodule.mapQ_surjective
  intro x
  obtain ⟨z, hz, hzx⟩ := hs x.property
  exact ⟨⟨z, hz⟩, Subtype.ext hzx⟩

end LinearMap

namespace TauCeti

open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Multiplication by `a^i` induces a map from `M / aM` to `a^i M / a^{i+1} M`. -/
noncomputable def smulPowQuotientMap (a : A) (i : ℕ) :
    M ⧸ (a • (⊤ : Submodule A M)) →ₗ[A]
      ((a ^ i • (⊤ : Submodule A M) : Submodule A M) ⧸
        (a ^ (i + 1) • (⊤ : Submodule A M)).comap (a ^ i • (⊤ : Submodule A M)).subtype) := by
  let f := (DistribSMul.toLinearMap A M (a ^ i)).codRestrict (a ^ i • ⊤) fun x ↦
    Submodule.smul_mem_pointwise_smul x _ _ Submodule.mem_top
  refine (a • (⊤ : Submodule A M)).mapQ _ f ?_
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have hmem : a ^ i • (a • y) ∈ a ^ (i + 1) • (⊤ : Submodule A M) := by
    rw [← mul_smul, pow_succ]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  exact hmem

/-- On a quotient class, `smulPowQuotientMap` multiplies its representative by `a^i`. -/
@[simp]
theorem smulPowQuotientMap_mk (a : A) (i : ℕ) (x : M) :
    smulPowQuotientMap a i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨a ^ i • x, Submodule.smul_mem_pointwise_smul x _ _ Submodule.mem_top⟩ :
          (a ^ i • ⊤ : Submodule A M)) :=
  (rfl)

/-- Every class in `a^i M / a^{i+1} M` comes from multiplication by `a^i` on `M / aM`. -/
theorem smulPowQuotientMap_surjective (a : A) (i : ℕ) :
    Function.Surjective (smulPowQuotientMap (M := M) a i) := by
  unfold smulPowQuotientMap
  apply Submodule.mapQ_surjective
  intro y
  obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp y.property
  exact ⟨x, Subtype.ext hx⟩

end TauCeti
