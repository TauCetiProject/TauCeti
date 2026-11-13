/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.Ideal.LeftIdealSMul
public import TauCeti.RingTheory.Idempotents.Module
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Corners of the first radical layer

For a two-sided ideal `J` of a `k`-algebra `A` and elements `f` and `g` of `A`, the corner
`f (J / J²) g` of the first radical layer `J / J²` is the `k`-subspace of `A ⧸ J ^ 2` spanned by
the classes of the elements `f x g` with `x ∈ J`. For idempotents `f` and `g`, it is the piece
`f M` of the first radical layer `M = J(Ag) / J²(Ag)` of the left ideal `Ag`.

## Main definitions

* `TauCeti.radicalLayerCorner k J f g`: the corner `f (J / J²) g` as a `k`-subspace of
  `A ⧸ J ^ 2`.
* `IsIdempotentElem.smulTopRadicalLayerEquiv`: for idempotents `f` and `g`, the piece `f M` of
  the first radical layer `M` of `Ag` is the corner `f (J / J²) g`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Section II.3 for the quiver of a basic algebra.
-/

public section

open scoped Pointwise

namespace TauCeti

section Corner

variable (k : Type*) {A : Type*} [CommSemiring k] [Ring A] [Algebra k A]

/-- The corner `f (J / J²) g` of the first radical layer `J / J²`, as a `k`-subspace of
`A ⧸ J ^ 2`: the classes of the elements `f x g` with `x ∈ J`. When `A` is a finite-dimensional
basic algebra over an algebraically closed field, `J` is its Jacobson radical, and `eⱼ` and `eᵢ`
belong to a complete family of primitive orthogonal idempotents, a basis of the `(j, i)`-corner
`eⱼ (J / J²) eᵢ` gives the arrows `i → j` of the quiver of `A`. -/
def radicalLayerCorner (J : Ideal A) [J.IsTwoSided] (f g : A) : Submodule k (A ⧸ J ^ 2) :=
  (J.restrictScalars k).map
    ((Ideal.Quotient.mkₐ k (J ^ 2)).toLinearMap ∘ₗ LinearMap.mulLeftRight k (f, g))

variable {k}

@[simp]
theorem mem_radicalLayerCorner {J : Ideal A} [J.IsTwoSided] {f g : A} {z : A ⧸ J ^ 2} :
    z ∈ radicalLayerCorner k J f g ↔ ∃ x ∈ J, Ideal.Quotient.mk (J ^ 2) (f * x * g) = z := by
  simp [radicalLayerCorner, Ideal.Quotient.mkₐ_eq_mk]

end Corner

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {k : Type*} {A : Type*} [CommRing k] [Ring A] [Algebra k A]
  {J : Ideal A} [J.IsTwoSided] {f g : A}

variable (k J) in
/-- The `k`-linear map from the first radical layer `J(Ag) / J²(Ag)` of the left ideal `Ag` to
`A ⧸ J ^ 2`, sending a class to the class of the underlying element of `A`. -/
private noncomputable def radicalLayerToQuotient (g : A) :
    (↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))) ⧸
        J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))) →ₗ[k]
      A ⧸ J ^ 2 :=
  (Submodule.liftQ _ ((J ^ 2).mkQ ∘ₗ (Ideal.span {g} : Ideal A).subtype ∘ₗ
    (J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))).subtype) fun y hy ↦ by
      simpa [Submodule.Quotient.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem] using
        coe_mem_sq_of_mem_smul le_rfl hy)
    |>.restrictScalars k

private theorem radicalLayerToQuotient_mk
    (y : ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A)))) :
    radicalLayerToQuotient k J g (Submodule.Quotient.mk y) =
      Ideal.Quotient.mk (J ^ 2) ((y : (Ideal.span {g} : Ideal A)) : A) :=
  (rfl)

/-- **The corners of the first radical layer.** For idempotents `f` and `g` and a two-sided ideal
`J`, the piece `f M` of the first radical layer `M = J(Ag) / J²(Ag)` of the left ideal `Ag` is
the corner `f (J / J²) g`, by sending a class to the class of the underlying element of `A`. -/
noncomputable def smulTopRadicalLayerEquiv (hf : IsIdempotentElem f) (hg : IsIdempotentElem g) :
    ↥(f • (⊤ : Submodule k (↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))) ⧸
        J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))))) ≃ₗ[k]
      radicalLayerCorner k J f g := by
  set P := (Ideal.span {g} : Ideal A)
  set K := J • (⊤ : Submodule A P)
  set φ := radicalLayerToQuotient k J g ∘ₗ
    (f • (⊤ : Submodule k (K ⧸ J • (⊤ : Submodule A K)))).subtype
  -- `φ` is injective because every element of `J ^ 2 g` comes from `J • K`, and its range is
  -- the corner because every element of `K` lies in `J` and is fixed by right multiplication
  -- by `g`.
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).mpr ?_
    rintro ⟨m, hm⟩ hφ
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hfm := (hf.mem_smul_top_iff_smul_eq_self (S := k)).mp hm
    rw [← Submodule.Quotient.mk_smul] at hfm
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply] at hφ
    rw [← hfm, radicalLayerToQuotient_mk, Ideal.Quotient.eq_zero_iff_mem] at hφ
    obtain ⟨t, ht, hte⟩ := exists_mem_smul_coe_eq_mul hφ
    have hfy : f • y = t := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [hte]
      simp [mul_assoc, (mem_span_singleton_iff_mul_eq_self hg).mp (y : P).property]
    refine Subtype.ext ?_
    simpa [← hfm, hfy, Submodule.Quotient.mk_eq_zero] using ht
  have hrange : LinearMap.range φ = radicalLayerCorner k J f g := by
    apply le_antisymm
    · rintro _ ⟨⟨m, hm⟩, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have hfm := (hf.mem_smul_top_iff_smul_eq_self (S := k)).mp hm
      rw [← Submodule.Quotient.mk_smul] at hfm
      refine mem_radicalLayerCorner.mpr ⟨(y : P), coe_mem_of_mem_smul y.property, ?_⟩
      simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [← hfm, radicalLayerToQuotient_mk]
      congr 1
      simp [mul_assoc, (mem_span_singleton_iff_mul_eq_self hg).mp (y : P).property]
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_radicalLayerCorner.mp hz
      have hxg : x • spanSingletonGenerator g ∈ K := Submodule.smul_mem_smul hx Submodule.mem_top
      let m : K ⧸ J • (⊤ : Submodule A K) := f • Submodule.Quotient.mk ⟨_, hxg⟩
      have hm : m ∈ f • (⊤ : Submodule k (K ⧸ J • (⊤ : Submodule A K))) :=
        Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
      refine ⟨⟨m, hm⟩, ?_⟩
      simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, m]
      rw [← Submodule.Quotient.mk_smul, radicalLayerToQuotient_mk]
      congr 1
      simp [mul_assoc, coe_spanSingletonGenerator]
  exact (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hrange)

@[simp]
theorem coe_smulTopRadicalLayerEquiv_mk (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (y : ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))
    (hy : Submodule.Quotient.mk y ∈ f • (⊤ : Submodule k
      (↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))) ⧸
        J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))))) :
    (smulTopRadicalLayerEquiv hf hg ⟨_, hy⟩ : A ⧸ J ^ 2) =
      Ideal.Quotient.mk (J ^ 2) ((y : (Ideal.span {g} : Ideal A)) : A) :=
  radicalLayerToQuotient_mk (k := k) y

end IsIdempotentElem
