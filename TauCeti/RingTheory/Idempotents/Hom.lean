/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Corner.Basic
public import TauCeti.RingTheory.Idempotents.Primitive.Basic

/-!
# Homomorphisms from an idempotent-generated left ideal

Let `A` be an algebra over a commutative semiring `k` and let `e` be an idempotent of `A`.
Evaluation at `e` identifies `Hom_A(Ae, M)` with the subspace `eM` of any module `M`.
For an arbitrary `f : A`, it also identifies the homomorphisms between the principal left ideals
`Ae` and `Af` with the corner:

`Hom_A(Ae, Af) ≃ₗ[k] eAf`, by `φ ↦ φ e`.

The corner `eAf` is defined in `TauCeti.RingTheory.Idempotents.Corner.Basic` as the range of the
`k`-linear map `x ↦ e x f`.

A homomorphism `φ` out of `Ae` is right multiplication by `φ e`
(`TauCeti.coe_apply_eq_mul_apply_generator`, proved for an arbitrary target ideal), which
therefore determines it. Its value `φ e` belongs to `Af` and is fixed by `e` on the left, so
lies in `eAf`. Conversely right multiplication by an element of `eAf` is a homomorphism
`Ae → Af`, since the left ideal `Af` is closed under left multiplication.

Specializing to `f = e` recovers the dictionary between the corner ring `eAe` and `End (Ae)` which
`TauCeti.RingTheory.Idempotents.Primitive.Basic` uses to compare primitivity of `e` with
indecomposability of `Ae`. When `f` is also idempotent, the dictionary computes the *graded*
homomorphism spaces between the indecomposable projectives of a graded algebra with a
distinguished family of idempotents, since the corner inherits the grading of `A`.

## Main definitions

* `IsIdempotentElem.spanSingletonHomEquivSMulTop`: evaluation gives `Hom_A(Ae, M) ≃ₗ[k] eM`.
* `TauCeti.cornerToSpanSingletonHom`: right multiplication by an element of `eAf`, as a
  homomorphism `Ae → Af`.

## Main results

* `TauCeti.spanSingletonHomEquivCorner`: **the dictionary `Hom_A(Ae, Af) ≃ₗ[k] eAf`.**
* `TauCeti.coe_apply_eq_mul_apply_generator`: a homomorphism out of `Ae` is right multiplication
  by its value at `e`.
* `IsIdempotentElem.endSpanSingletonRingEquiv`: the endomorphism ring of `Ae` is the opposite of
  the corner `eAe`, as rings.
* `IsIdempotentElem.exists_mul_eq_of_linearEquiv`: an isomorphism `Ae ≅ Af` gives `a ∈ eAf` and
  `b ∈ fAe` with `a b = e` and `b a = f`.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.4.
-/

public section

open scoped Pointwise

namespace IsIdempotentElem

open TauCeti

universe u v

variable {k : Type v} [CommSemiring k] {A : Type u} [Semiring A] [Algebra k A] {e : A}

/-- Evaluation at `e` identifies maps from `Ae` into any module with the subspace `eM`.
The inverse sends a vector `m` fixed by `e` to the map `a ↦ a • m`. -/
def spanSingletonHomEquivSMulTop {M : Type*} [AddCommMonoid M] [Module k M] [Module A M]
    [IsScalarTower k A M] (he : IsIdempotentElem e) :
    ((Ideal.span {e} : Ideal A) →ₗ[A] M) ≃ₗ[k] ↥(e • (⊤ : Submodule k M)) where
  toFun φ := ⟨φ (spanSingletonGenerator e), by
    rw [← smul_spanSingletonGenerator he (spanSingletonGenerator e), map_smul,
      coe_spanSingletonGenerator]
    exact Submodule.smul_mem_pointwise_smul _ e (⊤ : Submodule k M) (Submodule.mem_top)⟩
  map_add' φ ψ := Subtype.ext (by simp)
  map_smul' c φ := Subtype.ext (by simp)
  invFun m := (LinearMap.toSpanSingleton A M (m : M)).comp (Ideal.span {e} : Ideal A).subtype
  left_inv φ := by
    ext a
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
      ← map_smul, smul_spanSingletonGenerator he]
  right_inv m := by
    apply Subtype.ext
    obtain ⟨n, _, hn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 m.property
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.toSpanSingleton_apply,
      coe_spanSingletonGenerator]
    rw [← hn, smul_smul, he.eq]

/-- The evaluation equivalence sends a homomorphism to its value at the idempotent. -/
@[simp]
theorem coe_spanSingletonHomEquivSMulTop_apply {M : Type*} [AddCommMonoid M] [Module k M]
    [Module A M] [IsScalarTower k A M] (he : IsIdempotentElem e)
    (φ : (Ideal.span {e} : Ideal A) →ₗ[A] M) :
    (spanSingletonHomEquivSMulTop (k := k) he φ : M) = φ (spanSingletonGenerator e) :=
  (rfl)

/-- The inverse evaluation equivalence is scalar action by an element of `Ae`. -/
@[simp]
theorem spanSingletonHomEquivSMulTop_symm_apply {M : Type*} [AddCommMonoid M] [Module k M]
    [Module A M] [IsScalarTower k A M] (he : IsIdempotentElem e)
    (m : ↥(e • (⊤ : Submodule k M))) (a : (Ideal.span {e} : Ideal A)) :
    (spanSingletonHomEquivSMulTop (k := k) he).symm m a = (a : A) • (m : M) :=
  (rfl)

end IsIdempotentElem

namespace TauCeti

universe u v

variable (k : Type v) [CommSemiring k] {A : Type u} [Semiring A] [Algebra k A]

/-! ### The dictionary -/

variable {k}
variable {e f : A}

/-- The value at the generator of a homomorphism `Ae → Af` lies in the corner `eAf`. -/
theorem apply_generator_mem_cornerSubmodule (he : IsIdempotentElem e)
    (φ : (Ideal.span {e} : Ideal A) →ₗ[A] (Ideal.span {f} : Ideal A)) :
    (φ (spanSingletonGenerator e) : A) ∈ cornerSubmodule k e f := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (φ (spanSingletonGenerator e)).2
  have hleft : e * (φ (spanSingletonGenerator e) : A) = (φ (spanSingletonGenerator e) : A) := by
    simpa only [coe_spanSingletonGenerator] using
      (coe_apply_eq_mul_apply_generator he φ (spanSingletonGenerator e)).symm
  rw [cornerSubmodule_def, LinearMap.mem_range]
  exact ⟨a, by simpa only [LinearMap.mulLeftRight_apply, mul_assoc, ha] using hleft⟩

/-- Right multiplication by an element of the corner `eAf`, as a homomorphism `Ae → Af`. -/
def cornerToSpanSingletonHom (x : cornerSubmodule k e f) :
    (Ideal.span {e} : Ideal A) →ₗ[A] (Ideal.span {f} : Ideal A) where
  toFun y := ⟨(y : A) * (x : A), (Ideal.span {f}).mul_mem_left (y : A)
    (mem_span_singleton_of_mem_cornerSubmodule x.2)⟩
  map_add' y z := Subtype.ext (by simpa using add_mul (y : A) (z : A) (x : A))
  map_smul' a y := Subtype.ext (by simpa using mul_assoc a (y : A) (x : A))

@[simp]
theorem coe_cornerToSpanSingletonHom_apply (x : cornerSubmodule k e f)
    (y : (Ideal.span {e} : Ideal A)) :
    (cornerToSpanSingletonHom x y : A) = (y : A) * (x : A) :=
  (rfl)

/-- **The homomorphisms from `Ae` to `Af` are the corner `eAf`**, by evaluation at the generator
`e`. Only `e` must be idempotent; `f` is arbitrary. The inverse sends an element of the corner
to right multiplication by it. -/
def spanSingletonHomEquivCorner (he : IsIdempotentElem e) :
    ((Ideal.span {e} : Ideal A) →ₗ[A] (Ideal.span {f} : Ideal A)) ≃ₗ[k]
      cornerSubmodule k e f where
  toFun φ := ⟨(φ (spanSingletonGenerator e) : A), apply_generator_mem_cornerSubmodule he φ⟩
  map_add' φ ψ := Subtype.ext (by simp)
  map_smul' c φ := Subtype.ext (by simp)
  invFun := cornerToSpanSingletonHom
  left_inv φ := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [coe_cornerToSpanSingletonHom_apply]
    exact (coe_apply_eq_mul_apply_generator he φ y).symm
  right_inv x := by
    refine Subtype.ext ?_
    rw [coe_cornerToSpanSingletonHom_apply, coe_spanSingletonGenerator]
    exact mul_eq_self_of_mem_cornerSubmodule he x.2

@[simp]
theorem coe_spanSingletonHomEquivCorner_apply (he : IsIdempotentElem e)
    (φ : (Ideal.span {e} : Ideal A) →ₗ[A] (Ideal.span {f} : Ideal A)) :
    ((spanSingletonHomEquivCorner (k := k) he φ : cornerSubmodule k e f) : A) =
      (φ (spanSingletonGenerator e) : A) :=
  (rfl)

@[simp]
theorem coe_spanSingletonHomEquivCorner_symm_apply (he : IsIdempotentElem e)
    (x : cornerSubmodule k e f)
    (y : (Ideal.span {e} : Ideal A)) :
    (((spanSingletonHomEquivCorner (k := k) he).symm x) y : A) = (y : A) * (x : A) :=
  (rfl)

end TauCeti

namespace IsIdempotentElem

open TauCeti MulOpposite

variable {A : Type*} [Ring A] {e : A}

/-- **The endomorphism ring of `Ae` is the opposite of the corner `eAe`**: evaluation at the
generator `e` (`TauCeti.spanSingletonHomEquivCorner`) is multiplicative up to order, since an
endomorphism is right multiplication by its value at `e`. -/
noncomputable def endSpanSingletonRingEquiv (he : IsIdempotentElem e) :
    (Module.End A (Ideal.span {e} : Ideal A))ᵐᵒᵖ ≃+* he.Corner where
  toFun φ := (he.cornerLinearEquivCornerSubmodule (R := ℕ)).symm
    (spanSingletonHomEquivCorner (k := ℕ) he (unop φ))
  invFun c := op ((spanSingletonHomEquivCorner (k := ℕ) he).symm
    (he.cornerLinearEquivCornerSubmodule (R := ℕ) c))
  left_inv φ := by simp
  right_inv c := by simp
  map_mul' φ ψ := Subtype.ext <| by
    simpa using coe_apply_eq_mul_apply_generator he (unop ψ) (unop φ (spanSingletonGenerator e))
  map_add' φ ψ := Subtype.ext <| by simp

@[simp]
theorem val_endSpanSingletonRingEquiv_apply (he : IsIdempotentElem e)
    (φ : (Module.End A (Ideal.span {e} : Ideal A))ᵐᵒᵖ) :
    (he.endSpanSingletonRingEquiv φ).1 = (unop φ (spanSingletonGenerator e) : A) := by
  -- Unfold the definition to the two dictionary equivalences, which have `simp` lemmas.
  change ((he.cornerLinearEquivCornerSubmodule (R := ℕ)).symm
    (spanSingletonHomEquivCorner (k := ℕ) he (unop φ))).1 = _
  simp

@[simp]
theorem coe_unop_endSpanSingletonRingEquiv_symm_apply (he : IsIdempotentElem e) (c : he.Corner)
    (y : (Ideal.span {e} : Ideal A)) :
    (unop (he.endSpanSingletonRingEquiv.symm c) y : A) = (y : A) * c.1 := by
  -- Unfold the definition to the two dictionary equivalences, which have `simp` lemmas.
  change ((spanSingletonHomEquivCorner (k := ℕ) he).symm
    (he.cornerLinearEquivCornerSubmodule (R := ℕ) c) y : A) = _
  simp

/-- An isomorphism of left ideals `Ae ≅ Af` between idempotent generators is right multiplication
by some `a ∈ eAf`, with inverse right multiplication by some `b ∈ fAe`; then `a b = e` and
`b a = f`. -/
theorem exists_mul_eq_of_linearEquiv (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (φ : (Ideal.span {e} : Ideal A) ≃ₗ[A] (Ideal.span {f} : Ideal A)) :
    ∃ a b : A, e * a = a ∧ a * f = a ∧ f * b = b ∧ b * e = b ∧ a * b = e ∧ b * a = f := by
  -- `a` and `b` are the values of `φ` and `φ⁻¹` at the generators `e` and `f`.
  have hea : e * (φ (spanSingletonGenerator e) : A) = φ (spanSingletonGenerator e) := by
    simpa only [coe_spanSingletonGenerator, LinearEquiv.coe_coe] using
      (coe_apply_eq_mul_apply_generator he φ.toLinearMap (spanSingletonGenerator e)).symm
  have hfb : f * (φ.symm (spanSingletonGenerator f) : A) = φ.symm (spanSingletonGenerator f) := by
    simpa only [coe_spanSingletonGenerator, LinearEquiv.coe_coe] using
      (coe_apply_eq_mul_apply_generator hf φ.symm.toLinearMap (spanSingletonGenerator f)).symm
  have haf : (φ (spanSingletonGenerator e) : A) * f = φ (spanSingletonGenerator e) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (φ (spanSingletonGenerator e)).2
    rw [← hc, mul_assoc, hf.eq]
  have hbe : (φ.symm (spanSingletonGenerator f) : A) * e = φ.symm (spanSingletonGenerator f) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (φ.symm (spanSingletonGenerator f)).2
    rw [← hc, mul_assoc, he.eq]
  -- The value of `φ` at the generator is `a` times the generator of `Af`, and dually.
  have hφ : φ (spanSingletonGenerator e) =
      (φ (spanSingletonGenerator e) : A) • spanSingletonGenerator f :=
    Subtype.ext (by simp [haf])
  have hφ' : φ.symm (spanSingletonGenerator f) =
      (φ.symm (spanSingletonGenerator f) : A) • spanSingletonGenerator e :=
    Subtype.ext (by simp [hbe])
  refine ⟨_, _, hea, haf, hfb, hbe, ?_, ?_⟩
  · have := congrArg Subtype.val (φ.symm_apply_apply (spanSingletonGenerator e))
    rw [hφ, map_smul] at this
    simpa using this
  · have := congrArg Subtype.val (φ.apply_symm_apply (spanSingletonGenerator f))
    rw [hφ', map_smul] at this
    simpa using this

end IsIdempotentElem
