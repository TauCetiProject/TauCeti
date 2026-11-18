/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Pushout universal property of multivariate polynomial rings

For a ring homomorphism `f : B →+* B'`, the polynomial ring `MvPolynomial σ B'` is the pushout
`B' ⊗_B MvPolynomial σ B` of `f` and `MvPolynomial.C`, with canonical inclusions `MvPolynomial.C`
and `MvPolynomial.map f`. `MvPolynomial.pushoutLift` packages this universal property as an
equivalence on ring homomorphisms.

Factored from `TauCeti.LazardRing.tensorLift` in
`TauCeti/RingTheory/FormalGroup/CoordinateChange/HopfAlgebroid.lean`.
-/

public section

noncomputable section

namespace MvPolynomial

variable {σ B B' R : Type*} [CommSemiring B] [CommSemiring B'] [CommSemiring R]

/-- **Universal property of `MvPolynomial σ B'` as the pushout `B' ⊗_B MvPolynomial σ B`** of
`f : B →+* B'` and `C`, via restriction along `C` and along `map f`. -/
def pushoutLift (f : B →+* B') :
    {p : (B' →+* R) × (MvPolynomial σ B →+* R) // p.1.comp f = p.2.comp C} ≃
      (MvPolynomial σ B' →+* R) where
  toFun p := eval₂Hom p.1.1 (p.1.2 ∘ X)
  invFun k := ⟨(k.comp C, k.comp (map f)), RingHom.ext fun _ ↦ by simp⟩
  left_inv p := Subtype.ext <| Prod.ext (RingHom.ext (eval₂Hom_C _ _)) <|
    ringHom_ext' (RingHom.ext fun b ↦ by simpa using RingHom.congr_fun p.2 b) fun _ ↦ by simp
  right_inv _ := ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun _ ↦ by simp

/-- The left component classified by `k : MvPolynomial σ B' →+* R` is `k.comp C`. -/
@[simp] theorem pushoutLift_symm_apply_fst (f : B →+* B') (k : MvPolynomial σ B' →+* R) :
    ((pushoutLift f).symm k).1.1 = k.comp C := (rfl)

/-- The right component classified by `k : MvPolynomial σ B' →+* R` is `k.comp (map f)`. -/
@[simp] theorem pushoutLift_symm_apply_snd (f : B →+* B') (k : MvPolynomial σ B' →+* R) :
    ((pushoutLift f).symm k).1.2 = k.comp (map f) := (rfl)

section
variable (f : B →+* B') (p : {p : (B' →+* R) × (MvPolynomial σ B →+* R) // p.1.comp f = p.2.comp C})

/-- `pushoutLift f p` restricts to `p.1.1` along `C`. -/
@[simp] theorem pushoutLift_comp_C : (pushoutLift f p).comp C = p.1.1 :=
  congrArg (·.1.1) ((pushoutLift f).left_inv p)

/-- `pushoutLift f p` restricts to `p.1.2` along `map f`. -/
@[simp] theorem pushoutLift_comp_map : (pushoutLift f p).comp (map f) = p.1.2 :=
  congrArg (·.1.2) ((pushoutLift f).left_inv p)

/-- `pushoutLift f p` agrees with `p.1.1` on constants from `B'`. -/
@[simp] theorem pushoutLift_C (b : B') : pushoutLift f p (C b) = p.1.1 b :=
  RingHom.congr_fun (pushoutLift_comp_C f p) b

/-- `pushoutLift f p` agrees with `p.1.2` along `map f`. -/
@[simp] theorem pushoutLift_map (x : MvPolynomial σ B) : pushoutLift f p (map f x) = p.1.2 x :=
  RingHom.congr_fun (pushoutLift_comp_map f p) x

/-- `pushoutLift f p` agrees with `p.1.2` on the variables `X i`. -/
@[simp] theorem pushoutLift_X (i : σ) : pushoutLift f p (X i) = p.1.2 (X i) := by
  simpa using pushoutLift_map f p (X i)
end

/-- A ring homomorphism out of `MvPolynomial σ B'` is determined by its restrictions along `C` and
`map f`. -/
theorem pushout_ringHom_ext (f : B →+* B') {k k' : MvPolynomial σ B' →+* R}
    (h₁ : k.comp C = k'.comp C) (h₂ : k.comp (map f) = k'.comp (map f)) : k = k' :=
  (pushoutLift f).symm.injective (Subtype.ext (Prod.ext h₁ h₂))

/-- `pushoutLift` preserves degrees when both component maps are graded. -/
theorem pushoutLift_mem {M S₀ S₁ S₂ S ι : Type*} [AddCommMonoid M] [SetLike S₀ B']
    [SetLike S₁ (MvPolynomial σ B)] [SetLike S₂ (MvPolynomial σ B')] [SetLike S R]
    [AddCommMonoid ι] {w : σ → M} {ℬ : M → S₀} {𝒢 : M → S₁} {𝒯 : M → S₂} {𝒜 : ι → S}
    {r : M →+ ι} {f : B →+* B'}
    {p : {p : (B' →+* R) × (MvPolynomial σ B →+* R) // p.1.comp f = p.2.comp C}}
    (h𝒯 : (∀ ⦃n⦄ ⦃x⦄, x ∈ 𝒯 n → pushoutLift f p x ∈ 𝒜 (r n)) ↔
      (∀ ⦃n⦄ ⦃b⦄, b ∈ ℬ n → pushoutLift f p (C b) ∈ 𝒜 (r n)) ∧
        ∀ i : σ, pushoutLift f p (X i) ∈ 𝒜 (r (w i)))
    (hX : ∀ i, X i ∈ 𝒢 (w i)) (h₁ : ∀ ⦃n⦄ ⦃b⦄, b ∈ ℬ n → p.1.1 b ∈ 𝒜 (r n))
    (h₂ : ∀ ⦃n⦄ ⦃y⦄, y ∈ 𝒢 n → p.1.2 y ∈ 𝒜 (r n)) {n : M} {x : MvPolynomial σ B'}
    (hx : x ∈ 𝒯 n) : pushoutLift f p x ∈ 𝒜 (r n) :=
  h𝒯.mpr ⟨fun _ _ hb ↦ by simpa using h₁ hb, fun i ↦ by simpa using h₂ (hX i)⟩ hx

end MvPolynomial
