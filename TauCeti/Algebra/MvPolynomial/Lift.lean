/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Maps out of a polynomial ring

An `A`-algebra homomorphism out of a polynomial ring `A[X_σ]` is determined freely by the images
of the variables: `MvPolynomial.aevalEquiv` identifies such homomorphisms to `S` with the
functions `σ → S`, the points of affine space. So a homomorphism lifts along every surjective
`A`-algebra homomorphism `f : R → S`: send each variable to a preimage under `f` of its image.

## Main results

* `MvPolynomial.aevalEquiv`: evaluation `MvPolynomial.aeval` is a bijection from `σ → S` onto
  `A[X_σ] →ₐ[A] S`, with inverse evaluation at the variables.
* `MvPolynomial.exists_comp_eq_of_surjective`: every `g : A[X_σ] →ₐ[A] S` factors as `f.comp g'`
  through any surjective `f : R →ₐ[A] S`.
* `MvPolynomial.pushoutEquiv`: given `η : A →+* B`, ring homomorphisms `B[X_σ] →+* R` correspond
  to compatible pairs `(f, g)` of `f : B →+* R` and `g : A[X_σ] →+* R` with `f ∘ η = g ∘ C`.
* `MvPolynomial.ringHom_ext_comp_map`: a ring homomorphism out of `B[X_σ]` is determined by its
  restrictions along `C : B →+* B[X_σ]` and `MvPolynomial.map η : A[X_σ] →+* B[X_σ]`.
* `MvPolynomial.prodHomEquiv`: pairs of families `(σ → R) × (τ → R)` correspond to ring
  homomorphisms `ℤ[X_σ][X_τ] →+* R`.
* `MvPolynomial.iteratedRingHomEquivAlgHom`: ring homomorphisms `ℤ[X_σ][X_τ] →+* R` into an
  `A`-algebra `R` correspond to `A`-algebra homomorphisms `A[X_σ][X_τ] →ₐ[A] R`.
-/

public section

namespace MvPolynomial

/-- **Maps out of a polynomial ring are their values on the variables**: `MvPolynomial.aeval` is a
bijection from `σ → S` onto the `A`-algebra homomorphisms `A[X_σ] →ₐ[A] S`, with inverse
evaluation at the variables. -/
noncomputable def aevalEquiv (σ A S : Type*) [CommSemiring A] [CommSemiring S]
    [Algebra A S] :
    (σ → S) ≃ (MvPolynomial σ A →ₐ[A] S) where
  toFun := aeval
  invFun g i := g (X i)
  left_inv v := funext (aeval_X v)
  right_inv g := (aeval_unique g).symm

@[simp]
theorem aevalEquiv_apply {σ A S : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    (v : σ → S) : aevalEquiv σ A S v = aeval v :=
  (rfl)

@[simp]
theorem aevalEquiv_symm_apply {σ A S : Type*} [CommSemiring A] [CommSemiring S] [Algebra A S]
    (g : MvPolynomial σ A →ₐ[A] S) (i : σ) : (aevalEquiv σ A S).symm g i = g (X i) :=
  (rfl)

/-- **Maps out of a polynomial ring lift along surjections**: every `A`-algebra homomorphism
`g : A[X_σ] →ₐ[A] S` factors as `f.comp g'` through any surjective `f : R →ₐ[A] S`. -/
theorem exists_comp_eq_of_surjective {σ A R S : Type*} [CommSemiring A] [CommSemiring R]
    [CommSemiring S] [Algebra A R] [Algebra A S] {f : R →ₐ[A] S} (hf : Function.Surjective f)
    (g : MvPolynomial σ A →ₐ[A] S) : ∃ g' : MvPolynomial σ A →ₐ[A] R, f.comp g' = g :=
  ⟨aeval (Function.surjInv hf ∘ g ∘ X), algHom_ext fun _ ↦ by simp [Function.surjInv_eq hf]⟩

section Pushout

variable {σ A B R : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring R]

/-- **The pushout universal property of `MvPolynomial σ B`**: given `η : A →+* B`, ring
homomorphisms out of `MvPolynomial σ B` correspond to compatible pairs `(f, g)` of ring
homomorphisms `f : B →+* R` and `g : MvPolynomial σ A →+* R` with `f.comp η = g.comp C`, by
restriction along `C : B →+* MvPolynomial σ B` and `MvPolynomial.map η`.

Working with an explicit `η : A →+* B` rather than an `Algebra A B` instance avoids conflicting
`Algebra` instances when `B` is itself a polynomial ring over `A` endowed with a second structure
map distinct from `C` (such as the right unit of a Hopf algebroid). -/
noncomputable def pushoutEquiv (η : A →+* B) :
    {p : (B →+* R) × (MvPolynomial σ A →+* R) // p.1.comp η = p.2.comp C} ≃
      (MvPolynomial σ B →+* R) where
  toFun p := eval₂Hom p.val.1 (p.val.2 ∘ X)
  invFun k := ⟨(k.comp C, k.comp (map η)), by ext a; simp⟩
  left_inv p := by
    have hC : (eval₂Hom p.val.1 (p.val.2 ∘ X)).comp C = p.val.1 := RingHom.ext (eval₂Hom_C _ _)
    refine Subtype.ext (Prod.ext hC (ringHom_ext' ?_ fun _ ↦ by simp))
    ext a
    simpa [RingHom.comp_apply] using RingHom.congr_fun p.property a
  right_inv k := ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun _ ↦ by simp

/-- The left component of `(pushoutEquiv η).symm k` is the restriction of `k` along `C`. -/
@[simp]
theorem pushoutEquiv_symm_apply_fst (η : A →+* B) (k : MvPolynomial σ B →+* R) :
    ((pushoutEquiv η).symm k).val.1 = k.comp C :=
  (rfl)

/-- The right component of `(pushoutEquiv η).symm k` is the restriction of `k` along
`MvPolynomial.map η`. -/
@[simp]
theorem pushoutEquiv_symm_apply_snd (η : A →+* B) (k : MvPolynomial σ B →+* R) :
    ((pushoutEquiv η).symm k).val.2 = k.comp (map η) :=
  (rfl)

/-- `pushoutEquiv η (f, g)` restricts to `f` along `C`. -/
@[simp]
theorem pushoutEquiv_comp_C (η : A →+* B)
    (p : {p : (B →+* R) × (MvPolynomial σ A →+* R) // p.1.comp η = p.2.comp C}) :
    (pushoutEquiv η p).comp C = p.val.1 :=
  congrArg (fun q ↦ q.val.1) ((pushoutEquiv η).left_inv p)

/-- `pushoutEquiv η (f, g)` restricts to `g` along `MvPolynomial.map η`. -/
@[simp]
theorem pushoutEquiv_comp_map (η : A →+* B)
    (p : {p : (B →+* R) × (MvPolynomial σ A →+* R) // p.1.comp η = p.2.comp C}) :
    (pushoutEquiv η p).comp (map η) = p.val.2 :=
  congrArg (fun q ↦ q.val.2) ((pushoutEquiv η).left_inv p)

/-- `pushoutEquiv η (f, g)` agrees with `f` on constants `C b`. -/
@[simp]
theorem pushoutEquiv_C (η : A →+* B)
    (p : {p : (B →+* R) × (MvPolynomial σ A →+* R) // p.1.comp η = p.2.comp C}) (b : B) :
    pushoutEquiv η p (C b) = p.val.1 b :=
  RingHom.congr_fun (pushoutEquiv_comp_C η p) b

/-- `pushoutEquiv η (f, g)` agrees with `g` on the image of `MvPolynomial.map η`. -/
@[simp]
theorem pushoutEquiv_map (η : A →+* B)
    (p : {p : (B →+* R) × (MvPolynomial σ A →+* R) // p.1.comp η = p.2.comp C})
    (x : MvPolynomial σ A) :
    pushoutEquiv η p (map η x) = p.val.2 x :=
  RingHom.congr_fun (pushoutEquiv_comp_map η p) x

/-- `pushoutEquiv η (f, g)` agrees with `g` on the variables `X i`. -/
@[simp]
theorem pushoutEquiv_X (η : A →+* B)
    (p : {p : (B →+* R) × (MvPolynomial σ A →+* R) // p.1.comp η = p.2.comp C}) (i : σ) :
    pushoutEquiv η p (X i) = p.val.2 (X i) := by
  simpa using pushoutEquiv_map η p (X i)

/-- A ring homomorphism out of `MvPolynomial σ B` is uniquely determined by its restrictions along
`C : B →+* MvPolynomial σ B` and `MvPolynomial.map η : MvPolynomial σ A →+* MvPolynomial σ B`. -/
theorem ringHom_ext_comp_map (η : A →+* B) {k k' : MvPolynomial σ B →+* R}
    (h₁ : k.comp C = k'.comp C) (h₂ : k.comp (map η) = k'.comp (map η)) :
    k = k' :=
  (pushoutEquiv (σ := σ) η).symm.injective (Subtype.ext (Prod.ext h₁ h₂))

end Pushout

section Iterated

variable {σ τ R : Type*} [CommRing R]

/-- **Maps out of an iterated integral polynomial ring**: pairs of families `(σ → R) × (τ → R)`
correspond to ring homomorphisms out of `MvPolynomial τ (MvPolynomial σ ℤ)`. -/
noncomputable def prodHomEquiv :
    (σ → R) × (τ → R) ≃ (MvPolynomial τ (MvPolynomial σ ℤ) →+* R) where
  toFun vt := eval₂Hom (homEquiv.symm vt.1) vt.2
  invFun f := (f.comp C ∘ X, f ∘ X)
  left_inv _ := Prod.ext (funext fun _ ↦ by simp [homEquiv]) (funext fun _ ↦ by simp)
  right_inv f := ringHom_ext'
    ((RingHom.ext (eval₂Hom_C _ _)).trans (homEquiv.left_inv (f.comp C))) fun _ ↦ by simp

/-- The first component of `prodHomEquiv.symm f` evaluates `f ∘ C` on the inner variables. -/
@[simp] theorem prodHomEquiv_symm_apply_fst (f : MvPolynomial τ (MvPolynomial σ ℤ) →+* R) :
    (prodHomEquiv.symm f).1 = f.comp C ∘ X := (rfl)

/-- The second component of `prodHomEquiv.symm f` evaluates `f` on the outer variables. -/
@[simp] theorem prodHomEquiv_symm_apply_snd (f : MvPolynomial τ (MvPolynomial σ ℤ) →+* R) :
    (prodHomEquiv.symm f).2 = f ∘ X := (rfl)

/-- `prodHomEquiv vt` restricts along `C` to `homEquiv.symm vt.1`. -/
@[simp] theorem prodHomEquiv_comp_C (vt : (σ → R) × (τ → R)) :
    (prodHomEquiv vt).comp C = homEquiv.symm vt.1 := RingHom.ext (eval₂Hom_C _ _)

/-- `prodHomEquiv vt` evaluates constants `C a` via `homEquiv.symm vt.1`. -/
theorem prodHomEquiv_C (vt : (σ → R) × (τ → R)) (a : MvPolynomial σ ℤ) :
    prodHomEquiv vt (C a) = homEquiv.symm vt.1 a := eval₂Hom_C _ _ a

/-- `prodHomEquiv vt` sends an inner variable `C (X i)` to `vt.1 i`. -/
@[simp] theorem prodHomEquiv_C_X (vt : (σ → R) × (τ → R)) (i : σ) :
    prodHomEquiv vt (C (X i)) = vt.1 i := by simp [prodHomEquiv, homEquiv]

/-- `prodHomEquiv vt` sends an outer variable `X j` to `vt.2 j`. -/
@[simp] theorem prodHomEquiv_X (vt : (σ → R) × (τ → R)) (j : τ) :
    prodHomEquiv vt (X j) = vt.2 j := eval₂Hom_X' _ _ j

variable (A : Type*) [CommRing A] [Algebra A R]

/-- **Base change of maps out of an iterated polynomial ring**: for any `A`-algebra `R`, ring
homomorphisms out of `MvPolynomial τ (MvPolynomial σ ℤ)` correspond to `A`-algebra homomorphisms
out of `MvPolynomial τ (MvPolynomial σ A)`. -/
noncomputable def iteratedRingHomEquivAlgHom :
    (MvPolynomial τ (MvPolynomial σ ℤ) →+* R) ≃ (MvPolynomial τ (MvPolynomial σ A) →ₐ[A] R) where
  toFun f := aevalTower (aeval (f.comp C ∘ X)) (f ∘ X)
  invFun g := g.toRingHom.comp (map (map (Int.castRingHom A)))
  left_inv f := ringHom_ext' (homEquiv.injective <| funext fun _ ↦ by
      simp [homEquiv, aevalTower]) fun _ ↦ by simp
  right_inv g := algHom_ext' (algHom_ext fun _ ↦ by simp [algebraMap_eq]) fun _ ↦ by simp

/-- `iteratedRingHomEquivAlgHom A f` preserves the images of inner variables `C (X i)`. -/
@[simp] theorem iteratedRingHomEquivAlgHom_C_X (f : MvPolynomial τ (MvPolynomial σ ℤ) →+* R)
    (i : σ) : iteratedRingHomEquivAlgHom A f (C (X i)) = f (C (X i)) := by
  simp [iteratedRingHomEquivAlgHom, aevalTower]

/-- `iteratedRingHomEquivAlgHom A f` preserves the images of outer variables `X j`. -/
@[simp] theorem iteratedRingHomEquivAlgHom_X (f : MvPolynomial τ (MvPolynomial σ ℤ) →+* R)
    (j : τ) : iteratedRingHomEquivAlgHom A f (X j) = f (X j) := aevalTower_X _ _ j

/-- `(iteratedRingHomEquivAlgHom A).symm g` restricts `g` along `ℤ[X_σ][X_τ] →+* A[X_σ][X_τ]`. -/
@[simp] theorem iteratedRingHomEquivAlgHom_symm_apply
    (g : MvPolynomial τ (MvPolynomial σ A) →ₐ[A] R) :
    (iteratedRingHomEquivAlgHom A).symm g = g.toRingHom.comp (map (map (Int.castRingHom A))) :=
  (rfl)

end Iterated

end MvPolynomial
