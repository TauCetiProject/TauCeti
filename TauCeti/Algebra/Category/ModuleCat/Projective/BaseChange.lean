/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Algebra.Epi
import Mathlib.LinearAlgebra.TensorProduct.Projective
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Projective dimension under `Tor`-acyclic base change and homological epimorphisms

Let `A` be a commutative ring and `B` an `A`-algebra. If `X` is an `A`-module with
`Tor_k^A(X, B) = 0` for all `0 < k < n`, then tensoring a projective resolution of `X` with `B`
remains exact in the degrees needed to resolve `B ⊗[A] X`, so base change does not increase
projective dimension: if `pd_A X < n` then `pd_B (B ⊗[A] X) < n`
(`ModuleCat.hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor`). In particular, if
`Tor_{k+1}^A(X, B) = 0` for all `k`, then `pd_B (B ⊗[A] X) ≤ pd_A X`
(`ModuleCat.projectiveDimension_tensorProduct_le_of_isZero_Tor`). This weakens the flatness
hypothesis of `ModuleCat.hasProjectiveDimensionLT_tensorProduct` to `Tor`-acyclicity of the single
module `X`.

A particularly useful instance is a **surjective homological epimorphism** `A → B`, meaning a
surjection satisfying `Tor_{k+1}^A(B, B) = 0` for all `k` (equivalently `B ⊗^L_A B ≃ B`). For any
`B`-module `M`, resolving `M` by free `B`-modules and using that `B ⊗[A] N ≃ N` functorially for
all `B`-modules `N` (`TensorProduct.lid'`) shows by induction on `n` that `Tor_{n+1}^A(M, B) = 0`
(`ModuleCat.isZero_Tor_succ_of_surjective_of_isZero_Tor_succ`). Combining this with `Tor`-acyclic
base change and the identification `B ⊗[A] M ≃ M` yields `pd_B M ≤ pd_A M`
(`ModuleCat.projectiveDimension_le_restrictScalars_of_surjective_of_isZero_Tor_succ`).

## Main results

* `ModuleCat.hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor`: if `X` has projective
  dimension `< n` over `A` and `Tor_{k+1}^A(X, B) = 0` for all `k + 1 < n`, then `B ⊗[A] X` has
  projective dimension `< n` over `B`.
* `ModuleCat.projectiveDimension_tensorProduct_le_of_isZero_Tor`: if `Tor_{k+1}^A(X, B) = 0` for
  all `k`, then `pd_B (B ⊗[A] X) ≤ pd_A X`.
* `ModuleCat.isZero_Tor_succ_of_surjective_of_isZero_Tor_succ`: for a surjection `A → B` with
  `Tor_{k+1}^A(B, B) = 0` for `k ≤ n`, every `B`-module `M` satisfies `Tor_{n+1}^A(M, B) = 0`.
* `ModuleCat.hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ`: for a surjection `A → B`
  with `Tor_{k+1}^A(B, B) = 0` for `k + 1 < n`, any `B`-module whose restriction to `A` has
  projective dimension `< n` has projective dimension `< n` over `B`.
* `ModuleCat.projectiveDimension_le_restrictScalars_of_surjective_of_isZero_Tor_succ`: for a
  surjective homological epimorphism `A → B`, `pd_B M ≤ pd_A M` for every `B`-module `M`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), proof of Proposition 11.31.
-/

public section

open CategoryTheory Limits TensorProduct

namespace ModuleCat

universe u

section TorAcyclicBaseChange

variable {A : Type u} [CommRing A] (B : Type u) [Ring B] [Algebra A B]

/-- **Projective dimension under `Tor`-acyclic base change.** If `X` has projective dimension
`< n` over `A` and `Tor_{k+1}^A(X, B) = 0` for all `k + 1 < n`, then `B ⊗[A] X` has projective
dimension `< n` over `B`. -/
theorem hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor (X : ModuleCat.{u} A) {n : ℕ}
    (hX : HasProjectiveDimensionLT X n)
    (hTor : ∀ k, k + 1 < n → IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj X).obj (of A B))) :
    HasProjectiveDimensionLT (of B (B ⊗[A] X)) n := by
  induction n generalizing X with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero, isZero_iff_subsingleton] at hX ⊢
    infer_instance
  | succ n ih =>
    cases n with
    | zero =>
      rw [← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective] at hX ⊢
      infer_instance
    | succ d =>
      -- Resolve `X` by a projective `A`-module `P` with kernel `K`. Since `Tor₁(X, B) = 0`,
      -- tensoring `0 → K → P → X → 0` with `B` stays exact, and `Tor` shifts down by one.
      let P : ModuleCat.{u} A := Projective.over X
      let f : P →ₗ[A] X := (Projective.π X).hom
      have hf : Function.Surjective f := (epi_iff_surjective _).1 inferInstance
      have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
      have hX₁ : HasProjectiveDimensionLT (of A f.ker) (d + 1) :=
        (f.hasProjectiveDimensionLE_succ_iff_ker hf d).1 hX
      have hP : Module.Flat A P := Module.Flat.of_projective
      have hTor₁ : ∀ k, k + 1 < d + 1 →
          IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A f.ker)).obj (of A B)) :=
        fun k hk ↦ hS.isZero_Tor_X₁ (of A B) (hTor (k + 1) (by omega))
          (isZero_Tor_succ_of_flat P (of A B) k)
      have hSB : (shortComplexOfCompEqZero
          (AlgebraTensorModule.lTensor B B f.ker.subtype)
          (AlgebraTensorModule.lTensor B B f) (by
            ext
            simp)).ShortExact := by
        refine shortComplex_shortExact _ ?_ ?_ (LinearMap.lTensor_surjective B hf)
        · exact lTensor_exact B (LinearMap.exact_subtype_ker_map f) hf
        · exact (LinearMap.lTensor_inj_iff_rTensor_inj B f.ker.subtype).2
            (hS.rTensor_injective_of_isZero_Tor_one (of A B) (hTor 0 (by omega)))
      have hBP : Projective (of B (B ⊗[A] P)) :=
        (IsProjective.iff_projective _).1 inferInstance
      exact (hSB.hasProjectiveDimensionLT_X₃_iff d hBP).2 (ih (of A f.ker) hX₁ hTor₁)

/-- **Projective dimension under `Tor`-acyclic base change.** If `Tor_{k+1}^A(X, B) = 0` for all
`k`, then `pd_B (B ⊗[A] X) ≤ pd_A X`. -/
theorem projectiveDimension_tensorProduct_le_of_isZero_Tor (X : ModuleCat.{u} A)
    (hTor : ∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj X).obj (of A B))) :
    projectiveDimension (of B (B ⊗[A] X)) ≤ projectiveDimension X :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor B X h fun k _ ↦ hTor k

end TorAcyclicBaseChange

section SurjectiveHomologicalEpi

variable {A B : Type u} [CommRing A] [Ring B] [Algebra A B]

/-- Restricting scalars on a free `B`-module `ι →₀ B` yields `ι →₀ B` as an `A`-module, so `Tor`
vanishes on it whenever `Tor` vanishes on `B`. -/
private lemma isZero_Tor_restrictScalars_finsupp {ι : Type u} {n : ℕ}
    (hB : IsZero (((Tor (ModuleCat.{u} A) n).obj (of A B)).obj (of A B))) :
    IsZero (((Tor (ModuleCat.{u} A) n).obj
      ((restrictScalars (algebraMap A B)).obj (of B (ι →₀ B)))).obj (of A B)) :=
  (isZero_Tor_finsupp (ι := ι) (of A B) (of A B) hB).of_iso
    (((Tor (ModuleCat.{u} A) n).mapIso
      (restrictScalarsAlgebraMapIso (R := A) (S := B) (ι →₀ B))).app (of A B))

/-- Restricting scalars on the canonical free `B`-presentation of `M` yields a short exact sequence
in `ModuleCat A`. -/
private lemma shortExact_restrictScalars_finsupp (M : ModuleCat.{u} B) :
    ((restrictScalars (algebraMap A B)).mapShortComplex.obj
      (Finsupp.linearCombination B (id : M → M)).shortComplexKer).ShortExact := by
  let f : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
  have hf : Function.Surjective f := fun m ↦ ⟨Finsupp.single m 1, by simp [f]⟩
  exact shortComplex_shortExact _ (LinearMap.exact_subtype_ker_map f) Subtype.val_injective hf

/-- **`Tor` vanishing for modules over a surjective homological epimorphism.** Let `A → B` be a
surjective ring homomorphism with `Tor_{k+1}^A(B, B) = 0` for all `k ≤ n`. Then every `B`-module
`M` satisfies `Tor_{n+1}^A(M, B) = 0`. -/
theorem isZero_Tor_succ_of_surjective_of_isZero_Tor_succ
    (hsurj : Function.Surjective (algebraMap A B)) (M : ModuleCat.{u} B) {n : ℕ}
    (hBB : ∀ k ≤ n, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A B)).obj (of A B))) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj
      ((restrictScalars (algebraMap A B)).obj M)).obj (of A B)) := by
  induction n generalizing M with
  | zero =>
    -- Resolve `M` by a free `B`-module `M →₀ B`; since `B ⊗[A] N ≃ N` functorially for
    -- `B`-modules (`TensorProduct.lid'`), `B ⊗[A] ker f → B ⊗[A] (M →₀ B)` is injective, hence so
    -- is `ker f ⊗[A] B → (M →₀ B) ⊗[A] B`, and `Tor₁(M →₀ B, B) = 0`.
    let : CommSemiring B :=
      { ‹Ring B› with
        mul_comm := fun b₁ b₂ ↦ by obtain ⟨a, rfl⟩ := hsurj b₁; exact Algebra.commutes a b₂ }
    have := Algebra.isEpi_of_surjective_algebraMap A B hsurj
    let f : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
    let S := (restrictScalars (algebraMap A B)).mapShortComplex.obj f.shortComplexKer
    have hS : S.ShortExact := shortExact_restrictScalars_finsupp M
    have hF : IsZero (((Tor (ModuleCat.{u} A) 1).obj S.X₂).obj (of A B)) :=
      isZero_Tor_restrictScalars_finsupp (hBB 0 le_rfl)
    have := isScalarTower_restrictScalars (R := A) (of B f.ker)
    have := isScalarTower_restrictScalars (R := A) (of B (M →₀ B))
    let e₁ := TensorProduct.lid' A B ((restrictScalars (algebraMap A B)).obj (of B f.ker))
    let e₂ := TensorProduct.lid' A B ((restrictScalars (algebraMap A B)).obj (of B (M →₀ B)))
    have hinj : Function.Injective (S.f.hom.rTensor B) := by
      rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
      have hnat : e₂.toLinearMap.restrictScalars A ∘ₗ S.f.hom.lTensor B =
          S.f.hom ∘ₗ e₁.toLinearMap.restrictScalars A :=
        TensorProduct.ext' fun b x ↦ (f.ker.subtype.map_smul b x).symm
      refine Function.Injective.of_comp (f := e₂) ?_
      have hcomp : ⇑e₂ ∘ ⇑(S.f.hom.lTensor B) = ⇑S.f.hom ∘ ⇑e₁ := congrArg DFunLike.coe hnat
      rw [hcomp]
      exact Subtype.val_injective.comp e₁.injective
    exact hS.isZero_Tor_one_X₃ (of A B) hF hinj
  | succ k ih =>
    let f : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
    exact (shortExact_restrictScalars_finsupp M).isZero_Tor_succ_X₃ (of A B)
      (isZero_Tor_restrictScalars_finsupp (hBB (k + 1) le_rfl))
      (ih (of B f.ker) fun j hj ↦ hBB j (hj.trans (Nat.le_succ k)))

/-- **Projective dimension along a surjective homological epimorphism.** Let `A → B` be a
surjective ring homomorphism with `Tor_{k+1}^A(B, B) = 0` for all `k + 1 < n`. If a `B`-module
`M` has projective dimension `< n` as an `A`-module, then it has projective dimension `< n` as a
`B`-module. -/
theorem hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ
    (hsurj : Function.Surjective (algebraMap A B)) (M : ModuleCat.{u} B) {n : ℕ}
    (hM : HasProjectiveDimensionLT ((restrictScalars (algebraMap A B)).obj M) n)
    (hBB : ∀ k, k + 1 < n → IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A B)).obj (of A B))) :
    HasProjectiveDimensionLT M n := by
  let : CommSemiring B :=
    { ‹Ring B› with
      mul_comm := fun b₁ b₂ ↦ by obtain ⟨a, rfl⟩ := hsurj b₁; exact Algebra.commutes a b₂ }
  have := Algebra.isEpi_of_surjective_algebraMap A B hsurj
  have := isScalarTower_restrictScalars (R := A) M
  have hTor : ∀ k, k + 1 < n → IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj
      ((restrictScalars (algebraMap A B)).obj M)).obj (of A B)) :=
    fun k hk ↦ isZero_Tor_succ_of_surjective_of_isZero_Tor_succ hsurj M fun j hj ↦
      hBB j (by omega)
  have _ := hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor B
    ((restrictScalars (algebraMap A B)).obj M) hM hTor
  exact hasProjectiveDimensionLT_of_iso
    (TensorProduct.lid' A B ((restrictScalars (algebraMap A B)).obj M)).toModuleIso n

/-- **Projective dimension along a surjective homological epimorphism.** If `A → B` is a surjective
ring homomorphism with `Tor_{k+1}^A(B, B) = 0` for all `k`, then `pd_B M ≤ pd_A M` for every
`B`-module `M`. -/
theorem projectiveDimension_le_restrictScalars_of_surjective_of_isZero_Tor_succ
    (hsurj : Function.Surjective (algebraMap A B)) (M : ModuleCat.{u} B)
    (hBB : ∀ k, IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj (of A B)).obj (of A B))) :
    projectiveDimension M ≤ projectiveDimension ((restrictScalars (algebraMap A B)).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ h ↦
    hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ hsurj M h fun k _ ↦ hBB k

end SurjectiveHomologicalEpi

end ModuleCat
