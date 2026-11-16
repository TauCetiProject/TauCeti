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
import Mathlib.LinearAlgebra.TensorProduct.Projective
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor
import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension

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
surjection from a commutative ring `A` to an `A`-algebra `B` satisfying `Tor_{k+1}^A(B, B) = 0` for
all `k` (equivalently `B ⊗^L_A B ≃ B`). For any `B`-module `M`, resolving `M` by free `B`-modules
and using that `N ⊗[A] B ≃ N` functorially for all `B`-modules `N` shows by induction on `n` that
`Tor_{n+1}^A(M, B) = 0` (`ModuleCat.isZero_Tor_succ_of_surjective_of_isZero_Tor_succ`). Combining
this with `Tor`-acyclic base change and the identification `B ⊗[A] M ≃ M` yields
`pd_B M ≤ pd_A M`
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

/-- For an `A`-linear map `g : M → N`, `B ⊗[A] g` is injective whenever `g ⊗[A] B` is injective. -/
private lemma lTensor_injective_of_rTensor_injective {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {g : M →ₗ[A] N} (hg : Function.Injective (g.rTensor B)) :
    Function.Injective (AlgebraTensorModule.lTensor B B g) := by
  have hcomm : ∀ t : B ⊗[A] M,
      TensorProduct.comm A B N (AlgebraTensorModule.lTensor B B g t) =
        g.rTensor B (TensorProduct.comm A B M t) := fun t ↦ by
    induction t using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  intro x y hxy
  apply (TensorProduct.comm A B M).injective
  apply hg
  rw [← hcomm, ← hcomm, hxy]

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
        · exact lTensor_injective_of_rTensor_injective B
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

/-- For a surjection `A → B` and a `B`-module `M`, the multiplication map `B ⊗[A] M → M` is a
`B`-linear equivalence. -/
private noncomputable def lidOfSurjective (hsurj : Function.Surjective (algebraMap A B))
    (M : ModuleCat.{u} B) :
    B ⊗[A] ((restrictScalars (algebraMap A B)).obj M) ≃ₗ[B] M := by
  let _ : Module A M := ((restrictScalars (algebraMap A B)).obj M).isModule
  have : IsScalarTower A B M := ⟨fun a b m ↦ by
    change (a • b) • m = algebraMap A B a • (b • m)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsmul (b : B) (m : M) :
      (1 : B) ⊗ₜ[A] (b • m : (restrictScalars (algebraMap A B)).obj M) = b ⊗ₜ[A] m := by
    obtain ⟨a, rfl⟩ := hsurj b
    change (1 : B) ⊗ₜ[A] (a • (m : (restrictScalars (algebraMap A B)).obj M)) =
      algebraMap A B a ⊗ₜ[A] m
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  refine LinearEquiv.ofLinearMap
    (AlgebraTensorModule.lift
      { toFun := fun b ↦
          { toFun := fun m ↦ b • m
            map_add' := smul_add b
            map_smul' := fun a m ↦ by
              change b • (algebraMap A B a • m) = algebraMap A B a • (b • m)
              rw [← mul_smul, ← mul_smul, Algebra.commutes] }
        map_add' := fun b₁ b₂ ↦ by ext m; exact add_smul b₁ b₂ m
        map_smul' := fun b₁ b₂ ↦ by ext m; exact mul_smul b₁ b₂ m })
    { toFun := fun m ↦ (1 : B) ⊗ₜ[A] m
      map_add' := fun m₁ m₂ ↦ tmul_add (1 : B) m₁ m₂
      map_smul' := fun b m ↦ (hsmul b m).trans <| by
        change b ⊗ₜ[A] m = (b * 1) ⊗ₜ[A] m
        rw [mul_one] }
    (by ext m; exact one_smul B m)
    (AlgebraTensorModule.ext fun b m ↦ hsmul b m)

/-- For a surjection `A → B` and a `B`-module `M`, the multiplication map `M ⊗[A] B → M` is an
`A`-linear equivalence. -/
private noncomputable def ridOfSurjective (hsurj : Function.Surjective (algebraMap A B))
    (M : ModuleCat.{u} B) :
    ((restrictScalars (algebraMap A B)).obj M) ⊗[A] B ≃ₗ[A]
      ((restrictScalars (algebraMap A B)).obj M) := by
  let _ : Module A M := ((restrictScalars (algebraMap A B)).obj M).isModule
  have : IsScalarTower A B M := ⟨fun a b m ↦ by
    change (a • b) • m = algebraMap A B a • (b • m)
    rw [Algebra.smul_def, mul_smul]⟩
  exact TensorProduct.comm A _ B ≪≫ₗ (lidOfSurjective hsurj M).restrictScalars A

private lemma ridOfSurjective_rTensor (hsurj : Function.Surjective (algebraMap A B))
    {M N : ModuleCat.{u} B} (g : M ⟶ N)
    (t : ((restrictScalars (algebraMap A B)).obj M) ⊗[A] B) :
    ridOfSurjective hsurj N (((restrictScalars (algebraMap A B)).map g).hom.rTensor B t) =
      ((restrictScalars (algebraMap A B)).map g).hom (ridOfSurjective hsurj M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m b => exact (g.hom.map_smul b m).symm
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- Restricting scalars on a free `B`-module `ι →₀ B` yields `ι →₀ B` as an `A`-module, so `Tor`
vanishes on it whenever `Tor` vanishes on `B`. -/
private lemma isZero_Tor_restrictScalars_finsupp {ι : Type u} {n : ℕ}
    (hB : IsZero (((Tor (ModuleCat.{u} A) n).obj (of A B)).obj (of A B))) :
    IsZero (((Tor (ModuleCat.{u} A) n).obj
      ((restrictScalars (algebraMap A B)).obj (of B (ι →₀ B)))).obj (of A B)) := by
  let e : of A (ι →₀ B) ≃ₗ[A] (restrictScalars (algebraMap A B)).obj (of B (ι →₀ B)) :=
    { AddEquiv.refl (ι →₀ B) with
      map_smul' := fun a g ↦ Finsupp.ext fun i ↦ by
        change a • g i = algebraMap A B a * g i
        rw [Algebra.smul_def] }
  exact (isZero_Tor_finsupp (ι := ι) (of A B) (of A B) hB).of_iso
    (((Tor (ModuleCat.{u} A) n).mapIso e.toModuleIso).app (of A B)).symm

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
    -- Resolve `M` by a free `B`-module `M →₀ B`; since `N ⊗[A] B ≃ N` functorially for
    -- `B`-modules, `ker f ⊗[A] B → (M →₀ B) ⊗[A] B` is injective, and `Tor₁(M →₀ B, B) = 0`.
    let f : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
    let S := (restrictScalars (algebraMap A B)).mapShortComplex.obj f.shortComplexKer
    have hS : S.ShortExact := shortExact_restrictScalars_finsupp M
    have hF : IsZero (((Tor (ModuleCat.{u} A) 1).obj S.X₂).obj (of A B)) :=
      isZero_Tor_restrictScalars_finsupp (hBB 0 le_rfl)
    have hinj : Function.Injective (S.f.hom.rTensor B) := fun x y hxy ↦
      (ridOfSurjective hsurj (of B f.ker)).injective <| Subtype.val_injective <|
        (ridOfSurjective_rTensor hsurj f.shortComplexKer.f x).symm.trans <|
          (congrArg (ridOfSurjective hsurj f.shortComplexKer.X₂) hxy).trans
            (ridOfSurjective_rTensor hsurj f.shortComplexKer.f y)
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
  have hTor : ∀ k, k + 1 < n → IsZero (((Tor (ModuleCat.{u} A) (k + 1)).obj
      ((restrictScalars (algebraMap A B)).obj M)).obj (of A B)) :=
    fun k hk ↦ isZero_Tor_succ_of_surjective_of_isZero_Tor_succ hsurj M fun j hj ↦
      hBB j (by omega)
  have _ := hasProjectiveDimensionLT_tensorProduct_of_isZero_Tor B
    ((restrictScalars (algebraMap A B)).obj M) hM hTor
  exact hasProjectiveDimensionLT_of_iso (lidOfSurjective hsurj M).toModuleIso n

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
