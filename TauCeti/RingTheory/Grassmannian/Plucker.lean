/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.PicardGroup
import TauCeti.LinearAlgebra.ExteriorPower.Invertible

/-!
# The Plücker map on points of the Grassmannian

For a point `N` of the Grassmannian `G(k, X; R)` of quotients of `X` that are finite projective of
constant rank `k`, the top exterior power `⋀ᵏ (X ⧸ N)` is invertible, and the kernel of the
surjection `⋀ᵏ X → ⋀ᵏ (X ⧸ N)` is a point of `G(1, ⋀ᵏ X; R)`: the **Plücker point** of `N`
(`Module.Grassmannian.plucker`). Over an `R`-algebra `A`, with `X = A ⊗[R] M`, it is read in
`A ⊗[R] ⋀ᵏ M` through the base change isomorphism of exterior powers
(`Module.Grassmannian.pluckerBaseChange`), and it commutes with base change along `R`-algebra maps
(`Module.Grassmannian.pluckerBaseChange_map`). This naturality is what makes it the map on points of
the Plücker morphism of Grassmannian schemes (`Module.Grassmannian.pluckerHom`).

The naturality is proved by checking one inclusion on the wedges `(1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₖ)`, which
span `⋀ᵏ (A ⊗[R] M)`; equality then holds because comparable points of a Grassmannian are equal
(`Module.Grassmannian.eq_of_le`).

## Main definitions

* `Module.Grassmannian.plucker`: the Plücker point `ker (⋀ᵏ X → ⋀ᵏ (X ⧸ N))` of `N`.
* `Module.Grassmannian.pluckerBaseChange`: the Plücker point of `N ∈ G(k, A ⊗[R] M; A)`, as a point
  of `G(1, A ⊗[R] ⋀ᵏ M; A)`.

## Main results

* `Module.Grassmannian.toSubmodule_plucker_ofSurjective`: the Plücker point of the kernel of
  `φ : X ↠ P` is the kernel of `⋀ᵏ φ`.
* `Module.Grassmannian.pluckerBaseChange_map`: naturality in the algebra.
-/
public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

section Plucker

variable {R : Type u} [CommRing R] {X : Type v} [AddCommGroup X] [Module R X] {k : ℕ}

/-- The top exterior power `⋀ᵏ (X ⧸ N)` of the quotient by a point `N` of `G(k, X; R)` is
invertible: finite projective of constant rank one. -/
theorem invertible_exteriorPower_quotient (N : G(k, X; R)) :
    Module.Invertible R (⋀[R]^k (X ⧸ N.toSubmodule)) :=
  exteriorPower.invertible_of_rankAtStalk_eq N.rankAtStalk_eq

/-- **The Plücker point** of `N ∈ G(k, X; R)`: the kernel of the surjection
`⋀ᵏ X → ⋀ᵏ (X ⧸ N)` onto an invertible module, a point of `G(1, ⋀ᵏ X; R)`. -/
noncomputable def plucker (N : G(k, X; R)) : G(1, ⋀[R]^k X; R) :=
  have := invertible_exteriorPower_quotient N
  ofSurjective (exteriorPower.map k N.toSubmodule.mkQ)
    (exteriorPower.map_surjective N.toSubmodule.mkQ_surjective) fun p ↦ by
      rw [exteriorPower.rankAtStalk_eq_choose, N.rankAtStalk_eq, Nat.choose_self]

/-- The Plücker point of `N` is the kernel of `⋀ᵏ X → ⋀ᵏ (X ⧸ N)`. -/
@[simp]
theorem toSubmodule_plucker (N : G(k, X; R)) :
    (plucker N).toSubmodule = LinearMap.ker (exteriorPower.map k N.toSubmodule.mkQ) := by
  simp [plucker]

/-- The Plücker point of the kernel of a surjection `φ : X → P` onto a finite projective module of
constant rank `k` is the kernel of `⋀ᵏ φ`. -/
theorem toSubmodule_plucker_ofSurjective {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (φ : X →ₗ[R] P) (hφ : Function.Surjective φ)
    (hP : ∀ p, rankAtStalk (R := R) P p = k) :
    (plucker (ofSurjective φ hφ hP)).toSubmodule = LinearMap.ker (exteriorPower.map k φ) := by
  set e := φ.quotKerEquivOfSurjective hφ
  have hφe : φ = e.toLinearMap ∘ₗ (LinearMap.ker φ).mkQ := by
    ext x
    simp [e]
  rw [toSubmodule_plucker, toSubmodule_ofSurjective]
  conv_rhs => rw [hφe, exteriorPower.map_comp, ← LinearEquiv.exteriorPower_toLinearMap,
    LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

end Plucker

section BaseChange

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {A : Type w} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]

/-- **The Plücker point over an `R`-algebra `A`.** The Plücker point of `N ∈ G(k, A ⊗[R] M; A)`,
read in `A ⊗[R] ⋀ᵏ M` through the base change isomorphism `⋀ᵏ_A (A ⊗[R] M) ≃ A ⊗[R] ⋀ᵏ M`. -/
noncomputable def pluckerBaseChange (N : G(k, A ⊗[R] M; A)) : G(1, A ⊗[R] ⋀[R]^k M; A) :=
  (TauCeti.exteriorPower.equivBaseChange A k).grassmannianCongr (plucker N)

/-- The Plücker point over `A` is the image of the kernel of
`⋀ᵏ_A (A ⊗[R] M) → ⋀ᵏ_A ((A ⊗[R] M) ⧸ N)` in `A ⊗[R] ⋀ᵏ M`. -/
@[simp]
theorem toSubmodule_pluckerBaseChange (N : G(k, A ⊗[R] M; A)) :
    (pluckerBaseChange N).toSubmodule =
      (LinearMap.ker (exteriorPower.map k N.toSubmodule.mkQ)).map
        (TauCeti.exteriorPower.equivBaseChange A k).toLinearMap := by
  simp [pluckerBaseChange]

/-- The value of `⋀ᵏ (B ⊗[R] M) → ⋀ᵏ ((B ⊗[R] M) ⧸ map f N)` on the image of
`(1 ⊗ m₁) ∧ ⋯ ∧ (1 ⊗ mₖ)` under `⋀ᵏ_A (A ⊗[R] M) ≃ A ⊗[R] ⋀ᵏ M → B ⊗[R] ⋀ᵏ M ≃ ⋀ᵏ_B (B ⊗[R] M)`. -/
private theorem map_mkQ_rTensor_ιMulti (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) (m : Fin k → M) :
    exteriorPower.map k (map f N).toSubmodule.mkQ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm
        (f.toLinearMap.rTensor (⋀[R]^k M) (TauCeti.exteriorPower.equivBaseChange A k
          (exteriorPower.ιMulti A k fun i ↦ (1 : A) ⊗ₜ[R] m i)))) =
      exteriorPower.ιMulti B k fun i ↦ (map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] m i) := by
  have hA := TauCeti.exteriorPower.equivBaseChange_ιMulti_tmul (R := R) A (fun _ ↦ (1 : A)) m
  simp only [Finset.prod_const_one] at hA
  rw [hA, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    TauCeti.exteriorPower.equivBaseChange_symm_tmul_ιMulti, one_smul,
    exteriorPower.map_apply_ιMulti, Function.comp_def]

/-- The key step of `pluckerBaseChange_map`: the image under `f` of a vector of the Plücker point of
`N` lies in the Plücker point of `map f N`. -/
private theorem map_mkQ_rTensor_eq_zero (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A))
    {x : ⋀[A]^k (A ⊗[R] M)} (hx : exteriorPower.map k N.toSubmodule.mkQ x = 0) :
    exteriorPower.map k (map f N).toSubmodule.mkQ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm
        (f.toLinearMap.rTensor (⋀[R]^k M) (TauCeti.exteriorPower.equivBaseChange A k x))) = 0 := by
  algebraize [f.toRingHom]
  set Q := (B ⊗[R] M) ⧸ (map f N).toSubmodule
  -- after `algebraize`, `algebraMap A B` is `f` by definition
  have hf : (Algebra.linearMap A B).restrictScalars R = f.toLinearMap := LinearMap.ext fun _ ↦ rfl
  -- the map `A ⊗[R] M → B ⊗[R] M` induced by `f`, as an `A`-linear map
  let h : A ⊗[R] M →ₗ[A] B ⊗[R] M := AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)
  have hh (x : A ⊗[R] M) : h x = f.toLinearMap.rTensor M x := by
    rw [AlgebraTensorModule.coe_rTensor, hf]
  let g : (A ⊗[R] M) ⧸ N.toSubmodule →ₗ[A] Q :=
    N.toSubmodule.mapQ ((map f N).toSubmodule.restrictScalars A) h fun x hx ↦ by
      simpa [hh] using rTensor_mem_map f hx
  -- the composite is `A`-linear and factors through `⋀ᵏ (A ⊗[R] M) → ⋀ᵏ ((A ⊗[R] M) ⧸ N)`
  let T : ⋀[A]^k (A ⊗[R] M) →ₗ[A] ⋀[B]^k Q :=
    ((exteriorPower.map k (map f N).toSubmodule.mkQ).restrictScalars A) ∘ₗ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm.toLinearMap.restrictScalars A) ∘ₗ
      (AlgebraTensorModule.rTensor R (⋀[R]^k M) (Algebra.linearMap A B)) ∘ₗ
      (TauCeti.exteriorPower.equivBaseChange A k).toLinearMap
  let S : ⋀[A]^k ((A ⊗[R] M) ⧸ N.toSubmodule) →ₗ[A] ⋀[B]^k Q :=
    exteriorPower.alternatingMapLinearEquiv
      { toMultilinearMap :=
          ((exteriorPower.ιMulti B k).toMultilinearMap.restrictScalars A).compLinearMap
            fun _ ↦ g
        map_eq_zero_of_eq' := fun v i j hv hij ↦
          (exteriorPower.ιMulti B k).map_eq_zero_of_eq (fun l ↦ g (v l)) (by simp [hv]) hij }
  have hT (y) : T y = exteriorPower.map k (map f N).toSubmodule.mkQ
      ((TauCeti.exteriorPower.equivBaseChange B k).symm
        (f.toLinearMap.rTensor (⋀[R]^k M) (TauCeti.exteriorPower.equivBaseChange A k y))) := by
    simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, AlgebraTensorModule.coe_rTensor, hf]
  -- the vectors `1 ⊗ m` span `A ⊗[R] M` over `A`: it is the base change of `⊤`
  have hspan : Submodule.span A (Set.range (TensorProduct.mk R A M 1)) = ⊤ := by
    rw [← LinearMap.coe_range, LinearMap.range_eq_map, ← Submodule.baseChange_eq_span,
      Submodule.baseChange_top]
  have hTS : T = S ∘ₗ exteriorPower.map k N.toSubmodule.mkQ := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span_of_span A k (A ⊗[R] M) hspan) ?_
    rintro _ ⟨v, hv, rfl⟩
    choose m hm using fun i ↦ hv ⟨i, rfl⟩
    obtain rfl : v = fun i ↦ (1 : A) ⊗ₜ[R] m i := funext fun i ↦ (hm i).symm
    rw [hT, map_mkQ_rTensor_ιMulti, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    -- by definition, `S` sends the `A`-wedge of a family to the `B`-wedge of its images under `g`
    change _ = exteriorPower.ιMulti B k (fun i ↦ g (N.toSubmodule.mkQ (1 ⊗ₜ m i)))
    congr 1
    funext i
    -- by definition of `mapQ`, `g` sends the class of `1 ⊗ m` to the class of `h (1 ⊗ m)`
    change _ = (Submodule.Quotient.mk (h (1 ⊗ₜ m i)) : Q)
    simp [h]
  rw [← hT, hTS, LinearMap.comp_apply, hx, map_zero]

/-- **Naturality of the Plücker point.** For an `R`-algebra map `f : A → B`, the Plücker point of
the base change of `N` is the base change of the Plücker point of `N`. -/
theorem pluckerBaseChange_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    pluckerBaseChange (map f N) = map f (pluckerBaseChange N) := by
  refine (eq_of_le ?_).symm
  rw [map_toSubmodule_eq_span, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  rw [toSubmodule_pluckerBaseChange] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [SetLike.mem_coe, toSubmodule_pluckerBaseChange, Submodule.mem_map_equiv, LinearMap.mem_ker]
  exact map_mkQ_rTensor_eq_zero f N hx

end BaseChange

end Module.Grassmannian
