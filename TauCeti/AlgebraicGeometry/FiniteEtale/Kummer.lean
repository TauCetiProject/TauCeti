/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.AffineFiber
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic

import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Kummer covers and their geometric fibres

Let `R` be a commutative ring, `t` a unit of `R` and `n ≠ 0` a natural number invertible in `R`.
The *Kummer cover* `Spec R[x]/(x ^ n - t) ⟶ Spec R` extracts an `n`-th root of `t`; it is finite
étale (`TauCeti.standardTameCover_etale`). For `R = K[T, T⁻¹]` and `t = T` it is the power map
`z ↦ z ^ n` of the multiplicative group `𝔾_m` over `K`, whose fibre over `1` is the group
`μ_n` of `n`-th roots of unity. These covers and their fibres are the building blocks of the
étale fundamental group of `𝔾_m`: the fibres over `1` of the covers of all degrees form the
inverse system of the `μ_n` under the power maps, whose limit is the Tate module.

This file constructs the Kummer covers as finite étale `Spec R`-schemes, the maps between them
and their deck transformations, and computes them on geometric fibres:

* for `n ∣ m`, the map `kummerCoverMap` from the cover of degree `m` to the cover of degree `n`
  sends the root `x_n` to `x_m ^ (m / n)`; these maps are compatible with composition;
* the `n`-th roots of unity `ζ` of `R` act on `R[x]/(x ^ n - t)` by `x ↦ ζ x` (`kummerAlgEquiv`),
  hence on the cover of degree `n` by deck transformations (`kummerCoverDeck`);
* at a geometric point `Spec Ω ⟶ Spec R`, given by an `R`-algebra structure on a separably closed
  field `Ω`, the fibre of the cover of degree `n` is the set of `n`-th roots of the image of `t`
  in `Ω` (`kummerCoverFiberEquiv`). The map `kummerCoverMap` acts on fibres by `ω ↦ ω ^ (m / n)`
  and the deck transformation of `ζ` by multiplication by the image of `ζ`. When `t` maps to `1`
  the fibre is the group `μ_n(Ω)` of `n`-th roots of unity of `Ω`
  (`kummerCoverFiberEquivRootsOfUnity`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.kummerAlgebra t n hn`: the finite étale `R`-algebra `R[x]/(x ^ n - t)`.
* `TauCeti.FiniteEtaleScheme.kummerCover t n hn`: its spectrum, a finite étale `Spec R`-scheme.
* `TauCeti.FiniteEtaleScheme.kummerCoverMap`: for `n ∣ m`, the map from the Kummer cover of degree
  `m` to that of degree `n`.
* `TauCeti.FiniteEtaleScheme.kummerAlgEquiv`: the action of the `n`-th roots of unity of `R` on
  `R[x]/(x ^ n - t)` by `x ↦ ζ x`.
* `TauCeti.FiniteEtaleScheme.kummerCoverDeck`: the automorphism `x ↦ ζ x` of the Kummer cover of
  degree `n`, for an `n`-th root of unity `ζ` of `R`.
* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv`: the geometric fibre of the Kummer cover of
  degree `n` is the set of `n`-th roots of `t` in `Ω`.
* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquivRootsOfUnity`: when `t` maps to `1` in `Ω`,
  that fibre is `μ_n(Ω)`.

## Main results

* `TauCeti.FiniteEtaleScheme.kummerCoverMap_comp`: the maps between Kummer covers are compatible
  with composition.
* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv_map_kummerCoverMap`: on fibres, the map from
  degree `m` to degree `n` is `ω ↦ ω ^ (m / n)`.
* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv_map_kummerCoverDeck`: on fibres, the deck
  transformation of `ζ` is multiplication by the image of `ζ`.

## References

* A. Grothendieck, *SGA 1*, Exposé XIII, §2.
* T. Szamuely, *Galois groups and fundamental groups*, Example 4.6.12 (2).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite Polynomial

universe u

namespace TauCeti.FiniteEtaleScheme

variable {R : CommRingCat.{u}} (t : Rˣ)

section Cover

variable (n : ℕ) [NeZero n] (hn : IsUnit (n : R))

/-- The Kummer algebra `R[x]/(x ^ n - t)` for a unit `t` of `R` and an exponent `n ≠ 0` invertible
in `R`, as a finite étale `R`-algebra. It is reducible, so that maps out of its underlying algebra,
such as points of geometric fibres, are `R`-algebra maps out of `R[x]/(x ^ n - t)`. -/
noncomputable abbrev kummerAlgebra : CommAlgCat.FiniteEtale.{u} R :=
  haveI := standardTameCover_etale (A := R) t.isUnit hn
  CommAlgCat.FiniteEtale.of R (standardTameCover R (t : R) n)

/-- **The Kummer cover** `Spec R[x]/(x ^ n - t) ⟶ Spec R` of degree `n` along a unit `t`, as a
finite étale `Spec R`-scheme. It is étale because `n` and `t` are invertible in `R`. The body is
exposed so that the fibre computations below can be stated through `specCompFiberIso`. -/
@[expose] noncomputable def kummerCover : FiniteEtaleScheme (Spec R) :=
  (spec R).obj (op (kummerAlgebra t n hn))

/-- The Kummer cover is the spectrum of the Kummer algebra. -/
theorem kummerCover_def : kummerCover t n hn = (spec R).obj (op (kummerAlgebra t n hn)) :=
  (rfl)

end Cover

section Map

variable {n m : ℕ}

/-- For `n ∣ m`, the `R`-algebra map `R[x]/(x ^ n - t) → R[x]/(x ^ m - t)` sending `x` to
`x ^ (m / n)`. -/
noncomputable def kummerAlgHom (h : n ∣ m) :
    standardTameCover R (t : R) n →ₐ[R] standardTameCover R (t : R) m :=
  (AdjoinRoot.algHomEquiv _ _).symm ⟨AdjoinRoot.root _ ^ (m / n), by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← pow_mul, Nat.div_mul_cancel h,
      AdjoinRoot.root_X_pow_sub_C_pow, AdjoinRoot.algebraMap_eq, sub_self]⟩

/-- The map `kummerAlgHom` sends the root `x` to `x ^ (m / n)`. -/
@[simp]
theorem kummerAlgHom_root (h : n ∣ m) :
    kummerAlgHom t h (AdjoinRoot.root _) = AdjoinRoot.root _ ^ (m / n) :=
  AdjoinRoot.algHomEquiv_symm_apply_root _

/-- The map `kummerAlgHom` of `n ∣ n` is the identity. -/
@[simp]
theorem kummerAlgHom_refl [NeZero n] : kummerAlgHom t (dvd_refl n) = AlgHom.id R _ :=
  AdjoinRoot.algHom_ext (by simp [Nat.div_self (Nat.pos_of_neZero n)])

/-- The maps `kummerAlgHom` are compatible with composition. -/
theorem kummerAlgHom_comp {k : ℕ} (h₁ : n ∣ m) (h₂ : m ∣ k) :
    (kummerAlgHom t h₂).comp (kummerAlgHom t h₁) = kummerAlgHom t (h₁.trans h₂) := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, kummerAlgHom_root, map_pow, kummerAlgHom_root, kummerAlgHom_root,
    ← pow_mul, Nat.div_mul_div h₂ h₁]

variable [NeZero n] [NeZero m] (hn : IsUnit (n : R)) (hm : IsUnit (m : R))

/-- The morphism of finite étale algebras underlying `kummerCoverMap`. -/
private noncomputable def kummerAlgebraMap (h : n ∣ m) :
    kummerAlgebra t n hn ⟶ kummerAlgebra t m hm :=
  ObjectProperty.homMk (CommAlgCat.ofHom (kummerAlgHom t h))

private theorem kummerAlgebraMap_hom_hom (h : n ∣ m) :
    (kummerAlgebraMap t hn hm h).hom.hom = kummerAlgHom t h :=
  (rfl)

/-- For `n ∣ m`, the map of Kummer covers from degree `m` to degree `n`, given on coordinate
algebras by `x_n ↦ x_m ^ (m / n)`; on points, it raises an `m`-th root of `t` to the power
`m / n`. -/
noncomputable def kummerCoverMap (h : n ∣ m) : kummerCover t m hm ⟶ kummerCover t n hn :=
  (spec R).map (kummerAlgebraMap t hn hm h).op

/-- The map of Kummer covers of `n ∣ n` is the identity. -/
@[simp]
theorem kummerCoverMap_refl : kummerCoverMap t hn hn (dvd_refl n) = 𝟙 _ := by
  have : kummerAlgebraMap t hn hn (dvd_refl n) = 𝟙 _ := by
    ext : 2
    rw [kummerAlgebraMap_hom_hom, kummerAlgHom_refl]
    rfl
  rw [kummerCoverMap, this, op_id, (spec R).map_id]
  -- `kummerCover t n hn` is by definition `(spec R).obj (op (kummerAlgebra t n hn))`.
  rfl

/-- The maps between Kummer covers are compatible with composition. -/
@[reassoc (attr := simp)]
theorem kummerCoverMap_comp {k : ℕ} [NeZero k] (hk : IsUnit (k : R)) (h₁ : n ∣ m) (h₂ : m ∣ k) :
    kummerCoverMap t hm hk h₂ ≫ kummerCoverMap t hn hm h₁ =
      kummerCoverMap t hn hk (h₁.trans h₂) := by
  have : kummerAlgebraMap t hn hm h₁ ≫ kummerAlgebraMap t hm hk h₂ =
      kummerAlgebraMap t hn hk (h₁.trans h₂) := by
    ext : 2
    rw [kummerAlgebraMap_hom_hom, ← kummerAlgHom_comp t h₁ h₂]
    rfl
  exact ((spec R).map_comp _ _).symm.trans (congrArg (fun f ↦ (spec R).map f.op) this)

end Map

section Deck

variable {n : ℕ}

/-- The `R`-algebra endomorphism `x ↦ ζ x` of `R[x]/(x ^ n - t)`, for an `n`-th root of unity
`ζ` of `R`. -/
private noncomputable def kummerMulAlgHom (ζ : rootsOfUnity n R) :
    standardTameCover R (t : R) n →ₐ[R] standardTameCover R (t : R) n :=
  (AdjoinRoot.algHomEquiv _ _).symm ⟨algebraMap R _ (ζ : Rˣ) * AdjoinRoot.root _, by
    rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, ← map_pow, ← Units.val_pow_eq_pow_val,
      (mem_rootsOfUnity n _).mp ζ.2, Units.val_one, map_one, one_mul,
      AdjoinRoot.root_X_pow_sub_C_pow, AdjoinRoot.algebraMap_eq, sub_self]⟩

private theorem kummerMulAlgHom_root (ζ : rootsOfUnity n R) :
    kummerMulAlgHom t ζ (AdjoinRoot.root _) =
      algebraMap R (standardTameCover R (t : R) n) (ζ : Rˣ) * AdjoinRoot.root _ :=
  AdjoinRoot.algHomEquiv_symm_apply_root _

private theorem kummerMulAlgHom_comp (ζ ξ : rootsOfUnity n R) :
    (kummerMulAlgHom t ζ).comp (kummerMulAlgHom t ξ) = kummerMulAlgHom t (ζ * ξ) := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, kummerMulAlgHom_root, map_mul, AlgHom.commutes, kummerMulAlgHom_root,
    kummerMulAlgHom_root, Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

private theorem kummerMulAlgHom_one : kummerMulAlgHom t (1 : rootsOfUnity n R) = AlgHom.id R _ :=
  AdjoinRoot.algHom_ext (by
    rw [kummerMulAlgHom_root, OneMemClass.coe_one, Units.val_one, map_one, one_mul,
      AlgHom.id_apply])

/-- The action of the `n`-th roots of unity of `R` on `R[x]/(x ^ n - t)` by the `R`-algebra
automorphisms `x ↦ ζ x`. -/
noncomputable def kummerAlgEquiv :
    rootsOfUnity n R →* (standardTameCover R (t : R) n ≃ₐ[R] standardTameCover R (t : R) n) where
  toFun ζ := AlgEquiv.ofAlgHom (kummerMulAlgHom t ζ) (kummerMulAlgHom t ζ⁻¹)
    (by rw [kummerMulAlgHom_comp, mul_inv_cancel, kummerMulAlgHom_one])
    (by rw [kummerMulAlgHom_comp, inv_mul_cancel, kummerMulAlgHom_one])
  map_one' := AlgEquiv.ext fun x ↦ DFunLike.congr_fun (kummerMulAlgHom_one t) x
  map_mul' ζ ξ := AlgEquiv.ext fun x ↦ (DFunLike.congr_fun (kummerMulAlgHom_comp t ζ ξ) x).symm

/-- The automorphism `kummerAlgEquiv t ζ` sends the root `x` to `ζ x`. -/
@[simp]
theorem kummerAlgEquiv_root (ζ : rootsOfUnity n R) :
    kummerAlgEquiv t ζ (AdjoinRoot.root _) =
      algebraMap R (standardTameCover R (t : R) n) (ζ : Rˣ) * AdjoinRoot.root _ :=
  kummerMulAlgHom_root t ζ

variable [NeZero n] (hn : IsUnit (n : R))

/-- The deck transformation of the Kummer cover of degree `n` attached to an `n`-th root of unity
`ζ` of `R`, given on coordinate algebras by `x ↦ ζ x`. -/
noncomputable def kummerCoverDeck (ζ : rootsOfUnity n R) :
    kummerCover t n hn ≅ kummerCover t n hn :=
  (spec R).mapIso (CommAlgCat.FiniteEtale.isoMk (S := kummerAlgebra t n hn)
    (T := kummerAlgebra t n hn) (kummerAlgEquiv t ζ)).op

end Deck

section Fiber

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
variable (n : ℕ) [NeZero n] (hn : IsUnit (n : R))

/-- **The geometric fibre of a Kummer cover.** At the geometric point `Spec Ω ⟶ Spec R` given by
an `R`-algebra structure on a separably closed field `Ω`, the fibre of the Kummer cover of degree
`n` along `t` is the set of `n`-th roots of the image of `t` in `Ω`. A point of the fibre goes to
the value at the root `x` of the corresponding `R`-algebra map `R[x]/(x ^ n - t) → Ω`
(`coe_kummerCoverFiberEquiv_apply`). -/
noncomputable def kummerCoverFiberEquiv :
    (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn) ≃
      {ω : Ω // ω ^ n = algebraMap R Ω t} :=
  (specFiberEquiv R Ω (kummerAlgebra t n hn)).trans <|
    (AdjoinRoot.algHomEquiv Ω (X ^ n - C (t : R))).trans <|
      Equiv.subtypeEquivRight fun ω ↦ by
        rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]

/-- The `n`-th root of `t` attached to a point of the fibre of the Kummer cover is the value at
the root of the corresponding `R`-algebra map `R[x]/(x ^ n - t) → Ω` (`specFiberEquiv`). -/
theorem coe_kummerCoverFiberEquiv_apply
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    (kummerCoverFiberEquiv t Ω n hn y : Ω) =
      specFiberEquiv R Ω (kummerAlgebra t n hn) y (AdjoinRoot.root _) :=
  -- `Equiv.trans` and `Equiv.subtypeEquivRight` unfold to the value of `AdjoinRoot.algHomEquiv`.
  AdjoinRoot.coe_algHomEquiv_apply _

variable {Ω n} {m : ℕ} [NeZero m] (hm : IsUnit (m : R))

/-- On geometric fibres, the map of Kummer covers from degree `m` to degree `n ∣ m` raises an
`m`-th root of `t` to the power `m / n`. -/
@[simp]
theorem kummerCoverFiberEquiv_map_kummerCoverMap (h : n ∣ m)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t m hm)) :
    (kummerCoverFiberEquiv t Ω n hn
        ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
          (kummerCoverMap t hn hm h) y) : Ω) =
      (kummerCoverFiberEquiv t Ω m hm y : Ω) ^ (m / n) := by
  rw [coe_kummerCoverFiberEquiv_apply, coe_kummerCoverFiberEquiv_apply]
  -- `kummerCoverMap` is the spectrum of `kummerAlgebraMap`, so `specFiberEquiv_map` applies.
  refine (DFunLike.congr_fun (specFiberEquiv_map R Ω (kummerAlgebraMap t hn hm h) y)
    (AdjoinRoot.root _)).trans ?_
  rw [AlgHom.comp_apply, kummerAlgebraMap_hom_hom, kummerAlgHom_root, map_pow]

/-- On geometric fibres, the deck transformation of an `n`-th root of unity `ζ` of `R` multiplies
an `n`-th root of `t` by the image of `ζ`. -/
@[simp]
theorem kummerCoverFiberEquiv_map_kummerCoverDeck (ζ : rootsOfUnity n R)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    (kummerCoverFiberEquiv t Ω n hn
        ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
          (kummerCoverDeck t hn ζ).hom y) : Ω) =
      algebraMap R Ω (ζ : Rˣ) * kummerCoverFiberEquiv t Ω n hn y := by
  rw [coe_kummerCoverFiberEquiv_apply, coe_kummerCoverFiberEquiv_apply]
  -- `kummerCoverDeck` is the spectrum of the isomorphism of algebras `kummerAlgEquiv`.
  refine (DFunLike.congr_fun (specFiberEquiv_map R Ω (CommAlgCat.FiniteEtale.isoMk
    (S := kummerAlgebra t n hn) (T := kummerAlgebra t n hn) (kummerAlgEquiv t ζ)).hom y)
    (AdjoinRoot.root _)).trans ?_
  simp [-AdjoinRoot.algebraMap_eq]

variable (Ω n)

/-- **The fibre over `1` of a Kummer cover is `μ_n`.** When `t` maps to `1` in the separably
closed field `Ω`, for instance for the power map `z ↦ z ^ n` of `𝔾_m` at a geometric point over
`1`, the geometric fibre of the Kummer cover of degree `n` is the group of `n`-th roots of unity
of `Ω`. -/
noncomputable def kummerCoverFiberEquivRootsOfUnity (h : algebraMap R Ω t = 1) :
    (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn) ≃
      rootsOfUnity n Ω :=
  (kummerCoverFiberEquiv t Ω n hn).trans
    { toFun ω := rootsOfUnity.mkOfPowEq (ω : Ω) (ω.2.trans h)
      invFun ζ := ⟨(ζ : Ωˣ), by rw [h, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity n _).mp ζ.2,
        Units.val_one]⟩
      left_inv _ := rfl
      right_inv _ := rootsOfUnity.coe_injective rfl }

/-- The root of unity attached to a point of the fibre over `1` of the Kummer cover is the
corresponding `n`-th root of `t`. -/
@[simp]
theorem coe_kummerCoverFiberEquivRootsOfUnity_apply (h : algebraMap R Ω t = 1)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    ((kummerCoverFiberEquivRootsOfUnity t Ω n hn h y : Ωˣ) : Ω) =
      kummerCoverFiberEquiv t Ω n hn y :=
  (rfl)

end Fiber

end TauCeti.FiniteEtaleScheme
