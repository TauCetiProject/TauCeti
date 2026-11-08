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

Let `R` be a commutative ring, `t` a unit of `R` and `n` a natural number invertible in `R`.
The *Kummer cover* `Spec R[x]/(x ^ n - t) ⟶ Spec R` extracts an `n`-th root of `t`; it is finite
étale (`TauCeti.standardTameCover_etale`). For `R = K[T, T⁻¹]` and `t = T` it is the power map
`z ↦ z ^ n` of the multiplicative group `𝔾_m` over `K`, whose fibre over `1` is the group
`μ_n` of `n`-th roots of unity. The fibres over `1` of the covers of all degrees `n` invertible
in `R` form the inverse system of the `μ_n` under the power maps. In characteristic zero its
limit is the Tate module of `𝔾_m`; in characteristic `p > 0` only the prime-to-`p` part is
reached, since `𝔾_m` then also has covers, such as Artin–Schreier covers, which are not Kummer
covers.

This file constructs the Kummer covers as finite étale `Spec R`-schemes, the maps between them
and their deck transformations, and computes them on geometric fibres:

* for `n ∣ m`, the map `kummerCoverMap` from the cover of degree `m` to the cover of degree `n`
  sends the root `x_n` to `x_m ^ (m / n)`; these maps are compatible with composition;
* the `n`-th roots of unity `ζ` of `R` act on `R[x]/(x ^ n - t)` by `x ↦ ζ x`
  (`TauCeti.standardTameCoverAut`), hence on the cover of degree `n` by deck transformations
  (`kummerCoverDeck`), compatibly with the maps `kummerCoverMap`;
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
* `TauCeti.FiniteEtaleScheme.kummerCoverDeck_one`, `TauCeti.FiniteEtaleScheme.kummerCoverDeck_mul`:
  the deck transformations form an action of the `n`-th roots of unity.
* `TauCeti.FiniteEtaleScheme.kummerCoverDeck_hom_comp_kummerCoverMap`: the maps between Kummer
  covers intertwine the deck transformations of `ζ` and of `ζ ^ (m / n)`.
* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquiv_map_kummerCoverDeck`: on fibres, the deck
  transformation of `ζ` is multiplication by the image of `ζ`.
* `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquivRootsOfUnity_map_kummerCoverMap`,
  `TauCeti.FiniteEtaleScheme.kummerCoverFiberEquivRootsOfUnity_map_kummerCoverDeck`: on the
  fibres `μ_n(Ω)` over `1`, the maps between covers are the power maps and the deck
  transformations are multiplications.

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

variable (n : ℕ) (hn : IsUnit (n : R))

-- An `abbrev`, so that maps out of the underlying algebra, such as points of geometric fibres,
-- are `R`-algebra maps out of `R[x]/(x ^ n - t)`.
/-- The Kummer algebra `R[x]/(x ^ n - t)` for a unit `t` of `R` and an exponent `n` invertible
in `R`, as a finite étale `R`-algebra. -/
noncomputable abbrev kummerAlgebra : CommAlgCat.FiniteEtale.{u} R :=
  haveI := standardTameCover_etale (A := R) t.isUnit hn
  haveI : Module.Finite R (standardTameCover R (t : R) n) := by
    rcases eq_or_ne n 0 with rfl | hn₀
    · -- For `n = 0` the ring `R` is trivial, since `0` is invertible in it.
      have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hn)
      exact (monic_of_subsingleton _).finite_adjoinRoot
    · have : NeZero n := ⟨hn₀⟩
      infer_instance
  CommAlgCat.FiniteEtale.of R (standardTameCover R (t : R) n)

/-- **The Kummer cover** `Spec R[x]/(x ^ n - t) ⟶ Spec R` of degree `n` along a unit `t`, as a
finite étale `Spec R`-scheme. It is étale because `n` and `t` are invertible in `R`. -/
-- The body is exposed: the fibre equivalences below are built from `specFiberEquiv`, whose domain
-- is the fibre of `(spec R).obj (op (kummerAlgebra t n hn))`, so their statements need to unfold
-- `kummerCover` by definition.
@[expose] noncomputable def kummerCover : FiniteEtaleScheme (Spec R) :=
  (spec R).obj (op (kummerAlgebra t n hn))

/-- The Kummer cover is the spectrum of the Kummer algebra. -/
theorem kummerCover_def : kummerCover t n hn = (spec R).obj (op (kummerAlgebra t n hn)) :=
  (rfl)

end Cover

section SpecMap

variable {n m k : ℕ} {hn : IsUnit (n : R)} {hm : IsUnit (m : R)} {hk : IsUnit (k : R)}

/-- The morphism of Kummer covers that `spec R` attaches to a morphism of Kummer algebras. -/
private noncomputable def kummerSpecMap (f : kummerAlgebra t n hn ⟶ kummerAlgebra t m hm) :
    kummerCover t m hm ⟶ kummerCover t n hn :=
  (spec R).map f.op

private theorem kummerSpecMap_id : kummerSpecMap t (𝟙 (kummerAlgebra t n hn)) = 𝟙 _ :=
  (spec R).map_id _

private theorem kummerSpecMap_comp (f : kummerAlgebra t n hn ⟶ kummerAlgebra t m hm)
    (g : kummerAlgebra t m hm ⟶ kummerAlgebra t k hk) :
    kummerSpecMap t g ≫ kummerSpecMap t f = kummerSpecMap t (f ≫ g) :=
  ((spec R).map_comp _ _).symm

end SpecMap

section Map

variable {n m : ℕ} (hn : IsUnit (n : R)) (hm : IsUnit (m : R))

/-- The morphism of finite étale algebras underlying `kummerCoverMap`. -/
private noncomputable def kummerAlgebraMap (h : n ∣ m) :
    kummerAlgebra t n hn ⟶ kummerAlgebra t m hm :=
  ObjectProperty.homMk (CommAlgCat.ofHom (standardTameCoverAlgHomOfDvd (t : R) h))

private theorem kummerAlgebraMap_hom_hom (h : n ∣ m) :
    (kummerAlgebraMap t hn hm h).hom.hom = standardTameCoverAlgHomOfDvd (t : R) h :=
  (rfl)

/-- For `n ∣ m`, the map of Kummer covers from degree `m` to degree `n`, given on coordinate
algebras by `x_n ↦ x_m ^ (m / n)`; on points, it raises an `m`-th root of `t` to the power
`m / n`. -/
noncomputable def kummerCoverMap (h : n ∣ m) : kummerCover t m hm ⟶ kummerCover t n hn :=
  kummerSpecMap t (kummerAlgebraMap t hn hm h)

/-- The map of Kummer covers of `n ∣ n` is the identity. -/
@[simp]
theorem kummerCoverMap_refl : kummerCoverMap t hn hn (dvd_refl n) = 𝟙 _ := by
  have : kummerAlgebraMap t hn hn (dvd_refl n) = 𝟙 _ := by
    ext : 2
    simp only [kummerAlgebraMap_hom_hom, ObjectProperty.FullSubcategory.id_hom, CommAlgCat.hom_id]
    rcases eq_or_ne n 0 with rfl | hn₀
    · -- For `n = 0` the ring `R` is trivial, and so is the Kummer algebra.
      have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hn)
      have : Subsingleton (standardTameCover R (t : R) 0) := Module.subsingleton R _
      exact AlgHom.ext fun _ ↦ Subsingleton.elim _ _
    · have : NeZero n := ⟨hn₀⟩
      exact standardTameCoverAlgHomOfDvd_refl (t : R)
  rw [kummerCoverMap, this, kummerSpecMap_id]

/-- The maps between Kummer covers are compatible with composition. -/
@[reassoc (attr := simp)]
theorem kummerCoverMap_comp {k : ℕ} (hk : IsUnit (k : R)) (h₁ : n ∣ m) (h₂ : m ∣ k) :
    kummerCoverMap t hm hk h₂ ≫ kummerCoverMap t hn hm h₁ =
      kummerCoverMap t hn hk (h₁.trans h₂) := by
  have : kummerAlgebraMap t hn hm h₁ ≫ kummerAlgebraMap t hm hk h₂ =
      kummerAlgebraMap t hn hk (h₁.trans h₂) := by
    ext : 2
    simp [kummerAlgebraMap_hom_hom, standardTameCoverAlgHomOfDvd_comp]
  rw [kummerCoverMap, kummerCoverMap, kummerCoverMap, kummerSpecMap_comp, this]

end Map

section Deck

variable {n : ℕ} (hn : IsUnit (n : R))

/-- The automorphism of the Kummer algebra underlying `kummerCoverDeck`. -/
private noncomputable def kummerAlgebraDeck (ζ : rootsOfUnity n R) :
    kummerAlgebra t n hn ≅ kummerAlgebra t n hn :=
  CommAlgCat.FiniteEtale.isoMk (standardTameCoverAut (t : R) ζ)

private theorem kummerAlgebraDeck_hom_hom_hom (ζ : rootsOfUnity n R) :
    (kummerAlgebraDeck t hn ζ).hom.hom.hom = (standardTameCoverAut (t : R) ζ : _ →ₐ[R] _) :=
  (rfl)

/-- The deck transformation of the Kummer cover of degree `n` attached to an `n`-th root of unity
`ζ` of `R`, given on coordinate algebras by `x ↦ ζ x` (`TauCeti.standardTameCoverAut`). -/
noncomputable def kummerCoverDeck (ζ : rootsOfUnity n R) :
    kummerCover t n hn ≅ kummerCover t n hn :=
  (spec R).mapIso (kummerAlgebraDeck t hn ζ).op

private theorem kummerCoverDeck_hom (ζ : rootsOfUnity n R) :
    (kummerCoverDeck t hn ζ).hom = kummerSpecMap t (kummerAlgebraDeck t hn ζ).hom :=
  (rfl)

/-- The deck transformation of the root of unity `1` is the identity. -/
@[simp]
theorem kummerCoverDeck_one : kummerCoverDeck t hn 1 = Iso.refl _ := by
  have : kummerAlgebraDeck t hn 1 = Iso.refl _ := by
    ext : 3
    exact AlgHom.ext fun x ↦ by simp [kummerAlgebraDeck_hom_hom_hom]
  ext : 1
  rw [kummerCoverDeck_hom, this, Iso.refl_hom, kummerSpecMap_id, Iso.refl_hom]

/-- The deck transformations compose according to the multiplication of roots of unity. -/
theorem kummerCoverDeck_mul (ζ ξ : rootsOfUnity n R) :
    kummerCoverDeck t hn (ζ * ξ) = kummerCoverDeck t hn ζ ≪≫ kummerCoverDeck t hn ξ := by
  have : kummerAlgebraDeck t hn (ζ * ξ) = kummerAlgebraDeck t hn ξ ≪≫ kummerAlgebraDeck t hn ζ := by
    ext : 3
    exact AlgHom.ext fun x ↦ by simp [kummerAlgebraDeck_hom_hom_hom]
  ext : 1
  rw [Iso.trans_hom, kummerCoverDeck_hom, kummerCoverDeck_hom, kummerCoverDeck_hom,
    kummerSpecMap_comp, this, Iso.trans_hom]

/-- For `n ∣ m`, the map of Kummer covers from degree `m` to degree `n` intertwines the deck
transformation of an `m`-th root of unity `ζ` with that of the `n`-th root of unity
`ζ ^ (m / n)`. -/
@[reassoc]
theorem kummerCoverDeck_hom_comp_kummerCoverMap {m : ℕ} (hm : IsUnit (m : R)) (h : n ∣ m)
    (ζ : rootsOfUnity m R) (ξ : rootsOfUnity n R) (hξ : (ξ : Rˣ) = ζ ^ (m / n)) :
    (kummerCoverDeck t hm ζ).hom ≫ kummerCoverMap t hn hm h =
      kummerCoverMap t hn hm h ≫ (kummerCoverDeck t hn ξ).hom := by
  have : kummerAlgebraMap t hn hm h ≫ (kummerAlgebraDeck t hm ζ).hom =
      (kummerAlgebraDeck t hn ξ).hom ≫ kummerAlgebraMap t hn hm h := by
    ext : 2
    simp [kummerAlgebraMap_hom_hom, kummerAlgebraDeck_hom_hom_hom,
      standardTameCoverAut_comp_standardTameCoverAlgHomOfDvd (t : R) h ζ ξ hξ]
  rw [kummerCoverDeck_hom, kummerCoverDeck_hom, kummerCoverMap, kummerSpecMap_comp,
    kummerSpecMap_comp, this]

end Deck

section Fiber

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
variable (n : ℕ) (hn : IsUnit (n : R))

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

variable {Ω n} {m : ℕ} (hm : IsUnit (m : R))

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
  rw [AlgHom.comp_apply, kummerAlgebraMap_hom_hom, standardTameCoverAlgHomOfDvd_root, map_pow]

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
  -- `kummerCoverDeck` is the spectrum of the isomorphism of algebras `kummerAlgebraDeck`.
  refine (DFunLike.congr_fun (specFiberEquiv_map R Ω (kummerAlgebraDeck t hn ζ).hom y)
    (AdjoinRoot.root _)).trans ?_
  rw [AlgHom.comp_apply, kummerAlgebraDeck_hom_hom_hom]
  simp [-AdjoinRoot.algebraMap_eq]

variable (Ω n)

/-- **The fibre over `1` of a Kummer cover is `μ_n`.** When `t` maps to `1` in the separably
closed field `Ω`, for instance for the power map `z ↦ z ^ n` of `𝔾_m` at a geometric point over
`1`, the geometric fibre of the Kummer cover of degree `n` is the group of `n`-th roots of unity
of `Ω`. -/
noncomputable def kummerCoverFiberEquivRootsOfUnity (h : algebraMap R Ω t = 1) :
    (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn) ≃
      rootsOfUnity n Ω :=
  -- `n ≠ 0`: otherwise `R` would be the zero ring, which has no map to the field `Ω`.
  haveI : NeZero n := ⟨by rintro rfl; simpa using hn.map (algebraMap R Ω)⟩
  (kummerCoverFiberEquiv t Ω n hn).trans
    { toFun ω := rootsOfUnity.mkOfPowEq (ω : Ω) (ω.2.trans h)
      invFun ζ := ⟨(ζ : Ωˣ), by simpa [h] using congrArg Units.val ((mem_rootsOfUnity n _).mp ζ.2)⟩
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

variable {Ω n}

/-- On the fibres `μ_n(Ω)` over `1`, the map of Kummer covers from degree `m` to degree `n ∣ m`
is the power map `ζ ↦ ζ ^ (m / n)`. -/
@[simp]
theorem kummerCoverFiberEquivRootsOfUnity_map_kummerCoverMap (h : algebraMap R Ω t = 1)
    (hd : n ∣ m)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t m hm)) :
    (kummerCoverFiberEquivRootsOfUnity t Ω n hn h
        ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
          (kummerCoverMap t hn hm hd) y) : Ωˣ) =
      (kummerCoverFiberEquivRootsOfUnity t Ω m hm h y : Ωˣ) ^ (m / n) :=
  Units.ext (by simp)

/-- On the fibre `μ_n(Ω)` over `1`, the deck transformation of an `n`-th root of unity `ζ` of `R`
is multiplication by the image of `ζ` in `μ_n(Ω)`. -/
@[simp]
theorem kummerCoverFiberEquivRootsOfUnity_map_kummerCoverDeck (h : algebraMap R Ω t = 1)
    (ζ : rootsOfUnity n R)
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).obj (kummerCover t n hn)) :
    kummerCoverFiberEquivRootsOfUnity t Ω n hn h
        ((fiber (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).map
          (kummerCoverDeck t hn ζ).hom y) =
      restrictRootsOfUnity (algebraMap R Ω) n ζ * kummerCoverFiberEquivRootsOfUnity t Ω n hn h y :=
  Subtype.ext (Units.ext (by simp))

end Fiber

end TauCeti.FiniteEtaleScheme
