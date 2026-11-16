/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Smooth
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ZMod.LocalRing
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.RingTheory.Henselian.Product
import TauCeti.RingTheory.Smooth.EtaleSlice

/-!
# Checks and sharpness examples for smooth lifting over Henselian pairs

* **Disconnected non-Noetherian bases**: over the infinite product `ℕ → ZMod 4` modulo its product
  maximal ideal, points of the smooth group scheme `SL₂` (relative dimension `3`) lift
  simultaneously across infinitely many factors.
* **Non-uniqueness in positive relative dimension**: unlike `TauCeti.HenselianRing.comp_bijective`
  for étale algebras, reduction `(ZMod 4[X] →ₐ[ZMod 4] ZMod 4) → ZMod 4[X] →ₐ[ZMod 4] _ ⧸ 𝔪` is
  surjective (`TauCeti.HenselianRing.comp_surjective`) and not injective (`X ↦ 0` vs `X ↦ 2`).
* **Failure without smoothness**: the ramified algebra `ZMod 4[X] ⧸ (X² - 2)` has a closed-fibre
  point `X ↦ 0` over `(ZMod 4) ⧸ (2)` with no lift to `ZMod 4`.
* **Failure without Henselianity (while étale-slice factorization still holds)**: over the
  non-Henselian pair `(ℤ, (5))`, every `(ℤ ⧸ (5))`-point of `SL₂` still factors through an étale
  `ℤ`-algebra (`Algebra.Smooth.exists_etale_algHom_comp_eq`), whereas universal smooth section
  lifting fails (`TauCeti.henselianRing_iff_forall_smooth_comp_surjective`).
-/

public section

open Polynomial IsLocalRing

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : IsLocalRing (ZMod 4) := inferInstanceAs (IsLocalRing (ZMod (2 ^ 2)))

-- Over the non-Noetherian infinite product `ℕ → ZMod 4`, every closed-fibre point of the smooth
-- coordinate algebra of `SL₂` over `ℤ` lifts to an `(ℕ → ZMod 4)`-point.
example (ψ : TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 2 →ₐ[ℤ]
    (ℕ → ZMod 4) ⧸ Ideal.pi (fun _ : ℕ ↦ maximalIdeal (ZMod 4))) :
    ∃ φ : TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 2 →ₐ[ℤ] (ℕ → ZMod 4),
      (Ideal.Quotient.mkₐ ℤ (Ideal.pi fun _ : ℕ ↦ maximalIdeal (ZMod 4))).comp φ = ψ :=
  TauCeti.HenselianRing.comp_surjective_of_algebra
    (Ideal.pi fun _ : ℕ ↦ maximalIdeal (ZMod 4)) ψ

-- In positive relative dimension (`A = (ZMod 4)[X]`), reduction modulo the maximal ideal is
-- surjective (`comp_surjective`) and NOT injective (`X ↦ 0` and `X ↦ 2` have the same reduction).
example :
    Function.Surjective
      ((Ideal.Quotient.mkₐ (ZMod 4) (maximalIdeal (ZMod 4))).comp :
        ((ZMod 4)[X] →ₐ[ZMod 4] ZMod 4) → (ZMod 4)[X] →ₐ[ZMod 4] ZMod 4 ⧸ maximalIdeal (ZMod 4)) ∧
    ¬ Function.Injective
      ((Ideal.Quotient.mkₐ (ZMod 4) (maximalIdeal (ZMod 4))).comp :
        ((ZMod 4)[X] →ₐ[ZMod 4] ZMod 4) →
          (ZMod 4)[X] →ₐ[ZMod 4] ZMod 4 ⧸ maximalIdeal (ZMod 4)) := by
  have : Algebra.Smooth (ZMod 4) (ZMod 4)[X] := {}
  refine ⟨TauCeti.HenselianRing.comp_surjective (maximalIdeal (ZMod 4)), fun hinj ↦ ?_⟩
  have h2mem : (2 : ZMod 4) ∈ maximalIdeal (ZMod 4) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact (ZMod.isUnit_iff_coprime 2 4).not.mpr (by decide)
  have heq : (Ideal.Quotient.mkₐ (ZMod 4) (maximalIdeal (ZMod 4))).comp (aeval (0 : ZMod 4)) =
      (Ideal.Quotient.mkₐ (ZMod 4) (maximalIdeal (ZMod 4))).comp (aeval (2 : ZMod 4)) := by
    ext
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr h2mem]
  have h02 := AlgHom.congr_fun (hinj heq) X
  simp only [aeval_X] at h02
  exact absurd h02 (by decide)

-- Without smoothness, lifting fails over a Henselian local ring: `(ZMod 4)[X] ⧸ (X² - 2)` has a
-- section `X ↦ 0` modulo `𝔪 = (2)`, and no section over `ZMod 4` since `x² ≠ 2` for `x ∈ ZMod 4`.
example :
    let Irel : Ideal (ZMod 4)[X] := Ideal.span {X ^ 2 - C (2 : ZMod 4)}
    (∃ ψ : ((ZMod 4)[X] ⧸ Irel) →ₐ[ZMod 4] ZMod 4 ⧸ maximalIdeal (ZMod 4),
      ∀ φ : ((ZMod 4)[X] ⧸ Irel) →ₐ[ZMod 4] ZMod 4,
        (Ideal.Quotient.mkₐ (ZMod 4) (maximalIdeal (ZMod 4))).comp φ ≠ ψ) := by
  intro Irel
  have h2mem : (2 : ZMod 4) ∈ maximalIdeal (ZMod 4) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact (ZMod.isUnit_iff_coprime 2 4).not.mpr (by decide)
  let q := Ideal.Quotient.mkₐ (ZMod 4) (maximalIdeal (ZMod 4))
  let ψ : ((ZMod 4)[X] ⧸ Irel) →ₐ[ZMod 4] ZMod 4 ⧸ maximalIdeal (ZMod 4) :=
    Ideal.Quotient.liftₐ Irel (q.comp (aeval 0)) fun p hp ↦ by
      rw [← RingHom.mem_ker]
      refine Ideal.span_le.mpr ?_ hp
      rintro _ ⟨rfl⟩
      simp [RingHom.mem_ker, q, Ideal.Quotient.eq_zero_iff_mem.mpr h2mem]
  refine ⟨ψ, fun φ _ ↦ ?_⟩
  have hx : φ (Ideal.Quotient.mk Irel X) ^ 2 = 2 := by
    have hzero : Ideal.Quotient.mk Irel (X ^ 2 - C (2 : ZMod 4)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have hmap := congrArg φ hzero
    rw [map_sub, map_pow, ← Polynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, map_sub, map_pow, AlgHom.commutes, map_zero, sub_eq_zero,
      Ideal.Quotient.algebraMap_eq] at hmap
    exact hmap
  generalize φ (Ideal.Quotient.mk Irel X) = y at hx
  exact absurd hx (by decide +revert)

-- Over the non-Henselian pair `(ℤ, (5))`, `exists_etale_algHom_comp_eq` still factors every
-- `(ℤ ⧸ (5))`-point of `SL₂` through an étale `ℤ`-algebra, whereas universal smooth section lifting
-- fails by `henselianRing_iff_forall_smooth_comp_surjective`.
example (ψ : TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 2 →ₐ[ℤ] ℤ ⧸ Ideal.span {(5 : ℤ)}) :
    (∃ (C : Type) (_ : CommRing C) (_ : Algebra ℤ C) (_ : Algebra.Etale ℤ C)
      (f : TauCeti.SpecialLinear.coordinateHopfAlgebra ℤ 2 →ₐ[ℤ] C)
      (ψC : C →ₐ[ℤ] ℤ ⧸ Ideal.span {(5 : ℤ)}), ψC.comp f = ψ) ∧
    ¬ ∀ (A : Type) [CommRing A] [Algebra ℤ A] [Algebra.Smooth ℤ A],
      Function.Surjective
        ((Ideal.Quotient.mkₐ ℤ (Ideal.span {(5 : ℤ)})).comp :
          (A →ₐ[ℤ] ℤ) → A →ₐ[ℤ] ℤ ⧸ Ideal.span {(5 : ℤ)}) := by
  refine ⟨Algebra.Smooth.exists_etale_algHom_comp_eq Ideal.Quotient.mk_surjective ψ, fun h ↦ ?_⟩
  have hhens := TauCeti.henselianRing_iff_forall_smooth_comp_surjective.mpr h
  have h5 := Ring.mem_jacobson_iff.mp (hhens.jac (Ideal.subset_span rfl)) 1
  norm_num [Int.isUnit_iff] at h5
