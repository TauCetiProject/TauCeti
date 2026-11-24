/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import TauCeti.Algebra.Star.Projection.Basic

/-!
# Entrywise unitization lemmas and projection paths for C⋆-matrices

This file provides entrywise kernel and inclusion identities for `CStarMatrix` over a unitization
`A⁺¹`, together with a descent lemma turning a unitary path in `CStarMatrix k k A⁺¹` into a
norm-continuous path of star projections in `CStarMatrix k k A`.

## Main declarations

* `CStarMatrix.map_inr_map_snd_of_map_fstHom_eq_zero`: a matrix over `A⁺¹` with zero scalar part
  is the entrywise image of its `A`-part.
* `CStarMatrix.map_fstHom_map_inr`: the scalar part of a matrix embedded via `Unitization.inr`
  vanishes.
* `CStarMatrix.exists_path_isStarProjection_of_unitization_unitary_conj`: a unitary path in
  `CStarMatrix k k A⁺¹` joining `1` to a conjugator of `P.map inr` into `Q.map inr` descends to a
  path of star projections from `P` to `Q`.
-/

public section

open scoped CStarAlgebra ComplexOrder unitInterval

namespace CStarMatrix

/-- Entrywise application of `Unitization.inrNonUnitalStarAlgHom` agrees with entrywise
`Unitization.inr`. -/
@[simp]
theorem map_inrNonUnitalStarAlgHom {m n R A : Type*} [CommSemiring R] [StarAddMonoid R]
    [NonUnitalSemiring A] [Star A] [Module R A] (M : CStarMatrix m n A) :
    M.map (Unitization.inrNonUnitalStarAlgHom R A) =
      M.map (Unitization.inr : A → Unitization R A) :=
  ext fun _ _ => Unitization.inrNonUnitalStarAlgHom_apply R A _

/-- A matrix over `A⁺¹` whose entrywise scalar part vanishes is the entrywise `inr` image of its
`A`-component. -/
theorem map_inr_map_snd_of_map_fstHom_eq_zero {m n A : Type*} [NonUnitalSemiring A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] {M : CStarMatrix m n A⁺¹}
    (hM : M.map (Unitization.fstHom ℂ A) = 0) :
    (M.map (fun x : A⁺¹ => x.snd)).map (Unitization.inr : A → A⁺¹) = M := by
  refine CStarMatrix.ext fun i j => Unitization.ext ?_ rfl
  simpa using (congrArg (fun X : CStarMatrix m n ℂ => X i j) hM).symm

/-- Entrywise scalar parts vanish after entrywise `Unitization.inr` inclusion. -/
@[simp]
theorem map_fstHom_map_inr {m n A : Type*} [NonUnitalSemiring A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (M : CStarMatrix m n A) :
    (M.map (Unitization.inr : A → A⁺¹)).map (Unitization.fstHom ℂ A) = 0 :=
  CStarMatrix.ext fun _ _ => by simp

/-- Conjugation by a unitary path in `CStarMatrix k k A⁺¹` joining `1` to a conjugator of
`P.map inr` to `Q.map inr` yields a norm-continuous path of star projections from `P` to `Q` in
`CStarMatrix k k A`. -/
theorem exists_path_isStarProjection_of_unitization_unitary_conj {k A : Type*} [Fintype k]
    [DecidableEq k] [NonUnitalCStarAlgebra A] {P Q : CStarMatrix k k A} (hP : IsStarProjection P)
    {u : unitary (CStarMatrix k k A⁺¹)}
    (hconj : (u : CStarMatrix k k A⁺¹) * P.map (Unitization.inr : A → A⁺¹) *
      star (u : CStarMatrix k k A⁺¹) = Q.map (Unitization.inr : A → A⁺¹))
    (hjoin : Joined (1 : unitary (CStarMatrix k k A⁺¹)) u) :
    ∃ γ : Path P Q, ∀ t : I, IsStarProjection (γ t) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder A⁺¹ := CStarAlgebra.spectralOrder A⁺¹
  let : StarOrderedRing A⁺¹ := CStarAlgebra.spectralOrderedRing A⁺¹
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  obtain ⟨δ⟩ := hjoin
  have hfst (t : I) :
      ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
        (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), CStarMatrix.map_mul (Unitization.fstHom ℂ A),
      map_inrNonUnitalStarAlgHom, map_fstHom_map_inr P, mul_zero, zero_mul]
  let f : I → CStarMatrix k k A := fun t =>
    ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
      (fun x : A⁺¹ => x.snd)
  have hf_inr (t : I) : CStarMatrix.mapₙₐ (n := k) ι (f t) =
      (δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹) := by
    rw [CStarMatrix.mapₙₐ_apply, CStarMatrix.mapₗ_apply, map_inrNonUnitalStarAlgHom]
    exact map_inr_map_snd_of_map_fstHom_eq_zero (hfst t)
  have hf_cont : Continuous f := by
    have hδ : Continuous (fun t : I => ((δ t : unitary (CStarMatrix k k A⁺¹)) :
        CStarMatrix k k A⁺¹)) := continuous_subtypeVal.comp δ.continuous
    exact (CStarMatrix.continuous_map (Unitization.continuous_snd (𝕜 := ℂ) (A := A))).comp
      ((hδ.mul continuous_const).mul hδ.star)
  have hinj : Function.Injective (CStarMatrix.mapₙₐ (n := k) ι) :=
    CStarMatrix.map_injective (Unitization.inr_injective (R := ℂ) (A := A))
  have hP' : IsStarProjection (P.map ι) := hP.map (CStarMatrix.mapₙₐ ι)
  refine ⟨⟨⟨f, hf_cont⟩, hinj (by simp [hf_inr 0, δ.source]),
    hinj (by simpa only [hf_inr 1, δ.target, CStarMatrix.mapₙₐ_apply, CStarMatrix.mapₗ_apply, ι,
      LinearMap.coe_ofClass, map_inrNonUnitalStarAlgHom] using hconj)⟩, fun t => ?_⟩
  have hproj' : IsStarProjection (CStarMatrix.mapₙₐ (n := k) ι (f t)) := by
    rw [hf_inr t]
    simpa only [Unitary.conjStarAlgAut_apply] using
      hP'.map (Unitary.conjStarAlgAut ℂ (CStarMatrix k k A⁺¹) (δ t))
  exact hproj'.of_map_injective hinj

end CStarMatrix
