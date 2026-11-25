/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale

import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Algebra
import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Standard étale algebras and quotients of the base

Let `P` be a standard étale pair over a ring `A`, let `J` be an ideal of `A`, and suppose the
generator of `P.Ring` is congruent to an element `a` of `A` modulo the extended ideal. Then
`P.Ring` has the same closed fibre as `A`, that is, the canonical map
`A ⧸ J → P.Ring ⧸ J P.Ring` is bijective, if and only if the defining equations of `P` hold
modulo `J` at `a` (`StandardEtalePair.algebraMap_quotient_bijective_iff_hasMap`).

A standard étale algebra `B` over a quotient `A = S ⧸ I` lifts to a flat `S`-algebra `C` with
`C ⧸ I C ≅ B` (`TauCeti.exists_flat_lift_of_isStandardEtale`): if `B = (A[X] ⧸ (f))[1/g]` with `f`
monic, lift `f` to a monic polynomial `F` and `g` to a polynomial `G` over `S`, and take
`C = (S[X] ⧸ (F))[1/G]`. The surjection `C → B` has kernel `I C`, and flatness of `C` over `S`
identifies its conormal module as `I C/(I C)² ≃ B ⊗[A] I/I²`.

## References

* Mathlib's `Mathlib.RingTheory.Etale.StandardEtale`, for `StandardEtalePair` and its
  universal mapping API.
-/

public section

namespace StandardEtalePair

variable {A : Type*} [CommRing A]

/-- If the generator of a standard étale algebra is congruent to an element `a` of the base
modulo the extended ideal of `J`, then the algebra has the same closed fibre as its base along `J`
if and only if its defining equations hold modulo `J` at `a`. -/
theorem algebraMap_quotient_bijective_iff_hasMap (P : StandardEtalePair A) (J : Ideal A) {a : A}
    (hX : P.X - algebraMap A P.Ring a ∈ J.map (algebraMap A P.Ring)) :
    Function.Bijective (algebraMap (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))) ↔
      P.HasMap (Ideal.Quotient.mk J a) := by
  -- The generator and `a` have the same image in the closed fibre of `P.Ring`.
  have hXa : Ideal.Quotient.mk (J.map (algebraMap A P.Ring)) P.X =
      algebraMap (A ⧸ J) _ (Ideal.Quotient.mk J a) :=
    Ideal.Quotient.eq.mpr hX
  refine ⟨fun h ↦ ?_, fun ha ↦ ?_⟩
  · -- The inverse of the canonical map carries the generator of the closed fibre to `a`.
    have hf : Function.Bijective
        (IsScalarTower.toAlgHom A (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))) := by
      rwa [IsScalarTower.coe_toAlgHom']
    have := (P.hasMap_X.map (Ideal.Quotient.mkₐ A _)).map (AlgEquiv.ofBijective _ hf).symm.toAlgHom
    rwa [Ideal.Quotient.mkₐ_eq_mk, hXa, ← IsScalarTower.coe_toAlgHom' A, AlgEquiv.coe_toAlgHom,
      AlgEquiv.ofBijective_symm_apply_apply] at this
  -- The map `X ↦ a` factors through the closed fibre of `P.Ring`, and the factored map is
  -- inverse to the canonical map because the generator is congruent to `a`.
  have hker : J.map (algebraMap A P.Ring) ≤ RingHom.ker (P.lift _ ha) :=
    Ideal.map_le_iff_le_comap.mpr fun j hj ↦ by
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hj
  let σ := Ideal.Quotient.liftₐ _ (P.lift _ ha) fun y hy ↦ RingHom.mem_ker.mp (hker hy)
  have hright : (IsScalarTower.toAlgHom A (A ⧸ J) _).comp σ = AlgHom.id A _ :=
    Ideal.Quotient.algHom_ext _ <| P.hom_ext <| by
      simpa [AlgHom.comp_assoc, σ, Ideal.Quotient.liftₐ_comp] using hXa.symm
  refine Function.bijective_iff_has_inverse.mpr ⟨σ, fun r ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [σ]
  · simpa using DFunLike.congr_fun hright y

end StandardEtalePair

namespace TauCeti

open Algebra Polynomial

universe u

/-- A standard étale algebra `B` over a quotient `A` of `S` lifts to a flat `S`-algebra: there is a
flat `S`-algebra `C` with a surjection `C → B`, compatible with `S → A → B`, whose kernel is the
extension of the kernel of `S → A`. -/
theorem exists_flat_lift_of_isStandardEtale {S : Type u} {A B : Type*} [CommRing S] [CommRing A]
    [CommRing B] [Algebra S A] [Algebra A B] (hS : Function.Surjective (algebraMap S A))
    [IsStandardEtale A B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra S C) (_ : Module.Flat S C) (φ : C →+* B),
      Function.Surjective φ ∧
      (∀ s, φ (algebraMap S C s) = algebraMap A B (algebraMap S A s)) ∧
      RingHom.ker φ = (RingHom.ker (algebraMap S A)).map (algebraMap S C) := by
  obtain ⟨⟨⟨f, hfm, g, hcond⟩, x, hx, hbij⟩⟩ :=
    IsStandardEtale.nonempty_standardEtalePresentation (R := A) (S := B)
  let π := algebraMap S A
  obtain ⟨f, rfl, -, hf⟩ := lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hS f) hfm
  obtain ⟨g, rfl⟩ := Polynomial.map_surjective π hS g
  let Pe : StandardEtalePresentation A B := ⟨⟨f.map π, hfm, g.map π, hcond⟩, x, hx, hbij⟩
  let e : B ≃ₐ[A] Localization.Away (AdjoinRoot.mk (f.map π) (g.map π)) :=
    Pe.equivRing.trans Pe.P.equivAwayAdjoinRoot
  -- The lift `C = (S[X] ⧸ (f))[1/g]` is flat: `S[X] ⧸ (f)` is free since `f` is monic.
  let C := Localization.Away (AdjoinRoot.mk f g)
  have : Module.Free S (AdjoinRoot f) := hf.free_adjoinRoot
  have : Module.Flat S C := .trans S (AdjoinRoot f) C
  let ρ := AdjoinRoot.map π f (f.map π) dvd_rfl
  have : IsLocalization.Away (ρ (AdjoinRoot.mk f g))
      (Localization.Away (AdjoinRoot.mk (f.map π) (g.map π))) := by
    rw [AdjoinRoot.map_mk]
    infer_instance
  let φ₀ : C →+* Localization.Away (AdjoinRoot.mk (f.map π) (g.map π)) :=
    IsLocalization.Away.map _ _ ρ (AdjoinRoot.mk f g)
  refine ⟨C, inferInstance, inferInstance, inferInstance, e.symm.toRingHom.comp φ₀,
    e.symm.surjective.comp (IsLocalization.map_surjective_of_surjective _ _ _
      (AdjoinRoot.map_surjective hS _)), fun s ↦ ?_, ?_⟩
  · have hφ₀ : φ₀ (algebraMap S C s) =
        algebraMap A (Localization.Away (AdjoinRoot.mk (f.map π) (g.map π))) (π s) := by
      rw [IsScalarTower.algebraMap_apply S (AdjoinRoot f) C,
        IsScalarTower.algebraMap_apply A (AdjoinRoot (f.map π))]
      simp [φ₀, IsLocalization.Away.map, IsLocalization.map_eq, AdjoinRoot.algebraMap_eq, ρ]
    calc
      (e.symm.toRingHom.comp φ₀) (algebraMap S C s) =
          e.symm (algebraMap A _ (π s)) := by simp [hφ₀]
      _ = algebraMap A B (algebraMap S A s) := e.symm.commutes _
  · have hker : RingHom.ker φ₀ = (RingHom.ker ρ).map (algebraMap (AdjoinRoot f) C) :=
      IsLocalization.ker_map _ _ (Submonoid.map_powers ρ (AdjoinRoot.mk f g))
    rw [RingHom.ker_comp_of_injective _ e.symm.injective, hker,
      AdjoinRoot.ker_map_map_of_surjective hS, Ideal.map_map, ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end TauCeti
