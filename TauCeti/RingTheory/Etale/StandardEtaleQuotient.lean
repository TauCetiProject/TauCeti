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

Let `P` be a standard étale pair over a ring `A` and let `J` be an ideal of `A`. If the defining
equations of `P` hold modulo `J` at an element `a` of `A`, and the generator of `P.Ring` is
congruent to `a` modulo the extended ideal, then `P.Ring` has the same closed fibre as `A`: the
canonical map `A ⧸ J → P.Ring ⧸ J P.Ring` is bijective
(`StandardEtalePair.algebraMap_quotient_bijective_of_hasMap`).

A standard étale algebra `B` over a quotient `A = S ⧸ I` lifts to a flat `S`-algebra `C` with
`C ⧸ I C ≅ B` (`Algebra.IsStandardEtale.exists_flat_lift`): if `B = (A[X] ⧸ (f))[1/g]` with `f`
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

/-- A standard étale algebra has the same closed fibre as its base along an ideal `J`, provided
its defining equations hold modulo `J` at an element `a` of the base and its generator is
congruent to `a` modulo the extended ideal. -/
theorem algebraMap_quotient_bijective_of_hasMap (P : StandardEtalePair A) (J : Ideal A) {a : A}
    (ha : P.HasMap (Ideal.Quotient.mk J a))
    (hX : P.X - algebraMap A P.Ring a ∈ J.map (algebraMap A P.Ring)) :
    Function.Bijective (algebraMap (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))) := by
  -- The map `X ↦ a` is a retraction onto the closed fibre of `A`, and it is inverse to the
  -- canonical map because the generator is congruent to `a`.
  let σ := P.lift _ ha
  have hker : J.map (algebraMap A P.Ring) ≤ RingHom.ker (σ : P.Ring →+* A ⧸ J) :=
    Ideal.map_le_iff_le_comap.mpr fun j hj ↦ by
      simpa [σ] using Ideal.Quotient.eq_zero_iff_mem.mpr hj
  let σbar := Ideal.Quotient.lift _ (σ : P.Ring →+* A ⧸ J) fun y hy ↦
    RingHom.mem_ker.mp (hker hy)
  have hright : (IsScalarTower.toAlgHom A (A ⧸ J) (P.Ring ⧸ J.map (algebraMap A P.Ring))).comp σ =
      Ideal.Quotient.mkₐ A (J.map (algebraMap A P.Ring)) := by
    apply P.hom_ext
    simpa [σ, P.lift_X] using (Ideal.Quotient.eq.mpr hX).symm
  refine Function.bijective_iff_has_inverse.mpr ⟨σbar, fun r ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact σ.commutes r
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simpa [σbar] using DFunLike.congr_fun hright y

end StandardEtalePair

namespace Algebra.IsStandardEtale

open Polynomial

universe u

/-- A standard étale algebra `B` over a quotient `A` of `S` lifts to a flat `S`-algebra: there is a
flat `S`-algebra `C` with a surjection `C → B`, compatible with `S → A → B`, whose kernel is the
extension of the kernel of `S → A`. -/
theorem exists_flat_lift {S : Type u} {A B : Type*} [CommRing S] [CommRing A] [CommRing B]
    [Algebra S A] [Algebra A B] (hS : Function.Surjective (algebraMap S A)) [IsStandardEtale A B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra S C) (_ : Module.Flat S C) (φ : C →+* B),
      Function.Surjective φ ∧
      (∀ s, φ (algebraMap S C s) = algebraMap A B (algebraMap S A s)) ∧
      RingHom.ker φ = (RingHom.ker (algebraMap S A)).map (algebraMap S C) := by
  obtain ⟨⟨⟨f, hfm, g, hcond⟩, x, hx, hbij⟩⟩ := nonempty_standardEtalePresentation (R := A) (S := B)
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

end Algebra.IsStandardEtale
