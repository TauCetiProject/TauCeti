/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Henselian.Etale
import TauCeti.RingTheory.Henselization.Henselian
import Mathlib.RingTheory.Etale.Pi

/-!
# Examples of étale section lifting over henselian pairs

These examples exercise specified residue sections, arbitrary scalar bases, a localization
which is not module-finite, a nonlocal base, and the necessity of henselianity.
-/

namespace TauCeti

-- A split cover has a unique lift for each specified residue section.
example {R : Type*} [CommRing R] (I : Ideal R) [HenselianRing R I]
    (ψ : (Fin 2 → R) →ₐ[R] R ⧸ I) :
    ∃! φ : (Fin 2 → R) →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp φ = ψ := by
  obtain ⟨φ, hφ⟩ := (HenselianRing.comp_bijective I).2 ψ
  exact ⟨φ, hφ, fun φ' hφ' ↦ (HenselianRing.comp_bijective I).1 (hφ'.trans hφ.symm)⟩

-- The henselization along five admits the residue point of the non-finite étale algebra ℤ[1/2].
example :
    let I := Ideal.span {(5 : ℤ)}
    let A := Henselization.algebra I
    let J := Henselization.extended I
    ∃ φ : Localization.Away (2 : ℤ) →ₐ[ℤ] A,
      Ideal.Quotient.mk J (φ (IsLocalization.Away.invSelf (2 : ℤ))) =
        algebraMap ℤ (A ⧸ J) 3 := by
  dsimp only
  let I := Ideal.span {(5 : ℤ)}
  let A := Henselization.algebra I
  let J := Henselization.extended I
  have h5 : algebraMap ℤ (A ⧸ J) 5 = 0 := by
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have h23 : algebraMap ℤ (A ⧸ J) 2 * algebraMap ℤ (A ⧸ J) 3 = 1 := by
    have : (2 : ℤ) * 3 = 5 + 1 := by norm_num
    rw [← map_mul, this, map_add, h5, map_one, zero_add]
  have hu : IsUnit (algebraMap ℤ (A ⧸ J) 2) := IsUnit.of_mul_eq_one _ h23
  let ψ : Localization.Away (2 : ℤ) →ₐ[ℤ] A ⧸ J :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (2 : ℤ))
      (f := Algebra.ofId ℤ (A ⧸ J)) fun ⟨_, n, hn⟩ ↦ hn ▸ by simpa using hu.pow n
  obtain ⟨φ, hφ⟩ := (HenselianRing.comp_bijective_of_algebra (R := ℤ) J).2 ψ
  refine ⟨φ, ?_⟩
  have heq := AlgHom.congr_fun hφ (IsLocalization.Away.invSelf (2 : ℤ))
  have hmul := congrArg ψ (IsLocalization.Away.mul_invSelf
    (S := Localization.Away (2 : ℤ)) (2 : ℤ))
  have hbase : ψ (algebraMap ℤ (Localization.Away (2 : ℤ)) 2) =
      algebraMap ℤ (A ⧸ J) 2 := ψ.commutes 2
  rw [map_mul, hbase, map_one] at hmul
  exact heq.trans (hu.mul_left_cancel (hmul.trans h23.symm))

-- A proper ideal outside the Jacobson radical does not have the lifting property.
example : ¬ HenselianRing ℤ (Ideal.span {(5 : ℤ)}) := by
  intro h
  have hJ := h.jac (Ideal.subset_span (by simp) : (5 : ℤ) ∈ Ideal.span {5})
  rw [Ideal.mem_jacobson_bot] at hJ
  have := hJ 1
  norm_num [Int.isUnit_iff] at this

-- Neither a nonlocal base nor the zero ideal is excluded.
example : Function.Bijective
    ((Ideal.Quotient.mkₐ (ℤ × ℤ) (⊥ : Ideal (ℤ × ℤ))).comp :
      ((Fin 2 → ℤ × ℤ) →ₐ[ℤ × ℤ] ℤ × ℤ) →
        (Fin 2 → ℤ × ℤ) →ₐ[ℤ × ℤ] (ℤ × ℤ) ⧸ ⊥) :=
  HenselianRing.comp_bijective ⊥

-- The unit ideal is allowed in the zero ring.
example : Function.Bijective
    ((Ideal.Quotient.mkₐ (ZMod 1) (⊤ : Ideal (ZMod 1))).comp :
      (ZMod 1 →ₐ[ZMod 1] ZMod 1) → ZMod 1 →ₐ[ZMod 1] ZMod 1 ⧸ ⊤) :=
  HenselianRing.comp_bijective ⊤

end TauCeti
