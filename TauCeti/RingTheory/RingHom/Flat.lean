/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat ring homomorphisms

The equational criterion for a flat ring homomorphism `g : R →+* S`: every relation
`∑ g (fⱼ) xⱼ = 0` in `S` is trivial. This is Mathlib's
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` stated without the algebra structure that `g`
induces, so that it also applies to ring endomorphisms such as Frobenius, where that structure
would clash with the action of a ring on itself.

A commutative square whose horizontal maps are isomorphisms transports flatness after
localizing the target at corresponding primes. This lets symmetry arguments reduce
flatness of a morphism to flatness at one point.
-/

public section

namespace RingHom

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- **Equational criterion for a flat ring homomorphism.** If `g : R →+* S` is flat, every relation
`∑ g (fⱼ) xⱼ = 0` in `S` is trivial: there are `aⱼₛ ∈ R` and `wₛ ∈ S` such that
`xⱼ = ∑ₛ g (aⱼₛ) wₛ` for every `j` and `∑ⱼ fⱼ aⱼₛ = 0` for every `s`. -/
theorem Flat.exists_eq_sum_of_sum_mul_eq_zero {g : R →+* S} (hg : g.Flat) {ι : Type*}
    [Fintype ι] {f : ι → R} {x : ι → S} (h : ∑ j, g (f j) * x j = 0) :
    ∃ (k : ℕ) (a : ι → Fin k → R) (w : Fin k → S),
      (∀ j, x j = ∑ s, g (a j s) * w s) ∧ ∀ s, ∑ j, f j * a j s = 0 := by
  algebraize [g]
  obtain ⟨k, a, w, hxw, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := f) (x := x)
    (by simpa only [Algebra.smul_def, algebraMap_toAlgebra] using h)
  exact ⟨k, a, w, fun j ↦ by simpa only [Algebra.smul_def, algebraMap_toAlgebra] using hxw j, ha⟩

/-- A square of ring maps with isomorphic source and target preserves flatness after
localizing the target at corresponding prime ideals. -/
theorem flat_localization_comap_iff (f : R →+* S) (g : R' →+* S')
    (eR : R ≃+* R') (eS : S ≃+* S')
    (h : eS.toRingHom.comp f = g.comp eR.toRingHom) (p : Ideal S') [p.IsPrime] :
    ((algebraMap S (Localization.AtPrime (p.comap eS))).comp f).Flat ↔
      ((algebraMap S' (Localization.AtPrime p)).comp g).Flat := by
  let e := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.comap eS)) (Localization.AtPrime p)
    eS (eS.map_primeCompl_comap_eq p)
  have he : e.toRingHom.comp
      ((algebraMap S (Localization.AtPrime (p.comap eS))).comp f) =
      ((algebraMap S' (Localization.AtPrime p)).comp g).comp eR.toRingHom := by
    ext x
    exact (IsLocalization.ringEquivOfRingEquiv_eq (eS.map_primeCompl_comap_eq p) (f x)).trans
      (congrArg (algebraMap S' (Localization.AtPrime p)) (RingHom.congr_fun h x))
  calc
    _ ↔ (e.toRingHom.comp
        ((algebraMap S (Localization.AtPrime (p.comap eS))).comp f)).Flat :=
      (Flat.comp_iff_of_bijective_left (g := e.toRingHom) e.bijective).symm
    _ ↔ _ := by
      rw [he]
      exact Flat.comp_iff_of_bijective_right (g := eR.toRingHom) eR.bijective

end RingHom
