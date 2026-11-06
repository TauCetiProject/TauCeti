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

A commutative square whose horizontal maps are isomorphisms transports flatness after
localizing the target at corresponding primes. This lets symmetry arguments reduce
flatness of a morphism to flatness at one point.

The file also states the equational criterion for flatness for a ring homomorphism
`g : A →+* B`, without an `Algebra A B` instance
(`RingHom.Flat.exists_eq_sum_mul_of_sum_mul_eq_zero`). This form applies to endomorphisms such
as Frobenius, where `B = A` already carries its own `A`-module structure.
-/

public section

namespace RingHom

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

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

/-- **Equational criterion for flatness** of a ring homomorphism: if `g : A →+* B` is flat, every
relation `∑ⱼ g (fⱼ) xⱼ = 0` in `B` is trivial, that is, `xⱼ = ∑ᵢ g (aⱼᵢ) yᵢ` for some `aⱼᵢ ∈ A` and
`yᵢ ∈ B` with `∑ⱼ fⱼ aⱼᵢ = 0` for every `i`. -/
theorem Flat.exists_eq_sum_mul_of_sum_mul_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    {g : A →+* B} (hg : g.Flat) {ι : Type*} [Fintype ι] {f : ι → A} {x : ι → B}
    (h : ∑ j, g (f j) * x j = 0) :
    ∃ (k : ℕ) (a : ι → Fin k → A) (y : Fin k → B),
      (∀ j, x j = ∑ i, g (a j i) * y i) ∧ ∀ i, ∑ j, f j * a j i = 0 := by
  algebraize [g]
  obtain ⟨k, a, y, hxy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A)
    (M := B) (f := f) (x := x) (by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h)
  exact ⟨k, a, y, fun j ↦ by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hxy j, ha⟩

end RingHom
