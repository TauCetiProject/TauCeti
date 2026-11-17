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
localizing the targets at corresponding submonoids
(`RingHom.flat_localization_comp_iff_of_ringEquiv`). Applied at corresponding primes, this lets
symmetry arguments reduce flatness of a morphism to flatness at one point.

The file also states the equational criterion for flatness for a ring homomorphism
`g : A →+* B`, without an `Algebra A B` instance
(`RingHom.Flat.exists_eq_sum_mul_of_sum_mul_eq_zero`). This form applies to endomorphisms such
as Frobenius, where `B = A` already carries its own `A`-module structure. It is deduced from
`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`.

## References

* [Stacks: Equational criterion for flatness](https://stacks.math.columbia.edu/tag/00HK)
-/

public section

namespace RingHom

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- A commutative square `eS ∘ f = g ∘ eR` whose horizontal maps are ring isomorphisms
transports flatness after localizing the targets at corresponding submonoids: if `M.map eS = M'`,
`T` is a localization of `S` at `M` and `T'` is a localization of `S'` at `M'`, then `S → T` after
`f` is flat exactly when `S' → T'` after `g` is. -/
theorem flat_localization_comp_iff_of_ringEquiv {T T' : Type*} [CommRing T] [CommRing T']
    [Algebra S T] [Algebra S' T'] (f : R →+* S) (g : R' →+* S') (eR : R ≃+* R') (eS : S ≃+* S')
    (h : eS.toRingHom.comp f = g.comp eR.toRingHom) {M : Submonoid S} {M' : Submonoid S'}
    [IsLocalization M T] [IsLocalization M' T'] (hM : M.map eS = M') :
    ((algebraMap S T).comp f).Flat ↔ ((algebraMap S' T').comp g).Flat := by
  let e := IsLocalization.ringEquivOfRingEquiv T T' eS hM
  have he : e.toRingHom.comp ((algebraMap S T).comp f) =
      ((algebraMap S' T').comp g).comp eR.toRingHom := by
    ext x
    exact (IsLocalization.ringEquivOfRingEquiv_eq hM (f x)).trans
      (congrArg (algebraMap S' T') (RingHom.congr_fun h x))
  rw [← Flat.comp_iff_of_bijective_left (g := e.toRingHom) e.bijective, he,
    Flat.comp_iff_of_bijective_right eR.bijective]

/-- **Equational criterion for flatness** of a ring homomorphism: if `g : A →+* B` is flat, every
relation `∑ⱼ g (fⱼ) xⱼ = 0` in `B` is trivial, that is, `xⱼ = ∑ᵢ g (aⱼᵢ) yᵢ` for some `aⱼᵢ ∈ A` and
`yᵢ ∈ B` with `∑ⱼ fⱼ aⱼᵢ = 0` for every `i`. -/
@[stacks 00HK]
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
