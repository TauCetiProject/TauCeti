/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Transport principles for integral closures and their finiteness

General facts for transporting `IsIntegralClosure` and descending finiteness:

* Transporting across ring isomorphisms: if `eA : A ≃+* A'`, `eR : R ≃+* R'`, and `eB : B ≃+* B'`
  intertwine the algebra maps, `IsIntegralClosure A R B` transfers to `IsIntegralClosure A' R' B'`
  (`IsIntegralClosure.of_ringEquiv`). Compare Mathlib's `IsIntegralClosure.of_algEquiv`, which
  only varies the ambient ring.
* Descending the base: an integral closure of `A` in `B` is also the integral closure of `R` in
  `B` when `A` is integral over `R`. This is the converse of Mathlib's
  `IsIntegralClosure.tower_top`.
* Descending along an embedding: an integral `A`-algebra that embeds into a ring whose integral
  closure over `A` is a Noetherian `A`-module is itself a finite `A`-module. This is the
  "as `R` is Noetherian it suffices to enlarge the field" step of Stacks, Lemmas 10.161.5,
  10.161.12 and 10.161.13.

## Main results

* `IsIntegralClosure.of_ringEquiv`: transport of `IsIntegralClosure` along compatible ring
  equivalences of all three rings.
* `TauCeti.IsIntegralClosure.tower_bot`: the integral closure of `A` in `B` is the integral
  closure of `R` in `B` when `A` is integral over `R`.
* `TauCeti.IsIntegralClosure.finite_of_injective`: an integral `A`-algebra with an injective
  `A`-algebra map into `K'` is a finite `A`-module when the integral closure of `A` in `K'` is a
  Noetherian `A`-module.

## References

* [Stacks, Lemma 10.36.16 (tag 0308)](https://stacks.math.columbia.edu/tag/0308)
* [Stacks, Lemma 10.161.12 (tag 032N)](https://stacks.math.columbia.edu/tag/032N)
-/

public section

/-- **Integral closures transfer along compatible ring isomorphisms**: if `eA : A ≃+* A'`,
`eR : R ≃+* R'`, and `eB : B ≃+* B'` intertwine the algebra maps into `B` and `B'`, and `A` is
the integral closure of `R` in `B`, then `A'` is the integral closure of `R'` in `B'`. Compare
Mathlib's `IsIntegralClosure.of_algEquiv`, which fixes `A` and `R` and varies `B` by an
`R`-algebra equivalence. -/
theorem IsIntegralClosure.of_ringEquiv {A R B A' R' B' : Type*} [CommRing R] [CommSemiring A]
    [CommRing B] [Algebra R B] [Algebra A B] [CommRing R'] [CommSemiring A'] [CommRing B']
    [Algebra R' B'] [Algebra A' B'] (h : IsIntegralClosure A R B) (eA : A ≃+* A') (eR : R ≃+* R')
    (eB : B ≃+* B') (heR : ∀ r, eB (algebraMap R B r) = algebraMap R' B' (eR r))
    (heA : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a)) :
    IsIntegralClosure A' R' B' := by
  have hsymmR (r' : R') : eB.symm (algebraMap R' B' r') = algebraMap R B (eR.symm r') :=
    eB.symm_apply_eq.mpr (by rw [heR, eR.apply_symm_apply])
  have hsymmA (a' : A') : eB.symm (algebraMap A' B' a') = algebraMap A B (eA.symm a') :=
    eB.symm_apply_eq.mpr (by rw [heA, eA.apply_symm_apply])
  refine ⟨fun a₁ a₂ ha => eA.symm.injective (h.algebraMap_injective ?_),
    fun {x'} => ⟨fun hx' => ?_, ?_⟩⟩
  · rw [← hsymmA, ← hsymmA, ha]
  · obtain ⟨a, ha⟩ := h.isIntegral_iff.mp
      (hx'.map_of_comp_eq (eR.symm : R' →+* R) (eB.symm : B' →+* B)
        (RingHom.ext fun r' => (hsymmR r').symm))
    exact ⟨eA a, by simp [← heA, ha]⟩
  · rintro ⟨a', rfl⟩
    have ha : IsIntegral R (algebraMap A B (eA.symm a')) :=
      h.isIntegral_iff.mpr ⟨eA.symm a', rfl⟩
    have hmap := ha.map_of_comp_eq (eR : R →+* R') (eB : B →+* B')
      (RingHom.ext fun r => (heR r).symm)
    simpa [heA] using hmap

namespace TauCeti

/-- If `C` is the integral closure of `A` in `B` and `A` is integral over `R`, then `C` is the
integral closure of `R` in `B`. The converse of Mathlib's `IsIntegralClosure.tower_top`.

Source: Stacks, Lemma 10.36.16 (tag 0308): "Let `A → B → C` be ring maps. Let `B′` be the
integral closure of `A` in `B`, let `C′` be the integral closure of `B′` in `C`. Then `C′` is
the integral closure of `A` in `C`." -/
theorem IsIntegralClosure.tower_bot {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B]
    [CommSemiring C] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C A B] [Algebra.IsIntegral R A] : IsIntegralClosure C R B :=
  ⟨IsIntegralClosure.algebraMap_injective C A B,
    fun hx ↦ IsIntegralClosure.isIntegral_iff.mp (hx.tower_top (A := A)),
    fun hx ↦ isIntegral_trans _ ((IsIntegralClosure.isIntegral_iff (R := A)).mpr hx)⟩

/-- An integral `A`-algebra `C` with an injective `A`-algebra map into `K'` is a finite `A`-module
as soon as an integral closure `C'` of `A` in `K'` is a Noetherian `A`-module (for instance, a
finite module over a Noetherian ring `A`).

Source: Stacks, Lemma 10.161.12 (tag 032N), proof: "Choose a finite normal field extension
`M/K` containing `L`. As `R` is Noetherian it suffices to show that the integral closure of `R`
in `M` is finite over `R`." -/
theorem IsIntegralClosure.finite_of_injective {A K' C C' : Type*} [CommRing A] [CommRing K']
    [Algebra A K'] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] [CommRing C']
    [Algebra A C'] [Algebra C' K'] [IsScalarTower A C' K'] [IsIntegralClosure C' A K']
    [IsNoetherian A C'] (f : C →ₐ[A] K') (hf : Function.Injective f) : Module.Finite A C := by
  -- `f` makes `C` an algebra over which `IsIntegralClosure.lift` can land in `C'`
  let _ : Algebra C K' := f.toRingHom.toAlgebra
  have : IsScalarTower A C K' := .of_algebraMap_eq' f.comp_algebraMap.symm
  refine Module.Finite.of_injective (IsIntegralClosure.lift A C' K' (S := C)).toLinearMap
    fun a b hab ↦ hf ?_
  simpa [RingHom.algebraMap_toAlgebra] using congrArg (algebraMap C' K') hab

end TauCeti
