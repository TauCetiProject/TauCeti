/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Equality of algebra maps after shrinking a localization

For an essentially finite-type `R`-algebra `A`, two maps `A →ₐ[R] B` that agree after inverting
a submonoid of `R` already agree after inverting one element of that submonoid. In particular,
equality over a prime localization spreads to a principal neighbourhood of that prime. This is
the uniqueness input for spreading morphisms of affine schemes from a local scheme.

No Noetherianity, reducedness, or finiteness hypothesis on the target algebra is needed.
Essential finite type suffices because maps out of a localization are determined by their
restriction to a finite-type subalgebra.

## Main results

* `AlgHom.comp_eq_iff_exists_localizationAway`: equality after localization is equivalent to
equality after one principal localization.

Taking the submonoid to be `p.primeCompl` gives the prime-localization form, with the principal
neighbourhood specified by an element outside `p`.

## References

* The Stacks Project, Lemma 10.127.8 (05N9), the eventual-equality assertion for maps from a
finite-type algebra; and Lemma 32.20.3 (0BQ5), uniqueness after shrinking.
* Mathlib's `Algebra.EssFiniteType.algHom_ext` supplies the finite set of essential generators.
The result is the principal-localization form of the eventual-equality argument in
`RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`, without categorical colimit data.
-/

public section

namespace AlgHom

variable {R A B L : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing L]
  [Algebra R A] [Algebra R B] [Algebra B L] [Algebra R L] [IsScalarTower R B L]

/-- Two maps from an essentially finite-type algebra agree after inverting a submonoid of the
base exactly when they agree after inverting one element of that submonoid. The localization
`L` may be any model of the localization of `B` at the image of the submonoid. -/
theorem comp_eq_iff_exists_localizationAway [Algebra.EssFiniteType R A]
    (f g : A →ₐ[R] B) (M : Submonoid R)
    [IsLocalization (Algebra.algebraMapSubmonoid B M) L] :
    (IsScalarTower.toAlgHom R B L).comp f = (IsScalarTower.toAlgHom R B L).comp g ↔
      ∃ s ∈ M,
        (IsScalarTower.toAlgHom R B (Localization.Away (algebraMap R B s))).comp f =
          (IsScalarTower.toAlgHom R B (Localization.Away (algebraMap R B s))).comp g := by
  classical
  constructor
  · intro h
    let t := Algebra.EssFiniteType.finset R A
    have hex (a : t) : ∃ s ∈ M, algebraMap R B s * f a = algebraMap R B s * g a := by
      obtain ⟨⟨_, s, hs, rfl⟩, he⟩ :=
        IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid B M)
          (congrArg (fun k : A →ₐ[R] L ↦ k a) h)
      exact ⟨s, hs, he⟩
    choose s hs he using hex
    let u := ∏ a : t, s a
    refine ⟨u, M.prod_mem fun a _ ↦ hs a, Algebra.EssFiniteType.algHom_ext _ _ _ ?_⟩
    intro a ha
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ (⟨a, ha⟩ : t))
    apply (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R B u)) _).mpr
    refine ⟨⟨algebraMap R B u, Submonoid.mem_powers _⟩, ?_⟩
    simp only [u, hc, map_mul]
    calc
      _ = algebraMap R B c * (algebraMap R B (s ⟨a, ha⟩) * f a) := by
        simp [mul_left_comm, mul_assoc]
      _ = algebraMap R B c * (algebraMap R B (s ⟨a, ha⟩) * g a) := by rw [he]
      _ = _ := by simp [mul_left_comm, mul_assoc]
  · rintro ⟨s, hs, h⟩
    have hu : IsUnit (algebraMap B L (algebraMap R B s)) :=
      IsLocalization.map_units L ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨s, hs⟩ : M)⟩
    let l : Localization.Away (algebraMap R B s) →+* L :=
      IsLocalization.Away.lift (algebraMap R B s) hu
    ext a
    simpa [l] using congrArg l (congrArg (fun k ↦ k a) h)

end AlgHom
