/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Étaleness at a prime: flatness and unramifiedness of the local ring

Let `S` be a finitely presented `R`-algebra and `q` a prime of `S`. Mathlib's
`Algebra.IsEtaleAt R q` asks that `S_q` be formally étale over `R`. This file shows that this is
exactly flatness of `S_q` over `R` together with Mathlib's `Algebra.IsUnramifiedAt R q`
(`Algebra.isEtaleAt_iff_flat_and_isUnramifiedAt`). Only flatness at the single prime `q` is
assumed; Mathlib's `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` asks for flatness of all of `S`.

The converse direction spreads étaleness to some `S_f` with `f ∉ q`
(`Algebra.exists_etale_of_isEtaleAt`), which is flat, and localizes. For the forward direction,
put `p = q ∩ R`. The local ring `S_q` is flat over `R_p`, and its closed fibre
`κ(p) ⊗[R_p] S_q` is formally unramified and essentially of finite type over the field `κ(p)`,
hence formally étale. Mathlib's local criterion
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor` then makes `S_q` formally smooth
over `R_p`; with formal unramifiedness it is formally étale over `R_p`, hence over `R`. The
presentation of `S_q` as a localization of the finitely presented `R_p`-algebra `S_p` is set up
as in Mathlib's proof of `Algebra.IsSmoothAt.of_formallySmooth_fiber`.

The file also translates flatness and formal unramifiedness of the local homomorphism
`R_p → S_q` into these pointwise conditions (`Localization.flat_localRingHom_iff`,
`Localization.formallyUnramified_localRingHom_iff`). Stalk maps of morphisms of affine schemes
are such local homomorphisms, so this is how the conditions are read off from stalks.

## Main results

* `Algebra.isEtaleAt_iff_flat_and_isUnramifiedAt`: for `S` finitely presented over `R`, `S` is
  étale over `R` at `q` iff `S_q` is flat over `R` and `S` is unramified over `R` at `q`.
* `Algebra.IsEtaleAt.flat_localization`: the flatness half of the forward direction.

## References

* [The Stacks Project, Lemma 10.151.8 (08WD)](https://stacks.math.columbia.edu/tag/08WD), the
  global form: étale is flat, unramified and of finite presentation.
* [The Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF), smoothness at a prime
  from flatness and a smooth fibre.
-/

public section

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is finitely presented over `R` and étale at a prime `q`, then `S_q` is flat over
`R`. -/
theorem IsEtaleAt.flat_localization [FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [IsEtaleAt R q] : Module.Flat R (Localization.AtPrime q) := by
  obtain ⟨f, hfq, _⟩ := exists_etale_of_isEtaleAt (R := R) q
  have h : Submonoid.powers f ≤ q.primeCompl := Submonoid.powers_le.mpr hfq
  let := IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f)
    (Localization.AtPrime q) _ _ h
  have := IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f)
    (Localization.AtPrime q) _ _ h
  have := IsLocalization.isLocalization_of_submonoid_le (Localization.Away f)
    (Localization.AtPrime q) _ _ h
  have : Module.Flat (Localization.Away f) (Localization.AtPrime q) :=
    IsLocalization.flat _ (q.primeCompl.map (algebraMap S (Localization.Away f)))
  have : IsScalarTower R (Localization.Away f) (Localization.AtPrime q) := .to₁₃₄ _ S _ _
  exact .trans R (Localization.Away f) _

attribute [local instance] FormallyEtale.of_formallyUnramified_of_field in
/-- If `S` is finitely presented over `R`, unramified at a prime `q`, and `S_q` is flat over `R`,
then `S` is étale over `R` at `q`. -/
private theorem IsEtaleAt.of_flat_of_isUnramifiedAt [FinitePresentation R S] (q : Ideal S)
    [q.IsPrime] [Module.Flat R (Localization.AtPrime q)] [IsUnramifiedAt R q] :
    IsEtaleAt R q := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  -- Present `S_q` as a localization of the finitely presented `R_p`-algebra `S_p`.
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
      (f := Algebra.ofId _ _) (by
    rintro ⟨_, x, hx, rfl⟩
    simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
      by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
      (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  -- The closed fibre of `R_p → S_q` is formally étale, so `S_q` is formally smooth over `R_p`.
  have : Module.Flat Rp Sq := (Module.flat_iff_of_isLocalization Rp p.primeCompl Sq).mpr ‹_›
  have : FormallyUnramified Rp Sq := .of_restrictScalars R _ _
  have : EssFiniteType Rp Sq := .of_comp R _ _
  have : FormallySmooth Rp Sq := FormallySmooth.of_formallySmooth_residueField_tensor
    (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  have : FormallyEtale Rp Sq :=
    FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨‹_›, ‹_›⟩
  exact FormallyEtale.comp R Rp Sq

/-- A finitely presented `R`-algebra `S` is étale over `R` at a prime `q` if and only if `S_q` is
flat over `R` and `S` is unramified over `R` at `q`. -/
theorem isEtaleAt_iff_flat_and_isUnramifiedAt [FinitePresentation R S] (q : Ideal S)
    [q.IsPrime] :
    IsEtaleAt R q ↔ Module.Flat R (Localization.AtPrime q) ∧ IsUnramifiedAt R q :=
  ⟨fun _ ↦ ⟨IsEtaleAt.flat_localization q, inferInstance⟩,
    fun ⟨_, _⟩ ↦ IsEtaleAt.of_flat_of_isUnramifiedAt q⟩

end Algebra

namespace Localization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The local homomorphism `R_p → S_q` at primes `q` over `p` is flat iff `S_q` is flat over
`R`. -/
theorem flat_localRingHom_iff (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (h : p = q.comap (algebraMap R S)) :
    (localRingHom p q (algebraMap R S) h).Flat ↔ Module.Flat R (Localization.AtPrime q) := by
  have : q.LiesOver p := ⟨h⟩
  let := AtPrime.algebraOfLiesOver p q
  rw [← Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]
  exact RingHom.flat_algebraMap_iff

/-- The local homomorphism `R_p → S_q` at primes `q` over `p` is formally unramified iff `S` is
unramified over `R` at `q`. -/
theorem formallyUnramified_localRingHom_iff (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (h : p = q.comap (algebraMap R S)) :
    (localRingHom p q (algebraMap R S) h).FormallyUnramified ↔ Algebra.IsUnramifiedAt R q := by
  have : q.LiesOver p := ⟨h⟩
  let := AtPrime.algebraOfLiesOver p q
  refine RingHom.formallyUnramified_algebraMap.trans
    ⟨fun _ ↦ Algebra.FormallyUnramified.comp R (Localization.AtPrime p) _,
      fun _ ↦ .of_restrictScalars R _ _⟩

end Localization
