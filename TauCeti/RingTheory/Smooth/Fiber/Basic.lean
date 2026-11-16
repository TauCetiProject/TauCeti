/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Fiber

/-!
# Smoothness at a prime from flatness and the closed fibre of the local ring

Let `S` be a finitely presented `R`-algebra and `q` a prime of `S` over the prime `p` of `R`.
Mathlib's `Algebra.IsSmoothAt.of_formallySmooth_fiber` makes `S` smooth over `R` at `q` when `S`
is flat over `R` and the whole fibre over `p` is formally smooth. This file proves the pointwise
form: it suffices that the local ring `S_q` is flat over `R_p` and that its closed fibre
`κ(p) ⊗[R_p] S_q` is formally smooth over `κ(p)`.

## Main results

* `Algebra.IsSmoothAt.of_flat_of_formallySmooth_residueField_tensor`: smoothness at `q` from
  flatness of `S_q` over `R_p` and formal smoothness of its closed fibre.

## References

* [The Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF), smoothness at a prime
  from flatness and a smooth fibre.
-/

public section

open IsLocalRing TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Smoothness at a prime from flatness and a smooth closed fibre.** Let `S` be a finitely
presented `R`-algebra and `q` a prime of `S` over the prime `p` of `R`. If `S_q` is flat over
`R_p` and its closed fibre `κ(p) ⊗[R_p] S_q` is formally smooth over `κ(p)`, then `S` is smooth
over `R` at `q`.

The proof presents `S_q` as a localization of the finitely presented `R_p`-algebra `S_p`, as in
Mathlib's proof of `Algebra.IsSmoothAt.of_formallySmooth_fiber` (Andrew Yang), and applies
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`. -/
theorem IsSmoothAt.of_flat_of_formallySmooth_residueField_tensor [FinitePresentation R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    ∀ [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
      [FormallySmooth (ResidueField (Localization.AtPrime p))
        (ResidueField (Localization.AtPrime p) ⊗[Localization.AtPrime p] Localization.AtPrime q)],
      IsSmoothAt R q := by
  intro _ _
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
  have : FormallySmooth Rp Sq := FormallySmooth.of_formallySmooth_residueField_tensor
    (P := Sp) (algebraMapSubmonoid _ q.primeCompl)
  exact FormallySmooth.comp R Rp Sq

end Algebra
