/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Unramified.Field

/-!
# Reducedness of smooth algebras

A smooth algebra over a reduced commutative ring is reduced. The proof first treats integral
domains: a standard-smooth algebra embeds into its étale generic fibre over a polynomial ring,
and a standard-smooth localization cover gives the smooth case. For a reduced Noetherian base,
embed the base into the finite product of its minimal-prime domain quotients and use flatness.
Finally, Noetherian descent and passage through finitely generated subalgebras give the result
over an arbitrary reduced base.

Over any commutative ring, a smooth algebra is geometrically reduced: its base changes to
algebraic closures of residue fields are smooth over fields, hence reduced. This supplies the
reducedness of geometric fibres used in the study of smooth affine group schemes.

## Main declarations

* `TauCeti.isReduced_of_smooth`: a smooth algebra over a reduced commutative ring is reduced.
* `TauCeti.isGeometricallyReduced_of_smooth`: a smooth algebra over any commutative ring is
  geometrically reduced.

## References

* [The Stacks Project, Lemma 10.163.7](https://stacks.math.columbia.edu/tag/033B).
* The Stacks Project, Section 10.140, *Smooth algebras over fields*.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

private theorem isReduced_of_standardSmooth_of_isDomain
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.IsStandardSmooth R A] : IsReduced A := by
  have hs : (algebraMap R A).IsStandardSmooth := by
    rw [RingHom.isStandardSmooth_algebraMap]
    infer_instance
  obtain ⟨n, g, _, hg⟩ := hs.exists_etale_mvPolynomial
  let _ : Algebra (MvPolynomial (Fin n) R) A := g.toAlgebra
  let _ : Algebra.Etale (MvPolynomial (Fin n) R) A := hg.toAlgebra
  let F := FractionRing (MvPolynomial (Fin n) R)
  let B := F ⊗[MvPolynomial (Fin n) R] A
  let _ : Algebra.Etale F B :=
    Algebra.Etale.baseChange (MvPolynomial (Fin n) R) A F
  let _ : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field F B
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin n) R) (A := F) (B := A))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective _ F))

private theorem isReduced_of_smooth_of_isDomain
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] : IsReduced A := by
  obtain ⟨s, hs, hsmooth⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R A
  constructor
  intro x hx
  apply Module.eq_zero_of_isLocalized_span s hs
    (fun r : s ↦ Localization.Away r.1)
    (fun r : s ↦ Algebra.linearMap A (Localization.Away r.1))
  intro r
  let _ : Algebra.IsStandardSmooth R (Localization.Away r.1) := hsmooth r.1 r.2
  let _ : IsReduced (Localization.Away r.1) :=
    isReduced_of_standardSmooth_of_isDomain R (Localization.Away r.1)
  exact (hx.map (algebraMap A (Localization.Away r.1))).eq_zero

private theorem isReduced_of_smooth_of_isNoetherianRing
    (R : Type u) (A : Type v) [CommRing R] [IsReduced R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] : IsReduced A := by
  classical
  let P := minimalPrimes R
  let : Fintype P := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let (p : P) : p.1.IsPrime := p.2.1.1
  let Q (p : P) := R ⧸ p.1
  -- A reduced ring embeds into the product of its minimal-prime quotients.
  have hinj : Function.Injective (algebraMap R (∀ p : P, Q p)) := by
    have hker : RingHom.ker (algebraMap R (∀ p : P, Q p)) = ⨅ p : P, p.1 :=
      Ideal.ker_Pi_Quotient_mk (fun p : P ↦ p.1)
    rw [RingHom.injective_iff_ker_eq_bot, hker]
    simp only [P, minimalPrimes, iInf_subtype, ← sInf_eq_iInf, Ideal.sInf_minimalPrimes,
      Ideal.radical_bot_of_isReduced]
  -- Flatness preserves the embedding after tensoring with the smooth algebra.
  let (p : P) : IsReduced (A ⊗[R] Q p) := by
    let : IsReduced (Q p ⊗[R] A) := isReduced_of_smooth_of_isDomain (Q p) _
    exact isReduced_of_injective (Algebra.TensorProduct.comm R A (Q p))
      (Algebra.TensorProduct.comm R A (Q p)).injective
  let : IsReduced (A ⊗[R] (∀ p : P, Q p)) :=
    isReduced_of_injective (Algebra.TensorProduct.piRight R R A Q)
      (Algebra.TensorProduct.piRight R R A Q).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] (∀ p : P, Q p))
    (Algebra.TensorProduct.includeLeft_injective hinj)

/-- A smooth algebra over a reduced commutative ring is reduced. -/
theorem isReduced_of_smooth
    (R : Type u) (A : Type v) [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] : IsReduced A := by
  obtain ⟨R₀, A₀, _, _, _, _, _, _, _, _, ⟨e⟩⟩ :=
    Algebra.Smooth.exists_finiteType ℤ R A
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsReduced (A₀ ⊗[R₀] R) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    have : Algebra.FiniteType R₀ B := ⟨B.fg_top.mpr hB⟩
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R₀ _
    have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
    have : IsReduced (B ⊗[R₀] A₀) := isReduced_of_smooth_of_isNoetherianRing B _
    exact isReduced_of_injective (Algebra.TensorProduct.comm R₀ A₀ B)
      (Algebra.TensorProduct.comm R₀ A₀ B).injective
  have : IsReduced (R ⊗[R₀] A₀) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R₀ R A₀)
      (Algebra.TensorProduct.comm R₀ R A₀).injective
  exact isReduced_of_injective e e.injective

/-- A smooth algebra over a commutative ring is geometrically reduced. -/
theorem isGeometricallyReduced_of_smooth
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] : Algebra.IsGeometricallyReduced R A := by
  constructor
  intro p hp
  exact isReduced_of_smooth (AlgebraicClosure p.ResidueField)
    (AlgebraicClosure p.ResidueField ⊗[R] A)

end TauCeti
