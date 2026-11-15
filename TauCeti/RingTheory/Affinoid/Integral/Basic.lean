/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.Analysis.Normed.Algebra.ScaleRoots
import TauCeti.RingTheory.AdjoinRoot.Finite
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Finite algebras over affinoid algebras

Adjoining a root of a monic polynomial to an affinoid algebra gives an affinoid algebra, and
consequently every finite algebra over an affinoid algebra is affinoid. Together with
`TauCeti.IsAffinoidAlgebra.quotient`, this closes the class of affinoid algebras under the
two basic algebraic operations used to build finite morphisms of affinoid spaces.

For a monic `p` over `A = K⟨X₁, …, Xₙ⟩ ⧸ I`, lift `p` to a monic polynomial `P` over the Tate
algebra and rescale its roots by a small nonzero scalar, so that all coefficients have Gauss norm
at most one. The rescaled polynomial is distinguished, so Weierstrass division identifies its
polynomial quotient with the quotient of `K⟨X₁, …, Xₙ, Y⟩` by it. This quotient maps onto
`A[Y] ⧸ (p)`, sending `Y` to the rescaled root. A finite algebra is reached from `A` by adjoining
finitely many integral generators one at a time.

The coefficient field must be nontrivially normed, to rescale the roots. No reducedness,
characteristic, or nontriviality assumption is placed on the algebras.

## Main results

* `TauCeti.IsAffinoidAlgebra.adjoinRoot`: `A[X] ⧸ (p)` is affinoid for monic `p`.
* `TauCeti.IsAffinoidAlgebra.of_finite`: a finite algebra over an affinoid algebra is affinoid.
* `TauCeti.IsAffinoidAlgebra.of_algHom_finite`: the target of a finite algebra homomorphism
  from an affinoid algebra is affinoid.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries Polynomial

universe u v

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

variable {A : Type u} [CommRing A] [Algebra K A]

/-- Adjoining a root of a monic polynomial to an affinoid algebra gives an affinoid algebra. -/
theorem adjoinRoot (hA : IsAffinoidAlgebra K A) {p : A[X]} (hp : p.Monic) :
    IsAffinoidAlgebra K (AdjoinRoot p) := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K A).mp hA
  let R := Tate (Fin n)
  -- Lift `p` to a monic polynomial over the Tate algebra and make its coefficients small.
  obtain ⟨P, hPp, -, hPm⟩ := lifts_and_natDegree_eq_and_monic
    (f := π.toRingHom) (p := p) ((lifts_iff_coeff_lifts p).mpr fun k ↦ hπ _) hp
  obtain ⟨c, hc0, hc⟩ := exists_norm_coeff_scaleRoots_le_one (K := K) P
  set Q := P.scaleRoots (algebraMap K R c)
  have hQm : Q.IsMonicOfDegree P.natDegree :=
    ⟨natDegree_scaleRoots _ _, (monic_scaleRoots_iff _).mpr hPm⟩
  have hQ : PowerSeries.IsDistinguished 1 P.natDegree (Q : PowerSeries R) :=
    PowerSeries.isDistinguished_of_isMonicOfDegree one_pos hQm (by simpa using hc)
  -- Evaluate at the rescaled root of `p`.
  let ev : R[X] →ₐ[K] AdjoinRoot p := eval₂AlgHom ((AdjoinRoot.ofAlgHom K p).comp π)
    (algebraMap K (AdjoinRoot p) c * AdjoinRoot.root p) (fun _ ↦ Commute.all _ _)
  have hevQ : ev Q = 0 := by
    have h := scaleRoots_eval₂_eq_zero ((AdjoinRoot.of p).comp π.toRingHom)
      (r := AdjoinRoot.root p) (s := algebraMap K R c) (p := P) (by
        rw [← eval₂_map, hPp]
        exact AdjoinRoot.eval₂_root p)
    have hc' : ((AdjoinRoot.of p).comp π.toRingHom) (algebraMap K R c) =
        algebraMap K (AdjoinRoot p) c := ((AdjoinRoot.ofAlgHom K p).comp π).commutes c
    rwa [hc'] at h
  have hev : Function.Surjective ev := by
    have hof (a : A) : AdjoinRoot.of p a ∈ ev.toRingHom.range := by
      obtain ⟨r, rfl⟩ := hπ a
      exact ⟨Polynomial.C r, by simp [ev]⟩
    have hroot : AdjoinRoot.root p ∈ ev.toRingHom.range := by
      refine ⟨Polynomial.C (algebraMap K R c⁻¹) * Polynomial.X, ?_⟩
      simp [ev, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0]
    refine fun y ↦ RingHom.mem_range.mp ?_
    induction y using AdjoinRoot.induction_on with | ih q => ?_
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | monomial k a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      exact mul_mem (hof a) (pow_mem hroot k)
  -- Assemble the presentation by `K⟨X₁, …, Xₙ, Y⟩`, using Weierstrass division by `Q`.
  have hker : ∀ a ∈ Ideal.span {Q}, ev a = 0 := fun a ha ↦ by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hevQ, mul_zero]
  let g : R[X] ⧸ Ideal.span {Q} →ₐ[K] AdjoinRoot p := Ideal.Quotient.liftₐ _ ev hker
  let e := hQ.polynomialQuotientEquiv one_pos hQm
  let ψ : Tate (Option (Fin n)) →ₐ[K] AdjoinRoot p :=
    g.comp ((e.symm.restrictScalars K).toAlgHom.comp ((Ideal.Quotient.mkₐ K _).comp
      (restrictedOptionEquiv (σ := Fin n) (R := K)).toAlgHom))
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.lift_surjective_of_surjective _ hker hev).comp <|
      e.symm.surjective.comp <| Ideal.Quotient.mk_surjective.comp <| AlgEquiv.surjective _
  exact isAffinoidAlgebra_tate.of_surjective ψ hψ

variable {B : Type v} [CommRing B] [Algebra K B]

/-- A finite algebra over an affinoid algebra is affinoid. -/
theorem of_finite [Algebra A B] [IsScalarTower K A B] [Module.Finite A B]
    (hA : IsAffinoidAlgebra K A) : IsAffinoidAlgebra K B := by
  obtain ⟨A', _, _, f, hA', hf⟩ := exists_surjective_of_module_finite
    (fun A (_ : CommRing A) (_ : Algebra K A) ↦ IsAffinoidAlgebra K A)
    (fun _ _ _ _ hp hA ↦ hA.adjoinRoot hp) (A := A) (B := B) hA
  exact hA'.of_surjective f hf

/-- The target of a finite algebra homomorphism from an affinoid algebra is affinoid. -/
theorem of_algHom_finite (hA : IsAffinoidAlgebra K A) (f : A →ₐ[K] B) (hf : f.Finite) :
    IsAffinoidAlgebra K B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : Module.Finite A B := hf
  exact hA.of_finite

end TauCeti.IsAffinoidAlgebra
