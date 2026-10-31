/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.Analysis.Normed.Algebra.ScaleRoots
import TauCeti.RingTheory.AdjoinRoot.Finite
import TauCeti.RingTheory.Dagger.GaussNorm
import TauCeti.RingTheory.Dagger.Weierstrass

/-!
# Finite algebras over dagger algebras

Adjoining a root of a monic polynomial to a dagger algebra gives a dagger algebra, and
consequently every finite algebra over a dagger algebra is a dagger algebra. Together with
`TauCeti.Dagger.IsDaggerAlgebra.quotient`, this closes the class of dagger algebras under the two
algebraic operations from which finite morphisms of affinoid dagger spaces are built.

For a monic `p` over `A = K⟨X₁, …, Xₙ⟩† ⧸ I`, lift `p` to a monic polynomial `P` over the
Monsky–Washnitzer algebra and rescale its roots by a small nonzero scalar `c`, so that all
coefficients have Gauss norm at most one. The rescaling cannot be skipped: over `A = K`, the
polynomial `X - c⁻¹` with `0 < ‖c‖ < 1` is a unit of `K⟨X⟩†`, so `K⟨X⟩† ⧸ (X - c⁻¹)` is zero,
whereas `K[X] ⧸ (X - c⁻¹) ≅ K`. The rescaled polynomial `Q` is distinguished at the unit radius,
so overconvergent Weierstrass division identifies `K⟨X₁, …, Xₙ⟩†[Y] ⧸ (Q)` with
`K⟨X₁, …, Xₙ, Y⟩† ⧸ (Q)`, and this quotient maps onto `A[Y] ⧸ (p)`, sending `Y` to `c` times the
root. A finite algebra is reached from `A` by adjoining finitely many integral generators one at
a time.

The coefficient field must be nontrivially normed, to rescale the roots. No reducedness,
characteristic, or nontriviality assumption is placed on the algebras.

## Main results

* `TauCeti.Dagger.IsDaggerAlgebra.adjoinRoot`: `A[X] ⧸ (p)` is a dagger algebra for monic `p`.
* `TauCeti.Dagger.IsDaggerAlgebra.of_finite`: a finite algebra over a dagger algebra is a dagger
  algebra.
* `TauCeti.Dagger.IsDaggerAlgebra.of_algHom_finite`: the target of a finite algebra homomorphism
  from a dagger algebra is a dagger algebra.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Lemma 1.10.

The argument follows `TauCeti.IsAffinoidAlgebra.adjoinRoot` and
`TauCeti.IsAffinoidAlgebra.of_finite` in `TauCeti.RingTheory.Affinoid.Integral`, with the
overconvergent quotient comparison `TauCeti.Dagger.washnitzerAlgebra.polynomialQuotientEquiv` in
place of Weierstrass division in the Tate algebra.
-/

public section

namespace TauCeti.Dagger.IsDaggerAlgebra

open _root_.MvPowerSeries Polynomial Dagger.washnitzerAlgebra

universe u v

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

/-- **Adjoining a root of a monic polynomial.** If `A` is a dagger algebra and `p` is monic,
then `A[X] ⧸ (p)` is a dagger algebra. -/
theorem adjoinRoot [IsDaggerAlgebra K A] {p : A[X]} (hp : p.Monic) :
    IsDaggerAlgebra K (AdjoinRoot p) := by
  obtain ⟨n, π, hπ⟩ := exists_surjective (K := K) (A := A)
  let W := Dagger.washnitzerAlgebra (Fin n) K
  -- Lift `p` to a monic polynomial over `W` and make its coefficients small.
  obtain ⟨P, hPp, -, hPm⟩ := lifts_and_natDegree_eq_and_monic
    (f := π.toRingHom) (p := p) ((lifts_iff_coeff_lifts p).mpr fun k ↦ hπ _) hp
  obtain ⟨c, hc0, hc⟩ := exists_norm_coeff_scaleRoots_le_one (K := K) P
  set Q := P.scaleRoots (algebraMap K W c)
  have hQm : Q.IsMonicOfDegree P.natDegree :=
    ⟨natDegree_scaleRoots _ _, (monic_scaleRoots_iff _).mpr hPm⟩
  have hQ : PowerSeries.IsDistinguished 1 P.natDegree
      (Q.map (toTate (Fin n) K).toRingHom :
        PowerSeries (IsRestricted.subring (R := K) (fun _ : Fin n ↦ (1 : ℝ)))) :=
    PowerSeries.isDistinguished_of_isMonicOfDegree one_pos
      ⟨by rw [hQm.monic.natDegree_map, hQm.natDegree_eq], hQm.monic.map _⟩ fun k hk ↦ by
        simpa [Polynomial.coeff_map, norm_toTate] using hc k hk
  -- Evaluate at the rescaled root of `p`.
  let i : W →ₐ[K] AdjoinRoot p := (AdjoinRoot.ofAlgHom K p).comp π
  have hi (w : W) : i w = AdjoinRoot.of p (π w) := by simp [i]
  have hic : i (algebraMap K W c) = algebraMap K (AdjoinRoot p) c := i.commutes c
  have hevQ : Q.eval₂ (i : W →+* AdjoinRoot p) (algebraMap K (AdjoinRoot p) c *
      AdjoinRoot.root p) = 0 := by
    rw [← hic]
    refine scaleRoots_eval₂_eq_zero (i : W →+* AdjoinRoot p) ?_
    have hcomp : (i : W →+* AdjoinRoot p) = (AdjoinRoot.of p).comp π.toRingHom :=
      RingHom.ext hi
    rw [hcomp, ← eval₂_map, hPp]
    exact AdjoinRoot.eval₂_root p
  let g : AdjoinRoot Q →ₐ[K] AdjoinRoot p := AdjoinRoot.liftAlgHom Q i _ hevQ
  have hg : Function.Surjective g := by
    have hof (a : A) : AdjoinRoot.of p a ∈ g.toRingHom.range := by
      obtain ⟨r, rfl⟩ := hπ a
      exact ⟨AdjoinRoot.of Q r, by simp [g, hi]⟩
    have hroot : AdjoinRoot.root p ∈ g.toRingHom.range := by
      refine ⟨AdjoinRoot.of Q (algebraMap K W c⁻¹) * AdjoinRoot.root Q, ?_⟩
      simp only [g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, AdjoinRoot.liftAlgHom_of,
        AdjoinRoot.liftAlgHom_root, ← mul_assoc]
      rw [i.commutes, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    refine fun y ↦ RingHom.mem_range.mp ?_
    induction y using AdjoinRoot.induction_on with | ih q => ?_
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | monomial k a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      exact mul_mem (hof a) (pow_mem hroot k)
  -- Assemble the presentation by `K⟨X₁, …, Xₙ, Y⟩†`, using Weierstrass division by `Q`.
  let e := polynomialQuotientEquiv hQ hQm
  let ψ : Dagger.washnitzerAlgebra (Option (Fin n)) K →ₐ[K] AdjoinRoot p :=
    g.comp (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K _))
  exact of_surjective_washnitzerAlgebra ψ
    (hg.comp (e.symm.surjective.comp Ideal.Quotient.mk_surjective))

/-- **Finite algebras over dagger algebras are dagger algebras.** -/
theorem of_finite [IsDaggerAlgebra K A] {B : Type v} [CommRing B] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B] [Module.Finite A B] : IsDaggerAlgebra K B := by
  obtain ⟨A', _, _, f, hA', hf⟩ := exists_surjective_of_module_finite
    (fun A (_ : CommRing A) (_ : Algebra K A) ↦ IsDaggerAlgebra K A)
    (fun _ _ _ _ hp _ ↦ adjoinRoot hp) (A := A) (B := B) inferInstance
  exact hA'.of_surjective f hf

/-- The target of a finite algebra homomorphism from a dagger algebra is a dagger algebra. -/
theorem of_algHom_finite [IsDaggerAlgebra K A] {B : Type v} [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (hf : f.Finite) : IsDaggerAlgebra K B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : Module.Finite A B := hf
  exact of_finite (A := A)

end TauCeti.Dagger.IsDaggerAlgebra
