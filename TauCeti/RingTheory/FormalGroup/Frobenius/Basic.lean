/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic
public import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Frobenius factorization of formal group homomorphisms

Over a commutative ring of prime characteristic `p`, the series `X ^ p` is a homomorphism
from a formal group to its coefficient Frobenius twist. Its `h`-fold iterate has series
`X ^ (p ^ h)` and composes by expanding the outer series. A homomorphism with zero linear
coefficient factors uniquely through this Frobenius homomorphism. Its factor is obtained by
selecting the coefficients in degrees divisible by `p`, using the residue-zero Cartier
operator. The coefficient ring may have nilpotents, and the formal groups need not be
commutative.

This is the Frobenius factorization argument of Silverman, *The Arithmetic of Elliptic
Curves*, IV.7, Proposition 7.2, using the derivative criterion over arbitrary coefficient rings.
-/

public section

open MvPowerSeries

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

namespace FormalGroup

/-- Relative Frobenius iterated `h` times, with series `X ^ (p ^ h)`, maps to the
corresponding coefficient Frobenius twist. -/
noncomputable def iterateFrobeniusHom (F : FormalGroup R) (p : ℕ) [Fact p.Prime] [CharP R p]
    (h : ℕ) : TauCeti.FormalGroupHom F (F.map (iterateFrobenius R p h)) where
  toPowerSeries := PowerSeries.X ^ (p ^ h)
  zero_constantCoeff := by simp [(Fact.out : p.Prime).ne_zero]
  hom := by
    have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
    rw [PowerSeries.subst_pow hF, PowerSeries.subst_X hF]
    have hcoords (i : Fin 2) : PowerSeries.toMvPowerSeries i
        (PowerSeries.X ^ (p ^ h) : PowerSeries R) = X i ^ (p ^ h) := by
      rw [PowerSeries.toMvPowerSeries_eq_subst,
        PowerSeries.subst_pow (PowerSeries.HasSubst.X i),
        PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
    simp only [hcoords, map_toPowerSeries]
    exact (MvPowerSeries.map_iterateFrobenius_expand p (Fact.out : p.Prime).ne_zero
      F.toPowerSeries h).symm.trans (by
        rw [MvPowerSeries.map_expand, MvPowerSeries.expand, substAlgHom_apply])

@[simp]
theorem iterateFrobeniusHom_toPowerSeries (F : FormalGroup R) (h : ℕ) :
    (F.iterateFrobeniusHom p h).toPowerSeries = PowerSeries.X ^ (p ^ h) := (rfl)

/-- Relative Frobenius is the homomorphism with series `X ^ p` to the coefficient Frobenius
twist. -/
noncomputable def frobeniusHom (F : FormalGroup R) (p : ℕ) [Fact p.Prime] [CharP R p] :
    TauCeti.FormalGroupHom F (F.map (frobenius R p)) where
  toPowerSeries := PowerSeries.X ^ p
  zero_constantCoeff := by simp [(Fact.out : p.Prime).ne_zero]
  hom := by
    simpa only [iterateFrobeniusHom_toPowerSeries, pow_one, iterateFrobenius_one] using
      (F.iterateFrobeniusHom p 1).hom

@[simp]
theorem frobeniusHom_toPowerSeries (F : FormalGroup R) :
    (F.frobeniusHom p).toPowerSeries = PowerSeries.X ^ p := (rfl)

end FormalGroup

namespace TauCeti.FormalGroupHom

variable {F G : FormalGroup R}

/-- Composition with iterated relative Frobenius expands the outer series. -/
theorem comp_iterateFrobeniusHom_toPowerSeries (h : ℕ)
    (g : FormalGroupHom (F.map (iterateFrobenius R p h)) G) :
    (g.comp (F.iterateFrobeniusHom p h)).toPowerSeries =
      PowerSeries.expand (p ^ h) (pow_ne_zero h (Fact.out : p.Prime).ne_zero)
        g.toPowerSeries := by
  rw [comp_toPowerSeries, FormalGroup.iterateFrobeniusHom_toPowerSeries,
    PowerSeries.expand_apply]

/-- The factor of a homomorphism with zero tangent map through relative Frobenius. -/
noncomputable def frobeniusFactor (f : FormalGroupHom F G)
    (hf : PowerSeries.coeff 1 f.toPowerSeries = 0) :
    FormalGroupHom (F.map (frobenius R p)) G where
  toPowerSeries := PowerSeries.cartier R p 0 f.toPowerSeries
  zero_constantCoeff := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_cartier]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using f.zero_constantCoeff
  hom := by
    let g := PowerSeries.cartier R p 0 f.toPowerSeries
    have hexp : PowerSeries.expand p (Fact.out : p.Prime).ne_zero g = f.toPowerSeries :=
      PowerSeries.expand_cartier_of_derivative_eq_zero (f.derivative_eq_zero_iff.mpr hf)
    have htwist := PowerSeries.HasSubst.of_constantCoeff_zero
      (F.map (frobenius R p)).zero_constantCoeff
    have hg0 : g.constantCoeff = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_cartier]
      simpa only [Nat.mul_zero, Nat.add_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        using f.zero_constantCoeff
    have hcoords (i : Fin 2) :
        MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero (g.toMvPowerSeries i) =
          f.toPowerSeries.toMvPowerSeries i := by
      rw [← PowerSeries.toMvPowerSeries_expand, hexp]
    have hleft : MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
        (PowerSeries.subst (F.map (frobenius R p)).toPowerSeries g) =
          PowerSeries.subst F.toPowerSeries f.toPowerSeries := by
      rw [PowerSeries.expand_subst p (Fact.out : p.Prime).ne_zero htwist]
      have hpow : MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
          (F.map (frobenius R p)).toPowerSeries = F.toPowerSeries ^ p := by
        rw [FormalGroup.map_toPowerSeries, ← MvPowerSeries.map_expand,
          MvPowerSeries.map_frobenius_expand]
      rw [hpow, ← hexp, PowerSeries.subst_expand p (Fact.out : p.Prime).ne_zero
        (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff)]
    have hright : MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
        (subst (fun i : Fin 2 ↦ g.toMvPowerSeries i) G.toPowerSeries) =
          subst (fun i ↦ f.toPowerSeries.toMvPowerSeries i) G.toPowerSeries := by
      rw [MvPowerSeries.expand_subst _ _ (.toMvPowerSeries hg0)]
      simp only [hcoords]
    have heq := hleft.trans (f.hom.trans hright.symm)
    ext n
    have h := congrArg (MvPowerSeries.coeff (p • n)) heq
    simpa only [MvPowerSeries.coeff_expand_smul] using h

@[simp]
theorem frobeniusFactor_toPowerSeries (f : FormalGroupHom F G)
    (hf : PowerSeries.coeff 1 f.toPowerSeries = 0) :
    (f.frobeniusFactor (p := p) hf).toPowerSeries =
      PowerSeries.cartier R p 0 f.toPowerSeries := (rfl)

/-- Composing the Frobenius factor with relative Frobenius recovers the original map. -/
@[simp]
theorem frobeniusFactor_comp_frobeniusHom (f : FormalGroupHom F G)
    (hf : PowerSeries.coeff 1 f.toPowerSeries = 0) :
    (f.frobeniusFactor (p := p) hf).comp (F.frobeniusHom p) = f := by
  apply FormalGroupHom.ext
  rw [comp_toPowerSeries, FormalGroup.frobeniusHom_toPowerSeries,
    frobeniusFactor_toPowerSeries, ← PowerSeries.expand_apply]
  exact PowerSeries.expand_cartier_of_derivative_eq_zero (f.derivative_eq_zero_iff.mpr hf)

/-- A homomorphism with zero linear coefficient factors uniquely through relative Frobenius. -/
theorem existsUnique_comp_frobeniusHom (f : FormalGroupHom F G)
    (hf : PowerSeries.coeff 1 f.toPowerSeries = 0) :
    ∃! g : FormalGroupHom (F.map (frobenius R p)) G, g.comp (F.frobeniusHom p) = f := by
  refine ⟨f.frobeniusFactor hf, f.frobeniusFactor_comp_frobeniusHom hf, ?_⟩
  intro g hg
  apply FormalGroupHom.ext
  ext n
  have h := congrArg (fun a : FormalGroupHom F G ↦ PowerSeries.coeff (p * n) a.toPowerSeries) hg
  simpa only [comp_toPowerSeries, FormalGroup.frobeniusHom_toPowerSeries,
    ← PowerSeries.expand_apply p (Fact.out : p.Prime).ne_zero,
    PowerSeries.coeff_expand_mul, frobeniusFactor_toPowerSeries,
    PowerSeries.coeff_cartier, Nat.add_zero] using h

end TauCeti.FormalGroupHom
