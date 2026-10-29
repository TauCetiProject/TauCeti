/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Frobenius.Basic
public import TauCeti.RingTheory.FormalGroup.Height
import TauCeti.RingTheory.FormalGroup.BaseChange

/-!
# Iterated Frobenius factorization

A nonzero homomorphism of one-dimensional formal groups over a field of characteristic `p`
factors as relative Frobenius iterated `h` times followed by an isomorphism. The integer `h` is
characterized by the order `p ^ h` of its underlying series. For this fixed exponent the
isomorphism is unique, and its coefficients are those of the original homomorphism in degrees
divisible by `p ^ h`.

This separates the inseparable part of a homomorphism from its invertible coordinate, as used
in the classification of formal groups of finite height. No perfectness or commutativity
hypothesis is needed for this factorization. Applied to multiplication by `p`, it identifies
a finite-height commutative group with its height-fold coefficient Frobenius twist.

## References

* J. Silverman, *The Arithmetic of Elliptic Curves*, IV.7, Proposition 7.2.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)
    (p : ℕ) [Fact p.Prime] [CharP R p]

/-- Relative Frobenius iterated `h` times, with series `X ^ (p ^ h)`, maps to the
corresponding coefficient Frobenius twist. -/
noncomputable def iterateFrobeniusHom (h : ℕ) :
    TauCeti.FormalGroupHom F (F.map (iterateFrobenius R p h)) where
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
theorem iterateFrobeniusHom_toPowerSeries (h : ℕ) :
    (F.iterateFrobeniusHom p h).toPowerSeries = PowerSeries.X ^ (p ^ h) := (rfl)

end FormalGroup

namespace TauCeti.FormalGroupHom

section Ring

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    {F G : FormalGroup R}

/-- The factor's coefficients are selected from the original series at multiples of `p ^ h`. -/
theorem coeff_of_comp_iterateFrobeniusHom_eq (f : FormalGroupHom F G) (h : ℕ)
    (g : FormalGroupHom (F.map (iterateFrobenius R p h)) G)
    (hg : g.comp (F.iterateFrobeniusHom p h) = f) (n : ℕ) :
    PowerSeries.coeff n g.toPowerSeries = PowerSeries.coeff (p ^ h * n) f.toPowerSeries := by
  have he := congrArg (fun b : FormalGroupHom F G ↦
    PowerSeries.coeff (p ^ h * n) b.toPowerSeries) hg
  simpa only [comp_toPowerSeries, FormalGroup.iterateFrobeniusHom_toPowerSeries,
    ← PowerSeries.expand_apply _ (pow_ne_zero h (Fact.out : p.Prime).ne_zero),
    PowerSeries.coeff_expand_mul] using he

end Ring

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {F G : FormalGroup K}

/-- A homomorphism of order `p ^ h` factors through the `h`-fold relative Frobenius,
with a nonzero linear coefficient in its remaining factor. -/
private theorem exists_comp_iterateFrobeniusHom_of_order (f : FormalGroupHom F G) (h : ℕ)
    (hf : f.toPowerSeries.order = (p ^ h : ℕ)) :
    ∃ g : FormalGroupHom (F.map (iterateFrobenius K p h)) G,
      PowerSeries.coeff 1 g.toPowerSeries ≠ 0 ∧
        g.comp (F.iterateFrobeniusHom p h) = f := by
  induction h generalizing F with
  | zero =>
    have hf₁ : PowerSeries.coeff 1 f.toPowerSeries ≠ 0 := by
      simpa using (PowerSeries.order_eq_nat.mp hf).1
    let g : FormalGroupHom (F.map (iterateFrobenius K p 0)) G :=
      { toPowerSeries := f.toPowerSeries
        zero_constantCoeff := f.zero_constantCoeff
        hom := by simpa using f.hom }
    refine ⟨g, hf₁, ?_⟩
    apply FormalGroupHom.ext
    simp [g, PowerSeries.X_subst]
  | succ h ih =>
    -- Remove one Frobenius factor; its order drops from p^(h+1) to p^h.
    have hp : p.Prime := Fact.out
    have hf₁ : PowerSeries.coeff 1 f.toPowerSeries = 0 := by
      apply PowerSeries.coeff_of_lt_order
      rw [hf]
      exact_mod_cast (one_lt_pow₀ hp.one_lt (by omega : h + 1 ≠ 0))
    let g := f.frobeniusFactor (p := p) hf₁
    have hexp : PowerSeries.expand p hp.ne_zero g.toPowerSeries = f.toPowerSeries := by
      rw [PowerSeries.expand_apply]
      simpa only [comp_toPowerSeries, FormalGroup.frobeniusHom_toPowerSeries] using
        congrArg toPowerSeries (f.frobeniusFactor_comp_frobeniusHom hf₁)
    have hg₀ : g.toPowerSeries ≠ 0 := by
      intro hg
      have hf₀ : f.toPowerSeries = 0 := by simpa [hg] using hexp.symm
      rw [hf₀, PowerSeries.order_zero] at hf
      exact ENat.top_ne_natCast _ hf
    have hgord : g.toPowerSeries.order = (p ^ h : ℕ) := by
      have ho := congrArg PowerSeries.order hexp
      rw [PowerSeries.order_expand, nsmul_eq_mul, hf,
        ← PowerSeries.coe_toNat_order hg₀, ← Nat.cast_mul, pow_succ'] at ho
      have ho' : p * g.toPowerSeries.order.toNat = p * p ^ h := by exact_mod_cast ho
      rw [← PowerSeries.coe_toNat_order hg₀, Nat.mul_left_cancel hp.pos ho']
    obtain ⟨a, ha, heq⟩ := ih g hgord
    -- Compose the remaining factor with the iterated Frobenius on the twisted source.
    have htwist : (F.map (frobenius K p)).map (iterateFrobenius K p h) =
        F.map (iterateFrobenius K p (h + 1)) := by
      rw [FormalGroup.map_comp, iterateFrobenius_add, iterateFrobenius_one]
    let b : FormalGroupHom (F.map (iterateFrobenius K p (h + 1))) G :=
      { toPowerSeries := a.toPowerSeries
        zero_constantCoeff := a.zero_constantCoeff
        hom := by rw [← htwist]; exact a.hom }
    refine ⟨b, ha, ?_⟩
    apply FormalGroupHom.ext
    have he : PowerSeries.expand (p ^ h) (pow_ne_zero h hp.ne_zero) a.toPowerSeries =
        g.toPowerSeries := by
      rw [PowerSeries.expand_apply]
      simpa only [comp_toPowerSeries, FormalGroup.iterateFrobeniusHom_toPowerSeries] using
        congrArg toPowerSeries heq
    dsimp only [b]
    rw [comp_toPowerSeries, FormalGroup.iterateFrobeniusHom_toPowerSeries,
      ← PowerSeries.expand_apply _ (pow_ne_zero (h + 1) hp.ne_zero)]
    simpa only [pow_succ', PowerSeries.expand_mul p hp.ne_zero (p ^ h)
      (pow_ne_zero h hp.ne_zero), he] using hexp

/-- For a specified order `p ^ h`, the remaining factor is a unique isomorphism. -/
theorem existsUnique_iso_comp_iterateFrobeniusHom_of_order (f : FormalGroupHom F G) (h : ℕ)
    (hf : f.toPowerSeries.order = (p ^ h : ℕ)) :
    ∃! g : FormalGroupIso (F.map (iterateFrobenius K p h)) G,
      g.toHom.comp (F.iterateFrobeniusHom p h) = f := by
  obtain ⟨g, hg, heq⟩ := f.exists_comp_iterateFrobeniusHom_of_order h hf
  refine ⟨g.toIso (isUnit_iff_ne_zero.mpr hg), by simpa using heq, ?_⟩
  intro a ha
  apply FormalGroupIso.ext
  apply FormalGroupHom.ext
  rw [toIso_toHom]
  ext n
  exact (f.coeff_of_comp_iterateFrobeniusHom_eq h a.toHom ha n).trans
    (f.coeff_of_comp_iterateFrobeniusHom_eq h g heq n).symm

/-- Every nonzero formal group homomorphism over a characteristic-`p` field is an iterated
relative Frobenius followed by an isomorphism. -/
theorem exists_iso_comp_iterateFrobeniusHom (f : FormalGroupHom F G)
    (hf : f.toPowerSeries ≠ 0) :
    ∃ (h : ℕ) (g : FormalGroupIso (F.map (iterateFrobenius K p h)) G),
      f.toPowerSeries.order = (p ^ h : ℕ) ∧
        g.toHom.comp (F.iterateFrobeniusHom p h) = f := by
  obtain ⟨h, hh⟩ := F.exists_order_eq_pow_of_natCast_eq_zero G (Fact.out : p.Prime)
    (CharP.cast_eq_zero K p) f.zero_constantCoeff f.hom hf
  obtain ⟨g, hg, -⟩ := f.existsUnique_iso_comp_iterateFrobeniusHom_of_order h hh
  exact ⟨h, g, hh, hg⟩

end TauCeti.FormalGroupHom

namespace FormalGroup

variable {K : Type*} [Field K] (F : FormalGroup K) [F.IsComm]
    {p : ℕ} [Fact p.Prime] [CharP K p]

/-- For a formal group of finite height `h`, multiplication by `p` is the `h`-fold relative
Frobenius followed by a unique isomorphism from the Frobenius twist back to the group. -/
theorem existsUnique_iso_subst_X_pow_eq_nsmulSeries_of_height_eq {h : ℕ}
    (hh : F.height p = h) :
    ∃! g : TauCeti.FormalGroupIso (F.map (iterateFrobenius K p h)) F,
      PowerSeries.subst (PowerSeries.X ^ (p ^ h)) g.toHom.toPowerSeries = F.nsmulSeries p := by
  let f : TauCeti.FormalGroupHom F F :=
    { toPowerSeries := F.nsmulSeries p
      zero_constantCoeff := F.constantCoeff_nsmulSeries p
      hom := F.subst_toPowerSeries_nsmulSeries p }
  have hf : f.toPowerSeries.order = (p ^ h : ℕ) := F.height_eq_natCast_iff.mp hh
  simpa only [TauCeti.FormalGroupHom.ext_iff, TauCeti.FormalGroupHom.comp_toPowerSeries,
    iterateFrobeniusHom_toPowerSeries] using
    f.existsUnique_iso_comp_iterateFrobeniusHom_of_order h hf

end FormalGroup
