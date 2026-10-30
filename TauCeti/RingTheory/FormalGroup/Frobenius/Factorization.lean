/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Frobenius.Basic
public import TauCeti.RingTheory.FormalGroup.Height
import TauCeti.RingTheory.FormalGroup.BaseChange
import TauCeti.RingTheory.PowerSeries.Expand

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
  simpa only [comp_iterateFrobeniusHom_toPowerSeries, PowerSeries.coeff_expand_mul] using he

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
    let g := f.ofSourceEq (by simp : F = F.map (iterateFrobenius K p 0))
    refine ⟨g, by simpa [g] using hf₁, ?_⟩
    apply FormalGroupHom.ext
    simp [g, comp_toPowerSeries, PowerSeries.X_subst]
  | succ h ih =>
    -- Remove one Frobenius factor; its order drops from p^(h+1) to p^h.
    have hp : p.Prime := Fact.out
    have hf₁ : PowerSeries.coeff 1 f.toPowerSeries = 0 := by
      apply PowerSeries.coeff_of_lt_order
      rw [hf]
      exact_mod_cast (one_lt_pow₀ hp.one_lt (by omega : h + 1 ≠ 0))
    let g := f.frobeniusFactor (p := p) hf₁
    have hexp : PowerSeries.expand p hp.ne_zero g.toPowerSeries = f.toPowerSeries := by
      simpa only [g, frobeniusFactor_toPowerSeries] using
        PowerSeries.expand_cartier_of_derivative_eq_zero (f.derivative_eq_zero_iff.mpr hf₁)
    have hgord : g.toPowerSeries.order = (p ^ h : ℕ) :=
      PowerSeries.order_eq_of_order_expand_eq p hp.ne_zero (by rw [hexp, hf, pow_succ'])
    obtain ⟨a, ha, heq⟩ := ih g hgord
    -- Compose the remaining factor with the iterated Frobenius on the twisted source.
    have htwist : (F.map (frobenius K p)).map (iterateFrobenius K p h) =
        F.map (iterateFrobenius K p (h + 1)) := by
      rw [FormalGroup.map_comp, iterateFrobenius_add, iterateFrobenius_one]
    let b := a.ofSourceEq htwist
    refine ⟨b, by simpa [b] using ha, ?_⟩
    apply FormalGroupHom.ext
    have he : PowerSeries.expand (p ^ h) (pow_ne_zero h hp.ne_zero) a.toPowerSeries =
        g.toPowerSeries := by
      simpa only [comp_iterateFrobeniusHom_toPowerSeries] using congrArg toPowerSeries heq
    rw [comp_iterateFrobeniusHom_toPowerSeries]
    simp only [b, ofSourceEq_toPowerSeries]
    simpa only [pow_succ', PowerSeries.expand_mul p hp.ne_zero (p ^ h)
      (pow_ne_zero h hp.ne_zero), he] using hexp

/-- The invertible factor remaining after removing `h` relative Frobenius factors from a
homomorphism of order `p ^ h`. -/
noncomputable def iterateFrobeniusIso (f : FormalGroupHom F G) (h : ℕ)
    (hf : f.toPowerSeries.order = (p ^ h : ℕ)) :
    FormalGroupIso (F.map (iterateFrobenius K p h)) G :=
  (f.exists_comp_iterateFrobeniusHom_of_order h hf).choose.toIso
    (isUnit_iff_ne_zero.mpr (f.exists_comp_iterateFrobeniusHom_of_order h hf).choose_spec.1)

/-- The invertible factor composes with iterated relative Frobenius to recover the map. -/
@[simp]
theorem iterateFrobeniusIso_comp_iterateFrobeniusHom (f : FormalGroupHom F G) (h : ℕ)
    (hf : f.toPowerSeries.order = (p ^ h : ℕ)) :
    (f.iterateFrobeniusIso h hf).toHom.comp (F.iterateFrobeniusHom p h) = f := by
  simpa only [iterateFrobeniusIso, toIso_toHom] using
    (f.exists_comp_iterateFrobeniusHom_of_order h hf).choose_spec.2

/-- The invertible factor selects the coefficients in degrees divisible by `p ^ h`. -/
@[simp]
theorem coeff_iterateFrobeniusIso (f : FormalGroupHom F G) (h : ℕ)
    (hf : f.toPowerSeries.order = (p ^ h : ℕ)) (n : ℕ) :
    PowerSeries.coeff n (f.iterateFrobeniusIso h hf).toHom.toPowerSeries =
      PowerSeries.coeff (p ^ h * n) f.toPowerSeries :=
  f.coeff_of_comp_iterateFrobeniusHom_eq h _
    (f.iterateFrobeniusIso_comp_iterateFrobeniusHom h hf) n

/-- For a specified order `p ^ h`, the remaining factor is a unique isomorphism. -/
theorem existsUnique_iso_comp_iterateFrobeniusHom_of_order (f : FormalGroupHom F G) (h : ℕ)
    (hf : f.toPowerSeries.order = (p ^ h : ℕ)) :
    ∃! g : FormalGroupIso (F.map (iterateFrobenius K p h)) G,
      g.toHom.comp (F.iterateFrobeniusHom p h) = f := by
  refine ⟨f.iterateFrobeniusIso h hf, f.iterateFrobeniusIso_comp_iterateFrobeniusHom h hf, ?_⟩
  intro a ha
  apply FormalGroupIso.ext
  apply FormalGroupHom.ext
  ext n
  rw [coeff_iterateFrobeniusIso]
  exact f.coeff_of_comp_iterateFrobeniusHom_eq h a.toHom ha n

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

/-- The isomorphism from the height-fold coefficient Frobenius twist back to a finite-height
formal group, obtained by factoring its `p`-series. -/
noncomputable def heightFrobeniusIso {h : ℕ} (hh : F.height p = h) :
    TauCeti.FormalGroupIso (F.map (iterateFrobenius K p h)) F :=
  (F.nsmulHom p).iterateFrobeniusIso h
    (by simpa only [nsmulHom_toPowerSeries] using F.height_eq_natCast_iff.mp hh)

/-- The height factor selects coefficients of the `p`-series in degrees divisible by `p ^ h`. -/
@[simp]
theorem coeff_heightFrobeniusIso {h : ℕ} (hh : F.height p = h) (n : ℕ) :
    PowerSeries.coeff n (F.heightFrobeniusIso hh).toHom.toPowerSeries =
      PowerSeries.coeff (p ^ h * n) (F.nsmulSeries p) := by
  simp only [heightFrobeniusIso, TauCeti.FormalGroupHom.coeff_iterateFrobeniusIso,
    nsmulHom_toPowerSeries]

/-- The height factor composed with the height-fold relative Frobenius is the `p`-series. -/
@[simp]
theorem heightFrobeniusIso_comp_iterateFrobeniusHom {h : ℕ} (hh : F.height p = h) :
    (F.heightFrobeniusIso hh).toHom.comp (F.iterateFrobeniusHom p h) = F.nsmulHom p := by
  simp only [heightFrobeniusIso,
    TauCeti.FormalGroupHom.iterateFrobeniusIso_comp_iterateFrobeniusHom]

/-- For a formal group of finite height `h`, multiplication by `p` is the `h`-fold relative
Frobenius followed by a unique isomorphism from the Frobenius twist back to the group. -/
theorem existsUnique_iso_comp_iterateFrobeniusHom_eq_nsmulHom_of_height_eq {h : ℕ}
    (hh : F.height p = h) :
    ∃! g : TauCeti.FormalGroupIso (F.map (iterateFrobenius K p h)) F,
      g.toHom.comp (F.iterateFrobeniusHom p h) = F.nsmulHom p :=
  (F.nsmulHom p).existsUnique_iso_comp_iterateFrobeniusHom_of_order h
    (by simpa only [nsmulHom_toPowerSeries] using F.height_eq_natCast_iff.mp hh)

end FormalGroup
