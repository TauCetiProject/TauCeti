/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Representable
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Smooth
import TauCeti.RingTheory.Regular.Flat
import TauCeti.RingTheory.Regular.Pair

/-!
# Landweber regularity of Weierstrass curves with flat classifying map

Let `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and let `M_cub = [Spec A / G]` be the stack of Weierstrass cubics,
the quotient of `Spec A` by the group scheme `G = Spec ℤ[u, u⁻¹, r, s, t]` of changes of variables.
A Weierstrass curve `W` over a commutative ring `R` classifies a map `Spec R → M_cub`. Its pullback
along the atlas `Spec A → M_cub` is `Spec R × G = Spec R[u, u⁻¹, r, s, t]`, the scheme of changes
of variables `C` of `W`, and the projection to `Spec A` sends `C` to the target `C • W`. On rings
it is the specialization `A → R[u, u⁻¹, r, s, t]` of the universal curve to `C • W` for the
universal change `C` (`TauCeti.WeierstrassChange.ChangeRing.universalChange`). Since the atlas is
faithfully flat, `Spec R → M_cub` is flat exactly when this ring homomorphism is flat. For a curve
over which `(c₄, Δ)` generates the unit ideal, the map lands in the open substack `Mbar_ell`, and
this is flatness of `Spec R → Mbar_ell`.

This file proves Landweber's regularity conditions in heights `0` and `1` for such a curve: `p` is
a non-zero-divisor on `R` and `v₁` is a non-zero-divisor on `R ⧸ p`, for every prime `p`. Here
`v₁` is the coefficient of `Tᵖ` in the `p`-series of the formal group of `W`; equivalently, the
same holds for the Hasse invariant `A_W`, the coefficient of `Tᵖ⁻¹` in its invariant differential.

The proof transports the regularity of `(p, A)` for the universal curve
(`WeierstrassCurve.Universal.isRegular_natCast_coeff_invariantDifferential`) in three steps.
* Flat base change along `A → R[u, u⁻¹, r, s, t]` makes `(p, A_{C • W})` weakly regular on
  `R[u, u⁻¹, r, s, t]`.
* The second height ideal `(p, A_W)` does not depend on the Weierstrass equation
  (`WeierstrassCurve.VariableChange.heightIdeal_formalGroup_variableChange`), so `(p, A_W)` is
  weakly regular on `R[u, u⁻¹, r, s, t]` as well.
* The ring `R[u, u⁻¹, r, s, t]` is faithfully flat over `R`, so `(p, A_W)` is weakly regular on `R`
  (`IsBaseChange.isWeaklyRegular_map_algebraMap_iff`).

Regularity of a characteristic-`p` curve fails, since `p = 0` on `R`, even for an ordinary elliptic
curve; the hypothesis is flatness of the classifying map, not smoothness of the curve. For the
universal curve the classifying map is the right unit of the Weierstrass Hopf algebroid, which is
flat (`TauCeti.WeierstrassHopfAlgebroid.flat_rightUnit`).

## Main results

* `WeierstrassCurve.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat`: if the
  classifying map of `W` is flat, then `(p, A_W)` is a weakly regular sequence on `R`.
* `WeierstrassCurve.isWeaklyRegular_natCast_coeff_nsmulSeries_of_flat`: if the classifying map of
  `W` is flat, then `(p, v₁)` is a weakly regular sequence on `R`.

## References

* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire
  Bourbaki 1005 (2009), §3.2.
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3.
-/

public section

open RingTheory.Sequence TauCeti.WeierstrassChange

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p : ℕ}

/-- **Landweber regularity of the Hasse invariant for a flat Weierstrass curve.** Suppose the map
`Spec R → M_cub` classified by `W` is flat: the specialization of the universal curve to `C • W`,
for the universal change of variables `C` over `R[u, u⁻¹, r, s, t]`, is a flat ring homomorphism.
Then for every prime `p`, the sequence of `p` and the Hasse invariant of `W` is weakly regular on
`R`. -/
theorem isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat (hp : p.Prime)
    (hW : (ChangeRing.universalChange R • W.map (algebraMap R (ChangeRing R))).specialize.Flat) :
    IsWeaklyRegular R
      [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  set W' := W.map (algebraMap R (ChangeRing R))
  set V := ChangeRing.universalChange R • W'
  let := V.specialize.toAlgebra
  have : Module.Flat (MvPolynomial Coeff ℤ) (ChangeRing R) := RingHom.flat_algebraMap_iff.mp hW
  -- flat base change of the universal regular sequence `(p, A)` gives `(p, A_V)`
  have hV := (Universal.isRegular_natCast_coeff_invariantDifferential hp).1.of_flat
    (S := ChangeRing R)
  have hA : V.specialize
      (PowerSeries.coeff (p - 1) (formalGroup Universal.curve).invariantDifferential) =
        PowerSeries.coeff (p - 1) (formalGroup V).invariantDifferential := by
    rw [← PowerSeries.coeff_map, FormalGroup.map_invariantDifferential, ← map_formalGroup]
    exact congrArg (fun X ↦ PowerSeries.coeff (p - 1) (formalGroup X).invariantDifferential)
      (map_specialize V)
  simp only [List.map_cons, List.map_nil, map_natCast, RingHom.algebraMap_toAlgebra, hA] at hV
  -- the second height ideal `(p, A)` is the same for `V = C • W'` and `W'`
  rw [isWeaklyRegular_pair_iff_of_span_eq (b := PowerSeries.coeff (p - 1)
      (formalGroup W').invariantDifferential) (by
    rw [← heightIdeal_formalGroup_two _ hp, ← heightIdeal_formalGroup_two _ hp,
      VariableChange.heightIdeal_formalGroup_variableChange])] at hV
  -- and `R[u, u⁻¹, r, s, t]` is faithfully flat over `R`
  rw [← isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat (S := ChangeRing R)]
  simpa only [List.map_cons, List.map_nil, map_natCast, W', map_formalGroup,
    ← FormalGroup.map_invariantDifferential, PowerSeries.coeff_map] using hV

/-- **Landweber's conditions in heights `0` and `1` for a flat Weierstrass curve.** If the map
`Spec R → M_cub` classified by `W` is flat, then for every prime `p`, the sequence `(p, v₁)` formed
by `p` and the coefficient of `Tᵖ` in the `p`-series of the formal group of `W` is weakly regular
on `R`: `p` is a non-zero-divisor on `R` and `v₁` is a non-zero-divisor on `R ⧸ p`. -/
theorem isWeaklyRegular_natCast_coeff_nsmulSeries_of_flat (hp : p.Prime)
    (hW : (ChangeRing.universalChange R • W.map (algebraMap R (ChangeRing R))).specialize.Flat) :
    IsWeaklyRegular R [(p : R), PowerSeries.coeff p ((formalGroup W).nsmulSeries p)] :=
  (W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp R).mpr
    (W.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat hp hW)

end WeierstrassCurve
