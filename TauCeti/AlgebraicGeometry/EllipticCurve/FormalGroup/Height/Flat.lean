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
import TauCeti.RingTheory.Regular.RegularSequence

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
  `R[u, u⁻¹, r, s, t]`. This step holds for any curve whose specialization map from `A` is flat
  (`WeierstrassCurve.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat`).
* The second height ideal `(p, A_W)` does not depend on the Weierstrass equation
  (`WeierstrassCurve.VariableChange.heightIdeal_formalGroup_variableChange`), so `(p, A_W)` is
  weakly regular on `R[u, u⁻¹, r, s, t]` as well
  (`RingTheory.Sequence.isWeaklyRegular_append_singleton_iff_of_ofList_eq`).
* The ring `R[u, u⁻¹, r, s, t]` is faithfully flat over `R`, so `(p, A_W)` is weakly regular on `R`
  (`RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat`).

Regularity of a characteristic-`p` curve fails, since `p = 0` on `R`, even for an ordinary elliptic
curve; the hypothesis is flatness of the classifying map, not smoothness of the curve. For the
universal curve, the projection from the atlas pullback `Spec A[u, u⁻¹, r, s, t]` to `Spec A` is
induced by the right unit of the Weierstrass Hopf algebroid. The right unit is flat
(`TauCeti.WeierstrassHopfAlgebroid.flat_rightUnit`), so the classifying map of the universal curve
is flat.

When the third height ideal `I₃` is the unit ideal at every prime, for instance for an elliptic
curve, the full Landweber condition, in all heights, is
`isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat_universalChange` in
`WeierstrassCurve`, in `TauCeti/AlgebraicGeometry/EllipticCurve/FormalGroup/Height/Landweber.lean`.
The results here do not assume that the discriminant is a unit, so they apply over the base `R` of
a flatly classified family of Weierstrass curves that may have nodal fibres, not over the
individual fibres.

## Main results

* `WeierstrassCurve.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat_universalChange`:
  if the classifying map of `W` is flat, then `(p, A_W)` is a weakly regular sequence on `R`.
* `WeierstrassCurve.isWeaklyRegular_natCast_coeff_nsmulSeries_of_flat_universalChange`: if the
  classifying map of `W` is flat, then `(p, v₁)` is a weakly regular sequence on `R`.

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

/-- **Landweber regularity of the Hasse invariant for a flat classifying map.** Suppose the map
`Spec R → M_cub` classified by `W` is flat: the specialization of the universal curve to `C • W`,
for the universal change of variables `C` over `R[u, u⁻¹, r, s, t]`, is a flat ring homomorphism.
Then for every prime `p`, the sequence of `p` and the Hasse invariant of `W` is weakly regular on
`R`. -/
theorem isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat_universalChange (hp : p.Prime)
    (hW : (ChangeRing.universalChange R • W.baseChange (ChangeRing R)).specialize.Flat) :
    IsWeaklyRegular R
      [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  set W' := W.baseChange (ChangeRing R)
  -- flat base change of the universal regular sequence `(p, A)` gives `(p, A_{C • W'})`, and the
  -- second height ideal `(p, A)` is the same for `C • W'` and `W'`
  have hV : IsWeaklyRegular (ChangeRing R)
      [(p : ChangeRing R), PowerSeries.coeff (p - 1) (formalGroup W').invariantDifferential] :=
    (isWeaklyRegular_append_singleton_iff_of_ofList_eq (rs := [(p : ChangeRing R)]) (by
      simp only [Ideal.ofList_append, Ideal.ofList_singleton, ← Ideal.span_insert]
      rw [← heightIdeal_formalGroup_two _ hp, ← heightIdeal_formalGroup_two _ hp,
        VariableChange.heightIdeal_formalGroup_variableChange])).mp
    ((ChangeRing.universalChange R • W').isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat
      hW hp)
  -- and `R[u, u⁻¹, r, s, t]` is faithfully flat over `R`
  rw [← isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat (S := ChangeRing R)]
  simpa only [List.map_cons, List.map_nil, map_natCast, W', baseChange, map_formalGroup,
    ← FormalGroup.map_invariantDifferential, PowerSeries.coeff_map] using hV

/-- **Landweber's conditions in heights `0` and `1` for a flat classifying map.** If the map
`Spec R → M_cub` classified by `W` is flat, then for every prime `p`, the sequence `(p, v₁)` formed
by `p` and the coefficient of `Tᵖ` in the `p`-series of the formal group of `W` is weakly regular
on `R`: `p` is a non-zero-divisor on `R` and `v₁` is a non-zero-divisor on `R ⧸ p`. -/
theorem isWeaklyRegular_natCast_coeff_nsmulSeries_of_flat_universalChange (hp : p.Prime)
    (hW : (ChangeRing.universalChange R • W.baseChange (ChangeRing R)).specialize.Flat) :
    IsWeaklyRegular R [(p : R), PowerSeries.coeff p ((formalGroup W).nsmulSeries p)] :=
  (W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp R).mpr
    (W.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat_universalChange hp hW)

end WeierstrassCurve
