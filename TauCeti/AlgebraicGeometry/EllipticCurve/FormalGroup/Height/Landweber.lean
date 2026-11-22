/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Representable
public import TauCeti.RingTheory.FormalGroup.Height.Regular
import Mathlib.RingTheory.Regular.Flat
import Mathlib.Tactic.Algebraize
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Bound
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Smooth
import TauCeti.RingTheory.QuotSMulTop

/-!
# Landweber exactness of the formal group of an elliptic curve

Let `W` be an elliptic Weierstrass curve over a commutative ring `R` and `Ê` its formal group.
Landweber's exact functor theorem asks that `Ê` be Landweber regular on `R`: for every prime `p`
and every `n`, the sequence `(p, v₁, …, v_(n-1))` of coefficients of the `p`-series of `Ê` is
weakly regular on `R`.

For an elliptic curve the height ideals `I_n(Ê)` with `n ≥ 3` are the unit ideal and `v₂` is a
unit modulo `(p, v₁)` (`WeierstrassCurve.heightIdeal_formalGroup_eq_top`), and `v₁` may be replaced
by the Hasse invariant `A`, the coefficient of `Tᵖ⁻¹` in the invariant differential
(`WeierstrassCurve.isWeaklyRegular_natCast_coeff_nsmulSeries_iff`). So Landweber regularity of `Ê`
on an `R`-module `M` is the **regular-sequence criterion**: for every prime `p`, the sequence
`(p, A)` is weakly regular on `M` (`WeierstrassCurve.isLandweberRegular_formalGroup_iff`). This
criterion applies to every elliptic curve, without any flatness assumption.

For the universal Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆]` the sequence `(p, A)` is regular
(`WeierstrassCurve.Universal.isRegular_natCast_coeff_invariantDifferential`). Weak regularity
ascends along flat maps, so `Ê` is Landweber regular whenever the classifying map
`ℤ[a₁, ⋯, a₆] → R` of `W` is flat (`WeierstrassCurve.isLandweberRegular_formalGroup_of_flat`). In
particular the formal group of the universal elliptic curve over `ℤ[a₁, ⋯, a₆][Δ⁻¹]` is Landweber
regular (`WeierstrassCurve.Universal.isLandweberRegular_formalGroup_ellipticCurve`).

Flatness of the classifying map `Spec R → M_ell` to the moduli stack is a weaker condition. The
Weierstrass cubics form a smooth surjective atlas `Spec ℤ[a₁, ⋯, a₆]` of the stack of cubic
curves, presented by the group scheme of changes of variables, in which `M_ell` is the open
substack `Δ ≠ 0`. So `Spec R → M_ell` is flat exactly when its pullback to this atlas is flat.
That pullback is `Spec R[u, u⁻¹, r, s, t]`, the scheme of changes of variables `C` out of `W`,
and its map to the atlas classifies the target `C • W` of the universal change of variables. So
the stack-level hypothesis is that the classifying map of
`universalChange R • W.baseChange R[u, u⁻¹, r, s, t]` is flat. It follows from flatness of
`ℤ[a₁, ⋯, a₆] → R`, being the base change of the flat right unit of the Weierstrass Hopf
algebroid (`WeierstrassCurve.flat_specialize_universalChange_smul_baseChange`). Under this
hypothesis the formal group of `C • W` is Landweber regular on `R[u, u⁻¹, r, s, t]`. It is
isomorphic to the base change of `Ê`, and Landweber regularity descends along the faithfully flat
extension `R → R[u, u⁻¹, r, s, t]`
(`FormalGroup.isLandweberRegular_map_algebraMap_iff_of_faithfullyFlat`). Hence `Ê` is Landweber
regular on `R` (`WeierstrassCurve.isLandweberRegular_formalGroup_of_flat_universalChange`).

## Main results

* `WeierstrassCurve.isLandweberRegular_formalGroup_iff`: the formal group of an elliptic curve is
  Landweber regular on `M` exactly when `(p, A)` is weakly regular on `M` for every prime `p`.
* `WeierstrassCurve.isLandweberRegular_formalGroup_of_flat`: Landweber regularity when the
  classifying map `ℤ[a₁, ⋯, a₆] → R` is flat.
* `WeierstrassCurve.Universal.isLandweberRegular_formalGroup_ellipticCurve`: the formal group of
  the universal elliptic curve is Landweber regular.
* `WeierstrassCurve.isLandweberRegular_formalGroup_of_flat_universalChange`: Landweber regularity
  when the classifying map to the moduli stack is flat, tested on the Weierstrass atlas.

## References

* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire
  Bourbaki 1005 (2009), §3.2.
* C. L. Douglas, J. Francis, A. G. Henriques and M. A. Hill (eds.), *Topological modular forms*,
  Mathematical Surveys and Monographs 201, AMS (2014), Chapter 4 (elliptic cohomology theories
  from the Landweber exact functor theorem).
-/

public section

open RingTheory.Sequence TauCeti.WeierstrassChange

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **The regular-sequence criterion for Landweber exactness of an elliptic curve.** The formal
group of an elliptic Weierstrass curve `W` is Landweber regular on an `R`-module `M` exactly when,
for every prime `p`, the sequence `(p, A)` is weakly regular on `M`, where `A` is the Hasse
invariant, the coefficient of `Tᵖ⁻¹` in the invariant differential. -/
theorem isLandweberRegular_formalGroup_iff (M : Type*) [AddCommGroup M] [Module R M] :
    (formalGroup W).IsLandweberRegular M ↔ ∀ ⦃p : ℕ⦄, p.Prime →
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  rw [FormalGroup.isLandweberRegular_def]
  refine forall₂_congr fun p hp ↦ ?_
  rw [(formalGroup W).forall_isWeaklyRegular_landweberSequence_iff_of_heightIdeal_eq_top hp M
      (W.heightIdeal_formalGroup_eq_top hp le_rfl),
    ← W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp M, ← FormalGroup.landweberSequence_two,
    (formalGroup W).isWeaklyRegular_landweberSequence_iff hp M,
    (formalGroup W).isWeaklyRegular_landweberSequence_iff hp M]
  refine ⟨fun h i hi ↦ h i (by omega), fun h i hi ↦ ?_⟩
  obtain hi | rfl : i < 2 ∨ i = 2 := by omega
  · exact h i hi
  -- `v₂` is a unit modulo `I₂`, so it acts invertibly on `M ⧸ I₂ M`
  exact Ideal.isSMulRegular_quotient_smul_top_of_isUnit_mk _
    (W.isUnit_mk_coeff_nsmulSeries_formalGroup hp)

/-- **Landweber exactness for a flat classifying map.** If the classifying map
`ℤ[a₁, a₂, a₃, a₄, a₆] →+* R` of an elliptic Weierstrass curve `W` is flat, then the formal group of
`W` is Landweber regular on `R`. -/
theorem isLandweberRegular_formalGroup_of_flat (h : W.specialize.Flat) :
    (formalGroup W).IsLandweberRegular R := by
  algebraize [W.specialize]
  refine (W.isLandweberRegular_formalGroup_iff R).mpr fun p hp ↦ ?_
  have := (Universal.isRegular_natCast_coeff_invariantDifferential hp).toIsWeaklyRegular.of_flat (S
      := R)
  -- specialization carries the universal Hasse invariant to that of `W`
  simpa only [List.map_cons, List.map_nil, map_natCast, RingHom.algebraMap_toAlgebra,
    ← PowerSeries.coeff_map, FormalGroup.map_invariantDifferential, ← map_formalGroup,
    map_specialize] using this

/-- **Landweber exactness for a flat classifying map to the moduli stack.** Let `W` be an elliptic
Weierstrass curve over `R` and `S = R[u, u⁻¹, r, s, t]` the ring of changes of variables over `R`.
The map `Spec S → Spec ℤ[a₁, a₂, a₃, a₄, a₆]` classifying the universal change of variables
`C • W` of `W` is the pullback to the Weierstrass atlas of the classifying map `Spec R → M_ell`.
If it is flat, then the formal group of `W` is Landweber regular on `R`. -/
theorem isLandweberRegular_formalGroup_of_flat_universalChange
    (h : (ChangeRing.universalChange R • W.baseChange (ChangeRing R)).specialize.Flat) :
    (formalGroup W).IsLandweberRegular R := by
  have hreg := isLandweberRegular_formalGroup_of_flat _ h
  rw [VariableChange.formalGroup_smul, FormalGroup.isLandweberRegular_smul_iff, baseChange,
    map_formalGroup] at hreg
  exact (FormalGroup.isLandweberRegular_map_algebraMap_iff_of_faithfullyFlat _ _).mp hreg

namespace Universal

/-- **The universal elliptic curve is Landweber exact.** The formal group of the universal elliptic
Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆][Δ⁻¹]` is Landweber regular. -/
theorem isLandweberRegular_formalGroup_ellipticCurve :
    (formalGroup ellipticCurve).IsLandweberRegular EllipticRing := by
  refine ellipticCurve.isLandweberRegular_formalGroup_of_flat ?_
  have : ellipticCurve.specialize = algebraMap (MvPolynomial Coeff ℤ) EllipticRing := by
    ext i <;> simp [baseChange]
  rw [this, RingHom.flat_algebraMap_iff]
  exact IsLocalization.flat _ (.powers curve.Δ)

end Universal

end WeierstrassCurve
