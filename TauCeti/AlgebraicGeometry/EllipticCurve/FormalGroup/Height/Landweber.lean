/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Representable
public import TauCeti.RingTheory.FormalGroup.Height.Regular
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Bound
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Flat

/-!
# Landweber exactness of the formal group of a Weierstrass curve

Let `W` be a Weierstrass curve over a commutative ring `R` and `Ê = formalGroup W` its formal
group in the local parameter `T = -x / y`. Landweber's exact functor theorem asks that `Ê` be
Landweber regular on `R`: for every prime `p` and every `n`, the sequence `(p, v₁, …, v_(n-1))`
of coefficients of the `p`-series of `Ê` is weakly regular on `R`.

For any prime `p`, the second height ideal `I₂(Ê)` equals `(p, A)` where `A` is the Hasse
invariant `coeff (p - 1) Ê.invariantDifferential` (`WeierstrassCurve.heightIdeal_formalGroup_two`),
and `v₁` may be replaced by `A` in weak regularity of `(p, v₁)`
(`WeierstrassCurve.isWeaklyRegular_natCast_coeff_nsmulSeries_iff`). When `(p, c₄, Δ) = R` — in
particular for every smooth-or-nodal family (`(c₄, Δ) = R`) and every elliptic Weierstrass curve
(`IsUnit Δ`) — all height ideals `I_n(Ê)` for `n ≥ 3` equal `R`
(`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`), so Landweber's `v₂` is a unit modulo
`I₂(Ê)` (`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`,
`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup`), where
`WeierstrassCurve.heightIdeal_formalGroup_two` rewrites `I₂(Ê)` to `(p, A)`.

By `FormalGroup.forall_isWeaklyRegular_landweberSequence_iff_of_heightIdeal_succ_eq_top` (and
globally `FormalGroup.isLandweberRegular_iff_of_heightIdeal_succ_eq_top`), the unit condition on
`v₂` modulo `I₂(Ê)` collapses the entire infinite Landweber sequence at prime `p` onto `(p, v₁)`,
and hence onto `(p, A)`. Consequently:

* Whenever `I₃(Ê) = R` at every prime `p` — in particular for any smooth-or-nodal Weierstrass
  family (`(c₄, Δ) = R`) and for every elliptic Weierstrass curve — `Ê` is Landweber regular on an
  `R`-module `M` if and only if `(p, A)` is weakly regular on `M` for every prime `p`
  (`WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_heightIdeal_three_eq_top`,
  `WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_span_c₄_Δ_eq_top`,
  `WeierstrassCurve.isLandweberRegular_formalGroup_iff`). This criterion needs no flatness.
* For a singular family with `Δ = 0` and `(p, c₄) = R` at every prime `p` (in particular for a
  nodal family with `Δ = 0` and `IsUnit c₄`), `I₂(Ê) = R`, so `Ê` is Landweber regular on `M` if
  and only if every prime `p` is regular on `M`
  (`WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_Δ_eq_zero_of_span_natCast_c₄_eq_top`).

For the universal Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆]` the sequence `(p, A)` is regular
(`WeierstrassCurve.Universal.isRegular_natCast_coeff_invariantDifferential`). Weak regularity
ascends along flat maps
(`WeierstrassCurve.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat`), so `Ê` is
Landweber regular whenever `I₃(Ê) = R` at every prime `p` (in particular for a smooth-or-nodal
family or an elliptic curve) and the classifying map `ℤ[a₁, ⋯, a₆] → R` is flat
(`WeierstrassCurve.isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat`,
`WeierstrassCurve.isLandweberRegular_formalGroup_of_flat`). In particular, the formal group of
the universal elliptic curve over `ℤ[a₁, ⋯, a₆][Δ⁻¹]` is Landweber regular
(`WeierstrassCurve.Universal.isLandweberRegular_formalGroup_ellipticCurve`).

Flatness of the classifying map `Spec R → M_cub` to the quotient stack `M_cub` of Weierstrass
equations by Weierstrass changes of variables is a weaker condition. The universal Weierstrass
equation `Spec ℤ[a₁, ⋯, a₆]` is a smooth surjective atlas of `M_cub`, presented by the group
scheme of Weierstrass changes of variables, in which the smooth-or-nodal locus `(c₄, Δ) = R` and
`M_ell` are open substacks. So `Spec R → M_cub` is flat
exactly when its pullback to this atlas is flat. That pullback is `Spec R[u, u⁻¹, r, s, t]`, the
scheme of changes of variables `C` out of `W`, and its map to the atlas classifies the target
`C • W` of the universal change of variables. So the stack-level hypothesis is that the
classifying map of `universalChange R • W.baseChange R[u, u⁻¹, r, s, t]` is flat. It follows
from flatness of `W.specialize : ℤ[a₁, ⋯, a₆] →+* R`, since this classifying map is the composite
of the flat right unit with `ChangeRing.map W.specialize`, which is the base change of
`W.specialize` along the left unit
(`WeierstrassCurve.flat_specialize_universalChange_smul_baseChange`).
Under this flatness hypothesis `(p, A)` is weakly regular on `R` for every prime `p`, without any
assumption on `I₃(Ê)`: flat base change makes `(p, A)` for `C • W` weakly regular on
`R[u, u⁻¹, r, s, t]`, the second height ideal does not depend on the Weierstrass equation, and weak
regularity descends along the faithfully flat extension `R → R[u, u⁻¹, r, s, t]`
(`WeierstrassCurve.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat_universalChange`).
When `I₃(Ê) = R` at every prime `p`, the regular-sequence criterion then shows that `Ê` is
Landweber regular on `R` (see
`isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat_universalChange` in
`WeierstrassCurve`).

## Main results

* `WeierstrassCurve.isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three_eq_top`
  and `WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_heightIdeal_three_eq_top`: for `m ≥ 2`
  and `I₃(Ê) = ⊤` (in particular when `(p, c₄, Δ) = ⊤` or `W` is elliptic), weak regularity of the
  length-`m` Landweber sequence—and, when `I₃(Ê) = ⊤` holds at every prime `p`, Landweber
  regularity of `Ê`—reduces to `(p, A)`.
* `WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_span_c₄_Δ_eq_top` and
  `WeierstrassCurve.isLandweberRegular_formalGroup_iff`: Landweber regularity for smooth-or-nodal
  Weierstrass families and elliptic curves reduces to weak regularity of `(p, A)`.
* `WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_Δ_eq_zero_of_span_natCast_c₄_eq_top`:
  when `Δ = 0` and `(p, c₄) = R` at every prime `p` (in particular for nodal families with
  `IsUnit c₄`), Landweber regularity reduces to `p`-torsion-freeness.
* `WeierstrassCurve.isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat` and
  `WeierstrassCurve.isLandweberRegular_formalGroup_of_flat`: Landweber regularity when `I₃(Ê) = ⊤`
  at every prime `p` and for elliptic curves, respectively, when the classifying map
  `ℤ[a₁, ⋯, a₆] → R` is flat.
* `WeierstrassCurve.Universal.isLandweberRegular_formalGroup_ellipticCurve`: Landweber regularity
  of the universal elliptic curve.
* `isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat_universalChange` (in
  `WeierstrassCurve`): Landweber regularity when `I₃(Ê) = ⊤` at every prime `p` and the classifying
  map to the Weierstrass quotient stack is flat, tested on the Weierstrass atlas.

## References

* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire
  Bourbaki 1005 (2009), §3.2.
* C. L. Douglas, J. Francis, A. G. Henriques and M. A. Hill (eds.), *Topological modular forms*,
  Mathematical Surveys and Monographs 201, AMS (2014), Chapter 4 (elliptic cohomology theories
  from the Landweber exact functor theorem).
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4 and V.3.
-/

public section

open RingTheory.Sequence TauCeti.WeierstrassChange

namespace WeierstrassCurve

section General

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p : ℕ}

/-- **Regular-sequence Landweber criterion when `I₃(Ê) = ⊤`.** For `m ≥ 2`, a prime `p`, a
Weierstrass curve `W` over `R` with `(formalGroup W).heightIdeal p 3 = ⊤` (for instance when
`(p, c₄, Δ) = ⊤` via `heightIdeal_formalGroup_eq_top_iff` or when `W` is elliptic via
`heightIdeal_formalGroup_eq_top`), and an `R`-module `M`, the Landweber sequence
`(formalGroup W).landweberSequence p m` is weakly regular on `M` if and only if `(p, A)` is
weakly regular on `M`, where `A` is the Hasse invariant in the coordinate `T = -x / y`. -/
theorem isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three_eq_top
    (hp : p.Prime) (M : Type*) [AddCommGroup M] [Module R M] {m : ℕ} (hm : 2 ≤ m)
    (hI : (formalGroup W).heightIdeal p 3 = ⊤) :
    IsWeaklyRegular M ((formalGroup W).landweberSequence p m) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  rw [(formalGroup W).isWeaklyRegular_landweberSequence_iff_of_heightIdeal_succ_eq_top hp M hm hI,
    FormalGroup.landweberSequence_two]
  exact W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp M

/-- **Landweber regularity criterion when `I₃(Ê) = ⊤` at every prime.** If
`(formalGroup W).heightIdeal p 3 = ⊤` for every prime `p` (for instance when `(p, c₄, Δ) = ⊤` at
every prime `p`), then `formalGroup W` is Landweber regular on an `R`-module `M` if and only if
`(p, A)` is weakly regular on `M` for every prime `p`. -/
theorem isLandweberRegular_formalGroup_iff_of_heightIdeal_three_eq_top
    (M : Type*) [AddCommGroup M] [Module R M]
    (hI : ∀ ⦃p : ℕ⦄, p.Prime → (formalGroup W).heightIdeal p 3 = ⊤) :
    (formalGroup W).IsLandweberRegular M ↔
      ∀ ⦃p : ℕ⦄, p.Prime →
        IsWeaklyRegular M
          [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  rw [(formalGroup W).isLandweberRegular_iff_of_heightIdeal_succ_eq_top M hI]
  refine forall₂_congr fun _ hp ↦ ?_
  rw [FormalGroup.landweberSequence_two]
  exact W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp M

/-- **Landweber regularity criterion for smooth-or-nodal Weierstrass families.** If
`(c₄, Δ) = R`, then `formalGroup W` is Landweber regular on an `R`-module `M` if and only if
`(p, A)` is weakly regular on `M` for every prime `p`. -/
theorem isLandweberRegular_formalGroup_iff_of_span_c₄_Δ_eq_top
    (h : Ideal.span {W.c₄, W.Δ} = ⊤) (M : Type*) [AddCommGroup M] [Module R M] :
    (formalGroup W).IsLandweberRegular M ↔
      ∀ ⦃p : ℕ⦄, p.Prime →
        IsWeaklyRegular M
          [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] :=
  W.isLandweberRegular_formalGroup_iff_of_heightIdeal_three_eq_top M
    fun _ hp ↦ W.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top h hp le_rfl

/-- **Landweber regularity criterion when `Δ = 0` and `(p, c₄) = R` at every prime.** When `Δ = 0`
and `Ideal.span {(p : R), W.c₄} = ⊤` for every prime `p` (in particular for nodal Weierstrass
families where `IsUnit W.c₄`, via `Ideal.eq_top_of_isUnit_mem`), `I₂(Ê) = R` for every prime `p`,
so `formalGroup W` is Landweber regular on `M` if and only if multiplication by every prime `p` is
injective on `M`. -/
theorem isLandweberRegular_formalGroup_iff_of_Δ_eq_zero_of_span_natCast_c₄_eq_top (hΔ : W.Δ = 0)
    (hc₄ : ∀ ⦃p : ℕ⦄, p.Prime → Ideal.span {(p : R), W.c₄} = ⊤)
    (M : Type*) [AddCommGroup M] [Module R M] :
    (formalGroup W).IsLandweberRegular M ↔ ∀ ⦃p : ℕ⦄, p.Prime → IsSMulRegular M (p : R) :=
  (formalGroup W).isLandweberRegular_iff_of_heightIdeal_two_eq_top M fun _ hp ↦
    (W.heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero hΔ hp le_rfl).mpr (hc₄ hp)

/-- **Landweber regularity when `I₃(Ê) = ⊤` at every prime with flat classifying morphism.** If
`(formalGroup W).heightIdeal p 3 = ⊤` for every prime `p` (for instance when `(c₄, Δ) = R`, or in
particular when `W` is elliptic) and `W.specialize` is flat, then `formalGroup W` is Landweber
regular on `R`. -/
theorem isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat
    (hI : ∀ ⦃p : ℕ⦄, p.Prime → (formalGroup W).heightIdeal p 3 = ⊤) (hflat : W.specialize.Flat) :
    (formalGroup W).IsLandweberRegular R :=
  (W.isLandweberRegular_formalGroup_iff_of_heightIdeal_three_eq_top R hI).mpr
    fun _ hp ↦ W.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat hflat hp

/-- **Landweber exactness for a flat classifying map to the Weierstrass quotient stack.** Let `W`
be a Weierstrass curve over `R` with `(formalGroup W).heightIdeal p 3 = ⊤` for every prime `p`
(for instance when `(c₄, Δ) = R`), and let `S = R[u, u⁻¹, r, s, t]` be the ring of changes of
variables over `R`. The map `Spec S → Spec ℤ[a₁, a₂, a₃, a₄, a₆]` classifying the universal change
of variables `C • W` of `W` is the pullback to the Weierstrass atlas `Spec ℤ[a₁, a₂, a₃, a₄, a₆]`
of the classifying map `Spec R → M_cub` to the quotient stack `M_cub` of Weierstrass equations by
Weierstrass changes of variables. If it is flat, then the formal group of `W` is Landweber regular
on `R`. -/
theorem isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat_universalChange
    (hI : ∀ ⦃p : ℕ⦄, p.Prime → (formalGroup W).heightIdeal p 3 = ⊤)
    (h : (ChangeRing.universalChange R • W.baseChange (ChangeRing R)).specialize.Flat) :
    (formalGroup W).IsLandweberRegular R :=
  (W.isLandweberRegular_formalGroup_iff_of_heightIdeal_three_eq_top R hI).mpr fun _ hp ↦
    W.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat_universalChange hp h

end General

section Elliptic

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **The regular-sequence criterion for Landweber exactness of an elliptic curve.** The formal
group of an elliptic Weierstrass curve `W` is Landweber regular on an `R`-module `M` exactly when,
for every prime `p`, the sequence `(p, A)` is weakly regular on `M`, where `A` is the Hasse
invariant, the coefficient of `Tᵖ⁻¹` in the invariant differential. -/
theorem isLandweberRegular_formalGroup_iff (M : Type*) [AddCommGroup M] [Module R M] :
    (formalGroup W).IsLandweberRegular M ↔ ∀ ⦃p : ℕ⦄, p.Prime →
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] :=
  W.isLandweberRegular_formalGroup_iff_of_heightIdeal_three_eq_top M
    fun _ hp ↦ W.heightIdeal_formalGroup_eq_top hp le_rfl

/-- **Landweber exactness for a flat classifying map.** If the classifying map
`ℤ[a₁, a₂, a₃, a₄, a₆] →+* R` of an elliptic Weierstrass curve `W` is flat, then the formal group of
`W` is Landweber regular on `R`. -/
theorem isLandweberRegular_formalGroup_of_flat (h : W.specialize.Flat) :
    (formalGroup W).IsLandweberRegular R :=
  W.isLandweberRegular_formalGroup_of_heightIdeal_three_eq_top_of_flat
    (fun _ hp ↦ W.heightIdeal_formalGroup_eq_top hp le_rfl) h

namespace Universal

/-- **The universal elliptic curve is Landweber exact.** The formal group of the universal elliptic
Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆][Δ⁻¹]` is Landweber regular. -/
theorem isLandweberRegular_formalGroup_ellipticCurve :
    (formalGroup ellipticCurve).IsLandweberRegular EllipticRing :=
  (ellipticCurve.isLandweberRegular_formalGroup_iff EllipticRing).mpr
    fun _ hp ↦ isWeaklyRegular_natCast_coeff_invariantDifferential_ellipticCurve hp

end Universal

end Elliptic

end WeierstrassCurve
