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
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Smooth

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

By `FormalGroup.forall_isWeaklyRegular_landweberSequence_iff_of_heightIdeal_succ_eq_top`, the unit
condition on `v₂` modulo `I₂(Ê)` collapses the entire infinite Landweber sequence at prime `p`
onto `(p, v₁)`, and hence onto `(p, A)`. Consequently:

* For any smooth-or-nodal Weierstrass family (`(c₄, Δ) = R`) — and in particular for every
  elliptic Weierstrass curve — `Ê` is Landweber regular on an `R`-module `M` if and only if `(p, A)`
  is weakly regular on `M` for every prime `p`
  (`WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_span_c₄_Δ_eq_top`,
  `WeierstrassCurve.isLandweberRegular_formalGroup_iff`). This criterion needs no flatness.
* For a singular nodal family (`Δ = 0` and `IsUnit c₄`), `I₂(Ê) = R`, so `Ê` is Landweber regular
  on `M` if and only if every prime `p` is regular on `M`
  (`WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_Δ_eq_zero_of_isUnit_c₄`).

For the universal Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆]` the sequence `(p, A)` is regular
(`WeierstrassCurve.Universal.isRegular_natCast_coeff_invariantDifferential`). Weak regularity
ascends along flat maps
(`WeierstrassCurve.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat`), so `Ê` is
Landweber regular whenever the classifying map `ℤ[a₁, ⋯, a₆] → R` of a smooth-or-nodal family
(`(c₄, Δ) = R`) or an elliptic curve is flat
(`WeierstrassCurve.isLandweberRegular_formalGroup_of_flat_of_span_c₄_Δ_eq_top`,
`WeierstrassCurve.isLandweberRegular_formalGroup_of_flat`). In particular, the formal group of
the universal elliptic curve over `ℤ[a₁, ⋯, a₆][Δ⁻¹]` is Landweber regular
(`WeierstrassCurve.Universal.isLandweberRegular_formalGroup_ellipticCurve`), and flat base change
from `ℤ[a₁, ⋯, a₆][Δ⁻¹]` gives Landweber regularity whenever `W.specializeElliptic` is flat
(`WeierstrassCurve.isLandweberRegular_formalGroup_of_flat_elliptic`).

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

* `WeierstrassCurve.isWeaklyRegular_landweberSequence_formalGroup_iff_of_span_eq_top` and
  `WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_span_c₄_Δ_eq_top`: Landweber regularity
  for smooth-or-nodal Weierstrass families reduces to weak regularity of `(p, A)`.
* `WeierstrassCurve.isWeaklyRegular_landweberSequence_formalGroup_iff` and
  `WeierstrassCurve.isLandweberRegular_formalGroup_iff`: the formal group of an elliptic curve is
  Landweber regular on `M` exactly when `(p, A)` is weakly regular on `M` for every prime `p`.
* `WeierstrassCurve.isLandweberRegular_formalGroup_iff_of_Δ_eq_zero_of_isUnit_c₄`: for nodal
  families (`Δ = 0`, `IsUnit c₄`), Landweber regularity reduces to `p`-torsion-freeness.
* `WeierstrassCurve.isLandweberRegular_formalGroup_of_flat_of_span_c₄_Δ_eq_top` and
  `WeierstrassCurve.isLandweberRegular_formalGroup_of_flat`: Landweber regularity when the
  classifying map `ℤ[a₁, ⋯, a₆] → R` is flat.
* `WeierstrassCurve.Universal.isLandweberRegular_formalGroup_ellipticCurve` and
  `WeierstrassCurve.isLandweberRegular_formalGroup_of_flat_elliptic`: Landweber regularity of the
  universal elliptic curve and along flat `W.specializeElliptic`.
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
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4 and V.3.
-/

public section

open RingTheory.Sequence TauCeti.WeierstrassChange

namespace WeierstrassCurve

section General

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p : ℕ}

private theorem isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three
    (hp : p.Prime) (M : Type*) [AddCommGroup M] [Module R M] {m : ℕ} (hm : 2 ≤ m)
    (hI : (formalGroup W).heightIdeal p 3 = ⊤) :
    IsWeaklyRegular M ((formalGroup W).landweberSequence p m) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  rw [(formalGroup W).isWeaklyRegular_landweberSequence_iff_of_heightIdeal_succ_eq_top hp M hm hI,
    FormalGroup.landweberSequence_two]
  exact W.isWeaklyRegular_natCast_coeff_nsmulSeries_iff hp M

private theorem forall_isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three
    (hp : p.Prime) (M : Type*) [AddCommGroup M] [Module R M]
    (hI : (formalGroup W).heightIdeal p 3 = ⊤) :
    (∀ m : ℕ, IsWeaklyRegular M ((formalGroup W).landweberSequence p m)) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] :=
  ((formalGroup W).forall_isWeaklyRegular_landweberSequence_iff_of_heightIdeal_succ_eq_top
    hp M hI).trans
    (W.isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three hp M le_rfl hI)

private theorem isLandweberRegular_formalGroup_iff_of_heightIdeal_three
    (M : Type*) [AddCommGroup M] [Module R M]
    (hI : ∀ ⦃p : ℕ⦄, p.Prime → (formalGroup W).heightIdeal p 3 = ⊤) :
    (formalGroup W).IsLandweberRegular M ↔
      ∀ ⦃p : ℕ⦄, p.Prime →
        IsWeaklyRegular M
          [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] := by
  rw [FormalGroup.isLandweberRegular_def]
  exact forall₂_congr fun p hp ↦
    W.forall_isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three hp M (hI hp)

/-- **Regular-sequence Landweber criterion when `(p, c₄, Δ) = R`.** For `m ≥ 2`, a prime `p`, a
Weierstrass curve `W` over `R` with `(p, c₄, Δ) = R`, and an `R`-module `M`, the Landweber
sequence `(formalGroup W).landweberSequence p m` is weakly regular on `M` if and only if `(p, A)`
is weakly regular on `M`, where `A` is the Hasse invariant in the coordinate `T = -x / y`. -/
theorem isWeaklyRegular_landweberSequence_formalGroup_iff_of_span_eq_top
    (h : Ideal.span {(p : R), W.c₄, W.Δ} = ⊤) (hp : p.Prime) (M : Type*)
    [AddCommGroup M] [Module R M] {m : ℕ} (hm : 2 ≤ m) :
    IsWeaklyRegular M ((formalGroup W).landweberSequence p m) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] :=
  W.isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three hp M hm
    ((W.heightIdeal_formalGroup_eq_top_iff hp le_rfl).mpr h)

/-- **Landweber regularity criterion for smooth-or-nodal Weierstrass families.** If
`(c₄, Δ) = R`, then `formalGroup W` is Landweber regular on an `R`-module `M` if and only if
`(p, A)` is weakly regular on `M` for every prime `p`. -/
theorem isLandweberRegular_formalGroup_iff_of_span_c₄_Δ_eq_top
    (h : Ideal.span {W.c₄, W.Δ} = ⊤) (M : Type*) [AddCommGroup M] [Module R M] :
    (formalGroup W).IsLandweberRegular M ↔
      ∀ ⦃p : ℕ⦄, p.Prime →
        IsWeaklyRegular M
          [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] :=
  W.isLandweberRegular_formalGroup_iff_of_heightIdeal_three M
    fun _ hp ↦ W.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top h hp le_rfl

/-- **Landweber regularity criterion for nodal Weierstrass families.** When `Δ = 0` and `c₄` is a
unit, `I₂(Ê) = R` for every prime `p`, so `formalGroup W` is Landweber regular on `M` if and only
if multiplication by every prime `p` is injective on `M`. -/
theorem isLandweberRegular_formalGroup_iff_of_Δ_eq_zero_of_isUnit_c₄ (hΔ : W.Δ = 0)
    (hc₄ : IsUnit W.c₄) (M : Type*) [AddCommGroup M] [Module R M] :
    (formalGroup W).IsLandweberRegular M ↔ ∀ ⦃p : ℕ⦄, p.Prime → IsSMulRegular M (p : R) := by
  rw [FormalGroup.isLandweberRegular_def]
  refine forall₂_congr fun p hp ↦ ?_
  have hI₂ : (formalGroup W).heightIdeal p 2 = ⊤ :=
    (W.heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero hΔ hp le_rfl).mpr
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hc₄)
  rw [(formalGroup W).forall_isWeaklyRegular_landweberSequence_iff_of_heightIdeal_succ_eq_top
    hp M hI₂, FormalGroup.landweberSequence_one, isWeaklyRegular_singleton_iff]

/-- **Landweber regularity for smooth-or-nodal Weierstrass families with flat classifying
morphism.** If `(c₄, Δ) = R` and `W.specialize` is flat, then `formalGroup W` is Landweber
regular on `R`. -/
theorem isLandweberRegular_formalGroup_of_flat_of_span_c₄_Δ_eq_top
    (h : Ideal.span {W.c₄, W.Δ} = ⊤) (hflat : W.specialize.Flat) :
    (formalGroup W).IsLandweberRegular R :=
  (W.isLandweberRegular_formalGroup_iff_of_span_c₄_Δ_eq_top h R).mpr
    fun _ hp ↦ W.isWeaklyRegular_natCast_coeff_invariantDifferential_of_flat hflat hp

end General

section Elliptic

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- **Direct regular-sequence Landweber criterion for an elliptic curve.** For `m ≥ 2`, a prime
`p`, an elliptic curve `W` over `R`, and an `R`-module `M`, the Landweber sequence
`(formalGroup W).landweberSequence p m` is weakly regular on `M` if and only if `(p, A)` is
weakly regular on `M`, where `A` is the Hasse invariant in the coordinate `T = -x / y`. -/
theorem isWeaklyRegular_landweberSequence_formalGroup_iff {p : ℕ} (hp : p.Prime) (M : Type*)
    [AddCommGroup M] [Module R M] {m : ℕ} (hm : 2 ≤ m) :
    IsWeaklyRegular M ((formalGroup W).landweberSequence p m) ↔
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] :=
  W.isWeaklyRegular_landweberSequence_formalGroup_iff_of_heightIdeal_three hp M hm
    (W.heightIdeal_formalGroup_eq_top hp le_rfl)

/-- **The regular-sequence criterion for Landweber exactness of an elliptic curve.** The formal
group of an elliptic Weierstrass curve `W` is Landweber regular on an `R`-module `M` exactly when,
for every prime `p`, the sequence `(p, A)` is weakly regular on `M`, where `A` is the Hasse
invariant, the coefficient of `Tᵖ⁻¹` in the invariant differential. -/
theorem isLandweberRegular_formalGroup_iff (M : Type*) [AddCommGroup M] [Module R M] :
    (formalGroup W).IsLandweberRegular M ↔ ∀ ⦃p : ℕ⦄, p.Prime →
      IsWeaklyRegular M
        [(p : R), PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential] :=
  W.isLandweberRegular_formalGroup_iff_of_heightIdeal_three M
    fun _ hp ↦ W.heightIdeal_formalGroup_eq_top hp le_rfl

/-- **Landweber exactness for a flat classifying map.** If the classifying map
`ℤ[a₁, a₂, a₃, a₄, a₆] →+* R` of an elliptic Weierstrass curve `W` is flat, then the formal group of
`W` is Landweber regular on `R`. -/
theorem isLandweberRegular_formalGroup_of_flat (h : W.specialize.Flat) :
    (formalGroup W).IsLandweberRegular R :=
  W.isLandweberRegular_formalGroup_of_flat_of_span_c₄_Δ_eq_top
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) W.isUnit_Δ) h

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
    (formalGroup ellipticCurve).IsLandweberRegular EllipticRing :=
  (ellipticCurve.isLandweberRegular_formalGroup_iff EllipticRing).mpr
    fun _ hp ↦ isWeaklyRegular_natCast_coeff_invariantDifferential_ellipticCurve hp

end Universal

/-- **Landweber regularity for elliptic curves with flat elliptic classifying morphism.** If `W`
is an elliptic Weierstrass curve over `R` whose classifying morphism
`W.specializeElliptic : ℤ[a₁, a₂, a₃, a₄, a₆][Δ⁻¹] →+* R` is flat, then `formalGroup W` is
Landweber regular on `R`. -/
theorem isLandweberRegular_formalGroup_of_flat_elliptic (hflat : W.specializeElliptic.Flat) :
    (formalGroup W).IsLandweberRegular R := by
  have h := Universal.isLandweberRegular_formalGroup_ellipticCurve.map_of_flat hflat
  rwa [← Universal.ellipticCurve.map_formalGroup W.specializeElliptic,
    W.map_specializeElliptic] at h

end Elliptic

end WeierstrassCurve
