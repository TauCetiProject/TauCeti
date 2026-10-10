/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact

/-!
# The Kummer map of an elliptic curve and the `m`-descent sequence

Let `W` be an elliptic curve over a field `K`, `Kˢ` a separable closure, `G_K` its Galois group,
and `m` a natural number invertible in `K`. The Kummer sequence

```text
0 ⟶ E(Kˢ)[m] ⟶ E(Kˢ) ⟶ E(Kˢ) ⟶ 0
```

of discrete `G_K`-modules is `WeierstrassCurve.kummerShortExact`. Its degree-zero connecting map,
read through the identification `WeierstrassCurve.basePointEquivInvariants` of `H⁰(G_K, E(Kˢ))`
with `E(K)`, is the **Kummer map** `E(K) → H¹(G_K, E[m])`. This file constructs it, computes it on
cocycles, and proves the **`m`-descent exact sequence** (Silverman VIII.2, X.4)

```text
0 ⟶ E(K) ⧸ m E(K) ⟶ H¹(G_K, E[m]) ⟶ H¹(G_K, E)[m] ⟶ 0.
```

The computation is the classical one. Choose `Q ∈ E(Kˢ)` with `m • Q = P`; then `σ ↦ σ Q - Q`
takes values in `E[m]`, since `P` is fixed by `G_K`, and it is a continuous `1`-cocycle, its image
in `E(Kˢ)` being the coboundary of `Q`. Its class is the Kummer class of `P`.

The three exactness statements are read off the long exact sequence of continuous cohomology. At
`E(K) ⧸ m E(K)` it is exactness at `H⁰(G_K, E(Kˢ))`, `explicitLongExact_H0C`, together with the
commuting square `WeierstrassCurve.explicitCoeff0_basePointEquivInvariants`: multiplication by `m`
on the invariants is multiplication by `m` on `E(K)`. At `H¹(G_K, E[m])` it is exactness at the
node where `δ⁰` lands, `explicitLongExact_H1A`. At `H¹(G_K, E)` it is exactness at the middle
node, `explicitLongExact_H1B`, together with the fact that multiplication by `m` on coefficients
induces multiplication by `m` on `H¹`.

The construction follows that of the Kummer map of the multiplicative group,
`TauCeti.kummerMap`. That map is surjective by Hilbert 90; here the cokernel `H¹(G_K, E)[m]` is
the `m`-torsion of the Weil–Châtelet group `H¹(G_K, E)`, which is not zero in general. The
`m`-Selmer group and the Shafarevich–Tate group are cut out of the two outer terms of this
sequence by local conditions.

## Main definitions

* `WeierstrassCurve.kummerCocycle`: the cocycle `σ ↦ σ Q - Q` attached to an `m`th division point.
* `WeierstrassCurve.kummerMap`: the Kummer map `E(K) → H¹(G_K, E[m])`.
* `WeierstrassCurve.kummerClassMap`: the induced map on `E(K) ⧸ m E(K)`.

## Main results

* `WeierstrassCurve.kummerMap_eq_H1pi`: the Kummer class of `P` is the class of `σ ↦ σ Q - Q`, for
  any `Q` with `m • Q = P`.
* `WeierstrassCurve.ker_kummerMap`: the kernel of the Kummer map is `m E(K)`, with
  `WeierstrassCurve.kummerMap_eq_zero_iff` the pointwise form.
* `WeierstrassCurve.kummerClassMap_injective`: `E(K) ⧸ m E(K)` injects into `H¹(G_K, E[m])`.
* `WeierstrassCurve.range_kummerMap`: the image of the Kummer map is the kernel of
  `H¹(G_K, E[m]) → H¹(G_K, E)`.
* `WeierstrassCurve.range_explicitCoeff1_torsionCoeffIncl`: the image of
  `H¹(G_K, E[m]) → H¹(G_K, E)` is the `m`-torsion of `H¹(G_K, E)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.2 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : K))

/-! ### The Kummer cocycle -/

omit [W.IsElliptic] in
variable {W m} in
/-- **The Kummer difference is `m`-torsion**: if `m • Q` is the image of a point of `E(K)`, then
`σ Q - Q` is killed by `m`, because `G_K` fixes `m • Q`. -/
theorem smul_sub_mem_torsionCoeff {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) (σ : AbsoluteGaloisGroup K) :
    σ • Q - Q ∈ AddSubgroup.torsionBy W.PointCoeff m := by
  rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, smul_comm, hQ, smul_basePointCoeff, sub_self]

omit [W.IsElliptic] in
variable {W m} in
/-- **The Kummer cocycle** `σ ↦ σ Q - Q` attached to a point `Q` of `E(Kˢ)` with `m • Q` in
`E(K)`. -/
def kummerCocycle {P : W.toAffine.Point} {Q : W.PointCoeff} (hQ : m • Q = W.basePointCoeff P) :
    AbsoluteGaloisGroup K → W.TorsionCoeff m :=
  fun σ => ⟨σ • Q - Q, smul_sub_mem_torsionCoeff hQ σ⟩

omit [W.IsElliptic] in
variable {W m} in
@[simp]
theorem coe_kummerCocycle {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) (σ : AbsoluteGaloisGroup K) :
    (kummerCocycle hQ σ : W.PointCoeff) = σ • Q - Q :=
  (rfl)

include hm in
variable {W m} in
/-- **The Kummer cocycle is a continuous `1`-cocycle**: its image in `E(Kˢ)` is the coboundary
of `Q`. -/
theorem kummerCocycle_mem_Z1 {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) :
    kummerCocycle hQ ∈ Z1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) :=
  (W.kummerShortExact m hm).mem_Z1_of_incl_comp_eq_d0 fun σ => by
    rw [kummerShortExact_incl, AddSubgroup.coe_subtype, coe_kummerCocycle]

/-! ### The Kummer map -/

/-- **The Kummer map** `E(K) → H¹(G_K, E[m])`: the degree-zero connecting homomorphism of the
Kummer sequence of `W`, read on `E(K)` through its identification with the invariants of
`E(Kˢ)`. -/
def kummerMap : W.toAffine.Point →+ H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) :=
  (W.kummerShortExact m hm).explicitDelta0.comp (W.basePointEquivInvariants).toAddMonoidHom

/-- **The Kummer map is the degree-zero connecting homomorphism** of the Kummer sequence, read on
`P` through the identification of `E(K)` with the invariants of `E(Kˢ)`. -/
theorem kummerMap_apply (P : W.toAffine.Point) :
    W.kummerMap m hm P = (W.kummerShortExact m hm).explicitDelta0 (W.basePointEquivInvariants P) :=
  (rfl)

variable {W m} in
/-- **The Kummer class of `P` is represented by `σ ↦ σ Q - Q`**, for any `Q ∈ E(Kˢ)` with
`m • Q = P` (Silverman X.4). Such a `Q` exists because `E(Kˢ)` is divisible by `m`. -/
theorem kummerMap_eq_H1pi {P : W.toAffine.Point} {Q : W.PointCoeff}
    (hQ : m • Q = W.basePointCoeff P) :
    W.kummerMap m hm P =
      H1pi (AbsoluteGaloisGroup K) (W.TorsionCoeff m)
        ⟨kummerCocycle hQ, kummerCocycle_mem_Z1 hm hQ⟩ :=
  (W.kummerMap_apply m hm P).trans <| (W.kummerShortExact m hm).explicitDelta0_apply _ (b := Q)
    (by rw [kummerShortExact_proj, nsmulAddMonoidHom_apply, coe_basePointEquivInvariants, hQ])
    fun σ => by rw [kummerShortExact_incl, AddSubgroup.coe_subtype, coe_kummerCocycle]

/-- **Multiplication by `m` on the invariants of `E(Kˢ)` is multiplication by `m` on `E(K)`.**
This is the commuting square that turns exactness of the long exact sequence at
`H⁰(G_K, E(Kˢ))` into the computation of the kernel of the Kummer map. -/
theorem explicitCoeff0_basePointEquivInvariants (P : W.toAffine.Point) :
    explicitCoeff0 (AbsoluteGaloisGroup K) W.PointCoeff
        (W.kummerShortExact m hm).projDistribMulActionHom (W.basePointEquivInvariants P) =
      W.basePointEquivInvariants (m • P) :=
  Subtype.ext <| by
    rw [coe_explicitCoeff0, DiscreteShortExact.projDistribMulActionHom_apply, kummerShortExact_proj,
      nsmulAddMonoidHom_apply, coe_basePointEquivInvariants, coe_basePointEquivInvariants,
      map_nsmul]

/-- **The kernel of the Kummer map is `m E(K)`.** -/
theorem ker_kummerMap : (W.kummerMap m hm).ker = (nsmulAddMonoidHom m).range := by
  ext P
  rw [AddMonoidHom.mem_ker, kummerMap_apply, ← AddMonoidHom.mem_ker,
    ← (W.kummerShortExact m hm).explicitLongExact_H0C, AddMonoidHom.mem_range,
    AddMonoidHom.mem_range]
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨Q, hQ⟩ => ⟨W.basePointEquivInvariants Q, ?_⟩⟩
  · obtain ⟨Q, rfl⟩ := (W.basePointEquivInvariants).surjective u
    rw [explicitCoeff0_basePointEquivInvariants] at hu
    exact ⟨Q, (W.basePointEquivInvariants).injective hu⟩
  · rw [explicitCoeff0_basePointEquivInvariants, ← hQ, nsmulAddMonoidHom_apply]

variable {W m} in
/-- **A point has trivial Kummer class exactly when it is divisible by `m` in `E(K)`.** -/
theorem kummerMap_eq_zero_iff {P : W.toAffine.Point} :
    W.kummerMap m hm P = 0 ↔ ∃ Q : W.toAffine.Point, m • Q = P := by
  rw [← AddMonoidHom.mem_ker, ker_kummerMap, AddMonoidHom.mem_range]
  rfl

/-! ### The Kummer map on `E(K) ⧸ m E(K)` -/

/-- **The Kummer map on `E(K) ⧸ m E(K)`**, the first map of the `m`-descent sequence. It is
injective (`WeierstrassCurve.kummerClassMap_injective`). -/
def kummerClassMap :
    W.toAffine.Point ⧸ (nsmulAddMonoidHom (α := W.toAffine.Point) m).range →+
      H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) :=
  QuotientAddGroup.lift _ (W.kummerMap m hm) (W.ker_kummerMap m hm).ge

/-- The quotient Kummer map agrees with `kummerMap` on representatives. -/
@[simp]
theorem kummerClassMap_mk (P : W.toAffine.Point) :
    W.kummerClassMap m hm (QuotientAddGroup.mk P) = W.kummerMap m hm P :=
  (rfl)

/-- **`E(K) ⧸ m E(K)` injects into `H¹(G_K, E[m])`**, the kernel of the Kummer map being exactly
`m E(K)`. -/
theorem kummerClassMap_injective : Function.Injective (W.kummerClassMap m hm) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 (W.ker_kummerMap m hm).symm

/-! ### Exactness at `H¹(G_K, E[m])` and at `H¹(G_K, E)` -/

/-- **The image of the Kummer map is the kernel of `H¹(G_K, E[m]) → H¹(G_K, E)`.** -/
theorem range_kummerMap :
    (W.kummerMap m hm).range =
      (explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (W.torsionCoeffIncl m)
        continuous_of_discreteTopology).ker := by
  rw [← kummerShortExact_inclDistribMulActionHom W m hm,
    ← (W.kummerShortExact m hm).explicitLongExact_H1A]
  ext c
  refine ⟨fun ⟨P, hP⟩ => ⟨_, hP⟩, fun ⟨u, hu⟩ => ?_⟩
  obtain ⟨P, rfl⟩ := (W.basePointEquivInvariants).surjective u
  exact ⟨P, hu⟩

omit [DecidableEq K] in
include hm in
/-- **The image of `H¹(G_K, E[m]) → H¹(G_K, E)` is the `m`-torsion of `H¹(G_K, E)`**, the last
exactness statement of the `m`-descent sequence. -/
theorem range_explicitCoeff1_torsionCoeffIncl :
    (explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff m) (W.torsionCoeffIncl m)
        continuous_of_discreteTopology).range =
      AddSubgroup.torsionBy (H1 (AbsoluteGaloisGroup K) W.PointCoeff) m := by
  rw [← kummerShortExact_inclDistribMulActionHom W m hm,
    (W.kummerShortExact m hm).explicitLongExact_H1B]
  ext c
  rw [AddMonoidHom.mem_ker, AddSubgroup.torsionBy.nsmul_iff,
    explicitCoeff1_eq_nsmul _ _ _ _ fun P => by
      rw [DiscreteShortExact.projDistribMulActionHom_apply, kummerShortExact_proj,
        nsmulAddMonoidHom_apply]]

end WeierstrassCurve
