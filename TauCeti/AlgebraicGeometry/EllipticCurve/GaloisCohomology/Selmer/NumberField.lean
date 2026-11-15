/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EmbeddingIndependence
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion
-- Proof-only: finiteness of the Selmer group cut out at the finite places.
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Finite

/-!
# The Shafarevich–Tate group of an elliptic curve over a number field

For a Weierstrass curve `W` over a number field `K`, the Shafarevich–Tate group `Sha(E/K)` is the
group of classes in `H¹(G_K, E(Kˢ))` that become trivial over the completion `K_v` at every place
`v` of `K`, finite and infinite (Silverman X.4). Here it is
`WeierstrassCurve.shafarevichTateGroup` for the family of all completions
`TauCeti.GlobalNumberFields.Place.Completion`, with a fixed choice of embeddings of separable
closures; by `WeierstrassCurve.shafarevichTateGroup_eq_shafarevichTateGroup` the subgroup does not
depend on that choice, so `WeierstrassCurve.sha` is an invariant of `W`.

The `m`-Selmer group with local conditions at all places is contained in the one with conditions
at the finite places only, which is finite (`WeierstrassCurve.finite_selmerGroup`). Through the
surjection `Sel_m(E/K) → Sha(E/K)[m]` of the `m`-descent sequence, the `m`-torsion of `Sha(E/K)`
is finite for every `m ≠ 0`. Finiteness of `Sha(E/K)` itself is conjectural; it is the hypothesis
under which the order of `Sha(E/K)` enters the arithmetic side of the Birch–Swinnerton-Dyer
conjecture.

## Main definitions

* `WeierstrassCurve.sha`: the Shafarevich–Tate group `Sha(E/K)`, local triviality being required at
  every finite and infinite place of `K`.

## Main results

* `WeierstrassCurve.sha_eq_shafarevichTateGroup` and `WeierstrassCurve.mem_sha_iff`: any family of
  embeddings of separable closures computes `Sha(E/K)`; membership is local triviality at every
  place.
* `WeierstrassCurve.finite_selmerGroup_place`: the `m`-Selmer group with local conditions at all
  places is finite for `m ≠ 0`.
* `WeierstrassCurve.finite_torsionBy_sha`: `Sha(E/K)[m]` is finite for `m ≠ 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.2.
-/

public section

noncomputable section

namespace WeierstrassCurve

open IsDedekindDomain NumberField TauCeti TauCeti.ContCohomology TauCeti.GlobalNumberFields
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- **The Shafarevich–Tate group** `Sha(E/K)` of a Weierstrass curve over a number field: the
classes in `H¹(G_K, E(Kˢ))` whose restriction to the completion of `K` at every place, finite and
infinite, vanishes. The embeddings of separable closures are a fixed choice, on which the subgroup
does not depend (`WeierstrassCurve.sha_eq_shafarevichTateGroup`). -/
def sha : AddSubgroup (H1 (AbsoluteGaloisGroup K) W.PointCoeff) :=
  W.shafarevichTateGroup (L := Place.Completion (K := K)) fun _ ↦ IsSepClosed.lift

/-- Every family of embeddings of separable closures at all places computes `Sha(E/K)`. -/
theorem sha_eq_shafarevichTateGroup
    (τ : ∀ v : Place K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    W.sha = W.shafarevichTateGroup τ :=
  W.shafarevichTateGroup_eq_shafarevichTateGroup _ τ

/-- **Membership in `Sha(E/K)`**: a class lies in the Shafarevich–Tate group exactly when it
restricts to zero at every place of `K`, for any choice of embeddings of separable closures. -/
theorem mem_sha_iff
    (τ : ∀ v : Place K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion)
    {c : H1 (AbsoluteGaloisGroup K) W.PointCoeff} :
    c ∈ W.sha ↔ ∀ v, W.pointRes (τ v) c = 0 := by
  rw [W.sha_eq_shafarevichTateGroup τ, mem_shafarevichTateGroup_iff]

/-- **The `m`-Selmer group with local conditions at all places is finite** for `m ≠ 0`, the
local conditions being the images of the Kummer maps over the completions at every finite and
infinite place (Silverman X.4.2). -/
theorem finite_selmerGroup_place [W.IsElliptic] (m : ℕ) [NeZero m]
    (τ : ∀ v : Place K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion) :
    Finite (W.selmerGroup τ m) :=
  have := W.finite_selmerGroup m fun v ↦ τ (.inl v)
  Finite.of_injective _ (AddSubgroup.inclusion_injective (W.selmerGroup_le_comp τ m Sum.inl))

/-- **The `m`-torsion `Sha(E/K)[m]` of the Shafarevich–Tate group is finite** for every
`m ≠ 0`. -/
theorem finite_torsionBy_sha [W.IsElliptic] (m : ℕ) [NeZero m] :
    Finite (AddSubgroup.torsionBy W.sha m) := by
  have hm : IsUnit (m : K) := (Nat.cast_ne_zero.2 (NeZero.ne m)).isUnit
  have := W.finite_selmerGroup_place m fun _ ↦ IsSepClosed.lift
  rw [W.sha_eq_shafarevichTateGroup fun _ ↦ IsSepClosed.lift]
  exact Finite.of_surjective _ (W.selmerShaMap_surjective _ hm)

end WeierstrassCurve
