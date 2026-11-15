/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Weyl-fixed weights and the barycentre of a Weyl orbit

In a root system the coroots span the coweight space, so a weight killed by every coroot is `0`.
A weight fixed by a reflection `s_α` is killed by the coroot `α^∨`, so the only weight fixed by
the whole Weyl group `W` is `0`. Applied to the sum of a Weyl orbit, counted with multiplicity,
this says that every orbit has barycentre `0`:

`∑_{w ∈ W} w x = 0`.

Over a linearly ordered field it follows that `0` lies in the convex hull of every Weyl orbit
`W x`. This is the premise under which the convexity of Lakshmibai–Seshadri paths,
`π(t) ∈ t · Conv(W λ)`, gives the unscaled containment `π(t) ∈ Conv(W λ)` for `0 ≤ t ≤ 1`; see
`TauCeti/RepresentationTheory/LSPath/ConvexHull.lean`.

The spanning hypothesis is what makes the barycentre vanish. For a root pairing whose coroots do
not span, such as one of a reductive group with a nontrivial centre, a nonzero weight `x` killed
by every coroot is fixed by `W`, its orbit is `{x}`, and `0` is not in its convex hull.

## Main results

* `RootPairing.eq_zero_of_forall_reflection_apply_eq_self`: a weight of a root system fixed by
  every reflection is `0`.
* `RootPairing.eq_zero_of_forall_weylGroup_smul_eq_self`: a weight of a root system fixed by the
  Weyl group is `0`.
* `RootPairing.sum_weylGroup_smul_eq_zero`: the Weyl translates of a weight sum to `0`.
* `RootPairing.zero_mem_convexHull_orbit_weylGroup`: `0` lies in the convex hull of every Weyl
  orbit of a root system with a finite Weyl group over a linearly ordered field. The Weyl group
  of a root system with finitely many roots is finite, by `RootPairing.finite_weylGroup`.

## References

* N. Bourbaki, *Lie groups and Lie algebras*, Chapters 4–6, Chapter VI, §1.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, §4.
-/

public section

open Function Set

namespace RootPairing

variable {ι R M N : Type*}

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsRootSystem] [NeZero (2 : R)] [IsDomain R]
  [Module.IsTorsionFree R M] {x : M}

/-- A weight of a root system fixed by every reflection `s_α` is `0`: it is killed by every
coroot `α^∨`, and the coroots span. -/
theorem eq_zero_of_forall_reflection_apply_eq_self (h : ∀ i, P.reflection i x = x) : x = 0 := by
  refine P.eq_zero_iff_forall_coroot'_eq_zero.2 fun i ↦ ?_
  have hi := h i
  rw [reflection_apply, sub_eq_self] at hi
  exact (smul_eq_zero.1 hi).resolve_right (P.ne_zero i)

/-- A weight of a root system fixed by the Weyl group is `0`. -/
theorem eq_zero_of_forall_weylGroup_smul_eq_self (h : ∀ w : P.weylGroup, w • x = x) : x = 0 :=
  P.eq_zero_of_forall_reflection_apply_eq_self fun i ↦ by
    simpa using h (weylGroup.ofIdx P i)

/-- The Weyl translates of a weight of a root system, counted with multiplicity, sum to `0`: the
sum is fixed by the Weyl group. -/
theorem sum_weylGroup_smul_eq_zero [Fintype P.weylGroup] (x : M) :
    ∑ w : P.weylGroup, w • x = 0 :=
  P.eq_zero_of_forall_weylGroup_smul_eq_self fun g ↦ by
    rw [Finset.smul_sum]
    simp_rw [smul_smul]
    exact Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ fun _ ↦ rfl

end CommRing

section LinearOrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
  (P : RootPairing ι 𝕜 M N) [P.IsRootSystem] [Finite P.weylGroup]

/-- **The barycentre of a Weyl orbit is `0`.** For a root system with a finite Weyl group over a
linearly ordered field, `0` lies in the convex hull of the Weyl orbit `W x` of every weight `x`:
it is the average of the Weyl translates of `x`. -/
theorem zero_mem_convexHull_orbit_weylGroup (x : M) :
    (0 : M) ∈ convexHull 𝕜 (MulAction.orbit P.weylGroup x) := by
  let := Fintype.ofFinite P.weylGroup
  have hmem := (convex_convexHull 𝕜 (MulAction.orbit P.weylGroup x)).sum_mem
    (t := Finset.univ) (w := fun _ ↦ (Fintype.card P.weylGroup : 𝕜)⁻¹) (z := fun w ↦ w • x)
    (fun _ _ ↦ by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)])
    fun w _ ↦ subset_convexHull 𝕜 _ (MulAction.mem_orbit x w)
  rwa [← Finset.smul_sum, P.sum_weylGroup_smul_eq_zero, smul_zero] at hmem

end LinearOrderedField

end RootPairing
