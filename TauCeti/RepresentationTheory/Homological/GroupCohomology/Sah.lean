/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.Algebra.Group.Action.ScalarAction

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Sah's lemma for one-cocycles

Let a group `G` act on an abelian group `M`, and let `z : G` act on `M` by a map `m ↦ z • m` that
commutes with the action of `G` and for which `m ↦ z • m - m` is bijective; the typical case is a
scalar `r` of a coefficient ring with `r - 1` a unit. **Sah's lemma** says that every `1`-cocycle
is then a coboundary when `z` is central. This file proves the cocycle form that the Selmer
arguments use, in which `z` is only central *modulo the zero locus of the cocycle*: if `c` vanishes
at every element `(z * g)⁻¹ * (g * z)`, then `c` is the coboundary of the unique `m` with
`z • m - m = c z`.

The computation is the comparison of `c (g * z) = g • c z + c g` with
`c (z * g) = z • c g + c z`. The two products differ by the factor `(z * g)⁻¹ * (g * z)` on the
right, at which `c` vanishes, so `z • c g - c g = g • c z - c z`
(`groupCohomology.IsCocycle₁.smul_apply_sub_apply_eq`). Writing `c z = z • m - m` and using that
the action of `z` commutes with that of `g` turns the right-hand side into the image of
`g • m - m` under `m ↦ z • m - m`, and injectivity of that map gives `c g = g • m - m`.

This is the cocycle core of the restriction statement of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Sah.lean`: a class whose restriction to a
subgroup `L` vanishes has a representative vanishing on `L`, and if every element
`(z * g)⁻¹ * (g * z)` lies in `L` the lemma applies.

## Main statements

* `groupCohomology.IsCocycle₁.smul_apply_sub_apply_eq`: the identity
  `z • c g - c g = g • c z - c z` when `c` vanishes at `(z * g)⁻¹ * (g * z)`.
* `groupCohomology.IsCocycle₁.isCoboundary₁_of_bijective`: a `1`-cocycle vanishing at all the
  elements `(z * g)⁻¹ * (g * z)` is a coboundary when the action of `z` commutes with that of `G`
  and `m ↦ z • m - m` is bijective.
* `groupCohomology.IsCocycle₁.isCoboundary₁_of_smul_eq`: the same when `z` acts by a scalar `r` of
  a ring with `r - 1` a unit, through `TauCeti.smul_comm_of_smul_eq` and
  `TauCeti.bijective_smul_sub_of_smul_eq`.
* `groupCohomology.IsCocycle₁.isCoboundary₁_of_commute`: Sah's lemma, for `z` central in `G`.

## Provenance

The argument is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright
2026 Anthropic, PBC), file `src/New/Congruences/Selmer/SelmerData.lean`, declarations
`New.Selmer.SelmerDatum.cocycle_commutator_γ` and
`New.Selmer.SelmerDatum.cocycle_eq_zero_of_sahGroup`, where it is stated for cocycles normalised
to vanish at `z`, with values in `(O / a) ^ n` under a matrix representation. Here it is stated
for an arbitrary action and an arbitrary bijective `m ↦ z • m - m`.

## References

* C.-H. Sah, *Automorphisms of finite groups*, J. Algebra 10 (1968), 47–68: the lemma that a
  central element `z` kills `Hⁿ(G, M)` through `z - 1`.
-/

public section

namespace groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M] {c : G → M}

/-- **The Sah identity.** If a `1`-cocycle `c` vanishes at `(z * g)⁻¹ * (g * z)`, the factor by
which `g * z` differs from `z * g`, then `z • c g - c g = g • c z - c z`. -/
theorem IsCocycle₁.smul_apply_sub_apply_eq (hc : IsCocycle₁ c) {z g : G}
    (h : c ((z * g)⁻¹ * (g * z)) = 0) :
    z • c g - c g = g • c z - c z := by
  have hmul : z * g * ((z * g)⁻¹ * (g * z)) = g * z := by group
  have hgz := hc (z * g) ((z * g)⁻¹ * (g * z))
  rw [hmul, h, smul_zero, zero_add, hc g z, hc z g] at hgz
  rw [sub_eq_sub_iff_add_eq_add]
  exact hgz.symm.trans (add_comm _ _) |>.trans (by abel)

/-- **Sah's lemma, cocycle form.** Let `z : G` act on `M` by a map commuting with the action of
`G`, with `m ↦ z • m - m` bijective. A `1`-cocycle vanishing at every `(z * g)⁻¹ * (g * z)` is a
coboundary: it is `g ↦ g • m - m` for the `m` with `z • m - m = c z`. -/
theorem IsCocycle₁.isCoboundary₁_of_bijective (hc : IsCocycle₁ c) {z : G}
    (h : ∀ g, c ((z * g)⁻¹ * (g * z)) = 0) (hz : ∀ (g : G) (m : M), z • g • m = g • z • m)
    (hbij : Function.Bijective fun m : M => z • m - m) :
    IsCoboundary₁ c := by
  obtain ⟨m, hm⟩ := hbij.2 (c z)
  refine ⟨m, fun g => hbij.1 ?_⟩
  simp only at hm ⊢
  rw [hc.smul_apply_sub_apply_eq (h g), ← hm, smul_sub, smul_sub, hz]
  abel

/-- **Sah's lemma for a scalar.** If `z` acts on `M` by a scalar `r` of a ring `R` acting
compatibly with `G`, and `r - 1` is a unit, then a `1`-cocycle vanishing at every
`(z * g)⁻¹ * (g * z)` is a coboundary. -/
theorem IsCocycle₁.isCoboundary₁_of_smul_eq {R : Type*} [Ring R] [Module R M]
    [SMulCommClass G R M] (hc : IsCocycle₁ c) {z : G} (h : ∀ g, c ((z * g)⁻¹ * (g * z)) = 0)
    {r : R} (hzr : ∀ m : M, z • m = r • m) (hr : IsUnit (r - 1)) :
    IsCoboundary₁ c :=
  hc.isCoboundary₁_of_bijective h (TauCeti.smul_comm_of_smul_eq hzr)
    (TauCeti.bijective_smul_sub_of_smul_eq hzr hr)

/-- **Sah's lemma.** If `z` is central in `G` and `m ↦ z • m - m` is bijective, every `1`-cocycle
is a coboundary, so `H¹(G, M) = 0`. -/
theorem IsCocycle₁.isCoboundary₁_of_commute (hc : IsCocycle₁ c) {z : G}
    (hzG : ∀ g, Commute z g) (hbij : Function.Bijective fun m : M => z • m - m) :
    IsCoboundary₁ c :=
  hc.isCoboundary₁_of_bijective
    (fun g => by rw [(hzG g).eq, inv_mul_cancel, map_one_of_isCocycle₁ hc])
    (fun g m => by rw [← mul_smul, (hzG g).eq, mul_smul]) hbij

end groupCohomology
