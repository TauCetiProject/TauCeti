/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Group

/-!
# Transferring a conjugated power along conjugation

Let `φ` be an endomorphism of a group `G` and `pow : G → G` a map commuting with conjugation,
`pow (q * x * q⁻¹) = q * pow x * q⁻¹`; the motivating example is a `p`-adic or profinite power
on a profinite group. If `φ` carries `x` to the conjugate `c⁻¹ * pow x * c`, then it carries every
conjugate `y = q * x * q⁻¹` to a conjugate of `pow y`, and the conjugator is computed:

`φ y = d⁻¹ * pow y * d` with `d = q * c * (φ q)⁻¹`.

The conjugator involves `φ q`; it is not obtained by multiplying `c` by `q` on one side. This is
the step that moves a statement about the image of one peripheral element under an automorphism
of a free group to a statement about another choice of that element in its conjugacy class, such
as the two conventions `(P * T)⁻¹` and `(T * P)⁻¹` for the third peripheral element of a free
group on `P` and `T`.

## Main results

* `TauCeti.map_conj_eq_conj_of_map_eq_conj`: the conjugation-transfer lemma.
-/

public section

namespace TauCeti

/-- **The conjugation-transfer lemma.** Let `φ` be an endomorphism of a group `G` and `pow` a self
map of `G` commuting with conjugation. If `φ x = c⁻¹ * pow x * c`, then for every `q` the image of
the conjugate `q * x * q⁻¹` is the conjugate of `pow (q * x * q⁻¹)` by `q * c * (φ q)⁻¹`. -/
theorem map_conj_eq_conj_of_map_eq_conj {G M : Type*} [Group G] [FunLike M G G]
    [MonoidHomClass M G G] (φ : M) (pow : G → G)
    (hpow : ∀ q x : G, pow (q * x * q⁻¹) = q * pow x * q⁻¹) {x c : G}
    (hx : φ x = c⁻¹ * pow x * c) (q : G) :
    φ (q * x * q⁻¹) = (q * c * (φ q)⁻¹)⁻¹ * pow (q * x * q⁻¹) * (q * c * (φ q)⁻¹) := by
  rw [map_mul, map_mul, map_inv, hx, hpow]
  group

end TauCeti
