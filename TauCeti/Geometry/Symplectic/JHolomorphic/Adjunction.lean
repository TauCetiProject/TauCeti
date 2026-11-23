/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Tactic.Linarith

/-!
# Adjunction and the index of a simple pseudoholomorphic curve

Let `X` be a closed symplectic four-manifold with canonical class `κ` and a compatible almost
complex structure `J`, and let `C` be a simple (somewhere injective) `J`-holomorphic curve in the
class `c`, whose normalization has genus `g`. Two numbers attached to `C` constrain its class in
the intersection form `B` on integral homology.

* **Singular adjunction.** The curve has a singularity number `δ ≥ 0`, which vanishes exactly
  when `C` is embedded, and `2 g - 2 + 2 δ = c · c + κ · c`.
* **Index.** The moduli space of unparametrized simple curves of genus `g` in the class `c` has
  expected real dimension `2 g - 2 + 2 c₁(c) = 2 g - 2 - 2 κ · c`. If `J` is regular for these
  curves, the moduli space through `C` is a manifold of that dimension, so the index is
  nonnegative.

`TauCeti.IsRegularSimpleCurve B κ c g δ` records these two facts. By adjunction the index is
`d(c) - 2 δ`, where `d(c) = c · c - κ · c` is the virtual dimension of the class
(`TauCeti.IsRegularSimpleCurve.index_eq`), so `2 δ ≤ d(c)`. Adding the two relations gives
`c · c ≥ g - 1 + 2 δ ≥ -1`, and their equality cases are the curves of Taubes's canonical cycles:

* a curve of negative square is an embedded exceptional sphere: `g = δ = 0` and
  `c · c = κ · c = -1` (`TauCeti.IsRegularSimpleCurve.apply_self_eq_neg_one_of_apply_self_neg`,
  `TauCeti.IsRegularSimpleCurve.apply_canonical_eq_neg_one_of_apply_self_neg`,
  `TauCeti.IsRegularSimpleCurve.genus_eq_zero_of_apply_self_neg`);
* a curve of virtual dimension zero is embedded
  (`TauCeti.IsRegularSimpleCurve.singularity_eq_zero_of_apply_canonical_eq_apply_self`);
* a curve of square zero orthogonal to `κ` is an embedded torus
  (`TauCeti.IsRegularSimpleCurve.genus_eq_one_of_apply_self_eq_zero`).

Adjunction also bounds the genus by the class, `2 g ≤ c · c + κ · c + 2`
(`TauCeti.IsRegularSimpleCurve.two_mul_genus_le`), the genus bound used to count curve types
below an area bound.

The adjunction formula and the regularity of `J` are inputs here; the geometric theorems
supplying them are separate.

## References

* D. McDuff, *The local behaviour of holomorphic curves in almost complex 4-manifolds*,
  J. Differential Geom. 34 (1991), 143–164 (singular adjunction).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Chapter 3 (the index) and Section 2.6 (adjunction).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open LinearMap (BilinForm)

namespace TauCeti

variable {H : Type*} [AddCommGroup H]

/-- The numerical properties of a simple pseudoholomorphic curve in a symplectic four-manifold
with canonical class `κ`, read in the intersection form `B` on integral homology: the curve has
class `c`, its normalization has genus `g`, and it has singularity number `δ`. They are the
singular adjunction formula `c · c + κ · c = 2 g - 2 + 2 δ`, and the nonnegativity of the index
`2 g - 2 - 2 κ · c` of unparametrized simple curves of genus `g` in the class `c`, which holds
when the almost complex structure is regular for these curves. -/
structure IsRegularSimpleCurve (B : BilinForm ℤ H) (κ c : H) (g δ : ℕ) : Prop where
  /-- The singular adjunction formula `c · c + κ · c = 2 g - 2 + 2 δ`. -/
  adjunction : B c c + B κ c = 2 * g - 2 + 2 * δ
  /-- The index `2 g - 2 - 2 κ · c` of the moduli space of the curve is nonnegative. -/
  index_nonneg : 0 ≤ 2 * (g : ℤ) - 2 - 2 * B κ c

namespace IsRegularSimpleCurve

variable {B : BilinForm ℤ H} {κ c : H} {g δ : ℕ}

/-- By adjunction, the index `2 g - 2 - 2 κ · c` of a simple curve is `d(c) - 2 δ`, where
`d(c) = c · c - κ · c` is the virtual dimension of its class. -/
theorem index_eq (h : IsRegularSimpleCurve B κ c g δ) :
    2 * (g : ℤ) - 2 - 2 * B κ c = B c c - B κ c - 2 * δ := by
  linarith [h.adjunction]

/-- The singularities of a regular simple curve cut its virtual dimension down to its index:
`2 δ ≤ c · c - κ · c`. -/
theorem two_mul_singularity_le (h : IsRegularSimpleCurve B κ c g δ) :
    2 * (δ : ℤ) ≤ B c c - B κ c := by
  linarith [h.index_eq, h.index_nonneg]

/-- A regular simple curve has nonnegative virtual dimension: `κ · c ≤ c · c`. -/
theorem apply_canonical_le_apply_self (h : IsRegularSimpleCurve B κ c g δ) :
    B κ c ≤ B c c := by
  linarith [h.two_mul_singularity_le, Int.natCast_nonneg δ]

/-- **The genus bound of adjunction**: `2 g ≤ c · c + κ · c + 2`. -/
theorem two_mul_genus_le (h : IsRegularSimpleCurve B κ c g δ) :
    2 * (g : ℤ) ≤ B c c + B κ c + 2 := by
  linarith [h.adjunction, Int.natCast_nonneg δ]

/-- Adding adjunction and the index bound: `g - 1 + 2 δ ≤ c · c`. -/
theorem genus_sub_one_add_two_mul_singularity_le (h : IsRegularSimpleCurve B κ c g δ) :
    (g : ℤ) - 1 + 2 * δ ≤ B c c := by
  linarith [h.adjunction, h.index_nonneg]

/-- A regular simple curve has square at least `-1`. -/
theorem neg_one_le_apply_self (h : IsRegularSimpleCurve B κ c g δ) : -1 ≤ B c c := by
  linarith [h.genus_sub_one_add_two_mul_singularity_le, Int.natCast_nonneg g,
    Int.natCast_nonneg δ]

/-- A regular simple curve of negative square has square `-1`. -/
theorem apply_self_eq_neg_one_of_apply_self_neg (h : IsRegularSimpleCurve B κ c g δ)
    (hc : B c c < 0) : B c c = -1 := by
  linarith [h.neg_one_le_apply_self]

/-- A regular simple curve of negative square is a sphere. -/
theorem genus_eq_zero_of_apply_self_neg (h : IsRegularSimpleCurve B κ c g δ) (hc : B c c < 0) :
    g = 0 := by
  have := h.genus_sub_one_add_two_mul_singularity_le
  omega

/-- A regular simple curve of negative square is embedded. -/
theorem singularity_eq_zero_of_apply_self_neg (h : IsRegularSimpleCurve B κ c g δ)
    (hc : B c c < 0) : δ = 0 := by
  have := h.genus_sub_one_add_two_mul_singularity_le
  omega

/-- A regular simple curve of negative square pairs with the canonical class to `-1`: it is an
exceptional sphere. -/
theorem apply_canonical_eq_neg_one_of_apply_self_neg (h : IsRegularSimpleCurve B κ c g δ)
    (hc : B c c < 0) : B κ c = -1 := by
  have := h.adjunction
  have := h.apply_self_eq_neg_one_of_apply_self_neg hc
  have := h.genus_eq_zero_of_apply_self_neg hc
  have := h.singularity_eq_zero_of_apply_self_neg hc
  omega

/-- A regular simple curve of virtual dimension zero, `κ · c = c · c`, is embedded. -/
theorem singularity_eq_zero_of_apply_canonical_eq_apply_self (h : IsRegularSimpleCurve B κ c g δ)
    (hc : B κ c = B c c) : δ = 0 := by
  have := h.two_mul_singularity_le
  omega

/-- A regular simple curve of square zero orthogonal to the canonical class is a torus. -/
theorem genus_eq_one_of_apply_self_eq_zero (h : IsRegularSimpleCurve B κ c g δ)
    (hc : B c c = 0) (hκ : B κ c = 0) : g = 1 := by
  have := h.adjunction
  have := h.index_nonneg
  omega

end IsRegularSimpleCurve

end TauCeti
