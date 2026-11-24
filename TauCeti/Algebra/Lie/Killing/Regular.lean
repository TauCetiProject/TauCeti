/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.AdjointAction.Regular
import Mathlib.Algebra.Lie.Weights.Killing
import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.Submodule.Finrank

/-!
# The minimal centralizer dimension of a Killing Lie algebra is its rank

Let `L` be a finite-dimensional Lie algebra over an infinite field `K` whose Killing form is
nondegenerate. Two notions of regularity are in use: Mathlib's `LieAlgebra.IsRegular`, where the
coefficient of index `LieAlgebra.rank K L` of the characteristic polynomial of `ad x` is nonzero,
equivalently the Engel subalgebra `engel K x` has the minimal dimension `rank K L`; and
`LieAlgebra.IsCentralizerRegular`, where the centralizer `ker (ad x)` has minimal dimension. This
file shows that the minimal centralizer dimension is the rank:

`rank K L ≤ finrank K (ker (ad x))` for every `x : L`, with equality exactly when `x` is
centralizer-regular.

Equivalently, `x` is centralizer-regular exactly when `[L, x] = range (ad x)` has dimension
`dim L - rank L`, which is the dimension of the adjoint orbit of a regular element when `L` is the
Lie algebra of an algebraic group in characteristic zero.

For `x` regular in Mathlib's sense, `engel K x` is a Cartan subalgebra
(`LieAlgebra.IsRegular.isCartanSubalgebra_engel`), and Cartan subalgebras of a Lie algebra with
nondegenerate Killing form are abelian. Since `x ∈ engel K x`, the Engel subalgebra then
centralizes `x`, so `ker (ad x) = engel K x` has dimension `rank K L`. Some element is regular in
both senses (`LieAlgebra.exists_isRegular_and_isCentralizerRegular`), so the minimal centralizer
dimension is `rank K L`. In particular every element that is regular in Mathlib's sense is
centralizer-regular. The converse fails: a nonzero nilpotent element of `sl₂` is
centralizer-regular, but its Engel subalgebra is all of `sl₂`.

## Main results

* `LieAlgebra.IsRegular.ker_ad_eq_toSubmodule_engel`: the centralizer of a regular element is its
  Engel subalgebra.
* `LieAlgebra.IsRegular.finrank_ker_ad_eq_rank`: the centralizer of a regular element has
  dimension `rank K L`.
* `LieAlgebra.rank_le_finrank_ker_ad`: every centralizer has dimension at least `rank K L`.
* `LieAlgebra.isCentralizerRegular_iff_finrank_ker_ad_eq_rank` and
  `LieAlgebra.isCentralizerRegular_iff_finrank_range_ad_add_rank_eq`: an element is
  centralizer-regular exactly when its centralizer has dimension `rank K L`, equivalently when
  `[L, x]` has dimension `dim L - rank K L`.
* `LieAlgebra.IsRegular.isCentralizerRegular`: regularity in Mathlib's sense implies
  centralizer-regularity.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9
  (1972), §15.3.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §4.1.
-/

public section

open LinearMap LieSubalgebra Module

namespace LieAlgebra

variable {K L : Type*} [Field K] [Infinite K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L]

/-- **The centralizer of a regular element is its Engel subalgebra.** The Engel subalgebra is a
Cartan subalgebra, hence abelian because the Killing form is nondegenerate, and it contains the
element. -/
theorem IsRegular.ker_ad_eq_toSubmodule_engel {x : L} (hx : IsRegular K x) :
    ker (ad K L x) = (engel K x).toSubmodule := by
  have := hx.isCartanSubalgebra_engel
  refine le_antisymm (fun y hy ↦ (mem_engel_iff K x y).mpr ⟨1, by simpa using hy⟩)
    fun y hy ↦ ?_
  have hxy : ⁅(⟨x, self_mem_engel K x⟩ : engel K x), (⟨y, hy⟩ : engel K x)⁆ = 0 :=
    trivial_lie_zero _ _ _ _
  simpa using congrArg Subtype.val hxy

/-- **The centralizer of a regular element has dimension `rank K L`.** -/
theorem IsRegular.finrank_ker_ad_eq_rank {x : L} (hx : IsRegular K x) :
    finrank K (ker (ad K L x)) = rank K L := by
  rw [hx.ker_ad_eq_toSubmodule_engel, LieSubalgebra.finrank_toSubmodule,
    (isRegular_iff_finrank_engel_eq_rank K x).mp hx]

variable (K) in
/-- **Every centralizer has dimension at least the rank.** An element that is regular both in
Mathlib's sense and in the sense of `LieAlgebra.IsCentralizerRegular` has centralizer of dimension
`rank K L`, and that dimension is minimal. -/
theorem rank_le_finrank_ker_ad (x : L) : rank K L ≤ finrank K (ker (ad K L x)) := by
  obtain ⟨y, hy, hy'⟩ := exists_isRegular_and_isCentralizerRegular K L
  rw [← hy.finrank_ker_ad_eq_rank]
  exact isCentralizerRegular_iff_forall_finrank_ker_le.mp hy' x

/-- **Regular elements have centralizers of dimension `rank K L`.** An element has minimal
centralizer dimension exactly when its centralizer has dimension the rank of `L`. -/
theorem isCentralizerRegular_iff_finrank_ker_ad_eq_rank {x : L} :
    IsCentralizerRegular K x ↔ finrank K (ker (ad K L x)) = rank K L := by
  obtain ⟨y, hy, -⟩ := exists_isRegular_and_isCentralizerRegular K L
  rw [isCentralizerRegular_iff_forall_finrank_ker_le]
  refine ⟨fun h ↦ ((h y).trans hy.finrank_ker_ad_eq_rank.le).antisymm (rank_le_finrank_ker_ad K x),
    fun h z ↦ h ▸ rank_le_finrank_ker_ad K z⟩

/-- **Regular elements have `[L, x]` of dimension `dim L - rank K L`.** An element is
centralizer-regular exactly when the range of `ad x` has dimension `finrank K L - rank K L`. -/
theorem isCentralizerRegular_iff_finrank_range_ad_add_rank_eq {x : L} :
    IsCentralizerRegular K x ↔ finrank K (range (ad K L x)) + rank K L = finrank K L := by
  have := (ad K L x).finrank_range_add_finrank_ker
  rw [isCentralizerRegular_iff_finrank_ker_ad_eq_rank]
  omega

/-- **Regularity in Mathlib's sense implies centralizer-regularity.** -/
theorem IsRegular.isCentralizerRegular {x : L} (hx : IsRegular K x) : IsCentralizerRegular K x :=
  isCentralizerRegular_iff_finrank_ker_ad_eq_rank.mpr hx.finrank_ker_ad_eq_rank

end LieAlgebra
