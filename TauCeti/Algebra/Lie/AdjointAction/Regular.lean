/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import TauCeti.LinearAlgebra.Matrix.Rank.Closed

/-!
# Regular elements by minimal centralizer dimension

An element `x` of a Lie algebra `L` over a field `K` is **regular** when its centralizer
`ker (ad x)` has the smallest dimension among the centralizers of all elements of `L`
(`LieAlgebra.IsCentralizerRegular`). For a semisimple Lie algebra over an algebraically closed
field of characteristic zero this minimal dimension is the rank, and the regular elements include
both the regular semisimple elements and the regular nilpotent ones. If `L` is the Lie algebra of
an affine algebraic group `G` over a field of characteristic zero, the centralizer `C_G(x)` is
smooth with Lie algebra `ker (ad x)`, so these are also the elements whose group centralizer has
minimal dimension.

This notion differs from Mathlib's `LieAlgebra.IsRegular`, which minimizes the dimension of the
Engel subalgebra, the generalized `0`-eigenspace of `ad x`. No nilpotent element of a nonzero
semisimple Lie algebra is regular in that sense, while the regular nilpotent elements are regular
in the sense of this file.

Regular elements exist, and two regular elements have centralizers of the same dimension, so
regularity is the lower bound `rank (ad x₀) ≤ rank (ad x)` for any one regular element `x₀`. In
the coordinates of a basis of a finite-dimensional `L` this bound is a Zariski-open condition,
since it asks for a nonzero minor of the matrix of `ad x`, whose entries are linear in the
coordinates of `x`. Over an infinite field the regular elements therefore form a nonempty
Zariski-open and Zariski-dense subset of `L`. Regularity is preserved by Lie algebra isomorphisms,
hence by the adjoint action, and by nonzero scalars. The element `0` is regular only when `L` is
abelian.

## Main definitions

* `LieAlgebra.IsCentralizerRegular K x`: the centralizer `ker (ad x)` has minimal dimension.

## Main results

* `LieAlgebra.exists_isCentralizerRegular`: regular elements exist.
* `LieAlgebra.IsCentralizerRegular.isCentralizerRegular_iff_finrank_ker_le`: an element is
  regular exactly when its centralizer is no larger than that of a given regular element.
* `LieAlgebra.isCentralizerRegular_iff_forall_finrank_range_le`: in finite dimension, an element is
  regular exactly when `ad x` has maximal rank.
* `LieAlgebra.isCentralizerRegular_lieEquiv_apply_iff` and
  `LieAlgebra.isCentralizerRegular_smul_iff`: invariance under Lie algebra isomorphisms and
  nonzero scalars.
* `LieAlgebra.isCentralizerRegular_zero_iff`: `0` is regular exactly when `L` is abelian.
* `LieAlgebra.not_isCentralizerRegular_of_mem_zeroLocus_vanishingIdeal`: the nonregular elements
  form a Zariski-closed set.
* `LieAlgebra.vanishingIdeal_setOfPred_isCentralizerRegular_eq_bot`: over an infinite field the
  regular elements are Zariski dense.

## References

* B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. **85** (1963),
  327–404.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, Chapter 4.
-/

public section

open LinearMap Module MvPolynomial

namespace LieAlgebra

variable (K : Type*) {L L' : Type*} [Field K] [LieRing L] [LieAlgebra K L] [LieRing L']
  [LieAlgebra K L']

attribute [local instance 100] LieRing.ofAssociativeRing

/-- An element `x` of a Lie algebra is **regular** when its centralizer `ker (ad x)` has minimal
dimension among the centralizers of all elements. Over a field of characteristic zero this is the
dimension of the group centralizer `C_G(x)` when the Lie algebra is that of an affine algebraic
group `G`. This differs from Mathlib's `LieAlgebra.IsRegular`, which minimizes the dimension of
the generalized `0`-eigenspace of `ad x`. -/
def IsCentralizerRegular (x : L) : Prop :=
  ∀ y : L, finrank K (ker (ad K L x)) ≤ finrank K (ker (ad K L y))

variable {K}

/-- Unfold `LieAlgebra.IsCentralizerRegular`. -/
theorem isCentralizerRegular_iff {x : L} :
    IsCentralizerRegular K x ↔ ∀ y : L, finrank K (ker (ad K L x)) ≤ finrank K (ker (ad K L y)) :=
  Iff.rfl

variable (K L) in
/-- Every Lie algebra has a regular element. -/
theorem exists_isCentralizerRegular : ∃ x : L, IsCentralizerRegular K x :=
  ⟨_, fun y ↦ Function.argmin_le (fun x : L ↦ finrank K (ker (ad K L x))) y⟩

/-- Two regular elements have centralizers of the same dimension. -/
theorem IsCentralizerRegular.finrank_ker_eq {x y : L} (hx : IsCentralizerRegular K x)
    (hy : IsCentralizerRegular K y) :
    finrank K (ker (ad K L x)) = finrank K (ker (ad K L y)) :=
  (hx y).antisymm (hy x)

/-- Given one regular element `x₀`, an element is regular exactly when its centralizer is no
larger than that of `x₀`. -/
theorem IsCentralizerRegular.isCentralizerRegular_iff_finrank_ker_le {x₀ : L}
    (hx₀ : IsCentralizerRegular K x₀) {x : L} :
    IsCentralizerRegular K x ↔ finrank K (ker (ad K L x)) ≤ finrank K (ker (ad K L x₀)) :=
  ⟨fun hx ↦ hx x₀, fun h y ↦ h.trans (hx₀ y)⟩

/-- In finite dimension, an element `x` is regular exactly when `ad x` has maximal rank. -/
theorem isCentralizerRegular_iff_forall_finrank_range_le [FiniteDimensional K L] {x : L} :
    IsCentralizerRegular K x ↔
      ∀ y : L, finrank K (range (ad K L y)) ≤ finrank K (range (ad K L x)) := by
  refine forall_congr' fun y ↦ ?_
  have hx := (ad K L x).finrank_range_add_finrank_ker
  have hy := (ad K L y).finrank_range_add_finrank_ker
  omega

/-- Given one regular element `x₀` of a finite-dimensional Lie algebra, an element `x` is regular
exactly when `ad x` has rank at least that of `ad x₀`. -/
theorem IsCentralizerRegular.isCentralizerRegular_iff_finrank_range_le [FiniteDimensional K L]
    {x₀ : L} (hx₀ : IsCentralizerRegular K x₀) {x : L} :
    IsCentralizerRegular K x ↔ finrank K (range (ad K L x₀)) ≤ finrank K (range (ad K L x)) := by
  rw [hx₀.isCentralizerRegular_iff_finrank_ker_le]
  have hx := (ad K L x).finrank_range_add_finrank_ker
  have hx₀' := (ad K L x₀).finrank_range_add_finrank_ker
  omega

/-- A Lie algebra isomorphism carries the centralizer of `x` onto the centralizer of its image. -/
@[simp]
theorem finrank_ker_ad_lieEquiv_apply (e : L ≃ₗ⁅K⁆ L') (x : L) :
    finrank K (ker (ad K L' (e x))) = finrank K (ker (ad K L x)) := by
  rw [← conj_ad_apply, LinearEquiv.conj_apply, ker_comp, LinearEquiv.ker_comp,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm, LinearEquiv.finrank_map_eq]

/-- **Regularity is invariant under Lie algebra isomorphisms**, in particular under the adjoint
action of a group acting by Lie algebra automorphisms. -/
@[simp]
theorem isCentralizerRegular_lieEquiv_apply_iff (e : L ≃ₗ⁅K⁆ L') {x : L} :
    IsCentralizerRegular K (e x) ↔ IsCentralizerRegular K x := by
  refine ⟨fun h y ↦ ?_, fun h y' ↦ ?_⟩
  · simpa only [finrank_ker_ad_lieEquiv_apply] using h (e y)
  · obtain ⟨y, rfl⟩ := e.surjective y'
    simpa only [LieEquiv.coe_toLieHom, finrank_ker_ad_lieEquiv_apply] using h y

/-- Regularity is invariant under multiplication by a nonzero scalar. -/
@[simp]
theorem isCentralizerRegular_smul_iff {c : K} (hc : c ≠ 0) {x : L} :
    IsCentralizerRegular K (c • x) ↔ IsCentralizerRegular K x := by
  simp only [isCentralizerRegular_iff]
  rw [_root_.map_smul, ker_smul _ _ hc]

/-- In an abelian Lie algebra the adjoint action of every element vanishes. -/
private theorem ad_eq_zero_of_isLieAbelian [IsLieAbelian L] (x : L) : ad K L x = 0 :=
  LinearMap.ext fun z ↦ by rw [ad_apply, trivial_lie_zero, LinearMap.zero_apply]

/-- **`0` is regular exactly in an abelian Lie algebra.** In a finite-dimensional Lie algebra the
centralizer of `0` is everything, so `0` is regular exactly when every centralizer is
everything. -/
@[simp]
theorem isCentralizerRegular_zero_iff [FiniteDimensional K L] :
    IsCentralizerRegular K (0 : L) ↔ IsLieAbelian L := by
  rw [isCentralizerRegular_iff, _root_.map_zero, ker_zero, finrank_top]
  refine ⟨fun h ↦ ⟨fun y z ↦ ?_⟩, fun _ y ↦ ?_⟩
  · have hy : ker (ad K L y) = ⊤ := Submodule.eq_top_of_finrank_eq ((h y).antisymm' <|
      Submodule.finrank_le _)
    rw [← ad_apply (R := K), ← mem_ker, hy]
    exact Submodule.mem_top
  · rw [ad_eq_zero_of_isLieAbelian, ker_zero, finrank_top]

/-- In an abelian Lie algebra every element is regular. -/
theorem isCentralizerRegular_of_isLieAbelian [IsLieAbelian L] (x : L) :
    IsCentralizerRegular K x := fun y ↦ by
  rw [ad_eq_zero_of_isLieAbelian, ad_eq_zero_of_isLieAbelian]

/-! ### Zariski openness and density -/

section Zariski

variable {ι : Type*} [Finite ι] (b : Basis ι K L)

/-- **The nonregular elements form a Zariski-closed set.** If no element of a set `S` is regular,
then no `x` whose coordinates lie in the common zero locus of the polynomials vanishing on the
coordinates of `S` is regular. -/
theorem not_isCentralizerRegular_of_mem_zeroLocus_vanishingIdeal {S : Set L}
    (hS : ∀ y ∈ S, ¬IsCentralizerRegular K y) {x : L}
    (hx : b.equivFun x ∈ zeroLocus K (vanishingIdeal K (b.equivFun '' S))) :
    ¬IsCentralizerRegular K x := by
  have := Module.Finite.of_basis b
  obtain ⟨x₀, hx₀⟩ := exists_isCentralizerRegular K L
  rcases S.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · simp [vanishingIdeal_empty] at hx
  -- With `p` the rank of `ad x₀`, nonregularity is the closed condition `rank (ad y) ≤ p - 1`.
  have hlt : ∀ y ∈ S, finrank K (range (ad K L y)) < finrank K (range (ad K L x₀)) := fun y hy ↦
    not_le.1 fun h ↦ hS y hy (hx₀.isCentralizerRegular_iff_finrank_range_le.2 h)
  have hle := finrank_range_le_of_mem_zeroLocus_vanishingIdeal b (ad K L).toLinearMap
    (p := finrank K (range (ad K L x₀)) - 1) (fun y hy ↦ by
      have := hlt y hy
      simp only [LieHom.coe_toLinearMap]
      omega) hx
  have := hlt y₀ hy₀
  simp only [LieHom.coe_toLinearMap] at hle
  rw [hx₀.isCentralizerRegular_iff_finrank_range_le]
  omega

/-- **The regular elements are Zariski dense.** Over an infinite field, the only polynomial
vanishing on the coordinates of every regular element is zero. -/
theorem vanishingIdeal_setOfPred_isCentralizerRegular_eq_bot [Infinite K] :
    vanishingIdeal K (b.equivFun '' {x : L | IsCentralizerRegular K x}) = ⊥ := by
  have := Module.Finite.of_basis b
  obtain ⟨x₀, hx₀⟩ := exists_isCentralizerRegular K L
  have hset : {x : L | IsCentralizerRegular K x} =
      {x | finrank K (range ((ad K L).toLinearMap x₀)) ≤
        finrank K (range ((ad K L).toLinearMap x))} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    exact hx₀.isCentralizerRegular_iff_finrank_range_le
  rw [hset]
  exact vanishingIdeal_setOfPred_le_finrank_range_eq_bot b _ le_rfl

end Zariski

end LieAlgebra
