/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.RingTheory.PicardGroup.BaseChange
public import TauCeti.RingTheory.PicardGroup.TensorPower

/-!
# Frobenius acts on the Picard group by the `p`-th power

Let `R` be a commutative semiring of exponential characteristic `p`. Pulling an invertible
`R`-module `L` back along the Frobenius `frobenius R p : R →+* R` gives its `p`-th tensor power:
`R ⊗[R, φ] L ≃ L^{⊗p}`, by `a ⊗ x ↦ a • (x ⊗ ⋯ ⊗ x)`. Hence the endomorphism of the Picard group
induced by Frobenius is `L ↦ L ^ p` (`CommRing.Pic.mapRingHom_frobenius`). If `R` is perfect, the
Frobenius is a ring automorphism, so the `p`-th power map of `Pic R` is bijective: the Picard group
of a perfect ring is uniquely `p`-divisible (`CommRing.Pic.pow_left_bijective`). Through deformation
along `A_inf(R) → R` and `A_inf(R) → R^♭`, this is the input for the unique `p`-divisibility of
Picard groups of perfectoid rings.

The diagonal `x ↦ x ⊗ ⋯ ⊗ x` is additive because the tensor powers of an invertible module are
spanned by diagonal tensors in a controlled way: if `ξ y` is the value of a functional on a vector,
then `ξ y ^ n • (x₁ ⊗ ⋯ ⊗ xₙ) = (∏ ξ xᵢ) • (y ⊗ ⋯ ⊗ y)`
(`Module.Invertible.apply_pow_card_smul_tprod`). Summing over finitely many pairs `(ξⱼ, yⱼ)` with
`∑ ξⱼ yⱼ = 1`, whose `p`-th powers again sum to `1`, writes every pure tensor of `L^{⊗p}` as a
combination of diagonal tensors whose coefficients are additive in each `xᵢ` up to `p`-th powers.

The general facts used here about tensor powers of invertible modules are in
`TauCeti.RingTheory.PicardGroup.TensorPower`, and those about base change of Picard groups are in
`TauCeti.RingTheory.PicardGroup.BaseChange`.

## Main declarations

* `CommRing.Pic.mapRingHom_frobenius`: Frobenius acts on `Pic R` by `L ↦ L ^ p`.
* `CommRing.Pic.pow_left_bijective`: over a perfect ring, `L ↦ L ^ p` is bijective on `Pic R`.

## References

* B. Bhatt, P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022), proof of
  Corollary 9.7, where the Picard group of a perfect ring is noted to be uniquely `p`-divisible
  because Frobenius is an automorphism inducing multiplication by `p`.
-/

public section

noncomputable section

open Module TensorProduct PiTensorProduct

namespace CommRing.Pic

section Frobenius

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Invertible R M]
  (p : ℕ) [ExpChar R p]

/-- If `∑ ξⱼ yⱼ = 1`, every pure tensor of the `p`-th tensor power of an invertible module is a
combination of the diagonal tensors `yⱼ ⊗ ⋯ ⊗ yⱼ`. -/
private theorem tprod_eq_sum {s : Finset (Dual R M × M)} (hs : ∑ q ∈ s, q.1 q.2 = 1)
    (x : Fin p → M) :
    tprod R x = ∑ q ∈ s, (∏ i, q.1 (x i)) • tprod R fun _ : Fin p ↦ q.2 := by
  calc tprod R x = (∑ q ∈ s, q.1 q.2) ^ p • tprod R x := by rw [hs, one_pow, one_smul]
    _ = ∑ q ∈ s, q.1 q.2 ^ Fintype.card (Fin p) • tprod R x := by
        rw [sum_pow_char, Finset.sum_smul, Fintype.card_fin]
    _ = _ := Finset.sum_congr rfl fun q _ ↦ Module.Invertible.apply_pow_card_smul_tprod ..

/-- The diagonal `x ↦ x ⊗ ⋯ ⊗ x` of the `p`-th tensor power of an invertible module, which is
additive and semilinear for the Frobenius. -/
private def tprodDiagonal : M →ₛₗ[frobenius R p] ⨂[R]^p M where
  toFun x := tprod R fun _ ↦ x
  map_add' x y := by
    obtain ⟨s, hs⟩ := Module.Invertible.exists_finset_sum_apply_eq_one (R := R) (M := M)
    rw [tprod_eq_sum p hs, tprod_eq_sum p hs (fun _ ↦ x), tprod_eq_sum p hs (fun _ ↦ y),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    simp [Finset.prod_const, add_pow_expChar, add_smul]
  map_smul' r x := by
    simp [MultilinearMap.map_smul_univ, Finset.prod_const, frobenius_def]

/-- Frobenius acts on the Picard group of a semiring of exponential characteristic `p` by the
`p`-th power: the base change of an invertible module `L` along `frobenius R p` is `L^{⊗p}`. -/
@[simp]
theorem mapRingHom_frobenius (L : Pic R) : mapRingHom (frobenius R p) L = L ^ p := by
  obtain ⟨s, hs⟩ := Module.Invertible.exists_finset_sum_apply_eq_one (R := R) (M := L)
  calc mapRingHom (frobenius R p) L = mapRingHom (frobenius R p) (Pic.mk R L) := by
        rw [mk_eq_self]
    _ = Pic.mk R (⨂[R]^p L) := by
        refine mapRingHom_mk_eq_mk (tprodDiagonal p) (eq_top_iff.2 ?_)
        rw [← span_tprod_eq_top, Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        rw [tprod_eq_sum p hs x]
        exact Submodule.sum_mem _ fun q _ ↦
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩)
    _ = L ^ p := by rw [mk_tensorPower, mk_eq_self]

/-- The Picard group of a perfect semiring of exponential characteristic `p` is uniquely
`p`-divisible: `L ↦ L ^ p` is a bijection of `Pic R`. -/
theorem pow_left_bijective [PerfectRing R p] : Function.Bijective fun L : Pic R ↦ L ^ p := by
  have h : (frobeniusEquiv R p : R →+* R) = frobenius R p :=
    RingHom.ext fun x ↦ congrFun (coe_frobeniusEquiv R p) x
  convert (mapRingEquiv (frobeniusEquiv R p)).bijective using 1
  ext L
  rw [mapRingEquiv_apply, h, mapRingHom_frobenius]

end Frobenius

end CommRing.Pic
