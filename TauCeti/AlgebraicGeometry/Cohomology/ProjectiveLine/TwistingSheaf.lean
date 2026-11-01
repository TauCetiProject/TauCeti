/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent

/-!
# First cohomology of the twisting sheaves on the projective line

Let `ℙ¹_R = Proj R[X₀, X₁]` be the projective line over a commutative ring `R`
(`TauCeti.AlgebraicGeometry.projectiveLine`) and `𝒪(n)` its twisting sheaves
(`AlgebraicGeometry.Proj.twistingSheaf`). This file proves that `H¹(ℙ¹_R, 𝒪(n)) = 0` for every
`n ≥ -1`, over any ring. This is the vanishing half of the computation of `H¹(ℙ¹_R, 𝒪(n))` in
Hartshorne, Theorem III.5.1(b); the other half, not proved here, is that for `n ≤ -2` the group is
free of rank `-n - 1`, with basis the classes of the fractions `1 / (X₀ᵖ X₁^q)`, `p, q ≥ 1`,
`p + q = -n`.

The twisting sheaves are quasi-coherent, so they have no higher cohomology on the affine charts
`D₊(X₀)` and `D₊(X₁)`, and `H¹(ℙ¹_R, 𝒪(n))` is the quotient of the sections over the overlap
`D₊(X₀X₁)` by the differences of restrictions of sections over the two charts
(`TauCeti.AlgebraicGeometry.sectionsQuotientEquivCohomologyOne`). A section over the overlap is a
fraction `r / (X₀X₁)ᵏ` with `r` a form of degree `2k + n`. For `n ≥ -1` this degree is at least
`2k - 1`, so `r = X₀ᵏ a + X₁ᵏ b` with `a` and `b` forms of degree `k + n`
(`TauCeti.AlgebraicGeometry.projectiveLine.exists_eq_coord_pow_mul_add_coord_pow_mul`), and
`r / (X₀X₁)ᵏ = b / X₀ᵏ + a / X₁ᵏ` is a sum of sections over the two charts. For `n ≤ -2` this
fails for the monomials `X₀ᵖ X₁^q` with `p, q < k`.

## Main results

* `TauCeti.AlgebraicGeometry.projectiveLine.subsingleton_cohomology_one_twistingSheaf`:
  `H¹(ℙ¹_R, 𝒪(n)) = 0` for `n ≥ -1`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1.
* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Proj.twistingSheaf

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

open Scheme.Modules

variable (R : Type u) [CommRing R]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-- For `n ≥ -1`, every section of `𝒪(n)` over the overlap `D₊(X₀) ⊓ D₊(X₁)` of the two standard
charts is a difference of restrictions of sections over the charts. -/
private theorem range_mayerVietorisSectionsDifference_twistingSheaf_eq_top {n : ℤ}
    (hn : -1 ≤ n) :
    (mayerVietorisSectionsDifference (Proj.twistingSheaf 𝒜 n) (Proj.basicOpen 𝒜 (coord R 0))
      (Proj.basicOpen 𝒜 (coord R 1))).range = ⊤ := by
  refine AddMonoidHom.range_eq_top.mpr fun s ↦ ?_
  -- the overlap is `D₊(X₀X₁)`, on which `s` is a fraction `r / (X₀X₁)ᵏ`
  suffices h : ∀ (W : (projectiveLine R).Opens)
      (_ : Proj.basicOpen 𝒜 (coord R 0 * coord R 1) = W)
      (h₀ : W ≤ Proj.basicOpen 𝒜 (coord R 0)) (h₁ : W ≤ Proj.basicOpen 𝒜 (coord R 1))
      (s : Γ(Proj.twistingSheaf 𝒜 n, W)), ∃ t₀ t₁,
        (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE h₀).op t₀ -
          (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE h₁).op t₁ = s by
    obtain ⟨t₀, t₁, ht⟩ := h _ (Proj.basicOpen_mul _ _ _) inf_le_left inf_le_right s
    exact ⟨(t₀, t₁), (mayerVietorisSectionsDifference_apply _ _ _ t₀ t₁).trans ht⟩
  rintro W rfl h₀ h₁ s
  obtain ⟨k, j, h, r, hr, rfl⟩ := exists_eq_const_basicOpen
    (SetLike.mul_mem_graded (coord_mem R 0) (coord_mem R 1)) two_pos s
  -- `r` has degree `k + l` with `k ≤ l + 1`, so `r = X₀ᵏ a + X₁ᵏ b` with `a` and `b` of degree `l`
  obtain ⟨l, rfl⟩ : ∃ l, j = k + l := Nat.exists_eq_add_of_le (by push_cast at h; omega)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_eq_coord_pow_mul_add_coord_pow_mul R
    (by push_cast at h; omega) hr
  have hl : (l : ℤ) = (k * 1 : ℕ) + n := by push_cast at h ⊢; omega
  have hle (i : Fin 2) : Proj.basicOpen 𝒜 (coord R i) ≤ Proj.basicOpen 𝒜 (coord R i ^ k) :=
    fun x hx hxk ↦ hx (x.isPrime.mem_of_pow_mem k hxk)
  -- then `r / (X₀X₁)ᵏ = b / X₀ᵏ - (-a) / X₁ᵏ`
  refine ⟨const hl b _ hb (SetLike.pow_mem_graded k (coord_mem R 0)) _ (hle 0),
    const hl (-a) _ (neg_mem ha) (SetLike.pow_mem_graded k (coord_mem R 1)) _ (hle 1), ?_⟩
  rw [res_const, res_const, const_sub_const]
  exact const_ext (by ring)

/-- **The twisting sheaves `𝒪(n)`, `n ≥ -1`, on the projective line have no first cohomology**,
over any commutative ring `R`: `H¹(ℙ¹_R, 𝒪(n)) = 0`. -/
theorem subsingleton_cohomology_one_twistingSheaf {n : ℤ} (hn : -1 ≤ n) :
    Subsingleton (Cohomology (Proj.twistingSheaf 𝒜 n) 1) := by
  have hacyclic (i : Fin 2) :
      Subsingleton (cohomologyOn (Proj.twistingSheaf 𝒜 n) 1 (Proj.basicOpen 𝒜 (coord R i))) :=
    subsingleton_cohomologyOn_succ_of_isAffineOpen _
      (Proj.isAffineOpen_basicOpen 𝒜 _ (coord_mem R i) one_pos) 0
  -- `H¹` is the quotient of the sections over the overlap by the differences of restrictions
  have : Subsingleton (Γ(Proj.twistingSheaf 𝒜 n,
      Proj.basicOpen 𝒜 (coord R 0) ⊓ Proj.basicOpen 𝒜 (coord R 1)) ⧸
        (mayerVietorisSectionsDifference (Proj.twistingSheaf 𝒜 n) _ _).range) := by
    rw [range_mayerVietorisSectionsDifference_twistingSheaf_eq_top R hn]
    exact QuotientAddGroup.subsingleton_quotient_top
  exact (sectionsQuotientEquivCohomologyOne _ _ _ (basicOpen_coord_sup_eq_top R) (hacyclic 0)
    (hacyclic 1)).symm.toEquiv.subsingleton

end TauCeti.AlgebraicGeometry.projectiveLine
