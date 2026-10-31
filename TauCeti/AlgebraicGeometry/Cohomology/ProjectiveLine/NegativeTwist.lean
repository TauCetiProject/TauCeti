/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# First cohomology of the negative twisting sheaves on the projective line

Let `ℙ¹_R = Proj R[X₀, X₁]` be the projective line over a commutative ring `R`
(`TauCeti.AlgebraicGeometry.projectiveLine`) and `𝒪(n)` its twisting sheaves
(`AlgebraicGeometry.Proj.twistingSheaf`). This file computes `H¹(ℙ¹_R, 𝒪(n))` for `n ≤ -2`, over
any ring: writing `n = -(m + 2)`, it is isomorphic to the module `A_m` of forms of degree `m`, so it
is free of rank `-n - 1`. This is the nonvanishing half of Hartshorne, Theorem III.5.1(b), on the
projective line.

The twisting sheaves are quasi-coherent, so they have no higher cohomology on the affine charts
`D₊(X₀)` and `D₊(X₁)`, and the Mayer–Vietoris boundary identifies `H¹(ℙ¹_R, 𝒪(n))` with the sections
over the overlap `D₊(X₀X₁)` modulo the differences of restrictions of sections over the two charts
(`TauCeti.AlgebraicGeometry.mayerVietorisBoundaryLinear`,
`TauCeti.AlgebraicGeometry.ker_mayerVietorisBoundaryLinear`). Send a form `c` of degree `m` to the
class of the section `c / (X₀X₁)ᵐ⁺¹` over the overlap.

* *Surjectivity.* A section over the overlap is a fraction `r / (X₀X₁)ᵏ` with `r` of degree
  `2k - m - 2`; after multiplying numerator and denominator by `(X₀X₁)ᵐ⁺²` we may assume that
  `r` has degree `k + l` with `k = l + m + 2`. Every monomial `X₀ᵅ X₁ᵝ` of that degree has
  `α ≥ k`, or `β ≥ k`, or else both `α, β ≥ l + 1`. Hence `r = X₀ᵏ a + X₁ᵏ b + (X₀X₁)ˡ⁺¹ c` with
  `c` of degree `m`, and `r / (X₀X₁)ᵏ = a / X₁ᵏ + b / X₀ᵏ + c / (X₀X₁)ᵐ⁺¹`.
* *Injectivity.* If `c / (X₀X₁)ᵐ⁺¹ = a / X₀ᵏ - b / X₁ᵏ'` on the overlap, then
  `X₀ᵏ X₁ᵏ' c = (X₀X₁)ᵐ⁺¹ (X₁ᵏ' a - X₀ᵏ b)`, since the coordinates are nonzerodivisors. Setting
  `X₀ = 1` and `X₁ = X`, the coefficients of `X^{k' + i}`, `i ≤ m`, on the right vanish, by
  comparing degrees, so the dehomogenization of `c` vanishes, and so does `c`.

## Main results

All in the namespace `TauCeti.AlgebraicGeometry.projectiveLine`:

* `cohomologyOneTwistingSheafLinearEquiv`: `H¹(ℙ¹_R, 𝒪(-(m + 2))) ≃ₗ[R] A_m`, whose inverse
  sends `c` to the class of `c / (X₀X₁)ᵐ⁺¹`
  (`cohomologyOneTwistingSheafLinearEquiv_symm_apply`).
* `free_cohomology_one_twistingSheaf` and `finrank_cohomology_one_twistingSheaf`: for `n ≤ -2`,
  `H¹(ℙ¹_R, 𝒪(n))` is a free `R`-module of rank `-n - 1`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem III.5.1.
* [Stacks, Lemma 30.8.1 (01XS)](https://stacks.math.columbia.edu/tag/01XS)
-/

public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-! ### The comparison map -/

/-- The section `c / (X₀X₁)ᵐ⁺¹` of `𝒪(-(m + 2))` over the overlap of the standard charts. -/
private noncomputable def overlapSection (m : ℕ) (c : 𝒜 m) :
    Γ(Proj.twistingSheaf 𝒜 (-((m : ℤ) + 2)),
      Proj.basicOpen 𝒜 (coord R 0) ⊓ Proj.basicOpen 𝒜 (coord R 1)) :=
  Proj.twistingSheaf.const (i := (m + 1) * 2) (j := m) (by push_cast; ring) c.1
    ((coord R 0 * coord R 1) ^ (m + 1)) c.2 (coord_mul_coord_pow_mem R (m + 1)) _
    (inf_le_basicOpen_coord_mul_coord_pow R m.succ_pos)

private theorem smul_overlapSection (m : ℕ) (r : R) (c : 𝒜 m) :
    baseRingToGlobalSections R (projectiveLine R) r • overlapSection R m c =
      overlapSection R m (r • c) := by
  rw [sectionsGlobal_smul]
  refine Proj.twistingSheaf.ext fun x ↦ (Proj.twistingSheaf.smul_apply _ _ x).trans ?_
  refine (congrArg (· * _) (val_map_baseRingToGlobalSections R r _ x)).trans ?_
  -- both sections are the fractions `c / (X₀X₁)ᵐ⁺¹` and `(r • c) / (X₀X₁)ᵐ⁺¹` at `x`
  exact (Algebra.smul_def r _).symm.trans (Localization.smul_mk r c.1 _)

private theorem subsingleton_cohomologyOn_basicOpen_coord (n : ℤ) (i : Fin 2) :
    Subsingleton (cohomologyOn (Proj.twistingSheaf 𝒜 n) 1 (Proj.basicOpen 𝒜 (coord R i))) :=
  subsingleton_cohomologyOn_succ_of_isAffineOpen _
    (Proj.isAffineOpen_basicOpen 𝒜 _ (coord_mem R i) one_pos) 0

/-- The map `A_m → H¹(ℙ¹_R, 𝒪(-(m + 2)))` sending `c` to the class of `c / (X₀X₁)ᵐ⁺¹`. -/
private noncomputable def toCohomologyOne (m : ℕ) :
    𝒜 m →ₗ[R] Cohomology (Proj.twistingSheaf 𝒜 (-((m : ℤ) + 2))) 1 where
  toFun c := mayerVietorisBoundaryLinear _ _ _ (basicOpen_coord_sup_eq_top R)
    (overlapSection R m c)
  map_add' _ _ :=
    (congrArg _ (Proj.twistingSheaf.const_add ..).symm).trans (map_add _ _ _)
  map_smul' r c :=
    (congrArg _ (smul_overlapSection R m r c).symm).trans (LinearMap.map_smul _ _ _)

/-- Every section of `𝒪(-(m + 2))` over the overlap of the standard charts is `c / (X₀X₁)ᵐ⁺¹`
up to a difference of restrictions of sections over the two charts. -/
private theorem exists_sub_overlapSection_mem_range (m : ℕ)
    (s : Γ(Proj.twistingSheaf 𝒜 (-((m : ℤ) + 2)),
      Proj.basicOpen 𝒜 (coord R 0) ⊓ Proj.basicOpen 𝒜 (coord R 1))) :
    ∃ c, s - overlapSection R m c ∈ LinearMap.range (mayerVietorisSectionsDifferenceLinear
      (Proj.twistingSheaf 𝒜 (-((m : ℤ) + 2))) (Proj.basicOpen 𝒜 (coord R 0))
        (Proj.basicOpen 𝒜 (coord R 1))) := by
  -- the overlap is `D₊(X₀X₁)`, on which `s` is a fraction `r / (X₀X₁)ᵏ`
  suffices h : ∀ (W : (projectiveLine R).Opens)
      (_ : Proj.basicOpen 𝒜 (coord R 0 * coord R 1) = W)
      (h₀ : W ≤ Proj.basicOpen 𝒜 (coord R 0)) (h₁ : W ≤ Proj.basicOpen 𝒜 (coord R 1))
      (hW : W ≤ Proj.basicOpen 𝒜 ((coord R 0 * coord R 1) ^ (m + 1)))
      (s : Γ(Proj.twistingSheaf 𝒜 (-((m : ℤ) + 2)), W)), ∃ (c : 𝒜 m) (t₀ t₁ : _),
        s - Proj.twistingSheaf.const (i := (m + 1) * 2) (j := m) (by push_cast; ring) c.1
            ((coord R 0 * coord R 1) ^ (m + 1)) c.2 (coord_mul_coord_pow_mem R (m + 1)) W hW =
          (Proj.twistingSheaf 𝒜 _).presheaf.map (homOfLE h₀).op t₀ -
            (Proj.twistingSheaf 𝒜 _).presheaf.map (homOfLE h₁).op t₁ by
    obtain ⟨c, t₀, t₁, ht⟩ := h _ (Proj.basicOpen_mul _ _ _) inf_le_left inf_le_right
      (inf_le_basicOpen_coord_mul_coord_pow R m.succ_pos) s
    refine ⟨c, (t₀, t₁), ?_⟩
    rw [mayerVietorisSectionsDifferenceLinear_apply, mayerVietorisSectionsDifference_apply]
    exact ht.symm
  rintro W rfl h₀ h₁ hW s
  obtain ⟨k, j, h, r, hr, rfl⟩ := Proj.twistingSheaf.exists_eq_const_basicOpen
    (SetLike.mul_mem_graded (coord_mem R 0) (coord_mem R 1)) two_pos s
  -- `(X₀X₁)ᵐ⁺² r = X₀ᵏ⁺ᵐ⁺² a + X₁ᵏ⁺ᵐ⁺² b + (X₀X₁)ᵏ⁺¹ c` with `a`, `b` of degree `k`
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := exists_eq_coord_pow_mul_add_coord_pow_mul_add R
    (m := m) (k := k + m + 2) (l := k) rfl
    (r := (coord R 0 * coord R 1) ^ (m + 2) * r)
    (by convert SetLike.mul_mem_graded (coord_mul_coord_pow_mem R (m + 2)) hr using 2; omega)
  have hle (i : Fin 2) (e : ℕ) : Proj.basicOpen 𝒜 (coord R i) ≤
      Proj.basicOpen 𝒜 (coord R i ^ e) :=
    fun x hx hxe ↦ hx (x.isPrime.mem_of_pow_mem e hxe)
  have hdeg : (k : ℤ) = ((k + m + 2) * 1 : ℕ) + -((m : ℤ) + 2) := by push_cast; ring
  -- so `r / (X₀X₁)ᵏ - c / (X₀X₁)ᵐ⁺¹ = b / X₀ᵏ⁺ᵐ⁺² - (-a) / X₁ᵏ⁺ᵐ⁺²`
  refine ⟨⟨c, hc⟩,
    Proj.twistingSheaf.const hdeg b _ hb (SetLike.pow_mem_graded _ (coord_mem R 0)) _ (hle 0 _),
    Proj.twistingSheaf.const hdeg (-a) _ (neg_mem ha) (SetLike.pow_mem_graded _ (coord_mem R 1))
      _ (hle 1 _), ?_⟩
  rw [Proj.twistingSheaf.res_const, Proj.twistingSheaf.res_const,
    Proj.twistingSheaf.const_sub_const]
  refine (Proj.twistingSheaf.const_sub_const ..).trans (Proj.twistingSheaf.const_ext ?_)
  linear_combination (coord R 0 * coord R 1) ^ (k + m + 1) * habc

/-- The section `c / (X₀X₁)ᵐ⁺¹` is a difference of restrictions of sections over the two
standard charts only for `c = 0`. -/
private theorem eq_zero_of_overlapSection_mem_range (m : ℕ) {c : 𝒜 m}
    (hc : overlapSection R m c ∈ LinearMap.range (mayerVietorisSectionsDifferenceLinear
      (Proj.twistingSheaf 𝒜 (-((m : ℤ) + 2))) (Proj.basicOpen 𝒜 (coord R 0))
        (Proj.basicOpen 𝒜 (coord R 1)))) : c = 0 := by
  obtain ⟨⟨t₀, t₁⟩, ht⟩ := LinearMap.mem_range.mp hc
  rw [mayerVietorisSectionsDifferenceLinear_apply, mayerVietorisSectionsDifference_apply] at ht
  -- write `t₀ = a / X₀ᵏ` and `t₁ = b / X₁ᵏ'`
  obtain ⟨k, j, h, a, ha, rfl⟩ :=
    Proj.twistingSheaf.exists_eq_const_basicOpen (coord_mem R 0) one_pos t₀
  obtain ⟨k', j', h', b, hb, rfl⟩ :=
    Proj.twistingSheaf.exists_eq_const_basicOpen (coord_mem R 1) one_pos t₁
  -- on `D₊(X₀X₁)`, the fractions `(X₁ᵏ' a - X₀ᵏ b) / (X₀ᵏ X₁ᵏ')` and `c / (X₀X₁)ᵐ⁺¹` agree
  have hW : Proj.basicOpen 𝒜 (coord R 0 * coord R 1) ≤
      Proj.basicOpen 𝒜 (coord R 0) ⊓ Proj.basicOpen 𝒜 (coord R 1) :=
    (Proj.basicOpen_mul _ _ _).le
  obtain ⟨N, hN⟩ := (Proj.twistingSheaf.const_eq_const_iff (n := -((m : ℤ) + 2))
    (i := k * 1 + k' * 1) (j := k' * 1 + j) (i' := (m + 1) * 2) (j' := m)
    (r := coord R 1 ^ k' * a - coord R 0 ^ k * b) (s := coord R 0 ^ k * coord R 1 ^ k')
    (r' := c.1) (s' := (coord R 0 * coord R 1) ^ (m + 1))
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 two_pos
      (SetLike.mul_mem_graded (coord_mem R 0) (coord_mem R 1))) (by push_cast at h ⊢; omega)
    (by push_cast; ring)
    (sub_mem (SetLike.mul_mem_graded (SetLike.pow_mem_graded _ (coord_mem R 1)) ha)
      (by convert SetLike.mul_mem_graded (SetLike.pow_mem_graded k (coord_mem R 0)) hb using 2
          simp only [smul_eq_mul]; push_cast at h h'; omega))
    (SetLike.mul_mem_graded (SetLike.pow_mem_graded _ (coord_mem R 0))
      (SetLike.pow_mem_graded _ (coord_mem R 1)))
    c.2 (coord_mul_coord_pow_mem R (m + 1))
    (hW.trans fun x hx hxs ↦ (x.isPrime.mem_or_mem hxs).elim
      (fun h₀ ↦ hx.1 (x.isPrime.mem_of_pow_mem _ h₀))
      (fun h₁ ↦ hx.2 (x.isPrime.mem_of_pow_mem _ h₁)))
    (hW.trans (inf_le_basicOpen_coord_mul_coord_pow R m.succ_pos))).mp
    (Proj.twistingSheaf.ext fun x ↦ by
      -- both sides are the values at `x` of the fractions, by `const_apply`
      exact (Localization.sub_mk ..).symm.trans (congrArg (fun t ↦ t.1 ⟨x.1, hW x.2⟩) ht))
  -- the coordinates are nonzerodivisors, so `X₀ᵏ X₁ᵏ' c = (X₀X₁)ᵐ⁺¹ (X₁ᵏ' a - X₀ᵏ b)`
  have hE := (pow_mem (mul_mem (coord_mem_nonZeroDivisors R 0)
    (coord_mem_nonZeroDivisors R 1)) N).2 _ (by rw [mul_comm]; exact hN)
  exact Subtype.ext (eq_zero_of_coord_pow_mul_eq R (k := k) (k' := k') (a := a)
    (by push_cast at h'; omega) hb c.2 (by linear_combination -hE))

/-! ### First cohomology of `𝒪(n)` for `n ≤ -2` -/

/-- **The first cohomology of `𝒪(-(m + 2))` on the projective line is the module of forms of
degree `m`**, over any commutative ring `R`: `H¹(ℙ¹_R, 𝒪(-(m + 2))) ≃ₗ[R] A_m`. The inverse sends a
form `c` of degree `m` to the class of the section `c / (X₀X₁)ᵐ⁺¹` over the overlap of the
standard charts (`cohomologyOneTwistingSheafLinearEquiv_symm_apply`). -/
noncomputable def cohomologyOneTwistingSheafLinearEquiv (m : ℕ) :
    Cohomology (Proj.twistingSheaf 𝒜 (-((m : ℤ) + 2))) 1 ≃ₗ[R] 𝒜 m := by
  refine (LinearEquiv.ofBijective (toCohomologyOne R m) ⟨?_, fun y ↦ ?_⟩).symm
  · refine (injective_iff_map_eq_zero _).mpr fun c hc ↦
      eq_zero_of_overlapSection_mem_range R m ?_
    rw [← ker_mayerVietorisBoundaryLinear _ _ _ (basicOpen_coord_sup_eq_top R)]
    exact hc
  · obtain ⟨s, rfl⟩ := mayerVietorisBoundaryLinear_surjective _ _ _ (basicOpen_coord_sup_eq_top R)
      (subsingleton_cohomologyOn_basicOpen_coord R _ 0)
      (subsingleton_cohomologyOn_basicOpen_coord R _ 1) y
    obtain ⟨c, hc⟩ := exists_sub_overlapSection_mem_range R m s
    refine ⟨c, (sub_eq_zero.mp ?_).symm⟩
    rw [← ker_mayerVietorisBoundaryLinear _ _ _ (basicOpen_coord_sup_eq_top R)] at hc
    exact (map_sub _ _ _).symm.trans hc

/-- The inverse of `cohomologyOneTwistingSheafLinearEquiv` sends a form `c` of degree `m` to the
Mayer–Vietoris boundary of the section `c / (X₀X₁)ᵐ⁺¹` over the overlap of the standard charts. -/
theorem cohomologyOneTwistingSheafLinearEquiv_symm_apply (m : ℕ) (c : 𝒜 m) :
    (cohomologyOneTwistingSheafLinearEquiv R m).symm c =
      mayerVietorisBoundaryLinear _ _ _ (basicOpen_coord_sup_eq_top R)
        (Proj.twistingSheaf.const (i := (m + 1) * 2) (j := m) (by push_cast; ring) c.1
          ((coord R 0 * coord R 1) ^ (m + 1)) c.2 (coord_mul_coord_pow_mem R (m + 1)) _
          (inf_le_basicOpen_coord_mul_coord_pow R m.succ_pos)) :=
  (rfl)

/-- **For `n ≤ -2`, the first cohomology of `𝒪(n)` on the projective line is a free module**,
over any commutative ring `R`. -/
theorem free_cohomology_one_twistingSheaf {n : ℤ} (hn : n ≤ -2) :
    Module.Free R (Cohomology (Proj.twistingSheaf 𝒜 n) 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m : ℤ) + 2) := ⟨(-n - 2).toNat, by omega⟩
  exact .of_equiv (cohomologyOneTwistingSheafLinearEquiv R m).symm

/-- **For `n ≤ -2`, the first cohomology of `𝒪(n)` on the projective line has rank `-n - 1`**,
over any nontrivial commutative ring `R`. -/
theorem finrank_cohomology_one_twistingSheaf [Nontrivial R] {n : ℤ} (hn : n ≤ -2) :
    (Module.finrank R (Cohomology (Proj.twistingSheaf 𝒜 n) 1) : ℤ) = -n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m : ℤ) + 2) := ⟨(-n - 2).toNat, by omega⟩
  rw [(cohomologyOneTwistingSheafLinearEquiv R m).finrank_eq,
    (SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial R _ (Pi.basisFun R (Fin 2))
      m).finrank_eq, finrank_homogeneousSubmodule_fin_two]
  push_cast
  ring

end TauCeti.AlgebraicGeometry.projectiveLine
