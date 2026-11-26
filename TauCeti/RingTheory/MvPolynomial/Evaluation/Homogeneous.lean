/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.SetTheory.Cardinal.Basic
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.LocalRing.Module

/-!
# Values of homogeneous polynomials and spans of monomial values

Over an integral domain `R`, a homogeneous polynomial of degree `n ≤ #R` vanishing at every point
is zero (`MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card`). The bound is
sharp: `X ^ 2 * Y + X * Y ^ 2` vanishes on `𝔽₂ ^ 2`. Consequently, if `g` is homogeneous of
degree `e` with `g ≠ 0` and `n + e ≤ #R`, a homogeneous polynomial of degree `n`
vanishing at every point where `g` does not vanish is zero: apply it to the product.

Dually, the vectors `(y ^ γ)_γ` of values of the monomials `γ` of degree `n`, at the points `y`
where `g` is a unit, span the space of all families indexed by these monomials. Over a local ring
`W` whose residue field has at least `n + e` elements this holds by reduction to the residue field
(Nakayama), and it is preserved by any ring homomorphism `W →+* O`.

## Main results

* `MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_eval_ne_zero`: a homogeneous
  polynomial of degree `n` vanishing wherever a nonzero homogeneous `g` of degree `e` does not
  vanish is zero, if `n + e ≤ #R`.
* `MvPolynomial.IsHomogeneous.span_range_prod_pow_eq_top`: over a local ring `W` whose residue
  field has at least `n + e` elements and for a ring homomorphism `ι : W →+* O`, the vectors
  `(ι (y ^ γ))_γ`, `γ` of degree `n`, at the points `y` where `g` is a unit, span `O ^ Mon_n`.

Spanning statements of this kind are how the points of a
general linear group over a field span its Schur algebra in degrees below the size of the field.

## References

* J. A. Green, *Polynomial Representations of GLₙ*, Lecture Notes in Mathematics 830 (1980).
* D. Benson and S. Doty, *Schur–Weyl duality over finite fields*, Arch. Math. 93 (2009).
* For `MvPolynomial.IsHomogeneous.span_range_prod_pow_eq_top`, see
  `New.Average.eq_top_of_eval_monomial` in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
  Here the residue field need only have at least `n + e` elements (a cardinal bound) and `O` is
  any semiring.
-/

public section

open IsLocalRing

namespace MvPolynomial.IsHomogeneous

variable {σ R : Type*} [CommRing R] [IsDomain R]

/-- **A homogeneous polynomial vanishing off the zero set of another is zero.** Over an integral
domain `R`, let `g ≠ 0` be homogeneous of degree `e`, and `h` homogeneous of degree `n` with
`n + e ≤ #R`. If `h` vanishes at every point where `g` does not vanish, then `h = 0`. This is
`IsHomogeneous.eq_zero_of_forall_eval_eq_zero_of_le_card` applied to `h * g`. -/
theorem eq_zero_of_forall_eval_eq_zero_of_eval_ne_zero {h g : MvPolynomial σ R} {n e : ℕ}
    (hh : h.IsHomogeneous n) (hg : g.IsHomogeneous e)
    (hcard : ((n + e : ℕ) : Cardinal) ≤ Cardinal.mk R) (hg0 : g ≠ 0)
    (hvan : ∀ y, eval y g ≠ 0 → eval y h = 0) : h = 0 := by
  have hhg : h * g = 0 := (hh.mul hg).eq_zero_of_forall_eval_eq_zero_of_le_card (fun y ↦ by
    by_cases hy : eval y g = 0
    · simp [hy]
    · simp [hvan y hy]) hcard
  exact (mul_eq_zero.1 hhg).resolve_right hg0

variable [Fintype σ]

/-- The field case: the vectors of monomial values at the points where `g` does not vanish span.
A linear form killing them is the polynomial `∑ γ, c γ • X ^ γ`, which vanishes wherever `g` does
not. -/
private theorem span_range_prod_pow_eq_top_of_field {K : Type*} [Field K] {n e : ℕ}
    {g : MvPolynomial σ K} (hg : g.IsHomogeneous e)
    (hcard : ((n + e : ℕ) : Cardinal) ≤ Cardinal.mk K) (hg0 : g ≠ 0) :
    Submodule.span K (Set.range fun y : {y : σ → K // eval y g ≠ 0} ↦
      fun γ : {γ : σ →₀ ℕ // γ.degree = n} ↦ ∏ i, y.val i ^ (γ : σ →₀ ℕ) i) = ⊤ := by
  classical
  have := Fintype.ofFinite {γ : σ →₀ ℕ // γ.degree = n}
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  -- The coefficients of `φ` in the coordinate basis.
  let c (γ : {γ : σ →₀ ℕ // γ.degree = n}) : K := φ fun δ ↦ if γ = δ then 1 else 0
  let h : MvPolynomial σ K := ∑ γ, monomial γ.val (c γ)
  have hh : h.IsHomogeneous n :=
    IsHomogeneous.sum _ _ _ fun γ _ ↦ isHomogeneous_monomial _ γ.property
  have heval (y : σ → K) : eval y h = φ fun γ ↦ ∏ i, y i ^ (γ : σ →₀ ℕ) i := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [h, c, eval_monomial, Finsupp.prod_fintype, mul_comm]
  have h0 : h = 0 := hh.eq_zero_of_forall_eval_eq_zero_of_eval_ne_zero hg hcard hg0 fun y hy ↦ by
    rw [heval]
    exact hle (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
  have hc (γ : {γ : σ →₀ ℕ // γ.degree = n}) :
      φ (fun δ ↦ if γ = δ then 1 else 0) = 0 := by
    simpa [h, c, coeff_sum, coeff_monomial, Subtype.coe_inj] using
      congrArg (fun q : MvPolynomial σ K ↦ q.coeff γ.val) h0
  exact hφ (LinearMap.ext fun x ↦ by simp [LinearMap.pi_apply_eq_sum_univ φ x, hc])

/-- The local case over `W` itself, by reduction to the residue field. -/
private theorem span_range_prod_pow_eq_top_of_isLocalRing {W : Type*} [CommRing W]
    [IsLocalRing W] {n e : ℕ} {g : MvPolynomial σ W} (hg : g.IsHomogeneous e)
    (hcard : ((n + e : ℕ) : Cardinal) ≤ Cardinal.mk (ResidueField W))
    (hg₀ : ∃ y, IsUnit (eval y g)) :
    Submodule.span W (Set.range fun y : {y : σ → W // IsUnit (eval y g)} ↦
      fun γ : {γ : σ →₀ ℕ // γ.degree = n} ↦ ∏ i, y.val i ^ (γ : σ →₀ ℕ) i) = ⊤ := by
  refine TauCeti.IsLocalRing.span_eq_top_iff_span_image_residue_eq_top.2 (eq_top_iff.2 ?_)
  obtain ⟨y₀, hy₀⟩ := hg₀
  have hres (y : σ → W) : residue W (eval y g) = eval (residue W ∘ y) (map (residue W) g) := by
    rw [eval_map, eval₂_comp]
  have hgbar : map (residue W) g ≠ 0 := fun h0 ↦
    (residue_ne_zero_iff_isUnit _).2 hy₀ (by rw [hres, h0, map_zero])
  rw [← span_range_prod_pow_eq_top_of_field (hg.map _) hcard hgbar]
  refine Submodule.span_mono ?_
  -- A point of the residue field where `g` does not vanish lifts to a point where `g` is a unit.
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨y, rfl⟩ := residue_surjective.comp_left z
  refine ⟨_, ⟨⟨y, (residue_ne_zero_iff_isUnit _).1 (by rwa [hres])⟩, rfl⟩, ?_⟩
  ext γ
  simp

/-- **Monomial values at the points where a homogeneous polynomial is a unit span.** Let `W` be a
local ring whose residue field has at least `n + e` elements, `ι : W →+* O` a ring homomorphism to
any semiring, and `g` a homogeneous polynomial of degree `e` over `W` in finitely many variables
with a unit value at some point. Then the vectors `(ι (y ^ γ))_γ`, `γ` running over the exponents
of degree `n`, at the points `y` where `g y` is a unit, span `O ^ {γ // γ.degree = n}` as a left
`O`-module.
For a finite residue field the bound reads `n + e ≤ Nat.card (ResidueField W)` (`Nat.cast_card`). -/
theorem span_range_prod_pow_eq_top {W O : Type*} [CommRing W] [IsLocalRing W] [Semiring O]
    {n e : ℕ} {g : MvPolynomial σ W} (hg : g.IsHomogeneous e) (ι : W →+* O)
    (hcard : ((n + e : ℕ) : Cardinal) ≤ Cardinal.mk (ResidueField W))
    (hg₀ : ∃ y, IsUnit (eval y g)) :
    Submodule.span O (Set.range fun y : {y : σ → W // IsUnit (eval y g)} ↦
      fun γ : {γ : σ →₀ ℕ // γ.degree = n} ↦ ι (∏ i, y.val i ^ (γ : σ →₀ ℕ) i)) = ⊤ := by
  classical
  have := Fintype.ofFinite {γ : σ →₀ ℕ // γ.degree = n}
  -- Apply `ι` coordinatewise, a `ι`-semilinear map, to the spanning family over `W`.
  let F : ({γ : σ →₀ ℕ // γ.degree = n} → W) →ₛₗ[ι] ({γ : σ →₀ ℕ // γ.degree = n} → O) :=
    { toFun := (ι ∘ ·)
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  have hW := span_range_prod_pow_eq_top_of_isLocalRing (n := n) hg hcard hg₀
  have hF : (Set.range fun y : {y : σ → W // IsUnit (eval y g)} ↦
      fun γ : {γ : σ →₀ ℕ // γ.degree = n} ↦ ι (∏ i, y.val i ^ (γ : σ →₀ ℕ) i)) =
      F '' Set.range fun y : {y : σ → W // IsUnit (eval y g)} ↦
        fun γ : {γ : σ →₀ ℕ // γ.degree = n} ↦ ∏ i, y.val i ^ (γ : σ →₀ ℕ) i := by
    rw [← Set.range_comp]
    ext x
    simp [F, Function.comp_def]
  rw [hF, eq_top_iff]
  rintro u -
  rw [← Finset.univ_sum_single u]
  refine Submodule.sum_mem _ fun γ _ ↦ ?_
  have hγ : Pi.single γ (u γ) = u γ • F (Pi.single γ 1) := by
    ext δ
    by_cases h : δ = γ <;> simp [F, h]
  rw [hγ]
  exact Submodule.smul_mem _ _ (Submodule.image_span_subset_span F _
    ⟨_, hW ▸ Submodule.mem_top, rfl⟩)

end MvPolynomial.IsHomogeneous
