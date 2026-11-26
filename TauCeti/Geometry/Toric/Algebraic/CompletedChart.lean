/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Geometry.Toric.Algebraic.Boundary
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# Completions of regular toric charts along the boundary

Let `A_R = R[(ι →₀ ℕ) × Q]` be the coordinate ring of a regular toric chart, so that for
`Q = κ →₀ ℤ` it is `R[x_1, …, x_r, y_1^{±1}, …, y_s^{±1}]`, and let `t = x_1 ⋯ x_r` be the boundary
monomial, which cuts out the union of the boundary divisors. This file describes the `t`-adic
completion `Â_R = lim_h A_R ⧸ (t)^h` by its coefficients, over an arbitrary commutative ring `R`
(possibly zero or nonreduced), when there is at least one ray (`r > 0`).

For each `h`, the quotient `A_R ⧸ (t)^h` has the monomial basis of the exponents `(a, b)` with some
`a_i < h` (`TauCeti.Toric.boundaryPowQuotientBasis`). Every exponent `(a, b)` has `a_i < h` once
`h > a_i` for one `i`, and the transition maps keep these coordinates, so every element `x` of the
completion has a well-defined coefficient family `c_{a,b}(x)`
(`TauCeti.Toric.completedChartCoeff`). The coefficients of `x` at the exponents with some `a_i < h`
are those of any representative of the image of `x` in `A_R ⧸ (t)^h`
(`TauCeti.Toric.completedChartCoeff_eq_coeff`), so for each `h` only finitely many of them are
nonzero.

* `TauCeti.Toric.completedChartCoeffEquiv`: the completion is `R`-linearly isomorphic to the
  families `c : (ι →₀ ℕ) × Q → R` such that, for each `h`, only finitely many nonzero `c_{a,b}`
  have some `a_i < h`, that is, have `a` outside the diagonal tail `(h, …, h) + ℕ^r`
  (`TauCeti.Toric.completedChartFamilies`).
* `TauCeti.Toric.completedChartCoeff_mul`: multiplication in the completion is the convolution of
  coefficient families: the coefficient of a product at `(a, b)` is the `finsum`, over the
  decompositions `(a, b) = p₁ + p₂`, of the products of the coefficients.
* `TauCeti.Toric.completedChartCoeff_of` and `TauCeti.Toric.completedChartCoeff_one`: an element
  of `A_R`, in particular `1`, keeps its coefficients in the completion.

The admissibility condition is finiteness outside every diagonal tail; it is not the condition
defining the full power series ring. For `r = 1` and no torus directions every family is admitted,
as for `R⟦x⟧`; for `r = 2` the family of `∑ x_1^n x_2^n` is admitted while
the family of `∑ x_1^n` is not, since it is infinite modulo `x_1 x_2`. For `r = 0` the boundary
monomial is `1`, the completion is zero, and no coefficient description holds; this is why a ray
is required.

These completed regular charts are the formal neighbourhoods of the boundary of toroidal
compactifications on which Fourier–Jacobi and `q`-expansions live.

## References

* M. Dimitrov, *Compactifications arithmétiques des variétés de Hilbert et formes modulaires de
  Hilbert pour Γ₁(c, n)*, in *Geometric Aspects of Dwork Theory*, de Gruyter, 2004, §2.
* K.-W. Lan, *Arithmetic Compactifications of PEL-Type Shimura Varieties*, London Mathematical
  Society Monographs 36, Princeton University Press, 2013, §6.2.
-/

public section

namespace TauCeti.Toric

open AddMonoidAlgebra AdicCompletion

section Semiring

variable (R : Type*) [Semiring R] (ι : Type*) (Q : Type*)

/-- The coefficient families of the completion of a regular chart along its boundary: the
families `c : (ι →₀ ℕ) × Q → R` such that, for every `h`, only finitely many exponents `(a, b)`
with some `a_i < h` carry a nonzero coefficient. -/
def completedChartFamilies : Submodule R ((ι →₀ ℕ) × Q → R) where
  carrier := {c | ∀ h : ℕ, {p : (ι →₀ ℕ) × Q | (∃ i, p.1 i < h) ∧ c p ≠ 0}.Finite}
  zero_mem' h := by simp
  add_mem' {c d} hc hd h := ((hc h).union (hd h)).subset fun p ⟨hp, hcd⟩ ↦ by
    by_cases hcp : c p = 0
    · exact Or.inr ⟨hp, by simpa [hcp] using hcd⟩
    · exact Or.inl ⟨hp, hcp⟩
  smul_mem' r c hc h := (hc h).subset fun p ⟨hp, hrc⟩ ↦ ⟨hp, fun h0 ↦ hrc (by simp [h0])⟩

variable {R ι Q}

/-- A family lies in `TauCeti.Toric.completedChartFamilies` exactly when, for every `h`, only
finitely many exponents with some `a_i < h` carry a nonzero coefficient. -/
@[simp]
theorem mem_completedChartFamilies_iff {c : (ι →₀ ℕ) × Q → R} :
    c ∈ completedChartFamilies R ι Q ↔
      ∀ h : ℕ, {p : (ι →₀ ℕ) × Q | (∃ i, p.1 i < h) ∧ c p ≠ 0}.Finite := by
  rw [completedChartFamilies]
  rfl

open Classical in
/-- The finitely supported truncation of an admissible family to the exponents with some
`a_i < h`. -/
private noncomputable def truncation (c : completedChartFamilies R ι Q) (h : ℕ) :
    AddMonoidAlgebra R ((ι →₀ ℕ) × Q) :=
  ofCoeff <| Finsupp.ofSupportFinite (fun p ↦ if ∃ i, p.1 i < h then c.val p else 0) <|
    (mem_completedChartFamilies_iff.mp c.property h).subset fun p hp ↦ by
      by_cases hph : ∃ i, p.1 i < h
      · exact ⟨hph, by simpa [hph] using hp⟩
      · simp [hph] at hp

open Classical in
private theorem coeff_truncation (c : completedChartFamilies R ι Q) (h : ℕ)
    (p : (ι →₀ ℕ) × Q) :
    (truncation c h).coeff p = if ∃ i, p.1 i < h then c.val p else 0 := by
  simp [truncation, Finsupp.ofSupportFinite_coe]

end Semiring

variable {R ι Q : Type*} [CommRing R] [Fintype ι] [AddCommMonoid Q]

/-- The truncations of an admissible family form an adic Cauchy sequence. -/
private theorem isAdicCauchy_truncation (c : completedChartFamilies R ι Q) :
    IsAdicCauchy (Ideal.span {boundaryMonomial R ι Q}) (AddMonoidAlgebra R ((ι →₀ ℕ) × Q))
      (truncation c) := by
  intro m n hmn
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_boundaryMonomial_pow_iff]
  intro p i hp
  have hm : ∃ i, p.1 i < m := ⟨i, hp⟩
  have hn : ∃ i, p.1 i < n := ⟨i, hp.trans_le hmn⟩
  simp [coeff_truncation, hm, hn]

variable [Nonempty ι]

/-- The coefficient family of an element `x` of the completion of the regular chart
`R[(ι →₀ ℕ) × Q]` along the boundary monomial: the coefficient at `(a, b)` is the coordinate at
`(a, b)` of the image of `x` in `R[(ι →₀ ℕ) × Q] ⧸ (t)^h`, for any `h` exceeding some `a_i`
(`TauCeti.Toric.completedChartCoeff_apply`). -/
noncomputable def completedChartCoeff :
    AdicCompletion (Ideal.span {boundaryMonomial R ι Q}) (AddMonoidAlgebra R ((ι →₀ ℕ) × Q)) →ₗ[R]
      ((ι →₀ ℕ) × Q → R) :=
  LinearMap.pi fun p ↦
    Finsupp.lapply ⟨p, Classical.arbitrary ι, Nat.lt_succ_self _⟩ ∘ₗ
      (boundaryPowQuotientBasis (p.1 (Classical.arbitrary ι) + 1)).repr.toLinearMap ∘ₗ
        (evalₐ _ _).toLinearMap.restrictScalars R

/-- The coefficient of `x` at an exponent `p` with some `a_i < h` is the coordinate at `p` of the
image of `x` in `R[(ι →₀ ℕ) × Q] ⧸ (t)^h`. -/
theorem completedChartCoeff_apply (x : AdicCompletion (Ideal.span {boundaryMonomial R ι Q})
      (AddMonoidAlgebra R ((ι →₀ ℕ) × Q))) {h : ℕ} (p : {p : (ι →₀ ℕ) × Q // ∃ i, p.1 i < h}) :
    completedChartCoeff x p =
      (boundaryPowQuotientBasis h).repr (evalₐ (Ideal.span {boundaryMonomial R ι Q}) h x) p := by
  -- By definition, the coefficient is read off at the level `h₀ = a_{i₀} + 1`; compare both
  -- levels with their maximum through the transition maps.
  have h₀ : completedChartCoeff x p =
      (boundaryPowQuotientBasis (p.val.1 (Classical.arbitrary ι) + 1)).repr
        (evalₐ (Ideal.span {boundaryMonomial R ι Q}) (p.val.1 (Classical.arbitrary ι) + 1) x)
        ⟨p, Classical.arbitrary ι, Nat.lt_succ_self _⟩ := by
    simp [completedChartCoeff]
  have hle₀ := le_max_left (p.val.1 (Classical.arbitrary ι) + 1) h
  have hle := le_max_right (p.val.1 (Classical.arbitrary ι) + 1) h
  rw [h₀, ← factor_evalₐ hle₀, ← factor_evalₐ hle, boundaryPowQuotientBasis_repr_factor hle₀,
    boundaryPowQuotientBasis_repr_factor hle]

/-- The coefficient of `x` at an exponent `p` with `a_i < h` for some `i` is the coefficient at `p`
of any representative of the image of `x` in `R[(ι →₀ ℕ) × Q] ⧸ (t)^h`. -/
theorem completedChartCoeff_eq_coeff {x : AdicCompletion (Ideal.span {boundaryMonomial R ι Q})
      (AddMonoidAlgebra R ((ι →₀ ℕ) × Q))} {h : ℕ} {f : AddMonoidAlgebra R ((ι →₀ ℕ) × Q)}
    (hf : evalₐ (Ideal.span {boundaryMonomial R ι Q}) h x = Ideal.Quotient.mk _ f)
    {p : (ι →₀ ℕ) × Q} {i : ι} (hp : p.1 i < h) :
    completedChartCoeff x p = f.coeff p := by
  rw [completedChartCoeff_apply x ⟨p, i, hp⟩, hf, boundaryPowQuotientBasis_repr_mk]

/-- An element of the regular chart keeps its coefficients in the completion. -/
@[simp]
theorem completedChartCoeff_of (f : AddMonoidAlgebra R ((ι →₀ ℕ) × Q)) :
    completedChartCoeff (of _ _ f) = f.coeff := by
  ext p
  exact completedChartCoeff_eq_coeff (evalₐ_of _ _ f)
    (Nat.lt_succ_self (p.1 (Classical.arbitrary ι)))

/-- The unit of the completion has the coefficients of the unit of the regular chart. -/
@[simp]
theorem completedChartCoeff_one :
    completedChartCoeff (1 : AdicCompletion (Ideal.span {boundaryMonomial R ι Q})
      (AddMonoidAlgebra R ((ι →₀ ℕ) × Q))) = (1 : AddMonoidAlgebra R ((ι →₀ ℕ) × Q)).coeff := by
  ext p
  exact completedChartCoeff_eq_coeff (by rw [map_one, map_one])
    (Nat.lt_succ_self (p.1 (Classical.arbitrary ι)))

/-- For each `h`, only finitely many coefficients of an element of the completion at exponents
with some `a_i < h` are nonzero. -/
theorem completedChartCoeff_mem_completedChartFamilies
    (x : AdicCompletion (Ideal.span {boundaryMonomial R ι Q}) (AddMonoidAlgebra R ((ι →₀ ℕ) × Q))) :
    completedChartCoeff x ∈ completedChartFamilies R ι Q := by
  refine mem_completedChartFamilies_iff.mpr fun h ↦ ?_
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (evalₐ _ h x)
  refine f.coeff.support.finite_toSet.subset fun p ⟨⟨i, hp⟩, hx⟩ ↦ ?_
  rwa [completedChartCoeff_eq_coeff hf.symm hp, ← Finsupp.mem_support_iff] at hx

/-- An element of the completion is determined by its coefficients. -/
theorem completedChartCoeff_injective :
    Function.Injective (completedChartCoeff (R := R) (ι := ι) (Q := Q)) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ext_evalₐ fun h ↦ ?_
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (evalₐ _ h x)
  rw [← hf, map_zero, Ideal.Quotient.eq_zero_iff_mem, mem_span_boundaryMonomial_pow_iff]
  intro p i hp
  rw [← completedChartCoeff_eq_coeff hf.symm hp, hx, Pi.zero_apply]

/-- Every admissible family is the coefficient family of an element of the completion. -/
theorem exists_completedChartCoeff_eq {c : (ι →₀ ℕ) × Q → R}
    (hc : c ∈ completedChartFamilies R ι Q) :
    ∃ x, completedChartCoeff (R := R) (ι := ι) (Q := Q) x = c := by
  refine ⟨mk _ _ ⟨truncation ⟨c, hc⟩, isAdicCauchy_truncation ⟨c, hc⟩⟩, funext fun p ↦ ?_⟩
  have hp : p.1 (Classical.arbitrary ι) < p.1 (Classical.arbitrary ι) + 1 := Nat.lt_succ_self _
  rw [completedChartCoeff_eq_coeff
    (f := truncation ⟨c, hc⟩ (p.1 (Classical.arbitrary ι) + 1)) (evalₐ_mk _ _ _) hp,
    coeff_truncation, ite_eq_left ⟨_, hp⟩]

variable (R ι Q) in
/-- **Coefficients of a completed regular chart.** For at least one ray, the completion of the
regular chart `R[(ι →₀ ℕ) × Q]` along the boundary monomial `t = x_1 ⋯ x_r` is `R`-linearly
isomorphic, by taking coefficients, to the families `c : (ι →₀ ℕ) × Q → R` such that for every
`h` only finitely many exponents with some `a_i < h` carry a nonzero coefficient. Multiplication
corresponds to convolution (`TauCeti.Toric.completedChartCoeff_mul`). -/
noncomputable def completedChartCoeffEquiv :
    AdicCompletion (Ideal.span {boundaryMonomial R ι Q}) (AddMonoidAlgebra R ((ι →₀ ℕ) × Q)) ≃ₗ[R]
      completedChartFamilies R ι Q :=
  .ofBijective (completedChartCoeff.codRestrict _ completedChartCoeff_mem_completedChartFamilies)
    ⟨fun _ _ hxy ↦ completedChartCoeff_injective (congrArg Subtype.val hxy),
      fun c ↦ (exists_completedChartCoeff_eq c.property).imp fun _ hx ↦ Subtype.ext hx⟩

@[simp]
theorem coe_completedChartCoeffEquiv_apply (x : AdicCompletion
      (Ideal.span {boundaryMonomial R ι Q}) (AddMonoidAlgebra R ((ι →₀ ℕ) × Q))) :
    (completedChartCoeffEquiv R ι Q x : (ι →₀ ℕ) × Q → R) = completedChartCoeff x := by
  exact congrArg Subtype.val (LinearEquiv.ofBijective_apply _ x) |>.trans
    (LinearMap.codRestrict_apply _ _ x)

/-- The element of the completion with a given admissible coefficient family has that family as
its coefficients. -/
@[simp]
theorem completedChartCoeff_completedChartCoeffEquiv_symm (c : completedChartFamilies R ι Q) :
    completedChartCoeff ((completedChartCoeffEquiv R ι Q).symm c) = c := by
  rw [← coe_completedChartCoeffEquiv_apply, LinearEquiv.apply_symm_apply]

/-- **Multiplication in a completed regular chart is convolution.** The coefficient of a product
at `p` is the `finsum`, over the decompositions `p = p₁ + p₂`, of the products of the
coefficients. -/
theorem completedChartCoeff_mul (x y : AdicCompletion (Ideal.span {boundaryMonomial R ι Q})
      (AddMonoidAlgebra R ((ι →₀ ℕ) × Q))) (p : (ι →₀ ℕ) × Q) :
    completedChartCoeff (x * y) p =
      ∑ᶠ (q : ((ι →₀ ℕ) × Q) × ((ι →₀ ℕ) × Q)) (_ : q.1 + q.2 = p),
        completedChartCoeff x q.1 * completedChartCoeff y q.2 := by
  classical
  -- Work at a level `h` exceeding the first ray coordinate of `p`; every summand of a
  -- decomposition of `p` then has its coefficients computed by representatives at level `h`.
  set i₀ := Classical.arbitrary ι
  set h := p.1 i₀ + 1
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (evalₐ _ h x)
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (evalₐ _ h y)
  have hlt {q : ((ι →₀ ℕ) × Q) × ((ι →₀ ℕ) × Q)} (hq : q.1 + q.2 = p) :
      q.1.1 i₀ < h ∧ q.2.1 i₀ < h := by
    have := congrArg (fun r : (ι →₀ ℕ) × Q ↦ r.1 i₀) hq
    simp only [Prod.fst_add, Finsupp.add_apply] at this
    omega
  have hxy : evalₐ _ h (x * y) = Ideal.Quotient.mk _ (f * g) := by rw [map_mul, ← hf, ← hg, map_mul]
  have hfg : (f * g).coeff p = ∑ q ∈ f.coeff.support ×ˢ g.coeff.support with q.1 + q.2 = p,
      f.coeff q.1 * g.coeff q.2 := by
    rw [coeff_mul, Finset.sum_filter, Finset.sum_product]
    simp only [Finsupp.sum]
  rw [completedChartCoeff_eq_coeff hxy (Nat.lt_succ_self (p.1 i₀)), hfg,
    finsum_cond_eq_sum_of_cond_iff (fun q ↦ completedChartCoeff x q.1 * completedChartCoeff y q.2)
      (p := fun q ↦ q.1 + q.2 = p) (t := {q ∈ f.coeff.support ×ˢ g.coeff.support | q.1 + q.2 = p})]
  · refine Finset.sum_congr rfl fun q hq ↦ ?_
    have hqp := (Finset.mem_filter.mp hq).2
    rw [completedChartCoeff_eq_coeff hf.symm (hlt hqp).1,
      completedChartCoeff_eq_coeff hg.symm (hlt hqp).2]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finsupp.mem_support_iff]
    refine ⟨fun hqp ↦ ⟨⟨?_, ?_⟩, hqp⟩, fun hq' ↦ hq'.2⟩
    · rw [← completedChartCoeff_eq_coeff hf.symm (hlt hqp).1]
      exact left_ne_zero_of_mul hq
    · rw [← completedChartCoeff_eq_coeff hg.symm (hlt hqp).2]
      exact right_ne_zero_of_mul hq

end TauCeti.Toric
