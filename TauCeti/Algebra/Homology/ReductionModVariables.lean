/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.LinearAlgebra.Finsupp.LSum
public import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Graded complexes of free modules over a polynomial ring modulo the variables

Let `S = R[V_v : v ∈ σ]` be a polynomial ring and let `d` be a square-zero `S`-linear
endomorphism of the free module `ι →₀ S`. Setting every variable to zero, that is, applying
`MvPolynomial.constantCoeff` to every coordinate, turns `d` into an `R`-linear endomorphism `d₀`
of `ι →₀ R`, determined by `d₀ ∘ ρ = ρ ∘ d` for the reduction `ρ`. This file proves a graded
Nakayama lemma for such complexes: if each generator `i` carries an integer degree `g i`, the
degrees `g i` are bounded above, every variable `V_v` has negative degree `w v`, and `d` is
homogeneous of some degree `r`, then `d` is exact as soon as `d₀` is
(`LinearMap.ker_le_range_of_mapRange_constantCoeff`). Applied to mapping cones, a homogeneous
chain map `f` between two such complexes induces a bijection on homology as soon as its reduction
`f₀` does (`LinearMap.homologyMap_bijective_of_mapRange_constantCoeff`).

This is the algebraic input for deducing statements about the unblocked grid complexes `GC⁻`
over `𝔽₂[V₀, …, V_{n-1}]` from the fully blocked complexes, in which every variable is set to
zero: there the generators are the finitely many grid states, the variables lower the Maslov
grading by two, and the differentials lower it by one.

The proof filters a cycle `z` by the powers of the ideal `J = (V_v : v ∈ σ)`. If `z` lies in
`J ^ k • (ι →₀ S)`, its coefficients at the monomials `V ^ e` of total degree `k` form cycles of
`d₀`, since the higher terms of the matrix coefficients of `d` only contribute to monomials of
larger degree. Choosing primitives of these cycles under `d₀` corrects `z` by a boundary into
`J ^ (k + 1) • (ι →₀ S)`. The grading makes this process stop: the primitives can be chosen of
degree at least a fixed bound, while an element of `J ^ k • (ι →₀ S)` has degree at most
`max g - k`.

Without the grading the statement fails: on `S = R[V]`, multiplication by `1 + V` is a chain map
from `S` to itself, both with zero differential, which becomes the identity after setting `V = 0`
but is not surjective.

## Main definitions

* `LinearMap.constantCoeffReduction`: the reduction of a map between free modules over a
  polynomial ring modulo the variables.

## Main results

* `LinearMap.ker_le_range_of_mapRange_constantCoeff`: a graded square-zero endomorphism of a free
  module over a polynomial ring is exact if its reduction modulo the variables is.
* `LinearMap.homologyMap_bijective_of_mapRange_constantCoeff`: a graded chain map between such
  complexes induces a bijection on homology if its reduction modulo the variables does.
* `LinearMap.constantCoeffReduction_mapRange_constantCoeff`: `constantCoeffReduction f` is a
  reduction of `f` modulo the variables in the sense of the two results above.

## References

The graded homological algebra over `𝔽[V₁, …, Vₙ]` in which this reduction is used is that of
P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
and Monographs 208, 2015, Appendix A.
-/

public section

open Finsupp

namespace LinearMap

open MvPolynomial

variable {R σ ι κ : Type*}

section Coefficients

variable [CommRing R]
  {f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)}
  {f₀ : (ι →₀ R) →ₗ[R] (κ →₀ R)}

/-- The matrix coefficients of the reduction of `f` modulo the variables are the constant
coefficients of those of `f`. -/
private theorem reduction_single_apply
    (hf₀ : ∀ x, f₀ (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _)) (i : ι) (c : R) (j : κ) :
    f₀ (Finsupp.single i c) j = c * constantCoeff (f (Finsupp.single i 1) j) := by
  have h : Finsupp.single i c =
      (Finsupp.single i (C c : MvPolynomial σ R)).mapRange constantCoeff (map_zero _) := by
    rw [mapRange_single, constantCoeff_C]
  rw [h, hf₀, Finsupp.mapRange_apply, ← Finsupp.smul_single_one i (C c), map_smul,
    Finsupp.smul_apply, smul_eq_mul, map_mul, constantCoeff_C]

/-- `f` maps `J ^ k • (ι →₀ S)` into `J ^ k • (κ →₀ S)`, for `J` the ideal of the variables. -/
private theorem apply_mem_pow_idealOfVars {k : ℕ} {z : ι →₀ MvPolynomial σ R}
    (hz : ∀ i, z i ∈ idealOfVars σ R ^ k) (j : κ) : f z j ∈ idealOfVars σ R ^ k := by
  rw [apply_apply_eq_finsuppSum_mul]
  exact Submodule.finsuppSum_mem _ _ _ _ fun i _ ↦ Ideal.mul_mem_right _ _ (hz i)

/-- On `J ^ k • (ι →₀ S)`, the coefficients of `f` in total degree `k` are computed by the
reduction `f₀` of `f` modulo the variables. -/
private theorem coeff_apply_of_mem_pow_idealOfVars
    (hf₀ : ∀ x, f₀ (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _))
    {k : ℕ} {z : ι →₀ MvPolynomial σ R} (hz : ∀ i, z i ∈ idealOfVars σ R ^ k)
    {e : σ →₀ ℕ} (he : degree e = k) (j : κ) :
    (f z j).coeff e = f₀ (z.mapRange (lcoeff R e) (map_zero _)) j := by
  rw [apply_apply_eq_finsuppSum_mul, apply_apply_eq_finsuppSum_mul,
    Finsupp.sum_mapRange_index (by simp), Finsupp.sum, Finsupp.sum, coeff_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_mul_of_mem_pow_idealOfVars _ (hz i) _ he.le, reduction_single_apply hf₀, one_mul,
    lcoeff_apply]

end Coefficients

section Exactness

variable [CommRing R]
  {d : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (ι →₀ MvPolynomial σ R)}
  {d₀ : (ι →₀ R) →ₗ[R] (ι →₀ R)} {w : σ → ℤ} {g : ι → ℤ} {r : ℤ}

/-- A chain all of whose terms `V ^ e • single i a` have degree `g i + weight w e` at least `a`. -/
private def DegreeGE (w : σ → ℤ) (g : ι → ℤ) (a : ℤ) (z : ι →₀ MvPolynomial σ R) : Prop :=
  ∀ i e, (z i).coeff e ≠ 0 → a ≤ g i + weight w e

private theorem DegreeGE.sub {a : ℤ} {z z' : ι →₀ MvPolynomial σ R} (hz : DegreeGE w g a z)
    (hz' : DegreeGE w g a z') : DegreeGE w g a (z - z') := by
  intro i e he
  rw [Finsupp.sub_apply, coeff_sub] at he
  by_cases h : (z i).coeff e = 0
  · exact hz' i e fun h' ↦ he (by rw [h, h', sub_zero])
  · exact hz i e h

/-- A homogeneous map of degree `r` raises lower bounds on degrees by `r`. -/
private theorem DegreeGE.apply
    (hhom : ∀ i j, IsWeightedHomogeneous w (d (Finsupp.single i 1) j) (g i + r - g j)) {a : ℤ}
    {z : ι →₀ MvPolynomial σ R} (hz : DegreeGE w g a z) : DegreeGE w g (a + r) (d z) := by
  classical
  intro j e he
  rw [apply_apply_eq_finsuppSum_mul, Finsupp.sum, coeff_sum] at he
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [coeff_mul] at hi
  obtain ⟨⟨b, c⟩, hbc, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hbc : b + c = e := Finset.mem_antidiagonal.mp hbc
  have hb : a ≤ g i + weight w b := hz i b (left_ne_zero_of_mul hi)
  have hc : weight w c = g i + r - g j := hhom i j (right_ne_zero_of_mul hi)
  rw [← hbc, map_add]
  omega

/-- An element of `J ^ k • (ι →₀ S)` of degree at least `a` vanishes once `k > max g - a`. -/
private theorem DegreeGE.eq_zero (hw : ∀ v, w v < 0) {G : ℤ} (hG : ∀ i, g i ≤ G) {a : ℤ}
    {k : ℕ} (hk : G - a < k) {z : ι →₀ MvPolynomial σ R} (hz : DegreeGE w g a z)
    (hzk : ∀ i, z i ∈ idealOfVars σ R ^ k) : z = 0 := by
  ext i e
  by_contra he
  have h1 := hz i e he
  have h2 := weight_le_degree_nsmul e fun v ↦ Int.le_sub_one_of_lt (hw v)
  rw [zero_sub, nsmul_eq_mul, mul_neg_one] at h2
  have h3 : k ≤ degree e := (mem_pow_idealOfVars_iff k _).mp (hzk i) e
    (MvPolynomial.mem_support_iff.mpr he)
  have h4 := hG i
  omega

variable (hw : ∀ v, w v < 0)
  (hhom : ∀ i j, IsWeightedHomogeneous w (d (Finsupp.single i 1) j) (g i + r - g j))
  (hd₀ : ∀ x, d₀ (x.mapRange constantCoeff (map_zero _)) =
    (d x).mapRange constantCoeff (map_zero _))
include hhom hd₀

/-- The reduction of `d` moves the degree `g` of generators by `r`. -/
private theorem reduction_single_apply_ne_zero {i j : ι} {c : R}
    (h : d₀ (Finsupp.single i c) j ≠ 0) : g j = g i + r := by
  rw [reduction_single_apply hd₀, constantCoeff_eq] at h
  have := hhom i j (right_ne_zero_of_mul h)
  rw [map_zero] at this
  omega

/-- The reduction of `d` commutes with restricting to generators in a set of degrees, up to the
shift by `r`. -/
private theorem filter_reduction_apply (P : ℤ → Prop) [DecidablePred P] (u : ι →₀ R) :
    (d₀ u).filter (fun j ↦ P (g j)) = d₀ (u.filter fun i ↦ P (g i + r)) := by
  induction u using Finsupp.induction_linear with
  | zero => rw [filter_zero, map_zero, filter_zero]
  | add u v hu hv => rw [map_add, filter_add, hu, hv, filter_add, map_add]
  | single i c =>
    by_cases hP : P (g i + r)
    · rw [filter_single_of_pos (p := fun i ↦ P (g i + r)) hP, filter_eq_self_iff]
      intro j hj
      rwa [reduction_single_apply_ne_zero hhom hd₀ hj]
    · rw [filter_single_of_neg (p := fun i ↦ P (g i + r)) hP, map_zero, filter_eq_zero_iff]
      intro j hj
      by_contra h
      exact hP (reduction_single_apply_ne_zero hhom hd₀ h ▸ hj)

/-- One step of the filtration argument: a cycle in `J ^ k • (ι →₀ S)` of degree at least `a` is
congruent modulo `J ^ (k + 1) • (ι →₀ S)` to a boundary of a chain of degree at least `a - r`. -/
private theorem exists_sub_apply_mem_pow_idealOfVars (hexact : ker d₀ ≤ range d₀) {k : ℕ}
    {a : ℤ} {z : ι →₀ MvPolynomial σ R} (hz : d z = 0) (hza : DegreeGE w g a z)
    (hzk : ∀ i, z i ∈ idealOfVars σ R ^ k) :
    ∃ y, DegreeGE w g (a - r) y ∧ ∀ i, (z - d y) i ∈ idealOfVars σ R ^ (k + 1) := by
  classical
  -- the coefficients of `z` at the monomials `V ^ e` of total degree `k`
  let zc (e : σ →₀ ℕ) : ι →₀ R := z.mapRange (lcoeff R e) (map_zero _)
  have hzc (e : σ →₀ ℕ) (he : degree e = k) : ∃ u, d₀ u = zc e := by
    refine hexact (Finsupp.ext fun j ↦ ?_)
    rw [← coeff_apply_of_mem_pow_idealOfVars hd₀ hzk he, hz]
    simp
  choose u hu using fun e ↦ (em (degree e = k)).elim (fun he ↦ (hzc e he).imp fun _ h _ ↦ h)
    fun he ↦ ⟨0, fun h ↦ absurd h he⟩
  -- primitives of these coefficients, restricted to generators of degree at least `a - r`
  let u' (e : σ →₀ ℕ) : ι →₀ R := (u e).filter fun i ↦ a ≤ g i + r + weight w e
  have hu' (e : σ →₀ ℕ) (he : degree e = k) : d₀ (u' e) = zc e := by
    have := filter_reduction_apply hhom hd₀ (fun q ↦ a ≤ q + weight w e) (u e)
    rw [hu e he, (filter_eq_self_iff (fun j ↦ a ≤ g j + weight w e) _).mpr
      fun i hi ↦ hza i e (by simpa [zc] using hi)] at this
    exact this.symm
  -- the monomials of total degree `k` occurring in `z`
  let E : Finset (σ →₀ ℕ) := (z.support.biUnion fun i ↦ (z i).support).filter (degree · = k)
  have hE {e : σ →₀ ℕ} (he : degree e = k) (heE : e ∉ E) (i : ι) : (z i).coeff e = 0 := by
    by_contra h
    refine heE (Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, ?_, ?_⟩, he⟩)
    · exact Finsupp.mem_support_iff.mpr fun hi ↦ h (by simp [hi])
    · exact MvPolynomial.mem_support_iff.mpr h
  let y : ι →₀ MvPolynomial σ R := ∑ e ∈ E, (u' e).mapRange (monomial e) (map_zero _)
  have hy (e : σ →₀ ℕ) (i : ι) : (y i).coeff e = if e ∈ E then u' e i else 0 := by
    simp only [y, Finsupp.finsetSum_apply, Finsupp.mapRange_apply, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hyk (i : ι) : y i ∈ idealOfVars σ R ^ k := by
    rw [mem_pow_idealOfVars_iff]
    intro e he
    rw [MvPolynomial.mem_support_iff, hy] at he
    split_ifs at he with heE
    · exact (Finset.mem_filter.mp heE).2.ge
    · exact absurd rfl he
  refine ⟨y, fun i e he ↦ ?_, fun j ↦ ?_⟩
  · rw [hy] at he
    split_ifs at he with heE
    · by_contra h
      exact he (filter_apply_neg _ _ (by omega))
    · exact absurd rfl he
  · rw [mem_pow_idealOfVars_iff']
    intro e he
    rw [Finsupp.sub_apply, coeff_sub]
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | he
    · rw [(mem_pow_idealOfVars_iff' k _).mp (hzk j) e he,
        (mem_pow_idealOfVars_iff' k _).mp (apply_mem_pow_idealOfVars hyk j) e he, sub_zero]
    · rw [coeff_apply_of_mem_pow_idealOfVars hd₀ hyk he, sub_eq_zero]
      by_cases heE : e ∈ E
      · have : y.mapRange (lcoeff R e) (map_zero _) = u' e := Finsupp.ext fun i ↦ by
          simp [hy, heE]
        rw [this, hu' e he]
        simp [zc]
      · have : y.mapRange (lcoeff R e) (map_zero _) = 0 := Finsupp.ext fun i ↦ by
          simp [hy, heE]
        rw [this, map_zero, Finsupp.zero_apply, hE he heE]

omit hhom hd₀ in
/-- **Graded Nakayama lemma for free complexes over a polynomial ring.** Let `d` be a square-zero
endomorphism of the free module `ι →₀ R[V_v : v ∈ σ]` which is homogeneous of degree `r` when the
generator `i` has degree `g i` and the variable `V_v` has negative degree `w v`, with the degrees
`g i` bounded above. If the reduction `d₀` of `d` modulo the variables, the endomorphism of
`ι →₀ R` with `d₀ ∘ ρ = ρ ∘ d` for `ρ` the coordinatewise constant coefficient, is exact, then so
is `d`. -/
theorem ker_le_range_of_mapRange_constantCoeff
    (d : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (ι →₀ MvPolynomial σ R))
    (hw : ∀ v, w v < 0)
    (hhom : ∀ i j, IsWeightedHomogeneous w (d (Finsupp.single i 1) j) (g i + r - g j))
    (hd₀ : ∀ x, d₀ (x.mapRange constantCoeff (map_zero _)) =
      (d x).mapRange constantCoeff (map_zero _)) (hg : BddAbove (Set.range g))
    (hd : d ∘ₗ d = 0) (hexact : ker d₀ ≤ range d₀) : ker d ≤ range d := by
  classical
  intro z hz
  obtain ⟨G, hG⟩ := hg
  replace hG (i : ι) : g i ≤ G := hG (Set.mem_range_self i)
  -- a lower bound for the degrees of the terms of `z`
  obtain ⟨a, ha⟩ := (z.support.biUnion fun i ↦ (z i).support.image fun e ↦ g i + weight w e)
    |>.bddBelow
  have hza : DegreeGE w g a z := fun i e he ↦ ha <| Finset.mem_coe.mpr <|
    Finset.mem_biUnion.mpr ⟨i, Finsupp.mem_support_iff.mpr fun hi ↦ he (by simp [hi]),
      Finset.mem_image.mpr ⟨e, MvPolynomial.mem_support_iff.mpr he, rfl⟩⟩
  -- correct `z` by boundaries into deeper and deeper powers of the ideal of the variables
  have key (k : ℕ) : ∃ y, DegreeGE w g a (z - d y) ∧
      ∀ i, (z - d y) i ∈ idealOfVars σ R ^ k := by
    induction k with
    | zero => exact ⟨0, by simpa using hza, fun _ ↦ by simp⟩
    | succ k ih =>
      obtain ⟨y, hya, hyk⟩ := ih
      have hcycle : d (z - d y) = 0 := by
        rw [map_sub, mem_ker.mp hz, ← comp_apply d d, hd, zero_apply, sub_zero]
      obtain ⟨y', hy'a, hy'k⟩ :=
        exists_sub_apply_mem_pow_idealOfVars (d := d) hhom hd₀ hexact hcycle hya hyk
      refine ⟨y + y', ?_, ?_⟩
      · rw [map_add, ← sub_sub]
        exact hya.sub (by simpa using hy'a.apply hhom)
      · rwa [map_add, ← sub_sub]
  obtain ⟨y, hya, hyk⟩ := key (G - a + 1).toNat
  refine ⟨y, (sub_eq_zero.mp (hya.eq_zero hw hG (k := (G - a + 1).toNat) ?_ hyk)).symm⟩
  omega

end Exactness

section Reduction

variable [CommSemiring R] {μ : Type*}

/-- If `f₀` and `g₀` are the reductions of `f` and `g` modulo the variables, then `g₀ ∘ f₀` is the
reduction of `g ∘ f`. -/
theorem comp_apply_mapRange_constantCoeff
    (g : (κ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (μ →₀ MvPolynomial σ R))
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    {f₀ : (ι →₀ R) →ₗ[R] (κ →₀ R)} {g₀ : (κ →₀ R) →ₗ[R] (μ →₀ R)}
    (hf₀ : ∀ x, f₀ (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _))
    (hg₀ : ∀ x, g₀ (x.mapRange constantCoeff (map_zero _)) =
      (g x).mapRange constantCoeff (map_zero _)) (x : ι →₀ MvPolynomial σ R) :
    (g₀ ∘ₗ f₀) (x.mapRange constantCoeff (map_zero _)) =
      ((g ∘ₗ f) x).mapRange constantCoeff (map_zero _) := by
  rw [comp_apply, hf₀, hg₀, comp_apply]

/-- A reduction modulo the variables is determined by the map it reduces: reductions `f₀` of `f`
and `f₀'` of `f'` agree when `f = f'`. -/
theorem eq_of_mapRange_constantCoeff (f₀ f₀' : (ι →₀ R) →ₗ[R] (κ →₀ R))
    {f f' : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)}
    (hf₀ : ∀ x, f₀ (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _))
    (hf₀' : ∀ x, f₀' (x.mapRange constantCoeff (map_zero _)) =
      (f' x).mapRange constantCoeff (map_zero _)) (h : f = f') :
    f₀ = f₀' := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero _)
    (fun c ↦ ⟨C c, constantCoeff_C σ c⟩) x
  rw [hf₀, hf₀', h]

/-- The reduction of an `S`-linear map `f : (ι →₀ S) → (κ →₀ S)` modulo the variables, for
`S = R[V_v : v ∈ σ]`: the `R`-linear map `(ι →₀ R) → (κ →₀ R)` whose matrix coefficients are the
constant coefficients of those of `f`. It is the reduction in the sense of this file
(`LinearMap.constantCoeffReduction_mapRange_constantCoeff`). -/
noncomputable def constantCoeffReduction
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) :
    (ι →₀ R) →ₗ[R] (κ →₀ R) :=
  Finsupp.linearCombination R fun i ↦
    (f (Finsupp.single i 1)).mapRange constantCoeff (map_zero _)

/-- The matrix coefficients of the reduction of `f` modulo the variables are the constant
coefficients of those of `f`. -/
@[simp]
theorem constantCoeffReduction_single_apply
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) (i : ι) (c : R)
    (j : κ) :
    f.constantCoeffReduction (Finsupp.single i c) j =
      c * constantCoeff (f (Finsupp.single i 1) j) := by
  simp [constantCoeffReduction]

/-- **The reduction commutes with setting the variables to zero.** Applying
`constantCoeffReduction f` to the constant coefficients of `x` gives the constant coefficients of
`f x`. -/
@[simp]
theorem constantCoeffReduction_mapRange_constantCoeff
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    (x : ι →₀ MvPolynomial σ R) :
    f.constantCoeffReduction (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Finsupp.mapRange_add (map_add _), map_add, hx, hy, map_add,
      Finsupp.mapRange_add (map_add _)]
  | single i p =>
    ext j
    rw [Finsupp.mapRange_single, constantCoeffReduction_single_apply, Finsupp.mapRange_apply,
      ← Finsupp.smul_single_one i p, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]

/-- The reduction of a composite is the composite of the reductions. -/
@[simp]
theorem constantCoeffReduction_comp
    (g : (κ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (μ →₀ MvPolynomial σ R))
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) :
    (g ∘ₗ f).constantCoeffReduction = g.constantCoeffReduction ∘ₗ f.constantCoeffReduction :=
  eq_of_mapRange_constantCoeff _ _ (constantCoeffReduction_mapRange_constantCoeff _)
    (comp_apply_mapRange_constantCoeff g f (constantCoeffReduction_mapRange_constantCoeff f)
      (constantCoeffReduction_mapRange_constantCoeff g)) rfl

/-- The identity map reduces to the identity map. -/
@[simp]
theorem constantCoeffReduction_id :
    (LinearMap.id : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (ι →₀ MvPolynomial σ R)).constantCoeffReduction = LinearMap.id := by
  exact eq_of_mapRange_constantCoeff _ _
    (constantCoeffReduction_mapRange_constantCoeff _) (fun _ ↦ rfl) rfl

/-- Reduction commutes with addition of linear maps. -/
@[simp]
theorem constantCoeffReduction_add
    (f g : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (f + g).constantCoeffReduction = f.constantCoeffReduction + g.constantCoeffReduction := by
  ext i c
  simp [mul_add]

/-- Reduction commutes with scalar multiplication of linear maps. -/
@[simp]
theorem constantCoeffReduction_smul (p : MvPolynomial σ R)
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (p • f).constantCoeffReduction = constantCoeff p • f.constantCoeffReduction := by
  ext i c
  simp [constantCoeffReduction_single_apply]

/-- The reduction of the zero map is zero. -/
@[simp]
theorem constantCoeffReduction_zero :
    constantCoeffReduction
      (0 : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)) = 0 := by
  ext i c
  simp

end Reduction

section ReductionRing

variable [CommRing R]

/-- Reduction commutes with negation of linear maps. -/
@[simp]
theorem constantCoeffReduction_neg
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (-f).constantCoeffReduction = -f.constantCoeffReduction := by
  ext i c
  simp

/-- Reduction commutes with subtraction of linear maps. -/
@[simp]
theorem constantCoeffReduction_sub
    (f g : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (κ →₀ MvPolynomial σ R)) :
    (f - g).constantCoeffReduction = f.constantCoeffReduction - g.constantCoeffReduction := by
  ext i c
  simp [mul_sub]

end ReductionRing

section QuasiIso

variable [CommRing R]

variable {d : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (ι →₀ MvPolynomial σ R)}
  {e : (κ →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)}
  {f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R)}
  {d₀ : (ι →₀ R) →ₗ[R] (ι →₀ R)} {e₀ : (κ →₀ R) →ₗ[R] (κ →₀ R)} {f₀ : (ι →₀ R) →ₗ[R] (κ →₀ R)}
  {w : σ → ℤ} {g : ι → ℤ} {g' : κ → ℤ} {r δ : ℤ}

/-- **Quasi-isomorphisms of graded free complexes over a polynomial ring are detected modulo the
variables.** Let `d` and `e` be square-zero endomorphisms of the free modules `ι →₀ S` and
`κ →₀ S` over `S = R[V_v : v ∈ σ]`, and `f` a chain map between them. Suppose the generators
carry degrees `g i` and `g' j`, bounded above, the variables `V_v` have negative degrees `w v`, the
maps `d` and `e` are homogeneous of the same degree `r`, and `f` is homogeneous of degree `δ`. If
the reduction `f₀` of `f` modulo the variables induces a bijection from the homology of the
reduction `d₀` of `d` to that of the reduction `e₀` of `e`, then `f` induces a bijection on
homology. -/
theorem homologyMap_bijective_of_mapRange_constantCoeff
    (f : (ι →₀ MvPolynomial σ R) →ₗ[MvPolynomial σ R] (κ →₀ MvPolynomial σ R))
    (hw : ∀ v, w v < 0)
    (hg : BddAbove (Set.range g)) (hg' : BddAbove (Set.range g'))
    (hdhom : ∀ i j, IsWeightedHomogeneous w (d (Finsupp.single i 1) j) (g i + r - g j))
    (hehom : ∀ i j, IsWeightedHomogeneous w (e (Finsupp.single i 1) j) (g' i + r - g' j))
    (hfhom : ∀ i j, IsWeightedHomogeneous w (f (Finsupp.single i 1) j) (g i + δ - g' j))
    (hdd₀ : ∀ x, d₀ (x.mapRange constantCoeff (map_zero _)) =
      (d x).mapRange constantCoeff (map_zero _))
    (hee₀ : ∀ x, e₀ (x.mapRange constantCoeff (map_zero _)) =
      (e x).mapRange constantCoeff (map_zero _))
    (hff₀ : ∀ x, f₀ (x.mapRange constantCoeff (map_zero _)) =
      (f x).mapRange constantCoeff (map_zero _))
    (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0) (hf : f ∘ₗ d = e ∘ₗ f)
    (h : Function.Bijective (homologyMap f₀
      (eq_of_mapRange_constantCoeff _ _
        (comp_apply_mapRange_constantCoeff d d hdd₀ hdd₀) (by simp) hd)
      (eq_of_mapRange_constantCoeff _ _
        (comp_apply_mapRange_constantCoeff e e hee₀ hee₀) (by simp) he)
      (eq_of_mapRange_constantCoeff _ _ (comp_apply_mapRange_constantCoeff f d hdd₀ hff₀)
        (comp_apply_mapRange_constantCoeff e f hff₀ hee₀) hf))) :
    Function.Bijective (homologyMap f hd he hf) := by
  rw [← ker_le_range_mappingCone_iff, ← ker_le_range_sumMappingCone_iff]
  rw [← ker_le_range_mappingCone_iff, ← ker_le_range_sumMappingCone_iff] at h
  obtain ⟨G, hG⟩ := hg
  obtain ⟨G', hG'⟩ := hg'
  refine ker_le_range_of_mapRange_constantCoeff (sumMappingCone d e f)
    (g := Sum.elim (fun i ↦ g i + δ - r) g') (r := r)
    (d₀ := sumMappingCone d₀ e₀ f₀) hw ?_ ?_ ⟨max (G + δ - r) G', ?_⟩
    (sumMappingCone_comp_self hd he hf) h
  · rintro (i | i) (j | j)
    · convert (hdhom i j).neg using 1
      · simp
      · simp only [Sum.elim_inl]
        ring
    · convert hfhom i j using 1
      · simp
      · simp only [Sum.elim_inl, Sum.elim_inr]
        ring
    · convert isWeightedHomogeneous_zero R w _ using 1
      simp
    · convert hehom i j using 1
      · simp
      · simp only [Sum.elim_inr]
  · intro x
    have hε : sumFinsuppLEquivProdFinsupp R (x.mapRange constantCoeff (map_zero _)) =
        ((sumFinsuppLEquivProdFinsupp (MvPolynomial σ R) x).1.mapRange constantCoeff
            (map_zero _),
          (sumFinsuppLEquivProdFinsupp (MvPolynomial σ R) x).2.mapRange constantCoeff
            (map_zero _)) := by
      ext <;> simp
    ext (j | j)
    · simp only [sumMappingCone_apply, sumFinsuppLEquivProdFinsupp_symm_inl, mappingCone_apply,
        Finsupp.coe_neg, Pi.neg_apply, Finsupp.mapRange_apply, map_neg, hε]
      exact congr(-$(hdd₀ _) j)
    · simp only [sumMappingCone_apply, sumFinsuppLEquivProdFinsupp_symm_inr, mappingCone_apply,
        Finsupp.coe_add, Pi.add_apply, Finsupp.mapRange_apply, map_add, hε]
      exact congr($(hff₀ _) j + $(hee₀ _) j)
  · rintro _ ⟨i | i, rfl⟩
    · have := hG ⟨i, rfl⟩
      simp only [Sum.elim_inl]
      omega
    · have := hG' ⟨i, rfl⟩
      simp only [Sum.elim_inr]
      omega

end QuasiIso

end LinearMap
