/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import TauCeti.Algebra.Homology.SquareZero
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.ConstantCoeffReduction

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

## Main results

* `LinearMap.ker_le_range_of_mapRange_constantCoeff`: a graded square-zero endomorphism of a free
  module over a polynomial ring is exact if its reduction modulo the variables is.
* `LinearMap.homologyMap_bijective_of_mapRange_constantCoeff`: a graded chain map between such
  complexes induces a bijection on homology if its reduction modulo the variables does.

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
include hhom

/-- One step of the filtration argument: a cycle in `J ^ k • (ι →₀ S)` of degree at least `a` is
congruent modulo `J ^ (k + 1) • (ι →₀ S)` to a boundary of a chain of degree at least `a - r`. -/
private theorem exists_sub_apply_mem_pow_idealOfVars
    (hexact : ker d.constantCoeffReduction ≤ range d.constantCoeffReduction) {k : ℕ}
    {a : ℤ} {z : ι →₀ MvPolynomial σ R} (hz : d z = 0) (hza : DegreeGE w g a z)
    (hzk : ∀ i, z i ∈ idealOfVars σ R ^ k) :
    ∃ y, DegreeGE w g (a - r) y ∧ ∀ i, (z - d y) i ∈ idealOfVars σ R ^ (k + 1) := by
  classical
  -- the coefficients of `z` at the monomials `V ^ e` of total degree `k`
  let zc (e : σ →₀ ℕ) : ι →₀ R := z.mapRange (lcoeff R e) (map_zero _)
  have hzc (e : σ →₀ ℕ) (he : degree e = k) : ∃ u, d.constantCoeffReduction u = zc e := by
    refine hexact (Finsupp.ext fun j ↦ ?_)
    rw [← coeff_apply_of_mem_pow_idealOfVars d hzk he, hz]
    simp
  choose u hu using fun e ↦ (em (degree e = k)).elim (fun he ↦ (hzc e he).imp fun _ h _ ↦ h)
    fun he ↦ ⟨0, fun h ↦ absurd h he⟩
  -- primitives of these coefficients, restricted to generators of degree at least `a - r`
  let u' (e : σ →₀ ℕ) : ι →₀ R := (u e).filter fun i ↦ a ≤ g i + r + weight w e
  have hu' (e : σ →₀ ℕ) (he : degree e = k) : d.constantCoeffReduction (u' e) = zc e := by
    have := filter_constantCoeffReduction_apply d hhom (fun q ↦ a ≤ q + weight w e) (u e)
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
  have hdyk (j : ι) : d y j ∈ idealOfVars σ R ^ k := by
    rw [apply_apply_eq_finsuppSum_mul]
    exact Submodule.finsuppSum_mem _ _ _ _ fun i _ ↦ Ideal.mul_mem_right _ _ (hyk i)
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
        (mem_pow_idealOfVars_iff' k _).mp (hdyk j) e he, sub_zero]
    · rw [coeff_apply_of_mem_pow_idealOfVars d hyk he, sub_eq_zero]
      by_cases heE : e ∈ E
      · have : y.mapRange (lcoeff R e) (map_zero _) = u' e := Finsupp.ext fun i ↦ by
          simp [hy, heE]
        rw [this, hu' e he]
        simp [zc]
      · have : y.mapRange (lcoeff R e) (map_zero _) = 0 := Finsupp.ext fun i ↦ by
          simp [hy, heE]
        rw [this, map_zero, Finsupp.zero_apply, hE he heE]

omit hhom in
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
  have hred : d₀ = d.constantCoeffReduction :=
    eq_of_mapRange_constantCoeff _ _ hd₀ (constantCoeffReduction_mapRange_constantCoeff d) rfl
  subst d₀
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
        exists_sub_apply_mem_pow_idealOfVars (d := d) hhom hexact hcycle hya hyk
      refine ⟨y + y', ?_, ?_⟩
      · rw [map_add, ← sub_sub]
        exact hya.sub (by simpa using hy'a.apply hhom)
      · rwa [map_add, ← sub_sub]
  obtain ⟨y, hya, hyk⟩ := key (G - a + 1).toNat
  refine ⟨y, (sub_eq_zero.mp (hya.eq_zero hw hG (k := (G - a + 1).toNat) ?_ hyk)).symm⟩
  omega

end Exactness

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
