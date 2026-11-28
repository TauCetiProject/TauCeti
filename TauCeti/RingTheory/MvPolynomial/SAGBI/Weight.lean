/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Initial.Algebra
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Rees
public import TauCeti.RingTheory.MvPolynomial.Subalgebra.WeightFiltration
import TauCeti.Algebra.Polynomial.AlgHom

/-!
# Bounded expressions and the induced weight Rees algebra

Suppose `c i` has weight at most `d i`, with component `g i` in weight `d i`. If relations
`r j` generate the kernel of substitution by `g`, and each substituted relation has an
expression `Q j` of strictly smaller weight, every element of `R[c]` of ambient weight at
most `n` has an expression in the `c i` of weight at most `n`. The bound concerns the
whole expression, including cancellations, rather than just its substituted value.

Consequently the image of `weightReesAeval c d` is precisely the embedded Rees algebra
`Subalgebra.weightReesAlgebra` of the induced weight filtration
(`Subalgebra.map_weightReesAlgebra_eq_range_weightReesAeval`), and when `c` generates `A`, the
lifted presentation `weightReesAevalLift` surjects onto `A.weightReesAlgebra w`
(`TauCeti.MvPolynomial.weightReesAevalLift_surjective`); when the generator index `ι` is finite,
`A.weightReesAlgebra w` is of finite type over `R[t]` (`Subalgebra.finiteType_weightReesAlgebra`).
The weight-initial algebra `(Algebra.adjoin R (Set.range c)).weightInitialAlgebra w` is `R[g]`
(`TauCeti.MvPolynomial.weightInitialAlgebra_adjoin_eq`). These results use the same relation
certificates as `ker_weightReesAeval_eq_span`, so the presentation describes the actual induced
filtration, as well as its kernel. Zero weights, scalar generators, empty families, and arbitrary
commutative rings are allowed.

The reduction step is `exists_finsupp_sub_sum_mem_weightFiltrationLT` from
`TauCeti.RingTheory.MvPolynomial.SAGBI.Rees`: cancel the top block of an expression by
lifted relations, then induct on its weight.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, AMS, 1996, Chapter 11.
* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Mathematics 1430, Springer, 1990, 61–87.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial
open scoped Polynomial

variable {σ ι J R : Type*} [CommRing R] {w : σ → ℕ} {c g : ι → MvPolynomial σ R}
  {d : ι → ℕ} {r Q : J → MvPolynomial ι R} {e : J → ℕ}

/-- Bounded relation certificates give bounded expressions for every element of the generated
subalgebra. An ambient weight bound on the value can therefore be attained by its expression. -/
theorem exists_aeval_eq_of_mem_adjoin_of_mem_weightFiltration
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j))
    {f : MvPolynomial σ R} {n : ℕ} (hf : f ∈ Algebra.adjoin R (Set.range c))
    (hfn : f ∈ weightFiltration R w n) :
    ∃ P ∈ weightFiltration R d n, aeval c P = f := by
  classical
  rw [← aeval_range] at hf
  obtain ⟨P, hP⟩ := hf
  have reduce (l : ℕ) : ∀ P ∈ weightFiltration R d l, aeval c P = f →
      ∃ S ∈ weightFiltration R d n, aeval c S = f := by
    induction l using Nat.strong_induction_on with
    | ind l ih =>
      intro P hPl hPf
      by_cases hln : l ≤ n
      · exact ⟨P, weightFiltration_mono hln hPl, hPf⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
      have htop : weightedHomogeneousComponent w (k + 1) (aeval c P) = 0 := by
        rw [hPf]
        exact weightedHomogeneousComponent_eq_zero (φ := f) (w := w) (k + 1)
          (lt_of_le_of_lt (mem_weightFiltration_iff_weightedTotalDegree_le.1 hfn) (by omega))
      obtain ⟨h, -, hlt⟩ := exists_finsupp_sub_sum_mem_weightFiltrationLT hc hg hJ hr hQ hPl htop
      rw [weightFiltrationLT_succ] at hlt
      apply ih k (Nat.lt_succ_self k) _ hlt
      simp [Finsupp.sum, hQc, hPf]
  exact reduce (P.weightedTotalDegree d) P
    (mem_weightFiltration_iff_weightedTotalDegree_le.2 le_rfl) hP

/-- Every homogeneous component at a prescribed upper weight bound of an element of `R[c]`
belongs to `R[g]`, under the bounded relation certificates. -/
theorem weightedHomogeneousComponent_mem_adjoin_of_mem_weightFiltration
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j))
    {f : MvPolynomial σ R} {n : ℕ} (hf : f ∈ Algebra.adjoin R (Set.range c))
    (hfn : f ∈ weightFiltration R w n) :
    weightedHomogeneousComponent w n f ∈ Algebra.adjoin R (Set.range g) := by
  obtain ⟨P, hPn, rfl⟩ :=
    exists_aeval_eq_of_mem_adjoin_of_mem_weightFiltration hc hg hJ hr hQ hQc hf hfn
  rw [weightedHomogeneousComponent_aeval_of_mem_weightFiltration hc hg hPn, ← aeval_range]
  exact ⟨_, rfl⟩

/-- The bounded relation certificates identify the entire weight-initial algebra of `R[c]`
with `R[g]`. This uses initial forms of all elements, rather than just of the generators. -/
theorem weightInitialAlgebra_adjoin_eq
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (Algebra.adjoin R (Set.range c)).weightInitialAlgebra w =
      Algebra.adjoin R (Set.range g) := by
  rw [Subalgebra.weightInitialAlgebra_def]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨f, hf, rfl⟩
    rw [weightInitialForm_def]
    exact weightedHomogeneousComponent_mem_adjoin_of_mem_weightFiltration hc hg hJ hr hQ hQc hf
      (mem_weightFiltration_iff_weightedTotalDegree_le.2 le_rfl)
  · rintro _ ⟨i, rfl⟩
    rw [← hg i]
    have hle := mem_weightFiltration_iff_weightedTotalDegree_le.1 (hc i)
    rcases hle.eq_or_lt with heq | hlt
    · rw [← heq, ← weightInitialForm_def]
      exact Algebra.subset_adjoin ⟨c i, Algebra.subset_adjoin (Set.mem_range_self i), rfl⟩
    · rw [weightedHomogeneousComponent_eq_zero (w := w) (φ := c i) (d i) hlt]
      exact zero_mem _

/-- The image of the Rees presentation is the Rees algebra of the induced weight filtration
on `R[c]`: the coefficient of `t^n` belongs to `R[c]` and has ambient weight at most `n`. -/
theorem mem_range_weightReesAeval_iff
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) {f : (MvPolynomial σ R)[X]} :
    f ∈ (weightReesAeval c d).range ↔
      ∀ n, f.coeff n ∈ Algebra.adjoin R (Set.range c) ∧
        f.coeff n ∈ weightFiltration R w n := by
  classical
  constructor
  · rintro hf n
    obtain ⟨p, rfl⟩ := ((weightReesAeval c d).mem_range).1 hf
    refine ⟨?_, (mem_coeffSubalgebra_iff.1 (weightReesAeval_mem_weightReesAlgebra hc p)) n⟩
    rw [weightReesAeval_eq_comp, AlgHom.comp_apply, Polynomial.coe_mapAlgHom,
      Polynomial.coeff_map, ← aeval_range]
    exact ⟨_, rfl⟩
  · intro hf
    rw [f.as_sum_support]
    refine Subalgebra.sum_mem _ fun n _ ↦ ?_
    obtain ⟨P, hPn, hP⟩ := exists_aeval_eq_of_mem_adjoin_of_mem_weightFiltration
      hc hg hJ hr hQ hQc (hf n).1 (hf n).2
    apply ((weightReesAeval c d).mem_range).2
    exact ⟨weightHomogenization R d n P, by
      rw [weightReesAeval_weightHomogenization hPn, hP]⟩

/-- The image of the Rees presentation is the intersection of the ambient weight Rees
algebra with the polynomial algebra having coefficients in `R[c]`. -/
theorem range_weightReesAeval_eq_inf
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (weightReesAeval c d).range =
      weightReesAlgebra R w ⊓ (Polynomial.mapAlgHom (aeval c)).range := by
  ext f
  rw [mem_range_weightReesAeval_iff hc hg hJ hr hQ hQc, Algebra.mem_inf,
    mem_coeffSubalgebra_iff, Polynomial.mem_mapAlgHom_range, aeval_range]
  exact forall_and.trans and_comm

end TauCeti.MvPolynomial

namespace Subalgebra

open _root_.MvPolynomial TauCeti.MvPolynomial
open scoped Polynomial

/-- Under bounded relation certificates, the SAGBI Rees presentation is the embedded
Rees algebra of the induced filtration, not merely an algebra with the same generators. -/
theorem map_weightReesAlgebra_eq_range_weightReesAeval
    {σ ι J R : Type*} [CommRing R] (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ)
    {c g : ι → MvPolynomial σ R} {d : ι → ℕ}
    {r Q : J → MvPolynomial ι R} {e : J → ℕ}
    (hA : A = Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ TauCeti.MvPolynomial.weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ TauCeti.MvPolynomial.weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) = (weightReesAeval c d).range := by
  rw [A.map_weightReesAlgebra, range_weightReesAeval_eq_inf hc hg hJ hr hQ hQc]
  congr 1
  ext p
  rw [Polynomial.mem_mapAlgHom_range, Polynomial.mem_mapAlgHom_range, Subalgebra.range_val,
    aeval_range, hA]

end Subalgebra

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial
open scoped Polynomial

attribute [local instance] Polynomial.algebra in
/-- Under bounded relation certificates, `weightReesAevalLift` surjects onto the induced weight
Rees algebra `A.weightReesAlgebra w` whenever the `c i` generate `A`. -/
theorem weightReesAevalLift_surjective {σ ι J R : Type*} [CommRing R]
    {w : σ → ℕ} {c g : ι → MvPolynomial σ R} {d : ι → ℕ}
    {r Q : J → MvPolynomial ι R} {e : J → ℕ} {A : Subalgebra R (MvPolynomial σ R)}
    (hcA : ∀ i, c i ∈ A) (hA : A ≤ Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    Function.Surjective (weightReesAevalLift hcA hc) := by
  have hAeq : A = Algebra.adjoin R (Set.range c) :=
    le_antisymm hA (Algebra.adjoin_le (Set.range_subset_iff.mpr hcA))
  intro y
  have hy : ((A.weightReesInclusion w y : weightReesAlgebra R w) : (MvPolynomial σ R)[X]) ∈
      (weightReesAeval c d).range := by
    rw [← A.map_weightReesAlgebra_eq_range_weightReesAeval w hAeq hc hg hJ hr hQ hQc]
    exact Subalgebra.mem_map.mpr
      ⟨y, y.property, by rw [Polynomial.coe_mapAlgHom, A.coe_weightReesInclusion]⟩
  obtain ⟨f, hf⟩ := (weightReesAeval c d).mem_range.mp hy
  refine ⟨f, A.weightReesInclusion_injective w (Subtype.ext ?_)⟩
  rwa [coe_weightReesInclusion_weightReesAevalLift]

end TauCeti.MvPolynomial

namespace Subalgebra

open _root_.MvPolynomial TauCeti.MvPolynomial
open scoped Polynomial

attribute [local instance] Polynomial.algebra in
/-- Under bounded relation certificates with a finite generator index, the induced weight Rees
algebra `A.weightReesAlgebra w` is of finite type over `R[t]`. -/
theorem finiteType_weightReesAlgebra {σ ι J R : Type*} [CommRing R] [Finite ι]
    (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ)
    {c g : ι → MvPolynomial σ R} {d : ι → ℕ}
    {r Q : J → MvPolynomial ι R} {e : J → ℕ}
    (hA : A = Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ TauCeti.MvPolynomial.weightFiltration R w (d i))
    (hg : ∀ i, weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ TauCeti.MvPolynomial.weightFiltrationLT R d (e j))
    (hQc : ∀ j, aeval c (Q j) = aeval c (r j)) :
    Algebra.FiniteType R[X] (A.weightReesAlgebra w) := by
  have : Algebra.FiniteType R[X] (MvPolynomial ι R)[X] :=
    Algebra.FiniteType.of_restrictScalars_finiteType R R[X] (MvPolynomial ι R)[X]
  exact Algebra.FiniteType.of_surjective _
    (weightReesAevalLift_surjective (fun i ↦ hA ▸ Algebra.subset_adjoin (Set.mem_range_self i))
      hA.le hc hg hJ hr hQ hQc)

end Subalgebra
