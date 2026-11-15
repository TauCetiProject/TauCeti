/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.SAGBI.Weight
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Flat

/-!
# The induced weight filtration on a polynomial subalgebra

For a subalgebra `A` of a multivariate polynomial ring, pull back the ambient weight
filtration to `A`. Its Rees algebra is realized inside `A[t]` using `coeffSubalgebra`.
The coefficientwise embedding into the ambient polynomial ring identifies it with the
intersection of the ambient weight Rees algebra and `A[t]`. Thus the existing bounded
SAGBI certificates identify their Rees presentation with this carrier.

Over a field this Rees algebra is flat over `k[t]`, without any finite generation or SAGBI
hypothesis. The increasing and exhaustive filtration also permits applying the shared
`coeffSubalgebra` unit-fibre comparisons.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, AMS, 1996, Chapter 11.
* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, §15.8.
-/

public section

open scoped Polynomial
open TauCeti TauCeti.MvPolynomial

namespace Subalgebra

variable {σ R : Type*} [CommSemiring R] (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ)

/-- The ambient weight filtration restricted to a polynomial subalgebra. -/
noncomputable def weightFiltration (n : ℕ) : Submodule R A :=
  (TauCeti.MvPolynomial.weightFiltration R w n).comap A.val.toLinearMap

/-- Membership in the induced filtration is the ambient weight bound. -/
@[simp]
theorem mem_weightFiltration_iff {n : ℕ} {f : A} :
    f ∈ A.weightFiltration w n ↔
      (f : MvPolynomial σ R) ∈ TauCeti.MvPolynomial.weightFiltration R w n :=
  Iff.rfl

/-- The lower stages of the induced weight filtration. -/
noncomputable def weightFiltrationLT (n : ℕ) : Submodule R A :=
  (TauCeti.MvPolynomial.weightFiltrationLT R w n).comap A.val.toLinearMap

/-- Membership in a lower stage is the strict ambient weight bound. -/
@[simp]
theorem mem_weightFiltrationLT_iff {n : ℕ} {f : A} :
    f ∈ A.weightFiltrationLT w n ↔
      (f : MvPolynomial σ R) ∈ TauCeti.MvPolynomial.weightFiltrationLT R w n :=
  Iff.rfl

/-- The induced weight filtration is multiplicative. -/
instance weightFiltrationGradedMonoid : SetLike.GradedMonoid (A.weightFiltration w) where
  one_mem := by
    simpa using (SetLike.GradedOne.one_mem :
      (1 : MvPolynomial σ R) ∈ TauCeti.MvPolynomial.weightFiltration R w 0)
  mul_mem {i j} {f g} hf hg := by
    simpa using SetLike.mul_mem_graded
      ((A.mem_weightFiltration_iff w).mp hf) ((A.mem_weightFiltration_iff w).mp hg)

/-- The induced weight filtration is increasing. -/
theorem weightFiltration_mono : Monotone (A.weightFiltration w) :=
  fun _ _ h _ hf ↦ TauCeti.MvPolynomial.weightFiltration_mono h hf

/-- The induced filtration, with its strict lower stages, is a native ring filtration. -/
instance weightFiltrationIsRingFiltration :
    IsRingFiltration (A.weightFiltration w) (A.weightFiltrationLT w) where
  mono := A.weightFiltration_mono w
  is_le h _ hf := IsFiltration.is_le
    (F := TauCeti.MvPolynomial.weightFiltration R w) h hf
  is_sup B n hB := by
    cases n with
    | zero =>
      intro f hf
      have hf0 : (f : MvPolynomial σ R) = 0 := by
        simpa using (A.mem_weightFiltrationLT_iff w).mp hf
      have : f = 0 := Subtype.ext hf0
      exact this ▸ B.zero_mem
    | succ n =>
      intro f hf
      apply hB n (Nat.lt_succ_self n)
      simpa [weightFiltrationLT, weightFiltration,
        TauCeti.MvPolynomial.weightFiltrationLT_succ] using hf

/-- Every element of a polynomial subalgebra has a finite weight bound. -/
theorem iSup_weightFiltration : (⨆ n, A.weightFiltration w n) = ⊤ := by
  apply top_unique
  intro f _
  apply Submodule.mem_iSup_of_mem ((f : MvPolynomial σ R).weightedTotalDegree w)
  exact mem_weightFiltration_iff_weightedTotalDegree_le.mpr le_rfl

/-- The parameter belongs to the Rees algebra of the induced weight filtration. -/
theorem one_mem_weightFiltration_one : (1 : A) ∈ A.weightFiltration w 1 := by
  simpa using TauCeti.MvPolynomial.one_mem_weightFiltration_one R w

/-- The Rees algebra of the induced weight filtration, inside `A[t]`. -/
noncomputable abbrev weightReesAlgebra : Subalgebra R A[X] :=
  coeffSubalgebra (A.weightFiltration w)

/-- The induced Rees algebra embeds as the intersection of the ambient weight Rees algebra
with the polynomial algebra having coefficients in `A`. -/
theorem map_weightReesAlgebra :
    (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) =
      TauCeti.MvPolynomial.weightReesAlgebra R w ⊓ (Polynomial.mapAlgHom A.val).range := by
  ext p
  simp only [Subalgebra.mem_map, Algebra.mem_inf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, AlgHom.mem_range_self _ q⟩
    rw [TauCeti.MvPolynomial.weightReesAlgebra, mem_coeffSubalgebra_iff]
    simpa using mem_coeffSubalgebra_iff.mp hq
  · rintro ⟨hp, q, rfl⟩
    refine ⟨q, ?_, rfl⟩
    apply mem_coeffSubalgebra_iff.mpr
    simpa using mem_coeffSubalgebra_iff.mp hp

end Subalgebra

namespace Subalgebra

variable {σ R : Type*} [CommRing R] (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ)

/-- Under bounded relation certificates, the SAGBI Rees presentation is exactly the embedded
Rees algebra of the induced filtration, not merely an algebra with the same generators. -/
theorem map_weightReesAlgebra_eq_range_weightReesAeval
    {ι J : Type*} {c g : ι → MvPolynomial σ R} {d : ι → ℕ}
    {r Q : J → MvPolynomial ι R} {e : J → ℕ}
    (hA : A = Algebra.adjoin R (Set.range c))
    (hc : ∀ i, c i ∈ TauCeti.MvPolynomial.weightFiltration R w (d i))
    (hg : ∀ i, MvPolynomial.weightedHomogeneousComponent w (d i) (c i) = g i)
    (hJ : RingHom.ker (MvPolynomial.aeval g) = Ideal.span (Set.range r))
    (hr : ∀ j, (r j).IsWeightedHomogeneous d (e j))
    (hQ : ∀ j, Q j ∈ TauCeti.MvPolynomial.weightFiltrationLT R d (e j))
    (hQc : ∀ j, MvPolynomial.aeval c (Q j) = MvPolynomial.aeval c (r j)) :
    (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) = (weightReesAeval c d).range := by
  rw [A.map_weightReesAlgebra,
    range_weightReesAeval_eq_inf hc hg hJ hr hQ hQc]
  congr 1
  ext p
  have hv' : p ∈ (Polynomial.mapAlgHom A.val).range ↔ ∀ n, p.coeff n ∈ A.val.range :=
    Polynomial.mem_map_rangeS A.val.toRingHom
  rw [Subalgebra.range_val] at hv'
  have hc' : p ∈ (Polynomial.mapAlgHom (MvPolynomial.aeval c)).range ↔
      ∀ n, p.coeff n ∈ (MvPolynomial.aeval (R := R) c).range :=
    Polynomial.mem_map_rangeS (MvPolynomial.aeval (R := R) c).toRingHom
  rw [hv', hc', MvPolynomial.aeval_range, hA]

/-- The induced weight Rees algebra is flat over the actual parameter ring. No SAGBI basis,
finite generation, positivity of weights, or finite-variable hypothesis is needed. -/
theorem flat_weightReesAlgebra {k : Type*} [Field k]
    (A : Subalgebra k (MvPolynomial σ k)) (w : σ → ℕ) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    Module.Flat k[X] (A.weightReesAlgebra w) :=
  coeffSubalgebra.flat _ _

end Subalgebra
