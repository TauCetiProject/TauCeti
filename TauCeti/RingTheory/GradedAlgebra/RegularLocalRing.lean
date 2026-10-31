/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.GradedAlgebra.Cotangent
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Connected graded algebras that are regular at the vertex

Let `A` be an `ℕ`-graded algebra over a field `k` which is *connected*: its degree-zero part
consists of the scalars. Write `A₊` for the irrelevant ideal, the vertex of `Spec A`. If the local
ring `A_{A₊}` is regular of dimension `n`, then `A` is a polynomial algebra over `k` on `n`
homogeneous elements of positive degree.

The proof lifts generators of the maximal ideal of `A_{A₊}` to `A`. Since every element outside
`A₊` has a nonzero constant term (`TauCeti.GradedAlgebra.exists_sub_algebraMap_mem_irrelevant`),
the lifts span the `k`-vector space `A₊ ⧸ A₊²`. So whenever the maximal ideal of `A_{A₊}` is
finitely generated, the cotangent space `A₊ ⧸ A₊²` is finite-dimensional, of dimension at most the
minimal number of generators of that maximal ideal. In the regular case this number is `n`, while
`A` has Krull dimension at least `n`, the dimension of its localization, and at most the dimension
of its cotangent space (`TauCeti.GradedAlgebra.ringKrullDim_le_finrank_cotangent`). So the
cotangent space has dimension exactly `n`, and `A` is a polynomial algebra on `n` homogeneous
generators (`TauCeti.GradedAlgebra.exists_bijective_aeval_of_finrank_cotangent_le`).

No Noetherian hypothesis on `A` is needed: finite generation is a consequence.

For the invariants of a finite linear group this gives the last step of the homological proof of
the Chevalley–Shephard–Todd theorem: once the invariant ring is known to be regular at its
vertex, it is a polynomial algebra on homogeneous basic invariants.

## Main results

* `TauCeti.GradedAlgebra.finite_cotangent_of_fg`: if the maximal ideal of `A_{A₊}` is finitely
  generated, the cotangent space `A₊ ⧸ A₊²` is finite-dimensional over `k`.
* `TauCeti.GradedAlgebra.finrank_cotangent_le_spanFinrank`: its dimension is then at most the
  minimal number of generators of the maximal ideal of `A_{A₊}`.
* `TauCeti.GradedAlgebra.exists_bijective_aeval_of_isRegularLocalRing`: a connected graded algebra
  over a field whose localization at the irrelevant ideal is a regular local ring of dimension
  `n` is a polynomial algebra on `n` homogeneous elements of positive degree.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), § 18.
* W. Bruns, J. Herzog, *Cohen–Macaulay Rings*, Cambridge University Press (1993), Sections 1.5
  and 2.2.
-/

public section

open DirectSum IsLocalRing Submodule

namespace TauCeti.GradedAlgebra

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- If `u * x` lies in the ideal spanned by elements `aᵢ ∈ A₊`, where `x ∈ A₊` and `u ∉ A₊`,
then `x` is a `k`-linear combination of the `aᵢ` modulo `A₊²`: write `u` and the coefficients
as scalars plus elements of `A₊`, and note that the constant term of `u` is nonzero. -/
private theorem mem_span_sup_of_mul_mem (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A)) {n : ℕ}
    {a : Fin n → A} (ha : ∀ i, a i ∈ HomogeneousIdeal.irrelevant 𝒜) {u x : A}
    (hu : u ∉ HomogeneousIdeal.irrelevant 𝒜) (hx : x ∈ HomogeneousIdeal.irrelevant 𝒜)
    (hux : u * x ∈ Ideal.span (Set.range a)) :
    x ∈ span k (Set.range a) ⊔
      ((HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ 2).restrictScalars k := by
  set m := (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  obtain ⟨r, hr⟩ := (mem_span_range_iff_exists_fun A).1 hux
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_irrelevant 𝒜 h𝒜 u
  choose d hd using fun i ↦ exists_sub_algebraMap_mem_irrelevant 𝒜 h𝒜 (r i)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hu (by simpa using hc)
  have hsq {y z : A} (hy : y ∈ m) (hz : z ∈ m) : y * z ∈ m ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hy hz
  -- `c x = ∑ dᵢ aᵢ + (∑ (rᵢ - dᵢ) aᵢ - (u - c) x)`, and the bracket lies in `A₊²`.
  have hx' : x = c⁻¹ • ∑ i, d i • a i +
      c⁻¹ • (∑ i, (r i - algebraMap k A (d i)) * a i - (u - algebraMap k A c) * x) := by
    rw [← smul_add, eq_inv_smul_iff₀ hc0]
    simp only [smul_eq_mul, Algebra.smul_def, sub_mul, Finset.sum_sub_distrib] at hr ⊢
    rw [hr]
    ring
  rw [hx']
  refine add_mem_sup (smul_mem _ _ (sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, rfl⟩)))
    (smul_mem _ _ (sub_mem (sum_mem fun i _ ↦ hsq (hd i) (ha i)) (hsq hc hx)))

/-- If the maximal ideal of the localization of a connected graded algebra at the irrelevant ideal
`A₊` is finitely generated, then there are `spanFinrank` many elements of `A₊` spanning `A₊`
modulo `A₊²` over `k`. -/
private theorem exists_irrelevant_le_span_sup (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (hfg : (maximalIdeal (Localization.AtPrime P)).FG) :
    ∃ a : Fin (maximalIdeal (Localization.AtPrime P)).spanFinrank → A,
      (∀ i, a i ∈ HomogeneousIdeal.irrelevant 𝒜) ∧
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.restrictScalars k ≤
        span k (Set.range a) ⊔ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ 2).restrictScalars k := by
  subst hP
  set m := (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  -- Generators of the maximal ideal of `A_{A₊}`, written as fractions `aᵢ / uᵢ`.
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  generalize spanFinrank (maximalIdeal (Localization.AtPrime m)) = n at hcard ⊢
  let e := s.equivFinOfCardEq hcard
  choose a u hau using fun i ↦
    IsLocalization.exists_mk'_eq m.primeCompl ((e.symm i : s) : Localization.AtPrime m)
  have hmax : maximalIdeal (Localization.AtPrime m) ≤
      (Ideal.span (Set.range a)).map (algebraMap A (Localization.AtPrime m)) := by
    rw [← hspan, span_le]
    intro y hy
    rw [show y = (e.symm (e ⟨y, hy⟩) : _) by rw [Equiv.symm_apply_apply], ← hau, SetLike.mem_coe,
      IsLocalization.mk'_mem_iff]
    exact Ideal.mem_map_of_mem _ (subset_span ⟨_, rfl⟩)
  have ha (i) : a i ∈ m := by
    have hy : (e.symm i : Localization.AtPrime m) ∈ maximalIdeal _ :=
      hspan ▸ subset_span (e.symm i).2
    rwa [← hau, IsLocalization.mk'_mem_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m] at hy
  refine ⟨a, ha, fun x hx ↦ ?_⟩
  have hx' : algebraMap A (Localization.AtPrime m) x ∈ maximalIdeal _ :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m x).2 hx
  obtain ⟨w, hw, hwx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff m.primeCompl _ _ x).1 (hmax hx')
  exact mem_span_sup_of_mul_mem 𝒜 h𝒜 ha hw hx hwx

/-- If the maximal ideal of the localization of a connected graded algebra at the irrelevant ideal
`A₊` is finitely generated, then the cotangent space `A₊ ⧸ A₊²` is spanned over `k` by
`spanFinrank` many elements. -/
private theorem exists_span_toCotangent_eq_top (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (hfg : (maximalIdeal (Localization.AtPrime P)).FG) :
    ∃ v : Fin (maximalIdeal (Localization.AtPrime P)).spanFinrank →
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent,
      span k (Set.range v) = ⊤ := by
  set m := (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  obtain ⟨a, ha, hle⟩ := exists_irrelevant_le_span_sup 𝒜 h𝒜 P hP hfg
  refine ⟨fun i ↦ m.toCotangent ⟨a i, ha i⟩, eq_top_iff.2 fun y _ ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
  -- Write `x = ∑ cᵢ aᵢ + w` with `w ∈ A₊²`.
  obtain ⟨z, hz, w, hw, hzw⟩ := mem_sup.1 (hle x.2)
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun k).1 hz
  have hx : m.toCotangent x = m.toCotangent (∑ i, c i • ⟨a i, ha i⟩) := by
    have hw' : w ∈ m ^ 2 := hw
    rw [Ideal.toCotangent_eq]
    convert hw' using 1
    rw [← hzw]
    simp
  rw [hx, map_sum]
  exact sum_mem fun i _ ↦ by
    rw [LinearMap.map_smul_of_tower]
    exact smul_mem _ _ (subset_span ⟨i, rfl⟩)

/-- If the maximal ideal of the localization of a connected graded algebra at the irrelevant ideal
`A₊` is finitely generated, then the cotangent space `A₊ ⧸ A₊²` is finite-dimensional over `k`. -/
theorem finite_cotangent_of_fg (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (hfg : (maximalIdeal (Localization.AtPrime P)).FG) :
    Module.Finite k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent := by
  classical
  obtain ⟨v, hv⟩ := exists_span_toCotangent_eq_top 𝒜 h𝒜 P hP hfg
  exact ⟨⟨Finset.univ.image v, by rwa [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩⟩

/-- If the maximal ideal of the localization of a connected graded algebra at the irrelevant ideal
`A₊` is finitely generated, then the dimension of the cotangent space `A₊ ⧸ A₊²` over `k` is at
most the minimal number of generators of that maximal ideal. -/
theorem finrank_cotangent_le_spanFinrank (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (hfg : (maximalIdeal (Localization.AtPrime P)).FG) :
    Module.finrank k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent ≤
      (maximalIdeal (Localization.AtPrime P)).spanFinrank := by
  obtain ⟨v, hv⟩ := exists_span_toCotangent_eq_top 𝒜 h𝒜 P hP hfg
  have := finrank_range_le_card (R := k) v
  rwa [Set.finrank, hv, finrank_top, Fintype.card_fin] at this

/-- **A connected graded algebra regular at its vertex is a polynomial algebra.** Let `A` be an
`ℕ`-graded algebra over a field `k` whose degree-zero part consists of the scalars. If its
localization at the irrelevant ideal `A₊` is a regular local ring of dimension `n`, then there are
`n` homogeneous elements of positive degree `f₁, …, fₙ` such that `k[X₁, …, Xₙ] → A`,
`Xᵢ ↦ fᵢ`, is an isomorphism.

The prime `P` is any prime equal to `A₊`, so that the statement applies to an ideal presented in
another form. -/
theorem exists_bijective_aeval_of_isRegularLocalRing (h𝒜 : ∀ x ∈ 𝒜 0, x ∈ (⊥ : Subalgebra k A))
    (P : Ideal A) [P.IsPrime] (hP : P = (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    [IsRegularLocalRing (Localization.AtPrime P)] {n : ℕ}
    (hn : ringKrullDim (Localization.AtPrime P) = n) :
    ∃ f : Fin n → A, (∀ i, ∃ d, 0 < d ∧ f i ∈ 𝒜 d) ∧
      Function.Bijective (MvPolynomial.aeval (R := k) f) := by
  have hfg := IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime P))
  have := finite_cotangent_of_fg 𝒜 h𝒜 P hP hfg
  -- Compare dimensions: `n ≤ dim A ≤ dim_k (A₊ ⧸ A₊²) ≤ spanFinrank 𝔪 = n`.
  have hnA : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [← hn, IsLocalization.AtPrime.ringKrullDim_eq_height P]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  have hcot : Module.finrank k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent ≤ n := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime P)
    rw [hn] at this
    exact (finrank_cotangent_le_spanFinrank 𝒜 h𝒜 P hP hfg).trans (by exact_mod_cast this.le)
  have hcotn : Module.finrank k (HomogeneousIdeal.irrelevant 𝒜).toIdeal.Cotangent = n :=
    le_antisymm hcot (by exact_mod_cast hnA.trans (ringKrullDim_le_finrank_cotangent 𝒜 h𝒜))
  have h := exists_bijective_aeval_of_finrank_cotangent_le 𝒜 h𝒜 (by rwa [hcotn])
  rwa [hcotn] at h

end TauCeti.GradedAlgebra
