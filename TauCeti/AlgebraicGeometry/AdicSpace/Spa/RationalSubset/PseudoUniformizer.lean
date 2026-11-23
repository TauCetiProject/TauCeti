/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis

/-!
# Normalising rational subsets with a pseudouniformiser

Let `A` be a commutative ring with a topology in which multiplication is separately continuous,
containing a pseudouniformiser `ϖ`, and let `A⁺` be an open subring of `A`. Every rational subset
`R(T₀/s₀)` of `Spa(A, A⁺)` with open numerator ideal admits a presentation of the normalised shape

```text
R(T₀/s₀) = R((T ∪ {ϖ ^ N}) / s)   with T ⊆ A⁺, ϖ ^ N ∈ A⁺, s ∈ A⁺.
```

Two elementary steps produce this presentation without needing quasi-compactness or a Huber-ring
structure (Scholze, *Perfectoid spaces*, Remark 2.8 and proof of Theorem 6.3):
1. **Clearing denominators into `A⁺`** (`exists_subset_rationalSubset_eq_of_isPseudoUniformizer`):
   because `A⁺` is open and `ϖ` is topologically nilpotent, a common power `ϖ ^ M` multiplies all
   of `T₀` and `s₀` into `A⁺`; because `ϖ ^ M` is a unit, scaling by it leaves both `R(T₀/s₀)` and
   its numerator ideal unchanged (`rationalSubset_image_mul_right`).
2. **Inserting a high power of `ϖ`**
   (`exists_rationalSubset_eq_insert_pow_of_isPseudoUniformizer`): the open numerator ideal `T · A`
   contains a unit power `ϖ ^ k` and therefore equals `⊤`, giving a finite linear combination
   `1 = ∑ t ∈ T, c t * t`. Choosing `N` large enough that `ϖ ^ N ∈ A⁺` and `c t * ϖ ^ N ∈ A⁺` for
   every `t ∈ T` forces `v(ϖ ^ N) = v(∑ t ∈ T, (c t * ϖ ^ N) * t) ≤ v(s)` at every point
   `v ∈ R(T/s)`, so adjoining `ϖ ^ N` leaves `R(T/s)` unchanged
   (`rationalSubset_insert_of_forall_vle`) while making the numerator set contain the unit `ϖ ^ N`.

Conversely, any presentation `R((T ∪ {ϖ ^ N}) / s)` contains the unit `ϖ ^ N` among its numerators
and therefore belongs to `spaRationalFamily A⁺`
(`val_preimage_rationalSubset_mem_spaRationalFamily_of_isUnit_mem`). Thus `spaRationalFamily A⁺` is
*equal* to the family of normalised presentations (`spaRationalFamily_eq_of_isPseudoUniformizer`),
which consequently forms a topological basis of `Spa(A, A⁺)` when `A` is a Huber ring
(`isTopologicalBasis_insert_pow_of_isPseudoUniformizer`).

Neither `IsRingOfIntegralElements A⁺` nor `ϖ ∈ A⁺` is assumed: openness of `A⁺` alone puts high
powers of `ϖ` inside `A⁺`.

## Main results

* `TauCeti.ValuationSpectrum.exists_subset_rationalSubset_eq_of_isPseudoUniformizer` : scaling any
  pair `(T₀, s₀)` into an open subring `A⁺` by a power of `ϖ` without changing `R(T₀/s₀)` or the
  numerator ideal.
* `TauCeti.ValuationSpectrum.exists_rationalSubset_eq_insert_pow_of_isPseudoUniformizer` and
  `exists_eq_val_preimage_rationalSubset_insert_pow_of_isPseudoUniformizer` : every rational subset
  with open numerator ideal has a presentation `R((T ∪ {ϖ ^ N}) / s)` with `T ⊆ A⁺`, `ϖ ^ N ∈ A⁺`,
  and `s ∈ A⁺`.
* `TauCeti.ValuationSpectrum.spaRationalFamily_eq_of_isPseudoUniformizer` and
  `TauCeti.ValuationSpectrum.isTopologicalBasis_insert_pow_of_isPseudoUniformizer` : exact
  identification of `spaRationalFamily A⁺` with the normalised presentations, and the resulting
  topological basis of `Spa(A, A⁺)`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Remark 2.8 and proof of Theorem 6.3.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.29 and Theorem 7.35.
-/

public section

namespace TauCeti.ValuationSpectrum

open Filter Set Topology _root_.TopologicalSpace TauCeti.Huber

section SeparatelyContinuousMul

variable {A : Type*} [CommRing A] [TopologicalSpace A] [SeparatelyContinuousMul A]

open scoped Classical in
/-- **Scaling a presentation into an open subring by a power of a pseudouniformiser.** If `A⁺` is
an open subring of `A` and `ϖ` is a pseudouniformiser, any `(T₀, s₀)` can be scaled by a unit power
`ϖ ^ M` to `(T, s)` with `T ⊆ A⁺` and `s ∈ A⁺`, preserving both `rationalSubset A⁺` and the ideal
spanned by the numerators. -/
theorem exists_subset_rationalSubset_eq_of_isPseudoUniformizer {Aplus : Subring A}
    (hAplus : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    (T₀ : Finset A) (s₀ : A) :
    ∃ (T : Finset A) (s : A), (T : Set A) ⊆ Aplus ∧ s ∈ Aplus ∧
      Ideal.span (T : Set A) = Ideal.span (T₀ : Set A) ∧
      rationalSubset Aplus T₀ s₀ = rationalSubset Aplus T s := by
  have hev : ∀ᶠ m : ℕ in atTop, ∀ a ∈ (insert s₀ T₀ : Finset A), a * ϖ ^ m ∈ Aplus :=
    (eventually_all_finite (insert s₀ T₀).finite_toSet).mpr fun a _ ↦
      eventually_mul_pow_mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent hAplus a
  obtain ⟨M, hM⟩ := hev.exists
  have hu : IsUnit (ϖ ^ M) := hϖ.isUnit.pow M
  refine ⟨T₀.image (· * ϖ ^ M), s₀ * ϖ ^ M, ?_, hM s₀ (Finset.mem_insert_self s₀ T₀), ?_,
    (rationalSubset_image_mul_right Aplus T₀ s₀ (ϖ ^ M) hu).symm⟩
  · intro x hx
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    exact hM t₀ (Finset.mem_insert_of_mem ht₀)
  · open scoped Pointwise in
    have himg : ((T₀.image (· * ϖ ^ M) : Finset A) : Set A) = (ϖ ^ M) • (T₀ : Set A) := by
      ext x
      simp [Set.mem_smul_set, mul_comm]
    simpa only [himg, Ideal.submodule_span_eq] using
      Submodule.span_smul_eq_of_isUnit (T₀ : Set A) (ϖ ^ M) hu

open scoped Classical in
/-- **Normalised presentation of a rational subset with a pseudouniformiser.** Over a commutative
ring with separately continuous multiplication, a pseudouniformiser `ϖ`, and an open subring `A⁺`,
every rational subset `R(T₀/s₀)` with open numerator ideal equals `R((T ∪ {ϖ ^ N}) / s)` for some
finite `T ⊆ A⁺`, `s ∈ A⁺`, and `N : ℕ` with `ϖ ^ N ∈ A⁺`. -/
theorem exists_rationalSubset_eq_insert_pow_of_isPseudoUniformizer {Aplus : Subring A}
    (hAplus : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {T₀ : Finset A} {s₀ : A} (hT₀ : IsOpen (Ideal.span (T₀ : Set A) : Set A)) :
    ∃ (T : Finset A) (s : A) (N : ℕ),
      (T : Set A) ⊆ Aplus ∧ ϖ ^ N ∈ Aplus ∧ s ∈ Aplus ∧
      rationalSubset Aplus T₀ s₀ = rationalSubset Aplus (insert (ϖ ^ N) T) s := by
  obtain ⟨T, s, hTsub, hs, hspan, heq⟩ :=
    exists_subset_rationalSubset_eq_of_isPseudoUniformizer hAplus hϖ T₀ s₀
  have hTopen : IsOpen (Ideal.span (T : Set A) : Set A) := hspan.symm ▸ hT₀
  obtain ⟨k, hk⟩ :=
    hϖ.isTopologicallyNilpotent.exists_pow_mem_of_mem_nhds (hTopen.mem_nhds (Ideal.zero_mem _))
  have htop : Ideal.span (T : Set A) = ⊤ := Ideal.eq_top_of_isUnit_mem _ hk (hϖ.isUnit.pow k)
  have h1 : (1 : A) ∈ Submodule.span A (T : Set A) := by
    rw [Ideal.submodule_span_eq, htop]
    exact Submodule.mem_top
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h1
  have hϖev : ∀ᶠ N : ℕ in atTop, ϖ ^ N ∈ Aplus := by
    simpa only [one_mul] using
      eventually_mul_pow_mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent hAplus 1
  have hcev : ∀ᶠ N : ℕ in atTop, ∀ t ∈ T, c t * ϖ ^ N ∈ Aplus :=
    (eventually_all_finite T.finite_toSet).mpr fun t _ ↦
      eventually_mul_pow_mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent hAplus (c t)
  obtain ⟨N, hϖN, hcN⟩ := (hϖev.and hcev).exists
  have hsum : ∑ t ∈ T, c t * ϖ ^ N * t = ϖ ^ N := by
    calc ∑ t ∈ T, c t * ϖ ^ N * t
        = (∑ t ∈ T, c t * t) * ϖ ^ N := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ ↦ by ring
      _ = 1 * ϖ ^ N := by simpa only [smul_eq_mul] using congrArg (· * ϖ ^ N) hc
      _ = ϖ ^ N := one_mul _
  refine ⟨T, s, N, hTsub, hϖN, hs, heq.trans ?_⟩
  refine (rationalSubset_insert_of_forall_vle Aplus T s (ϖ ^ N) fun v hv ↦ ?_).symm
  have hvspa : v ∈ spa Aplus := rationalSubset_subset_spa Aplus T s hv
  refine (valuation_le_iff v (ϖ ^ N) s).mp ?_
  rw [← hsum]
  refine v.valuation.map_sum_le fun t ht ↦ ?_
  calc v.valuation (c t * ϖ ^ N * t)
      = v.valuation (c t * ϖ ^ N) * v.valuation t := map_mul _ _ _
    _ ≤ 1 * v.valuation s := mul_le_mul' (valuation_le_one_of_mem_spa hvspa (hcN t ht))
        ((valuation_le_iff v t s).mpr (((mem_rationalSubset_iff Aplus T s v).mp hv).2.1 t ht))
    _ = v.valuation s := one_mul _

open scoped Classical in
/-- **Every member of `spaRationalFamily` has a normalised presentation `R((T ∪ {ϖ ^ N}) / s)`**
with `T ⊆ A⁺`, `ϖ ^ N ∈ A⁺`, and `s ∈ A⁺`. -/
theorem exists_eq_val_preimage_rationalSubset_insert_pow_of_isPseudoUniformizer {Aplus : Subring A}
    (hAplus : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) :
    ∃ (T : Finset A) (s : A) (N : ℕ),
      (T : Set A) ⊆ Aplus ∧ ϖ ^ N ∈ Aplus ∧ s ∈ Aplus ∧
      U = Subtype.val ⁻¹' rationalSubset Aplus (insert (ϖ ^ N) T) s := by
  obtain ⟨T₀, s₀, hT₀, rfl⟩ := mem_spaRationalFamily_iff.mp hU
  obtain ⟨T, s, N, hT, hϖN, hs, heq⟩ :=
    exists_rationalSubset_eq_insert_pow_of_isPseudoUniformizer hAplus hϖ hT₀
  exact ⟨T, s, N, hT, hϖN, hs, congrArg (Subtype.val ⁻¹' ·) heq⟩

open scoped Classical in
/-- **Exact characterisation of `spaRationalFamily` via normalised presentations.** When `A` has a
pseudouniformiser `ϖ` and `A⁺` is open, `spaRationalFamily A⁺` consists precisely of the subsets
`R((T ∪ {ϖ ^ N}) / s)` with `T ⊆ A⁺`, `ϖ ^ N ∈ A⁺`, and `s ∈ A⁺`: the reverse inclusion holds
because the unit `ϖ ^ N` makes the numerator ideal equal to `⊤`. -/
theorem spaRationalFamily_eq_of_isPseudoUniformizer {Aplus : Subring A}
    (hAplus : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    spaRationalFamily Aplus =
      {U : Set (spa Aplus) | ∃ (T : Finset A) (s : A) (N : ℕ),
        (T : Set A) ⊆ Aplus ∧ ϖ ^ N ∈ Aplus ∧ s ∈ Aplus ∧
        U = Subtype.val ⁻¹' rationalSubset Aplus (insert (ϖ ^ N) T) s} := by
  ext U
  refine ⟨exists_eq_val_preimage_rationalSubset_insert_pow_of_isPseudoUniformizer hAplus hϖ, ?_⟩
  rintro ⟨T, s, N, -, -, -, rfl⟩
  exact val_preimage_rationalSubset_mem_spaRationalFamily_of_isUnit_mem Aplus
    (Finset.mem_insert_self (ϖ ^ N) T) (hϖ.isUnit.pow N)

end SeparatelyContinuousMul

section Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

open scoped Classical in
/-- **Normalised rational subsets `R((T ∪ {ϖ ^ N}) / s)` form a topological basis of `Spa(A, A⁺)`.**
-/
theorem isTopologicalBasis_insert_pow_of_isPseudoUniformizer {Aplus : Subring A}
    (hAplus : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    IsTopologicalBasis {U : Set (spa Aplus) | ∃ (T : Finset A) (s : A) (N : ℕ),
      (T : Set A) ⊆ Aplus ∧ ϖ ^ N ∈ Aplus ∧ s ∈ Aplus ∧
      U = Subtype.val ⁻¹' rationalSubset Aplus (insert (ϖ ^ N) T) s} :=
  spaRationalFamily_eq_of_isPseudoUniformizer hAplus hϖ ▸ isTopologicalBasis_spaRationalFamily Aplus

end Huber

end TauCeti.ValuationSpectrum
