/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Pow
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Isometry
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Shifts along Hilbert bases and the image of the Fredholm index

Let `b` and `c` be Hilbert bases of complete inner-product spaces `E` and `F`, and let `f` be an
injection of their index types that misses only finitely many indices. The isometry
`b i ↦ c (f i)` of `HilbertBasis.linearIsometryOfOrthonormal` is injective, and its range is the
orthogonal complement of the finitely many basis vectors `c j` with `j ∉ Set.range f`. So it is a
Fredholm operator of index `-#(Set.range f)ᶜ`. The unilateral shift `b n ↦ b (n + 1)` of a
Hilbert basis indexed by `ℕ` is the case of index `-1`.

On an infinite-dimensional space the index type of a Hilbert basis is infinite, so it is in
bijection with itself plus one point, and the corresponding shift has index `-1`. Its powers and
their adjoints realize every integer as the index of a Fredholm endomorphism, and composing with
one Fredholm operator `E → F` shifts these indices by a constant. So **if an infinite-dimensional
Hilbert space `E` admits any Fredholm operator to `F`, for instance a continuous linear
equivalence, then every integer is the index of a Fredholm operator `E → F`.** No separability is
assumed. For complex Hilbert spaces `E` and `F`, together with the norm-path classification
`ContinuousLinearMap.nonempty_path_iff_index_eq`, the index is then a bijection from the path
components of the Fredholm operators `E → F` onto `ℤ`.

The Fredholm and index computations for the shift, and the passage to every integer through powers
and adjoints, follow the forward shift on Hardy space in `TauCeti.Analysis.Fourier.Hardy.Index`,
which is the case `b = c = hardyBasis`, `f = Nat.succ` of the lemmas here.

## Main declarations

* `HilbertBasis.isFredholm_linearIsometryOfOrthonormal_comp`: the isometry `b i ↦ c (f i)` is
  Fredholm when `f` misses finitely many indices.
* `HilbertBasis.index_linearIsometryOfOrthonormal_comp`: its index is `-#(Set.range f)ᶜ`.
* `ContinuousLinearMap.IsFredholm.exists_isFredholm_index_eq`: if an infinite-dimensional Hilbert
  space `E` admits a Fredholm operator to `F`, every integer is the index of one.

## References

* D. S. Freed, *The Atiyah–Singer index theorem*, Bull. Amer. Math. Soc. 58 (2021), 517–566,
  display (3.13).
* H. B. Lawson, Jr., and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter III, §7.
-/

public section

noncomputable section

open Module

namespace HilbertBasis

variable {ι κ 𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) {f : ι → κ} (hf : Function.Injective f)

/-- The isometry `b i ↦ c (f i)` along an injection `f` of the index types of two Hilbert bases is
a Fredholm operator when `f` misses only finitely many indices. -/
theorem isFredholm_linearIsometryOfOrthonormal_comp (hfin : (Set.range f)ᶜ.Finite) :
    (b.linearIsometryOfOrthonormal (c.orthonormal.comp f hf)).toContinuousLinearMap.IsFredholm := by
  refine (b.linearIsometryOfOrthonormal _).isometry.isClosedEmbedding.isFredholm ?_
  rw [LinearIsometry.toLinearMap_toContinuousLinearMap,
    range_linearIsometryOfOrthonormal_comp b c hf]
  exact (Submodule.fg_span (hfin.image _)).cofg_of_isCompl
    (Submodule.isCompl_orthogonal_span_of_finite (hfin.image _))

omit [CompleteSpace E] in
/-- The isometry `b i ↦ c (f i)` along an injection `f` of the index types of two Hilbert bases
has index `-#(Set.range f)ᶜ` when `f` misses only finitely many indices: it is injective, and its
range is the orthogonal complement of the basis vectors `c j` with `j ∉ Set.range f`. -/
theorem index_linearIsometryOfOrthonormal_comp (hfin : (Set.range f)ᶜ.Finite) :
    (b.linearIsometryOfOrthonormal (c.orthonormal.comp f hf)).toContinuousLinearMap.index =
      -((Set.range f)ᶜ.ncard : ℤ) := by
  have hK : finrank 𝕜 (Submodule.span 𝕜 (c '' (Set.range f)ᶜ)) = (Set.range f)ᶜ.ncard := by
    have : Fintype ↥(Set.range f)ᶜ := hfin.fintype
    rw [Set.image_eq_range]
    refine (finrank_span_eq_card
      (c.orthonormal.linearIndependent.comp _ Subtype.val_injective)).trans ?_
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [ContinuousLinearMap.index_of_injective _ (b.linearIsometryOfOrthonormal _).injective,
    LinearIsometry.toLinearMap_toContinuousLinearMap, range_linearIsometryOfOrthonormal_comp b c hf,
    (Submodule.quotientEquivOfIsCompl _ _
      (Submodule.isCompl_orthogonal_span_of_finite (hfin.image _)).symm).finrank_eq, hK]

end HilbertBasis

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- An infinite-dimensional Hilbert space carries a Fredholm operator of index `-1`: the shift
along a bijection `Option ι ≃ ι` of the index type of a Hilbert basis with itself plus a point. -/
private theorem exists_isFredholm_index_eq_neg_one (hE : ¬FiniteDimensional 𝕜 E) :
    ∃ T : E →L[𝕜] E, T.IsFredholm ∧ T.index = -1 := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have hw : Infinite w := by
    refine not_finite_iff_infinite.1 fun _ ↦ hE ?_
    have := Fintype.ofFinite w
    exact Module.Finite.of_basis b.toOrthonormalBasis.toBasis
  obtain ⟨σ⟩ : Nonempty (Option w ≃ w) := Cardinal.eq.1 <| by
    rw [Cardinal.mk_option, Cardinal.add_one_eq (Cardinal.infinite_iff.1 hw)]
  have hf : Function.Injective (σ ∘ some) := σ.injective.comp (Option.some_injective _)
  -- The shift misses exactly the index `σ none`.
  have hcompl : (Set.range (σ ∘ some))ᶜ = {σ none} := by
    ext j
    obtain ⟨o, rfl⟩ := σ.surjective j
    cases o <;> simp
  have hfin : (Set.range (σ ∘ some))ᶜ.Finite := hcompl ▸ Set.finite_singleton _
  refine ⟨_, b.isFredholm_linearIsometryOfOrthonormal_comp b hf hfin, ?_⟩
  rw [b.index_linearIsometryOfOrthonormal_comp b hf hfin, hcompl, Set.ncard_singleton,
    Nat.cast_one]

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Every integer is a Fredholm index.** If the Hilbert space `E` is infinite-dimensional and
there is some Fredholm operator `E → F` (for instance a continuous linear equivalence, by
`ContinuousLinearEquiv.isFredholm`), then every integer is the index of a Fredholm operator
`E → F`. No separability is assumed. -/
theorem _root_.ContinuousLinearMap.IsFredholm.exists_isFredholm_index_eq {T₀ : E →L[𝕜] F}
    (hT₀ : T₀.IsFredholm) (hE : ¬FiniteDimensional 𝕜 E) (n : ℤ) :
    ∃ T : E →L[𝕜] F, T.IsFredholm ∧ T.index = n := by
  obtain ⟨S, hS, hSi⟩ := exists_isFredholm_index_eq_neg_one hE
  -- An endomorphism of any index `k` is a power of `S` or the adjoint of one.
  have hend (k : ℤ) : ∃ A : E →L[𝕜] E, A.IsFredholm ∧ A.index = k := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · refine ⟨ContinuousLinearMap.adjoint (S ^ m), (hS.pow m).adjoint, ?_⟩
      rw [ContinuousLinearMap.index_adjoint _ (hS.pow m),
        ContinuousLinearMap.index_pow _ hS, hSi, mul_neg_one, neg_neg]
    · exact ⟨S ^ m, hS.pow m, by rw [ContinuousLinearMap.index_pow _ hS, hSi, mul_neg_one]⟩
  obtain ⟨A, hA, hAi⟩ := hend (n - T₀.index)
  refine ⟨T₀.comp A, hT₀.comp hA, ?_⟩
  have h := hT₀.index_comp hA
  simp only [← ContinuousLinearMap.index_def] at h
  omega

end TauCeti
