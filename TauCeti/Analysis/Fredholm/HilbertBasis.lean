/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Isometry
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Fredholm shifts along Hilbert bases

Let `b` and `c` be Hilbert bases of complete inner-product spaces `E` and `F`, and let `f` be an
injection of their index types that misses only finitely many indices. The isometry
`b i ↦ c (f i)` of `HilbertBasis.linearIsometryOfOrthonormal` is injective, and its range is the
orthogonal complement of the finitely many basis vectors `c j` with `j ∉ Set.range f`. So it is a
Fredholm operator of index `-#(Set.range f)ᶜ`. The unilateral shift `b n ↦ b (n + 1)` of a
Hilbert basis indexed by `ℕ` is the case of index `-1`; the forward shift on Hardy space in
`TauCeti.Analysis.Fourier.Hardy.Index` is the case `b = c = hardyBasis`, `f = Nat.succ`.

## Main declarations

* `HilbertBasis.isFredholm_linearIsometryOfOrthonormal_comp`: the isometry `b i ↦ c (f i)` is
  Fredholm when `f` misses finitely many indices.
* `HilbertBasis.index_linearIsometryOfOrthonormal_comp`: its index is `-#(Set.range f)ᶜ`.

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
