/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.DirectSum.Basis
public import TauCeti.LinearAlgebra.SymmetricAlgebra.DegreeFiltration

/-!
# Homogeneous bases of a symmetric algebra and the degree filtration

Let `c` be a basis of `SymmetricAlgebra R M` made of homogeneous elements, `c i` of degree
`deg i`; for instance the monomial basis `Module.Basis.symmetricAlgebra` induced by a basis of
`M`, with `deg` the total degree of the exponent
(`Module.Basis.symmetricAlgebra_mem_homogeneousSubmodule`). Such a basis is adapted to the degree
filtration: the `k`-th step of the degree filtration (the word filtration of the generators) is
spanned by the basis vectors of degree at most `k`
(`TauCeti.SymmetricAlgebra.wordFiltration_eq_span_basis_image`). This is the form consumed by the
coordinate criterion for total tensor filtrations, `TauCeti.mem_tensorFiltration_iff_of_basis`.

## Main results

* `TauCeti.SymmetricAlgebra.wordFiltration_eq_span_basis_image`: degree `k` is spanned by the
  homogeneous basis vectors of degree at most `k`.
-/

public section

namespace TauCeti.SymmetricAlgebra

open TauCeti.Algebra Submodule

universe u v

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type*} {c : Module.Basis ι R (_root_.SymmetricAlgebra R M)} {deg : ι → ℕ}

/-- **A homogeneous basis is adapted to the degree filtration**: if every basis vector `c i` is
homogeneous of degree `deg i`, then degree `k` of the symmetric algebra is spanned by the basis
vectors of degree at most `k`. -/
theorem wordFiltration_eq_span_basis_image (hc : ∀ i, c i ∈ homogeneousSubmodule R M (deg i))
    (k : ℕ) :
    wordFiltration (_root_.SymmetricAlgebra.ι R M) k = span R (c '' {i | deg i ≤ k}) := by
  refine le_antisymm (fun x hx ↦ ?_) (span_le.mpr ?_)
  · rw [Module.Basis.mem_span_image]
    intro i hi
    by_contra hik
    refine Finsupp.mem_support_iff.mp hi ?_
    rw [← c.repr_decompose_apply_of_mem hc x i,
      coe_decompose_eq_zero_of_mem_wordFiltration (not_le.mp hik) hx, map_zero, Finsupp.zero_apply]
  · rintro _ ⟨i, hi, rfl⟩
    exact wordFiltration_mono _ hi (range_pow_le_wordFiltration _ _ (hc i))

end TauCeti.SymmetricAlgebra
