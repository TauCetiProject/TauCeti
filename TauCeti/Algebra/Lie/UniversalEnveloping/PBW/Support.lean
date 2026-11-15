/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.Algebra.Lie.UniversalEnveloping.Subalgebra

/-!
# PBW coordinates of an enveloping subalgebra

Suppose an ordered basis of a Lie subalgebra occurs, in the same order, among the vectors of an
ambient basis. Its enveloping subalgebra is spanned by exactly those ambient PBW monomials whose
exponents are supported on the subalgebra indices. Thus membership can be checked by vanishing
of the other PBW coefficients, without choosing a complement or unfolding the enveloping map.

The statements work over a commutative ring whenever the specified bases exist. They require
neither finite-dimensionality nor a restriction on the characteristic.

The coordinate criterion uses Mathlib's `Module.Basis.mem_span_image` and
`Finsupp.mem_range_embDomain_iff`, together with the ordered PBW basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.2 and §17.4.
-/

public section

namespace LieSubalgebra

open TauCeti.UniversalEnvelopingAlgebra

universe u v w z

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {ι : Type w} {κ : Type z} [LinearOrder ι] [LinearOrder κ]

local notation "U" => UniversalEnvelopingAlgebra R L

variable (A : LieSubalgebra R L) (b : Module.Basis ι R A) (c : Module.Basis κ R L)
  (e : ι ↪o κ) (h : ∀ i, (b i : L) = c (e i))

include b h

/-- The enveloping subalgebra is spanned by the ambient PBW basis vectors whose exponent
support lies in the indices of the subalgebra basis. -/
theorem envelopingSubalgebra_eq_span_pbwBasis :
    (envelopingSubalgebra R A).toSubmodule =
      Submodule.span R (c.pbwBasis ''
        {n : κ →₀ ℕ | (n.support : Set κ) ⊆ Set.range e}) := by
  have hrange : LinearMap.range (TauCeti.UniversalEnvelopingAlgebra.map R A.incl).toLinearMap =
      Submodule.span R (Set.range fun n : ι →₀ ℕ ↦
        c.pbwBasis (n.embDomain e.toEmbedding)) := by
    rw [← Submodule.map_top, ← b.pbwBasis.span_eq, Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    ext x
    simp only [Set.mem_range, Function.comp_apply, AlgHom.coe_toLinearMap,
      b.map_pbwBasis c A.incl e h]
  have hindices : Set.range (Finsupp.embDomain e.toEmbedding : (ι →₀ ℕ) → κ →₀ ℕ) =
      {n : κ →₀ ℕ | (n.support : Set κ) ⊆ Set.range e} := by
    ext n
    exact Finsupp.mem_range_embDomain_iff e.toEmbedding n
  rw [envelopingSubalgebra_eq_range_map]
  -- Forgetting multiplication does not change the image of the algebra homomorphism.
  have hforget : (TauCeti.UniversalEnvelopingAlgebra.map R A.incl).range.toSubmodule =
      LinearMap.range (TauCeti.UniversalEnvelopingAlgebra.map R A.incl).toLinearMap := by
    ext x
    rfl
  rw [hforget, hrange, ← hindices, ← Set.range_comp]
  rfl

/-- An element belongs to the enveloping subalgebra exactly when each exponent with a nonzero
PBW coefficient is supported on the subalgebra indices. -/
theorem mem_envelopingSubalgebra_iff_pbw_support (x : U) :
    x ∈ envelopingSubalgebra R A ↔
      ∀ n ∈ (c.pbwBasis.repr x).support, (n.support : Set κ) ⊆ Set.range e := by
  rw [← Subalgebra.mem_toSubmodule, A.envelopingSubalgebra_eq_span_pbwBasis b c e h,
    c.pbwBasis.mem_span_image]
  rfl

/-- Membership in the enveloping subalgebra is equivalent to vanishing of every PBW
coefficient at an exponent using an index outside the subalgebra basis. -/
theorem mem_envelopingSubalgebra_iff_pbw_coeff_eq_zero (x : U) :
    x ∈ envelopingSubalgebra R A ↔
      ∀ n : κ →₀ ℕ, ¬ (n.support : Set κ) ⊆ Set.range e → c.pbwBasis.repr x n = 0 := by
  rw [A.mem_envelopingSubalgebra_iff_pbw_support b c e h]
  simp only [Finsupp.mem_support_iff]
  exact ⟨fun hx n hn ↦ not_not.mp (fun hn' ↦ hn (hx n hn')),
    fun hx n hn ↦ by_contra fun hn' ↦ hn (hx n hn')⟩

/-- A single ambient PBW monomial lies in the enveloping subalgebra exactly when it uses only
indices from the subalgebra basis. The coefficient ring must be nontrivial for this test. -/
theorem pbwBasis_mem_envelopingSubalgebra_iff [Nontrivial R] (n : κ →₀ ℕ) :
    c.pbwBasis n ∈ envelopingSubalgebra R A ↔ (n.support : Set κ) ⊆ Set.range e := by
  rw [← Subalgebra.mem_toSubmodule, A.envelopingSubalgebra_eq_span_pbwBasis b c e h]
  exact c.pbwBasis.self_mem_span_image

end LieSubalgebra
