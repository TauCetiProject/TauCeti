/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Graded.Complement
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Free

/-!
# Homogeneous invariant coinvariant complements

For a finite linear group whose order is invertible in the coefficient field, the Hilbert ideal
in the symmetric algebra has a homogeneous invariant vector-space complement. Thus the
coinvariant algebra can be realized inside the symmetric algebra, compatibly with degree and
the group action. This complement is not asserted to be a subalgebra, nor to be canonical.
For a faithful pseudoreflection group on `V`, such a complement in `Sym(V*)` has dimension `|G|`.

These are coinvariant complements chosen by linear splitting and averaging; no inner product
or differential-operator characterization of harmonic polynomials is used.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Chapter V, § 5.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Chapter 3.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

variable {k G M : Type*} [Field k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)] [AddCommGroup M] [Module k M]

/-- The Hilbert ideal admits a homogeneous invariant vector-space complement. This holds
without finite-dimensionality or a pseudoreflection-generation hypothesis. -/
theorem exists_isCompl_symmetricAlgebraHilbertIdeal_isHomogeneous
    (ρ : Representation k G M) :
    ∃ H : Submodule k (SymmetricAlgebra k M),
      IsCompl (ρ.symmetricAlgebraHilbertIdeal.restrictScalars k) H ∧
      DirectSum.SetLike.IsHomogeneous (homogeneousSubmodule k M) H ∧
      ∀ g, Set.MapsTo (ρ.symmetricAlgebra g) H H := by
  apply ρ.symmetricAlgebra.exists_isCompl_isHomogeneous_of_invariant
    (homogeneousSubmodule k M)
    (fun g _ _ hp ↦ ρ.symmetricAlgebra_mem_homogeneousSubmodule g hp)
    (ρ.symmetricAlgebraHilbertIdeal.restrictScalars k)
    ρ.isHomogeneous_symmetricAlgebraHilbertIdeal
  intro g
  -- The induced algebra map fixes each invariant generator of the Hilbert ideal.
  have hle : ρ.symmetricAlgebraHilbertIdeal ≤
      ρ.symmetricAlgebraHilbertIdeal.comap (SymmetricAlgebra.map k (ρ g)) := by
    rw [ρ.symmetricAlgebraHilbertIdeal_eq_span]
    apply Ideal.span_le.2
    intro f hf
    simp only [SetLike.mem_coe, Ideal.mem_comap]
    rw [← symmetricAlgebra_apply, (ρ.mem_symmetricAlgebraInvariants f).1 hf.1 g]
    exact Ideal.subset_span hf
  intro f hf
  simpa only [SetLike.mem_coe, Submodule.restrictScalars_mem, Ideal.mem_comap,
    symmetricAlgebra_apply]
    using hle hf

/-- For a faithful pseudoreflection group of order invertible in the field, there is a
homogeneous invariant complement to the Hilbert ideal of `Sym(V*)`, of dimension `|G|`. -/
theorem exists_coinvariant_complement_dual_of_pseudoreflectionSubgroup_eq_top
    [FiniteDimensional k M] (ρ : Representation k G M)
    (hG : ρ.pseudoreflectionSubgroup = ⊤) (hρ : Function.Injective ρ) :
    ∃ H : Submodule k (SymmetricAlgebra k (Module.Dual k M)),
      IsCompl (ρ.dual.symmetricAlgebraHilbertIdeal.restrictScalars k) H ∧
      DirectSum.SetLike.IsHomogeneous (homogeneousSubmodule k (Module.Dual k M)) H ∧
      (∀ g, Set.MapsTo (ρ.dual.symmetricAlgebra g) H H) ∧ Module.finrank k H = Nat.card G := by
  obtain ⟨H, hH, hdeg, hstable⟩ :=
    ρ.dual.exists_isCompl_symmetricAlgebraHilbertIdeal_isHomogeneous
  refine ⟨H, hH, hdeg, hstable, ?_⟩
  -- Restriction of scalars does not change the quotient; use the explicit comparison.
  let e := ((ρ.dual.symmetricAlgebraHilbertIdeal.restrictScalars k).quotientEquivOfIsCompl H
    hH).symm.trans (Submodule.Quotient.restrictScalarsEquiv k ρ.dual.symmetricAlgebraHilbertIdeal)
  exact e.finrank_eq.trans
    (ρ.finrank_quotient_symmetricAlgebraHilbertIdeal_dual_of_pseudoreflectionSubgroup_eq_top hG hρ)

end Representation
