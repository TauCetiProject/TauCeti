/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Continuous.Intertwining

/-!
# Schur's lemma for continuous intertwiners

Schur's lemma has two halves. Between inequivalent irreducible representations every intertwiner
vanishes; and, over an algebraically closed field, every self-intertwiner of a finite-dimensional
irreducible representation is scalar. This file records both halves for Mathlib's bundled
continuous intertwining maps, which is the form the analytic theory uses.

No topology on the acting monoid and no invariant measure are involved: both halves are deduced
from Mathlib's algebraic Schur lemma (`Representation.IsIrreducible.bijective_or_eq_zero` and
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`) applied to the
underlying algebraic intertwiner.

The hypothesis of the vanishing half is inequivalence as *continuous* representations, which is
the weaker of the two hypotheses to discharge. `ContRepresentation.nonempty_equiv_iff` shows it is
no weaker in substance: for finite-dimensional Hausdorff representations over a complete
nontrivially normed field the two notions of equivalence agree, because every linear map out of a
finite-dimensional Hausdorff topological vector space is continuous.

## Main statements

* `ContRepresentation.eq_zero_of_isEmpty_equiv`: every continuous intertwiner between
  inequivalent irreducible finite-dimensional representations is zero.
* `ContRepresentation.exists_eq_smul_one_of_isIrreducible`: every continuous self-intertwiner of
  an irreducible finite-dimensional representation over an algebraically closed field is scalar.
* `ContRepresentation.eq_finrank_inv_mul_trace_smul_id_of_isIrreducible`: when the dimension is
  invertible in `𝕜` that scalar is the normalized trace `(finrank 𝕜 V)⁻¹ * trace f` of the
  intertwiner.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

namespace ContRepresentation

section Vanishing

variable {𝕜 G V W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W] [T2Space W]
  {π : ContRepresentation 𝕜 G V} {ρ : ContRepresentation 𝕜 G W}

/-- **Schur's lemma, vanishing half.** A continuous intertwiner between inequivalent irreducible
finite-dimensional Hausdorff continuous representations is zero.

Inequivalence is asked of the continuous representations, which by
`ContRepresentation.nonempty_equiv_iff` is the same condition as inequivalence of the underlying
algebraic representations. The field need not be algebraically closed. -/
theorem eq_zero_of_isEmpty_equiv (hπ : Representation.IsIrreducible π.toRepresentation)
    (hρ : Representation.IsIrreducible ρ.toRepresentation) (hne : IsEmpty (Equiv π ρ))
    (f : ContIntertwiningMap π ρ) :
    f = 0 := by
  have : IsEmpty (Representation.Equiv π.toRepresentation ρ.toRepresentation) :=
    ⟨fun φ ↦ hne.false (nonempty_equiv_iff.2 ⟨φ⟩).some⟩
  exact ContIntertwiningMap.toIntertwiningMap_injective (Subsingleton.elim _ _)

end Vanishing

section Scalar

variable {𝕜 G V : Type*} [Field 𝕜] [IsAlgClosed 𝕜] [Monoid G]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul 𝕜 V] [FiniteDimensional 𝕜 V]

variable (π : ContRepresentation 𝕜 G V)

/-- **Schur's lemma, scalar half.** Every continuous self-intertwiner of an irreducible
finite-dimensional representation over an algebraically closed field is a scalar multiple of the
identity. -/
theorem exists_eq_smul_one_of_isIrreducible
    (hirr : Representation.IsIrreducible π.toRepresentation) (f : ContIntertwiningMap π π) :
    ∃ c : 𝕜, f = c • 1 := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := π.toRepresentation)).2 f.toIntertwiningMap
  refine ⟨c, ContIntertwiningMap.ext <| ContinuousLinearMap.ext fun v ↦ ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one, ContIntertwiningMap.smul_apply,
    ContIntertwiningMap.one_apply] using congr($hc.symm v)

/-- **The Schur scalar is the normalized trace.** Taking traces pins down the scalar of
`exists_eq_smul_one_of_isIrreducible`: the underlying continuous linear map of a continuous
self-intertwiner `f` of an irreducible finite-dimensional representation over an algebraically
closed field is `(finrank 𝕜 V)⁻¹ * trace f` times the identity.

The dimension must be invertible in `𝕜`: when the characteristic of `𝕜` divides `finrank 𝕜 V`,
the scalar `(finrank 𝕜 V)⁻¹ * trace f` is zero and the statement fails. -/
theorem eq_finrank_inv_mul_trace_smul_id_of_isIrreducible
    (hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0)
    (hirr : Representation.IsIrreducible π.toRepresentation) (f : ContIntertwiningMap π π) :
    f.toContinuousLinearMap
      = ((Module.finrank 𝕜 V : 𝕜)⁻¹ *
          LinearMap.trace 𝕜 V (f.toContinuousLinearMap : V →ₗ[𝕜] V)) •
        ContinuousLinearMap.id 𝕜 V := by
  obtain ⟨c, rfl⟩ := π.exists_eq_smul_one_of_isIrreducible hirr f
  ext v
  simp [mul_comm c, inv_mul_cancel_left₀ hdim]

end Scalar

end ContRepresentation
