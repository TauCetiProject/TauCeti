/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible

/-!
# Schur's lemma on the module underlying an irreducible representation

Over an algebraically closed field, the self-intertwiners of a finite-dimensional irreducible
representation are exactly the scalars.  Mathlib states this as bijectivity of the algebra map
`k → Representation.IntertwiningMap ρ ρ`, in
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`.

A self-intertwiner is, however, usually met as a linear map on the underlying module together with
the equivariance equation `f (ρ g v) = ρ g (f v)` it satisfies -- that is the shape in which one
operator is compared with another, or produced by averaging, or read off a form.  This file records
Schur's lemma in that shape: such a map is a scalar multiple of the identity.  Both hypotheses are
needed for the scalar to exist: algebraic closedness supplies an eigenvalue, and finite
dimensionality is what makes the endomorphism algebra integral over `k`.

## Main statements

* `Representation.IsIrreducible.exists_eq_smul_id_of_comm`: a linear map commuting with a
  finite-dimensional irreducible action over an algebraically closed field is a scalar multiple of
  the identity.
-/

public section

namespace Representation.IsIrreducible

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **Schur's lemma on the underlying module.** A linear map commuting with a finite-dimensional
irreducible action over an algebraically closed field is a scalar multiple of the identity.

The scalar is unique, since the identity is nonzero on a nonzero space, so this pins the
commutant of an irreducible action down to `k`. -/
theorem exists_eq_smul_id_of_comm (ρ : Representation k G V) [ρ.IsIrreducible]
    [FiniteDimensional k V] (f : V →ₗ[k] V) (hf : ∀ (g : G) (v : V), f (ρ g v) = ρ g (f v)) :
    ∃ c : k, f = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 (f.intertwiningMap_of_isIntertwiningMap ρ ρ hf)
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  simpa using (congrArg (fun q : Representation.IntertwiningMap ρ ρ => q v) hc).symm

end Representation.IsIrreducible
