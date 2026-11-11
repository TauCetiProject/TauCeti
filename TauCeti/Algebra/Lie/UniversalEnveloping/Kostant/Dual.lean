/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Dual
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Antipode
public import TauCeti.LinearAlgebra.Dual.Lattice

/-!
# Integral duals of Kostant-stable lattices

If a submodule of a rational representation is preserved by the Kostant integral
form, its integral dual is preserved by the contragredient representation. The
reason is integral stability of the antipode, not just stability under the Lie
algebra: root divided powers and Cartan binomials must all preserve the lattice.

The statement applies both to an arbitrary enveloping-algebra representation and
to the native dual Lie module. If the original submodule is a full lattice, its
integral dual is a full lattice by `Submodule.isLattice_dualLattice`; its freeness
and finite generation follow over the integers. Thus dualizing supplies another
admissible integral module without choosing a bilinear form or identifying the
representation with its dual. This is useful when building integral matrix
representations together with their contragredients.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The proof uses the existing `AlgHom.hopfDual` and
`TauCeti.UniversalEnvelopingAlgebra.antipode_mem_kostantForm` constructions.
-/

public section

namespace AlgHom

variable {L V ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [AddCommGroup V] [Module ℚ V]

/-- The integral dual of a Kostant-stable submodule is stable under the Hopf
contragredient representation. No full-lattice or finite-dimensionality
hypothesis is needed for stability itself. -/
theorem hopfDual_kostantForm_apply_mem_dualLattice
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (e : ι → L) (h : κ → L) (N : Submodule ℤ V)
    (hN : ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm e h,
      ∀ v ∈ N, ρ u v ∈ N)
    (u : _root_.UniversalEnvelopingAlgebra ℚ L)
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm e h)
    {φ : Module.Dual ℚ V} (hφ : φ ∈ N.dualLattice ℚ) :
    ρ.hopfDual u φ ∈ N.dualLattice ℚ := by
  rw [Submodule.mem_dualLattice]
  intro v hv
  rw [hopfDual_apply]
  exact (Submodule.mem_dualLattice N φ).mp hφ _
    (hN _ (TauCeti.UniversalEnvelopingAlgebra.antipode_mem_kostantForm e h hu) v hv)

end AlgHom

namespace UniversalEnvelopingAlgebra

open TauCeti.UniversalEnvelopingAlgebra

variable {L V ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [AddCommGroup V] [Module ℚ V] [LieRingModule L V] [LieModule ℚ L V]

/-- The usual dual Lie module has a Kostant-stable integral dual whenever the
original module has a Kostant-stable integral submodule. -/
theorem representation_dual_apply_mem_dualLattice (e : ι → L) (h : κ → L)
    (N : Submodule ℤ V)
    (hN : ∀ u ∈ kostantForm e h, ∀ v ∈ N, representation ℚ L V u v ∈ N)
    (u : UniversalEnvelopingAlgebra ℚ L) (hu : u ∈ kostantForm e h)
    {φ : Module.Dual ℚ V} (hφ : φ ∈ N.dualLattice ℚ) :
    representation ℚ L (Module.Dual ℚ V) u φ ∈ N.dualLattice ℚ := by
  rw [representation_dual]
  exact (representation ℚ L V).hopfDual_kostantForm_apply_mem_dualLattice e h N hN u hu hφ

end UniversalEnvelopingAlgebra
