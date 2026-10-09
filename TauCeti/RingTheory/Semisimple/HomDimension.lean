/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.Schur
import TauCeti.LinearAlgebra.Pi

/-!
# Symmetry of hom-space dimensions for semisimple modules

For finite-dimensional semisimple modules `M` and `N` over a `k`-algebra `A`, the spaces
`Hom_A(M, N)` and `Hom_A(N, M)` have the same dimension over `k`. No splitting-field hypothesis
is needed: each pair of isomorphic simple constituents contributes the dimension of its
endomorphism division algebra, rather than necessarily one.

This comparison lets one compute maps into a one-dimensional character by instead counting
its occurrences in the source. In particular, it is the semisimple comparison used when reading
degree-two local Galois cohomology through Tate duality.

## Main results

* `TauCeti.finrank_linearMap_comm_of_isSemisimpleModule`: hom-space dimension is symmetric for
  finite-dimensional semisimple modules.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §2 (simple constituents and
  multiplicities).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.3.1)
  (the semisimple comparison in the local Euler characteristic).
-/

public section

namespace TauCeti

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- Hom-space dimension is symmetric between finite-dimensional semisimple modules over an
arbitrary field. The algebra itself need not be semisimple or finite-dimensional. -/
theorem finrank_linearMap_comm_of_isSemisimpleModule
    (M N : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [FiniteDimensional k M] [FiniteDimensional k N]
    [IsSemisimpleModule A M] [IsSemisimpleModule A N] :
    Module.finrank k (M →ₗ[A] N) = Module.finrank k (N →ₗ[A] M) := by
  classical
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  obtain ⟨m, S, eM, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M
  obtain ⟨n, T, eN, hT⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A N
  let _ (i : Fin m) : IsSimpleModule A (S i) := hS i
  let _ (j : Fin n) : IsSimpleModule A (T j) := hT j
  let _ (i : Fin m) : FiniteDimensional k (S i) :=
    Module.Finite.of_injective ((S i).subtype.restrictScalars k) Subtype.val_injective
  let _ (j : Fin n) : FiniteDimensional k (T j) :=
    Module.Finite.of_injective ((T j).subtype.restrictScalars k) Subtype.val_injective
  let epM := eM.trans DFinsupp.linearEquivFunOnFintype
  let epN := eN.trans DFinsupp.linearEquivFunOnFintype
  rw [(LinearEquiv.congrLeft N k epM).finrank_eq, (homCongrRight k epN).finrank_eq,
    (LinearEquiv.congrLeft M k epN).finrank_eq, (homCongrRight k epM).finrank_eq,
    finrank_linearMap_pi_eq_sum, finrank_linearMap_pi_eq_sum, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦
    finrank_linearMap_comm_of_isSimpleModule (S i) (T j)

end TauCeti
