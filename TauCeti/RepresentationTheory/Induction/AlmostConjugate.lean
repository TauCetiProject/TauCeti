/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.RepresentationTheory.Induction.Permutation
import TauCeti.RepresentationTheory.CharacterTable.FixedPointCount
import TauCeti.RepresentationTheory.Invariants

/-!
# Invariants of almost-conjugate subgroups

Two subgroups `H` and `K` of a finite group `G` are almost conjugate (`Subgroup.AlmostConjugate`)
when they meet every conjugacy class of `G` in the same number of elements. This file proves that,
over a field of characteristic zero, almost-conjugate subgroups have isomorphic spaces of
invariants in **every** representation of `G`:

`V ^ H ≃ₗ[k] V ^ K`.

The proof is Frobenius reciprocity. The `H`-invariants of `V` are the morphisms
`k[G ⧸ H] ⟶ V` (`TauCeti.quotientHomEquivInvariants`), and almost-conjugacy is equivalence of the
permutation representations `k[G ⧸ H]` and `k[G ⧸ K]`
(`TauCeti.almostConjugate_iff_nonempty_equiv_ofMulAction`), so the two spaces of
morphisms are isomorphic.

This is the representation-theoretic core of Sunada's construction of isospectral manifolds. If
`G` acts by isometries on a Riemannian manifold `X`, the eigenfunctions of the Laplacian on
`X ⧸ H` are the `H`-invariant eigenfunctions on `X`. Each eigenspace of the Laplacian on `X` is a
representation of `G`, so `X ⧸ H` and `X ⧸ K` have the same eigenvalues with the same
multiplicities. `Subgroup.AlmostConjugate.finrank_invariants_inf_eigenspace_eq` states this
equality of multiplicities for an operator commuting with the action. Only the dimensions agree:
the two spaces of invariants are in general different subspaces of the representation.

The coefficient field, the group and the representation share one universe, as the categorical
constructions behind `TauCeti.quotientHomEquivInvariants` (`Rep.indResHomEquiv` and
`Rep.trivialHomEquivInvariants`) require.

## Main statements

* `Subgroup.AlmostConjugate.nonempty_linearEquiv_invariants`: almost-conjugate subgroups have
  linearly equivalent invariants in every representation.
* `Subgroup.AlmostConjugate.finrank_invariants_eq`: the invariants have the same dimension.
* `Subgroup.AlmostConjugate.finrank_invariants_inf_eq`: the same holds for the invariants lying
  in any `G`-stable subspace.
* `Subgroup.AlmostConjugate.finrank_invariants_inf_eigenspace_eq`: for an operator commuting with
  the action, the spaces of `H`-fixed and `K`-fixed vectors in each eigenspace have the same
  dimension.

## References

* T. Sunada, *Riemannian coverings and isospectral manifolds*, Ann. of Math. **121** (1985),
  169–186.
* P. Bérard, *Transplantation et isospectralité. I*, Math. Ann. **292** (1992), 547–559,
  Theorem 17.
-/

public section

open CategoryTheory Module

universe u

namespace Subgroup.AlmostConjugate

variable {k : Type u} [Field k] [CharZero k] {G : Type u} [Group G] [Finite G] {H K : Subgroup G}
  {V : Type u} [AddCommGroup V] [Module k V]

/-- **Almost-conjugate subgroups have isomorphic invariants.** Over a field of characteristic zero,
if `H` and `K` are almost conjugate subgroups of a finite group `G`, then in every representation
`ρ` of `G` the `H`-invariants and the `K`-invariants are linearly equivalent. -/
theorem nonempty_linearEquiv_invariants (h : H.AlmostConjugate K) (ρ : Representation k G V) :
    Nonempty (Representation.invariants (ρ.comp H.subtype) ≃ₗ[k]
      Representation.invariants (ρ.comp K.subtype)) := by
  obtain ⟨e⟩ := (TauCeti.almostConjugate_iff_nonempty_equiv_ofMulAction k H K).1 h
  exact ⟨(TauCeti.quotientHomEquivInvariants k H (Rep.of ρ)).symm ≪≫ₗ
    Linear.homCongr k (Rep.mkIso e) (Iso.refl _) ≪≫ₗ
    TauCeti.quotientHomEquivInvariants k K (Rep.of ρ)⟩

/-- Almost-conjugate subgroups have invariants of the same dimension in every representation. -/
theorem finrank_invariants_eq (h : H.AlmostConjugate K) (ρ : Representation k G V) :
    finrank k (Representation.invariants (ρ.comp H.subtype)) =
      finrank k (Representation.invariants (ρ.comp K.subtype)) :=
  let ⟨e⟩ := h.nonempty_linearEquiv_invariants ρ
  e.finrank_eq

/-- Almost-conjugate subgroups have the same number of independent invariant vectors in every
`G`-stable subspace `W` of a representation. -/
theorem finrank_invariants_inf_eq (h : H.AlmostConjugate K) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    finrank k ↥(Representation.invariants (ρ.comp H.subtype) ⊓ W) =
      finrank k ↥(Representation.invariants (ρ.comp K.subtype) ⊓ W) := by
  rw [← Representation.map_subtype_invariants_subrepresentation (ρ.comp H.subtype) fun g ↦ hW g,
    ← Representation.map_subtype_invariants_subrepresentation (ρ.comp K.subtype) fun g ↦ hW g,
    Submodule.finrank_map_subtype_eq, Submodule.finrank_map_subtype_eq]
  -- Restricting to `W` and then to a subgroup `L` is restricting to `L` and then to `W`.
  have hres (L : Subgroup G) : (ρ.subrepresentation W hW).comp L.subtype =
      Representation.subrepresentation (ρ.comp L.subtype) W (fun g ↦ hW g) := _root_.rfl
  rw [← hres H, ← hres K]
  exact h.finrank_invariants_eq (ρ.subrepresentation W hW)

/-- **Equal multiplicities for almost-conjugate subgroups.** If a linear operator `T` commutes with
the action of `G` and `H`, `K` are almost conjugate, then the `H`-fixed vectors and the `K`-fixed
vectors in each eigenspace of `T` form subspaces of the same dimension. -/
theorem finrank_invariants_inf_eigenspace_eq (h : H.AlmostConjugate K) (ρ : Representation k G V)
    {T : End k V} (hT : ∀ g, Commute T (ρ g)) (μ : k) :
    finrank k ↥(Representation.invariants (ρ.comp H.subtype) ⊓ T.eigenspace μ) =
      finrank k ↥(Representation.invariants (ρ.comp K.subtype) ⊓ T.eigenspace μ) :=
  h.finrank_invariants_inf_eq ρ _ fun g _ hv ↦ End.mapsTo_genEigenspace_of_comm (hT g) μ 1 hv

end Subgroup.AlmostConjugate
