/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.RepresentationTheory.Subrepresentation.Eigenvector
public import TauCeti.RepresentationTheory.SymmetricPower

/-!
# Symmetric powers of semisimple representations of commutative monoids

A finite-dimensional semisimple representation of a commutative monoid over an algebraically
closed field has a basis of common eigenvectors
(`Representation.exists_basis_forall_apply_eq_smul`).
Such a basis of `V` induces a basis of the symmetric power `Sym^m V` whose vectors are again
common eigenvectors (`Module.Basis.map_symmetricPower_of_apply`), and a representation spanned by
common eigenvectors is semisimple (`Representation.isSemisimpleRepresentation_of_span_eq_top`).
Hence the symmetric powers of such a representation are semisimple.

For example, the Weil group `W_ℂ = ℂˣ` of `ℂ` (`TauCeti.ClassFieldTheory.WeilGroupComplex`) is
commutative and `ℂ` is algebraically closed, so the symmetric powers of a finite-dimensional
semisimple complex representation of `W_ℂ` are semisimple; for a representation of dimension `n`,
`Sym^m` has dimension `binom(n + m - 1, m)` (`SymmetricPower.finrank_eq_choose`).

## Main results

* `Representation.isSemisimpleRepresentation_symmetricPower`: the symmetric powers of a
  finite-dimensional semisimple representation of a commutative monoid over an algebraically
  closed field are semisimple.
-/

public section

open scoped TensorProduct

namespace Representation

open Module

variable {k : Type} {G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) [IsMulCommutative G] [IsAlgClosed k] [FiniteDimensional k V]

/-- **Symmetric powers of semisimple representations of commutative monoids are semisimple**,
over an algebraically closed field and in finite dimension: an eigenbasis of `V` induces an
eigenbasis of `Sym^m V`. -/
instance isSemisimpleRepresentation_symmetricPower [ρ.IsSemisimpleRepresentation] (m : ℕ) :
    IsSemisimpleRepresentation (k := k) (G := G) (V := Sym[k]^m V) (ρ.symmetricPower m) := by
  obtain ⟨s, b, hb⟩ := exists_basis_forall_apply_eq_smul ρ
  refine isSemisimpleRepresentation_of_span_eq_top (ρ.symmetricPower m)
    (S := Set.range (b.symmetricPower m)) ?_ (b.symmetricPower m).span_eq
  rintro _ ⟨t, rfl⟩ g
  choose c hc using fun i ↦ hb i g
  rw [symmetricPower_apply]
  exact ⟨_, Basis.map_symmetricPower_of_apply b (ρ g) c hc t⟩

end Representation
