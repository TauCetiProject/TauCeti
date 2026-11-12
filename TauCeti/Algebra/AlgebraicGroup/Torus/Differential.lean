/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Differential

/-!
# Differentiated torus actions

A tangent vector coming from a split torus over a commutative ring has eigenspaces
spanning every rational representation. Over an algebraically closed field this applies
to every torus.
The representation can have arbitrary dimension, and the homomorphism from the torus
need not be a closed immersion.

The eigenspace decomposition is transported from
`DiagonalizableGroup.iSup_eigenspace_differential_eq_top` through a splitting isomorphism.
It applies in every characteristic, even when distinct characters have equal differentials.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.7.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 22.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

section Split

variable {k : Type u} [CommRing k] {T : FiniteTypeCommHopfAlgCat.{u, u} k}
variable {H : Type v} [CommRing H] [Bialgebra k H]
variable (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]

/-- A tangent vector coming from a split torus has eigenspaces spanning any rational
representation, without a dimension or characteristic restriction. -/
theorem splitTorusCommHopfAlgProperty.iSup_eigenspace_differential_eq_top
    (hT : splitTorusCommHopfAlgProperty k T) (f : H →ₐc[k] T)
    (d : Derivation k T (Bialgebra.CounitAlgebra k T k)) :
    ⨆ μ : k, Module.End.eigenspace
      (Comodule.differential (R := k) (H := H) (M := V) (derivationComp f d)) μ = ⊤ := by
  obtain ⟨n, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff k T).mp hT
  let e := _root_.CommHopfAlgCat.ofIso
    ((forget₂ (FiniteTypeCommHopfAlgCat k) (_root_.CommHopfAlgCat k)).mapIso i)
  have hd := derivationComp_derivationComp_eq_self_of_comp_eq_id
    e.toBialgHom e.symm.toBialgHom e.comp_symm d
  have h := DiagonalizableGroup.iSup_eigenspace_differential_eq_top V
    (e.symm.toBialgHom.comp f) (derivationComp e.toBialgHom d)
  simpa only [derivationComp_comp, LinearMap.comp_apply, hd] using h

end Split

variable {k : Type u} [Field k] {T : FiniteTypeCommHopfAlgCat.{u, u} k}
variable {H : Type v} [CommRing H] [Bialgebra k H]
variable (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V]

/-- Over an algebraically closed field, a tangent vector coming from any torus has
eigenspaces spanning every rational representation. -/
theorem torusCommHopfAlgProperty.iSup_eigenspace_differential_eq_top [IsAlgClosed k]
    (hT : torusCommHopfAlgProperty k T) (f : H →ₐc[k] T)
    (d : Derivation k T (Bialgebra.CounitAlgebra k T k)) :
    ⨆ μ : k, Module.End.eigenspace
      (Comodule.differential (R := k) (H := H) (M := V) (derivationComp f d)) μ = ⊤ :=
  (hT.split k T).iSup_eigenspace_differential_eq_top V f d

end TauCeti
