/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.Topology.Algebra.Module.Multilinear.ModuleTopology
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations
public import TauCeti.RepresentationTheory.SymmetricPower

/-!
# Symmetric powers of continuous representations

Let `ρ` be a jointly continuous representation of a topological monoid `Γ` on a finite
module `M` over a topological commutative ring `A`, with its module topology. Then the action
`g ↦ Sym^d (ρ g)` on the symmetric power `Sym[A]^d M`, with its module topology, is again jointly
continuous (`TauCeti.ContinuousRep.symmetricPower`).

The input is that every multilinear map out of finite modules with their module topologies is
continuous (`IsModuleTopology.continuous_multilinearMap`). For a finite generating family `s` of
`M`, the pure symmetric tensors `⨂ₛ k, s (r k)` span `Sym[A]^d M`, their orbits
`g ↦ ⨂ₛ k, ρ g (s (r k))` are therefore continuous, and orbits of a finite spanning family suffice
for joint continuity.

## Main definitions

* `TauCeti.ContinuousRep.symmetricPower`: the `d`-th symmetric power of a continuous
  representation on a finite module.

## Main results

* `TauCeti.ContinuousRep.res_symmetricPower`: restriction commutes with symmetric powers.
* `TauCeti.ContinuousRep.isSemisimpleRepresentation_symmetricPower`: the underlying
  representation of `ρ.symmetricPower d` is semisimple whenever the symmetric power of the
  underlying representation of `ρ` is.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {Γ M : Type*} {A : Type} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] (d : ℕ) [TopologicalSpace (Sym[A]^d M)]
  [IsModuleTopology A (Sym[A]^d M)]

/-- The action on the `d`-th symmetric power of a finite module is jointly continuous for the
module topology on `Sym[A]^d M`. -/
private theorem continuous_symmetricPower_action (ρ : ContinuousRep Γ A M) :
    Continuous fun p : Γ × Sym[A]^d M ↦ ρ.toRepresentation.symmetricPower d p.1 p.2 := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have := IsModuleTopology.toContinuousAdd A (Sym[A]^d M)
  refine (IsModuleTopology.continuous_linearMap_apply_iff_of_span_eq_top
    (ρ.toRepresentation.symmetricPower d)
    (SymmetricPower.span_tprod_comp_eq_top_of_span_eq_top (ι := Fin d) hs)).2 fun r ↦ ?_
  have htprod : Continuous (SymmetricPower.tprod A (ι := Fin d) (M := M)) :=
    IsModuleTopology.continuous_multilinearMap _
  refine (htprod.comp (continuous_pi fun k ↦ ρ.continuous_orbit (s (r k)))).congr fun g ↦ ?_
  simp

/-- **The `d`-th symmetric power of a continuous representation** on a finite module:
`Γ` acts on `Sym[A]^d M` by `Sym^d (ρ g)`, jointly continuously for the module topology on
`Sym[A]^d M`. -/
noncomputable def symmetricPower (ρ : ContinuousRep Γ A M) : ContinuousRep Γ A (Sym[A]^d M) where
  toRepresentation := ρ.toRepresentation.symmetricPower d
  continuous_action := continuous_symmetricPower_action d ρ

/-- The underlying representation of the symmetric power. -/
@[simp]
theorem toRepresentation_symmetricPower (ρ : ContinuousRep Γ A M) :
    (ρ.symmetricPower d).toRepresentation = ρ.toRepresentation.symmetricPower d :=
  (rfl)

/-- The symmetric power acts by the symmetric powers of the original operators. -/
@[simp]
theorem symmetricPower_apply (ρ : ContinuousRep Γ A M) (g : Γ) :
    ρ.symmetricPower d g = SymmetricPower.map (ι := Fin d) (ρ g) :=
  ρ.toRepresentation.symmetricPower_apply d g

/-- Restriction commutes with symmetric powers. -/
@[simp]
theorem res_symmetricPower {Γ' : Type*} [Monoid Γ'] [TopologicalSpace Γ']
    (ρ : ContinuousRep Γ A M) (φ : Γ' →ₜ* Γ) :
    (ρ.symmetricPower d).res φ = (ρ.res φ).symmetricPower d :=
  ext fun _ _ ↦ by simp

section Semisimple

variable {k : Type} {V : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsModuleTopology k V] [FiniteDimensional k V]
  [TopologicalSpace (Sym[k]^d V)] [IsModuleTopology k (Sym[k]^d V)]

/-- The underlying representation of `ρ.symmetricPower d` is semisimple whenever
`Sym^d` of the underlying representation of `ρ` is. -/
instance isSemisimpleRepresentation_symmetricPower (ρ : ContinuousRep Γ k V)
    [(ρ.toRepresentation.symmetricPower d).IsSemisimpleRepresentation] :
    (ρ.symmetricPower d).toRepresentation.IsSemisimpleRepresentation := by
  rw [toRepresentation_symmetricPower]
  infer_instance

end Semisimple

end TauCeti.ContinuousRep
