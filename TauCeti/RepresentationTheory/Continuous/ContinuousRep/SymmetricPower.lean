/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.Topology.Algebra.Module.Multilinear.ModuleTopology
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.RepresentationTheory.SymmetricPower

/-!
# Symmetric powers of continuous representations

Let `ρ` be a jointly continuous representation of a topological monoid `Γ` on a finite free
module `M` over a topological commutative ring `A`, with its module topology. Then the action
`g ↦ Sym^d (ρ g)` on the symmetric power `Sym[A]^d M`, with its module topology, is again jointly
continuous (`TauCeti.ContinuousRep.symmetricPower`).

The input is that every multilinear map out of a finite free module with its module topology is
continuous (`IsModuleTopology.continuous_multilinearMap`): in a basis `b`, it is the finite sum
`∑ r, (∏ k, b.repr (x k) (r k)) • f (b ∘ r)` of products of continuous coordinates. The basis
vectors of `Sym[A]^d M` induced by `b` are pure symmetric tensors `⨂ₛ k, b (r k)`, whose orbits
`g ↦ ⨂ₛ k, ρ g (b (r k))` are continuous, and orbits of a spanning family suffice for joint
continuity.

## Main definitions

* `TauCeti.ContinuousRep.symmetricPower`: the `d`-th symmetric power of a continuous
  representation on a finite free module.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {Γ M : Type*} {A : Type} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Free A M] [Module.Finite A M] (d : ℕ) [TopologicalSpace (Sym[A]^d M)]
  [IsModuleTopology A (Sym[A]^d M)]

/-- The action on the `d`-th symmetric power of a finite free module is jointly continuous for the
module topology on `Sym[A]^d M`. -/
private theorem continuous_symmetricPower_action (ρ : ContinuousRep Γ A M) :
    Continuous fun p : Γ × Sym[A]^d M ↦ ρ.toRepresentation.symmetricPower d p.1 p.2 := by
  classical
  let b := Free.chooseBasis A M
  -- the pure tensors of basis vectors span the symmetric power
  have hspan : Submodule.span A
      (Set.range fun r : Fin d → Free.ChooseBasisIndex A M ↦ ⨂ₛ[A] k, b (r k)) = ⊤ := by
    refine eq_top_iff.mpr ((b.symmetricPower d).span_eq.symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨s, rfl⟩
    obtain ⟨r, rfl⟩ := Sym.ofFn_surjective s
    exact ⟨r, by rw [Basis.symmetricPower_apply, SymmetricPower.tprodOfSym_ofFn]⟩
  have : IsModuleTopology A (Sym[A]^d M) := ‹_›
  have := IsModuleTopology.toContinuousAdd A (Sym[A]^d M)
  refine (IsModuleTopology.continuous_linearMap_apply_iff_of_span_eq_top
    (ρ.toRepresentation.symmetricPower d) hspan).2 fun r ↦ ?_
  have htprod : Continuous (SymmetricPower.tprod A (ι := Fin d) (M := M)) :=
    IsModuleTopology.continuous_multilinearMap _
  refine (htprod.comp (continuous_pi fun k ↦ ρ.continuous_orbit (b (r k)))).congr fun g ↦ ?_
  simp

/-- **The `d`-th symmetric power of a continuous representation** on a finite free module:
`Γ` acts on `Sym[A]^d M` by `Sym^d (ρ g)`, jointly continuously for the module topology on
`Sym[A]^d M`. -/
noncomputable def symmetricPower (ρ : ContinuousRep Γ A M) : ContinuousRep Γ A (Sym[A]^d M) where
  toRepresentation := ρ.toRepresentation.symmetricPower d
  continuous_action := continuous_symmetricPower_action d ρ

/-- The underlying representation of the symmetric power. -/
theorem toRepresentation_symmetricPower (ρ : ContinuousRep Γ A M) :
    (ρ.symmetricPower d).toRepresentation = ρ.toRepresentation.symmetricPower d :=
  (rfl)

/-- The symmetric power acts by the symmetric powers of the original operators. -/
@[simp]
theorem symmetricPower_apply (ρ : ContinuousRep Γ A M) (g : Γ) :
    ρ.symmetricPower d g = SymmetricPower.map (ι := Fin d) (ρ g) :=
  ρ.toRepresentation.symmetricPower_apply d g

end TauCeti.ContinuousRep
