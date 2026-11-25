/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.FiberBundle.Reduction

/-!
# Local triviality of reductions of principal bundles

Let `P → B` be a principal `G`-bundle, `H` a subgroup of `G`, and `S` a set of points of the total
space of `P` that the right action carries into itself by exactly the elements of `H`: for `p ∈ S`,
`p • g ∈ S` if and only if `g ∈ H`. Such a set is a candidate reduction of the structure group of
`P` to `H`. Over an open set `U` on which `S` has a continuous local section `τ`, it is trivial with
fibre `H`: a point `p` of `S` over `y ∈ U` goes to `(y, τ y⁻¹ p)`, where `τ y⁻¹ p` is the element of
`G` carrying `τ y` to `p` (`TauCeti.PrincipalBundle.division`), which lies in `H`. The
trivialization is equivariant for the right action of `H`
(`TauCeti.PrincipalBundle.exists_trivialization_of_continuousOn_section_mem`).

This is the local step of a reduction of structure group
(`Bundle.Trivialization.exists_trivialization_of_continuousOn_symm_mem`) applied to the
trivialization of the principal bundle given by the section `τ`
(`TauCeti.PrincipalBundle.trivializationOfSection`): for instance for the points of a `Spinᶜ`
structure whose frames are adapted to a unit section.

## Main results

* `TauCeti.PrincipalBundle.exists_trivialization_of_continuousOn_section_mem`: a set of points of
  a principal `G`-bundle stable under exactly a subgroup `H` is trivial with fibre `H`,
  equivariantly, over every open set on which it has a continuous section.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
-/

public section

open Bundle MulOpposite

namespace TauCeti.PrincipalBundle

variable {B G : Type*} [Group G] {P : B → Type*} [∀ b, MulAction Gᵐᵒᵖ (P b)]
  [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [PrincipalBundle G P] [IsTopologicalGroup G]

/-- **Local triviality of a reduction of a principal bundle.** A set `S` of points of a principal
`G`-bundle, carried into itself by exactly the elements of a subgroup `H`, is trivial with fibre `H`
over every nonempty open set `U` on which it has a continuous section `τ`, by a trivialization
equivariant for the right action of `H`. -/
theorem exists_trivialization_of_continuousOn_section_mem {H : Subgroup G}
    {S : Set (TotalSpace G P)} (hS : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H) {τ : ∀ b, P b}
    {U : Set B} (hτS : ∀ b ∈ U, (⟨b, τ b⟩ : TotalSpace G P) ∈ S) (hU : IsOpen U)
    (hτ : ContinuousOn (fun b ↦ TotalSpace.mk' G b (τ b)) U) {b : B} (hb : b ∈ U) :
    ∃ t : Trivialization H (fun p : S ↦ (p : TotalSpace G P).proj),
      t.baseSet = U ∧ ∀ (g : H) (p : S) (hgp : op (g : G) • (p : TotalSpace G P) ∈ S),
        (p : TotalSpace G P).proj ∈ U → t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g) :=
  (trivializationOfSection τ hU hτ).exists_trivialization_of_continuousOn_symm_mem (c := 1)
    (fun _ _ ↦ rfl)
    (fun g p _ ↦ by
      rw [trivializationOfSection_apply, trivializationOfSection_apply]
      exact division_smul_right _ _ _)
    hS (baseSet_trivializationOfSection τ hU hτ).ge
    (fun y hy ↦ by
      rw [trivializationOfSection_symm_apply, Pi.one_apply, op_one, one_smul]
      exact hτS y hy)
    hU continuousOn_const hb

end TauCeti.PrincipalBundle
