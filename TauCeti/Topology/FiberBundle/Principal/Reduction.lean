/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.MapFiber
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

When such trivializations cover the base (`TauCeti.PrincipalBundle.IsLocallyTrivialReduction`),
the fibres of `S` form a principal `H`-bundle
(`TauCeti.PrincipalBundle.IsLocallyTrivialReduction.principalBundle`), with total space `S` and
fibres `TauCeti.MapFiber`; this holds in particular when `S` has a continuous local section near
every point (`TauCeti.PrincipalBundle.isLocallyTrivialReduction_of_forall_exists_section`).

## Main definitions

* `TauCeti.PrincipalBundle.reductionMulAction`: the right action of `H` on `S`.
* `TauCeti.PrincipalBundle.IsLocallyTrivialReduction`: every point of the base lies in the base
  set of an `H`-equivariant trivialization of `S`.
* `TauCeti.PrincipalBundle.IsLocallyTrivialReduction.fiberBundle`: the fibre bundle of `S`.

## Main results

* `TauCeti.PrincipalBundle.exists_trivialization_of_continuousOn_section_mem`: a set of points of
  a principal `G`-bundle stable under exactly a subgroup `H` is trivial with fibre `H`,
  equivariantly, over every open set on which it has a continuous section.
* `TauCeti.PrincipalBundle.IsLocallyTrivialReduction.principalBundle`: a locally trivial reduction
  is a principal `H`-bundle.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
-/

public section

open Bundle MulOpposite

namespace TauCeti.PrincipalBundle

variable {B G : Type*} [Group G] {P : B → Type*} [∀ b, MulAction Gᵐᵒᵖ (P b)]

section Exists

variable [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace (TotalSpace G P)]
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

end Exists

/-! ### The reduction as a principal bundle -/

section Reduction

variable {H : Subgroup G} {S : Set (TotalSpace G P)}

/-- The right action of a subgroup `H` on a set `S` of points of a principal `G`-bundle that `H`
carries into itself: the right action of `G` on the total space, restricted. -/
@[instance_reducible]
def reductionMulAction (hS : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H) : MulAction Hᵐᵒᵖ S where
  smul g p := ⟨op (g.unop : G) • (p : TotalSpace G P), (hS p p.property _).mpr g.unop.property⟩
  one_smul p := Subtype.ext (one_smul Gᵐᵒᵖ (p : TotalSpace G P))
  mul_smul g h p := Subtype.ext <| by
    change op ((g * h).unop : G) • (p : TotalSpace G P) =
      op (g.unop : G) • op (h.unop : G) • (p : TotalSpace G P)
    rw [unop_mul, Subgroup.coe_mul, op_mul, mul_smul]

/-- The action of `g ∈ H` on a point of `S` is that of `g` on the total space. -/
theorem coe_reductionMulAction_smul (hS : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H) (g : Hᵐᵒᵖ)
    (p : S) :
    letI := reductionMulAction hS
    ((g • p : S) : TotalSpace G P) = op (g.unop : G) • (p : TotalSpace G P) :=
  (rfl)

/-- The action of `H` on `S` preserves the base point. -/
theorem proj_reductionMulAction_smul (hS : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H) (g : Hᵐᵒᵖ)
    (p : S) :
    letI := reductionMulAction hS
    ((g • p : S) : TotalSpace G P).proj = (p : TotalSpace G P).proj :=
  (rfl)

variable [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace (TotalSpace G P)]

variable (H S) in
/-- A set `S` of points of a principal `G`-bundle is a *locally trivial reduction* to a subgroup
`H` when every point of the base lies in the base set of a trivialization of `S` with fibre `H`
that turns the action of `H` into right multiplication. -/
def IsLocallyTrivialReduction : Prop :=
  ∀ b : B, ∃ t : Trivialization H (fun p : S ↦ (p : TotalSpace G P).proj), b ∈ t.baseSet ∧
    ∀ (g : H) (p : S) (hgp : op (g : G) • (p : TotalSpace G P) ∈ S),
      (p : TotalSpace G P).proj ∈ t.baseSet → t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g)

/-- Unfolds `TauCeti.PrincipalBundle.IsLocallyTrivialReduction`. -/
theorem isLocallyTrivialReduction_iff : IsLocallyTrivialReduction H S ↔
    ∀ b : B, ∃ t : Trivialization H (fun p : S ↦ (p : TotalSpace G P).proj), b ∈ t.baseSet ∧
      ∀ (g : H) (p : S) (hgp : op (g : G) • (p : TotalSpace G P) ∈ S),
        (p : TotalSpace G P).proj ∈ t.baseSet → t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g) :=
  Iff.rfl

namespace IsLocallyTrivialReduction

variable (hS : IsLocallyTrivialReduction H S)

/-- The atlas of `S` given by the chosen equivariant trivializations of a locally trivial
reduction. -/
noncomputable def atlas : MapFiber.Atlas H (fun p : S ↦ (p : TotalSpace G P).proj) :=
  ⟨fun b ↦ (isLocallyTrivialReduction_iff.mp hS b).choose,
    fun b ↦ (isLocallyTrivialReduction_iff.mp hS b).choose_spec.1⟩

/-- The trivialization of the atlas at `b` is the chosen equivariant trivialization at `b`. -/
theorem atlas_trivAt (b : B) :
    hS.atlas.trivAt b = (isLocallyTrivialReduction_iff.mp hS b).choose :=
  (rfl)

/-- **A locally trivial reduction is a fibre bundle** with fibre `H`: the fibres of `S` over the
base, with the chosen trivializations as atlas. -/
@[instance_reducible]
noncomputable def fiberBundle : FiberBundle H (MapFiber fun p : S ↦ (p : TotalSpace G P).proj) :=
  hS.atlas.fiberBundle

/-- **A locally trivial reduction of a principal `G`-bundle to `H` is a principal `H`-bundle.** -/
theorem principalBundle (hSH : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H) :
    letI := hS.fiberBundle
    letI := reductionMulAction hSH
    letI := MapFiber.mulAction (proj := fun p : S ↦ (p : TotalSpace G P).proj)
      (M := Hᵐᵒᵖ) (proj_reductionMulAction_smul hSH)
    PrincipalBundle H (MapFiber fun p : S ↦ (p : TotalSpace G P).proj) :=
  letI := reductionMulAction hSH
  hS.atlas.principalBundle (proj_reductionMulAction_smul hSH)
    fun b p hp g ↦ congrArg Prod.snd ((isLocallyTrivialReduction_iff.mp hS b).choose_spec.2 g p
      ((hSH p p.property g).mpr g.property) hp)

end IsLocallyTrivialReduction

end Reduction

section Section

variable [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [PrincipalBundle G P] [IsTopologicalGroup G]
  {H : Subgroup G} {S : Set (TotalSpace G P)}

/-- **A set with continuous local sections is a locally trivial reduction.** If `S` is carried
into itself by exactly the elements of `H` and has a continuous section over an open
neighbourhood of every point of the base, it is a locally trivial reduction to `H`. -/
theorem isLocallyTrivialReduction_of_forall_exists_section
    (hS : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H)
    (hsec : ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧ ∃ τ : ∀ b, P b,
      (∀ y ∈ U, (⟨y, τ y⟩ : TotalSpace G P) ∈ S) ∧
        ContinuousOn (fun y ↦ TotalSpace.mk' G y (τ y)) U) :
    IsLocallyTrivialReduction H S := isLocallyTrivialReduction_iff.mpr fun b ↦ by
  obtain ⟨U, hU, hbU, τ, hτS, hτ⟩ := hsec b
  obtain ⟨t, ht, hteq⟩ := exists_trivialization_of_continuousOn_section_mem hS hτS hU hτ hbU
  exact ⟨t, ht ▸ hbU, fun g p hgp hp ↦ hteq g p hgp (ht ▸ hp)⟩

end Section

end TauCeti.PrincipalBundle
