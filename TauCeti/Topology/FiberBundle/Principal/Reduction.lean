/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.Basic

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

This is the local step of a reduction of structure group, as for the orthonormal frames adapted to
a structure (`TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`), but
inside an arbitrary principal bundle rather than the orthonormal frame bundle: for instance the
points of a `Spinᶜ` structure whose frames are adapted to a unit section.

## Main results

* `TauCeti.PrincipalBundle.exists_trivialization_of_continuousOn_section_mem`: a set of points of
  a principal `G`-bundle stable under exactly a subgroup `H` is trivial with fibre `H`,
  equivariantly, over every open set on which it has a continuous section.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
-/

public section

noncomputable section

open Bundle MulOpposite Set

namespace TauCeti.PrincipalBundle

variable {B G : Type*} [Group G] {P : B → Type*} [∀ b, MulAction Gᵐᵒᵖ (P b)]
  {H : Subgroup G} {S : Set (TotalSpace G P)}
  (hS : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H)
  {τ : ∀ b, P b} {U : Set B} (hτS : ∀ b ∈ U, (⟨b, τ b⟩ : TotalSpace G P) ∈ S)

variable (H) in
open scoped Classical in
/-- An element of `G`, as an element of `H` when it is one, and `1` otherwise. -/
private def toSubgroup (g : G) : H :=
  if h : g ∈ H then ⟨g, h⟩ else 1

private theorem coe_toSubgroup {g : G} (hg : g ∈ H) : (toSubgroup H g : G) = g := by
  simp [toSubgroup, hg]

include hS hτS in
/-- Over `U`, `τ y • h` lies in `S` for `h ∈ H`. -/
private theorem smul_mem {y : B} (hy : y ∈ U) {g : G} (hg : g ∈ H) :
    (⟨y, op g • τ y⟩ : TotalSpace G P) ∈ S := by
  rw [← TotalSpace.smul_mk]
  exact (hS _ (hτS y hy) g).2 hg

open scoped Classical in
variable (τ) in
/-- The inverse of `reductionTrivialization`: `(y, h) ↦ τ y • h`, and the junk value `p₀`
off `S`. -/
private def reductionTrivializationInv (p₀ : S) (q : B × H) : S :=
  if h : (⟨q.1, op (q.2 : G) • τ q.1⟩ : TotalSpace G P) ∈ S then ⟨_, h⟩ else p₀

include hS hτS in
private theorem coe_reductionTrivializationInv (p₀ : S) {q : B × H} (hq : q.1 ∈ U) :
    (reductionTrivializationInv τ p₀ q : TotalSpace G P) = ⟨q.1, op (q.2 : G) • τ q.1⟩ := by
  rw [reductionTrivializationInv, dite_eq_left (smul_mem hS hτS hq q.2.property)]

variable [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [PrincipalBundle G P]

include hS hτS in
/-- Over `U`, the element carrying `τ y` to a point `p` of `S` over `y` lies in `H`. -/
private theorem division_mem {p : TotalSpace G P} (hp : p.proj ∈ U) (h : p ∈ S) :
    division G (τ p.proj) p.snd ∈ H := by
  rw [← hS _ (hτS _ hp), TotalSpace.smul_mk, smul_division]
  exact h

variable [IsTopologicalGroup G] (hU : IsOpen U)
  (hτ : ContinuousOn (fun b ↦ TotalSpace.mk' G b (τ b)) U)

/-- The trivialization of `S` over `U` with fibre `H` given by the local section `τ`: a point `p`
over `y` goes to `(y, τ y⁻¹ p)`. The point `p₀` of `S` is a junk value of the inverse off its
target. -/
private def reductionTrivialization (p₀ : S) :
    Trivialization H (fun p : S ↦ (p : TotalSpace G P).proj) where
  toFun p := (p.val.proj, toSubgroup H (division G (τ p.val.proj) p.val.snd))
  invFun := reductionTrivializationInv τ p₀
  source := {p | p.val.proj ∈ U}
  target := U ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q hq := by
    rw [mem_ofPred_eq, coe_reductionTrivializationInv hS hτS p₀ hq.1]
    exact hq.1
  left_inv' p hp := by
    apply Subtype.ext
    rw [coe_reductionTrivializationInv (q := (p.val.proj, _)) hS hτS p₀ hp,
      coe_toSubgroup (division_mem hS hτS hp p.property), smul_division]
  right_inv' := by
    rintro ⟨y, g⟩ hq
    rw [Prod.mk.injEq, coe_reductionTrivializationInv hS hτS p₀ hq.1]
    refine ⟨rfl, Subtype.ext ?_⟩
    simp only
    rw [division_eq_iff.2 rfl, coe_toSubgroup g.property]
  open_source := hU.preimage ((FiberBundle.continuous_proj G P).comp continuous_subtypeVal)
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    have hproj : Continuous fun p : S ↦ (p : TotalSpace G P).proj :=
      (FiberBundle.continuous_proj G P).comp continuous_subtypeVal
    refine hproj.continuousOn.prodMk (Topology.IsInducing.subtypeVal.continuousOn_iff.2
      (ContinuousOn.congr ?_ fun p hp ↦ coe_toSubgroup (division_mem hS hτS hp p.property)))
    exact ContinuousOn.division (f := fun p : S ↦ (p : TotalSpace G P).proj)
      (p := fun p ↦ τ (p : TotalSpace G P).proj) (q := fun p ↦ (p : TotalSpace G P).snd)
      (hτ.comp hproj.continuousOn fun _ hp ↦ hp) continuous_subtypeVal.continuousOn
  continuousOn_invFun := by
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (ContinuousOn.congr
      (f := fun q : B × H ↦ (⟨q.1, op (q.2 : G) • τ q.1⟩ : TotalSpace G P)) ?_
      fun q hq ↦ coe_reductionTrivializationInv hS hτS p₀ hq.1)
    exact ContinuousOn.totalSpaceMk_smul (f := Prod.fst) (p := fun q : B × H ↦ τ q.1)
      (hτ.comp continuousOn_fst fun _ hq ↦ hq.1)
      (continuous_subtypeVal.comp continuous_snd).continuousOn
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

private theorem reductionTrivialization_apply (p₀ p : S) :
    reductionTrivialization (H := H) hS hτS hU hτ p₀ p =
      (p.val.proj, toSubgroup H (division G (τ p.val.proj) p.val.snd)) :=
  rfl

include hS hU hτ hτS in
/-- **Local triviality of a reduction of a principal bundle.** A set `S` of points of a principal
`G`-bundle, carried into itself by exactly the elements of a subgroup `H`, is trivial with fibre `H`
over every nonempty open set `U` on which it has a continuous section `τ`, by a trivialization
equivariant for the right action of `H`. -/
theorem exists_trivialization_of_continuousOn_section_mem {b : B} (hb : b ∈ U) :
    ∃ t : Trivialization H (fun p : S ↦ (p : TotalSpace G P).proj),
      t.baseSet = U ∧ ∀ (g : H) (p : S) (hgp : op (g : G) • (p : TotalSpace G P) ∈ S),
        (p : TotalSpace G P).proj ∈ U → t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g) := by
  refine ⟨reductionTrivialization (H := H) (U := U) hS hτS hU hτ ⟨_, hτS b hb⟩, rfl,
    fun g p hgp hp ↦ ?_⟩
  have h₁ := division_mem hS hτS hp p.property
  have h₂ := division_mem (p := op (g : G) • (p : TotalSpace G P)) hS hτS hp hgp
  rw [reductionTrivialization_apply, reductionTrivialization_apply]
  refine Prod.ext rfl (Subtype.ext ?_)
  rw [Subgroup.coe_mul, coe_toSubgroup h₂, coe_toSubgroup h₁]
  exact division_smul_right _ _ _

end TauCeti.PrincipalBundle
