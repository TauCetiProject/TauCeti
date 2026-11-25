/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Local triviality of reductions of structure group

Let `e` be a trivialization of a map `proj : Z → B` with model fibre a topological group `G`,
equivariant for a right action of `G` on `Z` preserving `proj`: `e (z • g) = (proj z, (e z).2 * g)`
over the base set of `e`. Let `H` be a subgroup of `G` and `S` a set of points of `Z` that the
right action carries into itself by exactly the elements of `H`: for `p ∈ S`, `p • g ∈ S` if and
only if `g ∈ H`. Such a set is a candidate reduction of the structure group to `H`.

If on an open subset `U` of the base set of `e` the points `e.symm (y, c y)` lie in `S` for a
continuous correction `c : B → G`, then `S` is trivial over `U` with fibre `H`, equivariantly for
the right action of `H`
(`Bundle.Trivialization.exists_trivialization_of_continuousOn_symm_mem`): a point `p` of `S` over
`y` goes to `(y, (c y)⁻¹ * (e p).2)`, and its second coordinate lies in `H`.

This is the local step shared by reductions of the orthonormal frame bundle
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_of_continuousOn_smul_mem`) and of principal
bundles (`TauCeti.PrincipalBundle.exists_trivialization_of_continuousOn_section_mem`).

## Main results

* `Bundle.Trivialization.exists_trivialization_of_continuousOn_symm_mem`: a set stable under
  exactly a subgroup `H` is trivial with fibre `H`, equivariantly, wherever an equivariant
  trivialization can be corrected into it continuously.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (reduction of the structure group).
-/

public section

noncomputable section

open MulOpposite Set

namespace Bundle.Trivialization

variable {B Z G : Type*} [Group G] {H : Subgroup G}

variable (H) in
open scoped Classical in
/-- An element of `G`, as an element of `H` when it is one, and `1` otherwise. -/
private def toSubgroup (g : G) : H :=
  if h : g ∈ H then ⟨g, h⟩ else 1

private theorem coe_toSubgroup {g : G} (hg : g ∈ H) : (toSubgroup H g : G) = g := by
  simp [toSubgroup, hg]

variable [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace G] [SMul Gᵐᵒᵖ Z]
  {proj : Z → B} {e : Trivialization G proj} {S : Set Z} {U : Set B} {c : B → G}

variable (e c) in
open scoped Classical in
/-- The inverse map of `reductionTrivialization`: it sends `(y, h)` to `e.symm (y, c y * h)` when
this lies in `S`, and to `p₀` otherwise. -/
private def reductionTrivializationInv (p₀ : S) (q : B × H) : S :=
  if h : e.toOpenPartialHomeomorph.symm (q.1, c q.1 * q.2) ∈ S then ⟨_, h⟩ else p₀

variable (hproj : ∀ (g : G) (p : Z), proj (op g • p) = proj p)
  (he : ∀ (g : G) (p : Z), proj p ∈ e.baseSet → (e (op g • p)).2 = (e p).2 * g)
  (hS : ∀ p ∈ S, ∀ g : G, op g • p ∈ S ↔ g ∈ H) (hUe : U ⊆ e.baseSet)
  (hcS : ∀ y ∈ U, e.toOpenPartialHomeomorph.symm (y, c y) ∈ S)

include hproj he hS hUe hcS

/-- Over `U`, the fibre coordinate of a point of `S`, multiplied by the inverse correction, lies in
`H`. -/
private theorem inv_mul_mem {p : Z} (hp : proj p ∈ U) (h : p ∈ S) :
    (c (proj p))⁻¹ * (e p).2 ∈ H := by
  rw [← hS _ (hcS _ hp), e.op_smul_symm hproj he (hUe hp), mul_inv_cancel_left]
  rwa [e.symm_apply_mk_proj (e.mem_source.2 (hUe hp))]

/-- Over `U`, the inverse of `e` at the correction times an element of `H` lies in `S`. -/
private theorem symm_mul_mem {y : B} (hy : y ∈ U) {g : G} (hg : g ∈ H) :
    e.toOpenPartialHomeomorph.symm (y, c y * g) ∈ S := by
  rw [← e.op_smul_symm hproj he (hUe hy)]
  exact (hS _ (hcS y hy) g).2 hg

private theorem coe_reductionTrivializationInv (p₀ : S) {q : B × H} (hq : q.1 ∈ U) :
    (reductionTrivializationInv e c p₀ q : Z) =
      e.toOpenPartialHomeomorph.symm (q.1, c q.1 * q.2) := by
  rw [reductionTrivializationInv,
    dite_eq_left (symm_mul_mem hproj he hS hUe hcS hq q.2.property)]

variable [IsTopologicalGroup G] (hU : IsOpen U) (hc : ContinuousOn c U)

variable (U) in
/-- The trivialization of `S` over `U` with fibre `H`: a point `p` over `y` goes to
`(y, (c y)⁻¹ * (e p).2)`. The point `p₀` of `S` is a junk value of the inverse off its target. -/
private def reductionTrivialization (p₀ : S) : Trivialization H (fun p : S ↦ proj p) where
  toFun p := (proj p, toSubgroup H ((c (proj p))⁻¹ * (e p).2))
  invFun := reductionTrivializationInv e c p₀
  source := {p | proj p ∈ U}
  target := U ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' q hq := by
    rw [mem_ofPred_eq, coe_reductionTrivializationInv hproj he hS hUe hcS p₀ hq.1,
      e.proj_symm_apply' (hUe hq.1)]
    exact hq.1
  left_inv' p hp := by
    apply Subtype.ext
    rw [coe_reductionTrivializationInv (q := (proj p, _)) hproj he hS hUe hcS p₀ hp,
      coe_toSubgroup (inv_mul_mem hproj he hS hUe hcS hp p.property), mul_inv_cancel_left]
    exact e.symm_apply_mk_proj (e.mem_source.2 (hUe hp))
  right_inv' := by
    rintro ⟨y, g⟩ hq
    rw [Prod.mk.injEq, coe_reductionTrivializationInv hproj he hS hUe hcS p₀ hq.1,
      e.proj_symm_apply' (hUe hq.1), e.apply_symm_apply' (hUe hq.1), inv_mul_cancel_left]
    exact ⟨rfl, Subtype.ext (coe_toSubgroup g.property)⟩
  open_source := (e.isOpen_preimage hU hUe).preimage continuous_subtypeVal
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := by
    have hproj' : ContinuousOn (fun p : S ↦ proj p) {p | proj p ∈ U} :=
      e.continuousOn_proj.comp continuous_subtypeVal.continuousOn
        fun _ hp ↦ e.mem_source.2 (hUe hp)
    refine hproj'.prodMk (Topology.IsInducing.subtypeVal.continuousOn_iff.2
      (ContinuousOn.congr ?_ fun p hp ↦ coe_toSubgroup (inv_mul_mem hproj he hS hUe hcS hp
        p.property)))
    exact ((hc.comp hproj' fun _ hp ↦ hp).inv).mul (continuous_snd.comp_continuousOn
      (e.continuousOn_toFun.comp continuous_subtypeVal.continuousOn
        fun _ hp ↦ e.mem_source.2 (hUe hp)))
  continuousOn_invFun := by
    refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 (ContinuousOn.congr
      (f := fun q : B × H ↦ e.toOpenPartialHomeomorph.symm (q.1, c q.1 * q.2)) ?_
      fun q hq ↦ coe_reductionTrivializationInv hproj he hS hUe hcS p₀ hq.1)
    refine e.toOpenPartialHomeomorph.continuousOn_symm.comp (continuousOn_fst.prodMk ?_)
      fun _ hq ↦ e.mem_target.2 (hUe hq.1)
    exact (hc.comp continuousOn_fst mapsTo_fst_prod).mul
      (continuous_subtypeVal.comp continuous_snd).continuousOn
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

private theorem reductionTrivialization_apply (p₀ p : S) :
    reductionTrivialization U hproj he hS hUe hcS hU hc p₀ p =
      (proj p, toSubgroup H ((c (proj p))⁻¹ * (e p).2)) :=
  rfl

include hU hc in
/-- **Local triviality of a reduction of structure group.** Let `e` be a trivialization with model
fibre a topological group `G`, equivariant for a right action of `G` preserving `proj`, and let `S`
be carried into itself by exactly the elements of a subgroup `H`. If over an open subset `U` of
the base set of `e` the points `e.symm (y, c y)` lie in `S` for a continuous `c : B → G`, then `S`
is trivial over `U` with fibre `H`, by a trivialization equivariant for the right action of `H`. -/
theorem exists_trivialization_of_continuousOn_symm_mem {x : B} (hx : x ∈ U) :
    ∃ t : Trivialization H (fun p : S ↦ proj p),
      t.baseSet = U ∧ ∀ (g : H) (p : S) (hgp : op (g : G) • (p : Z) ∈ S),
        proj p ∈ U → t ⟨_, hgp⟩ = ((t p).1, (t p).2 * g) := by
  refine ⟨reductionTrivialization U hproj he hS hUe hcS hU hc ⟨_, hcS x hx⟩, rfl,
    fun g p hgp hp ↦ ?_⟩
  have h₁ := inv_mul_mem hproj he hS hUe hcS hp p.property
  have h₂ := inv_mul_mem hproj he hS hUe hcS ((hproj _ _).symm ▸ hp) hgp
  rw [reductionTrivialization_apply, reductionTrivialization_apply]
  refine Prod.ext (hproj _ _) (Subtype.ext ?_)
  rw [Subgroup.coe_mul, coe_toSubgroup h₂, coe_toSubgroup h₁, he _ _ (hUe hp), hproj, mul_assoc]

end Bundle.Trivialization
