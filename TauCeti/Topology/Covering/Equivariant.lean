/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Topology.IsLocalHomeomorph

/-!
# Recovering an equivariant space by pulling back its orbit space

Suppose `p : X → Y` is equivariant for actions of `G` and `β : Y → Z` is a quotient
covering by `G`. If `f : X/G → Z` is the descent of `β ∘ p`, then
`x ↦ (p x, [x])` identifies `X` with the literal fibre product `Y ×_Z (X/G)`.
Its topology is the inherited product and subtype topology. The inverse chooses a
representative of an orbit and translates it to the prescribed point of `Y`; freeness
on `Y` makes the result independent of that choice.

This comparison applies to families with nontrivial fibre monodromy: pulling back a
quotient family through the base covering recovers the upstairs family.

## References

* A. Hatcher, *Algebraic Topology*, §1.3 (quotient coverings and their pullbacks).
-/

public section

open Function Set Topology

namespace MulActionHom

variable {G X Y Z : Type*} [Group G] [MulAction G X] [MulAction G Y]
  (p : X →[G] Y) (β : Y → Z)
  (f : MulAction.orbitRel.Quotient G X → Z)
  (hf : ∀ x, f (Quotient.mk _ x) = β (p x))

/-- The canonical map to the pullback of the descended projection through the base map. -/
def orbitRelQuotientPullback : X → β.Pullback f :=
  fun x ↦ ⟨(p x, Quotient.mk _ x), (hf x).symm⟩

/-- The two coordinates of the canonical comparison are the projection and the orbit class. -/
@[simp] theorem orbitRelQuotientPullback_val (x : X) :
    (p.orbitRelQuotientPullback β f hf x).1 = (p x, Quotient.mk _ x) := (rfl)

/-- A quotient covering of the base makes the canonical comparison bijective. -/
theorem bijective_orbitRelQuotientPullback [TopologicalSpace Y] [TopologicalSpace Z]
    (hβ : IsQuotientCoveringMap β G) : Bijective (p.orbitRelQuotientPullback β f hf) := by
  have := hβ.isCancelSMul
  constructor
  · intro a b hab
    have hp : p a = p b := congrArg (fun w ↦ w.1.1) hab
    obtain ⟨g, hg⟩ := Quotient.exact (congrArg (fun w ↦ w.1.2) hab)
    have hg1 : g = 1 := by
      apply isCancelSMul_iff_eq_one_of_smul_eq.mp ‹IsCancelSMul G Y› g (p b)
      exact (p.map_smul g b).symm.trans ((congrArg p hg).trans hp)
    simpa [hg1] using hg.symm
  · rintro ⟨⟨y, q⟩, hq⟩
    induction q using Quotient.inductionOn with | h x =>
      obtain ⟨g, hg⟩ := hβ.apply_eq_iff_mem_orbit.1 (hq.trans (hf x))
      refine ⟨g • x, Subtype.ext (Prod.ext ?_ ?_)⟩
      · exact (p.map_smul g x).trans hg
      · exact MulAction.orbitRel.Quotient.quotient_smul_eq

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

omit [TopologicalSpace Z] in
/-- The canonical pullback comparison is continuous for the inherited subtype topology. -/
theorem continuous_orbitRelQuotientPullback (hp : Continuous p) :
    Continuous (p.orbitRelQuotientPullback β f hf) :=
  (hp.prodMk continuous_quot_mk).subtype_mk _

variable [ContinuousConstSMul G X]

/-- An equivariant map into the source of a quotient covering pulls back disjoint
neighbourhoods, so its own orbit projection is a quotient covering. -/
theorem isQuotientCoveringMap_orbitRelQuotientMk (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G X)) G where
  __ := isQuotientMap_quot_mk
  apply_eq_iff_mem_orbit := Quotient.eq
  disjoint x := by
    obtain ⟨U, hU, hdisj⟩ := hβ.disjoint (p x)
    refine ⟨p ⁻¹' U, hp.continuousAt.preimage_mem_nhds hU, fun g hg ↦ ?_⟩
    apply hdisj g
    obtain ⟨_, ⟨a, ha, rfl⟩, hga⟩ := hg
    exact ⟨p (g • a), ⟨p a, ha, (p.map_smul g a).symm⟩, hga⟩

/-- Pulling the descended projection back through the base quotient covering recovers
the original equivariant space. No local triviality of `p` is required. -/
noncomputable def orbitRelQuotientPullbackHomeomorph (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) : X ≃ₜ β.Pullback f :=
  ((p.isQuotientCoveringMap_orbitRelQuotientMk β hp hβ).isLocalHomeomorph.of_comp
    (f := p.orbitRelQuotientPullback β f hf) (g := Pullback.snd)
    (hβ.isLocalHomeomorph.pullback_snd hfc)
    (p.continuous_orbitRelQuotientPullback β f hf hp)).toHomeomorphOfBijective
      (p.bijective_orbitRelQuotientPullback β f hf hβ)

/-- The homeomorphism is the canonical comparison on points. -/
@[simp] theorem orbitRelQuotientPullbackHomeomorph_apply (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (x : X) :
    p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc x =
      p.orbitRelQuotientPullback β f hf x := (rfl)

/-- The inverse over the orbit of `x`, at the base point `g • p x`, is `g • x`. -/
@[simp] theorem orbitRelQuotientPullbackHomeomorph_symm_mk (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (g : G) (x : X) :
    (p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm
      ⟨(g • p x, Quotient.mk _ x), (hβ.map_smul g).trans (hf x).symm⟩ = g • x := by
  apply (p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).injective
  apply Subtype.ext
  simp [p.map_smul]

/-- The inverse has the prescribed projection to the base. -/
@[simp] theorem map_orbitRelQuotientPullbackHomeomorph_symm (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (w : β.Pullback f) :
    p ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm w) = w.fst := by
  exact congrArg (fun v ↦ v.1.1)
    ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).apply_symm_apply w)

/-- The inverse belongs to the prescribed orbit. -/
@[simp] theorem mk_orbitRelQuotientPullbackHomeomorph_symm (hp : Continuous p)
    (hβ : IsQuotientCoveringMap β G) (hfc : Continuous f) (w : β.Pullback f) :
    Quotient.mk (MulAction.orbitRel G X)
      ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).symm w) = w.snd := by
  exact congrArg (fun v ↦ v.1.2)
    ((p.orbitRelQuotientPullbackHomeomorph β f hf hp hβ hfc).apply_symm_apply w)

end MulActionHom
