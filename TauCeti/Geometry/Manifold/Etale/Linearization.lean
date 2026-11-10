/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Etale.Basic
public import TauCeti.Geometry.Manifold.GroupAction.Linearization
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Linear-ball charts of proper étale groupoids

Near each object of a proper étale groupoid, the full groupoid is presented by its finite
isotropy group acting linearly on a ball for an invariant inner product. The comparison is
fully faithful, its object map is an open embedding and a local diffeomorphism, and each
labelled arrow section is also an open embedding and a local diffeomorphism. The object
image can be chosen inside any prescribed neighbourhood.

`TauCeti.exists_linear_ball_isotropy_chart` combines the smooth local isotropy action with
smooth Bochner linearization. It retains the original isotropy labels at the centre, even
when their linear actions coincide. No effectiveness hypothesis is imposed.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* S. Bochner, *Compact groups of differentiable transformations*, Ann. of Math. (2) 46
  (1945), 372–381.
-/

public section

open CategoryTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {n : ℕ∞ω} {C : Type*} [Groupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I n C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]

/-- **Retained-arrow linear-ball charts.** Every object of a proper étale real groupoid has,
inside any prescribed neighbourhood, a fully faithful linear-ball action chart of its full
finite isotropy group. The object and labelled-arrow maps are open embeddings and local
`C^n` diffeomorphisms. At the origin the arrow labelled `g` is the original arrow `g`,
including ineffective isotropy. The squared radius is measured with the orbit-sum inner
product. -/
theorem exists_linear_ball_isotropy_chart [T2Space (Quiver.Total C)]
    (hp : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right))
    (hs : IsLocalDiffeomorph J I n (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I n (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun y : C ↦ (⟨y, y, 𝟙 y⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2)
    (hn : 1 ≤ n) (x : C) {s : Set C} (hsx : s ∈ 𝓝 x) :
    ∃ (ι : Fintype (Aut x)), letI := ι;
    ∃ (σ : ContRepresentation ℝ (Aut x) E) (c : ℝ) (B : TopologicalSpace.Opens E)
      (_ : MulAction (Aut x) B) (f : B → C) (z : B)
      (F : ActionCategory (Aut x) B ⥤ C),
      0 < c ∧ (B : Set E) = σ.toRepresentation.sumOfConjugatesInnerSublevel c ∧
      (z : E) = 0 ∧ f z = x ∧
      (∀ g : Aut x, ∀ v : B, (g • v : B).val = σ g v) ∧
      ContMDiffConstSMul 𝓘(ℝ, E) n (Aut x) B ∧
      IsOpenEmbedding f ∧ IsLocalDiffeomorph 𝓘(ℝ, E) I n f ∧ range f ⊆ s ∧
      (∀ a, F.obj a = f a.back) ∧ F.Full ∧ F.Faithful ∧
      (∀ g : Aut x, IsOpenEmbedding fun v : B ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ :
          Quiver.Total C)) ∧
      (∀ g : Aut x, IsLocalDiffeomorph 𝓘(ℝ, E) J n fun v : B ↦
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ :
          Quiver.Total C)) ∧
      ∀ g : Aut x,
        (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, z)).hom⟩ :
          Quiver.Total C) = ⟨x, x, g.asIso.hom⟩ := by
  classical
  have := finite_aut_of_proper_source_target hp hs.isLocalHomeomorph x
  let ι : Fintype (Aut x) := Fintype.ofFinite (Aut x)
  obtain ⟨U, hxU, act, F₀, hsmul, hfix, hobj, hfull, hfaithful, hopen, harrow, hcentre⟩ :=
    exists_contMDiff_isotropy_action_of_proper_source_target hp hs ht hu hc x
  -- Register the action and functor instances returned by the existential chart theorem.
  let : MulAction (Aut x) U := act
  have : F₀.Full := hfull
  have : F₀.Faithful := hfaithful
  have hneigh : (Subtype.val : U → C) ⁻¹' s ∈ 𝓝 (⟨x, hxU⟩ : U) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hsx
  obtain ⟨σ, e, c, hcpos, hxe, hezero, hes, het, -, he, hei, hequiv, -⟩ :=
    exists_equivariant_contMDiff_chart_target_eq_sumOfConjugatesInnerSublevel
      (fun g ↦ hsmul.contMDiff_const_smul g) hn hfix hneigh
  let B : TopologicalSpace.Opens E := ⟨e.target, e.open_target⟩
  -- Restrict the linear representation to its invariant ball, retaining every group label.
  have hpres (g : Aut x) (v : E) (hv : v ∈ e.target) : σ g v ∈ e.target := by
    rw [het] at hv ⊢
    exact (σ.toRepresentation.preimage_sumOfConjugatesInnerSublevel g c).ge hv
  let actB : MulAction (Aut x) B := σ.mulActionOpens B hpres
  obtain ⟨f, hf, hfopen, hfdiff⟩ :=
    e.exists_equivariant_symm_restrict σ hpres he hei hequiv
  let A := ActionCategory.map (MonoidHom.id (Aut x)) f
  have : A.Full := ActionCategory.full_map_of_injective f hfopen.injective
  have : A.Faithful := ActionCategory.faithful_map _ _ Function.injective_id
  let F := A ⋙ F₀
  let z : B := ⟨0, hezero ▸ e.map_source hxe⟩
  have hfz : f z = ⟨x, hxU⟩ :=
    (hf z).trans ((congrArg e.symm hezero).symm.trans (e.left_inv hxe))
  have hlabel (g : Aut x) (v : B) :
      (⟨_, _, F.map ((ActionCategory.totalEquiv (Aut x) B).symm (g, v)).hom⟩ :
        Quiver.Total C) =
      ⟨_, _, F₀.map ((ActionCategory.totalEquiv (Aut x) U).symm (g, f v)).hom⟩ := by
    -- Label-source coordinates avoid dependent equality of the two target objects.
    exact congrArg F₀.toPrefunctor.mapTotal
      (ActionCategory.mapTotal_totalEquiv_symm (MonoidHom.id (Aut x)) f g v)
  have hsmoothB := σ.contMDiffConstSMul_mulActionOpens B hpres n
  refine ⟨ι, σ, c, B, actB, (fun v ↦ (f v : C)), z, F, hcpos, het, rfl,
    congrArg Subtype.val hfz, σ.val_mulActionOpens_smul B hpres, hsmoothB,
    U.isOpenEmbedding'.comp hfopen,
    (fun v ↦ (hfdiff v).comp (hg := isLocalDiffeomorph_subtype_val (f v))), ?_,
    (fun a ↦ (hobj (A.obj a)).trans
      (congrArg Subtype.val
        (ActionCategory.back_map_obj (MonoidHom.id (Aut x)) f a))),
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact hes (hf v ▸ e.map_target v.2)
  · intro g
    simp only [hlabel]
    exact (hopen g).comp hfopen
  · intro g
    simp only [hlabel]
    exact fun v ↦ (hfdiff v).comp (hg := harrow g (f v))
  · intro g
    rw [hlabel, hfz]
    exact hcentre g

end TauCeti
