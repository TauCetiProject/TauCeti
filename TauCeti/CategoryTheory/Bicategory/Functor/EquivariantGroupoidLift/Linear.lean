/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Pullback
public import TauCeti.CategoryTheory.Linear.LinearFunctor

/-!
# Scalar-linear equivariant groupoid transport

`EquivariantGroupoidLift.IsLinear` requires the transport functors on the prescribed fibers
to be scalar-linear. It imposes no linear structure on the auxiliary categories of the joint
pseudofunctor. Thus it constrains the actual fiber transport, not a choice of presentation.

A strong transformation between the normalized transport pseudofunctors, with scalar-linear
component equivalences, preserves and reflects this condition. Pullback along a functor of
parameter categories also preserves linearity.

The underlying coherent transport and fiber comparisons are those of
`EquivariantGroupoidLift`; no new coherence data or choices of inverse equivalences are added.
The scalar-linear refinement is needed when the fibers are complex representation categories,
where an arbitrary equivalence could instead be semilinear.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, §1.3: families of local
  representation categories.
* Niles Johnson and Donald Yau, *2-Dimensional Categories*: strong transformations and
  their naturality isomorphisms.
-/

public section

universe w v u₂ v₁ u₁ u₃ v₃

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (R : Type*) [Semiring R]
  [∀ p, Preadditive (fiber actions p)] [∀ p, CategoryTheory.Linear R (fiber actions p)]

/-- Scalar linearity of the actual transport functors between the prescribed fiber categories.
No scalar structure on the auxiliary joint fibers is assumed. -/
class IsLinear (L : EquivariantGroupoidLift Γ actions) : Prop where
  /-- Every parameter arrow acts by a scalar-linear functor after the fiber comparisons. -/
  linear_transport {p q : Γ} (g : p ⟶ q) : (L.transport g).Linear R

attribute [instance] IsLinear.linear_transport

variable (L : EquivariantGroupoidLift Γ actions)

/-- Transport along a parameter isomorphism is a scalar-linear equivalence. -/
instance linear_transportEquivalence_functor [IsLinear R L] {p q : Γ} (g : p ≅ q) :
    (L.transportEquivalence g).functor.Linear R := by
  rw [transportEquivalence_functor]
  infer_instance

/-- A lift is scalar-linear precisely when all its actual fiber transport functors are. -/
lemma isLinear_iff : IsLinear R L ↔ ∀ (p q : Γ) (g : p ⟶ q), (L.transport g).Linear R :=
  ⟨fun _ _ _ _ => inferInstance, fun h => ⟨fun g => h _ _ g⟩⟩

section JointPresentation

variable [∀ p, Preadditive (L.jointFiber p)]
  [∀ p, CategoryTheory.Linear R (L.jointFiber p)]
  [∀ p, (L.fiberEquivalence p).functor.Linear R]

/-- If the auxiliary fibers and their comparison equivalences are scalar-linear, linearity
of an actual transport is equivalent to linearity of its joint-pseudofunctor presentation. -/
lemma linear_transport_iff_jointMap {p q : Γ} (g : p ⟶ q) :
    (L.transport g).Linear R ↔ (L.jointMap g).Linear R := by
  let F := L.jointMap g ⋙ (L.fiberEquivalence q).functor
  -- Inserting the unit of the source fiber equivalence compares a joint map with
  -- its conjugate. The target is exactly the definition of the actual transport.
  let e : L.jointMap g ⋙ (L.fiberEquivalence q).functor ≅
      (L.fiberEquivalence p).functor ⋙ L.transport g :=
    F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight (L.fiberEquivalence p).unitIso F ≪≫
      Functor.associator _ _ _
  exact (Functor.linear_iff_of_comp_iso R _ _ _ _ e).symm

/-- If the joint fibers are scalar-linear and the fiber comparisons are scalar-linear
functors, `L` is scalar-linear if and only if every `jointMap` is. -/
lemma isLinear_iff_jointMap : IsLinear R L ↔
    ∀ (p q : Γ) (g : p ⟶ q), (L.jointMap g).Linear R := by
  simp only [isLinear_iff]
  exact forall_congr' fun p => forall_congr' fun q => forall_congr' fun g =>
    linear_transport_iff_jointMap R L g

end JointPresentation

section Comparison

variable {actions' : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  [∀ p, Preadditive (fiber actions' p)] [∀ p, CategoryTheory.Linear R (fiber actions' p)]
  (L' : EquivariantGroupoidLift Γ actions')
  (η : Pseudofunctor.StrongTrans L.transportPseudofunctor L'.transportPseudofunctor)
  -- The explicit fiber types keep instance search on the prescribed scalar structures,
  -- rather than asking it to unfold the object function of `transportPseudofunctor`.
  [∀ p : Γ, Functor.Linear R
    (show fiber actions p ⥤ fiber actions' p from (η.app ⟨p⟩).toFunctor)]
  [∀ p : Γ, (show fiber actions p ⥤ fiber actions' p from
    (η.app ⟨p⟩).toFunctor).IsEquivalence]

include η in
/-- A strong transformation of normalized transport pseudofunctors whose components are
scalar-linear equivalences preserves and reflects linearity along each parameter arrow. -/
lemma linear_transport_iff_of_strongTrans {p q : Γ} (g : p ⟶ q) :
    (L.transport g).Linear R ↔ (L'.transport g).Linear R := by
  -- The native `Cat` naturality cell has the required endpoints after converting its
  -- 1-morphisms to functors; `transportPseudofunctor` uses exactly `transport` on arrows.
  let U : fiber actions p ⥤ fiber actions' p := (η.app ⟨p⟩).toFunctor
  let V : fiber actions q ⥤ fiber actions' q := (η.app ⟨q⟩).toFunctor
  let e : L.transport g ⋙ V ≅ U ⋙ L'.transport g :=
    Cat.Hom.toNatIso (η.naturality g.toLoc)
  exact Functor.linear_iff_of_comp_iso R _ _ U V e

include η in
/-- Scalar linearity of coherent fiber transport is invariant under a strong transformation
of normalized transport pseudofunctors whose components are scalar-linear equivalences. -/
lemma isLinear_iff_of_strongTrans : IsLinear R L ↔ IsLinear R L' := by
  simp only [isLinear_iff]
  exact forall_congr' fun p => forall_congr' fun q => forall_congr' fun g =>
    linear_transport_iff_of_strongTrans R L L' η g

end Comparison

section Pullback

variable {Λ : Type u₃} [Category.{v₃} Λ] (ψ : Λ ⥤ Γ)

/-- Pulling back a scalar-linear lift preserves scalar linearity on its prescribed fibers. -/
instance isLinear_pullback [IsLinear R L] : IsLinear R (L.pullback ψ) where
  linear_transport g := by
    rw [pullback_transport]
    infer_instance

/-- Linearity of a pulled-back lift only tests the original transports along image arrows. -/
lemma isLinear_pullback_iff : IsLinear R (L.pullback ψ) ↔
    ∀ (p q : Λ) (g : p ⟶ q), (L.transport (ψ.map g)).Linear R := by
  simp only [isLinear_iff, pullback_transport]

end Pullback

end TauCeti.EquivariantGroupoidLift
