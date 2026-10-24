/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Basic
public import TauCeti.CategoryTheory.Linear.LinearFunctor

/-!
# Linear transport on prescribed fibers

For a coherent equivariant lift, scalar linearity is imposed on its actual transport functors
between the prescribed fibers. No linear structure on the auxiliary joint categories is
required. `EquivariantGroupoidLift.IsLinear` expresses this using native `Functor.Linear`.

Linearity is invariant under a strong comparison of the transport pseudofunctors whose
components are linear equivalences. The proof uses the naturality isomorphism of the strong
transformation; thus it also applies when that comparison respects additional group actions.
When the auxiliary joint categories do have linear structures and the fiber comparisons are
linear, linearity can instead be checked on the joint functors. The normalized pseudofunctor
and the isotropy actions then have linear arrow functors.

The setting of complex-linear local representation categories is described in Frenkel,
*Langlands Correspondence for Loop Groups*, §1.3. The comparison uses Mathlib's
`Pseudofunctor.StrongTrans` and its naturality isomorphisms.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (R : Type*) [Semiring R]
  [∀ p, Preadditive (fiber actions p)] [∀ p, CategoryTheory.Linear R (fiber actions p)]

/-- A coherent equivariant lift is linear if the transport on its prescribed fibers is linear.
This condition uses no linear structure on the auxiliary values of the joint pseudofunctor. -/
class IsLinear (L : EquivariantGroupoidLift Γ actions) : Prop where
  /-- Every actual transport functor respects scalar multiplication of morphisms. -/
  linear_transport {p q : Γ} (g : p ⟶ q) : (L.transport g).Linear R

attribute [instance] IsLinear.linear_transport

variable (L : EquivariantGroupoidLift Γ actions)

/-- Linearity of a lift is equivalent to native linearity of all its transport functors. -/
lemma isLinear_iff : L.IsLinear R ↔ ∀ ⦃p q : Γ⦄ (g : p ⟶ q), (L.transport g).Linear R :=
  ⟨fun _ _ _ g ↦ IsLinear.linear_transport g, fun h ↦ ⟨fun g ↦ h g⟩⟩

/-- The normalized pseudofunctor uses the preadditive structure of the prescribed fiber. -/
instance preadditiveTransportPseudofunctorObj (p : LocallyDiscrete Γ) :
    Preadditive (L.transportPseudofunctor.obj p) :=
  inferInstanceAs (Preadditive (fiber actions p.as))

/-- The normalized pseudofunctor uses the scalar action on the prescribed fiber. -/
instance linearTransportPseudofunctorObj (p : LocallyDiscrete Γ) :
    CategoryTheory.Linear R (L.transportPseudofunctor.obj p) :=
  inferInstanceAs (CategoryTheory.Linear R (fiber actions p.as))

/-- The isotropy action uses the preadditive structure of the prescribed fiber. -/
instance preadditiveEndActionObj (p : Γ) (a : LocallyDiscrete (SingleObj (End p))) :
    Preadditive ((L.endAction p).obj a) :=
  inferInstanceAs (Preadditive (fiber actions p))

/-- The isotropy action uses the scalar action on the prescribed fiber. -/
instance linearEndActionObj (p : Γ) (a : LocallyDiscrete (SingleObj (End p))) :
    CategoryTheory.Linear R ((L.endAction p).obj a) :=
  inferInstanceAs (CategoryTheory.Linear R (fiber actions p))

/-- A linear lift has linear arrow functors in its normalized transport pseudofunctor. -/
instance linear_transportPseudofunctor_map [L.IsLinear R] {p q : LocallyDiscrete Γ}
    (g : p ⟶ q) : (L.transportPseudofunctor.map g).toFunctor.Linear R := by
  exact (inferInstance : (L.transport g.as).Linear R)

/-- The isotropy action of a linear lift acts by linear functors on the prescribed fiber. -/
instance linear_endAction_map [L.IsLinear R] (p : Γ)
    {a b : LocallyDiscrete (SingleObj (End p))} (g : a ⟶ b) :
    ((L.endAction p).map g).toFunctor.Linear R := by
  exact (inferInstance : (L.transport g.as.asHom).Linear R)

section Comparison

variable {actions' : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  [∀ p, Preadditive (fiber actions' p)] [∀ p, CategoryTheory.Linear R (fiber actions' p)]
  (L' : EquivariantGroupoidLift Γ actions')
  (η : Pseudofunctor.StrongTrans L.transportPseudofunctor L'.transportPseudofunctor)
  [hlinear : ∀ p, ((η.app p).toFunctor).Linear R]
  [hequiv : ∀ p, ((η.app p).toFunctor).IsEquivalence]

include hlinear hequiv

/-- A strong comparison by linear equivalences preserves and reflects linearity of each
transport functor. Naturality supplies the commuting square on the prescribed fibers. -/
lemma linear_transport_iff_of_strongTrans {p q : Γ} (g : p ⟶ q) :
    (L.transport g).Linear R ↔ (L'.transport g).Linear R := by
  -- Give the components the prescribed fiber types: instance search does not identify the
  -- pseudofunctor object wrappers with these types when matching scalar actions.
  let U : fiber actions p ⥤ fiber actions' p := (η.app ⟨p⟩).toFunctor
  let V : fiber actions q ⥤ fiber actions' q := (η.app ⟨q⟩).toFunctor
  have : U.Linear R := hlinear ⟨p⟩
  have : V.Linear R := hlinear ⟨q⟩
  have : U.IsEquivalence := hequiv ⟨p⟩
  have : V.IsEquivalence := hequiv ⟨q⟩
  exact linear_iff_of_comp_iso R (L.transport g) (L'.transport g)
    U V
    (Cat.Hom.toNatIso (η.naturality g.toLoc))

/-- Linearity of actual fiber transport is invariant under a strong comparison whose
components are linear equivalences. This includes comparisons compatible with the actions. -/
lemma isLinear_iff_of_strongTrans : L.IsLinear R ↔ L'.IsLinear R := by
  simp only [isLinear_iff]
  exact ⟨fun h _ _ g ↦ (L.linear_transport_iff_of_strongTrans R L' η g).1 (h g),
    fun h _ _ g ↦ (L.linear_transport_iff_of_strongTrans R L' η g).2 (h g)⟩

end Comparison

section Joint

variable [∀ p, Preadditive (L.jointFiber p)]
  [∀ p, CategoryTheory.Linear R (L.jointFiber p)]
  [∀ p, (L.fiberEquivalence p).functor.Linear R]

/-- If the fiber equivalences are linear, linearity of an actual transport functor is
equivalent to linearity of its joint functor before the fiber comparisons. -/
lemma linear_transport_iff_jointMap {p q : Γ} (g : p ⟶ q) :
    (L.transport g).Linear R ↔ (L.jointMap g).Linear R := by
  rw [transport_def, Functor.linear_comp_iff_of_full_of_essSurj]
  exact linear_comp_iff_of_faithful R _ _

/-- Linear joint functors and linear fiber equivalences construct a linear lift. -/
lemma isLinear_of_jointMap [∀ (p q : Γ) (g : p ⟶ q), (L.jointMap g).Linear R] :
    L.IsLinear R :=
  ⟨fun g ↦ (L.linear_transport_iff_jointMap R g).2 inferInstance⟩

end Joint

end TauCeti.EquivariantGroupoidLift
