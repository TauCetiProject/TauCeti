/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.Descent.Affine

/-!
# Invariant functions of a descent datum

Let `p : S' ⟶ S` be a morphism of schemes and `D` a descent datum relative to `p` on a scheme
`X ⟶ S'`, with action `D.act : S' ×_S X ⟶ X`. A global function `b` on `X` is *invariant* under
`D` when its pullbacks along the action and along the second projection `S' ×_S X ⟶ X` agree:
`b (s · x) = b x`. The invariant functions form a subring `D.invariants` of `Γ(X, ⊤)`, which
contains the functions pulled back from `S`.

For affine schemes this is the descended algebra of the dictionary
`TauCeti.Algebra.DescentDatum.specEquiv` between descent data on `Spec B` and coactions on `B`
(`TauCeti.Algebra.DescentDatum.ΓSpecIso_inv_mem_invariants_spec_iff`). Hence effective descent
for algebras along a flat map gives the following form of effective descent for affine schemes:
if `S`, `S'` and `X` are affine and `p` is flat, then
`Γ(S, ⊤) ⟶ Γ(S', ⊤)`, `Γ(S, ⊤) ⟶ D.invariants`, `D.invariants ⟶ Γ(X, ⊤)` and
`Γ(S', ⊤) ⟶ Γ(X, ⊤)` form a pushout square of rings
(`TauCeti.DescentDatum.isPushout_invariants`): `Γ(X, ⊤) = Γ(S', ⊤) ⊗[Γ(S, ⊤)] D.invariants`.
Unlike `TauCeti.DescentDatum.exists_isAffine_baseChange_hom_isIso`, this names the descended ring
intrinsically in terms of `D`, so that it can be compared with the descended scheme
`TauCeti.DescentDatum.descended` of a descent datum on an affine morphism.

## Main declarations

* `TauCeti.DescentDatum.invariants D`: the ring of global functions on `X` invariant under `D`;
* `TauCeti.DescentDatum.Hom.appTop_mem_invariants_iff` and
  `TauCeti.DescentDatum.mem_invariants_transportArrow_iff`: invariance of `D.invariants` under
  isomorphisms of descent data and under transport along isomorphisms of arrows;
* `TauCeti.Algebra.DescentDatum.ΓSpecIso_inv_mem_invariants_spec_iff`: the invariant functions
  of the descent datum on `Spec B` defined by a coaction on `B` form the descended algebra;
* `TauCeti.DescentDatum.toInvariants D`: the functions on `S`, as invariant functions on `X`;
* `TauCeti.DescentDatum.isPushout_invariants`: **effective descent for affine schemes**, in terms
  of invariant functions.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace TauCeti

universe u

namespace DescentDatum

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X Y : Over S'}

/-- The global functions on `X` invariant under a descent datum `D`: those whose pullbacks along
the action `S' ×_S X ⟶ X` and along the second projection `S' ×_S X ⟶ X` agree. -/
noncomputable def invariants (D : DescentDatum p X) : Subring Γ(X.left, ⊤) :=
  RingHom.eqLocus D.act.appTop.hom (pullback.snd p (X.hom ≫ p)).appTop.hom

theorem mem_invariants_iff {D : DescentDatum p X} {b : Γ(X.left, ⊤)} :
    b ∈ D.invariants ↔ D.act.appTop b = (pullback.snd p (X.hom ≫ p)).appTop b :=
  Iff.rfl

/-- A function on `X` pulled back from `S` is invariant. -/
theorem hom_comp_appTop_mem_invariants (D : DescentDatum p X) (r : Γ(S, ⊤)) :
    (X.hom ≫ p).appTop r ∈ D.invariants := by
  rw [mem_invariants_iff, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, D.act_comp_hom_comp]

/-- The functions on `S`, as invariant functions on `X`. -/
noncomputable def toInvariants (D : DescentDatum p X) : Γ(S, ⊤) →+* D.invariants :=
  (X.hom ≫ p).appTop.hom.codRestrict D.invariants D.hom_comp_appTop_mem_invariants

@[simp]
theorem coe_toInvariants (D : DescentDatum p X) (r : Γ(S, ⊤)) :
    (D.toInvariants r : Γ(X.left, ⊤)) = (X.hom ≫ p).appTop r :=
  (rfl)

/-- A morphism of descent data pulls back invariant functions to invariant functions. -/
theorem Hom.appTop_mem_invariants {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    {b : Γ(Y.left, ⊤)} (hb : b ∈ E.invariants) : f.hom.left.appTop b ∈ D.invariants := by
  rw [mem_invariants_iff] at hb ⊢
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, ← f.map_act, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd]

/-- An isomorphism of descent data identifies the invariant functions. -/
theorem Hom.appTop_mem_invariants_iff {D : DescentDatum p X} {E : DescentDatum p Y} (f : Hom D E)
    [IsIso f.hom] {b : Γ(Y.left, ⊤)} : f.hom.left.appTop b ∈ D.invariants ↔ b ∈ E.invariants := by
  refine ⟨fun hb ↦ ?_, f.appTop_mem_invariants⟩
  have h := f.inv.appTop_mem_invariants hb
  rwa [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Hom.inv_hom, ← Over.comp_left,
    IsIso.inv_hom_id, Over.id_left, Scheme.Hom.id_appTop, CommRingCat.id_apply] at h

/-- Transport along an isomorphism of arrows does not change the invariant functions. -/
theorem mem_invariants_transportArrow_iff {T T' : Scheme.{u}} {q : T' ⟶ T}
    (e : Arrow.mk p ≅ Arrow.mk q) (D : DescentDatum p X) {b : Γ(X.left, ⊤)} :
    b ∈ (D.transportArrow e).invariants ↔ b ∈ D.invariants := by
  have : IsIso (transportArrowActionComparison e X).appTop :=
    inferInstanceAs (IsIso ((transportArrowActionComparison e X).app ⊤))
  rw [mem_invariants_iff, mem_invariants_iff, transportArrow_act,
    ← transportArrowActionComparison_snd e X]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact (ConcreteCategory.bijective_of_isIso
    (transportArrowActionComparison e X).appTop).injective.eq_iff

end DescentDatum

namespace Algebra.DescentDatum

variable {R S B : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- The invariant functions of the descent datum `E.spec` on `Spec B` defined by a descent datum
`E` on the algebra `B` are the elements of the descended algebra `E.descended`. -/
theorem ΓSpecIso_inv_mem_invariants_spec_iff (E : DescentDatum R S B) {b : B} :
    (Scheme.ΓSpecIso (.of B)).inv b ∈ E.spec.invariants ↔ b ∈ E.descended := by
  have hsq := isPullback_spec_tensorProduct R S B
  -- The comparison `Spec (S ⊗[R] B) ⟶ Spec S ×_{Spec R} Spec B` is an isomorphism, through which
  -- the action and the second projection are `Spec` of the coaction and of `b ↦ 1 ⊗ b`.
  let L := pullback.lift _ _ hsq.w
  have : IsIso L := by
    rw [show L = hsq.isoPullback.hom by refine pullback.hom_ext ?_ ?_ <;> simp [L]]
    infer_instance
  have : IsIso L.appTop := inferInstanceAs (IsIso (L.app ⊤))
  have hact : L ≫ E.spec.act = Spec.map (CommRingCat.ofHom E.coaction.toRingHom) :=
    lift_spec_act E _
  have hsnd : L ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom) :=
    pullback.lift_snd _ _ _
  rw [TauCeti.DescentDatum.mem_invariants_iff, mem_descended_iff,
    ← (ConcreteCategory.bijective_of_isIso L.appTop).injective.eq_iff]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hact, hsnd]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, CommRingCat.comp_apply,
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).injective.eq_iff]
  simp

end Algebra.DescentDatum

namespace DescentDatum

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'}

/-- **Effective descent for affine schemes, in terms of invariant functions.** Let `p : S' ⟶ S`
be a flat morphism of affine schemes and `D` a descent datum relative to `p` on an affine scheme
`X` over `S'`. Then `Γ(X, ⊤)` is the base change `Γ(S', ⊤) ⊗[Γ(S, ⊤)] D.invariants` of the ring
of invariant functions: the square formed by `D.toInvariants`, `p.appTop`, the inclusion of the
invariant functions and `X.hom.appTop` is a pushout square of rings. -/
theorem isPushout_invariants [IsAffine S] [IsAffine S'] [Flat p] [IsAffine X.left]
    (D : DescentDatum p X) :
    IsPushout (CommRingCat.ofHom D.toInvariants) p.appTop
      (CommRingCat.ofHom D.invariants.subtype) X.hom.appTop := by
  -- Present `p` as `Spec Γ(S', ⊤) ⟶ Spec Γ(S, ⊤)` and `X` as `Spec Γ(X, ⊤)`, as in
  -- `exists_isAffine_baseChange_hom_isIso`, and transport `D` to a descent datum `E` on the
  -- `Γ(S', ⊤)`-algebra `Γ(X, ⊤)`.
  let _ : Algebra Γ(S, ⊤) Γ(S', ⊤) := p.appTop.hom.toAlgebra
  have : Module.Flat Γ(S, ⊤) Γ(S', ⊤) := by
    rw [← RingHom.flat_algebraMap_iff, RingHom.algebraMap_toAlgebra]
    exact HasRingHomProperty.iff_of_isAffine.mp ‹Flat p›
  have hp : Spec.algebraMap Γ(S, ⊤) Γ(S', ⊤) = Spec.map p.appTop := by
    rw [Spec.algebraMap, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  let e : Arrow.mk p ≅ Arrow.mk (Spec.algebraMap Γ(S, ⊤) Γ(S', ⊤)) :=
    arrowIsoSpecΓOfIsAffine p ≪≫ Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simp [hp])
  let _ : Algebra Γ(S', ⊤) Γ(X.left, ⊤) := X.hom.appTop.hom.toAlgebra
  let _ : Algebra Γ(S, ⊤) Γ(X.left, ⊤) := (X.hom ≫ p).appTop.hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(S', ⊤) Γ(X.left, ⊤) := .of_algebraMap_eq fun _ ↦ rfl
  let e' : Over.mk (Spec.algebraMap Γ(S', ⊤) Γ(X.left, ⊤)) ≅ (Over.map e.hom.left).obj X :=
    (Over.isoMk X.left.isoSpec (by
      simp [e, Spec.algebraMap, RingHom.algebraMap_toAlgebra, Scheme.isoSpec_hom_naturality,
        arrowIsoSpecΓOfIsAffine]
      -- `e.hom.left` is `S'.isoSpec.hom` followed by the identity of `Arrow.isoMk`.
      rfl)).symm
  let E := (Algebra.DescentDatum.specEquiv _ _ _).symm (transport e' (D.transportArrow e))
  have : IsIso (transportHom e' (D.transportArrow e)).hom := by
    rw [transportHom_hom]
    infer_instance
  -- The invariant functions of `D` are the descended algebra of `E`.
  have hdesc : E.descended.toSubring = D.invariants := by
    ext b
    rw [← mem_invariants_transportArrow_iff e, ← (transportHom e' _).appTop_mem_invariants_iff,
      transportHom_hom, Subalgebra.mem_toSubring, ← E.ΓSpecIso_inv_mem_invariants_spec_iff,
      Algebra.DescentDatum.spec_specEquiv_symm]
    -- `e'.hom.left` is `X.left.isoSpec.inv`, whose map on global sections is `ΓSpecIso` inverse.
    erw [Scheme.isoSpec_inv_appTop X.left]
    rfl
  have : Algebra.IsPushout Γ(S, ⊤) Γ(S', ⊤) E.descended Γ(X.left, ⊤) :=
    ⟨E.isBaseChange_descended_val⟩
  -- Transport the pushout square of `Algebra.IsPushout` along `E.descended = D.invariants`; the
  -- four algebra maps are, elementwise, the maps of the target square.
  refine (CommRingCat.isPushout_of_isPushout Γ(S, ⊤) Γ(S', ⊤) E.descended Γ(X.left, ⊤)).flip.of_iso
    (Iso.refl _) (RingEquiv.subringCongr hdesc).toCommRingCatIso (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_ <;> ext <;> rfl

end DescentDatum

end TauCeti
