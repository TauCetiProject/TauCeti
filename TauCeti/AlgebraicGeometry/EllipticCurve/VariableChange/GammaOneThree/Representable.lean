/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import TauCeti.Algebra.Ring.Invertible
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.GammaOneThree.ArrowRing
import Mathlib.Tactic.FinCases
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic

/-!
# Functoriality, pushouts, and shearing for strict `Γ₁(3)` arrow algebras

`TauCeti.GammaOneThreeHopfAlgebroid.ArrowRing a₁ a₃` is the quotient of `B[r, s, t]` cutting out
strict changes of variables `C = (1, r, s, t)` carrying `WeierstrassCurve.gammaOneThreeForm a₁ a₃`
to another curve in `Γ₁(3)` normal form. While `ArrowRing.arrowEquiv` in
`TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/GammaOneThree/ArrowRing.lean` establishes
its universal property for `B`-algebra maps over a fixed base `B`, constructing the `Γ₁(3)` Hopf
algebroid requires ring homomorphisms across distinct coefficient extensions (notably the left and
right units `η_L, η_R : BaseRing R →+* UniversalArrowRing R`).

This file establishes for `ArrowRing a₁ a₃` over any commutative ring `B`:
* its universal property for ring homomorphisms (`ArrowRing.lift`, `ArrowRing.ringHom_ext`),
  derived fiberwise from `ArrowRing.arrowEquiv`;
* functoriality in `(B, a₁, a₃)` (`ArrowRing.mapOfEq`, `ArrowRing.map`);
* its pushout universal property (`ArrowRing.pushoutLiftOfEq`, `ArrowRing.pushoutLift`) and
  categorical pushout square in `CommRingCat` (`ArrowRing.isPushout`);
* the groupoid torsor shearing isomorphism (`ArrowRing.shearEquiv`) induced by precomposing with a
  strict `Γ₁(3)` arrow over `B`, used to factor the Hopf-algebroid coproduct as
  `Δ = shearEquiv ∘ map η_L`
  (`TauCeti.GammaOneThreeHopfAlgebroid.coproduct_eq_shearEquiv_comp_map`);
* base-change compatibility of the rank-`8` basis and `Algebra.trace` when `3` is invertible in `B`
  (`ArrowRing.mapOfEq_basis`, `ArrowRing.trace_mapOfEq`, `ArrowRing.trace_map`).

## Main definitions

* `TauCeti.GammaOneThreeHopfAlgebroid.ArrowRing.lift`: ring-homomorphism universal property of
  `ArrowRing a₁ a₃`.
* `TauCeti.GammaOneThreeHopfAlgebroid.ArrowRing.mapOfEq`, `ArrowRing.map`: coefficient extension
  along `f : B →+* B'`.
* `TauCeti.GammaOneThreeHopfAlgebroid.ArrowRing.pushoutLiftOfEq`, `ArrowRing.pushoutLift`:
  universal property of `ArrowRing a₁' a₃'` as a pushout over `B`.
* `TauCeti.GammaOneThreeHopfAlgebroid.ArrowRing.shearEquiv`: the `B`-algebra isomorphism induced by
  precomposing with a strict `Γ₁(3)` arrow over `B`.

## Main results

* `ArrowRing.isPushout`: the coefficient-extension square for `ArrowRing` is a pushout in
  `CommRingCat`.
* `ArrowRing.trace_mapOfEq`, `ArrowRing.trace_map`: base-change compatibility of `Algebra.trace` on
  `ArrowRing a₁ a₃` when `[Invertible (3 : B)]`.

## Provenance

The universal property (`lift`, `lift_symm_apply`, `ringHom_ext`), functoriality (`mapOfEq`,
`map`, `map_id`, `map_comp`), and pushout API (`pushoutLiftOfEq`, `pushoutLift`, `isPushout`
proof) closely adapt `TauCeti.WeierstrassChange.ChangeRing` in
`TauCeti/AlgebraicGeometry/EllipticCurve/VariableChange/Representable.lean` from the level-one
Weierstrass change ring to strict `Γ₁(3)` normal-form arrows.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §7.
* Christian Carrick, J. Davies and S. van Nigtevecht, *The descent spectral sequence for topological
  modular forms*, arXiv:2412.01640v2, §4.2.
-/

public section

noncomputable section

universe u

namespace TauCeti.GammaOneThreeHopfAlgebroid

open _root_.WeierstrassCurve

namespace ArrowRing

section UniversalProperty

variable {B B' S : Type*} [CommRing B] [CommRing B'] [CommRing S]

/-- Numeric literals invertible in `B` remain invertible in `ArrowRing a₁ a₃`. -/
instance instInvertibleOfNat (a₁ a₃ : B) {n : ℕ} [n.AtLeastTwo] [Invertible (ofNat(n) : B)] :
    Invertible (ofNat(n) : ArrowRing a₁ a₃) :=
  TauCeti.invertibleMapOfNat (algebraMap B (ArrowRing a₁ a₃)) n

variable {a₁ a₃ : B}

/-- **Ring-homomorphism universal property of `ArrowRing a₁ a₃`**: ring homomorphisms out of
`ArrowRing a₁ a₃` classify pairs `(f, D)` of a ring homomorphism `f : B →+* S` and a strict
`Γ₁(3)` arrow `D` out of `gammaOneThreeForm (f a₁) (f a₃)`. -/
def lift :
    {p : (B →+* S) × VariableChange S // IsStrictGammaOneThreeChange (p.1 a₁) (p.1 a₃) p.2} ≃
      (ArrowRing a₁ a₃ →+* S) where
  toFun p :=
    letI : Algebra B S := p.val.1.toAlgebra
    ((arrowEquiv a₁ a₃ S).symm ⟨p.val.2, p.property⟩).toRingHom
  invFun k := ⟨(k.comp (algebraMap B _), (universalChange a₁ a₃).map k),
    (isStrictGammaOneThreeChange_universalChange a₁ a₃).map k⟩
  left_inv p := by
    let _ : Algebra B S := p.val.1.toAlgebra
    exact Subtype.ext (Prod.ext
      (((arrowEquiv a₁ a₃ S).symm ⟨p.val.2, p.property⟩).comp_algebraMap)
      (map_universalChange_arrowEquiv_symm_apply a₁ a₃ S ⟨p.val.2, p.property⟩))
  right_inv k := by
    let _ : Algebra B S := (k.comp (algebraMap B _)).toAlgebra
    let kₐ : ArrowRing a₁ a₃ →ₐ[B] S := ⟨k, fun _ ↦ rfl⟩
    have hk : (⟨(universalChange a₁ a₃).map k,
        (isStrictGammaOneThreeChange_universalChange a₁ a₃).map k⟩ :
        {C : VariableChange S //
          IsStrictGammaOneThreeChange (algebraMap B S a₁) (algebraMap B S a₃) C}) =
        arrowEquiv a₁ a₃ S kₐ :=
      Subtype.ext (coe_arrowEquiv_apply a₁ a₃ S kₐ).symm
    dsimp only
    rw [hk]
    exact congrArg AlgHom.toRingHom ((arrowEquiv a₁ a₃ S).symm_apply_apply kₐ)

@[simp]
theorem lift_comp_algebraMap
    (p : {p : (B →+* S) × VariableChange S // IsStrictGammaOneThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    (lift p).comp (algebraMap B _) = p.val.1 :=
  congrArg (fun q ↦ q.val.1) (lift.left_inv p)

@[simp]
theorem lift_algebraMap
    (p : {p : (B →+* S) × VariableChange S // IsStrictGammaOneThreeChange (p.1 a₁) (p.1 a₃) p.2})
    (b : B) :
    lift p (algebraMap B _ b) = p.val.1 b :=
  RingHom.congr_fun (lift_comp_algebraMap p) b

@[simp]
theorem map_lift
    (p : {p : (B →+* S) × VariableChange S // IsStrictGammaOneThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    (universalChange a₁ a₃).map (lift p) = p.val.2 :=
  congrArg (fun q ↦ q.val.2) (lift.left_inv p)

@[simp]
theorem lift_r
    (p : {p : (B →+* S) × VariableChange S // IsStrictGammaOneThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    lift p r = p.val.2.r := by
  have h := congrArg VariableChange.r (map_lift p)
  rwa [VariableChange.map_r, universalChange_r] at h

@[simp]
theorem lift_s
    (p : {p : (B →+* S) × VariableChange S // IsStrictGammaOneThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    lift p s = p.val.2.s := by
  have h := congrArg VariableChange.s (map_lift p)
  rwa [VariableChange.map_s, universalChange_s] at h

@[simp]
theorem lift_t
    (p : {p : (B →+* S) × VariableChange S // IsStrictGammaOneThreeChange (p.1 a₁) (p.1 a₃) p.2}) :
    lift p t = p.val.2.t := by
  have h := congrArg VariableChange.t (map_lift p)
  rwa [VariableChange.map_t, universalChange_t] at h

@[simp]
theorem lift_symm_apply (k : ArrowRing a₁ a₃ →+* S) :
    (lift.symm k).val = (k.comp (algebraMap B _), (universalChange a₁ a₃).map k) :=
  (rfl)

/-- A ring homomorphism out of `ArrowRing a₁ a₃` is determined by its restriction to `B` and its
image of `universalChange a₁ a₃`. -/
theorem ringHom_ext {k k' : ArrowRing a₁ a₃ →+* S}
    (h₁ : k.comp (algebraMap B _) = k'.comp (algebraMap B _))
    (h₂ : (universalChange a₁ a₃).map k = (universalChange a₁ a₃).map k') : k = k' :=
  lift.symm.injective (Subtype.ext (Prod.ext h₁ h₂))

/-- Coefficient extension `ArrowRing a₁ a₃ →+* ArrowRing a₁' a₃'` along `f : B →+* B'` when
`f a₁ = a₁'` and `f a₃ = a₃'`. -/
def mapOfEq {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    ArrowRing a₁ a₃ →+* ArrowRing a₁' a₃' :=
  lift ⟨((algebraMap B' _).comp f, universalChange a₁' a₃'), by
    simpa [ha₁, ha₃] using isStrictGammaOneThreeChange_universalChange a₁' a₃'⟩

@[simp]
theorem mapOfEq_comp_algebraMap {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') :
    (mapOfEq f ha₁ ha₃).comp (algebraMap B _) = (algebraMap B' _).comp f := by
  rw [mapOfEq]
  exact lift_comp_algebraMap _

@[simp]
theorem mapOfEq_algebraMap {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃')
    (b : B) :
    mapOfEq f ha₁ ha₃ (algebraMap B _ b) = algebraMap B' _ (f b) := by
  rw [mapOfEq]
  exact lift_algebraMap _ b

@[simp]
theorem universalChange_map_mapOfEq {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') :
    (universalChange a₁ a₃).map (mapOfEq f ha₁ ha₃) = universalChange a₁' a₃' := by
  rw [mapOfEq]
  exact map_lift _

@[simp]
theorem mapOfEq_r {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    mapOfEq f ha₁ ha₃ r = r := by
  simp [mapOfEq]

@[simp]
theorem mapOfEq_s {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    mapOfEq f ha₁ ha₃ s = s := by
  simp [mapOfEq]

@[simp]
theorem mapOfEq_t {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    mapOfEq f ha₁ ha₃ t = t := by
  simp [mapOfEq]

/-- Coefficient extension `ArrowRing a₁ a₃ →+* ArrowRing (f a₁) (f a₃)` along `f : B →+* B'`. -/
abbrev map (f : B →+* B') : ArrowRing a₁ a₃ →+* ArrowRing (f a₁) (f a₃) :=
  mapOfEq f rfl rfl

@[simp]
theorem map_id : map (RingHom.id B) (a₁ := a₁) (a₃ := a₃) = RingHom.id (ArrowRing a₁ a₃) :=
  ringHom_ext (by simp) (by simp)

@[simp]
theorem map_comp {B'' : Type*} [CommRing B''] (g : B' →+* B'') (f : B →+* B') :
    map (g.comp f) (a₁ := a₁) (a₃ := a₃) = (map g).comp (map f) :=
  ringHom_ext (RingHom.ext fun b ↦ by simp) (by simp [← VariableChange.map_map])

/-- **Universal property of `ArrowRing a₁' a₃'` as the pushout `B' ⊗_B ArrowRing a₁ a₃`** along
`f : B →+* B'` (with `f a₁ = a₁'`, `f a₃ = a₃'`) and `algebraMap`. -/
def pushoutLiftOfEq {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') :
    {p : (B' →+* S) × (ArrowRing a₁ a₃ →+* S) //
      p.1.comp f = p.2.comp (algebraMap B _)} ≃
      (ArrowRing a₁' a₃' →+* S) where
  toFun p := lift ⟨(p.val.1, (universalChange a₁ a₃).map p.val.2), by
    have h₁ : p.val.1 a₁' = p.val.2 (algebraMap B _ a₁) := by
      rw [← ha₁]
      exact RingHom.congr_fun p.property a₁
    have h₃ : p.val.1 a₃' = p.val.2 (algebraMap B _ a₃) := by
      rw [← ha₃]
      exact RingHom.congr_fun p.property a₃
    rw [h₁, h₃]
    exact (isStrictGammaOneThreeChange_universalChange a₁ a₃).map p.val.2⟩
  invFun k := ⟨(k.comp (algebraMap B' _), k.comp (mapOfEq f ha₁ ha₃)), by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, mapOfEq_comp_algebraMap]⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext (lift_comp_algebraMap _) (ringHom_ext ?_ ?_))
    · rw [RingHom.comp_assoc, mapOfEq_comp_algebraMap, ← RingHom.comp_assoc, lift_comp_algebraMap,
        p.property]
    · rw [← VariableChange.map_map, universalChange_map_mapOfEq, map_lift]
  right_inv k := ringHom_ext (lift_comp_algebraMap _) (by
    rw [map_lift]
    dsimp only
    rw [← VariableChange.map_map, universalChange_map_mapOfEq])

/-- Pushout universal property for `ArrowRing (f a₁) (f a₃)`. -/
abbrev pushoutLift (f : B →+* B') :=
  pushoutLiftOfEq (S := S) (a₁ := a₁) (a₃ := a₃) f rfl rfl

@[simp]
theorem pushoutLiftOfEq_symm_apply_fst {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') (k : ArrowRing a₁' a₃' →+* S) :
    ((pushoutLiftOfEq f ha₁ ha₃).symm k).val.1 = k.comp (algebraMap B' _) :=
  (rfl)

@[simp]
theorem pushoutLiftOfEq_symm_apply_snd {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁')
    (ha₃ : f a₃ = a₃') (k : ArrowRing a₁' a₃' →+* S) :
    ((pushoutLiftOfEq f ha₁ ha₃).symm k).val.2 = k.comp (mapOfEq f ha₁ ha₃) :=
  (rfl)

section PushoutLemmas

variable {a₁' a₃' : B'} (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃')
  (p : {p : (B' →+* S) × (ArrowRing a₁ a₃ →+* S) //
    p.1.comp f = p.2.comp (algebraMap B _)})

@[simp]
theorem pushoutLiftOfEq_comp_algebraMap :
    (pushoutLiftOfEq f ha₁ ha₃ p).comp (algebraMap B' _) = p.val.1 :=
  congrArg (fun q ↦ q.val.1) ((pushoutLiftOfEq f ha₁ ha₃).left_inv p)

@[simp]
theorem pushoutLiftOfEq_comp_mapOfEq :
    (pushoutLiftOfEq f ha₁ ha₃ p).comp (mapOfEq f ha₁ ha₃) = p.val.2 :=
  congrArg (fun q ↦ q.val.2) ((pushoutLiftOfEq f ha₁ ha₃).left_inv p)

@[simp]
theorem pushoutLiftOfEq_algebraMap (b : B') :
    pushoutLiftOfEq f ha₁ ha₃ p (algebraMap B' _ b) = p.val.1 b :=
  RingHom.congr_fun (pushoutLiftOfEq_comp_algebraMap f ha₁ ha₃ p) b

@[simp]
theorem pushoutLiftOfEq_mapOfEq (x : ArrowRing a₁ a₃) :
    pushoutLiftOfEq f ha₁ ha₃ p (mapOfEq f ha₁ ha₃ x) = p.val.2 x :=
  RingHom.congr_fun (pushoutLiftOfEq_comp_mapOfEq f ha₁ ha₃ p) x

@[simp]
theorem universalChange_map_pushoutLiftOfEq :
    (universalChange a₁' a₃').map (pushoutLiftOfEq f ha₁ ha₃ p) =
      (universalChange a₁ a₃).map p.val.2 :=
  map_lift _

end PushoutLemmas

end UniversalProperty

open CategoryTheory CategoryTheory.Limits in
/-- The coefficient-extension square for `ArrowRing` is a pushout in `CommRingCat`. -/
theorem isPushout {B B' : Type u} [CommRing B] [CommRing B'] {a₁ a₃ : B} (f : B →+* B') :
    CategoryTheory.IsPushout (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap B (ArrowRing a₁ a₃)))
      (CommRingCat.ofHom (algebraMap B' (ArrowRing (f a₁) (f a₃))))
      (CommRingCat.ofHom (map f)) := by
  have comm : CommRingCat.ofHom f ≫
      CommRingCat.ofHom (algebraMap B' (ArrowRing (f a₁) (f a₃))) =
      CommRingCat.ofHom (algebraMap B (ArrowRing a₁ a₃)) ≫ CommRingCat.ofHom (map f) :=
    congrArg CommRingCat.ofHom (mapOfEq_comp_algebraMap (a₁ := a₁) (a₃ := a₃) f rfl rfl).symm
  let desc (c : PushoutCocone (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap B (ArrowRing a₁ a₃)))) :=
    CommRingCat.ofHom (pushoutLift (a₁ := a₁) (a₃ := a₃) f ⟨(c.inl.hom, c.inr.hom),
      congrArg CommRingCat.Hom.hom c.condition⟩)
  refine ⟨⟨comm⟩, ⟨PushoutCocone.IsColimit.mk comm desc ?_ ?_ ?_⟩⟩
  · intro c
    exact congrArg CommRingCat.ofHom (pushoutLiftOfEq_comp_algebraMap f rfl rfl _)
  · intro c
    exact congrArg CommRingCat.ofHom (pushoutLiftOfEq_comp_mapOfEq f rfl rfl _)
  · intro c m hm hn
    apply CommRingCat.hom_ext
    apply (pushoutLift (a₁ := a₁) (a₃ := a₃) f).symm.injective
    apply Subtype.ext
    apply Prod.ext
    · simpa only [pushoutLiftOfEq_symm_apply_fst, desc, CommRingCat.hom_ofHom,
        CommRingCat.hom_comp, pushoutLiftOfEq_comp_algebraMap] using congrArg CommRingCat.Hom.hom hm
    · simpa only [pushoutLiftOfEq_symm_apply_snd, desc, CommRingCat.hom_ofHom,
        CommRingCat.hom_comp, pushoutLiftOfEq_comp_mapOfEq] using congrArg CommRingCat.Hom.hom hn

section Shear

variable {B : Type*} [CommRing B] {a₁ a₃ : B}

/-- Precomposing the universal strict `Γ₁(3)` arrow over `(a₁', a₃')` with a strict `Γ₁(3)` arrow
`C₀` from `(a₁, a₃)` to `(a₁', a₃')` yields a strict `Γ₁(3)` arrow out of `(a₁, a₃)` over
`ArrowRing a₁' a₃'`. -/
theorem isStrictGammaOneThreeChange_universalChange_mul_map {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    IsStrictGammaOneThreeChange (algebraMap B (ArrowRing a₁' a₃') a₁)
      (algebraMap B (ArrowRing a₁' a₃') a₃)
      (universalChange a₁' a₃' * C₀.map (algebraMap B (ArrowRing a₁' a₃'))) := by
  refine (hC₀.map (algebraMap B (ArrowRing a₁' a₃'))).mul ?_
  simpa [ha₁, ha₃, map_ofNat] using isStrictGammaOneThreeChange_universalChange a₁' a₃'

private def shearHom {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    ArrowRing a₁ a₃ →+* ArrowRing a₁' a₃' :=
  lift ⟨(algebraMap B _,
    universalChange a₁' a₃' * C₀.map (algebraMap B (ArrowRing a₁' a₃'))),
    isStrictGammaOneThreeChange_universalChange_mul_map hC₀ ha₁ ha₃⟩

@[simp]
private theorem shearHom_comp_algebraMap {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    (shearHom hC₀ ha₁ ha₃).comp (algebraMap B _) = algebraMap B _ := by
  rw [shearHom]
  exact lift_comp_algebraMap _

@[simp]
private theorem shearHom_algebraMap {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) (b : B) :
    shearHom hC₀ ha₁ ha₃ (algebraMap B _ b) = algebraMap B _ b := by
  rw [shearHom]
  exact lift_algebraMap _ b

@[simp]
private theorem universalChange_map_shearHom {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    (universalChange a₁ a₃).map (shearHom hC₀ ha₁ ha₃) =
      universalChange a₁' a₃' * C₀.map (algebraMap B _) := by
  rw [shearHom]
  exact map_lift _

private theorem shearHom_comp_shearHom_eq_id {a₁' a₃' : B} {C₁ C₂ : VariableChange B}
    (hC₁ : IsStrictGammaOneThreeChange a₁ a₃ C₁)
    (ha₁' : a₁' = a₁ + 2 * C₁.s) (ha₃' : a₃' = a₃ + C₁.r * a₁ + 2 * C₁.t)
    (hC₂ : IsStrictGammaOneThreeChange a₁' a₃' C₂)
    (ha₁ : a₁ = a₁' + 2 * C₂.s) (ha₃ : a₃ = a₃' + C₂.r * a₁' + 2 * C₂.t)
    (hC : C₂ * C₁ = 1) :
    (shearHom hC₂ ha₁ ha₃).comp (shearHom hC₁ ha₁' ha₃') = RingHom.id _ := by
  refine ringHom_ext (RingHom.ext fun b ↦ by simp) ?_
  rw [← VariableChange.map_map, universalChange_map_shearHom, VariableChange.map_mul]
  simp [VariableChange.map_map, mul_assoc, ← VariableChange.map_mul, hC]

/-- **Groupoid shearing equivalence**: if `C₀` is a strict `Γ₁(3)` arrow over `B` from
`gammaOneThreeForm a₁ a₃` to `gammaOneThreeForm a₁' a₃'`, then precomposing with `C₀` gives an
isomorphism of `B`-algebras `ArrowRing a₁ a₃ ≃ₐ[B] ArrowRing a₁' a₃'`. -/
def shearEquiv {a₁' a₃' : B} {C₀ : VariableChange B} (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    ArrowRing a₁ a₃ ≃ₐ[B] ArrowRing a₁' a₃' :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom
      (shearHom hC₀ ha₁ ha₃)
      (shearHom (hC₀.inv_of_eq ha₁ ha₃) (hC₀.eq_add_two_mul_inv_s ha₁)
        (hC₀.eq_add_inv_r_mul_add_two_mul_inv_t ha₁ ha₃))
      (shearHom_comp_shearHom_eq_id (hC₀.inv_of_eq ha₁ ha₃) (hC₀.eq_add_two_mul_inv_s ha₁)
        (hC₀.eq_add_inv_r_mul_add_two_mul_inv_t ha₁ ha₃) hC₀ ha₁ ha₃ (mul_inv_cancel C₀))
      (shearHom_comp_shearHom_eq_id hC₀ ha₁ ha₃ (hC₀.inv_of_eq ha₁ ha₃)
        (hC₀.eq_add_two_mul_inv_s ha₁) (hC₀.eq_add_inv_r_mul_add_two_mul_inv_t ha₁ ha₃)
        (inv_mul_cancel C₀)))
    (shearHom_algebraMap hC₀ ha₁ ha₃)

private theorem coe_ringHom_shearEquiv {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    (shearEquiv hC₀ ha₁ ha₃ : ArrowRing a₁ a₃ →+* ArrowRing a₁' a₃') = shearHom hC₀ ha₁ ha₃ :=
  RingHom.ext fun _ ↦ rfl

@[simp]
theorem universalChange_map_shearEquiv {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    (universalChange a₁ a₃).map
      (shearEquiv hC₀ ha₁ ha₃ : ArrowRing a₁ a₃ →+* ArrowRing a₁' a₃') =
      universalChange a₁' a₃' * C₀.map (algebraMap B _) := by
  rw [coe_ringHom_shearEquiv, universalChange_map_shearHom]

@[simp]
theorem shearEquiv_r {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    shearEquiv hC₀ ha₁ ha₃ r = r + algebraMap B (ArrowRing a₁' a₃') C₀.r := by
  rw [← universalChange_r, ← RingHom.coe_coe (shearEquiv hC₀ ha₁ ha₃), ← VariableChange.map_r,
    universalChange_map_shearEquiv]
  simp [VariableChange.mul_def, hC₀.u_eq_one]

@[simp]
theorem shearEquiv_s {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    shearEquiv hC₀ ha₁ ha₃ s = s + algebraMap B (ArrowRing a₁' a₃') C₀.s := by
  rw [← universalChange_s, ← RingHom.coe_coe (shearEquiv hC₀ ha₁ ha₃), ← VariableChange.map_s,
    universalChange_map_shearEquiv]
  simp [VariableChange.mul_def, hC₀.u_eq_one]

@[simp]
theorem shearEquiv_t {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    shearEquiv hC₀ ha₁ ha₃ t =
      t + r * algebraMap B (ArrowRing a₁' a₃') C₀.s + algebraMap B (ArrowRing a₁' a₃') C₀.t := by
  rw [← universalChange_t, ← RingHom.coe_coe (shearEquiv hC₀ ha₁ ha₃), ← VariableChange.map_t,
    universalChange_map_shearEquiv]
  simp [VariableChange.mul_def, hC₀.u_eq_one]

@[simp]
theorem shearEquiv_symm {a₁' a₃' : B} {C₀ : VariableChange B}
    (hC₀ : IsStrictGammaOneThreeChange a₁ a₃ C₀)
    (ha₁ : a₁' = a₁ + 2 * C₀.s) (ha₃ : a₃' = a₃ + C₀.r * a₁ + 2 * C₀.t) :
    (shearEquiv hC₀ ha₁ ha₃).symm =
      shearEquiv (hC₀.inv_of_eq ha₁ ha₃) (hC₀.eq_add_two_mul_inv_s ha₁)
        (hC₀.eq_add_inv_r_mul_add_two_mul_inv_t ha₁ ha₃) := by
  have hcomp :
      (shearEquiv hC₀ ha₁ ha₃ : ArrowRing a₁ a₃ →+* ArrowRing a₁' a₃').comp
        (shearEquiv (hC₀.inv_of_eq ha₁ ha₃) (hC₀.eq_add_two_mul_inv_s ha₁)
          (hC₀.eq_add_inv_r_mul_add_two_mul_inv_t ha₁ ha₃) :
            ArrowRing a₁' a₃' →+* ArrowRing a₁ a₃) = RingHom.id _ := by
    rw [coe_ringHom_shearEquiv, coe_ringHom_shearEquiv]
    exact shearHom_comp_shearHom_eq_id (hC₀.inv_of_eq ha₁ ha₃) (hC₀.eq_add_two_mul_inv_s ha₁)
      (hC₀.eq_add_inv_r_mul_add_two_mul_inv_t ha₁ ha₃) hC₀ ha₁ ha₃ (mul_inv_cancel C₀)
  ext x
  exact (shearEquiv hC₀ ha₁ ha₃).symm_apply_eq.mpr (RingHom.congr_fun hcomp x).symm

end Shear

/-! ### Base-change compatibility of the rank-`8` basis and `Algebra.trace` -/

section TraceMap

variable {B B' : Type*} [CommRing B] [CommRing B'] [Invertible (3 : B)] {a₁ a₃ : B}

/-- Base-change sends each element of `ArrowRing.basis` to the corresponding basis element. -/
theorem mapOfEq_basis [Invertible (3 : B')] {a₁' a₃' : B'}
    (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') (i : Fin 8) :
    mapOfEq f ha₁ ha₃ (basis a₁ a₃ i) = basis a₁' a₃' i := by
  fin_cases i <;> simp

/-- **Base-change compatibility of `Algebra.trace`** for `ArrowRing`. -/
theorem trace_mapOfEq {a₁' a₃' : B'}
    (f : B →+* B') (ha₁ : f a₁ = a₁') (ha₃ : f a₃ = a₃') (y : ArrowRing a₁ a₃) :
    Algebra.trace B' (ArrowRing a₁' a₃') (mapOfEq f ha₁ ha₃ y) =
      f (Algebra.trace B (ArrowRing a₁ a₃) y) := by
  let _ : Invertible (3 : B') := TauCeti.invertibleMapOfNat f 3
  have hf3 : f ⅟(3 : B) = ⅟(3 : B') := TauCeti.map_invOf_ofNat f 3
  rw [← (basis a₁ a₃).sum_repr y]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hmap : mapOfEq f ha₁ ha₃ (((basis a₁ a₃).repr y) i • basis a₁ a₃ i) =
      f (((basis a₁ a₃).repr y) i) • basis a₁' a₃' i :=
    (congrArg (mapOfEq f ha₁ ha₃) (Algebra.smul_def _ _)).trans <| by
      rw [map_mul, mapOfEq_algebraMap, mapOfEq_basis, ← Algebra.smul_def]
  rw [hmap, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  congr 1
  rw [trace_basis, trace_basis]
  fin_cases i <;> simp [hf3, ha₁, ha₃, map_ofNat]

/-- Base-change compatibility of `Algebra.trace` along `ArrowRing.map f`. -/
theorem trace_map (f : B →+* B') (y : ArrowRing a₁ a₃) :
    Algebra.trace B' (ArrowRing (f a₁) (f a₃)) (map f y) =
      f (Algebra.trace B (ArrowRing a₁ a₃) y) :=
  trace_mapOfEq f rfl rfl y

end TraceMap

end ArrowRing

end TauCeti.GammaOneThreeHopfAlgebroid

end
