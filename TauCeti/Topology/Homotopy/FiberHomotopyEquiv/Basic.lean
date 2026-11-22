/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.ContinuousMap.RestrictPreimage
public import TauCeti.Topology.Constructions.Basic

/-!
# Fibre homotopy equivalences

For maps `p : E → B` and `q : E' → B`, a **fibre homotopy equivalence** from `p` to `q` is a pair
of maps `f : E → E'` and `g : E' → E` over `B` (`q ∘ f = p`, `p ∘ g = q`) whose two composites are
homotopic to the identities through maps over `B` (`ContinuousMap.HomotopicWith` with the predicate
"over `B`").  Since every stage of such a homotopy maps each fibre into itself, a fibre homotopy
equivalence restricts to a homotopy equivalence of the fibres over each point
(`TauCeti.FiberHomotopyEquiv.fiber`).

## Main definitions

* `TauCeti.FiberHomotopyEquiv p q`: fibre homotopy equivalences from `p` to `q`.
* `TauCeti.fiberMap`: the map of fibres induced by a map over `B`, the case `S = {b}` of
  `TauCeti.restrictPreimageMap`.
* `TauCeti.restrictPreimageHomotopyWith`: a homotopy over `B` restricted to the preimages of a
  subset `S` of `B`.
* `TauCeti.FiberHomotopyEquiv.refl`, `TauCeti.FiberHomotopyEquiv.symm`,
  `TauCeti.FiberHomotopyEquiv.trans`: identity, symmetry, and composition of fibre homotopy
  equivalences.
* `TauCeti.FiberHomotopyEquiv.ofHomeomorph`: a homeomorphism over `B` as a fibre homotopy
  equivalence.
* `TauCeti.FiberHomotopyEquiv.compBase`: postcomposing the base projections with `b : C(B, B')`.
* `TauCeti.FiberHomotopyEquiv.restrictPreimage`: the fibre homotopy equivalence over a subset `S`
  of `B` between the preimages of `S`.
* `TauCeti.FiberHomotopyEquiv.pullback`: base change along `f : A → B` to a fibre homotopy
  equivalence over `A`.
* `TauCeti.FiberHomotopyEquiv.fiber`: the homotopy equivalence of the fibres over a point.
* `TauCeti.FiberHomotopyEquiv.toHomotopyEquiv`: the underlying homotopy equivalence of the total
  spaces.

## Main results

* `ContinuousMap.homotopic_of_fiber`: a homotopy of maps to the total space staying over one point
  is a homotopy of maps into the fiber.

## Implementation notes

The fibres are stated as subtypes `{e // p e = b}`, while the general restriction to preimages
(`TauCeti.restrictPreimageMap`, `TauCeti.restrictPreimageHomotopyWith`,
`TauCeti.FiberHomotopyEquiv.restrictPreimage`) is stated over `↥(p ⁻¹' S)`. For `S = {b}` the two
types are definitionally equal: `↥(p ⁻¹' {b})` is `{e // e ∈ p ⁻¹' {b}}`, and unfolding
`Set.preimage`, set membership and `Set.singleton` reduces `e ∈ p ⁻¹' {b}` to `p e = b`. The
fibre declarations (`fiberMap`, `fiberHomotopy`, `FiberHomotopyEquiv.fiber`) and their lemmas use
this equality to be literally the singleton cases of the general ones, with no transport.
-/

public section

open ContinuousMap unitInterval

universe u u' u'' v

namespace TauCeti

variable {E : Type u} {E' : Type u'} {E'' : Type u''} {B : Type v} [TopologicalSpace E]
  [TopologicalSpace E'] [TopologicalSpace E''] [TopologicalSpace B]

/-- A **fibre homotopy equivalence** from `p : E → B` to `q : E' → B`: maps over `B` in both
directions whose composites are homotopic to the identities through maps over `B`. -/
structure FiberHomotopyEquiv (p : C(E, B)) (q : C(E', B)) where
  /-- The forward map, over `B`. -/
  toFun : C(E, E')
  /-- The backward map, over `B`. -/
  invFun : C(E', E)
  /-- The forward map lies over `B`. -/
  comp_toFun : q.comp toFun = p
  /-- The backward map lies over `B`. -/
  comp_invFun : p.comp invFun = q
  /-- The composite on `E` is homotopic to the identity through maps over `B`. -/
  left_inv : (invFun.comp toFun).HomotopicWith (.id E) fun f ↦ p.comp f = p
  /-- The composite on `E'` is homotopic to the identity through maps over `B`. -/
  right_inv : (toFun.comp invFun).HomotopicWith (.id E') fun f ↦ q.comp f = q

theorem apply_of_comp_eq {p : C(E, B)} {q : C(E', B)} {f : C(E, E')} (hf : q.comp f = p)
    {b : B} (e : {e // p e = b}) : q (f e) = b := by
  rw [← ContinuousMap.comp_apply, hf, e.property]

/-- The map of fibres over `b` induced by a map `f` over `B`. -/
-- The body has type `C(p ⁻¹' {b}, q ⁻¹' {b})`, definitionally equal to the stated type; see the
-- implementation notes in the module docstring.
def fiberMap {p : C(E, B)} {q : C(E', B)} (f : C(E, E')) (hf : q.comp f = p) (b : B) :
    C({e // p e = b}, {e' // q e' = b}) :=
  restrictPreimageMap {b} hf

@[simp]
theorem coe_fiberMap {p : C(E, B)} {q : C(E', B)} (f : C(E, E')) (hf : q.comp f = p) (b : B)
    (e : {e // p e = b}) : (fiberMap f hf b e : E') = f e :=
  coe_restrictPreimageMap {b} hf e

theorem fiberMap_comp {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)} (f : C(E, E'))
    (g : C(E', E'')) (hf : q.comp f = p) (hg : r.comp g = q) (b : B) :
    (fiberMap g hg b).comp (fiberMap f hf b) =
      fiberMap (g.comp f) (by rw [← ContinuousMap.comp_assoc, hg, hf]) b :=
  restrictPreimageMap_comp {b} hf hg

theorem fiberMap_id {p : C(E, B)} (b : B) :
    fiberMap (.id E) (ContinuousMap.comp_id p) b = .id _ :=
  restrictPreimageMap_id {b}

theorem apply_homotopyWith {p : C(E, B)} {f₀ f₁ : C(E, E)}
    (H : HomotopyWith f₀ f₁ fun f ↦ p.comp f = p) (t : I) (e : E) : p (H (t, e)) = p e :=
  congr($(H.prop' t) e)

/-- A homotopy through maps over `B` restricts to a homotopy through maps over `S` between the
restrictions to the preimage of `S`. -/
def restrictPreimageHomotopyWith {p : C(E, B)} (S : Set B) {f₀ f₁ : C(E, E)}
    (H : HomotopyWith f₀ f₁ fun f ↦ p.comp f = p) (h₀ : p.comp f₀ = p) (h₁ : p.comp f₁ = p) :
    HomotopyWith (restrictPreimageMap S h₀) (restrictPreimageMap S h₁)
      fun f ↦ (p.restrictPreimage S).comp f = p.restrictPreimage S where
  toFun x := ⟨H (x.1, x.2.val), by
    rw [Set.mem_preimage, apply_homotopyWith H]
    exact x.2.property⟩
  continuous_toFun := by fun_prop
  map_zero_left e := Subtype.ext ((H.apply_zero e).trans (coe_restrictPreimageMap S h₀ e).symm)
  map_one_left e := Subtype.ext ((H.apply_one e).trans (coe_restrictPreimageMap S h₁ e).symm)
  prop' t := ContinuousMap.ext fun e ↦ Subtype.ext (apply_homotopyWith H t e)

/-- A homotopy through maps over `B` restricts to a homotopy of the induced maps of the fibres. -/
def fiberHomotopy {p : C(E, B)} {f₀ f₁ : C(E, E)}
    (H : HomotopyWith f₀ f₁ fun f ↦ p.comp f = p) (h₀ : p.comp f₀ = p) (h₁ : p.comp f₁ = p)
    (b : B) : Homotopy (fiberMap f₀ h₀ b) (fiberMap f₁ h₁ b) :=
  (restrictPreimageHomotopyWith {b} H h₀ h₁).toHomotopy

namespace FiberHomotopyEquiv

section

variable {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q)

/-- Forgetting that the maps and homotopies lie over `B`, a fibre homotopy equivalence is a
**homotopy equivalence of the total spaces**. -/
def toHomotopyEquiv : HomotopyEquiv E E' where
  toFun := Φ.toFun
  invFun := Φ.invFun
  left_inv := ⟨Φ.left_inv.some.toHomotopy⟩
  right_inv := ⟨Φ.right_inv.some.toHomotopy⟩

@[simp]
theorem toHomotopyEquiv_apply (e : E) : Φ.toHomotopyEquiv e = Φ.toFun e :=
  (rfl)

@[simp]
theorem toHomotopyEquiv_symm_apply (e' : E') : Φ.toHomotopyEquiv.symm e' = Φ.invFun e' :=
  (rfl)

end

/-- The identity fibre homotopy equivalence of `p : C(E, B)`. -/
def refl (p : C(E, B)) : FiberHomotopyEquiv p p where
  toFun := .id E
  invFun := .id E
  comp_toFun := p.comp_id
  comp_invFun := p.comp_id
  left_inv := ⟨(HomotopyWith.refl (.id E) p.comp_id).cast (ContinuousMap.comp_id _).symm rfl⟩
  right_inv := ⟨(HomotopyWith.refl (.id E) p.comp_id).cast (ContinuousMap.comp_id _).symm rfl⟩

@[simp]
theorem refl_toFun (p : C(E, B)) : (refl p).toFun = .id E :=
  (rfl)

@[simp]
theorem refl_invFun (p : C(E, B)) : (refl p).invFun = .id E :=
  (rfl)

/-- Symmetry of fibre homotopy equivalences. -/
@[symm]
def symm {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) : FiberHomotopyEquiv q p where
  toFun := Φ.invFun
  invFun := Φ.toFun
  comp_toFun := Φ.comp_invFun
  comp_invFun := Φ.comp_toFun
  left_inv := Φ.right_inv
  right_inv := Φ.left_inv

@[simp]
theorem symm_toFun {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) :
    Φ.symm.toFun = Φ.invFun :=
  (rfl)

@[simp]
theorem symm_invFun {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) :
    Φ.symm.invFun = Φ.toFun :=
  (rfl)

@[simp]
theorem symm_symm {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) :
    Φ.symm.symm = Φ :=
  (rfl)

/-- A homeomorphism `e : E ≃ₜ E'` commuting with the projections to `B` is a fibre homotopy
equivalence. -/
def ofHomeomorph {p : C(E, B)} {q : C(E', B)} (e : E ≃ₜ E')
    (he : q.comp (e : C(E, E')) = p) : FiberHomotopyEquiv p q where
  toFun := e
  invFun := e.symm
  comp_toFun := he
  comp_invFun := ContinuousMap.ext fun x ↦ by simp [← he]
  left_inv :=
    ⟨(HomotopyWith.refl (.id E) p.comp_id).cast
      (ContinuousMap.ext fun x ↦ (e.symm_apply_apply x).symm) rfl⟩
  right_inv :=
    ⟨(HomotopyWith.refl (.id E') q.comp_id).cast
      (ContinuousMap.ext fun x ↦ (e.apply_symm_apply x).symm) rfl⟩

@[simp]
theorem ofHomeomorph_toFun {p : C(E, B)} {q : C(E', B)} (e : E ≃ₜ E')
    (he : q.comp (e : C(E, E')) = p) : (ofHomeomorph e he).toFun = (e : C(E, E')) :=
  (rfl)

@[simp]
theorem ofHomeomorph_invFun {p : C(E, B)} {q : C(E', B)} (e : E ≃ₜ E')
    (he : q.comp (e : C(E, E')) = p) : (ofHomeomorph e he).invFun = (e.symm : C(E', E)) :=
  (rfl)

private theorem homotopicWith_comp_conj {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) :
    ((Φ.invFun.comp Ψ.invFun).comp (Ψ.toFun.comp Φ.toFun)).HomotopicWith (.id E)
      fun f ↦ p.comp f = p := by
  refine (?_ : HomotopicWith _ (Φ.invFun.comp Φ.toFun) _).trans Φ.left_inv
  obtain ⟨H⟩ := Ψ.left_inv
  exact ⟨{
    toFun := fun x ↦ Φ.invFun (H (x.1, Φ.toFun x.2))
    continuous_toFun := by fun_prop
    map_zero_left := fun _ ↦ by simp [ContinuousMap.comp_apply]
    map_one_left := fun _ ↦ by simp [ContinuousMap.comp_apply]
    prop' := fun t ↦ ContinuousMap.ext fun e ↦ by
      have h1 : p (Φ.invFun (H (t, Φ.toFun e))) = q (H (t, Φ.toFun e)) :=
        congr($(Φ.comp_invFun) (H (t, Φ.toFun e)))
      have h2 : q (H (t, Φ.toFun e)) = q (Φ.toFun e) := apply_homotopyWith H t (Φ.toFun e)
      have h3 : q (Φ.toFun e) = p e := congr($(Φ.comp_toFun) e)
      exact h1.trans (h2.trans h3) }⟩

/-- Composition of fibre homotopy equivalences over `B`. -/
@[trans]
def trans {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) : FiberHomotopyEquiv p r where
  toFun := Ψ.toFun.comp Φ.toFun
  invFun := Φ.invFun.comp Ψ.invFun
  comp_toFun := by rw [← ContinuousMap.comp_assoc, Ψ.comp_toFun, Φ.comp_toFun]
  comp_invFun := by rw [← ContinuousMap.comp_assoc, Φ.comp_invFun, Ψ.comp_invFun]
  left_inv := homotopicWith_comp_conj Φ Ψ
  right_inv := homotopicWith_comp_conj Ψ.symm Φ.symm

@[simp]
theorem trans_toFun {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) :
    (Φ.trans Ψ).toFun = Ψ.toFun.comp Φ.toFun :=
  (rfl)

@[simp]
theorem trans_invFun {p : C(E, B)} {q : C(E', B)} {r : C(E'', B)}
    (Φ : FiberHomotopyEquiv p q) (Ψ : FiberHomotopyEquiv q r) :
    (Φ.trans Ψ).invFun = Φ.invFun.comp Ψ.invFun :=
  (rfl)

/-- Postcomposing both base projections with `b : C(B, B')` carries a fibre homotopy equivalence
over `B` to one over `B'`. -/
def compBase {B' : Type*} [TopologicalSpace B'] {p : C(E, B)} {q : C(E', B)}
    (b : C(B, B')) (Φ : FiberHomotopyEquiv p q) :
    FiberHomotopyEquiv (b.comp p) (b.comp q) where
  toFun := Φ.toFun
  invFun := Φ.invFun
  comp_toFun := by rw [ContinuousMap.comp_assoc, Φ.comp_toFun]
  comp_invFun := by rw [ContinuousMap.comp_assoc, Φ.comp_invFun]
  left_inv := Φ.left_inv.map fun H ↦
    { toHomotopy := H.toHomotopy
      prop' := fun t ↦ ContinuousMap.ext fun e ↦ congrArg b (apply_homotopyWith H t e) }
  right_inv := Φ.right_inv.map fun H ↦
    { toHomotopy := H.toHomotopy
      prop' := fun t ↦ ContinuousMap.ext fun e ↦ congrArg b (apply_homotopyWith H t e) }

@[simp]
theorem compBase_toFun {B' : Type*} [TopologicalSpace B'] {p : C(E, B)} {q : C(E', B)}
    (b : C(B, B')) (Φ : FiberHomotopyEquiv p q) :
    (Φ.compBase b).toFun = Φ.toFun :=
  (rfl)

@[simp]
theorem compBase_invFun {B' : Type*} [TopologicalSpace B'] {p : C(E, B)} {q : C(E', B)}
    (b : C(B, B')) (Φ : FiberHomotopyEquiv p q) :
    (Φ.compBase b).invFun = Φ.invFun :=
  (rfl)

section RestrictPreimage

/-- A fibre homotopy equivalence over `B` restricts to a **fibre homotopy equivalence over a
subset** `S` of `B`, between the preimages `p⁻¹(S)` and `q⁻¹(S)` projecting to `S`. -/
def restrictPreimage {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) (S : Set B) :
    FiberHomotopyEquiv (p.restrictPreimage S) (q.restrictPreimage S) where
  toFun := restrictPreimageMap S Φ.comp_toFun
  invFun := restrictPreimageMap S Φ.comp_invFun
  comp_toFun := ContinuousMap.ext fun e ↦ Subtype.ext <|
    (congrArg q (coe_restrictPreimageMap S Φ.comp_toFun e)).trans congr($(Φ.comp_toFun) e)
  comp_invFun := ContinuousMap.ext fun e ↦ Subtype.ext <|
    (congrArg p (coe_restrictPreimageMap S Φ.comp_invFun e)).trans congr($(Φ.comp_invFun) e)
  left_inv := by
    rw [restrictPreimageMap_comp, ← restrictPreimageMap_id S]
    exact Φ.left_inv.map fun H ↦ restrictPreimageHomotopyWith S H _ _
  right_inv := by
    rw [restrictPreimageMap_comp, ← restrictPreimageMap_id S]
    exact Φ.right_inv.map fun H ↦ restrictPreimageHomotopyWith S H _ _

@[simp]
theorem restrictPreimage_toFun {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q)
    (S : Set B) : (Φ.restrictPreimage S).toFun = restrictPreimageMap S Φ.comp_toFun :=
  (rfl)

@[simp]
theorem restrictPreimage_invFun {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q)
    (S : Set B) : (Φ.restrictPreimage S).invFun = restrictPreimageMap S Φ.comp_invFun :=
  (rfl)

theorem coe_restrictPreimage_toFun_apply {p : C(E, B)} {q : C(E', B)}
    (Φ : FiberHomotopyEquiv p q) (S : Set B) (e : p ⁻¹' S) :
    ((Φ.restrictPreimage S).toFun e : E') = Φ.toFun e :=
  coe_restrictPreimageMap S Φ.comp_toFun e

theorem coe_restrictPreimage_invFun_apply {p : C(E, B)} {q : C(E', B)}
    (Φ : FiberHomotopyEquiv p q) (S : Set B) (e' : q ⁻¹' S) :
    ((Φ.restrictPreimage S).invFun e' : E) = Φ.invFun e' :=
  coe_restrictPreimageMap S Φ.comp_invFun e'

/-- A fibre homotopy equivalence restricts to a **homotopy equivalence of the fibres** over each
point of the base: the case `S = {b}` of `restrictPreimage`. -/
def fiber {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) (b : B) :
    HomotopyEquiv {e // p e = b} {e' // q e' = b} :=
  (Φ.restrictPreimage {b}).toHomotopyEquiv

@[simp]
theorem coe_fiber_apply {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) (b : B)
    (e : {e // p e = b}) : (Φ.fiber b e : E') = Φ.toFun e :=
  coe_restrictPreimage_toFun_apply Φ {b} e

@[simp]
theorem coe_fiber_symm_apply {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) (b : B)
    (e' : {e' // q e' = b}) : ((Φ.fiber b).symm e' : E) = Φ.invFun e' :=
  coe_restrictPreimage_invFun_apply Φ {b} e'

end RestrictPreimage
private theorem homotopicWith_pullback {A : Type*} [TopologicalSpace A] {p : C(E, B)}
    {q : C(E', B)} (f : A → B) (Φ : FiberHomotopyEquiv p q) :
    ((ContinuousMap.mapPullbackSnd f Φ.invFun (congrArg DFunLike.coe Φ.comp_invFun)).comp
      (ContinuousMap.mapPullbackSnd f Φ.toFun (congrArg DFunLike.coe Φ.comp_toFun))).HomotopicWith
      (.id _)
      fun h ↦ (ContinuousMap.pullbackFst f (⇑p)).comp h =
        ContinuousMap.pullbackFst f (⇑p) :=
  Φ.left_inv.map fun H ↦
    { toFun y := ⟨(y.2.val.1, H (y.1, y.2.val.2)),
        y.2.property.trans (apply_homotopyWith H y.1 y.2.val.2).symm⟩
      continuous_toFun := (continuous_snd.subtypeVal.fst.prodMk
        (H.continuous.comp (continuous_fst.prodMk continuous_snd.subtypeVal.snd))).subtype_mk _
      map_zero_left x := Subtype.ext (by simp [H.apply_zero x.val.2])
      map_one_left x := Subtype.ext (Prod.ext rfl (H.apply_one x.val.2))
      prop' _ := ContinuousMap.ext fun _ ↦ by simp [Function.Pullback.fst] }

/-- Base change along `f : A → B` carries a fibre homotopy equivalence over `B` to one over
`A`. -/
def pullback {A : Type*} [TopologicalSpace A] {p : C(E, B)} {q : C(E', B)}
    (f : A → B) (Φ : FiberHomotopyEquiv p q) :
    FiberHomotopyEquiv (ContinuousMap.pullbackFst f (⇑p))
      (ContinuousMap.pullbackFst f (⇑q)) where
  toFun := ContinuousMap.mapPullbackSnd f Φ.toFun (congrArg DFunLike.coe Φ.comp_toFun)
  invFun := ContinuousMap.mapPullbackSnd f Φ.invFun (congrArg DFunLike.coe Φ.comp_invFun)
  comp_toFun := by simp
  comp_invFun := by simp
  left_inv := homotopicWith_pullback f Φ
  right_inv := homotopicWith_pullback f Φ.symm

@[simp]
theorem pullback_toFun {A : Type*} [TopologicalSpace A] {p : C(E, B)} {q : C(E', B)}
    (f : A → B) (Φ : FiberHomotopyEquiv p q) :
    (Φ.pullback f).toFun =
      ContinuousMap.mapPullbackSnd f Φ.toFun (congrArg DFunLike.coe Φ.comp_toFun) :=
  (rfl)

@[simp]
theorem pullback_invFun {A : Type*} [TopologicalSpace A] {p : C(E, B)} {q : C(E', B)}
    (f : A → B) (Φ : FiberHomotopyEquiv p q) :
    (Φ.pullback f).invFun =
      ContinuousMap.mapPullbackSnd f Φ.invFun (congrArg DFunLike.coe Φ.comp_invFun) :=
  (rfl)

theorem coe_pullback_toFun_apply {A : Type*} [TopologicalSpace A] {p : C(E, B)} {q : C(E', B)}
    (f : A → B) (Φ : FiberHomotopyEquiv p q) (x : f.Pullback ⇑p) :
    ((Φ.pullback f).toFun x).val = (x.val.1, Φ.toFun x.val.2) := by
  simp

theorem coe_pullback_invFun_apply {A : Type*} [TopologicalSpace A] {p : C(E, B)} {q : C(E', B)}
    (f : A → B) (Φ : FiberHomotopyEquiv p q) (x : f.Pullback ⇑q) :
    ((Φ.pullback f).invFun x).val = (x.val.1, Φ.invFun x.val.2) := by
  simp

end FiberHomotopyEquiv

end TauCeti

namespace ContinuousMap

/-- A homotopy of maps to the total space of a map `p`, staying over a fixed point `b`, gives a
homotopy of maps into the fiber over `b`. -/
theorem homotopic_of_fiber {E B Y : Type*} [TopologicalSpace E]
    [TopologicalSpace Y] {p : E → B} {b : B} (f g : C(Y, p ⁻¹' {b}))
    (K : C(Y × I, E)) (h₀ : ∀ y, K (y, 0) = f y) (h₁ : ∀ y, K (y, 1) = g y)
    (hK : ∀ y s, p (K (y, s)) = b) : f.Homotopic g :=
  ⟨{ toFun := fun z ↦ ⟨K (z.2, z.1), hK z.2 z.1⟩
     continuous_toFun := by fun_prop
     map_zero_left := fun y ↦ Subtype.ext (h₀ y)
     map_one_left := fun y ↦ Subtype.ext (h₁ y) }⟩

end ContinuousMap

