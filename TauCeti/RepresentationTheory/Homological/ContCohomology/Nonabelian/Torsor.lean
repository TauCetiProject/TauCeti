/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Torsor
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# Equivariant torsors and continuous nonabelian first cohomology

Let a group `G` with a topology act continuously by group automorphisms on a topological group
`A`. A **`(G, A)`-torsor** is a topological right `A`-torsor `P`, written as a topological torsor
`Torsor Aᵐᵒᵖ P` with `IsTopologicalTorsor P`, so that `p · a` is `MulOpposite.op a • p`, together
with a continuous left action of `G` that is **semilinear**:

`g • (p · a) = (g • p) · (g • a)`.

A point `p` of such a torsor gives a continuous cocycle `c_p`, the unique map with
`g • p = p · c_p g`. Moving the point to `p · a` replaces `c_p` by its twist
`g ↦ a⁻¹ * c_p g * g • a`, and an isomorphism of torsors (a homeomorphism respecting both actions)
preserves it, so the class `[P] = [c_p]` of `H¹(G, A)` depends only on the isomorphism class of
`P`. Conversely, a cocycle `c` gives the torsor `A` with right multiplication and the twisted
action `g ⋆ x = c g * g • x`, whose point `1` has cocycle `c`. This is the classification of
`(G, A)`-torsors by `H¹(G, A)`: torsors are isomorphic exactly when their classes agree, every
class is the class of a torsor, and a torsor has a `G`-fixed point exactly when its class is the
base point.

For a curve `X` with base point `b`, the torsor of étale (or unipotent) paths from `b` to a
rational point `x` is a torsor of this kind under the fundamental group at `b`, with `G` the
absolute Galois group; its class is the path class of `x` used in nonabelian Chabauty.

## Main definitions

* `TauCeti.NonabelianH1.IsSemilinearTorsor G A P`: the action of `G` on the right `A`-torsor `P`
  is semilinear.
* `TauCeti.NonabelianH1.TorsorEquiv G A P Q`: isomorphisms of `(G, A)`-torsors, homeomorphisms
  respecting both actions.
* `TauCeti.NonabelianH1.Cocycle.ofPoint G p`: the cocycle `c_p` of a point `p`.
* `TauCeti.NonabelianH1.Cocycle.TorsorModel c`: the torsor `A` with the action
  `g ⋆ x = c g * g • x` defined by a cocycle `c`.
* `TauCeti.NonabelianH1.ofTorsor G P`: the class `[P]` of a torsor in `H¹(G, A)`.
* `TauCeti.NonabelianH1.BundledTorsor G A`: `(G, A)`-torsors bundled with their carrier, with
  the setoid of isomorphism.
* `TauCeti.NonabelianH1.torsorClassEquiv`: the bijection between isomorphism classes of
  `(G, A)`-torsors and `H¹(G, A)`.

## Main results

* `TauCeti.NonabelianH1.Cocycle.ofPoint_op_smul`: `c_{p · a}` is the twist of `c_p` by `a`.
* `TauCeti.NonabelianH1.Cocycle.ofPoint_map`: isomorphisms of torsors preserve the cocycle of a
  point.
* `TauCeti.NonabelianH1.ofTorsor_eq_ofTorsor_iff`: two torsors have the same class exactly when
  they are isomorphic.
* `TauCeti.NonabelianH1.ofTorsor_torsorModel`: the torsor of a cocycle has the class of that
  cocycle.
* `TauCeti.NonabelianH1.ofTorsor_eq_one_iff`: a torsor has a `G`-fixed point exactly when its
  class is the base point.

## References

* M. Kim, *The motivic fundamental group of `P¹ ∖ {0, 1, ∞}` and the theorem of Siegel*,
  Invent. Math. 161 (2005), §1, Proposition 1 and its proof.
* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.2, Proposition 33.
-/

public section

open MulOpposite

namespace TauCeti

namespace NonabelianH1

universe u v w

variable {G : Type u} {A : Type v} [Group G] [Group A]

section Semilinear

variable (G A) (P : Type*) [MulDistribMulAction G A] [Torsor Aᵐᵒᵖ P] [MulAction G P]

/-- The action of `G` on a right `A`-torsor `P` is **semilinear**:
`g • (p · a) = (g • p) · (g • a)`, where `p · a` is `MulOpposite.op a • p`. -/
class IsSemilinearTorsor : Prop where
  /-- The action of `G` is semilinear for the right action of `A`. -/
  smul_op_smul (g : G) (a : A) (p : P) : g • (op a • p) = op (g • a) • g • p

variable {G A P} [IsSemilinearTorsor G A P] in
/-- The difference of the `G`-translates of two points is the `G`-translate of their
difference. -/
theorem IsSemilinearTorsor.smul_sdiv_smul (g : G) (p q : P) :
    (g • p) /ₛ (g • q) = op (g • unop (p /ₛ q)) :=
  (eq_smul_iff_sdiv_eq _ _ _).mp <| by rw [← smul_op_smul, op_unop, sdiv_smul]

end Semilinear

section TorsorEquiv

variable (G A) (P Q R : Type*) [TopologicalSpace P] [Torsor Aᵐᵒᵖ P] [MulAction G P]
  [TopologicalSpace Q] [Torsor Aᵐᵒᵖ Q] [MulAction G Q]
  [TopologicalSpace R] [Torsor Aᵐᵒᵖ R] [MulAction G R]

/-- An **isomorphism of `(G, A)`-torsors**: a homeomorphism `P ≃ₜ Q` commuting with the right
action of `A` and the action of `G`. -/
structure TorsorEquiv extends P ≃ₜ Q where
  /-- An isomorphism of torsors commutes with the right action of `A`. -/
  map_op_smul' (a : Aᵐᵒᵖ) (p : P) : toFun (a • p) = a • toFun p
  /-- An isomorphism of torsors commutes with the action of `G`. -/
  map_smul' (g : G) (p : P) : toFun (g • p) = g • toFun p

namespace TorsorEquiv

variable {G A P Q R}

instance : EquivLike (TorsorEquiv G A P Q) P Q where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h _ := by
    obtain ⟨⟨⟨_, _, _, _⟩, _, _⟩, _, _⟩ := e
    obtain ⟨⟨⟨_, _, _, _⟩, _, _⟩, _, _⟩ := e'
    congr

@[ext]
theorem ext {e e' : TorsorEquiv G A P Q} (h : ∀ p, e p = e' p) : e = e' :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toHomeomorph (e : TorsorEquiv G A P Q) : ⇑e.toHomeomorph = e :=
  (rfl)

/-- An isomorphism of torsors commutes with the right action of `A`. -/
@[simp]
theorem map_op_smul (e : TorsorEquiv G A P Q) (a : Aᵐᵒᵖ) (p : P) : e (a • p) = a • e p :=
  e.map_op_smul' a p

/-- An isomorphism of torsors commutes with the action of `G`. -/
@[simp]
theorem map_smul (e : TorsorEquiv G A P Q) (g : G) (p : P) : e (g • p) = g • e p :=
  e.map_smul' g p

variable (G A P) in
/-- The identity isomorphism of a torsor. -/
def refl : TorsorEquiv G A P P where
  toHomeomorph := .refl P
  map_op_smul' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_refl : ⇑(refl G A P) = id :=
  (rfl)

/-- The inverse of an isomorphism of torsors. -/
def symm (e : TorsorEquiv G A P Q) : TorsorEquiv G A Q P where
  toHomeomorph := e.toHomeomorph.symm
  map_op_smul' a q := e.toHomeomorph.symm_apply_eq.mpr <| by
    rw [coe_toHomeomorph, map_op_smul]
    exact (congrArg (a • ·) (e.toHomeomorph.apply_symm_apply q)).symm
  map_smul' g q := e.toHomeomorph.symm_apply_eq.mpr <| by
    rw [coe_toHomeomorph, map_smul]
    exact (congrArg (g • ·) (e.toHomeomorph.apply_symm_apply q)).symm

@[simp]
theorem apply_symm_apply (e : TorsorEquiv G A P Q) (q : Q) : e (e.symm q) = q :=
  e.toHomeomorph.apply_symm_apply q

@[simp]
theorem symm_apply_apply (e : TorsorEquiv G A P Q) (p : P) : e.symm (e p) = p :=
  e.toHomeomorph.symm_apply_apply p

/-- The composite of two isomorphisms of torsors. -/
def trans (e : TorsorEquiv G A P Q) (e' : TorsorEquiv G A Q R) : TorsorEquiv G A P R where
  toHomeomorph := e.toHomeomorph.trans e'.toHomeomorph
  map_op_smul' a p := by simp
  map_smul' g p := by simp

@[simp]
theorem trans_apply (e : TorsorEquiv G A P Q) (e' : TorsorEquiv G A Q R) (p : P) :
    e.trans e' p = e' (e p) :=
  (rfl)

@[simp]
theorem toHomeomorph_symm (e : TorsorEquiv G A P Q) : e.symm.toHomeomorph = e.toHomeomorph.symm :=
  (rfl)

@[simp]
theorem symm_symm (e : TorsorEquiv G A P Q) : e.symm.symm = e :=
  (rfl)

@[simp]
theorem refl_symm : (refl G A P).symm = refl G A P :=
  (rfl)

@[simp]
theorem trans_refl (e : TorsorEquiv G A P Q) : e.trans (refl G A Q) = e :=
  (rfl)

@[simp]
theorem refl_trans (e : TorsorEquiv G A P Q) : (refl G A P).trans e = e :=
  (rfl)

end TorsorEquiv

end TorsorEquiv

variable [TopologicalSpace G] [TopologicalSpace A] [MulDistribMulAction G A]

section Point

variable {P Q : Type*} [TopologicalSpace P] [Torsor Aᵐᵒᵖ P] [IsTopologicalTorsor P]
  [MulAction G P] [ContinuousSMul G P] [IsSemilinearTorsor G A P]
  [TopologicalSpace Q] [Torsor Aᵐᵒᵖ Q] [IsTopologicalTorsor Q]
  [MulAction G Q] [ContinuousSMul G Q] [IsSemilinearTorsor G A Q]

namespace Cocycle

variable (G) in
/-- The **cocycle of a point** `p` of a `(G, A)`-torsor: the continuous cocycle `c_p` with
`g • p = p · c_p g` (`TauCeti.NonabelianH1.Cocycle.op_ofPoint_smul`). -/
def ofPoint (p : P) : Cocycle G A where
  toFun g := unop ((g • p) /ₛ p)
  continuous_toFun := by fun_prop
  map_mul' g h := op_injective <| by
    rw [op_mul, op_unop, op_unop, ← IsSemilinearTorsor.smul_sdiv_smul, sdiv_mul_sdiv_cancel,
      mul_smul]

theorem ofPoint_apply (p : P) (g : G) : ofPoint G p g = unop ((g • p) /ₛ p) :=
  (rfl)

/-- The defining property of the cocycle of a point: `g • p = p · c_p g`. -/
@[simp]
theorem op_ofPoint_smul (p : P) (g : G) : op (ofPoint G p g) • p = g • p :=
  sdiv_smul _ _

/-- The cocycle of a point is the unique map with `g • p = p · c_p g`. -/
theorem ofPoint_apply_eq_iff {p : P} {g : G} {a : A} : ofPoint G p g = a ↔ g • p = op a • p := by
  rw [← op_ofPoint_smul, smul_right_cancel_iff, op_inj]

/-- The difference of a `G`-translate and a point, in terms of the cocycle of the point. -/
theorem smul_sdiv_eq_mul_op_ofPoint (g : G) (p q : P) :
    (g • p) /ₛ q = op (g • unop (p /ₛ q)) * op (ofPoint G q g) := by
  rw [← IsSemilinearTorsor.smul_sdiv_smul, ofPoint_apply, op_unop, sdiv_mul_sdiv_cancel]

/-- A point is fixed by `G` exactly when its cocycle is trivial. -/
theorem ofPoint_eq_one_iff {p : P} : ofPoint G p = 1 ↔ ∀ g : G, g • p = p := by
  simp only [Cocycle.ext_iff, one_apply, ofPoint_apply_eq_iff, op_one, one_smul]

/-- **Change of point**: the cocycle of `p · a` is the twist of the cocycle of `p` by `a`. -/
theorem ofPoint_op_smul [ContinuousMul A] [ContinuousSMul G A] (p : P) (a : A) :
    ofPoint G (op a • p) = (ofPoint G p).twist a := by
  ext g
  rw [ofPoint_apply_eq_iff, IsSemilinearTorsor.smul_op_smul, ← op_ofPoint_smul p g]
  simp only [twist_apply, ← mul_smul, op_mul, op_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- An isomorphism of torsors preserves the cocycle of a point. -/
@[simp]
theorem ofPoint_map (e : TorsorEquiv G A P Q) (p : P) : ofPoint G (e p) = ofPoint G p := by
  ext g
  rw [ofPoint_apply_eq_iff, ← e.map_smul, ← op_ofPoint_smul p g, e.map_op_smul]

end Cocycle

namespace TorsorEquiv

/-- The isomorphism of torsors sending a point `p` to a point `q` with the same cocycle: it sends
`p · a` to `q · a`. -/
def ofCocycleEq (p : P) (q : Q) (h : Cocycle.ofPoint G p = Cocycle.ofPoint G q) :
    TorsorEquiv G A P Q where
  toHomeomorph := (Homeomorph.smulConst p).symm.trans (Homeomorph.smulConst q)
  map_op_smul' a x := by simp [smul_sdiv_assoc, mul_smul]
  map_smul' g x := by
    simp only [Equiv.toFun_as_coe, Homeomorph.coe_toEquiv, Homeomorph.trans_apply,
      Homeomorph.smulConst_apply, Homeomorph.smulConst_symm_apply,
      Cocycle.smul_sdiv_eq_mul_op_ofPoint, mul_smul, h, Cocycle.op_ofPoint_smul,
      ← IsSemilinearTorsor.smul_op_smul, op_unop]

@[simp]
theorem ofCocycleEq_apply (p : P) (q : Q) (h : Cocycle.ofPoint G p = Cocycle.ofPoint G q)
    (x : P) : ofCocycleEq p q h x = (x /ₛ p) • q :=
  (rfl)

/-- The isomorphism `TauCeti.NonabelianH1.TorsorEquiv.ofCocycleEq p q h` sends `p` to `q`. -/
theorem ofCocycleEq_apply_self (p : P) (q : Q)
    (h : Cocycle.ofPoint G p = Cocycle.ofPoint G q) : ofCocycleEq p q h p = q := by
  simp

end TorsorEquiv

end Point

namespace Cocycle

/-- The **torsor model** `P_c` of a cocycle `c`: a copy of `A`, a right `A`-torsor under right
multiplication, on which `g : G` acts by `g ⋆ x = c g * g • x`
(`TauCeti.NonabelianH1.Cocycle.TorsorModel.toOriginal_smul`). It lives in any universe above that of
`A`, so that it can be compared with torsors with carriers in larger universes. -/
@[ext]
structure TorsorModel (c : Cocycle G A) : Type max v w where
  /-- The point of the torsor model with a given underlying element of `A`. -/
  ofOriginal ::
  /-- The underlying element of `A` of a point of the torsor model. -/
  toOriginal : A

namespace TorsorModel

variable {c : Cocycle G A}

@[simp]
theorem toOriginal_ofOriginal (a : A) : (ofOriginal a : TorsorModel.{u, v, w} c).toOriginal = a :=
  (rfl)

@[simp]
theorem ofOriginal_toOriginal (x : TorsorModel.{u, v, w} c) : ofOriginal x.toOriginal = x :=
  (rfl)

/-- The torsor model carries the topology of `A`. -/
instance : TopologicalSpace (TorsorModel.{u, v, w} c) :=
  .induced toOriginal ‹_›

@[continuity, fun_prop]
theorem continuous_toOriginal : Continuous (toOriginal : TorsorModel.{u, v, w} c → A) :=
  continuous_induced_dom

@[continuity, fun_prop]
theorem continuous_ofOriginal : Continuous (ofOriginal : A → TorsorModel.{u, v, w} c) :=
  continuous_induced_rng.2 continuous_id

variable (c) in
/-- The underlying identification `A ≃ₜ P_c` of the torsor model. It does not respect the actions
of `G`. -/
def homeomorph : A ≃ₜ TorsorModel.{u, v, w} c where
  toFun := ofOriginal
  invFun := toOriginal
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_homeomorph : ⇑(homeomorph.{u, v, w} c) = ofOriginal :=
  (rfl)

@[simp]
theorem coe_homeomorph_symm : ⇑(homeomorph.{u, v, w} c).symm = toOriginal :=
  (rfl)

/-- The right action of `A` on the torsor model, `x · a = x * a`. -/
instance : SMul Aᵐᵒᵖ (TorsorModel.{u, v, w} c) :=
  ⟨fun a x ↦ ofOriginal (x.toOriginal * unop a)⟩

@[simp]
theorem toOriginal_op_smul (a : Aᵐᵒᵖ) (x : TorsorModel.{u, v, w} c) :
    (a • x).toOriginal = x.toOriginal * unop a :=
  (rfl)

/-- The difference of two points `x, y` of the torsor model is `y⁻¹ * x`. -/
instance : SDiv Aᵐᵒᵖ (TorsorModel.{u, v, w} c) :=
  ⟨fun x y ↦ op (y.toOriginal⁻¹ * x.toOriginal)⟩

@[simp]
theorem sdiv_eq (x y : TorsorModel.{u, v, w} c) : x /ₛ y = op (y.toOriginal⁻¹ * x.toOriginal) :=
  (rfl)

/-- The torsor model is a right `A`-torsor under right multiplication. -/
instance : Torsor Aᵐᵒᵖ (TorsorModel.{u, v, w} c) where
  nonempty := ⟨ofOriginal 1⟩
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_assoc]
  sdiv_smul' _ _ := by ext; simp
  smul_sdiv' _ _ := by simp

/-- The point `x * y` of the torsor model is the right translate of `x` by `y`. -/
theorem ofOriginal_mul (x y : A) :
    (ofOriginal (x * y) : TorsorModel.{u, v, w} c) = op y • ofOriginal x :=
  (rfl)

instance [IsTopologicalGroup A] : IsTopologicalTorsor (TorsorModel.{u, v, w} c) where
  continuous_smul := continuous_induced_rng.2 <| by
    simp only [Function.comp_def, toOriginal_op_smul]
    fun_prop
  continuous_sdiv := by
    simp only [sdiv_eq]
    fun_prop

/-- The action of `G` on the torsor model, `g ⋆ x = c g * g • x`. -/
instance : SMul G (TorsorModel.{u, v, w} c) :=
  ⟨fun g x ↦ ofOriginal (c g * g • x.toOriginal)⟩

@[simp]
theorem toOriginal_smul (g : G) (x : TorsorModel.{u, v, w} c) :
    (g • x).toOriginal = c g * g • x.toOriginal :=
  (rfl)

instance : MulAction G (TorsorModel.{u, v, w} c) where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [apply_mul, mul_smul, smul_mul', mul_assoc]

instance [ContinuousMul A] [ContinuousSMul G A] : ContinuousSMul G (TorsorModel.{u, v, w} c) where
  continuous_smul := continuous_induced_rng.2 <| by
    simp only [Function.comp_def, toOriginal_smul]
    fun_prop

instance : IsSemilinearTorsor G A (TorsorModel.{u, v, w} c) where
  smul_op_smul g a x := by
    ext
    simp only [toOriginal_smul, toOriginal_op_smul, unop_op, smul_mul', mul_assoc]

end TorsorModel

variable [IsTopologicalGroup A] [ContinuousSMul G A]

/-- The cocycle of the point `x` of the torsor model of `c` is the twist of `c` by `x`. -/
theorem ofPoint_ofOriginal (c : Cocycle G A) (x : A) :
    ofPoint G (TorsorModel.ofOriginal x : TorsorModel.{u, v, w} c) = c.twist x := by
  ext g
  rw [ofPoint_apply_eq_iff]
  ext
  simp [twist_apply, mul_assoc]

/-- The cocycle of the point `1` of the torsor model of `c` is `c`. -/
@[simp]
theorem ofPoint_ofOriginal_one (c : Cocycle G A) :
    ofPoint G (TorsorModel.ofOriginal 1 : TorsorModel.{u, v, w} c) = c := by
  rw [ofPoint_ofOriginal, twist_one]

end Cocycle

section Class

variable (G) (P : Type*) {Q : Type*} [TopologicalSpace P] [Torsor Aᵐᵒᵖ P]
  [IsTopologicalTorsor P] [MulAction G P] [ContinuousSMul G P] [IsSemilinearTorsor G A P]
  [TopologicalSpace Q] [Torsor Aᵐᵒᵖ Q] [IsTopologicalTorsor Q]
  [MulAction G Q] [ContinuousSMul G Q] [IsSemilinearTorsor G A Q]

/-- The **class** `[P] ∈ H¹(G, A)` of a `(G, A)`-torsor: the class of the cocycle of any of its
points (`TauCeti.NonabelianH1.ofTorsor_eq_mk`). -/
noncomputable def ofTorsor : NonabelianH1 G A :=
  mk (Cocycle.ofPoint G (Classical.arbitrary P))

variable {G P}
variable [IsTopologicalGroup A] [ContinuousSMul G A]

/-- The class of a torsor is the class of the cocycle of each of its points. -/
theorem ofTorsor_eq_mk (p : P) : ofTorsor G P = mk (Cocycle.ofPoint G p) := by
  rw [ofTorsor, ← sdiv_smul p (Classical.arbitrary P), ← op_unop (p /ₛ _),
    Cocycle.ofPoint_op_smul, mk_twist]

/-- **Torsors are classified by `H¹`**: two `(G, A)`-torsors have the same class exactly when they
are isomorphic. -/
theorem ofTorsor_eq_ofTorsor_iff :
    ofTorsor G P = ofTorsor G Q ↔ Nonempty (TorsorEquiv G A P Q) := by
  obtain ⟨p⟩ : Nonempty P := inferInstance
  obtain ⟨q⟩ : Nonempty Q := inferInstance
  constructor
  · rw [ofTorsor_eq_mk p, ofTorsor_eq_mk q, mk_eq_mk_iff]
    rintro ⟨a, ha⟩
    refine ⟨TorsorEquiv.ofCocycleEq (op a • p) q ?_⟩
    rw [Cocycle.ofPoint_op_smul]
    exact Cocycle.ext fun g ↦ by rw [Cocycle.twist_apply, ha]
  · rintro ⟨e⟩
    rw [ofTorsor_eq_mk p, ofTorsor_eq_mk (e p), Cocycle.ofPoint_map]

/-- The torsor model of a cocycle has the class of that cocycle. -/
@[simp]
theorem ofTorsor_torsorModel (c : Cocycle G A) :
    ofTorsor G (Cocycle.TorsorModel.{u, v, w} c) = mk c := by
  rw [ofTorsor_eq_mk (Cocycle.TorsorModel.ofOriginal 1), Cocycle.ofPoint_ofOriginal_one]

/-- A torsor has a `G`-fixed point exactly when its class is the base point. -/
theorem ofTorsor_eq_one_iff : ofTorsor G P = 1 ↔ ∃ p : P, ∀ g : G, g • p = p := by
  constructor
  · obtain ⟨p⟩ : Nonempty P := inferInstance
    rw [ofTorsor_eq_mk p, mk_eq_one_iff]
    rintro ⟨a, ha⟩
    refine ⟨op a⁻¹ • p, Cocycle.ofPoint_eq_one_iff.mp <| Cocycle.ext fun g ↦ ?_⟩
    rw [Cocycle.ofPoint_op_smul, Cocycle.twist_apply, ha]
    simp
  · rintro ⟨p, hp⟩
    rw [ofTorsor_eq_mk p, Cocycle.ofPoint_eq_one_iff.mpr hp, mk_one]

end Class

section Bundled

variable (G A)

/-- A `(G, A)`-torsor bundled with its carrier type: a topological right `A`-torsor with a
continuous semilinear action of `G`. -/
structure BundledTorsor where
  /-- The underlying space of the torsor. -/
  carrier : Type w
  /-- The topology of the torsor. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The right action of `A`, as a torsor structure under `Aᵐᵒᵖ`. -/
  [torsor : Torsor Aᵐᵒᵖ carrier]
  /-- The right action of `A` is that of a topological torsor. -/
  [isTopologicalTorsor : IsTopologicalTorsor carrier]
  /-- The action of `G`. -/
  [mulAction : MulAction G carrier]
  /-- The action of `G` is continuous. -/
  [continuousSMul : ContinuousSMul G carrier]
  /-- The action of `G` is semilinear. -/
  [isSemilinearTorsor : IsSemilinearTorsor G A carrier]

attribute [instance] BundledTorsor.topologicalSpace BundledTorsor.torsor
  BundledTorsor.isTopologicalTorsor BundledTorsor.mulAction BundledTorsor.continuousSMul
  BundledTorsor.isSemilinearTorsor

namespace BundledTorsor

instance : CoeSort (BundledTorsor.{u, v, w} G A) (Type w) :=
  ⟨carrier⟩

/-- Isomorphism of `(G, A)`-torsors: `P ≈ Q` when there is an isomorphism `P ≃ Q` of torsors. -/
instance setoid : Setoid (BundledTorsor.{u, v, w} G A) where
  r P Q := Nonempty (TorsorEquiv G A P Q)
  iseqv := ⟨fun P ↦ ⟨.refl G A P⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

theorem equiv_iff {P Q : BundledTorsor.{u, v, w} G A} :
    P ≈ Q ↔ Nonempty (TorsorEquiv G A P Q) :=
  Iff.rfl

end BundledTorsor

variable [IsTopologicalGroup A] [ContinuousSMul G A]

/-- **Torsors are classified by `H¹`**: the bijection between isomorphism classes of
`(G, A)`-torsors and `H¹(G, A)` sending a torsor to its class. Its inverse sends the class of a
cocycle `c` to the torsor model of `c`. -/
noncomputable def torsorClassEquiv :
    Quotient (BundledTorsor.setoid.{u, v, max v w} G A) ≃ NonabelianH1 G A :=
  .ofBijective (Quotient.lift (fun P ↦ ofTorsor G P) fun _ _ h ↦ ofTorsor_eq_ofTorsor_iff.mpr h)
    ⟨fun P Q ↦ Quotient.inductionOn₂ P Q fun _ _ h ↦ Quotient.sound <|
      ofTorsor_eq_ofTorsor_iff.mp h,
    fun c ↦ c.induction_on fun c ↦ ⟨⟦⟨Cocycle.TorsorModel.{u, v, w} c⟩⟧, ofTorsor_torsorModel c⟩⟩

@[simp]
theorem torsorClassEquiv_mk (P : BundledTorsor.{u, v, max v w} G A) :
    torsorClassEquiv G A ⟦P⟧ = ofTorsor G P :=
  (rfl)

/-- The inverse of the classification sends the class of a cocycle to its torsor model. -/
@[simp]
theorem torsorClassEquiv_symm_mk (c : Cocycle G A) :
    (torsorClassEquiv.{u, v, w} G A).symm (mk c) = ⟦⟨Cocycle.TorsorModel.{u, v, w} c⟩⟧ :=
  (torsorClassEquiv G A).symm_apply_eq.mpr (ofTorsor_torsorModel c).symm

end Bundled

end NonabelianH1

end TauCeti
