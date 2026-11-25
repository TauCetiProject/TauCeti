/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Torsor

/-!
# Equivariant topological torsors

Let a group `G` act by group automorphisms on a group `A`. A topological right `A`-torsor `P` is
written as a topological torsor `Torsor Aᵐᵒᵖ P` with `IsTopologicalTorsor P`, so that `p · a` is
`MulOpposite.op a • p`. A left action of `G` on `P` is **semilinear** when

`g • (p · a) = (g • p) · (g • a)`.

A topological right `A`-torsor with a continuous semilinear action of `G` is a `(G, A)`-torsor;
these are classified by continuous nonabelian `H¹(G, A)` in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.TopologicalTorsor`. For a
curve `X` with base point `b`, the torsor of étale (or unipotent) paths from `b` to a rational
point is a torsor of this kind under the fundamental group at `b`, with `G` the absolute Galois
group.

## Main definitions

* `TauCeti.Torsor.orbitHomeomorph p`: the orbit homeomorphism `A ≃ₜ P`, `a ↦ p · a`, of a point
  `p` of a topological right `A`-torsor.
* `TauCeti.IsSemilinearTorsor G A P`: the action of `G` on the right `A`-torsor `P` is
  semilinear.
* `TauCeti.TorsorEquiv G A P Q`: isomorphisms of `(G, A)`-torsors, homeomorphisms respecting both
  actions.

## References

* M. Kim, *The motivic fundamental group of `P¹ ∖ {0, 1, ∞}` and the theorem of Siegel*,
  Invent. Math. 161 (2005), §1.
* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.2.
-/

public section

open MulOpposite

namespace TauCeti

variable {G A : Type*} [Group G] [Group A]

namespace Torsor

variable [TopologicalSpace A] {P : Type*} [TopologicalSpace P] [Torsor Aᵐᵒᵖ P]
  [IsTopologicalTorsor P]

/-- The **orbit homeomorphism** `A ≃ₜ P`, `a ↦ p · a`, of a point `p` of a topological right
`A`-torsor: `Homeomorph.smulConst p` composed with `MulOpposite.opHomeomorph`. -/
def orbitHomeomorph (p : P) : A ≃ₜ P :=
  MulOpposite.opHomeomorph.trans (Homeomorph.smulConst p)

@[simp]
theorem orbitHomeomorph_apply (p : P) (a : A) : orbitHomeomorph p a = op a • p :=
  (rfl)

@[simp]
theorem orbitHomeomorph_symm_apply (p q : P) : (orbitHomeomorph p).symm q = unop (q /ₛ p) :=
  (rfl)

/-- The orbit homeomorphism at `p` sends `1` to `p`. -/
theorem orbitHomeomorph_one (p : P) : orbitHomeomorph p (1 : A) = p := by
  simp

end Torsor

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

instance : HomeomorphClass (TorsorEquiv G A P Q) P Q where
  map_continuous e := e.continuous_toFun
  inv_continuous e := e.continuous_invFun

/-- An isomorphism of torsors is continuous. -/
@[fun_prop]
protected theorem continuous (e : TorsorEquiv G A P Q) : Continuous e :=
  map_continuous e

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

/-- An isomorphism of torsors preserves the difference of two points. -/
@[simp]
theorem map_sdiv (e : TorsorEquiv G A P Q) (p q : P) : e p /ₛ e q = p /ₛ q :=
  (eq_smul_iff_sdiv_eq _ _ _).mp <| by rw [← map_op_smul, sdiv_smul]

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

/-- The inverse of an isomorphism of torsors is continuous. -/
@[fun_prop]
theorem continuous_symm (e : TorsorEquiv G A P Q) : Continuous e.symm :=
  e.symm.continuous

@[simp]
theorem apply_symm_apply (e : TorsorEquiv G A P Q) (q : Q) : e (e.symm q) = q :=
  e.toHomeomorph.apply_symm_apply q

@[simp]
theorem symm_apply_apply (e : TorsorEquiv G A P Q) (p : P) : e.symm (e p) = p :=
  e.toHomeomorph.symm_apply_apply p

theorem symm_apply_eq (e : TorsorEquiv G A P Q) {q : Q} {p : P} : e.symm q = p ↔ q = e p :=
  e.toHomeomorph.symm_apply_eq

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

@[simp]
theorem self_trans_symm (e : TorsorEquiv G A P Q) : e.trans e.symm = refl G A P := by
  ext
  simp

@[simp]
theorem symm_trans_self (e : TorsorEquiv G A P Q) : e.symm.trans e = refl G A Q := by
  ext
  simp

end TorsorEquiv

end TorsorEquiv

end TauCeti
