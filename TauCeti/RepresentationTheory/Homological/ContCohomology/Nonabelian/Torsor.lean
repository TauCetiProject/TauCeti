/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic
public import TauCeti.Algebra.Torsor.Basic
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuous nonabelian first cohomology classifies smooth torsors

Let a topological group `G` act on a group `A` by group automorphisms. A **smooth
`(G, A)`-torsor** is an `A`-torsor `X` (a nonempty set with a simply transitive action of `A`,
Mathlib's `Torsor A X`) with an action of `G` with open stabilizers, compatible in the sense that
`g • (a • x) = (g • a) • (g • x)`. For a profinite Galois group `G` these are the stalks of
torsors under the sheaf of groups of a smooth `G`-group `A` on the site of finite continuous
`G`-sets, and the comparison below is the cocycle description of such torsors.

A point `x` of a smooth torsor `X` gives a continuous cocycle
(`TauCeti.NonabelianH1.SmoothTorsor.cocycle`), determined by `g • x = (f g)⁻¹ • x`; moving the
point changes the cocycle by a coboundary, so the class `TauCeti.NonabelianH1.SmoothTorsor.cls X`
in `H¹(G, A)` is well defined. Two smooth torsors are isomorphic exactly when they have the same
class (`TauCeti.NonabelianH1.SmoothTorsor.cls_eq_cls_iff`).

For discrete `A` with a continuous action of `G`, a cocycle `f` conversely defines the smooth
torsor `TauCeti.NonabelianH1.Cocycle.torsor f`, whose underlying set
`TauCeti.NonabelianH1.Cocycle.TorsorCarrier f` is a copy of `A`, with `A` acting by left
multiplication and `g` acting by `x ↦ (g • x) * (f g)⁻¹`. It has class `f`
(`TauCeti.NonabelianH1.SmoothTorsor.cls_torsor`), so every class arises
(`TauCeti.NonabelianH1.SmoothTorsor.cls_surjective`).

## Main definitions

* `TauCeti.NonabelianH1.SmoothTorsor G A`: smooth `(G, A)`-torsors, with isomorphisms
  `TauCeti.NonabelianH1.SmoothTorsor.Iso`.
* `TauCeti.NonabelianH1.SmoothTorsor.cocycle`: the cocycle of a smooth torsor at a point.
* `TauCeti.NonabelianH1.SmoothTorsor.cls`: the class of a smooth torsor in `H¹(G, A)`.
* `TauCeti.NonabelianH1.Cocycle.torsor f`: the smooth torsor of a cocycle `f`, with underlying
  set `TauCeti.NonabelianH1.Cocycle.TorsorCarrier f`.

## Main results

* `TauCeti.NonabelianH1.SmoothTorsor.cls_eq_cls_iff`: two smooth torsors have the same class
  exactly when they are isomorphic.
* `TauCeti.NonabelianH1.SmoothTorsor.cls_eq_one_iff`: a smooth torsor has the trivial class
  exactly when `G` fixes one of its points.
* `TauCeti.NonabelianH1.SmoothTorsor.cls_torsor`: the torsor of a cocycle has its class.
* `TauCeti.NonabelianH1.SmoothTorsor.cls_surjective`: for discrete `A` with a continuous action,
  every class is the class of a smooth torsor.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.
-/

public section

namespace TauCeti

namespace NonabelianH1

universe u v w w' w''

variable (G : Type u) (A : Type v) [Group G] [TopologicalSpace G] [Group A]
  [MulDistribMulAction G A]

/-- A **smooth `(G, A)`-torsor**: an `A`-torsor with an action of `G` with open stabilizers,
satisfying `g • (a • x) = (g • a) • (g • x)`. -/
structure SmoothTorsor where
  /-- The underlying set. -/
  carrier : Type w
  /-- The `A`-torsor structure: a simply transitive action of `A` on a nonempty set. -/
  [torsorA : Torsor A carrier]
  /-- The action of `G`. -/
  [mulActionG : MulAction G carrier]
  /-- The actions are compatible: `g • (a • x) = (g • a) • (g • x)`. -/
  smul_distrib_smul : ∀ (g : G) (a : A) (x : carrier), g • a • x = (g • a) • g • x
  /-- The stabilizers of `G` are open. -/
  isOpen_stabilizer : ∀ x : carrier, IsOpen (MulAction.stabilizer G x : Set G)

namespace SmoothTorsor

attribute [instance] torsorA mulActionG

variable {G A}

/-- An **isomorphism of smooth torsors**: a bijection commuting with both actions. -/
@[ext]
structure Iso (P : SmoothTorsor.{u, v, w} G A) (Q : SmoothTorsor.{u, v, w'} G A) where
  /-- The underlying bijection. -/
  toEquiv : P.carrier ≃ Q.carrier
  /-- The bijection commutes with the action of `A`. -/
  map_smul_A : ∀ (a : A) (x : P.carrier), toEquiv (a • x) = a • toEquiv x
  /-- The bijection commutes with the action of `G`. -/
  map_smul_G : ∀ (g : G) (x : P.carrier), toEquiv (g • x) = g • toEquiv x

namespace Iso

variable {P : SmoothTorsor.{u, v, w} G A} {Q : SmoothTorsor.{u, v, w'} G A}
  {R : SmoothTorsor.{u, v, w''} G A}

/-- The identity isomorphism of a smooth torsor. -/
def refl (P : SmoothTorsor.{u, v, w} G A) : P.Iso P where
  toEquiv := Equiv.refl _
  map_smul_A _ _ := rfl
  map_smul_G _ _ := rfl

/-- The inverse of an isomorphism of smooth torsors. -/
def symm (e : P.Iso Q) : Q.Iso P where
  toEquiv := e.toEquiv.symm
  map_smul_A a x := e.toEquiv.symm_apply_eq.mpr <| by rw [e.map_smul_A, Equiv.apply_symm_apply]
  map_smul_G g x := e.toEquiv.symm_apply_eq.mpr <| by rw [e.map_smul_G, Equiv.apply_symm_apply]

/-- The composition of isomorphisms of smooth torsors. -/
def trans (e : P.Iso Q) (e' : Q.Iso R) : P.Iso R where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_smul_A a x := by rw [Equiv.trans_apply, e.map_smul_A, e'.map_smul_A, Equiv.trans_apply]
  map_smul_G g x := by rw [Equiv.trans_apply, e.map_smul_G, e'.map_smul_G, Equiv.trans_apply]

@[simp]
theorem refl_toEquiv (P : SmoothTorsor.{u, v, w} G A) : (refl P).toEquiv = Equiv.refl _ :=
  (rfl)

@[simp]
theorem symm_toEquiv (e : P.Iso Q) : e.symm.toEquiv = e.toEquiv.symm :=
  (rfl)

@[simp]
theorem trans_toEquiv (e : P.Iso Q) (e' : Q.Iso R) :
    (e.trans e').toEquiv = e.toEquiv.trans e'.toEquiv :=
  (rfl)

end Iso

variable (P : SmoothTorsor.{u, v, w} G A)

variable [TopologicalSpace A] [ContinuousMul G]

/-- The **cocycle of a smooth torsor at a point** `x`: the cocycle `f` with
`g • x = (f g)⁻¹ • x`, that is `f g = x /ₛ (g • x)`. -/
noncomputable def cocycle (x : P.carrier) : Cocycle G A where
  toFun g := x /ₛ (g • x)
  continuous_toFun := by
    -- It is constant on the left cosets of the open stabilizer of `x`.
    refine IsLocallyConstant.continuous (IsLocallyConstant.iff_exists_open _ |>.mpr fun g ↦ ?_)
    refine ⟨(g⁻¹ * ·) ⁻¹' (MulAction.stabilizer G x : Set G),
      (P.isOpen_stabilizer x).preimage (continuous_const.mul continuous_id), by simp,
      fun h hh ↦ ?_⟩
    rw [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hh
    have : h • x = g • x :=
      calc h • x = g • (g⁻¹ * h) • x := by rw [smul_smul, mul_inv_cancel_left]
        _ = g • x := by rw [hh]
    rw [this]
  map_mul' g h := by
    -- With `a = x /ₛ (g • x)` and `b = x /ₛ (h • x)`, so that `g • x = a⁻¹ • x` and
    -- `h • x = b⁻¹ • x`, compute `(g * h) • x = (g • b)⁻¹ • a⁻¹ • x = (a * g • b)⁻¹ • x`.
    have hgh : (g * h) • x = ((x /ₛ (g • x)) * g • (x /ₛ (h • x)))⁻¹ • x := by
      conv_lhs => rw [mul_smul, ← inv_sdiv_smul x (h • x), P.smul_distrib_smul,
        ← inv_sdiv_smul x (g • x), smul_smul]
      rw [mul_inv_rev, smul_inv']
    rw [hgh, sdiv_smul_eq_sdiv_div, sdiv_self, one_div, inv_inv]

@[simp]
theorem cocycle_apply (x : P.carrier) (g : G) : P.cocycle x g = x /ₛ (g • x) :=
  (rfl)

/-- The defining property of the cocycle at `x`: `g • x = (f g)⁻¹ • x`. -/
theorem smul_eq_inv_cocycle_smul (x : P.carrier) (g : G) : g • x = (P.cocycle x g)⁻¹ • x :=
  (inv_sdiv_smul x (g • x)).symm

theorem cocycle_apply_eq_iff {x : P.carrier} {g : G} {a : A} :
    P.cocycle x g = a ↔ g • x = a⁻¹ • x := by
  rw [cocycle_apply, ← inv_inj, inv_sdiv_eq_sdiv_rev, eq_smul_iff_sdiv_eq]

/-- Moving the point by `b` changes the cocycle to `g ↦ b * f g * (g • b)⁻¹`. -/
theorem cocycle_smul (x : P.carrier) (b : A) (g : G) :
    P.cocycle (b • x) g = b * P.cocycle x g * (g • b)⁻¹ := by
  rw [cocycle_apply_eq_iff, P.smul_distrib_smul, smul_eq_inv_cocycle_smul, smul_smul, smul_smul]
  congr 1
  group

/-- Cocycles of a smooth torsor at different points are cohomologous. -/
theorem mk_cocycle_eq (x y : P.carrier) :
    NonabelianH1.mk (P.cocycle x) = NonabelianH1.mk (P.cocycle y) := by
  rw [← sdiv_smul y x, mk_eq_mk_iff]
  exact ⟨(y /ₛ x)⁻¹, fun g ↦ by rw [cocycle_smul, inv_inv, smul_inv']⟩

/-- The **class of a smooth torsor** in `H¹(G, A)`: the class of its cocycle at any point. -/
noncomputable def cls : NonabelianH1 G A :=
  NonabelianH1.mk (P.cocycle (Classical.arbitrary P.carrier))

theorem cls_eq (x : P.carrier) : P.cls = NonabelianH1.mk (P.cocycle x) :=
  P.mk_cocycle_eq _ x

/-- A smooth torsor has the trivial class exactly when `G` fixes one of its points. -/
theorem cls_eq_one_iff : P.cls = 1 ↔ ∃ x : P.carrier, ∀ g : G, g • x = x := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty P.carrier)
    obtain ⟨a, ha⟩ := mk_eq_one_iff.mp (P.cls_eq x ▸ h)
    refine ⟨a • x, fun g ↦ ?_⟩
    have h1 : P.cocycle (a • x) g = 1 := by
      rw [cocycle_smul, ha]
      group
    rw [cocycle_apply_eq_iff, inv_one, one_smul] at h1
    exact h1
  · rw [P.cls_eq x, mk_eq_one_iff]
    exact ⟨1, fun g ↦ by simp [hx]⟩

variable {P} {Q : SmoothTorsor.{u, v, w'} G A}

/-- An isomorphism of smooth torsors preserves cocycles. -/
@[simp]
theorem Iso.cocycle_eq (e : P.Iso Q) (x : P.carrier) : Q.cocycle (e.toEquiv x) = P.cocycle x :=
  Cocycle.ext fun g ↦ by
    rw [cocycle_apply_eq_iff, ← e.map_smul_G, ← e.map_smul_A, ← smul_eq_inv_cocycle_smul]

/-- Smooth torsors with equal cocycles at two points are isomorphic, by the bijection
`a • x ↦ a • y`. -/
noncomputable def isoOfCocycleEq {x : P.carrier} {y : Q.carrier}
    (h : P.cocycle x = Q.cocycle y) : P.Iso Q where
  toEquiv := (Equiv.smulConst x).symm.trans (Equiv.smulConst y)
  map_smul_A a z := by
    simp only [Equiv.trans_apply, Equiv.coe_smulConst_symm, Equiv.coe_smulConst, smul_sdiv_assoc,
      mul_smul]
  map_smul_G g z := by
    simp only [Equiv.trans_apply, Equiv.coe_smulConst_symm, Equiv.coe_smulConst]
    -- Write `z = (z /ₛ x) • x` and move `g` past it on both sides.
    conv_lhs => rw [← sdiv_smul z x]
    rw [P.smul_distrib_smul, smul_eq_inv_cocycle_smul P x g, smul_smul, smul_sdiv,
      Q.smul_distrib_smul, smul_eq_inv_cocycle_smul Q y g, smul_smul, h]

@[simp]
theorem isoOfCocycleEq_apply {x : P.carrier} {y : Q.carrier} (h : P.cocycle x = Q.cocycle y)
    (z : P.carrier) : (isoOfCocycleEq h).toEquiv z = (z /ₛ x) • y :=
  (rfl)

/-- **Smooth torsors are classified by `H¹(G, A)`**: two smooth torsors are isomorphic exactly
when they have the same class. -/
theorem cls_eq_cls_iff : P.cls = Q.cls ↔ Nonempty (P.Iso Q) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty P.carrier)
    obtain ⟨y⟩ := (inferInstance : Nonempty Q.carrier)
    rw [P.cls_eq x, Q.cls_eq y, mk_eq_mk_iff] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨isoOfCocycleEq (x := a⁻¹ • x) (y := y) (Cocycle.ext fun g ↦ ?_)⟩
    rw [cocycle_smul, ha, smul_inv', inv_inv]
  · obtain ⟨x⟩ := (inferInstance : Nonempty P.carrier)
    rw [P.cls_eq x, Q.cls_eq (e.toEquiv x), e.cocycle_eq]

end SmoothTorsor

variable [TopologicalSpace A]

namespace Cocycle

variable {G A}

/-- The underlying set of the smooth torsor of a cocycle `f`: a copy of `A`, on which `A` acts
by left multiplication and `g : G` by `x ↦ (g • x) * (f g)⁻¹`. -/
@[ext]
structure TorsorCarrier (f : Cocycle G A) where
  /-- The element of `A`. -/
  val : A

namespace TorsorCarrier

variable (f : Cocycle G A)

/-- `A` acts on the torsor of a cocycle by left multiplication. -/
instance instSMulA : SMul A (TorsorCarrier f) where
  smul a x := ⟨a * x.val⟩

/-- The quotient of two points of the torsor of a cocycle. -/
instance instSDiv : SDiv A (TorsorCarrier f) where
  sdiv x y := x.val / y.val

@[simp]
theorem val_smul_A (a : A) (x : TorsorCarrier f) : (a • x).val = a * x.val :=
  (rfl)

@[simp]
theorem sdiv_def (x y : TorsorCarrier f) : x /ₛ y = x.val / y.val :=
  (rfl)

instance : Nonempty (TorsorCarrier f) :=
  ⟨⟨1⟩⟩

/-- The torsor of a cocycle is an `A`-torsor under left multiplication, pulled back from `A`
as a torsor over itself. -/
instance instTorsor : Torsor A (TorsorCarrier f) :=
  Function.Injective.torsor TorsorCarrier.val (fun _ _ ↦ TorsorCarrier.ext) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

/-- `g : G` acts on the torsor of `f` by `x ↦ (g • x) * (f g)⁻¹`. -/
instance instSMulG : SMul G (TorsorCarrier f) where
  smul g x := ⟨(g • x.val) * (f g)⁻¹⟩

@[simp]
theorem val_smul_G (g : G) (x : TorsorCarrier f) : (g • x).val = (g • x.val) * (f g)⁻¹ :=
  (rfl)

instance instMulActionG : MulAction G (TorsorCarrier f) where
  one_smul x := TorsorCarrier.ext (by simp)
  mul_smul g h x := TorsorCarrier.ext (by
    simp only [val_smul_G, f.apply_mul, smul_mul', smul_inv', mul_inv_rev, mul_smul, mul_assoc])

end TorsorCarrier

variable [DiscreteTopology A] [ContinuousSMul G A]

/-- The **smooth torsor of a cocycle** `f`: the set `TorsorCarrier f`, a copy of `A`, with `A`
acting by left multiplication and `g : G` by `x ↦ (g • x) * (f g)⁻¹`. -/
noncomputable abbrev torsor (f : Cocycle G A) : SmoothTorsor.{u, v, v} G A where
  carrier := TorsorCarrier f
  smul_distrib_smul g a x := TorsorCarrier.ext (by simp [smul_mul', mul_assoc])
  isOpen_stabilizer x := by
    -- The stabilizers are open since `A` is discrete and the action of `G` on `A` is continuous.
    have hc : Continuous fun g : G ↦ (g • x.val, f g) :=
      (continuous_id.smul continuous_const).prodMk f.continuous
    have hs : (MulAction.stabilizer G x : Set G) =
        (fun g : G ↦ (g • x.val, f g)) ⁻¹' {p : A × A | p.1 * p.2⁻¹ = x.val} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe,
        MulAction.mem_stabilizer_iff, TorsorCarrier.ext_iff, TorsorCarrier.val_smul_G]
    rw [hs]
    exact (isOpen_discrete _).preimage hc

variable [ContinuousMul G]

/-- The cocycle of the torsor of `f` at the point `1` is `f`. -/
@[simp]
theorem cocycle_torsor (f : Cocycle G A) : f.torsor.cocycle (⟨1⟩ : TorsorCarrier f) = f :=
  ext fun g ↦ f.torsor.cocycle_apply_eq_iff.mpr <| TorsorCarrier.ext <| by simp

end Cocycle

namespace SmoothTorsor

variable {G A} [DiscreteTopology A] [ContinuousSMul G A] [ContinuousMul G]

/-- The smooth torsor of a cocycle `f` has class `[f]`. -/
@[simp]
theorem cls_torsor (f : Cocycle G A) : f.torsor.cls = NonabelianH1.mk f := by
  rw [cls_eq _ (⟨1⟩ : Cocycle.TorsorCarrier f), Cocycle.cocycle_torsor]

/-- The class map from smooth torsors to `H¹(G, A)` is surjective. -/
theorem cls_surjective :
    Function.Surjective fun P : SmoothTorsor.{u, v, v} G A ↦ P.cls := by
  intro c
  obtain ⟨f, rfl⟩ := NonabelianH1.mk_surjective c
  exact ⟨f.torsor, cls_torsor f⟩

end SmoothTorsor

end NonabelianH1

end TauCeti
