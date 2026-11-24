/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuous nonabelian first cohomology classifies smooth torsors

Let a topological group `G` act on a group `A` by group automorphisms. A **smooth
`(G, A)`-torsor** is a nonempty set `X` with a simply transitive action of `A` and an action of
`G` with open stabilizers, compatible in the sense that `g • (a • x) = (g • a) • (g • x)`. For a
profinite Galois group `G` these are the stalks of torsors under the sheaf of groups of a smooth
`G`-group `A` on the site of finite continuous `G`-sets, and the comparison below is the
cocycle description of such torsors.

A point `x` of a smooth torsor `X` gives a continuous cocycle
(`TauCeti.NonabelianH1.SmoothTorsor.cocycle`), determined by `g • x = (f g)⁻¹ • x`; moving the
point changes the cocycle by a coboundary, so the class `TauCeti.NonabelianH1.SmoothTorsor.cls X`
in `H¹(G, A)` is well defined. Conversely a cocycle `f` defines the smooth torsor
`TauCeti.NonabelianH1.Cocycle.Torsor f`: the set `A`, with `A` acting by left multiplication and
`g` acting by `x ↦ (g • x) * (f g)⁻¹`. Two smooth torsors are isomorphic exactly when they have
the same class (`TauCeti.NonabelianH1.SmoothTorsor.cls_eq_cls_iff`), and every class arises
(`TauCeti.NonabelianH1.SmoothTorsor.cls_torsor`).

For the trivial action, cocycles are continuous homomorphisms and the cohomology relation is
conjugacy, so `H¹(G, A)` is the set of continuous homomorphisms `G → A` modulo conjugation by `A`
(`TauCeti.NonabelianH1.equivOfTrivial`).

## Main definitions

* `TauCeti.NonabelianH1.SmoothTorsor G A`: smooth `(G, A)`-torsors, with isomorphisms
  `TauCeti.NonabelianH1.SmoothTorsor.Iso`.
* `TauCeti.NonabelianH1.SmoothTorsor.cocycle`: the cocycle of a smooth torsor at a point.
* `TauCeti.NonabelianH1.SmoothTorsor.cls`: the class of a smooth torsor in `H¹(G, A)`.
* `TauCeti.NonabelianH1.Cocycle.Torsor f`: the smooth torsor of a cocycle `f`.
* `TauCeti.NonabelianH1.Cocycle.equivOfTrivial`: for the trivial action, cocycles are continuous
  homomorphisms.
* `TauCeti.NonabelianH1.equivOfTrivial`: for the trivial action, `H¹(G, A)` is the set of
  continuous homomorphisms modulo conjugacy.

## Main results

* `TauCeti.NonabelianH1.SmoothTorsor.cls_eq_cls_iff`: two smooth torsors have the same class
  exactly when they are isomorphic.
* `TauCeti.NonabelianH1.SmoothTorsor.cls_torsor`: the torsor of a cocycle has its class.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.
-/

public section

namespace TauCeti

namespace NonabelianH1

universe u v w w'

variable (G : Type u) (A : Type v) [Group G] [TopologicalSpace G] [Group A]
  [MulDistribMulAction G A]

/-- A **smooth `(G, A)`-torsor**: a nonempty set with a simply transitive action of `A` and an
action of `G` with open stabilizers, satisfying `g • (a • x) = (g • a) • (g • x)`. -/
structure SmoothTorsor where
  /-- The underlying set. -/
  carrier : Type w
  /-- The action of `A`. -/
  [mulActionA : MulAction A carrier]
  /-- The action of `G`. -/
  [mulActionG : MulAction G carrier]
  /-- The actions are compatible: `g • (a • x) = (g • a) • (g • x)`. -/
  smul_smul_eq : ∀ (g : G) (a : A) (x : carrier), g • a • x = (g • a) • g • x
  /-- The stabilizers of `G` are open. -/
  isOpen_stabilizer : ∀ x : carrier, IsOpen (MulAction.stabilizer G x : Set G)
  /-- The action of `A` is simply transitive. -/
  bijective : ∀ x : carrier, Function.Bijective fun a : A ↦ a • x
  /-- The set is nonempty. -/
  nonempty : Nonempty carrier

namespace SmoothTorsor

attribute [instance] mulActionA mulActionG

variable {G A}

/-- An **isomorphism of smooth torsors**: a bijection commuting with both actions. -/
structure Iso (P : SmoothTorsor.{u, v, w} G A) (Q : SmoothTorsor.{u, v, w'} G A) where
  /-- The underlying bijection. -/
  toEquiv : P.carrier ≃ Q.carrier
  /-- The bijection commutes with the action of `A`. -/
  map_smul_A : ∀ (a : A) (x : P.carrier), toEquiv (a • x) = a • toEquiv x
  /-- The bijection commutes with the action of `G`. -/
  map_smul_G : ∀ (g : G) (x : P.carrier), toEquiv (g • x) = g • toEquiv x

variable (P : SmoothTorsor.{u, v, w} G A)

/-- The element `a` with `a • x = y`. -/
noncomputable def quot (x y : P.carrier) : A :=
  (Equiv.ofBijective _ (P.bijective x)).symm y

@[simp]
theorem quot_smul (x y : P.carrier) : P.quot x y • x = y :=
  (Equiv.ofBijective _ (P.bijective x)).apply_symm_apply y

theorem quot_eq_iff {x y : P.carrier} {a : A} : P.quot x y = a ↔ a • x = y :=
  ⟨fun h ↦ h ▸ P.quot_smul x y, fun h ↦ (P.bijective x).1 (by simp [h])⟩

variable [TopologicalSpace A] [ContinuousMul G]

/-- The **cocycle of a smooth torsor at a point** `x`: the cocycle `f` with
`g • x = (f g)⁻¹ • x`. It is continuous because it is constant on the left cosets of the open
stabilizer of `x`. -/
noncomputable def cocycle (x : P.carrier) : Cocycle G A where
  toFun g := (P.quot x (g • x))⁻¹
  continuous_toFun := by
    refine IsLocallyConstant.continuous (IsLocallyConstant.iff_exists_open _ |>.mpr fun g ↦ ?_)
    refine ⟨(g⁻¹ * ·) ⁻¹' (MulAction.stabilizer G x : Set G),
      (P.isOpen_stabilizer x).preimage (continuous_const.mul continuous_id), by simp,
      fun h hh ↦ ?_⟩
    have hh : (g⁻¹ * h) • x = x := hh
    have : h • x = g • x :=
      calc h • x = g • (g⁻¹ * h) • x := by rw [smul_smul, mul_inv_cancel_left]
        _ = g • x := by rw [hh]
    rw [this]
  map_mul' g h := by
    rw [inv_eq_iff_eq_inv, quot_eq_iff, mul_inv_rev, smul_inv', inv_inv, inv_inv,
      mul_smul _ (P.quot x (g • x)), quot_smul, ← P.smul_smul_eq, quot_smul, mul_smul]

/-- The defining property of the cocycle at `x`: `g • x = (f g)⁻¹ • x`. -/
theorem smul_eq_cocycle (x : P.carrier) (g : G) : g • x = (P.cocycle x g)⁻¹ • x := by
  change g • x = ((P.quot x (g • x))⁻¹)⁻¹ • x
  rw [inv_inv, quot_smul]

theorem cocycle_apply_eq_iff {x : P.carrier} {g : G} {a : A} :
    P.cocycle x g = a ↔ g • x = a⁻¹ • x := by
  change (P.quot x (g • x))⁻¹ = a ↔ _
  rw [inv_eq_iff_eq_inv, quot_eq_iff, eq_comm]

/-- Moving the point by `b` changes the cocycle to `g ↦ b * f g * (g • b)⁻¹`. -/
theorem cocycle_smul (x : P.carrier) (b : A) (g : G) :
    P.cocycle (b • x) g = b * P.cocycle x g * (g • b)⁻¹ := by
  rw [cocycle_apply_eq_iff, P.smul_smul_eq, smul_eq_cocycle, smul_smul, smul_smul]
  congr 1
  group

/-- Cocycles of a smooth torsor at different points are cohomologous. -/
theorem mk_cocycle_eq (x y : P.carrier) :
    NonabelianH1.mk (P.cocycle x) = NonabelianH1.mk (P.cocycle y) := by
  rw [← P.quot_smul x y, mk_eq_mk_iff]
  exact ⟨(P.quot x y)⁻¹, fun g ↦ by rw [cocycle_smul, inv_inv, smul_inv']⟩

/-- The **class of a smooth torsor** in `H¹(G, A)`: the class of its cocycle at any point. -/
noncomputable def cls : NonabelianH1 G A :=
  NonabelianH1.mk (P.cocycle (Classical.choice P.nonempty))

theorem cls_eq (x : P.carrier) : P.cls = NonabelianH1.mk (P.cocycle x) :=
  P.mk_cocycle_eq _ x

variable {P} {Q : SmoothTorsor.{u, v, w'} G A}

/-- An isomorphism of smooth torsors preserves cocycles. -/
theorem Iso.cocycle_eq (e : P.Iso Q) (x : P.carrier) : Q.cocycle (e.toEquiv x) = P.cocycle x :=
  Cocycle.ext fun g ↦ by
    rw [cocycle_apply_eq_iff, ← e.map_smul_G, ← e.map_smul_A, ← smul_eq_cocycle]

/-- Smooth torsors with equal cocycles at two points are isomorphic, by the bijection
`a • x ↦ a • y`. -/
noncomputable def isoOfCocycleEq {x : P.carrier} {y : Q.carrier}
    (h : P.cocycle x = Q.cocycle y) : P.Iso Q where
  toEquiv := (Equiv.ofBijective _ (P.bijective x)).symm.trans
    (Equiv.ofBijective _ (Q.bijective y))
  map_smul_A a z := by
    change P.quot x (a • z) • y = a • P.quot x z • y
    rw [smul_smul, (P.quot_eq_iff).mpr]
    rw [mul_smul, quot_smul]
  map_smul_G g z := by
    change P.quot x (g • z) • y = g • P.quot x z • y
    have hz : g • z = ((g • P.quot x z) * (P.cocycle x g)⁻¹) • x := by
      conv_lhs => rw [← P.quot_smul x z]
      rw [P.smul_smul_eq, smul_eq_cocycle, smul_smul]
    rw [(P.quot_eq_iff).mpr hz.symm, Q.smul_smul_eq, smul_eq_cocycle Q y g, smul_smul, h]

/-- **Smooth torsors are classified by `H¹(G, A)`**: two smooth torsors are isomorphic exactly
when they have the same class. -/
theorem cls_eq_cls_iff : P.cls = Q.cls ↔ Nonempty (P.Iso Q) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · obtain ⟨x⟩ := P.nonempty
    obtain ⟨y⟩ := Q.nonempty
    rw [P.cls_eq x, Q.cls_eq y, mk_eq_mk_iff] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨isoOfCocycleEq (x := a⁻¹ • x) (y := y) (Cocycle.ext fun g ↦ ?_)⟩
    rw [cocycle_smul, ha, smul_inv', inv_inv]
  · obtain ⟨x⟩ := P.nonempty
    rw [P.cls_eq x, Q.cls_eq (e.toEquiv x), e.cocycle_eq]

end SmoothTorsor

variable [TopologicalSpace A]

namespace Cocycle

variable {G A}

/-- The underlying set of the smooth torsor of a cocycle `f`: a copy of `A`, on which `A` acts
by left multiplication and `g : G` by `x ↦ (g • x) * (f g)⁻¹`. -/
@[ext]
structure Torsor (f : Cocycle G A) where
  /-- The element of `A`. -/
  val : A

namespace Torsor

variable (f : Cocycle G A)

/-- `A` acts on the torsor of a cocycle by left multiplication. -/
instance instMulActionA : MulAction A (Torsor f) where
  smul a x := ⟨a * x.val⟩
  one_smul x := Torsor.ext (one_mul x.val)
  mul_smul a b x := Torsor.ext (mul_assoc a b x.val)

@[simp]
theorem val_smul_A (a : A) (x : Torsor f) : (a • x).val = a * x.val :=
  (rfl)

/-- `g : G` acts on the torsor of `f` by `x ↦ (g • x) * (f g)⁻¹`. -/
instance instMulActionG : MulAction G (Torsor f) where
  smul g x := ⟨(g • x.val) * (f g)⁻¹⟩
  one_smul x := Torsor.ext (by
    change (1 : G) • x.val * (f 1)⁻¹ = x.val
    simp)
  mul_smul g h x := Torsor.ext (by
    change (g * h) • x.val * (f (g * h))⁻¹ = g • (h • x.val * (f h)⁻¹) * (f g)⁻¹
    simp only [f.apply_mul, smul_mul', smul_inv', mul_inv_rev, mul_smul, mul_assoc])

@[simp]
theorem val_smul_G (g : G) (x : Torsor f) : (g • x).val = (g • x.val) * (f g)⁻¹ :=
  (rfl)

end Torsor

variable [DiscreteTopology A] [ContinuousSMul G A]

/-- The **smooth torsor of a cocycle** `f`: the set `A` with `A` acting by left multiplication and
`g : G` by `x ↦ (g • x) * (f g)⁻¹`. Its stabilizers are open since `A` is discrete and the action
of `G` on `A` is continuous. -/
@[expose] noncomputable def torsor (f : Cocycle G A) : SmoothTorsor.{u, v, v} G A where
  carrier := Torsor f
  smul_smul_eq g a x := Torsor.ext (by simp [smul_mul', mul_assoc])
  isOpen_stabilizer x := by
    have hc : Continuous fun g : G ↦ (g • x.val, f g) :=
      (continuous_id.smul continuous_const).prodMk f.continuous
    have hs : (MulAction.stabilizer G x : Set G) =
        (fun g : G ↦ (g • x.val, f g)) ⁻¹' {p : A × A | p.1 * p.2⁻¹ = x.val} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe,
        MulAction.mem_stabilizer_iff, Torsor.ext_iff, Torsor.val_smul_G]
    rw [hs]
    exact (isOpen_discrete _).preimage hc
  bijective x :=
    ⟨fun a b hab ↦ mul_right_cancel (congrArg Torsor.val hab : a * x.val = b * x.val),
      fun y ↦ ⟨y.val * x.val⁻¹, Torsor.ext (by simp)⟩⟩
  nonempty := ⟨(⟨1⟩ : Torsor f)⟩

variable [ContinuousMul G]

/-- The cocycle of the torsor of `f` at the point `1` is `f`. -/
theorem cocycle_torsor (f : Cocycle G A) : f.torsor.cocycle (⟨1⟩ : Torsor f) = f :=
  ext fun g ↦ f.torsor.cocycle_apply_eq_iff.mpr <| Torsor.ext <| by
    change g • (1 : A) * (f g)⁻¹ = (f g)⁻¹ * 1
    simp

end Cocycle

namespace SmoothTorsor

variable {G A} [DiscreteTopology A] [ContinuousSMul G A] [ContinuousMul G]

/-- **Every class is the class of a smooth torsor**: the torsor of a cocycle has its class. -/
theorem cls_torsor (f : Cocycle G A) : f.torsor.cls = NonabelianH1.mk f := by
  rw [cls_eq _ (⟨1⟩ : Cocycle.Torsor f), Cocycle.cocycle_torsor]

/-- The class map from smooth torsors to `H¹(G, A)` is surjective. -/
theorem cls_surjective :
    Function.Surjective fun P : SmoothTorsor.{u, v, v} G A ↦ P.cls := by
  intro c
  obtain ⟨f, rfl⟩ := NonabelianH1.mk_surjective c
  exact ⟨f.torsor, cls_torsor f⟩

end SmoothTorsor

section Trivial

variable {G A}

/-- **Cocycles for the trivial action are continuous homomorphisms.** -/
def Cocycle.equivOfTrivial (h : ∀ (g : G) (a : A), g • a = a) : Cocycle G A ≃ (G →ₜ* A) where
  toFun f :=
    { toFun := f
      map_one' := f.apply_one
      map_mul' g g' := by rw [f.apply_mul, h]
      continuous_toFun := f.continuous }
  invFun φ := ⟨φ, φ.continuous, fun g g' ↦ by rw [map_mul, h]⟩

@[simp]
theorem Cocycle.equivOfTrivial_symm_apply (h : ∀ (g : G) (a : A), g • a = a) (φ : G →ₜ* A)
    (g : G) : (Cocycle.equivOfTrivial h).symm φ g = φ g :=
  (rfl)

@[simp]
theorem Cocycle.equivOfTrivial_apply (h : ∀ (g : G) (a : A), g • a = a) (f : Cocycle G A)
    (g : G) : Cocycle.equivOfTrivial h f g = f g :=
  (rfl)

variable (G A) in
/-- **Conjugacy of continuous homomorphisms**: `φ'` is conjugate to `φ` when
`φ' g = a⁻¹ * φ g * a` for one `a : A` and all `g`. -/
def conjSetoid : Setoid (G →ₜ* A) where
  r φ φ' := ∃ a : A, ∀ g, φ' g = a⁻¹ * φ g * a
  iseqv := by
    refine ⟨fun φ ↦ ⟨1, fun g ↦ by simp⟩, ?_, ?_⟩
    · rintro φ φ' ⟨a, ha⟩
      exact ⟨a⁻¹, fun g ↦ by simp [ha, mul_assoc]⟩
    · rintro φ φ' φ'' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, fun g ↦ by simp [ha, hb, mul_assoc]⟩

/-- For the trivial action, two cocycles are cohomologous exactly when the corresponding
homomorphisms are conjugate. -/
theorem Cocycle.equiv_iff_of_trivial (h : ∀ (g : G) (a : A), g • a = a) {f f' : Cocycle G A} :
    f ≈ f' ↔ conjSetoid G A (Cocycle.equivOfTrivial h f) (Cocycle.equivOfTrivial h f') := by
  change (∃ a : A, ∀ g, f' g = a⁻¹ * f g * g • a) ↔ ∃ a : A, ∀ g, f' g = a⁻¹ * f g * a
  simp only [h]

/-- **`H¹` for the trivial action**: when `G` acts trivially on `A`, `H¹(G, A)` is the set of
continuous homomorphisms `G → A` modulo conjugation by `A`. -/
def equivOfTrivial (h : ∀ (g : G) (a : A), g • a = a) :
    NonabelianH1 G A ≃ Quotient (conjSetoid G A) where
  toFun := lift (fun f ↦ Quotient.mk _ (Cocycle.equivOfTrivial h f)) fun _ _ hff' ↦
    Quotient.sound ((Cocycle.equiv_iff_of_trivial h).mp hff')
  invFun := Quotient.lift (fun φ ↦ mk ((Cocycle.equivOfTrivial h).symm φ)) fun _ _ ⟨a, ha⟩ ↦
    mk_eq_mk_iff.mpr ⟨a, fun g ↦ by simp [ha, h]⟩
  left_inv c := induction_on c fun f ↦ by simp
  right_inv φ := Quotient.inductionOn φ fun φ ↦ by simp

@[simp]
theorem equivOfTrivial_mk (h : ∀ (g : G) (a : A), g • a = a) (f : Cocycle G A) :
    equivOfTrivial h (mk f) = Quotient.mk _ (Cocycle.equivOfTrivial h f) :=
  lift_mk _ _ f

end Trivial

end NonabelianH1

end TauCeti
