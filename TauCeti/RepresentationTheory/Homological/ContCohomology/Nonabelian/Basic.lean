/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Continuous nonabelian first cohomology

Let a group `G` with a topology act on a group `A` with a topology by group automorphisms
(`MulDistribMulAction G A`); `A` need not be commutative. A **continuous `1`-cocycle** is a
continuous map `f : G → A` with

`f (g * h) = f g * g • f h`,

and two cocycles `f, f'` are **cohomologous** when `f' g = a⁻¹ * f g * g • a` for one `a : A`
and all `g`. The quotient is the pointed set `H¹(G, A)`, whose base point is the class of the
trivial cocycle. For a commutative `A` the cocycles and the relation are the classical ones of
abelian first cohomology, written multiplicatively; for a general `A` the quotient carries no group
structure, and only its base point is distinguished.

This is the cohomology that classifies forms and twists: for a Galois extension with group `G`
and an object whose automorphism group is `A`, the twists of the object are classified by
`H¹(G, A)` (Serre, *Galois Cohomology*, III.1). For the twists of an elliptic curve, `G` is an
absolute Galois group and `A` the automorphism group of the curve over a separable closure, with
the discrete topology.

The functoriality is that of *compatible pairs*: a continuous homomorphism `ψ : G' →ₜ* G` and a
continuous homomorphism `φ : A →ₜ* A'` with `φ (ψ g • a) = g • φ a` send cocycles to cocycles by
`f ↦ φ ∘ f ∘ ψ`, preserving cohomology. Taking `ψ` to be the inclusion of a subgroup gives
restriction. Inflation, the other named instance, is in
`TauCeti/RepresentationTheory/Homological/ContCohomology/Nonabelian/Inflation.lean`.

## Main definitions

* `TauCeti.NonabelianH1.Cocycle G A`: the continuous `1`-cocycles of `G` with values in `A`.
* `TauCeti.NonabelianH1.Cocycle.setoid`: the cohomology relation on cocycles.
* `TauCeti.NonabelianH1.Cocycle.twist`: the twist `g ↦ a⁻¹ * f g * g • a` of a cocycle by
  `a : A`; two cocycles are cohomologous exactly when one is a twist of the other
  (`TauCeti.NonabelianH1.Cocycle.equiv_iff_exists_twist_eq`).
* `TauCeti.NonabelianH1 G A`: the pointed set `H¹(G, A)` of cohomology classes, with
  `TauCeti.NonabelianH1.mk` the class of a cocycle.
* `TauCeti.NonabelianH1.Cocycle.map` and `TauCeti.NonabelianH1.map`: the maps of cocycles and of
  classes induced by a compatible pair.
* `TauCeti.NonabelianH1.res`: restriction to a subgroup.

## Main results

* `TauCeti.NonabelianH1.mk_eq_mk_iff`: two cocycles have the same class exactly when they are
  cohomologous.
* `TauCeti.NonabelianH1.mk_eq_one_iff`: the class of a cocycle is the base point exactly when the
  cocycle is a coboundary `g ↦ a⁻¹ * g • a`.
* `TauCeti.NonabelianH1.map_one`, `TauCeti.NonabelianH1.map_id` and
  `TauCeti.NonabelianH1.map_map`: the induced maps are maps of pointed sets, and the construction
  is functorial.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5 and III.1.
-/

public section

namespace TauCeti

variable (G A : Type*) [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
  [MulDistribMulAction G A]

/-- A **continuous `1`-cocycle** of `G` with values in the `G`-group `A`: a continuous map
`f : G → A` with `f (g * h) = f g * g • f h`. -/
structure NonabelianH1.Cocycle where
  /-- The underlying function of a cocycle. -/
  toFun : G → A
  /-- A cocycle is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The cocycle identity `f (g * h) = f g * g • f h`. -/
  map_mul' : ∀ g h : G, toFun (g * h) = toFun g * g • toFun h

namespace NonabelianH1

namespace Cocycle

variable {G A}

instance : FunLike (Cocycle G A) G A where
  coe := toFun
  coe_injective f f' h := by
    cases f
    cases f'
    congr

@[ext]
theorem ext {f f' : Cocycle G A} (h : ∀ g, f g = f' g) : f = f' :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : G → A) (hf : Continuous f) (hmul : ∀ g h : G, f (g * h) = f g * g • f h) :
    ⇑(⟨f, hf, hmul⟩ : Cocycle G A) = f :=
  (rfl)

/-- A cocycle is continuous. -/
@[continuity, fun_prop]
theorem continuous (f : Cocycle G A) : Continuous f :=
  f.continuous_toFun

/-- The cocycle identity. -/
theorem apply_mul (f : Cocycle G A) (g h : G) : f (g * h) = f g * g • f h :=
  f.map_mul' g h

/-- A cocycle takes the value `1` at `1`. -/
@[simp]
theorem apply_one (f : Cocycle G A) : f 1 = 1 := by
  simpa using f.apply_mul 1 1

/-- The value of a cocycle at an inverse. -/
theorem apply_inv (f : Cocycle G A) (g : G) : f g⁻¹ = g⁻¹ • (f g)⁻¹ := by
  have h := f.apply_mul g⁻¹ g
  rw [inv_mul_cancel, apply_one, eq_comm, mul_eq_one_iff_eq_inv] at h
  rw [h, smul_inv']

/-- The trivial cocycle `g ↦ 1`. -/
instance : One (Cocycle G A) :=
  ⟨⟨fun _ ↦ 1, continuous_const, fun g h ↦ by simp⟩⟩

@[simp]
theorem one_apply (g : G) : (1 : Cocycle G A) g = 1 :=
  (rfl)

instance : Inhabited (Cocycle G A) :=
  ⟨1⟩

/-- The **cohomology relation** on cocycles: `f ≈ f'` when `f' g = a⁻¹ * f g * g • a` for one
`a : A` and all `g : G`. -/
instance setoid : Setoid (Cocycle G A) where
  r f f' := ∃ a : A, ∀ g, f' g = a⁻¹ * f g * g • a
  iseqv := by
    refine ⟨fun f ↦ ⟨1, fun g ↦ by simp⟩, ?_, ?_⟩
    · rintro f f' ⟨a, ha⟩
      exact ⟨a⁻¹, fun g ↦ by simp [ha, mul_assoc]⟩
    · rintro f f' f'' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, fun g ↦ by simp [ha, hb, mul_assoc, smul_mul']⟩

theorem equiv_iff {f f' : Cocycle G A} : f ≈ f' ↔ ∃ a : A, ∀ g, f' g = a⁻¹ * f g * g • a :=
  Iff.rfl

section Twist

variable [ContinuousMul A] [ContinuousSMul G A]

/-- The **twist** `g ↦ a⁻¹ * f g * g • a` of a cocycle `f` by `a : A`, the action of `A` on
cocycles whose orbits are the cohomology classes. -/
def twist (f : Cocycle G A) (a : A) : Cocycle G A where
  toFun g := a⁻¹ * f g * g • a
  continuous_toFun := by fun_prop
  map_mul' g h := by
    simp only [f.apply_mul, mul_smul, smul_mul', smul_inv', mul_assoc, mul_inv_cancel_left]

@[simp]
theorem twist_apply (f : Cocycle G A) (a : A) (g : G) : f.twist a g = a⁻¹ * f g * g • a :=
  (rfl)

@[simp]
theorem twist_one (f : Cocycle G A) : f.twist 1 = f :=
  ext fun g ↦ by simp

theorem twist_twist (f : Cocycle G A) (a b : A) : (f.twist a).twist b = f.twist (a * b) :=
  ext fun g ↦ by simp [mul_assoc, smul_mul']

/-- Two cocycles are cohomologous exactly when one is a twist of the other. -/
theorem equiv_iff_exists_twist_eq {f f' : Cocycle G A} : f ≈ f' ↔ ∃ a : A, f.twist a = f' := by
  simp only [equiv_iff, Cocycle.ext_iff, twist_apply, eq_comm]

theorem equiv_twist (f : Cocycle G A) (a : A) : f ≈ f.twist a :=
  equiv_iff_exists_twist_eq.mpr ⟨a, rfl⟩

end Twist

end Cocycle

end NonabelianH1

/-- The **continuous nonabelian first cohomology** `H¹(G, A)`: continuous `1`-cocycles of `G` with
values in `A`, up to the cohomology relation. It is a pointed set, with base point the class of
the trivial cocycle. -/
def NonabelianH1 : Type _ :=
  Quotient (NonabelianH1.Cocycle.setoid (G := G) (A := A))

namespace NonabelianH1

variable {G A}

/-- The cohomology class of a cocycle. -/
def mk (f : Cocycle G A) : NonabelianH1 G A :=
  Quotient.mk _ f

theorem mk_surjective : Function.Surjective (mk : Cocycle G A → NonabelianH1 G A) :=
  Quotient.mk_surjective

@[elab_as_elim]
theorem induction_on {motive : NonabelianH1 G A → Prop} (c : NonabelianH1 G A)
    (mk : ∀ f : Cocycle G A, motive (mk f)) : motive c :=
  Quotient.inductionOn c mk

/-- Two cocycles have the same class exactly when they are cohomologous. -/
theorem mk_eq_mk_iff {f f' : Cocycle G A} :
    mk f = mk f' ↔ ∃ a : A, ∀ g, f' g = a⁻¹ * f g * g • a :=
  Quotient.eq

/-- The base point of `H¹(G, A)`, the class of the trivial cocycle. -/
instance : One (NonabelianH1 G A) :=
  ⟨mk 1⟩

instance : Inhabited (NonabelianH1 G A) :=
  ⟨1⟩

theorem one_def : (1 : NonabelianH1 G A) = mk 1 :=
  (rfl)

@[simp]
theorem mk_one : mk (1 : Cocycle G A) = 1 :=
  (rfl)

/-- The class of a cocycle is the base point exactly when the cocycle is a **coboundary**
`g ↦ a⁻¹ * g • a`. -/
theorem mk_eq_one_iff {f : Cocycle G A} : mk f = 1 ↔ ∃ a : A, ∀ g, f g = a⁻¹ * g • a := by
  rw [one_def, eq_comm, mk_eq_mk_iff]
  simp only [Cocycle.one_apply, mul_one]

/-- A twisted cocycle has the same class. -/
@[simp]
theorem mk_twist [ContinuousMul A] [ContinuousSMul G A] (f : Cocycle G A) (a : A) :
    mk (f.twist a) = mk f :=
  (Quotient.sound (f.equiv_twist a)).symm

section Map

variable {G' A' : Type*} [Group G'] [TopologicalSpace G'] [Group A'] [TopologicalSpace A']
  [MulDistribMulAction G' A']

/-- The cocycle `φ ∘ f ∘ ψ` induced by a **compatible pair** `(ψ, φ)`: continuous homomorphisms
`ψ : G' →ₜ* G` and `φ : A →ₜ* A'` with `φ (ψ g • a) = g • φ a`. -/
def Cocycle.map (ψ : G' →ₜ* G) (φ : A →ₜ* A') (h : ∀ (g : G') (a : A), φ (ψ g • a) = g • φ a)
    (f : Cocycle G A) : Cocycle G' A' where
  toFun g := φ (f (ψ g))
  continuous_toFun := by fun_prop
  map_mul' g g' := by rw [_root_.map_mul, f.apply_mul, _root_.map_mul, h]

@[simp]
theorem Cocycle.map_apply (ψ : G' →ₜ* G) (φ : A →ₜ* A')
    (h : ∀ (g : G') (a : A), φ (ψ g • a) = g • φ a) (f : Cocycle G A) (g : G') :
    f.map ψ φ h g = φ (f (ψ g)) :=
  (rfl)

/-- A compatible pair sends the trivial cocycle to the trivial cocycle. -/
@[simp]
theorem Cocycle.map_one (ψ : G' →ₜ* G) (φ : A →ₜ* A')
    (h : ∀ (g : G') (a : A), φ (ψ g • a) = g • φ a) :
    (1 : Cocycle G A).map ψ φ h = 1 := by
  ext
  simp

/-- The map `H¹(G, A) → H¹(G', A')` induced by a compatible pair `(ψ, φ)`. -/
def map (ψ : G' →ₜ* G) (φ : A →ₜ* A') (h : ∀ (g : G') (a : A), φ (ψ g • a) = g • φ a) :
    NonabelianH1 G A → NonabelianH1 G' A' :=
  Quotient.map (Cocycle.map ψ φ h) fun _ _ ⟨a, ha⟩ ↦
    ⟨φ a, fun g ↦ by simp [ha, h]⟩

@[simp]
theorem map_mk (ψ : G' →ₜ* G) (φ : A →ₜ* A') (h : ∀ (g : G') (a : A), φ (ψ g • a) = g • φ a)
    (f : Cocycle G A) : map ψ φ h (mk f) = mk (f.map ψ φ h) :=
  (rfl)

/-- The map induced by a compatible pair preserves the base point. -/
@[simp]
theorem map_one (ψ : G' →ₜ* G) (φ : A →ₜ* A') (h : ∀ (g : G') (a : A), φ (ψ g • a) = g • φ a) :
    map ψ φ h 1 = 1 := by
  rw [one_def, map_mk, Cocycle.map_one, mk_one]

/-- The identity pair induces the identity. -/
@[simp]
theorem map_id :
    map (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id A) (fun _ _ ↦ rfl) =
      (id : NonabelianH1 G A → NonabelianH1 G A) := by
  funext c
  induction c using induction_on
  rfl

/-- The maps induced by compatible pairs compose. -/
theorem map_map {G'' A'' : Type*} [Group G''] [TopologicalSpace G''] [Group A'']
    [TopologicalSpace A''] [MulDistribMulAction G'' A''] (ψ : G' →ₜ* G) (φ : A →ₜ* A')
    (h : ∀ (g : G') (a : A), φ (ψ g • a) = g • φ a) (ψ' : G'' →ₜ* G') (φ' : A' →ₜ* A'')
    (h' : ∀ (g : G'') (a : A'), φ' (ψ' g • a) = g • φ' a) (c : NonabelianH1 G A) :
    map ψ' φ' h' (map ψ φ h c) =
      map (ψ.comp ψ') (φ'.comp φ) (fun g a ↦ by simp [h, h']) c := by
  induction c using induction_on
  rfl

end Map

section Res

/-- The inclusion of a subgroup and the identity of `A` form a compatible pair. -/
theorem id_subgroupSubtype_smul (S : Subgroup G) (s : S) (a : A) :
    ContinuousMonoidHom.id A (ContinuousMonoidHom.subgroupSubtype S s • a) =
      s • ContinuousMonoidHom.id A a :=
  (rfl)

/-- **Restriction** `H¹(G, A) → H¹(S, A)` to a subgroup `S`, carrying the subspace topology: the
map induced by the inclusion of `S` and the identity of `A`. -/
def res (S : Subgroup G) : NonabelianH1 G A → NonabelianH1 S A :=
  map (ContinuousMonoidHom.subgroupSubtype S) (ContinuousMonoidHom.id A) (id_subgroupSubtype_smul S)

/-- Restriction restricts a representing cocycle. -/
theorem res_mk (S : Subgroup G) (f : Cocycle G A) :
    res S (mk f) =
      mk (f.map (ContinuousMonoidHom.subgroupSubtype S) (ContinuousMonoidHom.id A)
        (id_subgroupSubtype_smul S)) :=
  map_mk _ _ _ f

/-- Restriction preserves the base point. -/
@[simp]
theorem res_one (S : Subgroup G) : res S (1 : NonabelianH1 G A) = 1 :=
  map_one _ _ _

end Res

end NonabelianH1

end TauCeti
