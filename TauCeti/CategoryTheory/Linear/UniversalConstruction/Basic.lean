/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic

/-!
# State spaces from outgoing tests

Fix an object `U` of an `R`-linear category and a linear evaluation of its endomorphisms.
A filling of `X` is a morphism `U ⟶ X`; an outgoing test is a morphism `X ⟶ U`.
The state space is the quotient of fillings by those whose composite with every test
has evaluation zero. Postcomposition induces a linear functor to modules.

The descended pairing separates states, but need not be perfect. No finiteness,
nondegeneracy or scalar-extension assumption is used. The morphisms acting as zero on
states form a two-sided ideal, characterized by tests before and after the morphism.
If evaluation is multiplicative and normalized, the state space of `U` is `R`.
The distinguished object can in particular be the tensor unit of a linear monoidal category;
the construction here only uses its ordinary linear category.

## References

* C. Blanchet, N. Habegger, G. Masbaum and P. Vogel, *Topological quantum field theories
  derived from the Kauffman bracket*, Topology 34 (1995), 883–927, Proposition 1.1
  and the universal construction, p. 886.
* H. Goertz, L. Marino and P. Wedrich, *Monoidal 2-categories from foam evaluation*,
  arXiv:2602.11120v1, Lemmas 3.18–3.19.
-/

public section

namespace TauCeti.UniversalConstruction

open CategoryTheory

universe u v w

variable {R : Type w} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] (U : C) (ev : (U ⟶ U) →ₗ[R] R)

/-- Evaluate a filling against an outgoing test, in that order of composition. -/
def pairing (X : C) : (U ⟶ X) →ₗ[R] Module.Dual R (X ⟶ U) :=
  (Linear.comp (S := R) U X U).compr₂ ev

@[simp]
theorem pairing_apply (X : C) (a : U ⟶ X) (b : X ⟶ U) :
    pairing U ev X a b = ev (a ≫ b) := (rfl)

/-- Fillings invisible to every outgoing test. -/
def radical (X : C) : Submodule R (U ⟶ X) :=
  LinearMap.ker (pairing U ev X)

/-- Membership in the radical means vanishing against every outgoing test. -/
@[simp]
theorem mem_radical_iff {X : C} (a : U ⟶ X) :
    a ∈ radical U ev X ↔ ∀ b : X ⟶ U, ev (a ≫ b) = 0 := by
  simp only [radical, LinearMap.mem_ker, LinearMap.ext_iff, pairing_apply,
    LinearMap.zero_apply]

/-- Postcomposition carries invisible fillings to invisible fillings. -/
theorem comp_mem_radical {X Y : C} {a : U ⟶ X} (ha : a ∈ radical U ev X)
    (f : X ⟶ Y) : a ≫ f ∈ radical U ev Y := by
  rw [mem_radical_iff] at ha ⊢
  intro b
  simpa only [Category.assoc] using ha (f ≫ b)

/-- The module of states, obtained by dividing fillings by the outgoing-test radical. -/
abbrev State (X : C) := (U ⟶ X) ⧸ radical U ev X

/-- Equality of states is exactly indistinguishability by outgoing tests. -/
theorem mk_eq_iff {X : C} (a a' : U ⟶ X) :
    (Submodule.Quotient.mk a : State U ev X) = Submodule.Quotient.mk a' ↔
      ∀ b : X ⟶ U, ev (a ≫ b) = ev (a' ≫ b) := by
  rw [Submodule.Quotient.eq, mem_radical_iff]
  simp only [Preadditive.sub_comp, map_sub, sub_eq_zero]

/-- The descended outgoing pairing, viewed as a map into the dual of the test module. -/
def statePairing (X : C) : State U ev X →ₗ[R] Module.Dual R (X ⟶ U) :=
  (radical U ev X).liftQ (pairing U ev X) le_rfl

@[simp]
theorem statePairing_mk (X : C) (a : U ⟶ X) :
    statePairing U ev X (Submodule.Quotient.mk a) = pairing U ev X a := (rfl)

/-- Outgoing tests separate states. This asserts injectivity, not perfectness. -/
theorem statePairing_injective (X : C) : Function.Injective (statePairing U ev X) := by
  exact LinearMap.ker_eq_bot.mp
    ((radical U ev X).ker_liftQ_eq_bot (pairing U ev X) le_rfl le_rfl)

/-- States are equal if every outgoing test gives the same value. -/
@[ext]
theorem state_ext {X : C} {x y : State U ev X}
    (h : ∀ b : X ⟶ U, statePairing U ev X x b = statePairing U ev X y b) : x = y :=
  statePairing_injective U ev X (LinearMap.ext h)

/-- The map on states induced by postcomposing with a morphism. -/
def stateMap {X Y : C} (f : X ⟶ Y) : State U ev X →ₗ[R] State U ev Y :=
  (radical U ev X).mapQ (radical U ev Y) (Linear.rightComp R U f)
    (fun _ ha ↦ comp_mem_radical U ev ha f)

@[simp]
theorem stateMap_mk {X Y : C} (f : X ⟶ Y) (a : U ⟶ X) :
    stateMap U ev f (Submodule.Quotient.mk a) = Submodule.Quotient.mk (a ≫ f) := (rfl)

/-- Postcomposition on states is adjoint to precomposition on outgoing tests. -/
theorem statePairing_stateMap {X Y : C} (f : X ⟶ Y) (x : State U ev X) (b : Y ⟶ U) :
    statePairing U ev Y (stateMap U ev f x) b = statePairing U ev X x (f ≫ b) := by
  obtain ⟨a, rfl⟩ := (radical U ev X).mkQ_surjective x
  simp only [Submodule.mkQ_apply, stateMap_mk, statePairing_mk, pairing_apply, Category.assoc]

@[simp]
theorem stateMap_id (X : C) : stateMap U ev (𝟙 X) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (radical U ev X).mkQ_surjective x
  simp only [Submodule.mkQ_apply, stateMap_mk, LinearMap.id_apply, Category.comp_id]

@[simp]
theorem stateMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    stateMap U ev (f ≫ g) = (stateMap U ev g).comp (stateMap U ev f) := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (radical U ev X).mkQ_surjective x
  simp only [Submodule.mkQ_apply, stateMap_mk, LinearMap.comp_apply, Category.assoc]

@[simp]
theorem stateMap_add {X Y : C} (f g : X ⟶ Y) :
    stateMap U ev (f + g) = stateMap U ev f + stateMap U ev g := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (radical U ev X).mkQ_surjective x
  simp only [Submodule.mkQ_apply, stateMap_mk, LinearMap.add_apply,
    Preadditive.comp_add, Submodule.Quotient.mk_add]

@[simp]
theorem stateMap_smul {X Y : C} (r : R) (f : X ⟶ Y) :
    stateMap U ev (r • f) = r • stateMap U ev f := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (radical U ev X).mkQ_surjective x
  simp only [Submodule.mkQ_apply, stateMap_mk, LinearMap.smul_apply,
    Linear.comp_smul, Submodule.Quotient.mk_smul]

/-- The linear state-space functor associated to an evaluation at a distinguished object. -/
-- The object carrier must reduce to `State` for morphisms and states to share their API.
@[expose, implicit_reducible, simps obj]
def stateFunctor : C ⥤ ModuleCat.{v} R where
  obj X := ModuleCat.of R (State U ev X)
  map f := ModuleCat.ofHom (stateMap U ev f)
  map_id X := by apply ModuleCat.hom_ext; exact stateMap_id U ev X
  map_comp f g := by apply ModuleCat.hom_ext; exact stateMap_comp U ev f g

@[simp]
theorem stateFunctor_map_hom {X Y : C} (f : X ⟶ Y) :
    ((stateFunctor U ev).map f).hom = stateMap U ev f := (rfl)

instance : (stateFunctor U ev).Additive where
  map_add := by intro X Y f g; apply ModuleCat.hom_ext; exact stateMap_add U ev f g

instance : (stateFunctor U ev).Linear R where
  map_smul := by intro X Y f r; apply ModuleCat.hom_ext; exact stateMap_smul U ev r f

/-- The state-action ideal: morphisms inducing zero on all states. -/
abbrev actionIdeal : MorphismIdeal C := (stateFunctor U ev).kerIdeal

/-- A morphism acts as zero exactly when every filling and subsequent outgoing test vanish. -/
theorem mem_actionIdeal_iff {X Y : C} (f : X ⟶ Y) :
    f ∈ (actionIdeal U ev).hom X Y ↔
      ∀ (a : U ⟶ X) (b : Y ⟶ U), ev (a ≫ f ≫ b) = 0 := by
  rw [CategoryTheory.Functor.mem_kerIdeal_hom]
  constructor
  · intro h a b
    have hz : stateMap U ev f (Submodule.Quotient.mk a) = 0 := by
      exact congrArg (fun k ↦ (k : (stateFunctor U ev).obj X ⟶
        (stateFunctor U ev).obj Y) (Submodule.Quotient.mk a)) h
    have ha := (Submodule.Quotient.mk_eq_zero (radical U ev Y)).1 hz
    simpa only [Category.assoc] using (mem_radical_iff U ev (a ≫ f)).1 ha b
  · intro h
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨a, rfl⟩ := (radical U ev X).mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero (radical U ev Y)).2
    exact (mem_radical_iff U ev (a ≫ f)).2 (by simpa using h a)

section Unit

variable (hmul : ∀ a b : U ⟶ U, ev (a ≫ b) = ev a * ev b) (hone : ev (𝟙 U) = 1)

include hmul

/-- For a multiplicative evaluation, the radical at `U` is its kernel. -/
theorem radical_unit : radical U ev U = LinearMap.ker ev := by
  ext a
  rw [mem_radical_iff, LinearMap.mem_ker]
  constructor
  · intro h
    simpa using h (𝟙 U)
  · intro h b
    rw [hmul, h, zero_mul]

/-- Evaluate a state of the distinguished object. -/
def unitEvaluation : State U ev U →ₗ[R] R :=
  (radical U ev U).liftQ ev (radical_unit U ev hmul ▸ le_rfl)

@[simp]
theorem unitEvaluation_mk (a : U ⟶ U) :
    unitEvaluation U ev hmul (Submodule.Quotient.mk a) = ev a := (rfl)

/-- The empty filling generates the unit state module. -/
theorem mk_unit (a : U ⟶ U) :
    (Submodule.Quotient.mk a : State U ev U) = ev a • Submodule.Quotient.mk (𝟙 U) := by
  rw [← Submodule.Quotient.mk_smul, mk_eq_iff]
  intro b
  simp [hmul]

/-- A multiplicative normalized evaluation identifies the unit state space with the scalars. -/
def unitEquiv : State U ev U ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (unitEvaluation U ev hmul)
    (LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk (𝟙 U)))
    (by ext; simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
          map_smul, unitEvaluation_mk, hone, smul_eq_mul, mul_one,
          LinearMap.id_apply])
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨a, rfl⟩ := (radical U ev U).mkQ_surjective x
      simp only [Submodule.mkQ_apply, LinearMap.comp_apply, unitEvaluation_mk,
        LinearMap.toSpanSingleton_apply,
        LinearMap.id_apply]
      exact (mk_unit U ev hmul a).symm)

@[simp]
theorem unitEquiv_mk (a : U ⟶ U) :
    unitEquiv U ev hmul hone (Submodule.Quotient.mk a) = ev a := (rfl)

@[simp]
theorem unitEquiv_symm_apply (r : R) :
    (unitEquiv U ev hmul hone).symm r = r • Submodule.Quotient.mk (𝟙 U) := (rfl)

end Unit

end TauCeti.UniversalConstruction
