/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Weakly contractible simplicial sets

A simplicial set `K` is *weakly contractible* (`SSet.IsWeaklyContractible`) when, for every Kan
complex `Z`, the inclusion `SSet.constMaps K Z : Z ⟶ Fun(K, Z)` of the constant maps into the
internal hom is a simplicial homotopy equivalence. This is the mapping-space formulation used to
define final maps of quasicategories: a map `K ⟶ L` is final when its fibre products with the
coslices of `L` are weakly contractible.

A simplicial set with a homotopy from a constant map to its identity, such as a standard simplex
(`SSet.stdSimplex.contraction`), is weakly contractible: evaluation at the vertex is a homotopy
inverse. Conversely, a weakly contractible simplicial set is nonempty, since `Fun(K, Z)` has a
vertex when `K` is empty, while the empty simplicial set is a Kan complex without vertices. Every
map from it to a Kan complex is homotopic to a constant map, and testing this against its map to
the discrete simplicial set on its connected components shows that it is connected.

The comparison with the weak equivalences of
`TauCeti/AlgebraicTopology/SimplicialSet/WeakEquivalence.lean`, namely that `K` is weakly
contractible exactly when `K ⟶ Δ[0]` is a weak homotopy equivalence, needs the homotopy theory
of the Kan–Quillen model structure and is not proved here.

## Main declarations

* `SSet.constMaps K Z`: the constant maps `Z ⟶ Fun(K, Z)`, and `SSet.evalAt x Z`, evaluation at a
  vertex `x`, which is a retraction of it (`SSet.constMaps_evalAt`).
* `SSet.IsWeaklyContractible`: weakly contractible simplicial sets.
* `SSet.IsWeaklyContractible.of_homotopy`: contractible simplicial sets are weakly contractible;
  in particular every standard simplex `Δ[n]` is.
* `SSet.IsWeaklyContractible.of_iso`: invariance under isomorphism.
* `SSet.IsWeaklyContractible.nonempty`: the empty simplicial set is not weakly contractible.
* `SSet.IsWeaklyContractible.exists_homotopy_const`: maps to Kan complexes are homotopic to
  constant maps.
* `SSet.IsWeaklyContractible.isConnected`: weakly contractible simplicial sets are connected.

## References

* J. Lurie, *Higher Topos Theory*, Definition 4.1.1.1 and Proposition 4.1.1.3.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed Opposite

open scoped Simplicial

universe u

namespace SSet

variable (K : SSet.{u})

/-- The inclusion `Z ⟶ Fun(K, Z)` of the constant maps, adjoint to the projection
`K ⊗ Z ⟶ Z`. -/
noncomputable def constMaps (Z : SSet.{u}) : Z ⟶ (ihom K).obj Z :=
  curry (snd K Z)

variable {K} in
/-- Evaluation `Fun(K, Z) ⟶ Z` at a vertex `x` of `K`. -/
noncomputable def evalAt (x : K _⦋0⦌) (Z : SSet.{u}) : (ihom K).obj Z ⟶ Z :=
  lift (const x) (𝟙 _) ≫ (ihom.ev K).app Z

/-- Evaluating a constant map at a vertex returns its value. -/
@[reassoc (attr := simp)]
lemma constMaps_evalAt (x : K _⦋0⦌) (Z : SSet.{u}) : constMaps K Z ≫ evalAt x Z = 𝟙 Z := by
  rw [constMaps, evalAt, comp_lift_assoc, comp_const, Category.comp_id,
    ← Category.id_comp (curry _), ← lift_whiskerLeft, Category.assoc, whiskerLeft_curry_ihom_ev_app,
    lift_snd]

/-- Precomposition with a map `f : K ⟶ L` sends constant maps out of `L` to constant maps out
of `K`. -/
@[reassoc (attr := simp)]
lemma constMaps_pre {L : SSet.{u}} (f : K ⟶ L) (Z : SSet.{u}) :
    constMaps L Z ≫ (pre f).app Z = constMaps K Z := by
  rw [constMaps, constMaps, curry_pre_app, whiskerRight_snd]

/-- A simplicial set `K` is *weakly contractible* when, for every Kan complex `Z`, the inclusion
of the constant maps `Z ⟶ Fun(K, Z)` is a simplicial homotopy equivalence. -/
class IsWeaklyContractible : Prop where
  exists_homotopyInverse (Z : SSet.{u}) [KanComplex Z] :
    ∃ g : (ihom K).obj Z ⟶ Z, Nonempty (Homotopy (constMaps K Z ≫ g) (𝟙 Z)) ∧
      Nonempty (Homotopy (g ≫ constMaps K Z) (𝟙 _))

variable {K}

/-- Evaluating at `x` and then taking the constant map is adjoint to evaluation at `x` on the
second factor of `K ⊗ Fun(K, Z)`. -/
lemma evalAt_constMaps (x : K _⦋0⦌) (Z : SSet.{u}) :
    evalAt x Z ≫ constMaps K Z = curry (snd K _ ≫ evalAt x Z) := by
  rw [constMaps, ← curry_natural_left, whiskerLeft_snd]

section

variable (h : K ⊗ Δ[1] ⟶ K) (Z : SSet.{u})

/-- The map `Fun(K, Z) ⊗ Δ[1] ⟶ Fun(K, Z)` precomposing with a map `h : K ⊗ Δ[1] ⟶ K`. -/
private noncomputable def contractingMap : (ihom K).obj Z ⊗ Δ[1] ⟶ (ihom K).obj Z :=
  curry (lift (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ h) (snd _ _ ≫ fst _ _) ≫ (ihom.ev K).app Z)

private lemma ι₀_contractingMap {x : K _⦋0⦌} (h₀ : ι₀ ≫ h = const x) :
    ι₀ ≫ contractingMap h Z = evalAt x Z ≫ constMaps K Z := by
  rw [evalAt_constMaps, contractingMap, ← curry_natural_left, ← Category.assoc, evalAt,
    ← Category.assoc]
  congr 2
  have hι₀ :
      lift (K ◁ ι₀ ≫ fst _ _) (K ◁ ι₀ ≫ snd _ _ ≫ snd _ _) = fst K ((ihom K).obj Z) ≫ ι₀ := by
    ext : 1 <;> simp
  ext : 1
  · rw [Category.assoc, lift_fst, comp_lift_assoc, hι₀, Category.assoc, h₀]
    simp
  · simp

private lemma ι₁_contractingMap (h₁ : ι₁ ≫ h = 𝟙 K) : ι₁ ≫ contractingMap h Z = 𝟙 _ := by
  rw [contractingMap, ← curry_natural_left, curry_eq_iff, uncurry_id_eq_ev, ← Category.assoc]
  convert Category.id_comp _
  have hι₁ :
      lift (K ◁ ι₁ ≫ fst _ _) (K ◁ ι₁ ≫ snd _ _ ≫ snd _ _) = fst K ((ihom K).obj Z) ≫ ι₁ := by
    ext : 1 <;> simp
  ext : 1
  · rw [Category.assoc, lift_fst, comp_lift_assoc, hι₁, Category.assoc, h₁]
    simp
  · simp

end

/-- A homotopy from a constant map to the identity of `K` contracts the mapping spaces out of `K`
onto their values at the vertex. -/
noncomputable def homotopyEvalAtConstMaps {x : K _⦋0⦌} (H : Homotopy (const x) (𝟙 K))
    (Z : SSet.{u}) : Homotopy (evalAt x Z ≫ constMaps K Z) (𝟙 _) where
  h := contractingMap H.h Z
  h₀ := ι₀_contractingMap H.h Z H.h₀
  h₁ := ι₁_contractingMap H.h Z H.h₁
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

namespace IsWeaklyContractible

/-- A simplicial set with a homotopy from a constant map to its identity is weakly
contractible. -/
lemma of_homotopy {x : K _⦋0⦌} (H : Homotopy (const x) (𝟙 K)) : IsWeaklyContractible K where
  exists_homotopyInverse Z _ :=
    ⟨evalAt x Z, ⟨.ofEq (congrArg _ (constMaps_evalAt K x Z))⟩, ⟨homotopyEvalAtConstMaps H Z⟩⟩

instance (n : ℕ) : IsWeaklyContractible Δ[n] :=
  of_homotopy (stdSimplex.contraction n)

/-- Weak contractibility is invariant under isomorphism. -/
lemma of_iso {L : SSet.{u}} (e : K ≅ L) [IsWeaklyContractible K] : IsWeaklyContractible L where
  exists_homotopyInverse Z _ := by
    obtain ⟨g, ⟨H₁⟩, ⟨H₂⟩⟩ := exists_homotopyInverse (K := K) Z
    obtain ⟨h, h₀, h₁⟩ : ∃ h : (ihom K).obj Z ⊗ Δ[1] ⟶ (ihom K).obj Z,
        ι₀ ≫ h = g ≫ constMaps K Z ∧ ι₁ ≫ h = 𝟙 _ := ⟨H₂.h, H₂.h₀, H₂.h₁⟩
    have hPQ : (pre e.hom).app Z ≫ (pre e.inv).app Z = 𝟙 _ := by
      rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id, NatTrans.id_app]
    let P := (pre e.hom).app Z
    refine ⟨P ≫ g, ⟨?_⟩, ⟨{ h := P ▷ _ ≫ h ≫ (pre e.inv).app Z, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩⟩
    · rwa [constMaps_pre_assoc]
    · -- `change` unfolds `RelativeMorphism.botEquiv.symm` in the types of the fields.
      change ι₀ ≫ _ = ((pre e.hom).app Z ≫ g) ≫ constMaps L Z
      rw [ι₀_comp_assoc, reassoc_of% h₀, constMaps_pre, Category.assoc]
    · change ι₁ ≫ _ = 𝟙 _
      rw [ι₁_comp_assoc, reassoc_of% h₁, hPQ]
    · ext _ ⟨⟨_, ⟨⟩⟩, _⟩

variable [IsWeaklyContractible K]

/-- A weakly contractible simplicial set is nonempty: otherwise `Fun(K, ∅)` would be a point
admitting no map to the empty Kan complex. -/
lemma nonempty : K.Nonempty := by
  by_contra hK
  let E : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  have : KanComplex E := by
    rw [KanComplex.iff]
    intro n i f _
    exact ((f _ (i.succAbove_ne 0)).app _ (stdSimplex.obj₀Equiv.symm 0)).2.elim
  obtain ⟨g, -⟩ := exists_homotopyInverse (K := K) E
  exact ((curry (fst K Δ[0] ≫ (isInitialOfNotNonempty hK).to E) ≫ g).app _
    (stdSimplex.obj₀Equiv.symm 0)).2.elim

/-- Every map from a weakly contractible simplicial set to a Kan complex is homotopic to a
constant map. -/
lemma exists_homotopy_const {Z : SSet.{u}} [KanComplex Z] (f : K ⟶ Z) :
    ∃ z : Z _⦋0⦌, Nonempty (Homotopy (const z) f) := by
  obtain ⟨g, -, ⟨H⟩⟩ := exists_homotopyInverse (K := K) Z
  obtain ⟨h, h₀, h₁⟩ : ∃ h : (ihom K).obj Z ⊗ Δ[1] ⟶ (ihom K).obj Z,
      ι₀ ≫ h = g ≫ constMaps K Z ∧ ι₁ ≫ h = 𝟙 _ := ⟨H.h, H.h₀, H.h₁⟩
  let v : (Δ[0] : SSet.{u}) _⦋0⦌ := stdSimplex.obj₀Equiv.symm 0
  let φ : Δ[0] ⟶ (ihom K).obj Z := curry (fst K _ ≫ f)
  -- The edge of `Fun(K, Z)` traced by the homotopy `h` at the vertex `f`.
  let e : Δ[1] ⟶ (ihom K).obj Z := lift (const v) (𝟙 _) ≫ φ ▷ Δ[1] ≫ h
  have he₀ :
      const (X := K) (stdSimplex.obj₀Equiv.symm 0) ≫ e = const v ≫ φ ≫ g ≫ constMaps K Z := by
    rw [← h₀, ← ι₀_comp_assoc]
    simp only [e, ← Category.assoc]
    congr 2
  have he₁ : const (X := K) (stdSimplex.obj₀Equiv.symm 1) ≫ e = const v ≫ φ := by
    rw [← Category.comp_id φ, ← h₁, ← ι₁_comp_assoc]
    simp only [e, ← Category.assoc]
    congr 2
  -- Through `uncurry`, the edge `e` is a homotopy `K ⊗ Δ[1] ⟶ Z`, whose ends are the values of
  -- `e` at the vertices of `Δ[1]`, both curried.
  have hι₀ : ι₀ ≫ K ◁ e = lift (𝟙 K) (const (stdSimplex.obj₀Equiv.symm 0) ≫ e) := by
    ext : 1 <;> simp
  have hι₁ : ι₁ ≫ K ◁ e = lift (𝟙 K) (const (stdSimplex.obj₀Equiv.symm 1) ≫ e) := by
    ext : 1 <;> simp
  refine ⟨(φ ≫ g).app _ v, ⟨{ h := uncurry e, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩⟩
  · -- `change` unfolds `RelativeMorphism.botEquiv.symm` in the types of the fields.
    change ι₀ ≫ uncurry e = const _
    rw [uncurry_eq, reassoc_of% hι₀, he₀, ← Category.assoc, ← Category.assoc, constMaps,
      ← lift_whiskerLeft, Category.assoc, whiskerLeft_curry_ihom_ev_app, lift_snd, Category.assoc,
      const_comp]
  · change ι₁ ≫ uncurry e = f
    rw [uncurry_eq, reassoc_of% hι₁, he₁, ← lift_whiskerLeft, Category.assoc,
      whiskerLeft_curry_ihom_ev_app, ← Category.assoc, lift_fst, Category.id_comp]
  · ext _ ⟨⟨_, ⟨⟩⟩, _⟩

/-- A weakly contractible simplicial set is connected. -/
instance isConnected : K.IsConnected where
  nonempty := nonempty
  allEq := π₀.rec fun x ↦ π₀.rec fun y ↦ by
    obtain ⟨z, ⟨H⟩⟩ := exists_homotopy_const (toπ₀ K)
    obtain ⟨h, h₀, h₁⟩ : ∃ h : K ⊗ Δ[1] ⟶ _, ι₀ ≫ h = const z ∧ ι₁ ≫ h = toπ₀ K :=
      ⟨H.h, H.h₀, H.h₁⟩
    suffices key : ∀ x : K _⦋0⦌, π₀.mk x = z from (key x).trans (key y).symm
    intro x
    -- The homotopy is constant along the edge `(σ₀ x, 𝟙)` of `K ⊗ Δ[1]`, because its target is
    -- discrete: the faces of a discrete simplicial set, and its constant maps in degree `0`, are
    -- identities by definition.
    let e : (K ⊗ Δ[1] : SSet.{u}) _⦋1⦌ := ⟨K.σ 0 x, stdSimplex.objEquiv.symm (𝟙 _)⟩
    have e₀ : (K ⊗ Δ[1]).δ 1 e = ι₀.app _ x :=
      Prod.ext (K.δ_comp_σ_succ_apply 0 x) (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)
    have e₁ : (K ⊗ Δ[1]).δ 0 e = ι₁.app _ x :=
      Prod.ext (K.δ_comp_σ_self_apply 0 x) (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)
    calc π₀.mk x = (ι₁ ≫ h).app _ x := by
          rw [h₁, toπ₀_app_zero]
      _ = h.app _ e := by
          rw [comp_app, types_comp_apply, ← e₁]
          exact NatTrans.naturality_apply h _ e
      _ = (ι₀ ≫ h).app _ x := by
          rw [comp_app, types_comp_apply, ← e₀]
          exact (NatTrans.naturality_apply h _ e).symm
      _ = z := by rw [h₀]; rfl

end IsWeaklyContractible

end SSet
