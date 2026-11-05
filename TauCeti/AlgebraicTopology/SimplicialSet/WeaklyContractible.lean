/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Groupoid
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.SingleObj
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex
public import TauCeti.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Weakly contractible simplicial sets

A simplicial set `K` is *weakly contractible* (`SSet.IsWeaklyContractible`) when, for every Kan
complex `Z`, the inclusion `SSet.constMaps K Z : Z ⟶ Fun(K, Z)` of the constant maps into the
internal hom is a simplicial homotopy equivalence. It appears in Joyal's Theorem A (HTT Theorem
4.1.3.1, Kerodon Theorem 7.2.3.1): a map `K ⟶ L` to a quasicategory is right cofinal exactly when
its fibre products with the coslices of `L` are weakly contractible.

A simplicial set with a homotopy from a constant map to its identity, such as a standard simplex
(`SSet.stdSimplex.contraction`), is weakly contractible: evaluation at the vertex is a homotopy
inverse. Conversely, a weakly contractible simplicial set is nonempty, since `Fun(K, Z)` has a
vertex when `K` is empty, while the empty simplicial set is a Kan complex without vertices. Every
map from it to a Kan complex is homotopic to a constant map, and testing this against its map to
the discrete simplicial set on its connected components shows that it is connected.

Connectedness does not suffice: the boundary `∂Δ[2]` is connected, but the map from it to the
nerve of the group `ℤ`, viewed as a category with one object, which sends the edges `0 → 1` and
`1 → 2` to `0` and the edge `0 → 2` to `1` is not homotopic to a constant map. Indeed, a homotopy
from a constant map to a map `φ` into the nerve of a group assigns to each vertex `k` an element
`w k` with `w b = φ (a → b) * w a` for every edge, forcing `φ (0 → 2) = φ (1 → 2) * φ (0 → 1)`.

The comparison with the weak equivalences of
`TauCeti/AlgebraicTopology/SimplicialSet/WeakEquivalence.lean`, namely that `K` is weakly
contractible exactly when `K ⟶ Δ[0]` is a weak homotopy equivalence, needs the homotopy theory
of the Kan–Quillen model structure and is not proved here.

## Main declarations

* `SSet.constMaps K Z`: the constant maps `Z ⟶ Fun(K, Z)`, and `SSet.evalAt x Z`, evaluation at a
  vertex `x`, which is a retraction of it (`SSet.constMaps_evalAt`); `SSet.curry_evalAt`
  evaluates curried maps.
* `SSet.IsWeaklyContractible`: weakly contractible simplicial sets.
* `SSet.IsWeaklyContractible.of_homotopy`: contractible simplicial sets are weakly contractible;
  in particular every standard simplex `Δ[n]` is.
* `SSet.IsWeaklyContractible.of_iso`: invariance under isomorphism.
* `SSet.IsWeaklyContractible.nonempty`: the empty simplicial set is not weakly contractible.
* `SSet.IsWeaklyContractible.exists_homotopy_const`: maps to Kan complexes are homotopic to
  constant maps.
* `SSet.IsWeaklyContractible.isConnected`: weakly contractible simplicial sets are connected.
* `SSet.isWeaklyContractible_const_iff`: the discrete simplicial set on `ι` is weakly
  contractible exactly when `ι` has a unique element.
* `SSet.not_isWeaklyContractible_boundary_two`: the connected simplicial set `∂Δ[2]` is not
  weakly contractible.

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

variable {K} in
/-- Evaluating a curried map at a vertex `x` of `K` restricts it to `x` on the first factor. -/
@[reassoc (attr := simp)]
lemma curry_evalAt {Y Z : SSet.{u}} (x : K _⦋0⦌) (f : K ⊗ Y ⟶ Z) :
    curry f ≫ evalAt x Z = lift (const x) (𝟙 Y) ≫ f := by
  simpa [evalAt, comp_lift_assoc] using lift_curry_ihom_ev_app (const x) (𝟙 Y) f

/-- Evaluating a constant map at a vertex returns its value. -/
@[reassoc (attr := simp)]
lemma constMaps_evalAt (x : K _⦋0⦌) (Z : SSet.{u}) : constMaps K Z ≫ evalAt x Z = 𝟙 Z := by
  simp [constMaps]

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

/-- Over a vertex `i` of `Δ[1]`, `contractingMap h Z` precomposes with the restriction of `h`
to `i`. -/
private lemma lift_const_contractingMap (i : Δ[1] _⦋0⦌) :
    lift (𝟙 _) (const i) ≫ contractingMap h Z =
      curry (lift (fst _ _ ≫ lift (𝟙 K) (const i) ≫ h) (snd _ _) ≫ (ihom.ev K).app Z) := by
  have hi : K ◁ lift (𝟙 ((ihom K).obj Z)) (const i) ≫ lift (fst _ _) (snd _ _ ≫ snd _ _) =
      fst _ _ ≫ lift (𝟙 K) (const i) := by
    ext : 1 <;> simp
  rw [contractingMap, ← curry_natural_left]
  simp [comp_lift_assoc, reassoc_of% hi]

private lemma ι₀_contractingMap {x : K _⦋0⦌} (h₀ : ι₀ ≫ h = const x) :
    ι₀ ≫ contractingMap h Z = evalAt x Z ≫ constMaps K Z := by
  rw [ι₀, lift_const_contractingMap, ← ι₀, h₀, evalAt_constMaps, evalAt, comp_lift_assoc]
  simp

private lemma ι₁_contractingMap (h₁ : ι₁ ≫ h = 𝟙 K) : ι₁ ≫ contractingMap h Z = 𝟙 _ := by
  rw [ι₁, lift_const_contractingMap, ← ι₁, h₁]
  simp [← uncurry_id_eq_ev]

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
  have he₀ : const (X := K) (stdSimplex.obj₀Equiv.symm 0) ≫ e =
      const ((φ ≫ g).app _ v) ≫ constMaps K Z := by
    rw [← const_comp, Category.assoc, Category.assoc, ← h₀, ← ι₀_comp_assoc]
    simp only [e, ← Category.assoc]
    congr 2
  have he₁ : const (X := K) (stdSimplex.obj₀Equiv.symm 1) ≫ e = const v ≫ φ := by
    rw [← Category.comp_id φ, ← h₁, ← ι₁_comp_assoc]
    simp only [e, ← Category.assoc]
    congr 2
  -- Through `uncurry`, the edge `e` is a homotopy `K ⊗ Δ[1] ⟶ Z`, whose ends are the values of
  -- `e` at the vertices of `Δ[1]`, both curried.
  refine ⟨(φ ≫ g).app _ v, ⟨{ h := uncurry e, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩⟩
  · -- `change` unfolds `RelativeMorphism.botEquiv.symm` in the types of the fields.
    change ι₀ ≫ uncurry e = const _
    rw [ι₀, uncurry_eq, lift_whiskerLeft_assoc, he₀, constMaps, lift_curry_ihom_ev_app, lift_snd]
  · change ι₁ ≫ uncurry e = f
    rw [ι₁, uncurry_eq, lift_whiskerLeft_assoc, he₁, lift_curry_ihom_ev_app, lift_fst_assoc,
      Category.id_comp]
  · ext _ ⟨⟨_, ⟨⟩⟩, _⟩

/-- A weakly contractible simplicial set is connected. -/
instance isConnected : K.IsConnected where
  nonempty := nonempty
  allEq := π₀.rec fun x ↦ π₀.rec fun y ↦ by
    obtain ⟨z, ⟨H⟩⟩ := exists_homotopy_const (toπ₀ K)
    -- The homotopy induces equal maps on connected components, and the connected components of
    -- the discrete target are its vertices.
    suffices key : ∀ x : K _⦋0⦌, π₀.mk x = z from (key x).trans (key y).symm
    intro x
    have := congrArg (constπ₀Equiv _) (congrFun H.mapπ₀_eq (π₀.mk x))
    simpa [mapπ₀_mk, toπ₀_app_zero] using this.symm

end IsWeaklyContractible

/-- The discrete simplicial set on a type `ι` is weakly contractible exactly when `ι` has a unique
element: its connected components are the elements of `ι`. -/
theorem isWeaklyContractible_const_iff (ι : Type u) :
    IsWeaklyContractible ((Functor.const SimplexCategoryᵒᵖ).obj ι) ↔ Nonempty (Unique ι) := by
  rw [unique_iff_subsingleton_and_nonempty]
  refine ⟨fun _ ↦ ⟨(constπ₀Equiv ι).symm.injective.subsingleton,
    IsWeaklyContractible.nonempty (K := (Functor.const SimplexCategoryᵒᵖ).obj ι)⟩,
    fun ⟨_, ⟨i⟩⟩ ↦ IsWeaklyContractible.of_homotopy (x := i) (.ofEq ?_)⟩
  -- Every simplicial set map to a discrete simplicial set on a subsingleton is the identity.
  ext n s
  exact Subsingleton.elim (α := ι) _ _

section Boundary

/-! ### The boundary of the `2`-simplex is not weakly contractible -/

variable {G : Type u} [Group G]

/-- The element of `G` assigned to the edge from `a` to `b` of `∂Δ[2]` by the map `boundaryLoop g`:
`g` on the edge from `0` to `2`, and `1` on all other edges. -/
private def loopCocycle (g : G) (a b : Fin 3) : G := if a = 0 ∧ b = 2 then g else 1

private lemma loopCocycle_comp (g : G) {a b c : Fin 3} (hab : a ≤ b) (hbc : b ≤ c)
    (h : ¬ (a = 0 ∧ b = 1 ∧ c = 2)) :
    loopCocycle g a c = loopCocycle g b c * loopCocycle g a b := by
  unfold loopCocycle
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

/-- The map from `∂Δ[2]` to the nerve of `G`, viewed as a category with one object, sending the
edge from `0` to `2` to `g` and the other edges to `1`. A simplex of `∂Δ[2]` misses a vertex, so
it never contains all three edges at once. -/
private noncomputable def boundaryLoop (g : G) : (∂Δ[2] : SSet.{u}) ⟶ nerve (SingleObj G) where
  app n := ↾fun s ↦
    { obj _ := SingleObj.star G
      map {a b} _ := loopCocycle g (stdSimplex.asOrderHom s.1 a) (stdSimplex.asOrderHom s.1 b)
      map_id a := by
        rw [SingleObj.id_as_one, loopCocycle, ite_eq_right_iff]
        rintro ⟨h₀, h₂⟩
        exact absurd (h₀.symm.trans h₂) (by decide)
      map_comp {a b c} hab hbc := by
        rw [SingleObj.comp_as_mul]
        refine loopCocycle_comp g ((stdSimplex.asOrderHom s.1).monotone (leOfHom hab))
          ((stdSimplex.asOrderHom s.1).monotone (leOfHom hbc)) ?_
        rintro ⟨ha, hb, hc⟩
        apply s.2
        intro k
        fin_cases k
        exacts [⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩] }
  -- The value on a simplex only depends on its vertices, so it commutes with reindexing.
  naturality n m θ := by
    ext s
    exact CategoryTheory.Functor.ext (fun _ ↦ rfl)
      (fun _ _ _ ↦ by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)

/-- The boundary `∂Δ[2]` is connected (`SSet.boundary.isConnected`) but not weakly contractible:
its map to the nerve of `ℤ` sending the edge from `0` to `2` to `1` and the other edges to `0` is
not homotopic to a constant map. -/
theorem not_isWeaklyContractible_boundary_two : ¬ IsWeaklyContractible (∂Δ[2] : SSet.{u}) := by
  intro hK
  let g : Multiplicative (ULift.{u} ℤ) := Multiplicative.ofAdd (ULift.up 1)
  obtain ⟨z, ⟨H⟩⟩ := hK.exists_homotopy_const (boundaryLoop g)
  -- The edge of `∂Δ[2]` from `a` to `b`.
  let e (a b : Fin 3) (hab : a ≤ b) : (∂Δ[2] : SSet.{u}) _⦋1⦌ :=
    ⟨stdSimplex.edge 2 a b hab, by simp [boundary_obj_eq_univ]⟩
  -- Over each edge, the vertical edges of `H` differ by the value of `boundaryLoop g`, since the
  -- edges of the constant map represent `1`.
  have h₀₁ := nerve.edgeElem_homotopy H (e 0 1 (by decide))
  have h₁₂ := nerve.edgeElem_homotopy H (e 1 2 (by decide))
  have h₀₂ := nerve.edgeElem_homotopy H (e 0 2 (by decide))
  simp only [nerve.edgeElem_const_app, mul_one] at h₀₁ h₁₂ h₀₂
  -- The three edges share their endpoints, and the values of `boundaryLoop g` on them are `1`,
  -- `1` and `g`, by evaluating `loopCocycle` on their vertices.
  have v₀ : (∂Δ[2] : SSet.{u}).δ 1 (e 0 1 (by decide)) =
      (∂Δ[2] : SSet.{u}).δ 1 (e 0 2 (by decide)) := by decide
  have v₁ : (∂Δ[2] : SSet.{u}).δ 0 (e 0 1 (by decide)) =
      (∂Δ[2] : SSet.{u}).δ 1 (e 1 2 (by decide)) := by decide
  have v₂ : (∂Δ[2] : SSet.{u}).δ 0 (e 1 2 (by decide)) =
      (∂Δ[2] : SSet.{u}).δ 0 (e 0 2 (by decide)) := by decide
  have c₀₁ : nerve.edgeElem ((boundaryLoop g).app _ (e 0 1 (by decide))) = 1 := rfl
  have c₁₂ : nerve.edgeElem ((boundaryLoop g).app _ (e 1 2 (by decide))) = 1 := rfl
  have c₀₂ : nerve.edgeElem ((boundaryLoop g).app _ (e 0 2 (by decide))) = g := rfl
  rw [v₀, v₁, c₀₁, one_mul] at h₀₁
  rw [v₂, c₁₂, one_mul] at h₁₂
  rw [c₀₂, h₁₂, h₀₁] at h₀₂
  exact absurd (mul_eq_right.1 h₀₂.symm) (by decide)

end Boundary

end SSet
