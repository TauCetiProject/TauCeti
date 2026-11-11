/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Marked.Limits
public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

import TauCeti.AlgebraicTopology.SimplicialSet.Horn

/-!
# Marked anodyne extensions

The *marked anodyne extensions* are the morphisms of marked simplicial sets with the left lifting
property with respect to every morphism which has the right lifting property with respect to the
following generators (HTT Definition 3.1.1.1):

1. the inner horn inclusions `Λ[n, i]♭ ⟶ Δ[n]♭` for `0 < i < n`;
2. the inclusions `Λ[n + 1, n + 1] ⟶ Δ[n + 1]` of the last horns, where in both the edge from
   `n` to `n + 1` is marked together with the degenerate edges;
3. the morphism `Δ[2] ⟶ Δ[2]♯` from `Δ[2]` marked at the two edges of its spine `Λ[2, 1]`, that
   is, from the pushout `Λ[2, 1]♯ ⊔ Δ[2]♭` of `Λ[2, 1]♭ ⟶ Λ[2, 1]♯` along `Λ[2, 1]♭ ⟶ Δ[2]♭`;
4. the morphisms `K♭ ⟶ K♯` for every Kan complex `K`.

Being defined by a left lifting property, they form a weakly saturated class. They are the
anodyne extensions of the marked models for Cartesian fibrations. The morphisms with the right
lifting property with respect to them are the marked fibrations. An object of the Cartesian
model structure is fibrant exactly when its morphism to the base has this lifting property, and
over a point the fibrant objects are the quasicategories marked at their equivalences (HTT
Proposition 3.1.4.1).

This file proves the properties of the class which do not use Cartesian edges or Joyal's theorem
on special outer horns. The functor `(-)♭` sends inner anodyne extensions to marked anodyne
extensions, and the functor `(-)♯` sends every morphism with the right lifting property with
respect to the horns `Λ[n, i]`, `0 < i`, for instance every Kan fibration, to a morphism with the
right lifting property with respect to marked anodyne extensions; in particular `K♯` is fibrant
for every Kan complex `K`. Conversely, if a marked simplicial set `X` is fibrant, that is
`X ⟶ 𝟙_` has the right lifting property with respect to marked anodyne extensions, then its
underlying simplicial set is a quasicategory, every marked edge is an equivalence, a composite of
two marked edges is marked, and every morphism from a Kan complex sends all edges to marked edges.
That every equivalence of `X` is marked is not proved here.

## Main definitions

* `TauCeti.MarkedSSet.markedAnodyneGenerators`: the four families of generators above.
* `TauCeti.MarkedSSet.markedAnodyneExtensions`: the marked anodyne extensions.

## Main results

* `TauCeti.MarkedSSet.markedAnodyneExtensions.flat_map`: `(-)♭` sends inner anodyne extensions to
  marked anodyne extensions.
* `TauCeti.MarkedSSet.rlp_markedAnodyneExtensions_sharp_map`: `(-)♯` sends a morphism with the
  right lifting property with respect to the horns `Λ[n, i]`, `0 < i`, to a morphism with the right
  lifting property with respect to marked anodyne extensions.
* `TauCeti.MarkedSSet.rlp_markedAnodyneExtensions_toUnit_sharp_obj`: `K♯` is fibrant for every Kan
  complex `K`.
* `TauCeti.MarkedSSet.hasLiftingProperty_iff_of_hom_eq_id`: lifting against a morphism `A ⟶ A♯`
  which is the identity on underlying simplicial sets only asks to mark edges.
* `TauCeti.MarkedSSet.quasicategory_of_rlp_markedAnodyneExtensions`,
  `TauCeti.MarkedSSet.isEquivalence_of_mem_marked`, `TauCeti.MarkedSSet.mem_marked_of_compStruct`
  and `TauCeti.MarkedSSet.map_mem_marked_of_kanComplex`: the properties of fibrant marked
  simplicial sets listed above.

## Implementation notes

That a marked edge `e` of a fibrant marked simplicial set is an equivalence follows from filling
two last horns whose last edge is `e`: `Λ[2, 2]` gives an edge `g` with `g ≫ e = id`, and then
`Λ[3, 3]` gives `e ≫ g = id`. This is the easy half of Joyal's characterization of equivalences
by special outer horns (HTT Proposition 1.2.4.3).

## References

* J. Lurie, *Higher Topos Theory*, Definition 3.1.1.1, Proposition 3.1.4.1 and
  Proposition 1.2.4.3.
-/

public section

open CategoryTheory Limits MonoidalCategory MorphismProperty Opposite Simplicial
  CartesianMonoidalCategory

universe u

namespace TauCeti

namespace MarkedSSet

section generators

/-- The standard simplex `Δ[n + 1]` marked at its last edge, from `n` to `n + 1`. -/
abbrev lastEdgeSimplex (n : ℕ) : MarkedSSet.{u} :=
  ofEdges Δ[n + 1]
    {SSet.stdSimplex.edge (n + 1) (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _)}

/-- The horn `Λ[n + 1, n + 1]` marked at the last edge of `Δ[n + 1]`. For `n = 0` this edge does
not lie in the horn, and no nondegenerate edge is marked. -/
abbrev lastEdgeHorn (n : ℕ) : MarkedSSet.{u} :=
  ofEdges Λ[n + 1, Fin.last (n + 1)]
    (Λ[n + 1, Fin.last (n + 1)].ι.app _ ⁻¹'
      {SSet.stdSimplex.edge (n + 1) (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _)})

/-- The inclusion of the marked horn `lastEdgeHorn n` into `lastEdgeSimplex n`. -/
def lastEdgeHornι (n : ℕ) : lastEdgeHorn.{u} n ⟶ lastEdgeSimplex n :=
  ofEdgesHom Λ[n + 1, Fin.last (n + 1)].ι fun _ he ↦ Or.inr he

@[simp]
lemma lastEdgeHornι_hom (n : ℕ) :
    (lastEdgeHornι.{u} n).hom = Λ[n + 1, Fin.last (n + 1)].ι :=
  ofEdgesHom_hom _ _

/-- The standard simplex `Δ[2]` marked at the two edges of its spine `Λ[2, 1]`, the faces `δ 2`
from `0` to `1` and `δ 0` from `1` to `2`. This is the pushout of `Λ[2, 1]♭ ⟶ Λ[2, 1]♯` along
`Λ[2, 1]♭ ⟶ Δ[2]♭`. -/
abbrev spineMarked : MarkedSSet.{u} :=
  ofEdges Δ[2]
    {SSet.yonedaEquiv (SSet.stdSimplex.δ 2), SSet.yonedaEquiv (SSet.stdSimplex.δ 0)}

/-- The morphism from `Δ[2]` marked along its spine to `Δ[2]♯`, the identity on underlying
simplicial sets. -/
def spineMarkedToSharp : spineMarked.{u} ⟶ sharp.obj Δ[2] :=
  toSharp (𝟙 _)

@[simp]
lemma spineMarkedToSharp_hom : spineMarkedToSharp.{u}.hom = 𝟙 Δ[2] :=
  (rfl)

/-- The generators of the marked anodyne extensions (HTT Definition 3.1.1.1). -/
inductive markedAnodyneGenerators : MorphismProperty MarkedSSet.{u} where
  | innerHorn {n : ℕ} (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    markedAnodyneGenerators (flat.map Λ[n + 2, i].ι)
  | lastEdgeHorn (n : ℕ) : markedAnodyneGenerators (lastEdgeHornι n)
  | spine : markedAnodyneGenerators spineMarkedToSharp
  | kanComplex (K : SSet.{u}) [K.KanComplex] : markedAnodyneGenerators (flatToSharp.app K)

/-- The marked anodyne extensions: the morphisms with the left lifting property with respect to
every morphism with the right lifting property with respect to `markedAnodyneGenerators`. -/
def markedAnodyneExtensions : MorphismProperty MarkedSSet.{u} :=
  markedAnodyneGenerators.rlp.llp
deriving IsMultiplicative, RespectsIso, IsStableUnderCobaseChange,
  IsStableUnderRetracts, IsStableUnderTransfiniteComposition,
  IsStableUnderCoproducts

lemma markedAnodyneExtensions_eq_llp_rlp :
    markedAnodyneExtensions.{u} = markedAnodyneGenerators.rlp.llp :=
  (rfl)

lemma markedAnodyneGenerators_le :
    markedAnodyneGenerators.{u} ≤ markedAnodyneExtensions :=
  le_llp_rlp _

/-- A morphism has the right lifting property with respect to all marked anodyne extensions
exactly when it has it with respect to the generators. -/
lemma rlp_markedAnodyneExtensions :
    markedAnodyneExtensions.{u}.rlp = markedAnodyneGenerators.rlp :=
  rlp_llp_rlp _

/-- The functor `(-)♭` sends inner anodyne extensions to marked anodyne extensions. -/
lemma markedAnodyneExtensions.flat_map {A B : SSet.{u}} {f : A ⟶ B}
    (hf : SSet.innerAnodyneExtensions f) : markedAnodyneExtensions (flat.map f) := by
  intro X Y p hp
  rw [flatForgetAdj.hasLiftingProperty_iff]
  apply hf
  rintro _ _ _ ⟨i, h0, hn⟩
  exact (flatForgetAdj.hasLiftingProperty_iff _ _).1 (hp _ (.innerHorn i h0 hn))

end generators

section lifting

variable {X Y : MarkedSSet.{u}}

/-- Lifting against a morphism `A ⟶ A♯` which is the identity on underlying simplicial sets: every
morphism `A ⟶ X` sending all edges to edges with marked image in `Y` sends all edges to marked
edges. -/
lemma hasLiftingProperty_iff_of_hom_eq_id {A : MarkedSSet.{u}} (i : A ⟶ sharp.obj A.toSSet)
    (hi : i.hom = 𝟙 _) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ ∀ a : A ⟶ X, (∀ e, p.hom.app _ (a.hom.app _ e) ∈ Y.marked) →
      ∀ e, a.hom.app _ e ∈ X.marked := by
  have hcomp {Z : MarkedSSet.{u}} (b : sharp.obj A.toSSet ⟶ Z) : (i ≫ b).hom = b.hom := by
    rw [hom_comp, hi]
    exact Category.id_comp _
  refine ⟨fun _ a ha e ↦ ?_, fun H ↦ ⟨fun {a b} sq ↦ ?_⟩⟩
  · let b : sharp.obj A.toSSet ⟶ Y := ⟨a.hom ≫ p.hom, fun e _ ↦ ha e⟩
    have sq : CommSq a i p b := ⟨by ext : 1; rw [hcomp]; exact hom_comp a p⟩
    rw [← congrArg Hom.hom sq.fac_left, hcomp]
    exact map_mem_marked _ (mem_sharp_marked e)
  · have hw : a.hom ≫ p.hom = b.hom := (congrArg Hom.hom sq.w).trans (hcomp b)
    have hb (e : A.toSSet _⦋1⦌) : p.hom.app _ (a.hom.app _ e) ∈ Y.marked := by
      rw [← NatTrans.comp_app_apply, hw]
      exact map_mem_marked b (mem_sharp_marked e)
    exact ⟨⟨{ l := ⟨a.hom, fun e _ ↦ H a hb e⟩
              fac_left := by ext : 1; exact hcomp _
              fac_right := by ext : 1; exact hw }⟩⟩

/-- The functor `(-)♯` sends a morphism with the right lifting property with respect to the horns
`Λ[n + 1, i]` with `0 < i` to a morphism with the right lifting property with respect to all marked
anodyne extensions. -/
lemma rlp_markedAnodyneExtensions_sharp_map {A B : SSet.{u}} (p : A ⟶ B)
    (hp : ∀ ⦃n : ℕ⦄ (i : Fin (n + 2)), 0 < i → HasLiftingProperty Λ[n + 1, i].ι p) :
    markedAnodyneExtensions.rlp (sharp.map p) := by
  rw [rlp_markedAnodyneExtensions]
  intro _ _ i hi
  rw [← forgetSharpAdj.hasLiftingProperty_iff]
  induction hi with
  | innerHorn i h0 _ => exact hp i h0
  | lastEdgeHorn n =>
    rw [forget_map, lastEdgeHornι_hom]
    exact hp (Fin.last (n + 1)) Fin.last_pos
  | spine =>
    have : IsIso (forget.map spineMarkedToSharp.{u}) := by
      rw [forget_map, spineMarkedToSharp_hom]
      exact IsIso.id _
    infer_instance
  | kanComplex K =>
    have : IsIso (forget.map (flatToSharp.app K)) := by
      rw [forget_map, flatToSharp_app_hom]
      exact IsIso.id _
    infer_instance

open HomotopicalAlgebra SSet.modelCategoryQuillen in
/-- The functor `(-)♯` sends Kan fibrations to morphisms with the right lifting property with
respect to marked anodyne extensions. -/
lemma rlp_markedAnodyneExtensions_sharp_map_of_fibration {A B : SSet.{u}} (p : A ⟶ B)
    [Fibration p] : markedAnodyneExtensions.rlp (sharp.map p) :=
  rlp_markedAnodyneExtensions_sharp_map p fun n i _ ↦
    (SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance _ (horn_ι_mem_J (n + 1) i)

open HomotopicalAlgebra SSet.modelCategoryQuillen in
/-- For a Kan complex `K`, the marked simplicial set `K♯` is fibrant: its morphism to the terminal
object has the right lifting property with respect to marked anodyne extensions. -/
lemma rlp_markedAnodyneExtensions_toUnit_sharp_obj (K : SSet.{u}) [K.KanComplex] :
    markedAnodyneExtensions.rlp (toUnit (sharp.obj K)) := by
  have : Fibration (toUnit K) := (isFibrant_iff_of_isTerminal _ isTerminalTensorUnit).1 ‹_›
  have : IsIso (toUnit (sharp.obj (𝟙_ SSet.{u}))) :=
    isIso_of_isTerminal (isTerminalSharpObj isTerminalTensorUnit) isTerminalTensorUnit _
  rw [← toUnit_unique (sharp.map (toUnit K) ≫ toUnit _) (toUnit (sharp.obj K))]
  exact comp_mem _ _ _ (rlp_markedAnodyneExtensions_sharp_map_of_fibration _) (of_isIso _ _)

end lifting

section fibrant

variable {X : MarkedSSet.{u}}

/-- A morphism with the right lifting property with respect to marked anodyne extensions is an
inner fibration on underlying simplicial sets. -/
lemma innerFibration_hom_of_rlp_markedAnodyneExtensions {Y : MarkedSSet.{u}} {p : X ⟶ Y}
    (hp : markedAnodyneExtensions.rlp p) : SSet.InnerFibration p.hom := by
  constructor
  rintro _ _ _ ⟨i, h0, hn⟩
  exact (flatForgetAdj.hasLiftingProperty_iff _ p).1
    (hp _ (markedAnodyneGenerators_le _ (.innerHorn i h0 hn)))

/-- The underlying simplicial set of a fibrant marked simplicial set is a quasicategory. -/
lemma quasicategory_of_rlp_markedAnodyneExtensions
    (hX : markedAnodyneExtensions.rlp (toUnit X)) : SSet.Quasicategory X.toSSet := by
  have := innerFibration_hom_of_rlp_markedAnodyneExtensions hX
  exact (SSet.quasicategory_iff_of_isTerminal (toUnit X).hom
    (isTerminalTensorUnit.isTerminalObj forget)).2 this

/-- In a fibrant marked simplicial set, a generator of the marked anodyne extensions has a lift
against every morphism out of its source. -/
private lemma exists_lift (hX : markedAnodyneExtensions.rlp (toUnit X)) {A B : MarkedSSet.{u}}
    {i : A ⟶ B} (hi : markedAnodyneGenerators i) (a : A ⟶ X) : ∃ b : B ⟶ X, i ≫ b = a := by
  have := hX _ (markedAnodyneGenerators_le _ hi)
  have sq : CommSq a i (toUnit X) (toUnit B) := ⟨toUnit_unique _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- In a fibrant marked simplicial set, every morphism from a Kan complex sends all edges to marked
edges. -/
lemma map_mem_marked_of_kanComplex (hX : markedAnodyneExtensions.rlp (toUnit X))
    {K : SSet.{u}} [K.KanComplex] (g : K ⟶ X.toSSet) (e : K _⦋1⦌) : g.app _ e ∈ X.marked := by
  have h := (hasLiftingProperty_iff_of_hom_eq_id (flatToSharp.app K) (flatToSharp_app_hom K)
    (toUnit X)).1 (hX _ (markedAnodyneGenerators_le _ (.kanComplex K))) (fromFlat g)
    (fun _ ↦ mem_tensorUnit_marked _) e
  rwa [fromFlat_hom] at h

/-- In a fibrant marked simplicial set, the composite of two marked edges is marked: in a
`2`-simplex whose edges from `0` to `1` and from `1` to `2` are marked, the edge from `0` to `2` is
marked. -/
lemma mem_marked_of_compStruct (hX : markedAnodyneExtensions.rlp (toUnit X))
    {x₀ x₁ x₂ : X.toSSet _⦋0⦌} {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂}
    {e₀₂ : SSet.Edge x₀ x₂} (h : e₀₁.CompStruct e₁₂ e₀₂) (h₀₁ : e₀₁.edge ∈ X.marked)
    (h₁₂ : e₁₂.edge ∈ X.marked) : e₀₂.edge ∈ X.marked := by
  have key := (hasLiftingProperty_iff_of_hom_eq_id spineMarkedToSharp spineMarkedToSharp_hom
    (toUnit X)).1 (hX _ (markedAnodyneGenerators_le _ .spine))
  have ha : ∀ e ∈ ({SSet.yonedaEquiv (SSet.stdSimplex.δ 2),
      SSet.yonedaEquiv (SSet.stdSimplex.δ 0)} : Set (Δ[2] _⦋1⦌)),
      (SSet.yonedaEquiv.symm h.simplex).app _ e ∈ X.marked := by
    rintro _ (rfl | rfl) <;>
      simpa [← SSet.yonedaEquiv_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  simpa [← SSet.yonedaEquiv_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm] using
    key (ofEdgesHom _ ha) (fun _ ↦ mem_tensorUnit_marked _) (SSet.yonedaEquiv (SSet.stdSimplex.δ 1))

private lemma stdSimplex_edge_last_one_eq :
    SSet.stdSimplex.edge.{u} (0 + 1) (Fin.last 0).castSucc (Fin.last (0 + 1)) (Fin.le_last _) =
      SSet.yonedaEquiv (𝟙 Δ[1]) := by
  ext i
  fin_cases i <;> rfl

private lemma stdSimplex_edge_last_two_eq :
    SSet.stdSimplex.edge.{u} (1 + 1) (Fin.last 1).castSucc (Fin.last (1 + 1)) (Fin.le_last _) =
      SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 3)) := by
  ext i
  fin_cases i <;> rfl

private lemma stdSimplex_δ_zero_app_edge (n : ℕ) :
    (SSet.stdSimplex.δ.{u} (0 : Fin (n + 3))).app _
        (SSet.stdSimplex.edge (n + 1) (Fin.last n).castSucc (Fin.last (n + 1)) (Fin.le_last _)) =
      SSet.stdSimplex.edge (n + 2) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _) := by
  ext i
  fin_cases i <;> rfl

/-- In a fibrant marked simplicial set, a compatible family of faces of the horn `Λ[n + 2, n + 2]`
whose face `0` sends the last edge of `Δ[n + 1]` to a marked edge consists of the faces of an
`(n + 2)`-simplex: the last edge of the horn is the last edge of its face `0`, so the horn
extends along the generator `lastEdgeHornι (n + 1)`. -/
private lemma exists_δ_eq_of_isCompatible (hX : markedAnodyneExtensions.rlp (toUnit X)) {n : ℕ}
    {f : ∀ j : Fin (n + 3), j ≠ Fin.last (n + 2) → (Δ[n + 1] ⟶ X.toSSet)}
    (hf : SSet.horn.IsCompatible f)
    (hf₀ : (f 0 (by simp)).app _ (SSet.stdSimplex.edge (n + 1) (Fin.last n).castSucc
      (Fin.last (n + 1)) (Fin.le_last _)) ∈ X.marked) :
    ∃ s : X.toSSet _⦋n + 2⦌, ∀ j hj, X.toSSet.δ j s = SSet.yonedaEquiv (f j hj) := by
  have hmarked : ∀ t ∈ Λ[n + 2, Fin.last (n + 2)].ι.app _ ⁻¹'
      {SSet.stdSimplex.edge (n + 2) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _)}, hf.desc.app _ t ∈ X.marked := by
    intro t ht
    rw [Set.mem_preimage, Set.mem_singleton_iff] at ht
    obtain rfl : t = (SSet.horn.ι (Fin.last (n + 2)) 0 (by simp)).app _
        (SSet.stdSimplex.edge (n + 1) (Fin.last n).castSucc (Fin.last (n + 1))
          (Fin.le_last _)) := by
      refine injective_of_mono (SSet.Subcomplex.ι.{u} _ |>.app _) (ht.trans ?_)
      rw [← NatTrans.comp_app_apply, SSet.horn.ι_ι, stdSimplex_δ_zero_app_edge]
    rwa [hf.desc_app_ι_app]
  obtain ⟨b, hb⟩ := exists_lift hX (.lastEdgeHorn (n + 1)) (ofEdgesHom hf.desc hmarked)
  obtain ⟨s, hs⟩ := SSet.yonedaEquiv.symm.surjective b.hom
  have hι : Λ[n + 2, Fin.last (n + 2)].ι ≫ SSet.yonedaEquiv.symm s = hf.desc := by
    simpa [hs] using congrArg Hom.hom hb
  exact ⟨s, fun j hj ↦ by simpa using hf.δ_yonedaEquiv_of_desc_eq hι.symm j hj⟩

/-- In a fibrant marked simplicial set, a marked edge `e : x₀ ⟶ x₁` has a right inverse up to a
`2`-simplex: filling the horn `Λ[2, 2]` with faces `e` (from `1` to `2`) and `id x₁` (from `0`
to `2`) gives an edge `g` with `g ≫ e = id x₁`. -/
private lemma exists_compStruct_id_of_mem_marked (hX : markedAnodyneExtensions.rlp (toUnit X))
    {x₀ x₁ : X.toSSet _⦋0⦌} (e : SSet.Edge x₀ x₁) (he : e.edge ∈ X.marked) :
    ∃ g : SSet.Edge x₁ x₀, Nonempty (g.CompStruct e (.id x₁)) := by
  let f : ∀ j : Fin 3, j ≠ Fin.last 2 → (Δ[1] ⟶ X.toSSet) := fun j _ ↦
    ![SSet.yonedaEquiv.symm e.edge, SSet.yonedaEquiv.symm (SSet.Edge.id x₁).edge,
      SSet.yonedaEquiv.symm e.edge] j
  have hf : SSet.horn.IsCompatible f := by
    rw [SSet.horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢
    simp [f, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, -SSet.Edge.id_edge]
  obtain ⟨s, hs⟩ := exists_δ_eq_of_isCompatible hX hf (by
    rw [stdSimplex_edge_last_one_eq]
    simpa [f] using he)
  have hs₀ : X.toSSet.δ 0 s = e.edge := by simpa [f] using hs 0 (by decide)
  have hs₁ : X.toSSet.δ 1 s = (SSet.Edge.id x₁).edge := by
    simpa [f, -SSet.Edge.id_edge] using hs 1 (by decide)
  exact ⟨.mk (X.toSSet.δ 2 s)
    ((SSet.δ_comp_δ_apply (i := 1) (j := 1) le_rfl s).trans (by simp [hs₁, -SSet.Edge.id_edge]))
    ((SSet.δ_comp_δ_apply (i := 0) (j := 1) (by decide) s).trans (by simp [hs₀])),
    ⟨.mk s rfl hs₀ hs₁⟩⟩

/-- In a fibrant marked simplicial set, a right inverse `g` of a marked edge `e : x₀ ⟶ x₁` is also
a left inverse: filling the horn `Λ[3, 3]` with faces given by `g ≫ e = id x₁` (on `1, 2, 3`),
`id x₀ ≫ e = e` (on `0, 2, 3`) and `e ≫ id x₁ = e` (on `0, 1, 3`), the remaining face exhibits
`e ≫ g = id x₀`. -/
private lemma nonempty_compStruct_id_of_mem_marked (hX : markedAnodyneExtensions.rlp (toUnit X))
    {x₀ x₁ : X.toSSet _⦋0⦌} {e : SSet.Edge x₀ x₁} (he : e.edge ∈ X.marked)
    {g : SSet.Edge x₁ x₀} (c : g.CompStruct e (.id x₁)) :
    Nonempty (e.CompStruct g (.id x₀)) := by
  let f : ∀ j : Fin 4, j ≠ Fin.last 3 → (Δ[2] ⟶ X.toSSet) := fun j _ ↦
    ![SSet.yonedaEquiv.symm c.simplex,
      SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp e).simplex,
      SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId e).simplex,
      SSet.yonedaEquiv.symm c.simplex] j
  have hf : SSet.horn.IsCompatible f := by
    rw [SSet.horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢ <;>
      simp [f, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, -SSet.Edge.id_edge,
        -SSet.Edge.CompStruct.idComp_simplex, -SSet.Edge.CompStruct.compId_simplex]
  obtain ⟨w, hw⟩ := exists_δ_eq_of_isCompatible hX hf (by
    rw [stdSimplex_edge_last_two_eq, ← SSet.yonedaEquiv_comp]
    simpa [f, SSet.stdSimplex.δ_comp_yonedaEquiv_symm] using he)
  exact ⟨.mk (X.toSSet.δ 3 w)
    ((SSet.δ_comp_δ_apply (i := 2) (j := 2) le_rfl w).trans (by
      simpa [f, -SSet.Edge.CompStruct.compId_simplex] using
        congrArg (X.toSSet.δ 2) (hw 2 (by decide))))
    ((SSet.δ_comp_δ_apply (i := 0) (j := 2) (by decide) w).trans (by
      simpa [f] using congrArg (X.toSSet.δ 2) (hw 0 (by decide))))
    ((SSet.δ_comp_δ_apply (i := 1) (j := 2) (by decide) w).trans (by
      simpa [f, -SSet.Edge.CompStruct.idComp_simplex, -SSet.Edge.id_edge] using
        congrArg (X.toSSet.δ 2) (hw 1 (by decide))))⟩

/-- In a fibrant marked simplicial set, every marked edge is an equivalence. -/
lemma isEquivalence_of_mem_marked (hX : markedAnodyneExtensions.rlp (toUnit X))
    {x₀ x₁ : X.toSSet _⦋0⦌} (e : SSet.Edge x₀ x₁) (he : e.edge ∈ X.marked) :
    e.IsEquivalence := by
  obtain ⟨g, ⟨c₁⟩⟩ := exists_compStruct_id_of_mem_marked hX e he
  obtain ⟨c₂⟩ := nonempty_compStruct_id_of_mem_marked hX he c₁
  exact SSet.Edge.InvStruct.isEquivalence { inv := g, homInvId := c₂, invHomId := c₁ }

end fibrant

end MarkedSSet

end TauCeti
