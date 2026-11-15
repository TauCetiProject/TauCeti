/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Topology.Category.TopPair.Quotient
import Mathlib.Topology.CompactOpen
import TauCeti.Topology.Category.TopPair

/-!
# The pointed smash product of topological spaces

For pointed topological spaces `(X, x₀)` and `(Y, y₀)`, the smash product `X ∧ Y` collapses the
axes `X × {y₀} ∪ {x₀} × Y` inside `X × Y` to a single basepoint. Here `TauCeti.SmashProduct x₀ y₀`
is constructed as the pointed pair quotient `TopPair.ordinaryPairQuotient` of `TauCeti.smashPair`,
so relative homology and cohomology comparisons for pair quotients apply directly to it.

Because `(x₀, y₀)` belongs to the collapsed subspace, the quotient map
`TauCeti.SmashProduct.mk x₀ y₀ : C(X × Y, SmashProduct x₀ y₀)` is unconditionally a surjective
quotient map (`TauCeti.SmashProduct.isQuotientMap_mk`), with no nonemptiness or separation
hypotheses on `X` or `Y`. Continuous maps out of `SmashProduct x₀ y₀` into any space `Z` are
therefore continuous maps out of `X × Y` taking a common value on `X × {y₀}` and `{x₀} × Y`
(`TauCeti.SmashProduct.lift`).

For pairs `(X, A)` and `(Y, B)`, when `X` and `Y / B` are locally compact (in particular when `X`
and `Y` are compact Hausdorff and `B` is closed), the pointed quotient of the product pair
`(X × Y, A × Y ∪ X × B)` is homeomorphic to `(X / A) ∧ (Y / B)`
(`TopPair.ordinaryPairQuotientProdHomeomorph`), including when `A` or `B` is empty. Likewise, when
`X` and `Z` are locally compact, the smash product `(X ∧ Y) ∧ Z ≃ₜ X ∧ (Y ∧ Z)` is associative
(`TauCeti.SmashProduct.assoc`).

## Main declarations

* `TauCeti.smashPair` and `TauCeti.SmashProduct`: the pair `(X × Y, X × {y₀} ∪ {x₀} × Y)` and its
  pointed quotient `X ∧ Y`.
* `TauCeti.SmashProduct.basepoint` and `TauCeti.SmashProduct.mk`: the basepoint and quotient map
  `C(X × Y, SmashProduct x₀ y₀)`, with `TauCeti.SmashProduct.isQuotientMap_mk`,
  `TauCeti.SmashProduct.mk_eq_basepoint_iff`, and `TauCeti.SmashProduct.mk_eq_mk_iff`.
* `TauCeti.SmashProduct.lift` and `TauCeti.SmashProduct.hom_ext`: the universal mapping property.
* `TauCeti.SmashProduct.map`, `TauCeti.SmashProduct.congrHomeomorph`, `TauCeti.SmashProduct.comm`,
  and `TauCeti.SmashProduct.assoc`: functoriality, symmetry, and associativity.
* `TopPair.ordinaryPairQuotientProdHomeomorph`: `(X × Y) / (A × Y ∪ X × B) ≃ₜ (X / A) ∧ (Y / B)`
  for locally compact `X` and `Y / B`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0,
  the smash product in "Operations on spaces".
* J. P. May, *A Concise Course in Algebraic Topology*, Section 8.1, quotient maps and associativity
  of the smash product on locally compact spaces.
-/

public section

noncomputable section

open CategoryTheory Set Topology

universe u v

namespace TauCeti

section SmashPair

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The topological pair `(X × Y, X × {y₀} ∪ {x₀} × Y)` whose pointed quotient is the smash product
of `(X, x₀)` and `(Y, y₀)`. -/
abbrev smashPair (x₀ : X) (y₀ : Y) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (X × Y)) (univ ×ˢ {y₀} ∪ {x₀} ×ˢ univ)

/-- A pair `(x, y)` lies in the subspace of `TauCeti.smashPair x₀ y₀` exactly when `x = x₀` or
`y = y₀`. -/
lemma mem_range_smashPair_map_iff {x₀ : X} {y₀ : Y} {p : X × Y} :
    (p : (smashPair x₀ y₀).fst) ∈ range (smashPair x₀ y₀).map ↔ p.1 = x₀ ∨ p.2 = y₀ := by
  rw [TopPair.range_ofSubset_map]
  exact ⟨fun h ↦ h.elim (fun h ↦ Or.inr h.2) fun h ↦ Or.inl h.1,
    fun h ↦ h.elim (fun h ↦ Or.inr ⟨h, trivial⟩) fun h ↦ Or.inl ⟨trivial, h⟩⟩

instance instNonemptySmashPairSnd (x₀ : X) (y₀ : Y) : Nonempty (smashPair x₀ y₀).snd :=
  ⟨⟨(x₀, y₀), Or.inl ⟨trivial, rfl⟩⟩⟩

/-- **The pointed smash product `X ∧ Y`** of `(X, x₀)` and `(Y, y₀)`: the pointed quotient
`TopPair.ordinaryPairQuotient` of `TauCeti.smashPair x₀ y₀`. -/
def SmashProduct (x₀ : X) (y₀ : Y) : TopCat.{u} :=
  (smashPair x₀ y₀).ordinaryPairQuotient

lemma smashPair_ordinaryPairQuotient (x₀ : X) (y₀ : Y) :
    (smashPair x₀ y₀).ordinaryPairQuotient = SmashProduct x₀ y₀ := (rfl)

end SmashPair

namespace SmashProduct

section Basic

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y)

/-- The basepoint of `X ∧ Y`, the collapsed image of `X × {y₀} ∪ {x₀} × Y`. -/
def basepoint : SmashProduct x₀ y₀ :=
  (smashPair x₀ y₀).ordinaryPairQuotientBasepoint

instance : Inhabited (SmashProduct x₀ y₀) :=
  ⟨basepoint x₀ y₀⟩

/-- The quotient map `X × Y → X ∧ Y` sending `(x, y)` to `x ∧ y`. -/
def mk : C(X × Y, SmashProduct x₀ y₀) :=
  ((smashPair x₀ y₀).ordinaryPairQuotientπ).hom

variable {x₀ y₀}

/-- A pair `(x, y)` maps to the basepoint of `X ∧ Y` exactly when `x = x₀` or `y = y₀`. -/
@[simp]
lemma mk_eq_basepoint_iff {x : X} {y : Y} :
    mk x₀ y₀ (x, y) = basepoint x₀ y₀ ↔ x = x₀ ∨ y = y₀ :=
  ((smashPair x₀ y₀).ordinaryPairQuotientπ_eq_basepoint_iff (x, y)).trans
    (mem_range_smashPair_map_iff (p := (x, y)))

@[simp]
lemma mk_basepoint_left (y : Y) : mk x₀ y₀ (x₀, y) = basepoint x₀ y₀ :=
  mk_eq_basepoint_iff.2 (Or.inl rfl)

@[simp]
lemma mk_basepoint_right (x : X) : mk x₀ y₀ (x, y₀) = basepoint x₀ y₀ :=
  mk_eq_basepoint_iff.2 (Or.inr rfl)

/-- Two pairs represent the same point of `X ∧ Y` exactly when they are equal or each has at least
one basepoint coordinate. -/
lemma mk_eq_mk_iff {x x' : X} {y y' : Y} :
    mk x₀ y₀ (x, y) = mk x₀ y₀ (x', y') ↔
      (x = x' ∧ y = y') ∨ (x = x₀ ∨ y = y₀) ∧ (x' = x₀ ∨ y' = y₀) := by
  refine ((smashPair x₀ y₀).ordinaryPairQuotientπ_eq_iff (x, y) (x', y')).trans ?_
  refine or_congr ⟨fun h ↦ Prod.mk.inj h, fun ⟨h₁, h₂⟩ ↦ Prod.ext h₁ h₂⟩ ?_
  exact and_congr (mem_range_smashPair_map_iff (p := (x, y)))
    (mem_range_smashPair_map_iff (p := (x', y')))

variable (x₀ y₀) in
/-- The projection `X × Y → X ∧ Y` is unconditionally surjective, as `(x₀, y₀)` maps to the
basepoint. -/
lemma surjective_mk : Function.Surjective (mk x₀ y₀) :=
  (smashPair x₀ y₀).surjective_ordinaryPairQuotientπ

variable (x₀ y₀) in
/-- **The projection `X × Y → X ∧ Y` is unconditionally a quotient map.** -/
lemma isQuotientMap_mk : IsQuotientMap (mk x₀ y₀) :=
  (smashPair x₀ y₀).isQuotientMap_ordinaryPairQuotientπ

/-- Induction principle for `X ∧ Y`: every point is of the form `mk x₀ y₀ (x, y)`. -/
@[elab_as_elim]
lemma ind {motive : SmashProduct x₀ y₀ → Prop}
    (hmk : ∀ x y, motive (mk x₀ y₀ (x, y))) (z : SmashProduct x₀ y₀) : motive z := by
  obtain ⟨⟨x, y⟩, rfl⟩ := surjective_mk x₀ y₀ z
  exact hmk x y

lemma isOpen_iff {s : Set (SmashProduct x₀ y₀)} :
    IsOpen s ↔ IsOpen (mk x₀ y₀ ⁻¹' s) :=
  (smashPair x₀ y₀).isOpen_ordinaryPairQuotient_iff

lemma isClosed_iff {s : Set (SmashProduct x₀ y₀)} :
    IsClosed s ↔ IsClosed (mk x₀ y₀ ⁻¹' s) :=
  (smashPair x₀ y₀).isClosed_ordinaryPairQuotient_iff

/-- **Extensionality for continuous maps out of `X ∧ Y`.** -/
@[ext]
lemma hom_ext {Z : Type v} [TopologicalSpace Z] {f g : C(SmashProduct x₀ y₀, Z)}
    (h : ∀ x y, f (mk x₀ y₀ (x, y)) = g (mk x₀ y₀ (x, y))) : f = g := by
  ext z
  induction z using ind with
  | hmk x y => exact h x y

private lemma factorsThrough_mk {Z : Type v} {f : X × Y → Z} (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) :
    Function.FactorsThrough f (mk x₀ y₀) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  rcases mk_eq_mk_iff.1 h with ⟨rfl, rfl⟩ | ⟨h₁, h₂⟩
  · rfl
  · have eq₁ : f (x₁, y₁) = z₀ := h₁.elim (fun hx ↦ hx ▸ hx₀ y₁) fun hy ↦ hy ▸ hy₀ x₁
    have eq₂ : f (x₂, y₂) = z₀ := h₂.elim (fun hx ↦ hx ▸ hx₀ y₂) fun hy ↦ hy ▸ hy₀ x₂
    exact eq₁.trans eq₂.symm

/-- **The universal property of the smash product.** A continuous map `f : C(X × Y, Z)` taking a
constant value `z₀` along `{x₀} × Y` and `X × {y₀}` descends to `C(SmashProduct x₀ y₀, Z)`. -/
def lift {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) :
    C(SmashProduct x₀ y₀, Z) :=
  (isQuotientMap_mk x₀ y₀).lift f (factorsThrough_mk z₀ hx₀ hy₀)

@[simp]
lemma lift_mk {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) (x : X) (y : Y) :
    lift f z₀ hx₀ hy₀ (mk x₀ y₀ (x, y)) = f (x, y) :=
  DFunLike.congr_fun ((isQuotientMap_mk x₀ y₀).lift_comp f (factorsThrough_mk z₀ hx₀ hy₀)) (x, y)

@[simp]
lemma lift_comp_mk {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) :
    (lift f z₀ hx₀ hy₀).comp (mk x₀ y₀) = f := by
  ext ⟨x, y⟩
  exact lift_mk f z₀ hx₀ hy₀ x y

@[simp]
lemma lift_basepoint {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) :
    lift f z₀ hx₀ hy₀ (basepoint x₀ y₀) = z₀ := by
  rw [← mk_basepoint_left (x₀ := x₀) y₀, lift_mk, hx₀]

/-! ### Topological properties -/

instance [CompactSpace X] [CompactSpace Y] : CompactSpace (SmashProduct x₀ y₀) :=
  haveI : CompactSpace (smashPair x₀ y₀).fst := inferInstanceAs (CompactSpace (X × Y))
  (smashPair x₀ y₀).compactSpace_ordinaryPairQuotient

instance [T3Space X] [T3Space Y] : T2Space (SmashProduct x₀ y₀) := by
  have : T3Space (smashPair x₀ y₀).fst := inferInstanceAs (T3Space (X × Y))
  refine (smashPair x₀ y₀).t2Space_ordinaryPairQuotient_of_isClosed ?_
  rw [TopPair.range_ofSubset_map]
  exact (isClosed_univ.prod isClosed_singleton).union (isClosed_singleton.prod isClosed_univ)

instance subsingleton_left [Subsingleton X] : Subsingleton (SmashProduct x₀ y₀) := by
  refine ⟨fun z₁ z₂ ↦ ?_⟩
  have hbase (z : SmashProduct x₀ y₀) : z = basepoint x₀ y₀ := by
    induction z using ind with
    | hmk x y => rw [Subsingleton.elim x x₀, mk_basepoint_left]
  exact (hbase z₁).trans (hbase z₂).symm

instance subsingleton_right [Subsingleton Y] : Subsingleton (SmashProduct x₀ y₀) := by
  refine ⟨fun z₁ z₂ ↦ ?_⟩
  have hbase (z : SmashProduct x₀ y₀) : z = basepoint x₀ y₀ := by
    induction z using ind with
    | hmk x y => rw [Subsingleton.elim y y₀, mk_basepoint_right]
  exact (hbase z₁).trans (hbase z₂).symm

instance [PathConnectedSpace X] [PathConnectedSpace Y] :
    PathConnectedSpace (SmashProduct x₀ y₀) :=
  (isQuotientMap_mk x₀ y₀).surjective.pathConnectedSpace (mk x₀ y₀).continuous

end Basic

/-! ### Functoriality, symmetry, and associativity -/

section Functoriality

variable {X Y X' Y' X'' Y'' : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  [TopologicalSpace X''] [TopologicalSpace Y'']
  {x₀ : X} {y₀ : Y} {x₀' : X'} {y₀' : Y'} {x₀'' : X''} {y₀'' : Y''}

/-- The pointed map `X ∧ Y → X' ∧ Y'` induced by pointed continuous maps `f : (X, x₀) → (X', x₀')`
and `g : (Y, y₀) → (Y', y₀')`. -/
def map (f : C(X, X')) (g : C(Y, Y')) (hf : f x₀ = x₀') (hg : g y₀ = y₀') :
    C(SmashProduct x₀ y₀, SmashProduct x₀' y₀') :=
  lift ((mk x₀' y₀').comp (f.prodMap g)) (basepoint x₀' y₀')
    (fun y ↦ by simp [hf]) (fun x ↦ by simp [hg])

@[simp]
lemma map_mk (f : C(X, X')) (g : C(Y, Y')) (hf : f x₀ = x₀') (hg : g y₀ = y₀') (x : X) (y : Y) :
    map f g hf hg (mk x₀ y₀ (x, y)) = mk x₀' y₀' (f x, g y) :=
  lift_mk _ _ _ _ x y

@[simp]
lemma map_basepoint (f : C(X, X')) (g : C(Y, Y')) (hf : f x₀ = x₀') (hg : g y₀ = y₀') :
    map f g hf hg (basepoint x₀ y₀) = basepoint x₀' y₀' :=
  lift_basepoint _ _ _ _

@[simp]
lemma map_id (x₀ : X) (y₀ : Y) :
    map (x₀ := x₀) (y₀ := y₀) (x₀' := x₀) (y₀' := y₀)
      (ContinuousMap.id X) (ContinuousMap.id Y) rfl rfl =
      ContinuousMap.id (SmashProduct x₀ y₀) := by
  apply hom_ext
  intro x y
  exact map_mk _ _ _ _ x y

lemma map_comp (f : C(X, X')) (g : C(Y, Y')) (hf : f x₀ = x₀') (hg : g y₀ = y₀')
    (f' : C(X', X'')) (g' : C(Y', Y'')) (hf' : f' x₀' = x₀'') (hg' : g' y₀' = y₀'') :
    (map f' g' hf' hg').comp (map f g hf hg) =
      map (f'.comp f) (g'.comp g) (by simp [hf, hf']) (by simp [hg, hg']) := by
  apply hom_ext
  intro x y
  simp

/-- Pointed homeomorphisms `X ≃ₜ X'` and `Y ≃ₜ Y'` induce a homeomorphism `X ∧ Y ≃ₜ X' ∧ Y'`. -/
def congrHomeomorph (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀') (he₂ : e₂ y₀ = y₀') :
    SmashProduct x₀ y₀ ≃ₜ SmashProduct x₀' y₀' where
  toFun := map (e₁ : C(X, X')) (e₂ : C(Y, Y')) he₁ he₂
  invFun := map (e₁.symm : C(X', X)) (e₂.symm : C(Y', Y)) (e₁.symm_apply_eq.2 he₁.symm)
    (e₂.symm_apply_eq.2 he₂.symm)
  left_inv z := by
    induction z using ind with
    | hmk x y => simp
  right_inv z' := by
    induction z' using ind with
    | hmk x' y' => simp
  continuous_toFun := (map (e₁ : C(X, X')) (e₂ : C(Y, Y')) he₁ he₂).continuous
  continuous_invFun := (map (e₁.symm : C(X', X)) (e₂.symm : C(Y', Y))
    (e₁.symm_apply_eq.2 he₁.symm) (e₂.symm_apply_eq.2 he₂.symm)).continuous

@[simp]
lemma congrHomeomorph_mk (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀') (he₂ : e₂ y₀ = y₀')
    (x : X) (y : Y) :
    congrHomeomorph e₁ e₂ he₁ he₂ (mk x₀ y₀ (x, y)) = mk x₀' y₀' (e₁ x, e₂ y) := by
  simp [congrHomeomorph]

@[simp]
lemma congrHomeomorph_basepoint (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀')
    (he₂ : e₂ y₀ = y₀') :
    congrHomeomorph e₁ e₂ he₁ he₂ (basepoint x₀ y₀) = basepoint x₀' y₀' := by
  simp [congrHomeomorph]

@[simp]
lemma congrHomeomorph_symm (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀')
    (he₂ : e₂ y₀ = y₀') :
    (congrHomeomorph e₁ e₂ he₁ he₂).symm =
      congrHomeomorph e₁.symm e₂.symm (e₁.symm_apply_eq.2 he₁.symm)
        (e₂.symm_apply_eq.2 he₂.symm) := (rfl)

private def commMap (x₀ : X) (y₀ : Y) : C(SmashProduct x₀ y₀, SmashProduct y₀ x₀) :=
  lift ((mk y₀ x₀).comp ContinuousMap.prodSwap) (basepoint y₀ x₀)
    (fun y ↦ by simp) (fun x ↦ by simp)

/-- **Symmetry of the smash product**: `X ∧ Y ≃ₜ Y ∧ X` by swapping the two factors. -/
def comm (x₀ : X) (y₀ : Y) : SmashProduct x₀ y₀ ≃ₜ SmashProduct y₀ x₀ where
  toFun := commMap x₀ y₀
  invFun := commMap y₀ x₀
  left_inv z := by
    induction z using ind with
    | hmk x y => simp [commMap]
  right_inv z' := by
    induction z' using ind with
    | hmk y x => simp [commMap]
  continuous_toFun := (commMap x₀ y₀).continuous
  continuous_invFun := (commMap y₀ x₀).continuous

@[simp]
lemma comm_mk (x : X) (y : Y) : comm x₀ y₀ (mk x₀ y₀ (x, y)) = mk y₀ x₀ (y, x) := by
  simp [comm, commMap]

@[simp]
lemma comm_basepoint : comm x₀ y₀ (basepoint x₀ y₀) = basepoint y₀ x₀ := by
  simp [comm, commMap]

@[simp]
lemma comm_symm (x₀ : X) (y₀ : Y) : (comm x₀ y₀).symm = comm y₀ x₀ := (rfl)

@[simp]
lemma comm_comm_apply (w : SmashProduct x₀ y₀) : comm y₀ x₀ (comm x₀ y₀ w) = w :=
  (comm x₀ y₀).symm_apply_apply w

end Functoriality

section Assoc

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private def assocFwdSlice (x₀ : X) (y₀ : Y) (z₀ : Z) (z : Z) :
    C(SmashProduct x₀ y₀, SmashProduct x₀ (basepoint y₀ z₀)) :=
  lift ⟨fun xy : X × Y ↦ mk x₀ (basepoint y₀ z₀) (xy.1, mk y₀ z₀ (xy.2, z)), by fun_prop⟩
    (basepoint x₀ (basepoint y₀ z₀)) (fun y ↦ by simp) (fun x ↦ by simp)

private def assocFwdProd [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    C(SmashProduct x₀ y₀ × Z, SmashProduct x₀ (basepoint y₀ z₀)) where
  toFun p := assocFwdSlice x₀ y₀ z₀ p.2 p.1
  continuous_toFun := by
    refine (isQuotientMap_mk x₀ y₀).continuous_lift_prod_left ?_
    have hEq : (fun q : (X × Y) × Z ↦ assocFwdSlice x₀ y₀ z₀ q.2 (mk x₀ y₀ q.1)) =
        fun q : (X × Y) × Z ↦ mk x₀ (basepoint y₀ z₀) (q.1.1, mk y₀ z₀ (q.1.2, q.2)) := by
      funext ⟨⟨x, y⟩, z⟩
      exact lift_mk _ _ _ _ x y
    rw [hEq]
    fun_prop

@[simp]
private lemma assocFwdProd_mk [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z)
    (x : X) (y : Y) (z : Z) :
    assocFwdProd x₀ y₀ z₀ (mk x₀ y₀ (x, y), z) = mk x₀ (basepoint y₀ z₀) (x, mk y₀ z₀ (y, z)) := by
  simp [assocFwdProd, assocFwdSlice]

@[simp]
private lemma assocFwdProd_basepoint [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) (z : Z) :
    assocFwdProd x₀ y₀ z₀ (basepoint x₀ y₀, z) = basepoint x₀ (basepoint y₀ z₀) := by
  simp [assocFwdProd, assocFwdSlice]

private def assocFwdMap [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    C(SmashProduct (basepoint x₀ y₀) z₀, SmashProduct x₀ (basepoint y₀ z₀)) :=
  lift (assocFwdProd x₀ y₀ z₀) (basepoint x₀ (basepoint y₀ z₀))
    (fun z ↦ assocFwdProd_basepoint x₀ y₀ z₀ z)
    (fun w ↦ by
      induction w using ind with
      | hmk x y => simp)

private def assocBwdSlice (x₀ : X) (y₀ : Y) (z₀ : Z) (x : X) :
    C(SmashProduct y₀ z₀, SmashProduct (basepoint x₀ y₀) z₀) :=
  lift ⟨fun yz : Y × Z ↦ mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (x, yz.1), yz.2), by fun_prop⟩
    (basepoint (basepoint x₀ y₀) z₀) (fun z ↦ by simp) (fun y ↦ by simp)

private def assocBwdProd [LocallyCompactSpace X] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    C(X × SmashProduct y₀ z₀, SmashProduct (basepoint x₀ y₀) z₀) where
  toFun p := assocBwdSlice x₀ y₀ z₀ p.1 p.2
  continuous_toFun := by
    refine (isQuotientMap_mk y₀ z₀).continuous_lift_prod_right ?_
    have hEq : (fun q : X × (Y × Z) ↦ assocBwdSlice x₀ y₀ z₀ q.1 (mk y₀ z₀ q.2)) =
        fun q : X × (Y × Z) ↦ mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (q.1, q.2.1), q.2.2) := by
      funext ⟨x, ⟨y, z⟩⟩
      exact lift_mk _ _ _ _ y z
    rw [hEq]
    fun_prop

@[simp]
private lemma assocBwdProd_mk [LocallyCompactSpace X] (x₀ : X) (y₀ : Y) (z₀ : Z)
    (x : X) (y : Y) (z : Z) :
    assocBwdProd x₀ y₀ z₀ (x, mk y₀ z₀ (y, z)) = mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (x, y), z) := by
  simp [assocBwdProd, assocBwdSlice]

@[simp]
private lemma assocBwdProd_basepoint [LocallyCompactSpace X] (x₀ : X) (y₀ : Y) (z₀ : Z) (x : X) :
    assocBwdProd x₀ y₀ z₀ (x, basepoint y₀ z₀) = basepoint (basepoint x₀ y₀) z₀ := by
  simp [assocBwdProd, assocBwdSlice]

private def assocBwdMap [LocallyCompactSpace X] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    C(SmashProduct x₀ (basepoint y₀ z₀), SmashProduct (basepoint x₀ y₀) z₀) :=
  lift (assocBwdProd x₀ y₀ z₀) (basepoint (basepoint x₀ y₀) z₀)
    (fun w ↦ by
      induction w using ind with
      | hmk y z => simp)
    (fun x ↦ assocBwdProd_basepoint x₀ y₀ z₀ x)

/-- **Associativity of the smash product**: `(X ∧ Y) ∧ Z ≃ₜ X ∧ (Y ∧ Z)` whenever the outer factors
`X` and `Z` are locally compact (in particular for all compact Hausdorff spaces). -/
def assoc [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    SmashProduct (basepoint x₀ y₀) z₀ ≃ₜ SmashProduct x₀ (basepoint y₀ z₀) where
  toFun := assocFwdMap x₀ y₀ z₀
  invFun := assocBwdMap x₀ y₀ z₀
  left_inv q := by
    induction q using ind with
    | hmk w z =>
      induction w using ind with
      | hmk x y => simp [assocFwdMap, assocBwdMap]
  right_inv q := by
    induction q using ind with
    | hmk x w =>
      induction w using ind with
      | hmk y z => simp [assocFwdMap, assocBwdMap]
  continuous_toFun := (assocFwdMap x₀ y₀ z₀).continuous
  continuous_invFun := (assocBwdMap x₀ y₀ z₀).continuous

@[simp]
lemma assoc_mk [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z)
    (x : X) (y : Y) (z : Z) :
    assoc x₀ y₀ z₀ (mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (x, y), z)) =
      mk x₀ (basepoint y₀ z₀) (x, mk y₀ z₀ (y, z)) := by
  simp [assoc, assocFwdMap]

@[simp]
lemma assoc_symm_mk [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z)
    (x : X) (y : Y) (z : Z) :
    (assoc x₀ y₀ z₀).symm (mk x₀ (basepoint y₀ z₀) (x, mk y₀ z₀ (y, z))) =
      mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (x, y), z) := by
  simp [assoc, assocBwdMap]

@[simp]
lemma assoc_basepoint [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    assoc x₀ y₀ z₀ (basepoint (basepoint x₀ y₀) z₀) = basepoint x₀ (basepoint y₀ z₀) := by
  simp [assoc, assocFwdMap]

@[simp]
lemma assoc_symm_basepoint [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y)
    (z₀ : Z) :
    (assoc x₀ y₀ z₀).symm (basepoint x₀ (basepoint y₀ z₀)) = basepoint (basepoint x₀ y₀) z₀ := by
  simp [assoc, assocBwdMap]

end Assoc

end SmashProduct

end TauCeti

namespace TopPair

open TauCeti

section ProdQuotient

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (B : Set Y)

/-- The canonical continuous map `(X × Y) / (A × Y ∪ X × B) → (X / A) ∧ (Y / B)` sending `(x, y)`
to `π_A x ∧ π_B y` and the basepoint to the smash basepoint. -/
def ordinaryPairQuotientProdToSmash :
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotient ⟶
      SmashProduct (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientBasepoint
        (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientBasepoint :=
  (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientDesc
    (TopCat.ofHom ((SmashProduct.mk _ _).comp
      (((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ).hom.prodMap
        ((ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ).hom)))
    (SmashProduct.basepoint _ _) fun b ↦ by
      rcases b.2 with ⟨hxA, -⟩ | ⟨-, hyB⟩
      · have hπ : (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ b.1.1 =
            (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientBasepoint :=
          (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ_map ⟨b.1.1, hxA⟩
        exact (congrArg (fun u ↦ SmashProduct.mk _ _ (u, _)) hπ).trans
          (SmashProduct.mk_basepoint_left _)
      · have hπ : (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ b.1.2 =
            (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientBasepoint :=
          (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ_map ⟨b.1.2, hyB⟩
        exact (congrArg (fun v ↦ SmashProduct.mk _ _ (_, v)) hπ).trans
          (SmashProduct.mk_basepoint_right _)

@[simp]
lemma ordinaryPairQuotientProdToSmash_π (x : X) (y : Y) :
    ordinaryPairQuotientProdToSmash A B
      ((ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y)) =
      SmashProduct.mk _ _
        ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ x,
          (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ y) :=
  ordinaryPairQuotientπ_desc_apply (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B))
    _ _ _ (x, y)

@[simp]
lemma ordinaryPairQuotientProdToSmash_basepoint :
    ordinaryPairQuotientProdToSmash A B
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint =
      SmashProduct.basepoint _ _ :=
  ordinaryPairQuotientDesc_basepoint (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B))
    _ _ _

private def prodQuotientFromRight (x : X)
    (qb : (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient) :
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotient :=
  (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientDesc
    (TopCat.ofHom ⟨fun y ↦ (ofSubset (X := TopCat.of (X × Y))
      (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y),
      ((ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ).hom.continuous.comp
        (continuous_const.prodMk continuous_id)⟩)
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint
    (fun b ↦ (ofSubset (X := TopCat.of (X × Y))
      (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ_map ⟨(x, b.1), Or.inr ⟨trivial, b.2⟩⟩)
    qb

@[simp]
private lemma prodQuotientFromRight_π (x : X) (y : Y) :
    prodQuotientFromRight A B x ((ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ y) =
      (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y) :=
  ordinaryPairQuotientπ_desc_apply (ofSubset (X := TopCat.of Y) B) _ _ _ y

@[simp]
private lemma prodQuotientFromRight_basepoint (x : X) :
    prodQuotientFromRight A B x (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientBasepoint =
      (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint :=
  ordinaryPairQuotientDesc_basepoint _ _ _ _

private lemma continuous_prodQuotientFromRight [LocallyCompactSpace X] :
    Continuous fun p : X × (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient ↦
      prodQuotientFromRight A B p.1 p.2 := by
  refine (ofSubset (X := TopCat.of Y) B).isQuotientMap_ordinaryPairQuotient
    |>.continuous_lift_prod_right ?_
  refine (Homeomorph.prodSumDistrib (Z := PUnit.{u + 1})).symm.comp_continuous_iff'.1 ?_
  refine continuous_sum_dom.2 ⟨?_, ?_⟩
  · exact ((ofSubset (X := TopCat.of (X × Y))
      (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ).hom.continuous.congr fun ⟨x, y⟩ ↦
      (prodQuotientFromRight_π A B x y).symm
  · exact (continuous_const (y := (ofSubset (X := TopCat.of (X × Y))
      (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint)).congr fun ⟨x, _⟩ ↦
      (prodQuotientFromRight_basepoint A B x).symm

private def prodQuotientFromBoth (qa : (ofSubset (X := TopCat.of X) A).ordinaryPairQuotient)
    (qb : (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient) :
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotient :=
  (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientDesc
    (TopCat.ofHom ⟨fun x ↦ prodQuotientFromRight A B x qb,
      -- Continuity in `x` for fixed `qb` holds by case analysis on `qb`.
      by
        induction qb using ordinaryPairQuotient_ind with
        | hπ y =>
          exact (((ofSubset (X := TopCat.of (X × Y))
            (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ).hom.continuous.comp
            (continuous_id.prodMk (continuous_const (y := y)))).congr fun x ↦
            (prodQuotientFromRight_π A B x y).symm
        | hbase =>
          exact (continuous_const (y := (ofSubset (X := TopCat.of (X × Y))
            (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint)).congr fun x ↦
            (prodQuotientFromRight_basepoint A B x).symm⟩)
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint
    (fun a ↦ by
      induction qb using ordinaryPairQuotient_ind with
      | hπ y =>
        exact (prodQuotientFromRight_π A B a.1 y).trans
          ((ofSubset (X := TopCat.of (X × Y))
            (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ_map ⟨(a.1, y), Or.inl ⟨a.2, trivial⟩⟩)
      | hbase => exact prodQuotientFromRight_basepoint A B a.1)
    qa

@[simp]
private lemma prodQuotientFromBoth_π (x : X)
    (qb : (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient) :
    prodQuotientFromBoth A B ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ x) qb =
      prodQuotientFromRight A B x qb :=
  ordinaryPairQuotientπ_desc_apply (ofSubset (X := TopCat.of X) A) _ _ _ x

@[simp]
private lemma prodQuotientFromBoth_basepoint
    (qb : (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient) :
    prodQuotientFromBoth A B (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientBasepoint qb =
      (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint :=
  ordinaryPairQuotientDesc_basepoint _ _ _ _

private lemma continuous_prodQuotientFromBoth [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    Continuous fun p : (ofSubset (X := TopCat.of X) A).ordinaryPairQuotient ×
      (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient ↦ prodQuotientFromBoth A B p.1 p.2 := by
  refine (ofSubset (X := TopCat.of X) A).isQuotientMap_ordinaryPairQuotient
    |>.continuous_lift_prod_left ?_
  refine (Homeomorph.sumProdDistrib (Y := PUnit.{u + 1})
    (Z := (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient)).symm.comp_continuous_iff'.1 ?_
  refine continuous_sum_dom.2 ⟨?_, ?_⟩
  · exact (continuous_prodQuotientFromRight A B).congr fun ⟨x, qb⟩ ↦
      (prodQuotientFromBoth_π A B x qb).symm
  · exact (continuous_const (y := (ofSubset (X := TopCat.of (X × Y))
      (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint)).congr fun ⟨_, qb⟩ ↦
      (prodQuotientFromBoth_basepoint A B qb).symm

private def prodQuotientFromBothMap [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    C((ofSubset (X := TopCat.of X) A).ordinaryPairQuotient ×
        (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient,
      (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotient) :=
  ⟨fun p ↦ prodQuotientFromBoth A B p.1 p.2, continuous_prodQuotientFromBoth A B⟩

@[simp]
private lemma prodQuotientFromBothMap_π_π [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] (x : X) (y : Y) :
    prodQuotientFromBothMap A B
      ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ x,
        (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ y) =
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y) := by
  simp [prodQuotientFromBothMap]

@[simp]
private lemma prodQuotientFromBothMap_basepoint_left [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient]
    (qb : (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient) :
    prodQuotientFromBothMap A B
      ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientBasepoint, qb) =
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint := by
  simp [prodQuotientFromBothMap]

@[simp]
private lemma prodQuotientFromBothMap_basepoint_right [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient]
    (qa : (ofSubset (X := TopCat.of X) A).ordinaryPairQuotient) :
    prodQuotientFromBothMap A B
      (qa, (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientBasepoint) =
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint := by
  induction qa using ordinaryPairQuotient_ind with
  | hπ x =>
    exact (prodQuotientFromBoth_π A B x _).trans (prodQuotientFromRight_basepoint A B x)
  | hbase => exact prodQuotientFromBothMap_basepoint_left A B _

private def smashToOrdinaryPairQuotientProd [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    C(SmashProduct (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientBasepoint
        (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientBasepoint,
      (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotient) :=
  SmashProduct.lift (prodQuotientFromBothMap A B)
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint
    (prodQuotientFromBothMap_basepoint_left A B)
    (prodQuotientFromBothMap_basepoint_right A B)

private lemma smashToOrdinaryPairQuotientProd_mk_π [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] (x : X) (y : Y) :
    smashToOrdinaryPairQuotientProd A B
      (SmashProduct.mk _ _
        ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ x,
          (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ y)) =
      (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y) :=
  (SmashProduct.lift_mk (prodQuotientFromBothMap A B) _ _ _ _ _).trans
    (prodQuotientFromBothMap_π_π A B x y)

private lemma smashToOrdinaryPairQuotientProd_basepoint [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    smashToOrdinaryPairQuotientProd A B (SmashProduct.basepoint _ _) =
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint := by
  simp [smashToOrdinaryPairQuotientProd]

/-- **The pointed quotient of a product pair is the smash product of the pointed quotients.**
When `X` and `Y / B` are locally compact (in particular when `X` and `Y` are compact Hausdorff and
`B` is closed), `(X × Y) / (A × Y ∪ X × B) ≃ₜ (X / A) ∧ (Y / B)`, including when `A` or `B` is
empty. -/
def ordinaryPairQuotientProdHomeomorph [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotient ≃ₜ
      SmashProduct (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientBasepoint
        (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientBasepoint where
  toFun := ordinaryPairQuotientProdToSmash A B
  invFun := smashToOrdinaryPairQuotientProd A B
  left_inv z := by
    induction z using ordinaryPairQuotient_ind with
    | hπ p =>
      rcases p with ⟨x, y⟩
      exact (congrArg (smashToOrdinaryPairQuotientProd A B)
        (ordinaryPairQuotientProdToSmash_π A B x y)).trans
        (smashToOrdinaryPairQuotientProd_mk_π A B x y)
    | hbase =>
      exact (congrArg (smashToOrdinaryPairQuotientProd A B)
        (ordinaryPairQuotientProdToSmash_basepoint A B)).trans
        (smashToOrdinaryPairQuotientProd_basepoint A B)
  right_inv w := by
    induction w using SmashProduct.ind with
    | hmk qa qb =>
      induction qa using ordinaryPairQuotient_ind with
      | hπ x =>
        induction qb using ordinaryPairQuotient_ind with
        | hπ y =>
          exact (congrArg (ordinaryPairQuotientProdToSmash A B)
            (smashToOrdinaryPairQuotientProd_mk_π A B x y)).trans
            (ordinaryPairQuotientProdToSmash_π A B x y)
        | hbase =>
          rw [SmashProduct.mk_basepoint_right]
          exact (congrArg (ordinaryPairQuotientProdToSmash A B)
            (smashToOrdinaryPairQuotientProd_basepoint A B)).trans
            (ordinaryPairQuotientProdToSmash_basepoint A B)
      | hbase =>
        rw [SmashProduct.mk_basepoint_left]
        exact (congrArg (ordinaryPairQuotientProdToSmash A B)
          (smashToOrdinaryPairQuotientProd_basepoint A B)).trans
          (ordinaryPairQuotientProdToSmash_basepoint A B)
  continuous_toFun := (ordinaryPairQuotientProdToSmash A B).hom.continuous
  continuous_invFun := (smashToOrdinaryPairQuotientProd A B).continuous

@[simp]
lemma ordinaryPairQuotientProdHomeomorph_π [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] (x : X) (y : Y) :
    ordinaryPairQuotientProdHomeomorph A B
      ((ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y)) =
      SmashProduct.mk _ _
        ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ x,
          (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ y) :=
  ordinaryPairQuotientProdToSmash_π A B x y

@[simp]
lemma ordinaryPairQuotientProdHomeomorph_basepoint [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    ordinaryPairQuotientProdHomeomorph A B
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint =
      SmashProduct.basepoint _ _ :=
  ordinaryPairQuotientProdToSmash_basepoint A B

@[simp]
lemma ordinaryPairQuotientProdHomeomorph_symm_mk_π [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] (x : X) (y : Y) :
    (ordinaryPairQuotientProdHomeomorph A B).symm
      (SmashProduct.mk _ _
        ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ x,
          (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ y)) =
      (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y) :=
  smashToOrdinaryPairQuotientProd_mk_π A B x y

@[simp]
lemma ordinaryPairQuotientProdHomeomorph_symm_basepoint [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    (ordinaryPairQuotientProdHomeomorph A B).symm (SmashProduct.basepoint _ _) =
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint :=
  smashToOrdinaryPairQuotientProd_basepoint A B

end ProdQuotient

end TopPair
