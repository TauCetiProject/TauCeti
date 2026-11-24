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
is constructed as `TopPair.ordinaryPairQuotient` of `TauCeti.smashPair`, so relative homology and
cohomology comparisons for pair quotients apply directly.

Because `(x₀, y₀)` belongs to the collapsed subspace, `TauCeti.SmashProduct.mk x₀ y₀` is
unconditionally a surjective quotient map (`TauCeti.SmashProduct.isQuotientMap_mk`), with universal
mapping property `TauCeti.SmashProduct.lift`. When `X` and `Y / B` are locally compact,
`TopPair.ordinaryPairQuotientProdHomeomorph` gives `(X × Y) / (A × Y ∪ X × B) ≃ₜ (X / A) ∧ (Y / B)`
including empty subspaces; when `X` and `Z` are locally compact, `TauCeti.SmashProduct.assoc` gives
`(X ∧ Y) ∧ Z ≃ₜ X ∧ (Y ∧ Z)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0.
* J. P. May, *A Concise Course in Algebraic Topology*, Section 8.1.
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
  exact ⟨fun h ↦ h.elim (Or.inr ∘ And.right) (Or.inl ∘ And.left),
    fun h ↦ h.elim (fun hx ↦ Or.inr ⟨hx, trivial⟩) fun hy ↦ Or.inl ⟨trivial, hy⟩⟩

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

instance : Inhabited (SmashProduct x₀ y₀) := ⟨basepoint x₀ y₀⟩

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
      (x = x' ∧ y = y') ∨ (x = x₀ ∨ y = y₀) ∧ (x' = x₀ ∨ y' = y₀) :=
  ((smashPair x₀ y₀).ordinaryPairQuotientπ_eq_iff (x, y) (x', y')).trans <|
    or_congr ⟨Prod.mk.inj, fun ⟨h₁, h₂⟩ ↦ Prod.ext h₁ h₂⟩
      (and_congr (mem_range_smashPair_map_iff (p := (x, y)))
        (mem_range_smashPair_map_iff (p := (x', y'))))

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
    (hmk : ∀ x y, motive (mk x₀ y₀ (x, y))) (z : SmashProduct x₀ y₀) : motive z :=
  let ⟨⟨x, y⟩, h⟩ := surjective_mk x₀ y₀ z; h ▸ hmk x y

lemma isOpen_iff {s : Set (SmashProduct x₀ y₀)} : IsOpen s ↔ IsOpen (mk x₀ y₀ ⁻¹' s) :=
  (smashPair x₀ y₀).isOpen_ordinaryPairQuotient_iff

lemma isClosed_iff {s : Set (SmashProduct x₀ y₀)} : IsClosed s ↔ IsClosed (mk x₀ y₀ ⁻¹' s) :=
  (smashPair x₀ y₀).isClosed_ordinaryPairQuotient_iff

/-- **Extensionality for continuous maps out of `X ∧ Y`.** -/
@[ext]
lemma hom_ext {Z : Type v} [TopologicalSpace Z] {f g : C(SmashProduct x₀ y₀, Z)}
    (h : ∀ x y, f (mk x₀ y₀ (x, y)) = g (mk x₀ y₀ (x, y))) : f = g :=
  DFunLike.ext _ _ (ind h)

private lemma factorsThrough_mk {Z : Type v} {f : X × Y → Z} (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) :
    Function.FactorsThrough f (mk x₀ y₀) := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h ↦
  (mk_eq_mk_iff.1 h).elim (fun ⟨hx, hy⟩ ↦ hx ▸ hy ▸ rfl) fun ⟨h₁, h₂⟩ ↦
    (h₁.elim (· ▸ hx₀ y₁) (· ▸ hy₀ x₁)).trans (h₂.elim (· ▸ hx₀ y₂) (· ▸ hy₀ x₂)).symm

/-- **The universal property of the smash product.** A continuous map `f : C(X × Y, Z)` taking a
constant value `z₀` along `{x₀} × Y` and `X × {y₀}` descends to `C(SmashProduct x₀ y₀, Z)`. -/
def lift {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) : C(SmashProduct x₀ y₀, Z) :=
  (isQuotientMap_mk x₀ y₀).lift f (factorsThrough_mk z₀ hx₀ hy₀)

@[simp]
lemma lift_mk {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) (x : X) (y : Y) :
    lift f z₀ hx₀ hy₀ (mk x₀ y₀ (x, y)) = f (x, y) :=
  DFunLike.congr_fun ((isQuotientMap_mk x₀ y₀).lift_comp f (factorsThrough_mk z₀ hx₀ hy₀)) (x, y)

@[simp]
lemma lift_comp_mk {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) :
    (lift f z₀ hx₀ hy₀).comp (mk x₀ y₀) = f :=
  DFunLike.ext _ _ fun ⟨x, y⟩ ↦ lift_mk f z₀ hx₀ hy₀ x y

@[simp]
lemma lift_basepoint {Z : Type v} [TopologicalSpace Z] (f : C(X × Y, Z)) (z₀ : Z)
    (hx₀ : ∀ y, f (x₀, y) = z₀) (hy₀ : ∀ x, f (x, y₀) = z₀) :
    lift f z₀ hx₀ hy₀ (basepoint x₀ y₀) = z₀ := by
  rw [← mk_basepoint_left (x₀ := x₀) y₀, lift_mk, hx₀]

instance [CompactSpace X] [CompactSpace Y] : CompactSpace (SmashProduct x₀ y₀) :=
  haveI : CompactSpace (smashPair x₀ y₀).fst := inferInstanceAs (CompactSpace (X × Y))
  (smashPair x₀ y₀).compactSpace_ordinaryPairQuotient

private lemma disjoint_nhdsSet_smashAxes [T2Space X] [T2Space Y] {x : X} {y : Y}
    (hx : x ≠ x₀) (hy : y ≠ y₀) :
    Disjoint (𝓝ˢ (univ ×ˢ {y₀} ∪ {x₀} ×ˢ univ : Set (X × Y))) (𝓝 (x, y)) := by
  rw [nhdsSet_union, disjoint_sup_left, nhds_prod_eq]
  exact ⟨(Filter.disjoint_prod.2 <| Or.inr <|
      isCompact_singleton.disjoint_nhdsSet_nhds hy).mono_left (nhdsSet_prod_le _ _),
    (Filter.disjoint_prod.2 <| Or.inl <|
      isCompact_singleton.disjoint_nhdsSet_nhds hx).mono_left (nhdsSet_prod_le _ _)⟩

instance [T2Space X] [T2Space Y] : T2Space (SmashProduct x₀ y₀) := by
  -- The ambient space `(smashPair x₀ y₀).fst` is `TopCat.of (X × Y)`, whose carrier and topology
  -- are definitionally `X × Y` with its product topology (`TopCat.coe_of`).
  have : T2Space (smashPair x₀ y₀).fst := inferInstanceAs (T2Space (X × Y))
  refine (smashPair x₀ y₀).t2Space_ordinaryPairQuotient_of_disjoint_nhdsSet fun ⟨x, y⟩ h ↦ ?_
  rw [TopPair.range_ofSubset_map] at h ⊢
  exact disjoint_nhdsSet_smashAxes
    (fun hx ↦ h (Or.inr ⟨hx, trivial⟩)) (fun hy ↦ h (Or.inl ⟨trivial, hy⟩))

instance subsingleton_left [Subsingleton X] : Subsingleton (SmashProduct x₀ y₀) :=
  subsingleton_of_forall_eq (basepoint x₀ y₀)
    (ind fun x y ↦ Subsingleton.elim x x₀ ▸ mk_basepoint_left y)

instance subsingleton_right [Subsingleton Y] : Subsingleton (SmashProduct x₀ y₀) :=
  subsingleton_of_forall_eq (basepoint x₀ y₀)
    (ind fun x y ↦ Subsingleton.elim y y₀ ▸ mk_basepoint_right x)

end Basic

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
      ContinuousMap.id (SmashProduct x₀ y₀) :=
  hom_ext fun x y ↦ map_mk _ _ _ _ x y

lemma map_comp (f : C(X, X')) (g : C(Y, Y')) (hf : f x₀ = x₀') (hg : g y₀ = y₀')
    (f' : C(X', X'')) (g' : C(Y', Y'')) (hf' : f' x₀' = x₀'') (hg' : g' y₀' = y₀'') :
    (map f' g' hf' hg').comp (map f g hf hg) =
      map (f'.comp f) (g'.comp g) (by simp [hf, hf']) (by simp [hg, hg']) :=
  hom_ext fun x y ↦ by simp

/-- Pointed homeomorphisms `X ≃ₜ X'` and `Y ≃ₜ Y'` induce a homeomorphism `X ∧ Y ≃ₜ X' ∧ Y'`. -/
def congrHomeomorph (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀') (he₂ : e₂ y₀ = y₀') :
    SmashProduct x₀ y₀ ≃ₜ SmashProduct x₀' y₀' where
  toFun := map (e₁ : C(X, X')) (e₂ : C(Y, Y')) he₁ he₂
  invFun := map (e₁.symm : C(X', X)) (e₂.symm : C(Y', Y)) (e₁.symm_apply_eq.2 he₁.symm)
    (e₂.symm_apply_eq.2 he₂.symm)
  left_inv := ind fun x y ↦ by simp
  right_inv := ind fun x' y' ↦ by simp
  continuous_toFun := (map (e₁ : C(X, X')) (e₂ : C(Y, Y')) he₁ he₂).continuous
  continuous_invFun := (map (e₁.symm : C(X', X)) (e₂.symm : C(Y', Y))
    (e₁.symm_apply_eq.2 he₁.symm) (e₂.symm_apply_eq.2 he₂.symm)).continuous

@[simp]
lemma congrHomeomorph_mk (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀') (he₂ : e₂ y₀ = y₀')
    (x : X) (y : Y) :
    congrHomeomorph e₁ e₂ he₁ he₂ (mk x₀ y₀ (x, y)) = mk x₀' y₀' (e₁ x, e₂ y) :=
  map_mk _ _ he₁ he₂ x y

@[simp]
lemma congrHomeomorph_basepoint (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀')
    (he₂ : e₂ y₀ = y₀') :
    congrHomeomorph e₁ e₂ he₁ he₂ (basepoint x₀ y₀) = basepoint x₀' y₀' :=
  map_basepoint _ _ he₁ he₂

@[simp]
lemma congrHomeomorph_symm (e₁ : X ≃ₜ X') (e₂ : Y ≃ₜ Y') (he₁ : e₁ x₀ = x₀')
    (he₂ : e₂ y₀ = y₀') :
    (congrHomeomorph e₁ e₂ he₁ he₂).symm =
      congrHomeomorph e₁.symm e₂.symm (e₁.symm_apply_eq.2 he₁.symm)
        (e₂.symm_apply_eq.2 he₂.symm) := (rfl)

private def commMap (x₀ : X) (y₀ : Y) : C(SmashProduct x₀ y₀, SmashProduct y₀ x₀) :=
  lift ((mk y₀ x₀).comp ContinuousMap.prodSwap) (basepoint y₀ x₀) (by simp) (by simp)

/-- **Symmetry of the smash product**: `X ∧ Y ≃ₜ Y ∧ X` by swapping the two factors. -/
def comm (x₀ : X) (y₀ : Y) : SmashProduct x₀ y₀ ≃ₜ SmashProduct y₀ x₀ where
  toFun := commMap x₀ y₀
  invFun := commMap y₀ x₀
  left_inv := ind fun x y ↦ by simp [commMap]
  right_inv := ind fun y x ↦ by simp [commMap]
  continuous_toFun := (commMap x₀ y₀).continuous
  continuous_invFun := (commMap y₀ x₀).continuous

@[simp]
lemma comm_mk (x : X) (y : Y) : comm x₀ y₀ (mk x₀ y₀ (x, y)) = mk y₀ x₀ (y, x) := by
  simp [comm, commMap]

@[simp]
lemma comm_basepoint : comm x₀ y₀ (basepoint x₀ y₀) = basepoint y₀ x₀ := by simp [comm, commMap]

@[simp]
lemma comm_symm (x₀ : X) (y₀ : Y) : (comm x₀ y₀).symm = comm y₀ x₀ := (rfl)

@[simp]
lemma comm_comm_apply (w : SmashProduct x₀ y₀) : comm y₀ x₀ (comm x₀ y₀ w) = w :=
  (comm x₀ y₀).symm_apply_apply w

instance pathConnectedSpace_left [PathConnectedSpace X] :
    PathConnectedSpace (SmashProduct x₀ y₀) where
  nonempty := ⟨basepoint x₀ y₀⟩
  joined :=
    have hbase : ∀ z, Joined (basepoint x₀ y₀) z := ind fun x y ↦ by
      simpa only [mk_basepoint_left] using (PathConnectedSpace.joined x₀ x).map
        (f := fun u ↦ mk x₀ y₀ (u, y))
        ((mk x₀ y₀).continuous.comp (continuous_id.prodMk continuous_const))
    fun z₁ z₂ ↦ (hbase z₁).symm.trans (hbase z₂)

instance pathConnectedSpace_right [PathConnectedSpace Y] :
    PathConnectedSpace (SmashProduct x₀ y₀) :=
  (comm y₀ x₀).pathConnectedSpace

end Functoriality

section Assoc

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private def assocFwdSlice (x₀ : X) (y₀ : Y) (z₀ : Z) (z : Z) :
    C(SmashProduct x₀ y₀, SmashProduct x₀ (basepoint y₀ z₀)) :=
  lift ⟨fun xy : X × Y ↦ mk x₀ (basepoint y₀ z₀) (xy.1, mk y₀ z₀ (xy.2, z)), by fun_prop⟩
    (basepoint x₀ (basepoint y₀ z₀)) (by simp) (by simp)

private def assocFwdProd [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    C(SmashProduct x₀ y₀ × Z, SmashProduct x₀ (basepoint y₀ z₀)) where
  toFun p := assocFwdSlice x₀ y₀ z₀ p.2 p.1
  continuous_toFun := (isQuotientMap_mk x₀ y₀).continuous_lift_prod_left <| by
    have hEq : (fun q : (X × Y) × Z ↦ assocFwdSlice x₀ y₀ z₀ q.2 (mk x₀ y₀ q.1)) =
        fun q ↦ mk x₀ (basepoint y₀ z₀) (q.1.1, mk y₀ z₀ (q.1.2, q.2)) :=
      funext fun ⟨⟨x, y⟩, _⟩ ↦ lift_mk _ _ _ _ x y
    rw [hEq]; fun_prop

private def assocFwdMap [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    C(SmashProduct (basepoint x₀ y₀) z₀, SmashProduct x₀ (basepoint y₀ z₀)) :=
  lift (assocFwdProd x₀ y₀ z₀) (basepoint x₀ (basepoint y₀ z₀))
    (fun _ ↦ by simp [assocFwdProd, assocFwdSlice])
    (ind fun x y ↦ by simp [assocFwdProd, assocFwdSlice])

@[simp]
private lemma assocFwdMap_mk [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z)
    (x : X) (y : Y) (z : Z) :
    assocFwdMap x₀ y₀ z₀ (mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (x, y), z)) =
      mk x₀ (basepoint y₀ z₀) (x, mk y₀ z₀ (y, z)) := by
  simp [assocFwdMap, assocFwdProd, assocFwdSlice]

/-- **Associativity of the smash product**: `(X ∧ Y) ∧ Z ≃ₜ X ∧ (Y ∧ Z)` whenever the outer factors
`X` and `Z` are locally compact (in particular for all compact Hausdorff spaces). -/
def assoc [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    SmashProduct (basepoint x₀ y₀) z₀ ≃ₜ SmashProduct x₀ (basepoint y₀ z₀) :=
  let e₁ := (comm x₀ (basepoint y₀ z₀)).trans <| congrHomeomorph (comm y₀ z₀) (.refl X)
    comm_basepoint (congrFun (Homeomorph.refl_apply X) x₀)
  let e₂ := (congrHomeomorph (.refl Z) (comm y₀ x₀) (congrFun (Homeomorph.refl_apply Z) z₀)
    comm_basepoint).trans (comm z₀ (basepoint x₀ y₀))
  { toFun := assocFwdMap x₀ y₀ z₀
    invFun p := e₂ (assocFwdMap z₀ y₀ x₀ (e₁ p))
    left_inv := ind <| ind fun x y z ↦ by simp [e₁, e₂]
    right_inv := ind fun x ↦ ind fun y z ↦ by simp [e₁, e₂]
    continuous_toFun := (assocFwdMap x₀ y₀ z₀).continuous
    continuous_invFun := e₂.continuous.comp ((assocFwdMap z₀ y₀ x₀).continuous.comp e₁.continuous) }

@[simp]
lemma assoc_mk [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z)
    (x : X) (y : Y) (z : Z) :
    assoc x₀ y₀ z₀ (mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (x, y), z)) =
      mk x₀ (basepoint y₀ z₀) (x, mk y₀ z₀ (y, z)) :=
  assocFwdMap_mk x₀ y₀ z₀ x y z

@[simp]
lemma assoc_symm_mk [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z)
    (x : X) (y : Y) (z : Z) :
    (assoc x₀ y₀ z₀).symm (mk x₀ (basepoint y₀ z₀) (x, mk y₀ z₀ (y, z))) =
      mk (basepoint x₀ y₀) z₀ (mk x₀ y₀ (x, y), z) :=
  (assoc x₀ y₀ z₀).symm_apply_eq.2 (assoc_mk x₀ y₀ z₀ x y z).symm

@[simp]
lemma assoc_basepoint [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y) (z₀ : Z) :
    assoc x₀ y₀ z₀ (basepoint (basepoint x₀ y₀) z₀) = basepoint x₀ (basepoint y₀ z₀) := by
  simp [assoc, assocFwdMap]

@[simp]
lemma assoc_symm_basepoint [LocallyCompactSpace X] [LocallyCompactSpace Z] (x₀ : X) (y₀ : Y)
    (z₀ : Z) :
    (assoc x₀ y₀ z₀).symm (basepoint x₀ (basepoint y₀ z₀)) = basepoint (basepoint x₀ y₀) z₀ :=
  (assoc x₀ y₀ z₀).symm_apply_eq.2 (assoc_basepoint x₀ y₀ z₀).symm

end Assoc

end SmashProduct

end TauCeti

namespace TopPair

open TauCeti

section ProdQuotient

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (B : Set Y)

private abbrev qLeft : TopPair.{u} := ofSubset (X := TopCat.of X) A
private abbrev qRight : TopPair.{u} := ofSubset (X := TopCat.of Y) B
private abbrev qProd : TopPair.{u} := ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)

/-- The canonical continuous map `(X × Y) / (A × Y ∪ X × B) → (X / A) ∧ (Y / B)` sending `(x, y)`
to `π_A x ∧ π_B y` and the basepoint to the smash basepoint. -/
def ordinaryPairQuotientProdToSmash :
    (ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotient ⟶
      SmashProduct (ofSubset (X := TopCat.of X) A).ordinaryPairQuotientBasepoint
        (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientBasepoint :=
  (qProd A B).ordinaryPairQuotientDesc
    (TopCat.ofHom ((SmashProduct.mk _ _).comp
      (((qLeft A).ordinaryPairQuotientπ).hom.prodMap ((qRight B).ordinaryPairQuotientπ).hom)))
    (SmashProduct.basepoint _ _) fun b ↦ b.property.elim
      (fun ⟨hxA, _⟩ ↦ (congrArg (fun u ↦ SmashProduct.mk _ _ (u, _))
        ((qLeft A).ordinaryPairQuotientπ_map ⟨b.val.1, hxA⟩)).trans
        (SmashProduct.mk_basepoint_left _))
      (fun ⟨_, hyB⟩ ↦ (congrArg (fun v ↦ SmashProduct.mk _ _ (_, v))
        ((qRight B).ordinaryPairQuotientπ_map ⟨b.val.2, hyB⟩)).trans
        (SmashProduct.mk_basepoint_right _))

@[simp]
lemma ordinaryPairQuotientProdToSmash_π (x : X) (y : Y) :
    ordinaryPairQuotientProdToSmash A B
      ((ofSubset (X := TopCat.of (X × Y)) (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientπ (x, y)) =
      SmashProduct.mk _ _
        ((ofSubset (X := TopCat.of X) A).ordinaryPairQuotientπ x,
          (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotientπ y) :=
  ordinaryPairQuotientπ_desc_apply (qProd A B) _ _ _ (x, y)

@[simp]
lemma ordinaryPairQuotientProdToSmash_basepoint :
    ordinaryPairQuotientProdToSmash A B
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint =
      SmashProduct.basepoint _ _ :=
  ordinaryPairQuotientDesc_basepoint (qProd A B) _ _ _

private def prodQuotientFromRight (x : X)
    (qb : (qRight B).ordinaryPairQuotient) : (qProd A B).ordinaryPairQuotient :=
  (qRight B).ordinaryPairQuotientDesc
    (TopCat.ofHom ⟨fun y ↦ (qProd A B).ordinaryPairQuotientπ (x, y),
      ((qProd A B).ordinaryPairQuotientπ).hom.continuous.comp
        (continuous_const.prodMk continuous_id)⟩)
    (qProd A B).ordinaryPairQuotientBasepoint
    (fun b ↦ (qProd A B).ordinaryPairQuotientπ_map ⟨(x, b.val), Or.inr ⟨trivial, b.property⟩⟩) qb

@[simp]
private lemma prodQuotientFromRight_π (x : X) (y : Y) :
    prodQuotientFromRight A B x ((qRight B).ordinaryPairQuotientπ y) =
      (qProd A B).ordinaryPairQuotientπ (x, y) :=
  ordinaryPairQuotientπ_desc_apply (qRight B) _ _ _ y

@[simp]
private lemma prodQuotientFromRight_basepoint (x : X) :
    prodQuotientFromRight A B x (qRight B).ordinaryPairQuotientBasepoint =
      (qProd A B).ordinaryPairQuotientBasepoint :=
  ordinaryPairQuotientDesc_basepoint _ _ _ _

private lemma continuous_prodQuotientFromRight [LocallyCompactSpace X] :
    Continuous fun p : X × (qRight B).ordinaryPairQuotient ↦
      prodQuotientFromRight A B p.1 p.2 := by
  refine (qRight B).isQuotientMap_ordinaryPairQuotient.continuous_lift_prod_right ?_
  refine (Homeomorph.prodSumDistrib (Z := PUnit.{u + 1})).symm.comp_continuous_iff'.1
    (continuous_sum_dom.2 ⟨?_, ?_⟩)
  · exact ((qProd A B).ordinaryPairQuotientπ).hom.continuous.congr
      fun ⟨x, y⟩ ↦ (prodQuotientFromRight_π A B x y).symm
  · exact (continuous_const (y := (qProd A B).ordinaryPairQuotientBasepoint)).congr
      fun ⟨x, _⟩ ↦ (prodQuotientFromRight_basepoint A B x).symm

private def prodQuotientFromBoth (qa : (qLeft A).ordinaryPairQuotient)
    (qb : (qRight B).ordinaryPairQuotient) : (qProd A B).ordinaryPairQuotient :=
  (qLeft A).ordinaryPairQuotientDesc
    (TopCat.ofHom ⟨fun x ↦ prodQuotientFromRight A B x qb,
      ordinaryPairQuotient_ind (P := qRight B)
        (fun y ↦ (((qProd A B).ordinaryPairQuotientπ).hom.continuous.comp
          (continuous_id.prodMk continuous_const)).congr
          fun x ↦ (prodQuotientFromRight_π A B x y).symm)
        ((continuous_const (y := (qProd A B).ordinaryPairQuotientBasepoint)).congr
          fun x ↦ (prodQuotientFromRight_basepoint A B x).symm) qb⟩)
    (qProd A B).ordinaryPairQuotientBasepoint
    (fun a ↦ ordinaryPairQuotient_ind (P := qRight B)
      (fun y ↦ (prodQuotientFromRight_π A B a.val y).trans
        ((qProd A B).ordinaryPairQuotientπ_map ⟨(a.val, y), Or.inl ⟨a.property, trivial⟩⟩))
      (prodQuotientFromRight_basepoint A B a.val) qb) qa

@[simp]
private lemma prodQuotientFromBoth_π (x : X) (qb : (qRight B).ordinaryPairQuotient) :
    prodQuotientFromBoth A B ((qLeft A).ordinaryPairQuotientπ x) qb =
      prodQuotientFromRight A B x qb :=
  ordinaryPairQuotientπ_desc_apply (qLeft A) _ _ _ x

@[simp]
private lemma prodQuotientFromBoth_basepoint (qb : (qRight B).ordinaryPairQuotient) :
    prodQuotientFromBoth A B (qLeft A).ordinaryPairQuotientBasepoint qb =
      (qProd A B).ordinaryPairQuotientBasepoint :=
  ordinaryPairQuotientDesc_basepoint _ _ _ _

private def smashToOrdinaryPairQuotientProd [LocallyCompactSpace X]
    [LocallyCompactSpace (qRight B).ordinaryPairQuotient] :
    C(SmashProduct (qLeft A).ordinaryPairQuotientBasepoint (qRight B).ordinaryPairQuotientBasepoint,
      (qProd A B).ordinaryPairQuotient) :=
  SmashProduct.lift
    ⟨fun p ↦ prodQuotientFromBoth A B p.1 p.2, by
      refine (qLeft A).isQuotientMap_ordinaryPairQuotient.continuous_lift_prod_left ?_
      refine (Homeomorph.sumProdDistrib (Y := PUnit.{u + 1})
        (Z := (qRight B).ordinaryPairQuotient)).symm.comp_continuous_iff'.1
        (continuous_sum_dom.2 ⟨?_, ?_⟩)
      · exact (continuous_prodQuotientFromRight A B).congr
          fun ⟨x, qb⟩ ↦ (prodQuotientFromBoth_π A B x qb).symm
      · exact (continuous_const (y := (qProd A B).ordinaryPairQuotientBasepoint)).congr
          fun ⟨_, qb⟩ ↦ (prodQuotientFromBoth_basepoint A B qb).symm⟩
    (qProd A B).ordinaryPairQuotientBasepoint
    (prodQuotientFromBoth_basepoint A B)
    (ordinaryPairQuotient_ind (P := qLeft A)
      (fun x ↦ (prodQuotientFromBoth_π A B x _).trans (prodQuotientFromRight_basepoint A B x))
      (prodQuotientFromBoth_basepoint A B _))

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
  left_inv := ordinaryPairQuotient_ind (P := qProd A B)
    (fun ⟨x, y⟩ ↦ (congrArg (smashToOrdinaryPairQuotientProd A B)
      (ordinaryPairQuotientProdToSmash_π A B x y)).trans
      (by simp [smashToOrdinaryPairQuotientProd]))
    ((congrArg (smashToOrdinaryPairQuotientProd A B)
      (ordinaryPairQuotientProdToSmash_basepoint A B)).trans
      (by simp [smashToOrdinaryPairQuotientProd]))
  right_inv := SmashProduct.ind <|
    ordinaryPairQuotient_ind (P := qLeft A)
      (fun x ↦ ordinaryPairQuotient_ind (P := qRight B)
        (fun y ↦ (congrArg (ordinaryPairQuotientProdToSmash A B)
          (((SmashProduct.lift_mk _ _ _ _ _ _).trans (prodQuotientFromBoth_π A B x _)).trans
            (prodQuotientFromRight_π A B x y))).trans (ordinaryPairQuotientProdToSmash_π A B x y))
        (by rw [SmashProduct.mk_basepoint_right]
            simpa [smashToOrdinaryPairQuotientProd] using
              ordinaryPairQuotientProdToSmash_basepoint A B))
      (fun _ ↦ by rw [SmashProduct.mk_basepoint_left]
                  simpa [smashToOrdinaryPairQuotientProd] using
                    ordinaryPairQuotientProdToSmash_basepoint A B)
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
  (ordinaryPairQuotientProdHomeomorph A B).symm_apply_eq.2
    (ordinaryPairQuotientProdHomeomorph_π A B x y).symm

@[simp]
lemma ordinaryPairQuotientProdHomeomorph_symm_basepoint [LocallyCompactSpace X]
    [LocallyCompactSpace (ofSubset (X := TopCat.of Y) B).ordinaryPairQuotient] :
    (ordinaryPairQuotientProdHomeomorph A B).symm (SmashProduct.basepoint _ _) =
      (ofSubset (X := TopCat.of (X × Y))
        (A ×ˢ univ ∪ univ ×ˢ B)).ordinaryPairQuotientBasepoint :=
  (ordinaryPairQuotientProdHomeomorph A B).symm_apply_eq.2
    (ordinaryPairQuotientProdHomeomorph_basepoint A B).symm

end ProdQuotient

end TopPair
