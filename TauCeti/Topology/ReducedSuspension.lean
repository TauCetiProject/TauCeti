/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.SmashProduct

import TauCeti.Topology.Category.TopPair

/-!
# The reduced suspension of a pointed topological space

For a pointed topological space `(X, x₀)`, the reduced suspension `ΣX` collapses the top and bottom
lids `X × {0, 1}` together with the basepoint fibre `{x₀} × I` inside `X × I` to a single
basepoint. Following the interval-last convention matching `X ∧ S¹`, the cylinder is `X × I` rather
than `I × X`.

Here `TauCeti.ReducedSuspension x₀` is constructed directly as `TopPair.ordinaryPairQuotient` of
`TauCeti.reducedSuspensionPair x₀` so pair-quotient homology and cohomology APIs apply without an
extra translation layer. Because `(x₀, 0)` belongs to the collapsed subspace, the quotient
projection `TauCeti.ReducedSuspension.mk x₀ : C(X × I, ReducedSuspension x₀)` is unconditionally a
surjective quotient map (`TauCeti.ReducedSuspension.isQuotientMap_mk`), and `ReducedSuspension x₀`
is unconditionally path-connected (`TauCeti.ReducedSuspension.instPathConnectedSpace`).

When `X` is locally compact, `TauCeti.ReducedSuspension.homeomorphSmashIntervalQuotient` identifies
`ΣX` with `X ∧ (I / {0, 1})`, sending `mk x₀ (x, t)` to `x ∧ π t` with the interval factor on the
right.

## Main declarations

* `TauCeti.intervalEndpointPair`: the pair `(ULift I, {0, 1})` whose pointed quotient is the circle
  model `I / ∂I`.
* `TauCeti.reducedSuspensionPair` and `TauCeti.ReducedSuspension`: the pair
  `(X × I, X × {0, 1} ∪ {x₀} × I)` and its pointed quotient `ΣX`.
* `TauCeti.ReducedSuspension.basepoint`, `TauCeti.ReducedSuspension.mk`,
  `TauCeti.ReducedSuspension.lift`, and `TauCeti.ReducedSuspension.hom_ext`: quotient map and
  universal property.
* `TauCeti.ReducedSuspension.map` and `TauCeti.ReducedSuspension.congrHomeomorph`: functoriality in
  pointed maps and pointed homeomorphisms.
* `TauCeti.ReducedSuspension.homeomorphSmashIntervalQuotient`: `ΣX ≃ₜ X ∧ (I / {0, 1})` for locally
  compact `X`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0,
  reduced suspension and its identification with `X ∧ S¹`.
* J. P. May, *A Concise Course in Algebraic Topology*, Section 8.2, reduced suspension and smash
  products.
-/

public section

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

universe u v

namespace TauCeti

/-- The unit interval `I` and its boundary `{0, 1}`, lifted to universe `u` as a `TopPair`. -/
abbrev intervalEndpointPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (ULift.{u} I)) (ULift.down ⁻¹' ({0, 1} : Set I))

instance instCompactSpaceIntervalEndpointPairQuotient :
    CompactSpace intervalEndpointPair.{u}.ordinaryPairQuotient :=
  haveI : CompactSpace intervalEndpointPair.{u}.fst := inferInstanceAs (CompactSpace (ULift.{u} I))
  intervalEndpointPair.{u}.compactSpace_ordinaryPairQuotient

instance instT2SpaceIntervalEndpointPairQuotient :
    T2Space intervalEndpointPair.{u}.ordinaryPairQuotient := by
  have : T3Space intervalEndpointPair.{u}.fst := inferInstanceAs (T3Space (ULift.{u} I))
  refine intervalEndpointPair.{u}.t2Space_ordinaryPairQuotient_of_isClosed ?_
  rw [TopPair.range_ofSubset_map]
  exact (isClosed_singleton.union isClosed_singleton).preimage continuous_uliftDown

section Pair

variable {X : Type u} [TopologicalSpace X]

/-- The topological pair `(X × I, X × {0, 1} ∪ {x₀} × I)` whose pointed quotient is the reduced
suspension of `(X, x₀)`. -/
abbrev reducedSuspensionPair (x₀ : X) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (X × I)) (univ ×ˢ ({0, 1} : Set I) ∪ {x₀} ×ˢ univ)

/-- A point `(x, t)` lies in the subspace of `TauCeti.reducedSuspensionPair x₀` exactly when
`x = x₀`, `t = 0`, or `t = 1`. -/
lemma mem_range_reducedSuspensionPair_map_iff {x₀ : X} {p : X × I} :
    (p : (reducedSuspensionPair x₀).fst) ∈ range (reducedSuspensionPair x₀).map ↔
      p.1 = x₀ ∨ p.2 = 0 ∨ p.2 = 1 :=
  (Eq.to_iff (congrArg (p ∈ ·) TopPair.range_ofSubset_map)).trans
    ⟨fun h ↦ h.elim (fun ⟨_, ht⟩ ↦ Or.inr ht) fun ⟨hx, _⟩ ↦ Or.inl hx,
     fun h ↦ h.elim (fun hx ↦ Or.inr ⟨hx, trivial⟩) fun ht ↦ Or.inl ⟨trivial, ht⟩⟩

instance instNonemptyReducedSuspensionPairSnd (x₀ : X) :
    Nonempty (reducedSuspensionPair x₀).snd :=
  ⟨⟨(x₀, 0), Or.inl ⟨trivial, Or.inl rfl⟩⟩⟩

/-- **The reduced suspension `ΣX`** of a pointed space `(X, x₀)`, with the interval coordinate
placed last: `TopPair.ordinaryPairQuotient` of `TauCeti.reducedSuspensionPair x₀`. -/
def ReducedSuspension (x₀ : X) : TopCat.{u} :=
  (reducedSuspensionPair x₀).ordinaryPairQuotient

lemma reducedSuspensionPair_ordinaryPairQuotient (x₀ : X) :
    (reducedSuspensionPair x₀).ordinaryPairQuotient = ReducedSuspension x₀ := (rfl)

end Pair

namespace ReducedSuspension

section Basic

variable {X : Type u} [TopologicalSpace X] (x₀ : X)

/-- The basepoint of `ΣX`, the collapsed image of `X × {0, 1} ∪ {x₀} × I`. -/
def basepoint : ReducedSuspension x₀ :=
  (reducedSuspensionPair x₀).ordinaryPairQuotientBasepoint

instance : Inhabited (ReducedSuspension x₀) :=
  ⟨basepoint x₀⟩

/-- The quotient map `X × I → ΣX`. -/
def mk : C(X × I, ReducedSuspension x₀) :=
  ((reducedSuspensionPair x₀).ordinaryPairQuotientπ).hom

variable {x₀}

/-- A point `(x, t)` maps to the basepoint of `ΣX` exactly when `x = x₀`, `t = 0`, or `t = 1`. -/
@[simp]
lemma mk_eq_basepoint_iff {x : X} {t : I} :
    mk x₀ (x, t) = basepoint x₀ ↔ x = x₀ ∨ t = 0 ∨ t = 1 :=
  ((reducedSuspensionPair x₀).ordinaryPairQuotientπ_eq_basepoint_iff (x, t)).trans
    (mem_range_reducedSuspensionPair_map_iff (p := (x, t)))

@[simp]
lemma mk_basepoint (t : I) : mk x₀ (x₀, t) = basepoint x₀ :=
  mk_eq_basepoint_iff.2 (Or.inl rfl)

@[simp]
lemma mk_zero (x : X) : mk x₀ (x, 0) = basepoint x₀ :=
  mk_eq_basepoint_iff.2 (Or.inr (Or.inl rfl))

@[simp]
lemma mk_one (x : X) : mk x₀ (x, 1) = basepoint x₀ :=
  mk_eq_basepoint_iff.2 (Or.inr (Or.inr rfl))

/-- Two points of `X × I` become equal in `ΣX` exactly when they coincide or both lie in
`X × {0, 1} ∪ {x₀} × I`. -/
lemma mk_eq_mk_iff {x x' : X} {t t' : I} :
    mk x₀ (x, t) = mk x₀ (x', t') ↔
      (x = x' ∧ t = t') ∨
        (x = x₀ ∨ t = 0 ∨ t = 1) ∧ (x' = x₀ ∨ t' = 0 ∨ t' = 1) := by
  refine ((reducedSuspensionPair x₀).ordinaryPairQuotientπ_eq_iff (x, t) (x', t')).trans ?_
  refine or_congr ⟨fun h ↦ Prod.mk.inj h, fun ⟨h₁, h₂⟩ ↦ Prod.ext h₁ h₂⟩ ?_
  exact and_congr (mem_range_reducedSuspensionPair_map_iff (p := (x, t)))
    (mem_range_reducedSuspensionPair_map_iff (p := (x', t')))

variable (x₀) in
/-- The projection `X × I → ΣX` is unconditionally surjective. -/
lemma surjective_mk : Function.Surjective (mk x₀) :=
  (reducedSuspensionPair x₀).surjective_ordinaryPairQuotientπ

variable (x₀) in
/-- **The projection `X × I → ΣX` is unconditionally a quotient map.** -/
lemma isQuotientMap_mk : IsQuotientMap (mk x₀) :=
  (reducedSuspensionPair x₀).isQuotientMap_ordinaryPairQuotientπ

/-- Induction principle for `ΣX`: every point is of the form `mk x₀ (x, t)`. -/
@[elab_as_elim]
lemma ind {motive : ReducedSuspension x₀ → Prop}
    (hmk : ∀ x t, motive (mk x₀ (x, t))) (z : ReducedSuspension x₀) : motive z := by
  obtain ⟨⟨x, t⟩, rfl⟩ := surjective_mk x₀ z
  exact hmk x t

lemma isOpen_iff {s : Set (ReducedSuspension x₀)} :
    IsOpen s ↔ IsOpen (mk x₀ ⁻¹' s) :=
  (reducedSuspensionPair x₀).isOpen_ordinaryPairQuotient_iff

lemma isClosed_iff {s : Set (ReducedSuspension x₀)} :
    IsClosed s ↔ IsClosed (mk x₀ ⁻¹' s) :=
  (reducedSuspensionPair x₀).isClosed_ordinaryPairQuotient_iff

/-- **Extensionality for continuous maps out of `ΣX`.** -/
@[ext]
lemma hom_ext {Z : Type v} [TopologicalSpace Z] {f g : C(ReducedSuspension x₀, Z)}
    (h : ∀ x t, f (mk x₀ (x, t)) = g (mk x₀ (x, t))) : f = g := by
  ext z
  induction z using ind with
  | hmk x t => exact h x t

private lemma factorsThrough_mk {Z : Type v} {f : X × I → Z} (z₀ : Z)
    (hx₀ : ∀ t, f (x₀, t) = z₀) (h0 : ∀ x, f (x, 0) = z₀) (h1 : ∀ x, f (x, 1) = z₀) :
    Function.FactorsThrough f (mk x₀) := by
  rintro ⟨x₁, t₁⟩ ⟨x₂, t₂⟩ h
  rcases mk_eq_mk_iff.1 h with ⟨rfl, rfl⟩ | ⟨h₁', h₂'⟩
  · rfl
  · have eq₁ : f (x₁, t₁) = z₀ := by
      rcases h₁' with rfl | rfl | rfl
      exacts [hx₀ t₁, h0 x₁, h1 x₁]
    have eq₂ : f (x₂, t₂) = z₀ := by
      rcases h₂' with rfl | rfl | rfl
      exacts [hx₀ t₂, h0 x₂, h1 x₂]
    exact eq₁.trans eq₂.symm

/-- **The universal property of the reduced suspension.** A continuous map `f : C(X × I, Z)`
sending `{x₀} × I`, `X × {0}`, and `X × {1}` to `z₀` descends to `C(ReducedSuspension x₀, Z)`. -/
def lift {Z : Type v} [TopologicalSpace Z] (f : C(X × I, Z)) (z₀ : Z)
    (hx₀ : ∀ t, f (x₀, t) = z₀) (h0 : ∀ x, f (x, 0) = z₀) (h1 : ∀ x, f (x, 1) = z₀) :
    C(ReducedSuspension x₀, Z) :=
  (isQuotientMap_mk x₀).lift f (factorsThrough_mk z₀ hx₀ h0 h1)

@[simp]
lemma lift_mk {Z : Type v} [TopologicalSpace Z] (f : C(X × I, Z)) (z₀ : Z)
    (hx₀ : ∀ t, f (x₀, t) = z₀) (h0 : ∀ x, f (x, 0) = z₀) (h1 : ∀ x, f (x, 1) = z₀)
    (x : X) (t : I) :
    lift f z₀ hx₀ h0 h1 (mk x₀ (x, t)) = f (x, t) :=
  DFunLike.congr_fun ((isQuotientMap_mk x₀).lift_comp f (factorsThrough_mk z₀ hx₀ h0 h1)) (x, t)

@[simp]
lemma lift_comp_mk {Z : Type v} [TopologicalSpace Z] (f : C(X × I, Z)) (z₀ : Z)
    (hx₀ : ∀ t, f (x₀, t) = z₀) (h0 : ∀ x, f (x, 0) = z₀) (h1 : ∀ x, f (x, 1) = z₀) :
    (lift f z₀ hx₀ h0 h1).comp (mk x₀) = f := by
  ext ⟨x, t⟩
  exact lift_mk f z₀ hx₀ h0 h1 x t

@[simp]
lemma lift_basepoint {Z : Type v} [TopologicalSpace Z] (f : C(X × I, Z)) (z₀ : Z)
    (hx₀ : ∀ t, f (x₀, t) = z₀) (h0 : ∀ x, f (x, 0) = z₀) (h1 : ∀ x, f (x, 1) = z₀) :
    lift f z₀ hx₀ h0 h1 (basepoint x₀) = z₀ := by
  rw [← mk_zero x₀, lift_mk, h0]

/-! ### Topological properties -/

instance [CompactSpace X] : CompactSpace (ReducedSuspension x₀) :=
  haveI : CompactSpace (reducedSuspensionPair x₀).fst := inferInstanceAs (CompactSpace (X × I))
  (reducedSuspensionPair x₀).compactSpace_ordinaryPairQuotient

instance [T3Space X] : T2Space (ReducedSuspension x₀) := by
  have : T3Space (reducedSuspensionPair x₀).fst := inferInstanceAs (T3Space (X × I))
  refine (reducedSuspensionPair x₀).t2Space_ordinaryPairQuotient_of_isClosed ?_
  rw [TopPair.range_ofSubset_map]
  exact (isClosed_univ.prod (isClosed_singleton.union isClosed_singleton)).union
    (isClosed_singleton.prod isClosed_univ)

instance [Subsingleton X] : Subsingleton (ReducedSuspension x₀) := by
  refine ⟨fun z₁ z₂ ↦ ?_⟩
  have hbase (z : ReducedSuspension x₀) : z = basepoint x₀ := by
    induction z using ind with
    | hmk x t => rw [Subsingleton.elim x x₀, mk_basepoint]
  exact (hbase z₁).trans (hbase z₂).symm

/-- **Every reduced suspension is path-connected**, without any connectedness assumption on `X`:
each point `mk x₀ (x, t)` is joined to `mk x₀ (x, 0) = basepoint x₀` along `{x} × I`. -/
instance instPathConnectedSpace : PathConnectedSpace (ReducedSuspension x₀) where
  nonempty := ⟨basepoint x₀⟩
  joined := by
    have hbase (z : ReducedSuspension x₀) : Joined (basepoint x₀) z := by
      induction z using ind with
      | hmk x t =>
        refine ⟨{
          toFun := fun s ↦ mk x₀ (x, ⟨(s : ℝ) * (t : ℝ), unitInterval.mul_mem s.2 t.2⟩)
          continuous_toFun := (mk x₀).continuous.comp <|
            continuous_const.prodMk ((continuous_subtype_val.mul continuous_const).subtype_mk _)
          source' := ?_
          target' := ?_ }⟩
        · have h0 : (⟨(0 : I) * (t : ℝ), unitInterval.mul_mem (0 : I).2 t.2⟩ : I) = 0 :=
            Subtype.ext (zero_mul _)
          exact (congrArg (fun u ↦ mk x₀ (x, u)) h0).trans (mk_zero x)
        · have h1 : (⟨(1 : I) * (t : ℝ), unitInterval.mul_mem (1 : I).2 t.2⟩ : I) = t :=
            Subtype.ext (one_mul _)
          exact congrArg (fun u ↦ mk x₀ (x, u)) h1
    exact fun z₁ z₂ ↦ (hbase z₁).symm.trans (hbase z₂)

end Basic

/-! ### Functoriality and smash-product comparison -/

section Functoriality

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x₀ : X} {y₀ : Y} {z₀ : Z}

/-- The pointed map `ΣX → ΣY` induced by a pointed continuous map `f : (X, x₀) → (Y, y₀)`. -/
def map (f : C(X, Y)) (hf : f x₀ = y₀) : C(ReducedSuspension x₀, ReducedSuspension y₀) :=
  lift ((mk y₀).comp (f.prodMap (ContinuousMap.id I))) (basepoint y₀)
    (fun t ↦ by simp [hf]) (fun x ↦ by simp) (fun x ↦ by simp)

@[simp]
lemma map_mk (f : C(X, Y)) (hf : f x₀ = y₀) (x : X) (t : I) :
    map f hf (mk x₀ (x, t)) = mk y₀ (f x, t) :=
  lift_mk _ _ _ _ _ x t

@[simp]
lemma map_basepoint (f : C(X, Y)) (hf : f x₀ = y₀) :
    map f hf (basepoint x₀) = basepoint y₀ :=
  lift_basepoint _ _ _ _ _

@[simp]
lemma map_id (x₀ : X) :
    map (x₀ := x₀) (y₀ := x₀) (ContinuousMap.id X) rfl =
      ContinuousMap.id (ReducedSuspension x₀) := by
  apply hom_ext
  intro x t
  exact map_mk _ _ x t

lemma map_comp (f : C(X, Y)) (hf : f x₀ = y₀) (g : C(Y, Z)) (hg : g y₀ = z₀) :
    (map g hg).comp (map f hf) = map (g.comp f) (by simp [hf, hg]) := by
  apply hom_ext
  intro x t
  simp

/-- A pointed homeomorphism `X ≃ₜ Y` induces a homeomorphism `ΣX ≃ₜ ΣY`. -/
def congrHomeomorph (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    ReducedSuspension x₀ ≃ₜ ReducedSuspension y₀ where
  toFun := map (e : C(X, Y)) he
  invFun := map (e.symm : C(Y, X)) (e.symm_apply_eq.2 he.symm)
  left_inv z := by
    induction z using ind with
    | hmk x t => simp
  right_inv z' := by
    induction z' using ind with
    | hmk y t => simp
  continuous_toFun := (map (e : C(X, Y)) he).continuous
  continuous_invFun := (map (e.symm : C(Y, X)) (e.symm_apply_eq.2 he.symm)).continuous

@[simp]
lemma congrHomeomorph_mk (e : X ≃ₜ Y) (he : e x₀ = y₀) (x : X) (t : I) :
    congrHomeomorph e he (mk x₀ (x, t)) = mk y₀ (e x, t) := by
  simp [congrHomeomorph]

@[simp]
lemma congrHomeomorph_basepoint (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    congrHomeomorph e he (basepoint x₀) = basepoint y₀ := by
  simp [congrHomeomorph]

@[simp]
lemma congrHomeomorph_symm (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    (congrHomeomorph e he).symm = congrHomeomorph e.symm (e.symm_apply_eq.2 he.symm) := (rfl)

end Functoriality

section SmashComparison

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] (x₀ : X)

private def pairIsoProdULift :
    reducedSuspensionPair x₀ ≅
      TopPair.ofSubset (X := TopCat.of (X × ULift.{u} I))
        (({x₀} : Set X) ×ˢ univ ∪ univ ×ˢ (ULift.down ⁻¹' ({0, 1} : Set I))) :=
  TopPair.ofSubsetIso
    (X := TopCat.of (X × I)) (Y := TopCat.of (X × ULift.{u} I))
    ((Homeomorph.refl X).prodCongr Homeomorph.ulift.{u}.symm)
    fun _ ↦
      ⟨fun h ↦ h.elim (fun ⟨_, ht⟩ ↦ Or.inr ⟨trivial, ht⟩) fun ⟨hx, _⟩ ↦ Or.inl ⟨hx, trivial⟩,
       fun h ↦ h.elim (fun ⟨hx, _⟩ ↦ Or.inr ⟨hx, trivial⟩) fun ⟨_, ht⟩ ↦ Or.inl ⟨trivial, ht⟩⟩

/-- **The reduced suspension is the smash product with `I / {0, 1}`** when `X` is locally compact:
`ΣX ≃ₜ X ∧ (I / {0, 1})`, with the interval factor on the right. -/
def homeomorphSmashIntervalQuotient :
    ReducedSuspension x₀ ≃ₜ
      SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint :=
  (TopPair.ordinaryPairQuotientHomeomorph (pairIsoProdULift x₀)).trans <|
    (TopPair.ordinaryPairQuotientProdHomeomorph ({x₀} : Set X)
      (ULift.down ⁻¹' ({0, 1} : Set I))).trans <|
      SmashProduct.congrHomeomorph
        (TopPair.ordinaryPairQuotientSingletonHomeomorph (X := TopCat.of X) x₀)
        (Homeomorph.refl _)
        (TopPair.ordinaryPairQuotientSingletonHomeomorph_basepoint (X := TopCat.of X) x₀)
        (congrFun (Homeomorph.refl_apply _) _)

@[simp]
lemma homeomorphSmashIntervalQuotient_mk (x : X) (t : I) :
    homeomorphSmashIntervalQuotient x₀ (mk x₀ (x, t)) =
      SmashProduct.mk x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint
        (x, intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)) := by
  let e₁ := TopPair.ordinaryPairQuotientHomeomorph (pairIsoProdULift x₀)
  let e₂ := TopPair.ordinaryPairQuotientProdHomeomorph ({x₀} : Set X)
    (ULift.down ⁻¹' ({0, 1} : Set I))
  let e₃ := SmashProduct.congrHomeomorph
    (TopPair.ordinaryPairQuotientSingletonHomeomorph (X := TopCat.of X) x₀)
    (Homeomorph.refl intervalEndpointPair.{u}.ordinaryPairQuotient)
    (TopPair.ordinaryPairQuotientSingletonHomeomorph_basepoint (X := TopCat.of X) x₀)
    (congrFun (Homeomorph.refl_apply _) intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint)
  have h₁ : e₁ (mk x₀ (x, t)) =
      (TopPair.ofSubset (X := TopCat.of (X × ULift.{u} I))
        (({x₀} : Set X) ×ˢ univ ∪
          univ ×ˢ (ULift.down ⁻¹' ({0, 1} : Set I)))).ordinaryPairQuotientπ
        (x, ULift.up t) := by
    refine (TopPair.ordinaryPairQuotientHomeomorph_π (pairIsoProdULift x₀) (x, t)).trans ?_
    refine congrArg
      (TopPair.ofSubset (X := TopCat.of (X × ULift.{u} I))
        (({x₀} : Set X) ×ˢ univ ∪
          univ ×ˢ (ULift.down ⁻¹' ({0, 1} : Set I)))).ordinaryPairQuotientπ ?_
    exact (congrArg (fun f : reducedSuspensionPair x₀ ⟶ _ ↦ TopPair.Hom.fst f (x, t))
      (TopPair.ofSubsetIso_hom _ _)).trans
      (congrArg (fun g : TopCat.of (X × I) ⟶ _ ↦ g (x, t)) (TopPair.ofSubsetMap_fst _ _))
  calc e₃ (e₂ (e₁ (mk x₀ (x, t))))
    _ = e₃ (e₂ ((TopPair.ofSubset (X := TopCat.of (X × ULift.{u} I))
          (({x₀} : Set X) ×ˢ univ ∪
            univ ×ˢ (ULift.down ⁻¹' ({0, 1} : Set I)))).ordinaryPairQuotientπ
          (x, ULift.up t))) :=
        congrArg (fun z ↦ e₃ (e₂ z)) h₁
    _ = e₃ (SmashProduct.mk _ _
          ((TopPair.ofSubset (X := TopCat.of X) ({x₀} : Set X)).ordinaryPairQuotientπ x,
            intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t))) :=
        congrArg e₃ (TopPair.ordinaryPairQuotientProdHomeomorph_π _ _ x (ULift.up t))
    _ = _ := by
        rw [SmashProduct.congrHomeomorph_mk]
        exact congrArg (fun a ↦ SmashProduct.mk _ _ (a, _))
          (TopPair.ordinaryPairQuotientSingletonHomeomorph_π (X := TopCat.of X) x₀ x)

@[simp]
lemma homeomorphSmashIntervalQuotient_basepoint :
    homeomorphSmashIntervalQuotient x₀ (basepoint x₀) =
      SmashProduct.basepoint x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint := by
  let e₁ := TopPair.ordinaryPairQuotientHomeomorph (pairIsoProdULift x₀)
  let e₂ := TopPair.ordinaryPairQuotientProdHomeomorph ({x₀} : Set X)
    (ULift.down ⁻¹' ({0, 1} : Set I))
  let e₃ := SmashProduct.congrHomeomorph
    (TopPair.ordinaryPairQuotientSingletonHomeomorph (X := TopCat.of X) x₀)
    (Homeomorph.refl intervalEndpointPair.{u}.ordinaryPairQuotient)
    (TopPair.ordinaryPairQuotientSingletonHomeomorph_basepoint (X := TopCat.of X) x₀)
    (congrFun (Homeomorph.refl_apply _) intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint)
  calc e₃ (e₂ (e₁ (basepoint x₀)))
    _ = e₃ (e₂ ((TopPair.ofSubset (X := TopCat.of (X × ULift.{u} I))
          (({x₀} : Set X) ×ˢ univ ∪
            univ ×ˢ (ULift.down ⁻¹' ({0, 1} : Set I)))).ordinaryPairQuotientBasepoint)) :=
        congrArg (fun z ↦ e₃ (e₂ z))
          (TopPair.ordinaryPairQuotientHomeomorph_basepoint (pairIsoProdULift x₀))
    _ = e₃ (SmashProduct.basepoint _ _) :=
        congrArg e₃ (TopPair.ordinaryPairQuotientProdHomeomorph_basepoint _ _)
    _ = _ := SmashProduct.congrHomeomorph_basepoint _ _ _ _

@[simp]
lemma homeomorphSmashIntervalQuotient_symm_mk_π (x : X) (t : I) :
    (homeomorphSmashIntervalQuotient x₀).symm
      (SmashProduct.mk x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint
        (x, intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t))) =
      mk x₀ (x, t) :=
  (homeomorphSmashIntervalQuotient x₀).symm_apply_eq.2
    (homeomorphSmashIntervalQuotient_mk x₀ x t).symm

@[simp]
lemma homeomorphSmashIntervalQuotient_symm_basepoint :
    (homeomorphSmashIntervalQuotient x₀).symm
      (SmashProduct.basepoint x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint) =
      basepoint x₀ :=
  (homeomorphSmashIntervalQuotient x₀).symm_apply_eq.2
    (homeomorphSmashIntervalQuotient_basepoint x₀).symm

end SmashComparison

end ReducedSuspension

end TauCeti

end
