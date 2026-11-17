/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.SmashProduct
import Mathlib.Topology.Maps.Proper.Basic
import TauCeti.Topology.Category.TopPair

/-!
# The reduced suspension of a pointed topological space

For a pointed topological space `(X, x₀)`, the reduced suspension `ΣX` collapses `X × {0, 1}` and
`{x₀} × I` inside `X × I` to a single basepoint, with the interval coordinate placed last to match
`X ∧ S¹`. Here `TauCeti.ReducedSuspension x₀` is constructed directly as
`TopPair.ordinaryPairQuotient` of `TauCeti.reducedSuspensionPair x₀`, so the quotient projection
`TauCeti.ReducedSuspension.mk` is unconditionally a surjective quotient map and
`ReducedSuspension x₀` is unconditionally path-connected. For every pointed topological space `X`,
`TauCeti.ReducedSuspension.homeomorphSmashIntervalQuotient` identifies `ΣX` with `X ∧ (I / {0, 1})`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0.
* J. P. May, *A Concise Course in Algebraic Topology*, Section 8.2.
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
    ⟨fun h ↦ h.elim (Or.inr ∘ And.right) (Or.inl ∘ And.left),
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

instance : Inhabited (ReducedSuspension x₀) := ⟨basepoint x₀⟩

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
lemma mk_basepoint (t : I) : mk x₀ (x₀, t) = basepoint x₀ := mk_eq_basepoint_iff.2 (Or.inl rfl)

@[simp]
lemma mk_zero (x : X) : mk x₀ (x, 0) = basepoint x₀ := mk_eq_basepoint_iff.2 (Or.inr (Or.inl rfl))

@[simp]
lemma mk_one (x : X) : mk x₀ (x, 1) = basepoint x₀ := mk_eq_basepoint_iff.2 (Or.inr (Or.inr rfl))

/-- Two points of `X × I` become equal in `ΣX` exactly when they coincide or both lie in
`X × {0, 1} ∪ {x₀} × I`. -/
lemma mk_eq_mk_iff {x x' : X} {t t' : I} :
    mk x₀ (x, t) = mk x₀ (x', t') ↔
      (x = x' ∧ t = t') ∨ (x = x₀ ∨ t = 0 ∨ t = 1) ∧ (x' = x₀ ∨ t' = 0 ∨ t' = 1) :=
  ((reducedSuspensionPair x₀).ordinaryPairQuotientπ_eq_iff (x, t) (x', t')).trans <|
    or_congr ⟨Prod.mk.inj, fun ⟨h₁, h₂⟩ ↦ Prod.ext h₁ h₂⟩
      (and_congr (mem_range_reducedSuspensionPair_map_iff (p := (x, t)))
        (mem_range_reducedSuspensionPair_map_iff (p := (x', t'))))

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
    (hmk : ∀ x t, motive (mk x₀ (x, t))) (z : ReducedSuspension x₀) : motive z :=
  let ⟨⟨x, t⟩, h⟩ := surjective_mk x₀ z; h ▸ hmk x t

lemma isOpen_iff {s : Set (ReducedSuspension x₀)} : IsOpen s ↔ IsOpen (mk x₀ ⁻¹' s) :=
  (reducedSuspensionPair x₀).isOpen_ordinaryPairQuotient_iff

lemma isClosed_iff {s : Set (ReducedSuspension x₀)} : IsClosed s ↔ IsClosed (mk x₀ ⁻¹' s) :=
  (reducedSuspensionPair x₀).isClosed_ordinaryPairQuotient_iff

/-- **Extensionality for continuous maps out of `ΣX`.** -/
@[ext]
lemma hom_ext {Z : Type v} [TopologicalSpace Z] {f g : C(ReducedSuspension x₀, Z)}
    (h : ∀ x t, f (mk x₀ (x, t)) = g (mk x₀ (x, t))) : f = g :=
  DFunLike.ext _ _ (ind h)

private lemma factorsThrough_mk {Z : Type v} {f : X × I → Z} (z₀ : Z)
    (hx₀ : ∀ t, f (x₀, t) = z₀) (h0 : ∀ x, f (x, 0) = z₀) (h1 : ∀ x, f (x, 1) = z₀) :
    Function.FactorsThrough f (mk x₀) := fun ⟨_, _⟩ ⟨_, _⟩ h ↦
  (mk_eq_mk_iff.1 h).elim (fun ⟨hx, ht⟩ ↦ hx ▸ ht ▸ rfl) fun ⟨h₁', h₂'⟩ ↦
    have val {x t} (ht : x = x₀ ∨ t = 0 ∨ t = 1) : f (x, t) = z₀ :=
      ht.elim (· ▸ hx₀ t) fun ht ↦ ht.elim (· ▸ h0 x) (· ▸ h1 x)
    (val h₁').trans (val h₂').symm

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
    (lift f z₀ hx₀ h0 h1).comp (mk x₀) = f :=
  DFunLike.ext _ _ fun ⟨x, t⟩ ↦ lift_mk f z₀ hx₀ h0 h1 x t

@[simp]
lemma lift_basepoint {Z : Type v} [TopologicalSpace Z] (f : C(X × I, Z)) (z₀ : Z)
    (hx₀ : ∀ t, f (x₀, t) = z₀) (h0 : ∀ x, f (x, 0) = z₀) (h1 : ∀ x, f (x, 1) = z₀) :
    lift f z₀ hx₀ h0 h1 (basepoint x₀) = z₀ := by
  rw [← mk_zero x₀, lift_mk, h0]

instance [CompactSpace X] : CompactSpace (ReducedSuspension x₀) :=
  haveI : CompactSpace (reducedSuspensionPair x₀).fst := inferInstanceAs (CompactSpace (X × I))
  (reducedSuspensionPair x₀).compactSpace_ordinaryPairQuotient

instance [T2Space X] : T2Space (ReducedSuspension x₀) := by
  have : T2Space (reducedSuspensionPair x₀).fst := inferInstanceAs (T2Space (X × I))
  refine (reducedSuspensionPair x₀).t2Space_ordinaryPairQuotient_of_disjoint_nhdsSet
    fun ⟨x, t⟩ h ↦ ?_
  rw [TopPair.range_ofSubset_map] at h ⊢
  exact show Disjoint (𝓝ˢ (univ ×ˢ ({0, 1} : Set I) ∪ {x₀} ×ˢ univ : Set (X × I))) (𝓝 (x, t)) by
    rw [nhdsSet_union, disjoint_sup_left, nhds_prod_eq]
    exact ⟨(Filter.disjoint_prod.2 <| Or.inr <| (Set.toFinite _).isCompact.disjoint_nhdsSet_nhds
        fun ht ↦ h (Or.inl ⟨trivial, ht⟩)).mono_left (nhdsSet_prod_le _ _),
      (Filter.disjoint_prod.2 <| Or.inl <| isCompact_singleton.disjoint_nhdsSet_nhds
        fun hx ↦ h (Or.inr ⟨hx, trivial⟩)).mono_left (nhdsSet_prod_le _ _)⟩

instance [Subsingleton X] : Subsingleton (ReducedSuspension x₀) :=
  subsingleton_of_forall_eq (basepoint x₀)
    (ind fun x t ↦ Subsingleton.elim x x₀ ▸ mk_basepoint t)

/-- **Every reduced suspension is path-connected**, without any connectedness assumption on `X`:
each point `mk x₀ (x, t)` is joined to `mk x₀ (x, 0) = basepoint x₀` along `{x} × I`. -/
instance instPathConnectedSpace : PathConnectedSpace (ReducedSuspension x₀) where
  nonempty := ⟨basepoint x₀⟩
  joined :=
    have hbase : ∀ z, Joined (basepoint x₀) z := ind fun x t ↦ ⟨{
      toFun := fun s ↦ mk x₀ (x, ⟨(s : ℝ) * t, unitInterval.mul_mem s.2 t.2⟩)
      continuous_toFun := (mk x₀).continuous.comp <|
        continuous_const.prodMk ((continuous_subtype_val.mul continuous_const).subtype_mk _)
      source' := (congrArg (fun u ↦ mk x₀ (x, u)) (Subtype.ext (zero_mul _))).trans (mk_zero x)
      target' := congrArg (fun u ↦ mk x₀ (x, u)) (Subtype.ext (one_mul _)) }⟩
    fun z₁ z₂ ↦ (hbase z₁).symm.trans (hbase z₂)

end Basic

section Functoriality

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x₀ : X} {y₀ : Y} {z₀ : Z}

/-- The pointed map `ΣX → ΣY` induced by a pointed continuous map `f : (X, x₀) → (Y, y₀)`. -/
def map (f : C(X, Y)) (hf : f x₀ = y₀) : C(ReducedSuspension x₀, ReducedSuspension y₀) :=
  lift ((mk y₀).comp (f.prodMap (ContinuousMap.id I))) (basepoint y₀)
    (fun _ ↦ by simp [hf]) (by simp) (by simp)

@[simp]
lemma map_mk (f : C(X, Y)) (hf : f x₀ = y₀) (x : X) (t : I) :
    map f hf (mk x₀ (x, t)) = mk y₀ (f x, t) := lift_mk _ _ _ _ _ x t

@[simp]
lemma map_basepoint (f : C(X, Y)) (hf : f x₀ = y₀) :
    map f hf (basepoint x₀) = basepoint y₀ := lift_basepoint _ _ _ _ _

@[simp]
lemma map_id (x₀ : X) :
    map (x₀ := x₀) (y₀ := x₀) (ContinuousMap.id X) rfl =
      ContinuousMap.id (ReducedSuspension x₀) :=
  hom_ext fun x t ↦ map_mk _ _ x t

lemma map_comp (f : C(X, Y)) (hf : f x₀ = y₀) (g : C(Y, Z)) (hg : g y₀ = z₀) :
    (map g hg).comp (map f hf) = map (g.comp f) (by simp [hf, hg]) :=
  hom_ext fun x t ↦ by simp

/-- A pointed homeomorphism `X ≃ₜ Y` induces a homeomorphism `ΣX ≃ₜ ΣY`. -/
def congrHomeomorph (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    ReducedSuspension x₀ ≃ₜ ReducedSuspension y₀ where
  toFun := map (e : C(X, Y)) he
  invFun := map (e.symm : C(Y, X)) (e.symm_apply_eq.2 he.symm)
  left_inv := ind fun x t ↦ by simp
  right_inv := ind fun y t ↦ by simp
  continuous_toFun := (map (e : C(X, Y)) he).continuous
  continuous_invFun := (map (e.symm : C(Y, X)) (e.symm_apply_eq.2 he.symm)).continuous

@[simp]
lemma congrHomeomorph_mk (e : X ≃ₜ Y) (he : e x₀ = y₀) (x : X) (t : I) :
    congrHomeomorph e he (mk x₀ (x, t)) = mk y₀ (e x, t) := by simp [congrHomeomorph]

@[simp]
lemma congrHomeomorph_basepoint (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    congrHomeomorph e he (basepoint x₀) = basepoint y₀ := by simp [congrHomeomorph]

@[simp]
lemma congrHomeomorph_symm (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    (congrHomeomorph e he).symm = congrHomeomorph e.symm (e.symm_apply_eq.2 he.symm) := (rfl)

end Functoriality

section SmashComparison

variable {X : Type u} [TopologicalSpace X] (x₀ : X)

private def intervalπ : C(I, intervalEndpointPair.{u}.ordinaryPairQuotient) :=
  ⟨fun t ↦ intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t),
    intervalEndpointPair.{u}.ordinaryPairQuotientπ.hom.continuous.comp continuous_uliftUp⟩

private lemma isQuotientMap_id_prodMap_intervalπ :
    IsQuotientMap ((ContinuousMap.id X).prodMap intervalπ.{u}) :=
  haveI : Nonempty intervalEndpointPair.{u}.snd := ⟨⟨ULift.up 0, Or.inl rfl⟩⟩
  (isProperMap_id.prodMap intervalπ.{u}.continuous.isProperMap).isClosedMap.isQuotientMap
    ((ContinuousMap.id X).prodMap intervalπ.{u}).continuous <| Function.surjective_id.prodMap <|
      intervalEndpointPair.{u}.surjective_ordinaryPairQuotientπ.comp Equiv.ulift.symm.surjective

/-- **The reduced suspension is the smash product with `I / {0, 1}`** for every pointed
topological space `(X, x₀)`: `ΣX ≃ₜ X ∧ (I / {0, 1})`, with the interval factor on the right. -/
def homeomorphSmashIntervalQuotient :
    ReducedSuspension x₀ ≃ₜ
      SmashProduct x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint :=
  let q := (ContinuousMap.id X).prodMap intervalπ.{u}
  have hπ {t : I} (ht : t = 0 ∨ t = 1) : intervalπ.{u} t = _ :=
    intervalEndpointPair.{u}.ordinaryPairQuotientπ_map ⟨ULift.up t, ht⟩
  have hq : IsQuotientMap q := isQuotientMap_id_prodMap_intervalπ (X := X)
  have hsurj : Function.Surjective intervalπ.{u} := fun z ↦
    let ⟨⟨_, t⟩, h⟩ := hq.surjective (x₀, z); ⟨t, (Prod.mk.inj h).2⟩
  let fwd := lift ((SmashProduct.mk x₀ _).comp q) (SmashProduct.basepoint _ _) (fun _ ↦ by simp [q])
    (fun _ ↦ by simp [q, hπ (Or.inl rfl)]) (fun _ ↦ by simp [q, hπ (Or.inr rfl)])
  have hfact : Function.FactorsThrough (mk x₀) q := fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by
    obtain ⟨rfl, ht⟩ := Prod.mk.inj h
    rcases (intervalEndpointPair.{u}.ordinaryPairQuotientπ_eq_iff _ _).1 ht with h' | ⟨h₁, h₂⟩
    · cases congrArg ULift.down h'; rfl
    · rw [TopPair.range_ofSubset_map] at h₁ h₂
      exact mk_eq_mk_iff.2 (Or.inr ⟨Or.inr h₁, Or.inr h₂⟩)
  let g := hq.lift (mk x₀) hfact
  have hg (x : X) (t : I) : g (x, intervalπ.{u} t) = mk x₀ (x, t) :=
    DFunLike.congr_fun (hq.lift_comp (mk x₀) hfact) (x, t)
  let inv := SmashProduct.lift g (basepoint x₀)
    (fun z ↦ let ⟨t, ht⟩ := hsurj z; ht ▸ (hg x₀ t).trans (mk_basepoint t))
    (fun x ↦ hπ (Or.inl rfl) ▸ (hg x 0).trans (mk_zero x))
  { toFun := fwd, invFun := inv
    left_inv := ind fun x t ↦ by simp [fwd, inv, q, hg]
    right_inv := SmashProduct.ind fun x z ↦ by obtain ⟨t, rfl⟩ := hsurj z; simp [fwd, inv, q, hg]
    continuous_toFun := fwd.continuous, continuous_invFun := inv.continuous }

@[simp]
lemma homeomorphSmashIntervalQuotient_mk (x : X) (t : I) :
    homeomorphSmashIntervalQuotient x₀ (mk x₀ (x, t)) =
      SmashProduct.mk x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint
        (x, intervalEndpointPair.{u}.ordinaryPairQuotientπ (ULift.up t)) := by
  simp [homeomorphSmashIntervalQuotient, intervalπ]

@[simp]
lemma homeomorphSmashIntervalQuotient_basepoint :
    homeomorphSmashIntervalQuotient x₀ (basepoint x₀) =
      SmashProduct.basepoint x₀ intervalEndpointPair.{u}.ordinaryPairQuotientBasepoint := by
  simp [homeomorphSmashIntervalQuotient]

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
