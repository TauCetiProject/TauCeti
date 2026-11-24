/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Subpath
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Category.TopPair.Quotient

/-!
# The reduced suspension

The **reduced suspension** of a pointed space `(X, x₀)` is the quotient

`ΣX = (X × I) / (X × ∂I ∪ {x₀} × I)`

of the cylinder on `X` in which both ends and the segment over the basepoint are collapsed to a
single basepoint (`TauCeti.ReducedSuspension`). It is the pointed quotient
`TopPair.ordinaryPairQuotient` of the pair `(X × I, X × ∂I ∪ {x₀} × I)`, so it carries the
quotient topology of the cylinder, with no compact-generation correction, and its basepoint is the
image of the collapsed locus. Write `[x, s]` for the image of `(x, s)`
(`TauCeti.ReducedSuspension.mk`).

* Two points of the cylinder have the same image exactly when they are equal or both collapsed
  (`TauCeti.ReducedSuspension.mk_eq_mk_iff`), and the projection is a quotient map
  (`TauCeti.ReducedSuspension.isQuotientMap_mk`).
* A continuous map out of the cylinder that is constant on the collapsed locus descends to the
  reduced suspension (`TauCeti.ReducedSuspension.lift`), uniquely
  (`TauCeti.ReducedSuspension.continuousMap_ext`). In particular a based map `f : X → Y` induces
  the based map `Σf : [x, s] ↦ [f x, s]` (`TauCeti.ReducedSuspension.map`), functorially.
* The identity is a homeomorphism onto the pointed quotient of the pair
  (`TauCeti.ReducedSuspension.homeomorphOrdinaryPairQuotient`), through which the results on
  pointed quotients of pairs apply to the reduced suspension.
* The **meridian** through `x` is the loop `s ↦ [x, s]` at the basepoint
  (`TauCeti.ReducedSuspension.meridian`). It depends continuously on `x`, and the meridian through
  the basepoint is the constant loop. As a based map `X → Ω(ΣX)` it is the unit of the
  suspension–loop adjunction. Normalized to the unit interval, the James map sends the letter `x`
  to the meridian through `x` (`TauCeti.JamesReducedProduct.toPath_jamesMap_letter`).
* Every point `[x, s]` lies on the meridian through `x`, so the reduced suspension of any pointed
  space is path connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (suspension) and
  Section 4.3 (the reduced suspension and the suspension–loop adjunction).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public section

noncomputable section

open scoped unitInterval
open Topology

universe u v w

namespace TauCeti

variable (X : Type u) [TopologicalSpace X] (x₀ : X)

omit [TopologicalSpace X] in
/-- The part `X × ∂I ∪ {x₀} × I` of the cylinder `X × I` that the reduced suspension collapses to
its basepoint. -/
def reducedSuspensionLocus : Set (X × I) :=
  {p | p.1 = x₀ ∨ p.2 = 0 ∨ p.2 = 1}

/-- The topological pair `(X × I, X × ∂I ∪ {x₀} × I)` whose pointed quotient is the reduced
suspension. -/
abbrev reducedSuspensionPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (X × I)) (reducedSuspensionLocus X x₀)

/-- The **reduced suspension** `ΣX = (X × I) / (X × ∂I ∪ {x₀} × I)` of a pointed space `(X, x₀)`:
the pointed quotient of the cylinder `X × I` collapsing both ends and the segment over the
basepoint to a single point, with the quotient topology. -/
def ReducedSuspension : Type u :=
  (reducedSuspensionPair X x₀).ordinaryPairQuotient

instance : TopologicalSpace (ReducedSuspension X x₀) :=
  inferInstanceAs (TopologicalSpace (reducedSuspensionPair X x₀).ordinaryPairQuotient)

variable {X x₀}

omit [TopologicalSpace X] in
@[simp]
theorem mem_reducedSuspensionLocus {p : X × I} :
    p ∈ reducedSuspensionLocus X x₀ ↔ p.1 = x₀ ∨ p.2 = 0 ∨ p.2 = 1 :=
  Iff.rfl

namespace ReducedSuspension

/-- The projection `X × I → ΣX`, `(x, s) ↦ [x, s]`. -/
def mk : C(X × I, ReducedSuspension X x₀) :=
  (reducedSuspensionPair X x₀).ordinaryPairQuotientπ.hom

/-- The basepoint of the reduced suspension, the image of the collapsed locus. -/
def basepoint : ReducedSuspension X x₀ :=
  (reducedSuspensionPair X x₀).ordinaryPairQuotientBasepoint

instance : Inhabited (ReducedSuspension X x₀) :=
  ⟨basepoint⟩

variable (X x₀) in
/-- The reduced suspension is the pointed quotient of the pair `(X × I, X × ∂I ∪ {x₀} × I)`,
through the identity map. This identifies `[x, s]` with the collapse of `(x, s)` and the basepoint
with the collapsed point (`TauCeti.ReducedSuspension.homeomorphOrdinaryPairQuotient_mk`,
`TauCeti.ReducedSuspension.homeomorphOrdinaryPairQuotient_basepoint`), so that the results on
pointed quotients of pairs apply to the reduced suspension. -/
def homeomorphOrdinaryPairQuotient :
    ReducedSuspension X x₀ ≃ₜ (reducedSuspensionPair X x₀).ordinaryPairQuotient :=
  .refl _

@[simp]
theorem homeomorphOrdinaryPairQuotient_mk (p : X × I) :
    homeomorphOrdinaryPairQuotient X x₀ (mk p) =
      (reducedSuspensionPair X x₀).ordinaryPairQuotientπ p :=
  (rfl)

@[simp]
theorem homeomorphOrdinaryPairQuotient_basepoint :
    homeomorphOrdinaryPairQuotient X x₀ basepoint =
      (reducedSuspensionPair X x₀).ordinaryPairQuotientBasepoint :=
  (rfl)

/-- Exactly the collapsed locus is sent to the basepoint. -/
theorem mk_eq_basepoint_iff {p : X × I} :
    (mk p : ReducedSuspension X x₀) = basepoint ↔ p ∈ reducedSuspensionLocus X x₀ :=
  ((reducedSuspensionPair X x₀).ordinaryPairQuotientπ_eq_basepoint_iff p).trans
    (by rw [TopPair.range_ofSubset_map]; exact Iff.rfl)

theorem mk_eq_basepoint {p : X × I} (hp : p ∈ reducedSuspensionLocus X x₀) :
    (mk p : ReducedSuspension X x₀) = basepoint :=
  mk_eq_basepoint_iff.2 hp

@[simp]
theorem mk_basepoint (s : I) : (mk (x₀, s) : ReducedSuspension X x₀) = basepoint :=
  mk_eq_basepoint (Or.inl rfl)

@[simp]
theorem mk_zero (x : X) : (mk (x, 0) : ReducedSuspension X x₀) = basepoint :=
  mk_eq_basepoint (Or.inr (Or.inl rfl))

@[simp]
theorem mk_one (x : X) : (mk (x, 1) : ReducedSuspension X x₀) = basepoint :=
  mk_eq_basepoint (Or.inr (Or.inr rfl))

/-- Two points of the cylinder have the same image in the reduced suspension exactly when they are
equal or both lie in the collapsed locus. -/
theorem mk_eq_mk_iff {p q : X × I} :
    (mk p : ReducedSuspension X x₀) = mk q ↔
      p = q ∨ p ∈ reducedSuspensionLocus X x₀ ∧ q ∈ reducedSuspensionLocus X x₀ := by
  refine ((reducedSuspensionPair X x₀).ordinaryPairQuotientπ_eq_iff p q).trans ?_
  rw [TopPair.range_ofSubset_map]
  rfl

theorem mk_surjective : Function.Surjective (mk : X × I → ReducedSuspension X x₀) := by
  intro z
  obtain ⟨p, hp⟩ | rfl :=
    (reducedSuspensionPair X x₀).exists_ordinaryPairQuotientπ_or_eq_basepoint z
  · exact ⟨p, hp⟩
  · exact ⟨(x₀, 0), mk_basepoint 0⟩

/-- A map out of the reduced suspension is continuous exactly when its composite with the
projection from the cylinder is. -/
theorem continuous_iff {Y : Type v} [TopologicalSpace Y] {f : ReducedSuspension X x₀ → Y} :
    Continuous f ↔ Continuous (f ∘ mk) :=
  (reducedSuspensionPair X x₀).continuous_ordinaryPairQuotient_iff f

/-- The projection from the cylinder onto the reduced suspension is a quotient map. -/
theorem isQuotientMap_mk : IsQuotientMap (mk : X × I → ReducedSuspension X x₀) :=
  ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ by
    rw [isOpen_iff_continuous_mem, isOpen_iff_continuous_mem]
    exact continuous_iff.symm, mk_surjective⟩

/-- Continuous maps out of the reduced suspension are determined by their composites with the
projection from the cylinder. -/
@[ext]
theorem continuousMap_ext {Y : Type v} [TopologicalSpace Y] {f g : C(ReducedSuspension X x₀, Y)}
    (h : ∀ p, f (mk p) = g (mk p)) : f = g :=
  ContinuousMap.ext fun z ↦ by
    obtain ⟨p, rfl⟩ := mk_surjective z
    exact h p

section Lift

variable {Y : Type v} [TopologicalSpace Y]

/-- The **universal property** of the reduced suspension: a continuous map `f` out of the
cylinder `X × I` sending the collapsed locus to a point `y` descends to the continuous map
`[x, s] ↦ f (x, s)` out of the reduced suspension, which sends the basepoint to `y`. It is the
only such map (`TauCeti.ReducedSuspension.continuousMap_ext`). -/
def lift (f : C(X × I, Y)) (y : Y) (hf : ∀ p ∈ reducedSuspensionLocus X x₀, f p = y) :
    C(ReducedSuspension X x₀, Y) :=
  isQuotientMap_mk.lift f fun p q hpq ↦ by
    obtain rfl | ⟨hp, hq⟩ := mk_eq_mk_iff.1 hpq
    · rfl
    · rw [hf p hp, hf q hq]

@[simp]
theorem lift_comp_mk (f : C(X × I, Y)) (y : Y)
    (hf : ∀ p ∈ reducedSuspensionLocus X x₀, f p = y) : (lift f y hf).comp mk = f :=
  isQuotientMap_mk.lift_comp f _

@[simp]
theorem lift_mk (f : C(X × I, Y)) (y : Y) (hf : ∀ p ∈ reducedSuspensionLocus X x₀, f p = y)
    (p : X × I) : lift f y hf (mk p) = f p :=
  DFunLike.congr_fun (lift_comp_mk f y hf) p

@[simp]
theorem lift_basepoint (f : C(X × I, Y)) (y : Y)
    (hf : ∀ p ∈ reducedSuspensionLocus X x₀, f p = y) : lift f y hf basepoint = y := by
  rw [← mk_basepoint (x₀ := x₀) 0, lift_mk, hf _ (Or.inl rfl)]

end Lift

/-! ### Functoriality -/

section Map

variable {Y : Type v} [TopologicalSpace Y] {y₀ : Y} {Z : Type w} [TopologicalSpace Z] {z₀ : Z}

/-- The based map `Σf : ΣX → ΣY`, `[x, s] ↦ [f x, s]`, induced by a based map `f : X → Y`. -/
def map (f : C(X, Y)) (hf : f x₀ = y₀) : C(ReducedSuspension X x₀, ReducedSuspension Y y₀) :=
  lift (mk.comp (f.prodMap (.id I))) basepoint fun p hp ↦ mk_eq_basepoint <| by
    rcases hp with h | h | h
    · exact Or.inl ((congrArg f h).trans hf)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

@[simp]
theorem map_mk (f : C(X, Y)) (hf : f x₀ = y₀) (p : X × I) :
    map f hf (mk p) = mk (f p.1, p.2) :=
  lift_mk _ _ _ p

@[simp]
theorem map_basepoint (f : C(X, Y)) (hf : f x₀ = y₀) :
    map f hf (basepoint : ReducedSuspension X x₀) = basepoint :=
  lift_basepoint _ _ _

@[simp]
theorem map_id : map (.id X) rfl = .id (ReducedSuspension X x₀) :=
  continuousMap_ext fun _ ↦ map_mk _ _ _

theorem map_comp (g : C(Y, Z)) (hg : g y₀ = z₀) (f : C(X, Y)) (hf : f x₀ = y₀) :
    map (g.comp f) ((congrArg g hf).trans hg) = (map g hg).comp (map f hf) :=
  continuousMap_ext fun p ↦ by simp

end Map

/-! ### Meridians -/

/-- The **meridian** through a point `x`: the loop `s ↦ [x, s]` at the basepoint of the reduced
suspension. It depends continuously on `x`, so it is a map `X → Ω(ΣX)`; this is the unit of the
suspension–loop adjunction. -/
def meridian : C(X, Path (basepoint : ReducedSuspension X x₀) basepoint) where
  toFun x :=
    { toContinuousMap := mk.comp ((ContinuousMap.const I x).prodMk (.id I))
      source' := mk_zero x
      target' := mk_one x }
  continuous_toFun := Path.continuous_uncurry_iff.1 mk.continuous

@[simp]
theorem meridian_apply (x : X) (s : I) :
    (meridian x : Path (basepoint : ReducedSuspension X x₀) basepoint) s = mk (x, s) :=
  (rfl)

/-- The meridian through the basepoint is the constant loop. -/
@[simp]
theorem meridian_basepoint :
    (meridian x₀ : Path (basepoint : ReducedSuspension X x₀) basepoint) = .refl basepoint :=
  Path.ext <| funext fun s ↦ mk_basepoint s

/-- The meridians are natural in based maps: the meridian through `f x` is the image under `Σf` of
the meridian through `x`. -/
theorem meridian_map {Y : Type v} [TopologicalSpace Y] {y₀ : Y} (f : C(X, Y)) (hf : f x₀ = y₀)
    (x : X) :
    (meridian (f x) : Path (basepoint : ReducedSuspension Y y₀) basepoint) =
      ((meridian x).map (map f hf).continuous).cast (map_basepoint f hf).symm
        (map_basepoint f hf).symm :=
  Path.ext <| funext fun s ↦ by simp

/-- Induction principle for `ΣX`: every point is of the form `mk (x, t)`. -/
@[elab_as_elim]
lemma ind {motive : ReducedSuspension X x₀ → Prop}
    (hmk : ∀ x t, motive (mk (x, t))) (z : ReducedSuspension X x₀) : motive z :=
  let ⟨⟨x, t⟩, h⟩ := mk_surjective z; h ▸ hmk x t

lemma isOpen_iff {s : Set (ReducedSuspension X x₀)} : IsOpen s ↔ IsOpen (mk ⁻¹' s) :=
  (reducedSuspensionPair X x₀).isOpen_ordinaryPairQuotient_iff

lemma isClosed_iff {s : Set (ReducedSuspension X x₀)} : IsClosed s ↔ IsClosed (mk ⁻¹' s) :=
  (reducedSuspensionPair X x₀).isClosed_ordinaryPairQuotient_iff

instance [CompactSpace X] : CompactSpace (ReducedSuspension X x₀) :=
  haveI : CompactSpace (reducedSuspensionPair X x₀).fst := inferInstanceAs (CompactSpace (X × I))
  (reducedSuspensionPair X x₀).compactSpace_ordinaryPairQuotient

private lemma disjoint_nhdsSet_reducedSuspensionLocus [T2Space X] {x : X} {t : I}
    (hx : x ≠ x₀) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Disjoint (𝓝ˢ (reducedSuspensionLocus X x₀)) (𝓝 (x, t)) := by
  have hsub : reducedSuspensionLocus X x₀ =
      Set.univ ×ˢ ({0, 1} : Set I) ∪ {x₀} ×ˢ Set.univ := by
    ext ⟨u, s⟩
    simp [reducedSuspensionLocus, or_comm]
  rw [hsub, nhdsSet_union, disjoint_sup_left, nhds_prod_eq]
  exact ⟨(Filter.disjoint_prod.2 <| Or.inr <|
      (Set.toFinite ({0, 1} : Set I)).isCompact.disjoint_nhdsSet_nhds <| by
        simp [ht0, ht1]).mono_left (nhdsSet_prod_le _ _),
    (Filter.disjoint_prod.2 <| Or.inl <|
      isCompact_singleton.disjoint_nhdsSet_nhds hx).mono_left (nhdsSet_prod_le _ _)⟩

instance [T2Space X] : T2Space (ReducedSuspension X x₀) := by
  -- `ReducedSuspension X x₀` is the quotient of `reducedSuspensionPair X x₀`, whose ambient
  -- space `TopCat.of (X × I)` has carrier and topology `X × I` (`TopCat.coe_of`).
  have : T2Space (reducedSuspensionPair X x₀).fst := inferInstanceAs (T2Space (X × I))
  refine (reducedSuspensionPair X x₀).t2Space_ordinaryPairQuotient_of_disjoint_nhdsSet
    fun ⟨x, t⟩ h ↦ ?_
  rw [TopPair.range_ofSubset_map] at h ⊢
  exact disjoint_nhdsSet_reducedSuspensionLocus
    (fun hx ↦ h (Or.inl hx)) (fun ht ↦ h (Or.inr (Or.inl ht))) (fun ht ↦ h (Or.inr (Or.inr ht)))

instance [Subsingleton X] : Subsingleton (ReducedSuspension X x₀) :=
  subsingleton_of_forall_eq basepoint (ind fun x t ↦ Subsingleton.elim x x₀ ▸ mk_basepoint t)

/-- A pointed homeomorphism `X ≃ₜ Y` induces a homeomorphism `ΣX ≃ₜ ΣY`. -/
def congrHomeomorph {Y : Type v} [TopologicalSpace Y] {y₀ : Y} (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    ReducedSuspension X x₀ ≃ₜ ReducedSuspension Y y₀ where
  toFun := map (e : C(X, Y)) he
  invFun := map (e.symm : C(Y, X)) (e.symm_apply_eq.2 he.symm)
  left_inv := ind fun x t ↦ by simp
  right_inv := ind fun y t ↦ by simp
  continuous_toFun := (map (e : C(X, Y)) he).continuous
  continuous_invFun := (map (e.symm : C(Y, X)) (e.symm_apply_eq.2 he.symm)).continuous

@[simp]
lemma congrHomeomorph_mk {Y : Type v} [TopologicalSpace Y] {y₀ : Y}
    (e : X ≃ₜ Y) (he : e x₀ = y₀) (p : X × I) :
    congrHomeomorph e he (mk p) = mk (e p.1, p.2) :=
  map_mk (e : C(X, Y)) he p

@[simp]
lemma congrHomeomorph_basepoint {Y : Type v} [TopologicalSpace Y] {y₀ : Y}
    (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    congrHomeomorph e he (basepoint : ReducedSuspension X x₀) = basepoint :=
  map_basepoint (e : C(X, Y)) he

@[simp]
lemma congrHomeomorph_symm {Y : Type v} [TopologicalSpace Y] {y₀ : Y}
    (e : X ≃ₜ Y) (he : e x₀ = y₀) :
    (congrHomeomorph e he).symm = congrHomeomorph e.symm (e.symm_apply_eq.2 he.symm) := (rfl)

/-- The reduced suspension of any pointed space is path connected: every point `[x, s]` is joined
to the basepoint along the meridian through `x`. -/
instance : PathConnectedSpace (ReducedSuspension X x₀) := by
  refine pathConnectedSpace_iff_eq.2 ⟨basepoint, Set.eq_univ_of_forall fun z ↦ ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := mk_surjective z
  exact ⟨((meridian x).subpath 0 s).cast (meridian x).source.symm rfl⟩

end ReducedSuspension

end TauCeti
