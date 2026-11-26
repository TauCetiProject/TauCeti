/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Subpath
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Category.TopPair.Quotient
public import TauCeti.Topology.Homotopy.Quotient

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
* A homotopy `F` of based maps relative to the basepoint suspends to the homotopy
  `(t, [x, s]) ↦ [F (t, x), s]` relative to the basepoint
  (`ContinuousMap.HomotopyRel.reducedSuspensionMap`), so pointed-homotopic maps have
  pointed-homotopic suspensions (`ContinuousMap.HomotopicRel.reducedSuspensionMap`).
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

omit [TopologicalSpace X] in
/-- A map `f` sending `x₀` to `y₀`, applied to the first coordinate, carries the collapsed locus of
the cylinder on `X` into the collapsed locus of the cylinder on `Y`. -/
theorem map_fst_mem_reducedSuspensionLocus {Y : Type v} {y₀ : Y} {f : X → Y} (hf : f x₀ = y₀)
    {p : X × I} (hp : p ∈ reducedSuspensionLocus X x₀) :
    (f p.1, p.2) ∈ reducedSuspensionLocus Y y₀ := by
  rcases hp with h | h | h
  · exact Or.inl ((congrArg f h).trans hf)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

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
  lift (mk.comp (f.prodMap (.id I))) basepoint fun _ hp ↦
    mk_eq_basepoint (map_fst_mem_reducedSuspensionLocus hf hp)

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

/-- The reduced suspension of any pointed space is path connected: every point `[x, s]` is joined
to the basepoint along the meridian through `x`. -/
instance : PathConnectedSpace (ReducedSuspension X x₀) := by
  refine pathConnectedSpace_iff_eq.2 ⟨basepoint, Set.eq_univ_of_forall fun z ↦ ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := mk_surjective z
  exact ⟨((meridian x).subpath 0 s).cast (meridian x).source.symm rfl⟩

end ReducedSuspension

end TauCeti

namespace ContinuousMap

open TauCeti TauCeti.ReducedSuspension

variable {X : Type u} [TopologicalSpace X] {x₀ : X} {Y : Type v} [TopologicalSpace Y] {y₀ : Y}
  {f₀ f₁ : C(X, Y)}

/-- **The suspension of a pointed homotopy.** A homotopy `F` between based maps `f₀ f₁ : X → Y`
relative to the basepoint `x₀` suspends to the homotopy `(t, [x, s]) ↦ [F (t, x), s]` between
`Σf₀` and `Σf₁`, relative to the basepoint of `ΣX`. -/
def HomotopyRel.reducedSuspensionMap (F : f₀.HomotopyRel f₁ {x₀}) (h₀ : f₀ x₀ = y₀)
    (h₁ : f₁ x₀ = y₀) :
    (map f₀ h₀).HomotopyRel (map f₁ h₁) {(basepoint : ReducedSuspension X x₀)} where
  -- The homotopy `(t, (x, s)) ↦ [F (t, x), s]` of the cylinder is constant on the fibres of the
  -- projection to `ΣX`, so it descends along that quotient map.
  toHomotopy := isQuotientMap_mk.liftHomotopy (f₀ := (map f₀ h₀).comp ReducedSuspension.mk)
    (f₁ := (map f₁ h₁).comp ReducedSuspension.mk)
    { toFun q := ReducedSuspension.mk (F (q.1, q.2.1), q.2.2)
      map_zero_left p := by simp
      map_one_left p := by simp }
    (fun t p q hpq ↦ by
      obtain rfl | ⟨hp, hq⟩ := mk_eq_mk_iff.1 hpq
      · rfl
      · -- Both points are collapsed, and so are their images under `F` at time `t`.
        have hFt : F (t, x₀) = y₀ := (F.eq_fst t rfl).trans h₀
        exact (mk_eq_basepoint (map_fst_mem_reducedSuspensionLocus (f := F.curry t) hFt hp)).trans
          (mk_eq_basepoint (map_fst_mem_reducedSuspensionLocus (f := F.curry t) hFt hq)).symm)
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  prop' t z hz := by
    -- The basepoint of `ΣX` is `[x₀, 0]`, where the descended homotopy is `[F (t, x₀), 0]`.
    rw [Set.mem_singleton_iff.1 hz, map_basepoint, ← mk_basepoint (x₀ := x₀) 0]
    exact (Topology.IsQuotientMap.liftHomotopy_apply _ _ _ _ _ t (x₀, 0)).trans (mk_zero _)

@[simp]
theorem HomotopyRel.reducedSuspensionMap_apply_mk (F : f₀.HomotopyRel f₁ {x₀}) (h₀ : f₀ x₀ = y₀)
    (h₁ : f₁ x₀ = y₀) (t : I) (p : X × I) :
    F.reducedSuspensionMap h₀ h₁ (t, ReducedSuspension.mk p) =
      ReducedSuspension.mk (F (t, p.1), p.2) := by
  rw [← HomotopyWith.coe_toHomotopy (F.reducedSuspensionMap h₀ h₁)]
  exact Topology.IsQuotientMap.liftHomotopy_apply _ _ _ _ _ t p

/-- **Pointed-homotopic maps have pointed-homotopic suspensions.** If the based maps
`f₀ f₁ : X → Y` are homotopic relative to the basepoint, then so are `Σf₀` and `Σf₁`. -/
theorem HomotopicRel.reducedSuspensionMap (h : f₀.HomotopicRel f₁ {x₀}) (h₀ : f₀ x₀ = y₀)
    (h₁ : f₁ x₀ = y₀) :
    (map f₀ h₀).HomotopicRel (map f₁ h₁) {(basepoint : ReducedSuspension X x₀)} :=
  h.map fun F ↦ F.reducedSuspensionMap h₀ h₁

end ContinuousMap
