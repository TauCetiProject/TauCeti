/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Sets.Opens

/-!
# The connected sum of two spaces along coordinate balls

Let `E` be a real inner product space and let `e₁ : E → M` and `e₂ : E → N` be open embeddings of
`E` into two spaces, the coordinate balls along which the connected sum is formed. The connected sum
`TauCeti.ConnectedSum e₁ e₂` removes the centres `e₁ 0` and `e₂ 0` and glues the punctured balls
`e₁ (E ∖ {0})` and `e₂ (E ∖ {0})` by the inversion `v ↦ v / ‖v‖²` of `E` in its unit sphere: for
`v ≠ 0`, the point `e₁ v` is identified with `e₂ (inversion 0 1 v)`. As `v` runs from the centre of
the first ball to its end, its partner runs from the end of the second ball to its centre, so a
neighbourhood of the removed centre on either side is replaced by the far end of the other ball.

This is Kosinski's construction of the connected sum (*Differential Manifolds*, Chapter VI,
Section 1), where the closed unit disc is used and `t u` is glued to `(1 - t) u`; the inversion of
the whole space is the same gluing after rescaling the radial coordinate. Removing a point rather
than an open ball means that no boundary appears and no collar is needed, so the summands are glued
along open subsets.

The summands with their centres removed, `TauCeti.ConnectedSum.puncture e₁` and
`TauCeti.ConnectedSum.puncture e₂`, are open subspaces of the connected sum
(`TauCeti.ConnectedSum.isOpenEmbedding_inl`, `TauCeti.ConnectedSum.isOpenEmbedding_inr`) which
together cover it, and they meet exactly along the glued punctured balls
(`TauCeti.ConnectedSum.inl_eq_inr_iff`); so the quotient map from their disjoint union is a local
homeomorphism (`TauCeti.ConnectedSum.isLocalHomeomorph_mk`). When `E` is finite-dimensional and `M`
and `N` are Hausdorff, so is the connected sum (`TauCeti.ConnectedSum.t2Space`): a point outside
both balls is kept apart from the far end of the other ball by the image of a closed ball.

The construction takes the balls as data, as the connected sum depends on them; that the result
does not depend on the choice up to diffeomorphism, for orientation-compatible balls in connected
manifolds, is the disc theorem of Palais and is not part of this file.

## Main definitions

* `TauCeti.ConnectedSum e₁ e₂`: the connected sum of `M` and `N` along `e₁` and `e₂`.
* `TauCeti.ConnectedSum.puncture e`: the complement of the centre of the ball `e`, as an open set.
* `TauCeti.ConnectedSum.mk`, `TauCeti.ConnectedSum.inl`, `TauCeti.ConnectedSum.inr`: the quotient
  map from the disjoint union of the punctured summands and its two components.

## Main results

* `TauCeti.ConnectedSum.mk_eq_mk_iff`, `TauCeti.ConnectedSum.inl_eq_inr_iff`: the identifications
  made by the gluing.
* `TauCeti.ConnectedSum.lift_unique`, `TauCeti.ConnectedSum.hom_ext`: a map out of the connected
  sum is determined by its restrictions to the two punctured summands.
* `TauCeti.ConnectedSum.isOpenQuotientMap_mk`: the quotient map is open.
* `TauCeti.ConnectedSum.isLocalHomeomorph_mk`: the quotient map is a local homeomorphism.
* `TauCeti.ConnectedSum.isOpenEmbedding_inl`, `TauCeti.ConnectedSum.isOpenEmbedding_inr`: each
  punctured summand is an open subspace.
* `TauCeti.ConnectedSum.t2Space`: the connected sum of Hausdorff spaces along finite-dimensional
  balls is Hausdorff.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
-/

public section

open Set Filter Function Topology TopologicalSpace EuclideanGeometry

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {N : Type*} [TopologicalSpace N] [T1Space N]

namespace ConnectedSum

/-- The complement of the centre `e 0` of a coordinate ball `e : E → M`, as an open subset of `M`:
a summand of the connected sum along `e`, with the centre removed. -/
def puncture (e : E → M) : Opens M :=
  ⟨{e 0}ᶜ, isOpen_compl_singleton⟩

@[simp]
theorem mem_puncture {e : E → M} {x : M} : x ∈ puncture e ↔ x ≠ e 0 :=
  Iff.rfl

@[simp]
theorem coe_puncture (e : E → M) : (puncture e : Set M) = {e 0}ᶜ :=
  (rfl)

/-- An injective map carrying the centre of the ball `e` to the centre of the ball `e'` carries
the punctured summand `M ∖ {e 0}` into the punctured summand `M' ∖ {e' 0}`. -/
theorem apply_mem_puncture {M' : Type*} [TopologicalSpace M'] [T1Space M'] {e : E → M}
    {e' : E → M'} {φ : M → M'} (hφ : Injective φ) (h0 : φ (e 0) = e' 0) {x : M}
    (hx : x ∈ puncture e) : φ x ∈ puncture e' :=
  mem_puncture.2 (h0 ▸ hφ.ne hx)

/-- An injective ball does not meet its centre at the inversion of a nonzero vector. -/
theorem apply_inversion_mem_puncture [InnerProductSpace ℝ E] {e : E → M} (he : Injective e)
    {w : E} (hw : w ≠ 0) : e (inversion 0 1 w) ∈ puncture e := by
  simpa [he.eq_iff, inversion_eq_center one_ne_zero] using hw

variable [InnerProductSpace ℝ E] (e₁ : E → M) (e₂ : E → N)

/-- The gluing relation of the connected sum: for `v ≠ 0`, the point `e₁ v` of the first punctured
summand is related to the point `e₂ (inversion 0 1 v)` of the second. -/
def Rel : puncture e₁ ⊕ puncture e₂ → puncture e₁ ⊕ puncture e₂ → Prop
  | .inl x, .inr y => ∃ v ≠ 0, e₁ v = x ∧ e₂ (inversion 0 1 v) = y
  | _, _ => False

variable {e₁ e₂}

@[simp]
theorem rel_inl_inr {x : puncture e₁} {y : puncture e₂} :
    Rel e₁ e₂ (.inl x) (.inr y) ↔ ∃ v ≠ 0, e₁ v = x ∧ e₂ (inversion 0 1 v) = y :=
  Iff.rfl

@[simp]
theorem not_rel_inl_inl {x x' : puncture e₁} : ¬Rel e₁ e₂ (.inl x) (.inl x') :=
  id

@[simp]
theorem not_rel_inr_inl {y : puncture e₂} {x : puncture e₁} : ¬Rel e₁ e₂ (.inr y) (.inl x) :=
  id

@[simp]
theorem not_rel_inr_inr {y y' : puncture e₂} : ¬Rel e₁ e₂ (.inr y) (.inr y') :=
  id

end ConnectedSum

variable [InnerProductSpace ℝ E]

/-- The **connected sum** of `M` and `N` along the coordinate balls `e₁ : E → M` and `e₂ : E → N`:
the centres `e₁ 0` and `e₂ 0` are removed, and for `v ≠ 0` the point `e₁ v` is glued to
`e₂ (inversion 0 1 v)`. -/
def ConnectedSum (e₁ : E → M) (e₂ : E → N) : Type _ :=
  Quot (ConnectedSum.Rel e₁ e₂)

namespace ConnectedSum

variable (e₁ : E → M) (e₂ : E → N)

instance : TopologicalSpace (ConnectedSum e₁ e₂) :=
  inferInstanceAs (TopologicalSpace (Quot (Rel e₁ e₂)))

/-- The quotient map from the disjoint union of the punctured summands onto the connected sum. -/
def mk : puncture e₁ ⊕ puncture e₂ → ConnectedSum e₁ e₂ :=
  Quot.mk _

/-- The first punctured summand, as a subspace of the connected sum. -/
def inl (x : puncture e₁) : ConnectedSum e₁ e₂ :=
  mk e₁ e₂ (.inl x)

/-- The second punctured summand, as a subspace of the connected sum. -/
def inr (y : puncture e₂) : ConnectedSum e₁ e₂ :=
  mk e₁ e₂ (.inr y)

@[simp]
theorem mk_inl (x : puncture e₁) : mk e₁ e₂ (.inl x) = inl e₁ e₂ x :=
  (rfl)

@[simp]
theorem mk_inr (y : puncture e₂) : mk e₁ e₂ (.inr y) = inr e₁ e₂ y :=
  (rfl)

theorem mk_surjective : Surjective (mk e₁ e₂) :=
  Quot.mk_surjective

theorem range_inl_union_range_inr : range (inl e₁ e₂) ∪ range (inr e₁ e₂) = univ := by
  refine eq_univ_of_forall fun p ↦ ?_
  obtain ⟨x | y, rfl⟩ := mk_surjective e₁ e₂ p
  exacts [Or.inl ⟨x, rfl⟩, Or.inr ⟨y, rfl⟩]

theorem isQuotientMap_mk : IsQuotientMap (mk e₁ e₂) :=
  isQuotientMap_quot_mk

theorem continuous_mk : Continuous (mk e₁ e₂) :=
  (isQuotientMap_mk e₁ e₂).continuous

theorem continuous_inl : Continuous (inl e₁ e₂) :=
  (continuous_mk e₁ e₂).comp _root_.continuous_inl

theorem continuous_inr : Continuous (inr e₁ e₂) :=
  (continuous_mk e₁ e₂).comp _root_.continuous_inr

variable {e₁ e₂}

/-- The gluing relation together with equality and its converse is transitive, once the balls are
injective. -/
private theorem rel_trans (he₁ : Injective e₁) (he₂ : Injective e₂)
    {a b c : puncture e₁ ⊕ puncture e₂} (hab : a = b ∨ Rel e₁ e₂ a b ∨ Rel e₁ e₂ b a)
    (hbc : b = c ∨ Rel e₁ e₂ b c ∨ Rel e₁ e₂ c b) :
    a = c ∨ Rel e₁ e₂ a c ∨ Rel e₁ e₂ c a := by
  rcases a with x | x <;> rcases b with y | y <;> rcases c with z | z <;>
    simp only [Rel, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, or_false, false_or] at hab hbc ⊢
  · exact hab.trans hbc
  · subst hab; exact hbc
  · obtain ⟨v, -, hv₁, hv₂⟩ := hab
    obtain ⟨w, -, hw₁, hw₂⟩ := hbc
    obtain rfl := inversion_injective (0 : E) one_ne_zero (he₂ (hw₂.trans hv₂.symm))
    exact Subtype.ext (hv₁.symm.trans hw₁)
  · subst hbc; exact hab
  · subst hbc; exact hab
  · obtain ⟨v, -, hv₁, hv₂⟩ := hab
    obtain ⟨w, -, hw₁, hw₂⟩ := hbc
    obtain rfl := he₁ (hw₁.trans hv₁.symm)
    exact Subtype.ext (hv₂.symm.trans hw₂)
  · subst hab; exact hbc
  · exact hab.trans hbc

/-- **The identifications of the connected sum.** Two points of the punctured summands are
identified exactly when they are equal or glued, provided the balls are injective. -/
theorem mk_eq_mk_iff (he₁ : Injective e₁) (he₂ : Injective e₂)
    {a b : puncture e₁ ⊕ puncture e₂} :
    mk e₁ e₂ a = mk e₁ e₂ b ↔ a = b ∨ Rel e₁ e₂ a b ∨ Rel e₁ e₂ b a := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hg := Quot.eqvGen_exact h
    clear h
    induction hg with
    | rel a b h => exact Or.inr (Or.inl h)
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      obtain rfl | h | h := ih
      exacts [Or.inl rfl, Or.inr (Or.inr h), Or.inr (Or.inl h)]
    | trans a b c _ _ ihab ihbc => exact rel_trans he₁ he₂ ihab ihbc
  · rintro (rfl | h | h)
    exacts [rfl, Quot.sound h, (Quot.sound h).symm]

theorem inl_injective (he₁ : Injective e₁) (he₂ : Injective e₂) : Injective (inl e₁ e₂) := by
  intro x y h
  rw [← mk_inl, ← mk_inl, mk_eq_mk_iff he₁ he₂] at h
  simpa using h

theorem inr_injective (he₁ : Injective e₁) (he₂ : Injective e₂) : Injective (inr e₁ e₂) := by
  intro x y h
  rw [← mk_inr, ← mk_inr, mk_eq_mk_iff he₁ he₂] at h
  simpa using h

/-- **The two punctured summands meet along the glued punctured balls**: `x` and `y` are
identified exactly when `x = e₁ v` and `y = e₂ (inversion 0 1 v)` for some `v ≠ 0`. -/
theorem inl_eq_inr_iff (he₁ : Injective e₁) (he₂ : Injective e₂) {x : puncture e₁}
    {y : puncture e₂} :
    inl e₁ e₂ x = inr e₁ e₂ y ↔ ∃ v ≠ 0, e₁ v = x ∧ e₂ (inversion 0 1 v) = y := by
  rw [← mk_inl, ← mk_inr, mk_eq_mk_iff he₁ he₂]
  simp

/-- The glued points determined by a nonzero vector `v`. -/
theorem inl_eq_inr (v : E) (hv : v ≠ 0) (hx : e₁ v ∈ puncture e₁)
    (hy : e₂ (inversion 0 1 v) ∈ puncture e₂) :
    inl e₁ e₂ ⟨e₁ v, hx⟩ = inr e₁ e₂ ⟨e₂ (inversion 0 1 v), hy⟩ :=
  Quot.sound ⟨v, hv, rfl, rfl⟩

/-- The glued points determined by a nonzero vector `w`, read from the second ball: `e₂ w` is glued
to `e₁ (inversion 0 1 w)`, as the inversion is an involution. -/
theorem inl_inversion_eq_inr {w : E} (hw : w ≠ 0) (hx : e₁ (inversion 0 1 w) ∈ puncture e₁)
    (hy : e₂ w ∈ puncture e₂) :
    inl e₁ e₂ ⟨e₁ (inversion 0 1 w), hx⟩ = inr e₁ e₂ ⟨e₂ w, hy⟩ :=
  Quot.sound ⟨inversion 0 1 w, by simpa [inversion_eq_center one_ne_zero] using hw, rfl,
    by rw [inversion_inversion (0 : E) one_ne_zero]⟩

section lift

variable {Z : Type*} (f : puncture e₁ → Z) (g : puncture e₂ → Z)
  (hfg : ∀ v ≠ 0, ∀ hx hy, f ⟨e₁ v, hx⟩ = g ⟨e₂ (inversion 0 1 v), hy⟩)

/-- **Maps out of the connected sum.** Maps on the two punctured summands which agree at glued
points descend to the connected sum. -/
def lift : ConnectedSum e₁ e₂ → Z :=
  Quot.lift (Sum.elim f g) <| by
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) (⟨y, hy⟩ | ⟨y, hy⟩) h <;>
      simp only [rel_inl_inr, not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr] at h
    obtain ⟨v, hv, rfl, rfl⟩ := h
    exact hfg v hv _ _

@[simp]
theorem lift_inl (x : puncture e₁) : lift f g hfg (inl e₁ e₂ x) = f x :=
  (rfl)

@[simp]
theorem lift_inr (y : puncture e₂) : lift f g hfg (inr e₁ e₂ y) = g y :=
  (rfl)

theorem lift_comp_mk : lift f g hfg ∘ mk e₁ e₂ = Sum.elim f g :=
  funext <| Sum.rec (lift_inl f g hfg) (lift_inr f g hfg)

/-- Two maps out of the connected sum are equal when they agree on both punctured summands. -/
theorem hom_ext {φ ψ : ConnectedSum e₁ e₂ → Z} (hl : ∀ x, φ (inl e₁ e₂ x) = ψ (inl e₁ e₂ x))
    (hr : ∀ y, φ (inr e₁ e₂ y) = ψ (inr e₁ e₂ y)) : φ = ψ :=
  funext <| Quot.ind <| Sum.rec hl hr

/-- **Uniqueness of maps out of the connected sum.** A map restricting to `f` and `g` on the
punctured summands is the lift of `f` and `g`. -/
theorem lift_unique (φ : ConnectedSum e₁ e₂ → Z) (hl : ∀ x, φ (inl e₁ e₂ x) = f x)
    (hr : ∀ y, φ (inr e₁ e₂ y) = g y) : φ = lift f g hfg :=
  hom_ext hl hr

/-- A map out of the connected sum is continuous when its restrictions to the two punctured
summands are. -/
theorem continuous_lift [TopologicalSpace Z] (hf : Continuous f) (hg : Continuous g) :
    Continuous (lift f g hfg) :=
  (isQuotientMap_mk e₁ e₂).continuous_iff.2 (by rw [lift_comp_mk]; exact hf.sumElim hg)

end lift

/-- The quotient map of the connected sum is open: the saturation of an open set adds to it the
points of the other summand glued to it, which form an open set. -/
theorem isOpenQuotientMap_mk (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    IsOpenQuotientMap (mk e₁ e₂) := by
  refine ⟨mk_surjective e₁ e₂, continuous_mk e₁ e₂, fun U hU ↦ ?_⟩
  rw [← (isQuotientMap_mk e₁ e₂).isOpen_preimage, isOpen_sum_iff]
  obtain ⟨hU₁, hU₂⟩ := isOpen_sum_iff.1 hU
  -- The points of `U` in each summand, as open subsets of `M` and of `N`.
  set U₁ : Set M := (↑) '' (Sum.inl ⁻¹' U : Set (puncture e₁))
  set U₂ : Set N := (↑) '' (Sum.inr ⁻¹' U : Set (puncture e₂))
  have hU₁' : IsOpen U₁ := (puncture e₁).isOpen.isOpenMap_subtype_val _ hU₁
  have hU₂' : IsOpen U₂ := (puncture e₂).isOpen.isOpenMap_subtype_val _ hU₂
  -- The points of one ball glued to an open set `V` of the other form the open set
  -- `e '' ({0}ᶜ ∩ inversion 0 1 ⁻¹' (e' ⁻¹' V))`.
  have hinv : ContinuousOn (inversion (0 : E) 1) {0}ᶜ :=
    continuousOn_const.inversion continuousOn_const continuousOn_id fun _ ↦ id
  constructor
  · -- `x` is in the saturation if it is in `U`, or if it is glued to a point of `U₂`.
    have hW := h₁.isOpenMap _
      (hinv.isOpen_inter_preimage isOpen_compl_singleton (hU₂'.preimage h₂.continuous))
    convert hU₁.union (hW.preimage continuous_subtype_val) using 1
    refine Set.ext fun x ↦ ?_
    simp only [mem_union, mem_preimage, mem_image, U₂]
    constructor
    · rintro ⟨x' | y, hU, hxy⟩
      · rw [mk_inl, mk_inl, (inl_injective h₁.injective h₂.injective).eq_iff] at hxy
        exact Or.inl (hxy ▸ hU)
      · rw [mk_inl, mk_inr, eq_comm, inl_eq_inr_iff h₁.injective h₂.injective] at hxy
        obtain ⟨v, hv, hvx, hvy⟩ := hxy
        exact Or.inr ⟨v, ⟨hv, y, hU, hvy.symm⟩, hvx⟩
    · rintro (hx | ⟨v, ⟨hv, y, hyU, hy⟩, hvx⟩)
      · exact ⟨_, hx, rfl⟩
      · refine ⟨.inr y, hyU, ?_⟩
        rw [mk_inl, mk_inr, eq_comm, inl_eq_inr_iff h₁.injective h₂.injective]
        exact ⟨v, hv, hvx, hy.symm⟩
  · -- `y` is in the saturation if it is in `U`, or if it is glued to a point of `U₁`; the
    -- gluing read from the second summand is again the inversion, an involution.
    have hW := h₂.isOpenMap _
      (hinv.isOpen_inter_preimage isOpen_compl_singleton (hU₁'.preimage h₁.continuous))
    convert hU₂.union (hW.preimage continuous_subtype_val) using 1
    refine Set.ext fun y ↦ ?_
    simp only [mem_union, mem_preimage, mem_image, U₁]
    constructor
    · rintro ⟨x | y', hU, hxy⟩
      · rw [mk_inl, mk_inr, inl_eq_inr_iff h₁.injective h₂.injective] at hxy
        obtain ⟨v, hv, hvx, hvy⟩ := hxy
        refine Or.inr ⟨inversion 0 1 v, ⟨by simpa [inversion_eq_center one_ne_zero] using hv, x,
          hU, ?_⟩, hvy⟩
        rw [inversion_inversion (0 : E) one_ne_zero, hvx]
      · rw [mk_inr, mk_inr, (inr_injective h₁.injective h₂.injective).eq_iff] at hxy
        exact Or.inl (hxy ▸ hU)
    · rintro (hy | ⟨w, ⟨hw, x, hxU, hx⟩, hwy⟩)
      · exact ⟨_, hy, rfl⟩
      · refine ⟨.inl x, hxU, ?_⟩
        rw [mk_inl, mk_inr, inl_eq_inr_iff h₁.injective h₂.injective]
        refine ⟨inversion 0 1 w, by simpa [inversion_eq_center one_ne_zero] using hw, hx.symm, ?_⟩
        rw [inversion_inversion (0 : E) one_ne_zero, hwy]

/-- The first punctured summand is an open subspace of the connected sum. -/
theorem isOpenEmbedding_inl (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    IsOpenEmbedding (inl e₁ e₂) :=
  .of_continuous_injective_isOpenMap (continuous_inl e₁ e₂)
    (inl_injective h₁.injective h₂.injective)
    ((isOpenQuotientMap_mk h₁ h₂).isOpenMap.comp isOpenMap_inl)

/-- The second punctured summand is an open subspace of the connected sum. -/
theorem isOpenEmbedding_inr (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    IsOpenEmbedding (inr e₁ e₂) :=
  .of_continuous_injective_isOpenMap (continuous_inr e₁ e₂)
    (inr_injective h₁.injective h₂.injective)
    ((isOpenQuotientMap_mk h₁ h₂).isOpenMap.comp isOpenMap_inr)

/-- The quotient map of the connected sum is a local homeomorphism: on each punctured summand, an
open subset of the disjoint union, it restricts to an open embedding. -/
theorem isLocalHomeomorph_mk (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    IsLocalHomeomorph (mk e₁ e₂) := by
  have hopen := (isOpenQuotientMap_mk h₁ h₂).isOpenMap
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.2 fun p ↦ ?_
  -- The summand containing `p` is an open neighbourhood on which `mk` is injective.
  have key : ∀ U : Set (puncture e₁ ⊕ puncture e₂), IsOpen U → p ∈ U →
      InjOn (mk e₁ e₂) U → ∃ U ∈ 𝓝 p, IsOpenEmbedding (U.domRestrict (mk e₁ e₂)) :=
    fun U hU hp hinj ↦ ⟨U, hU.mem_nhds hp, .of_continuous_injective_isOpenMap
      ((continuous_mk e₁ e₂).comp continuous_subtype_val) hinj.injective
      (hopen.comp hU.isOpenMap_subtype_val)⟩
  rcases p with x | y
  · refine key _ isOpen_range_inl ⟨x, rfl⟩ ?_
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ h
    exact congrArg _ (inl_injective h₁.injective h₂.injective (by simpa using h))
  · refine key _ isOpen_range_inr ⟨y, rfl⟩ ?_
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩ h
    exact congrArg _ (inr_injective h₁.injective h₂.injective (by simpa using h))

/-- A point of the first summand outside the first ball and a point of the second summand outside
the second ball are separated by open sets: the complements of the images of the closed unit
balls are disjoint once glued, since the inversion exchanges the inside and the outside of the
unit sphere. -/
private theorem separated_inl_inr [T2Space M] [T2Space N] [ProperSpace E]
    (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) {x : puncture e₁} {y : puncture e₂}
    (hx : (x : M) ∉ range e₁) (hy : (y : N) ∉ range e₂) :
    ∃ u v : Set (ConnectedSum e₁ e₂), IsOpen u ∧ IsOpen v ∧ inl e₁ e₂ x ∈ u ∧ inr e₁ e₂ y ∈ v ∧
      Disjoint u v := by
  have hK₁ : IsClosed (e₁ '' Metric.closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image h₁.continuous).isClosed
  have hK₂ : IsClosed (e₂ '' Metric.closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image h₂.continuous).isClosed
  refine ⟨inl e₁ e₂ '' ((↑) ⁻¹' (e₁ '' Metric.closedBall 0 1)ᶜ),
    inr e₁ e₂ '' ((↑) ⁻¹' (e₂ '' Metric.closedBall 0 1)ᶜ),
    (isOpenEmbedding_inl h₁ h₂).isOpenMap _ (hK₁.isOpen_compl.preimage continuous_subtype_val),
    (isOpenEmbedding_inr h₁ h₂).isOpenMap _ (hK₂.isOpen_compl.preimage continuous_subtype_val),
    ⟨x, fun ⟨v, _, hv⟩ ↦ hx ⟨v, hv⟩, rfl⟩, ⟨y, fun ⟨v, _, hv⟩ ↦ hy ⟨v, hv⟩, rfl⟩, ?_⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨x', hx', rfl⟩ ⟨y', hy', hxy⟩
    obtain ⟨v, hv, hvx, hvy⟩ := (inl_eq_inr_iff h₁.injective h₂.injective).1 hxy.symm
    simp only [mem_preimage, mem_compl_iff, ← hvx, ← hvy] at hx' hy'
    refine hy' ⟨_, ?_, rfl⟩
    have hv1 : 1 < ‖v‖ := not_le.1 fun h ↦ hx' ⟨v, by simpa using h, rfl⟩
    rw [Metric.mem_closedBall, dist_inversion_center, dist_zero_right]
    exact (div_le_one (by linarith)).2 (by linarith)

/-- A point of the first summand lies in the second exactly when it is in the punctured first
ball. -/
private theorem inl_mem_range_inr_of_mem_range (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) {x : puncture e₁} (hx : (x : M) ∈ range e₁) :
    inl e₁ e₂ x ∈ range (inr e₁ e₂) := by
  obtain ⟨v, hv⟩ := hx
  have hv0 : v ≠ 0 := by rintro rfl; exact x.2 hv.symm
  have hy : e₂ (inversion 0 1 v) ∈ puncture e₂ := by
    simpa [h₂.injective.eq_iff, inversion_eq_center one_ne_zero] using hv0
  refine ⟨⟨_, hy⟩, ?_⟩
  rw [eq_comm, inl_eq_inr_iff h₁.injective h₂.injective]
  exact ⟨v, hv0, hv, rfl⟩

/-- A point of the second summand lies in the first exactly when it is in the punctured second
ball. -/
private theorem inr_mem_range_inl_of_mem_range (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) {y : puncture e₂} (hy : (y : N) ∈ range e₂) :
    inr e₁ e₂ y ∈ range (inl e₁ e₂) := by
  obtain ⟨w, hw⟩ := hy
  have hw0 : w ≠ 0 := by rintro rfl; exact y.2 hw.symm
  have hx : e₁ (inversion 0 1 w) ∈ puncture e₁ := by
    simpa [h₁.injective.eq_iff, inversion_eq_center one_ne_zero] using hw0
  refine ⟨⟨_, hx⟩, ?_⟩
  rw [inl_eq_inr_iff h₁.injective h₂.injective]
  refine ⟨inversion 0 1 w, by simpa [inversion_eq_center one_ne_zero] using hw0, rfl, ?_⟩
  rw [inversion_inversion (0 : E) one_ne_zero, hw]

/-- **The connected sum of Hausdorff spaces is Hausdorff**, for balls modelled on a
finite-dimensional space. -/
theorem t2Space [T2Space M] [T2Space N] [ProperSpace E] (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) : T2Space (ConnectedSum e₁ e₂) := by
  refine ⟨fun p q hpq ↦ ?_⟩
  have hcov := range_inl_union_range_inr e₁ e₂
  -- Points in a common summand are separated there; otherwise each lies outside the other ball.
  by_cases hp : p ∈ range (inl e₁ e₂) <;> by_cases hq : q ∈ range (inl e₁ e₂)
  · obtain ⟨x, rfl⟩ := hp
    obtain ⟨x', rfl⟩ := hq
    exact separated_by_isOpenEmbedding (isOpenEmbedding_inl h₁ h₂) (ne_of_apply_ne _ hpq)
  · have hq' : q ∈ range (inr e₁ e₂) := (hcov.symm ▸ mem_univ q).resolve_left hq
    by_cases hp' : p ∈ range (inr e₁ e₂)
    · obtain ⟨y, rfl⟩ := hp'
      obtain ⟨y', rfl⟩ := hq'
      exact separated_by_isOpenEmbedding (isOpenEmbedding_inr h₁ h₂) (ne_of_apply_ne _ hpq)
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq'
    exact separated_inl_inr h₁ h₂ (fun h ↦ hp' (inl_mem_range_inr_of_mem_range h₁ h₂ h))
      fun h ↦ hq (inr_mem_range_inl_of_mem_range h₁ h₂ h)
  · have hp' : p ∈ range (inr e₁ e₂) := (hcov.symm ▸ mem_univ p).resolve_left hp
    by_cases hq' : q ∈ range (inr e₁ e₂)
    · obtain ⟨y, rfl⟩ := hp'
      obtain ⟨y', rfl⟩ := hq'
      exact separated_by_isOpenEmbedding (isOpenEmbedding_inr h₁ h₂) (ne_of_apply_ne _ hpq)
    obtain ⟨y, rfl⟩ := hp'
    obtain ⟨x, rfl⟩ := hq
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := separated_inl_inr h₁ h₂
      (fun h ↦ hq' (inl_mem_range_inr_of_mem_range h₁ h₂ h))
      fun h ↦ hp (inr_mem_range_inl_of_mem_range h₁ h₂ h)
    exact ⟨v, u, hv, hu, hyv, hxu, huv.symm⟩
  · have hp' : p ∈ range (inr e₁ e₂) := (hcov.symm ▸ mem_univ p).resolve_left hp
    have hq' : q ∈ range (inr e₁ e₂) := (hcov.symm ▸ mem_univ q).resolve_left hq
    obtain ⟨y, rfl⟩ := hp'
    obtain ⟨y', rfl⟩ := hq'
    exact separated_by_isOpenEmbedding (isOpenEmbedding_inr h₁ h₂) (ne_of_apply_ne _ hpq)

end ConnectedSum

end TauCeti
