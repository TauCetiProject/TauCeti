/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import TauCeti.GroupTheory.BruhatTits.AffineRoot
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Order.Interval.Finite

/-!
# Walls, alcoves and facets of the apartment

Let `φ` be a valuation of a root datum and `A(φ)` its apartment. Every affine root `α` is an
affine function on `A(φ)`, with wall `{α = 0}`. Two points lie in the same *facet* if every
affine root has the same sign (`-1`, `0` or `1`) at both of them; the facets partition the
apartment. The common sign of `α` on a facet `F` is `F.sign α`.

* An *alcove* is a facet meeting no wall, equivalently one on which no affine root vanishes.
* Facets are ordered by `F ≤ F'` if, for every affine root, its sign on `F` is `0` or its sign
  on `F'`. This is the closure order: `F ≤ F'` exactly when, for `x ∈ F` and `y ∈ F'`, every
  point `x + t (y - x)` with `0 < t ≤ 1` lies in `F'` (`Facet.le_iff_forall_lineMap_mem`).
* A point is *special* if, for every root `a`, some wall through it has gradient a positive
  multiple of `a`.

Facets are convex, and two points off the walls lie in the same alcove exactly when the segment
joining them meets no wall (`Facet.facet_eq_facet_iff_of_notMem_wall`): alcoves are the
connected pieces of the complement of the walls, in segment form.

For a discrete valuation with finitely many roots the walls are locally finite: a closed segment
meets the walls of only finitely many affine roots
(`AffineRoot.finite_setOf_exists_lineMap_mem_wall`). Consequently a segment leaving a point
stays in one facet for a short time (`Facet.exists_forall_facet_lineMap_eq`), every facet lies
in the closure of an alcove (`Facet.exists_isAlcove_le`), and the alcoves are exactly the
maximal facets (`Facet.isAlcove_iff_isMax`).

## Main definitions

* `TauCeti.BruhatTits.Facet`: the facets of the apartment, the sign classes of points.
* `TauCeti.BruhatTits.Apartment.facet`: the facet of a point.
* `TauCeti.BruhatTits.Facet.carrier`: the points of a facet.
* `TauCeti.BruhatTits.Facet.sign`: the sign of an affine root on a facet.
* `TauCeti.BruhatTits.Facet.wall`: the union of the walls of all affine roots.
* `TauCeti.BruhatTits.Facet.IsAlcove`: a facet meeting no wall.
* `TauCeti.BruhatTits.Facet.instPartialOrder`: the closure order on facets.
* `TauCeti.BruhatTits.Apartment.IsSpecial`: special points.

## Main results

* `TauCeti.BruhatTits.Facet.existsUnique_mem_carrier`: every point lies in exactly one facet.
* `TauCeti.BruhatTits.Facet.le_iff_forall_lineMap_mem`: the order is the closure order.
* `TauCeti.BruhatTits.Facet.facet_eq_facet_iff_of_notMem_wall`: alcoves in segment form.
* `TauCeti.BruhatTits.AffineRoot.finite_setOf_exists_lineMap_mem_wall`: local finiteness of
  walls.
* `TauCeti.BruhatTits.Facet.exists_isAlcove_le` and `TauCeti.BruhatTits.Facet.isAlcove_iff_isMax`.
* `TauCeti.BruhatTits.Apartment.IsSpecial.not_isAlcove`: a special point lies in no alcove.

## Implementation notes

Facets are defined by the sign pattern of the affine roots for every valuation. For a dense
valuation the facets of [Bruhat–Tits I], 7.2.4, are germs of sets, which sign classes do not
model; for a discrete valuation with finitely many roots they are the facets of
[Bruhat–Tits I], 1.3.3. The order is stated with signs rather than with closed half-apartments,
so that it is the closure order without using that the affine roots are stable under negation.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  1.3.1–1.3.7, pp. 19–22, and 7.2.1–7.2.7, pp. 161–163.
-/

public section

open AffineMap Set

namespace TauCeti.BruhatTits

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  {P : RootPairing ι ℝ M N} {G : Type*} [Group G] {D : RootDatum P G} {φ : Valuation D}

/-! ### Affine roots along segments -/

namespace AffineRoot

/-- An affine root restricted to a segment is the affine interpolation of its endpoint values. -/
@[simp]
theorem eval_lineMap (α : AffineRoot φ) (x y : Apartment φ) (t : ℝ) :
    α.eval (lineMap x y t) = lineMap (α.eval x) (α.eval y) t := by
  have h := α.toAffineMap.apply_lineMap x y t
  simp only [toAffineMap_apply] at h
  exact h

/-- On a segment from `x` to `y`, an affine root has the sign it has at `y` at every point other
than `x`, provided its sign at `x` is `0` or its sign at `y`. -/
theorem sign_eval_lineMap {α : AffineRoot φ} {x y : Apartment φ}
    (h : SignType.sign (α.eval x) = 0 ∨ SignType.sign (α.eval x) = SignType.sign (α.eval y))
    {t : ℝ} (ht : t ∈ Ioc 0 1) :
    SignType.sign (α.eval (lineMap x y t)) = SignType.sign (α.eval y) := by
  obtain ⟨ht0, ht1⟩ := ht
  rw [eval_lineMap, lineMap_apply_ring']
  set a := α.eval x
  set b := α.eval y
  rcases lt_trichotomy a 0 with ha | ha | ha <;> rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [sign_neg hb, sign_neg (by nlinarith)]
  · simp [sign_neg ha, hb] at h
  · simp [sign_neg ha, sign_pos hb] at h
  · rw [sign_neg hb, sign_neg (by simp [ha]; nlinarith)]
  · simp [ha, hb]
  · rw [sign_pos hb, sign_pos (by simp [ha]; nlinarith)]
  · simp [sign_pos ha, sign_neg hb] at h
  · simp [sign_pos ha, hb] at h
  · rw [sign_pos hb, sign_pos (by nlinarith)]

/-- An affine root which vanishes nowhere on the part of a segment between the parameters `s`
and `t` has the same sign at both ends. -/
theorem sign_eval_lineMap_eq_of_forall_ne_zero {α : AffineRoot φ} {x y : Apartment φ} {s t : ℝ}
    (hst : s ≤ t) (h : ∀ r ∈ Icc s t, α.eval (lineMap x y r) ≠ 0) :
    SignType.sign (α.eval (lineMap x y s)) = SignType.sign (α.eval (lineMap x y t)) := by
  have hcont : ContinuousOn (fun r : ℝ ↦ α.eval (lineMap x y r)) (Icc s t) := by
    simp only [eval_lineMap, lineMap_apply_ring']
    fun_prop
  have hs := h s (left_mem_Icc.mpr hst)
  have ht := h t (right_mem_Icc.mpr hst)
  rcases hs.lt_or_gt with hs' | hs' <;> rcases ht.lt_or_gt with ht' | ht'
  · rw [sign_neg hs', sign_neg ht']
  · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hst hcont (mem_Icc.mpr ⟨hs'.le, ht'.le⟩)
    exact absurd hr0 (h r hr)
  · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hst hcont (mem_Icc.mpr ⟨ht'.le, hs'.le⟩)
    exact absurd hr0 (h r hr)
  · rw [sign_pos hs', sign_pos ht']

/-- If an affine root has a constant sign `σ` on the points `x + t (y - x)` with `0 < t ≤ 1`,
then its sign at `x` is `0` or `σ`. -/
theorem sign_eval_eq_zero_or_of_forall_lineMap {α : AffineRoot φ} {x y : Apartment φ}
    {σ : SignType} (h : ∀ t ∈ Ioc (0 : ℝ) 1, SignType.sign (α.eval (lineMap x y t)) = σ) :
    SignType.sign (α.eval x) = 0 ∨ SignType.sign (α.eval x) = σ := by
  have h1 := h 1 ⟨one_pos, le_rfl⟩
  rw [lineMap_apply_one] at h1
  subst h1
  set a := α.eval x
  set b := α.eval y
  -- If `a ≠ 0` and `b` does not have the sign of `a`, the point at parameter
  -- `a / (2 (a - b)) ∈ (0, 1]` has value `a / 2`, of the sign of `a`.
  have hmid (hab : a - b ≠ 0) : α.eval (lineMap x y (a / (2 * (a - b)))) = a / 2 := by
    rw [eval_lineMap, lineMap_apply_ring']
    field_simp
    ring
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_or_ge b 0 with hb | hb
    · exact Or.inr (by rw [sign_neg ha, sign_neg hb])
    · have hab : a - b < 0 := by linarith
      have ht := h _ ⟨div_pos_of_neg_of_neg ha (by linarith),
        (div_le_one_of_neg (show 2 * (a - b) < 0 by linarith)).mpr (by linarith)⟩
      rw [hmid hab.ne, sign_neg (by linarith)] at ht
      exact absurd (sign_eq_neg_one_iff.mp ht.symm) hb.not_gt
  · exact Or.inl (by simp [ha])
  · rcases le_or_gt b 0 with hb | hb
    · have hab : 0 < a - b := by linarith
      have ht := h _ ⟨div_pos ha (by linarith),
        (div_le_one (show 0 < 2 * (a - b) by linarith)).mpr (by linarith)⟩
      rw [hmid hab.ne', sign_pos (by linarith)] at ht
      exact absurd (sign_eq_one_iff.mp ht.symm) hb.not_gt
    · exact Or.inr (by rw [sign_pos ha, sign_pos hb])

/-! ### Discrete valuations: local finiteness of the walls -/

section Discrete

variable [Finite ι]

/-- **Local finiteness of the walls.** For a discrete valuation with finitely many roots, a
closed segment meets the walls of only finitely many affine roots. -/
theorem finite_setOf_exists_lineMap_mem_wall
    (hφ : φ.IsDiscrete) (x y : Apartment φ) :
    {α : AffineRoot φ | ∃ t ∈ Icc (0 : ℝ) 1, lineMap x y t ∈ α.wall}.Finite := by
  -- On the segment, the root `a` takes values between `a (x - φ)` and `a (y - φ)`, so the
  -- constant of an affine root with gradient `a` vanishing there lies in a bounded interval.
  let S : Set (ι × ℝ) := ⋃ i, Prod.mk i '' (φ.valueSet i ∩
    Icc (-max (P.root' i x.displacement) (P.root' i y.displacement))
      (-min (P.root' i x.displacement) (P.root' i y.displacement)))
  have hS : S.Finite := Set.finite_iUnion fun i ↦ (φ.isDiscrete_iff.mp hφ i _ _).image _
  refine (hS.preimage (f := fun α : AffineRoot φ ↦ (α.gradient, α.constant))
    fun α _ β _ h ↦ AffineRoot.ext (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2).subset ?_
  rintro α ⟨t, ⟨ht0, ht1⟩, hw⟩
  refine mem_iUnion.mpr ⟨α.gradient, α.constant,
    ⟨φ.primedValueSet_subset_valueSet _ α.constant_mem, ?_⟩, rfl⟩
  rw [mem_wall_iff, eval_lineMap, eval_def, eval_def, lineMap_apply_ring'] at hw
  rcases le_total (P.root' α.gradient x.displacement) (P.root' α.gradient y.displacement) with h | h
  · rw [max_eq_right h, min_eq_left h]
    constructor <;> nlinarith
  · rw [max_eq_left h, min_eq_right h]
    constructor <;> nlinarith

/-- For a discrete valuation with finitely many roots, only finitely many walls pass through a
point. -/
theorem finite_setOf_mem_wall (hφ : φ.IsDiscrete)
    (x : Apartment φ) : {α : AffineRoot φ | x ∈ α.wall}.Finite :=
  (finite_setOf_exists_lineMap_mem_wall hφ x x).subset fun _ h ↦
    ⟨0, left_mem_Icc.mpr zero_le_one, by simpa using h⟩

end Discrete

end AffineRoot

/-! ### Facets -/

namespace Apartment

variable (φ) in
/-- Two points of the apartment are related when every affine root has the same sign at both. -/
noncomputable def facetSetoid : Setoid (Apartment φ) :=
  Setoid.ker fun x (α : AffineRoot φ) ↦ SignType.sign (α.eval x)

end Apartment

variable (φ) in
/-- The facets of the apartment of `φ`: the classes of points at which every affine root has the
same sign. -/
def Facet : Type _ :=
  Quotient (Apartment.facetSetoid φ)

namespace Apartment

/-- The facet containing a point of the apartment. -/
noncomputable def facet (x : Apartment φ) : Facet φ :=
  Quotient.mk _ x

/-- Every facet is the facet of one of its points. -/
theorem facet_surjective : Function.Surjective (facet (φ := φ)) :=
  Quotient.mk_surjective

/-- Two points lie in the same facet if and only if every affine root has the same sign at
them. -/
theorem facet_eq_facet_iff {x y : Apartment φ} :
    x.facet = y.facet ↔ ∀ α : AffineRoot φ, SignType.sign (α.eval x) = SignType.sign (α.eval y) :=
  Quotient.eq.trans funext_iff

end Apartment

namespace Facet

open Apartment

/-- Induction on facets: a property of all facets of points is a property of all facets. -/
@[elab_as_elim]
theorem ind {p : Facet φ → Prop} (h : ∀ x : Apartment φ, p x.facet) (F : Facet φ) : p F :=
  Quotient.ind h F

/-- The sign of an affine root on a facet, its common sign at the points of the facet. -/
noncomputable def sign (F : Facet φ) (α : AffineRoot φ) : SignType :=
  Quotient.lift (fun x : Apartment φ ↦ SignType.sign (α.eval x)) (fun _ _ h ↦ congrFun h α) F

@[simp]
theorem sign_facet (x : Apartment φ) (α : AffineRoot φ) :
    x.facet.sign α = SignType.sign (α.eval x) :=
  (rfl)

/-- A facet is determined by the signs of the affine roots on it. -/
theorem ext_sign {F F' : Facet φ} (h : ∀ α, F.sign α = F'.sign α) : F = F' := by
  induction F using Facet.ind with | h x => ?_
  induction F' using Facet.ind with | h y => ?_
  exact facet_eq_facet_iff.mpr fun α ↦ by simpa using h α

/-- The points of a facet. -/
def carrier (F : Facet φ) : Set (Apartment φ) :=
  {x | x.facet = F}

@[simp]
theorem mem_carrier {F : Facet φ} {x : Apartment φ} : x ∈ F.carrier ↔ x.facet = F :=
  Iff.rfl

/-- A point lies in a facet exactly when every affine root has, at it, its sign on the facet. -/
theorem mem_carrier_iff_sign {F : Facet φ} {x : Apartment φ} :
    x ∈ F.carrier ↔ ∀ α, SignType.sign (α.eval x) = F.sign α := by
  induction F using Facet.ind with | h y => ?_
  simp [facet_eq_facet_iff]

/-- The facet of `x` is the full class of points at which every affine root has its sign at
`x`. -/
theorem mem_carrier_iff {x y : Apartment φ} :
    y ∈ x.facet.carrier ↔ ∀ α : AffineRoot φ, SignType.sign (α.eval y) = SignType.sign (α.eval x) :=
  facet_eq_facet_iff

theorem mem_carrier_facet (x : Apartment φ) : x ∈ x.facet.carrier :=
  mem_carrier.mpr rfl

theorem carrier_nonempty (F : Facet φ) : F.carrier.Nonempty :=
  (facet_surjective F).imp fun _ ↦ id

/-- Every point of the apartment lies in exactly one facet. -/
theorem existsUnique_mem_carrier (x : Apartment φ) : ∃! F : Facet φ, x ∈ F.carrier :=
  ⟨x.facet, rfl, fun _ h ↦ h.symm⟩

theorem carrier_injective : Function.Injective (carrier (φ := φ)) := fun F F' h ↦ by
  obtain ⟨x, hx⟩ := F.carrier_nonempty
  exact hx.symm.trans (h ▸ hx : x ∈ F'.carrier)

/-- An affine root has the same sign at all points of a facet. -/
theorem sign_eval_of_mem_carrier {F : Facet φ} {x : Apartment φ} (hx : x ∈ F.carrier)
    (α : AffineRoot φ) : SignType.sign (α.eval x) = F.sign α :=
  mem_carrier_iff_sign.mp hx α

/-! ### Walls and alcoves -/

variable (φ) in
/-- The union of the walls of all affine roots. -/
def wall : Set (Apartment φ) :=
  ⋃ α : AffineRoot φ, α.wall

@[simp]
theorem mem_wall_iff {x : Apartment φ} : x ∈ wall φ ↔ ∃ α : AffineRoot φ, α.eval x = 0 := by
  simp [wall]

/-- An alcove is a facet meeting no wall. -/
def IsAlcove (F : Facet φ) : Prop :=
  Disjoint F.carrier (wall φ)

/-- A facet is an alcove exactly when no affine root vanishes on it. -/
theorem isAlcove_iff_sign_ne_zero {F : Facet φ} : F.IsAlcove ↔ ∀ α, F.sign α ≠ 0 := by
  induction F using Facet.ind with | h x => ?_
  simp only [IsAlcove, Set.disjoint_left, mem_carrier, mem_wall_iff, not_exists, sign_facet,
    ne_eq, sign_eq_zero_iff]
  refine ⟨fun h α ↦ h rfl α, fun h y hy α ↦ ?_⟩
  rw [← sign_eq_zero_iff, ← sign_facet, hy, sign_facet, sign_eq_zero_iff]
  exact h α

/-- The facet of a point is an alcove exactly when the point lies on no wall. -/
@[simp]
theorem isAlcove_facet_iff {x : Apartment φ} : x.facet.IsAlcove ↔ x ∉ wall φ := by
  simp [isAlcove_iff_sign_ne_zero]

/-! ### The closure order -/

/-- Facets are ordered by `F ≤ F'` if every affine root has sign `0` on `F` or the same sign on
`F` and on `F'`. This says that `F` lies in the closure of `F'`
(`Facet.le_iff_forall_lineMap_mem`). -/
instance instPartialOrder : PartialOrder (Facet φ) where
  le F F' := ∀ α, F.sign α = 0 ∨ F.sign α = F'.sign α
  le_refl _ _ := Or.inr rfl
  le_trans _ _ _ h h' α := (h α).elim Or.inl fun e ↦ e ▸ h' α
  le_antisymm _ _ h h' := ext_sign fun α ↦ by
    rcases h α with e | e <;> rcases h' α with e' | e' <;> simp_all

theorem le_def {F F' : Facet φ} : F ≤ F' ↔ ∀ α, F.sign α = 0 ∨ F.sign α = F'.sign α :=
  Iff.rfl

/-- If `F ≤ F'`, every affine root which is nonnegative on `F'` is nonnegative on `F`. -/
theorem carrier_subset_halfApartment_of_le {F F' : Facet φ} (h : F ≤ F') {α : AffineRoot φ}
    (hα : F'.carrier ⊆ α.halfApartment) : F.carrier ⊆ α.halfApartment := by
  obtain ⟨y, hy⟩ := F'.carrier_nonempty
  intro x hx
  have hy' : 0 ≤ SignType.sign (α.eval y) :=
    sign_nonneg_iff.mpr (AffineRoot.mem_halfApartment_iff.mp (hα hy))
  rw [AffineRoot.mem_halfApartment_iff, ← sign_nonneg_iff, sign_eval_of_mem_carrier hx]
  rw [sign_eval_of_mem_carrier hy] at hy'
  rcases h α with e | e
  · exact e.symm.le
  · exact e ▸ hy'

/-- If `F ≤ F'`, `x ∈ F` and `y ∈ F'`, the points `x + t (y - x)` with `0 < t ≤ 1` lie
in `F'`. -/
theorem lineMap_mem_carrier_of_le {F F' : Facet φ} (h : F ≤ F') {x y : Apartment φ}
    (hx : x ∈ F.carrier) (hy : y ∈ F'.carrier) {t : ℝ} (ht : t ∈ Ioc 0 1) :
    lineMap x y t ∈ F'.carrier := by
  rw [← hy, mem_carrier_iff]
  refine fun α ↦ AffineRoot.sign_eval_lineMap ?_ ht
  rw [sign_eval_of_mem_carrier hx, sign_eval_of_mem_carrier hy]
  exact h α

/-- If the points `x + t (y - x)` with `0 < t ≤ 1` lie in `F'`, the facet of `x` lies in the
closure of `F'`. -/
theorem le_of_forall_lineMap_mem {F F' : Facet φ} {x y : Apartment φ} (hx : x ∈ F.carrier)
    (h : ∀ t ∈ Ioc (0 : ℝ) 1, lineMap x y t ∈ F'.carrier) : F ≤ F' := fun α ↦ by
  rw [← sign_eval_of_mem_carrier hx]
  exact AffineRoot.sign_eval_eq_zero_or_of_forall_lineMap fun t ht ↦
    sign_eval_of_mem_carrier (h t ht) α

/-- The order on facets is the closure order: `F ≤ F'` if and only if, for all `x ∈ F` and
`y ∈ F'`, the half-open segment from `x` to `y` without `x` lies in `F'`. -/
theorem le_iff_forall_lineMap_mem {F F' : Facet φ} :
    F ≤ F' ↔ ∀ x ∈ F.carrier, ∀ y ∈ F'.carrier, ∀ t ∈ Ioc (0 : ℝ) 1,
      lineMap x y t ∈ F'.carrier := by
  refine ⟨fun h x hx y hy t ht ↦ lineMap_mem_carrier_of_le h hx hy ht, fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := F.carrier_nonempty
  obtain ⟨y, hy⟩ := F'.carrier_nonempty
  exact le_of_forall_lineMap_mem hx (h x hx y hy)

/-- Facets are convex. -/
theorem lineMap_mem_carrier {F : Facet φ} {x y : Apartment φ} (hx : x ∈ F.carrier)
    (hy : y ∈ F.carrier) {t : ℝ} (ht : t ∈ Icc 0 1) : lineMap x y t ∈ F.carrier := by
  rcases ht.1.eq_or_lt with rfl | ht0
  · simpa using hx
  · exact lineMap_mem_carrier_of_le le_rfl hx hy ⟨ht0, ht.2⟩

/-- An alcove lies in the closure of no other facet. -/
theorem IsAlcove.eq_of_le {C F : Facet φ} (hC : C.IsAlcove) (h : C ≤ F) : C = F :=
  ext_sign fun α ↦ (h α).resolve_left (isAlcove_iff_sign_ne_zero.mp hC α)

/-- Alcoves are maximal facets. -/
theorem IsAlcove.isMax {C : Facet φ} (hC : C.IsAlcove) : IsMax C :=
  fun _ h ↦ (hC.eq_of_le h).ge

/-- Two points off the walls lie in the same alcove if and only if the segment joining them
meets no wall. -/
theorem facet_eq_facet_iff_of_notMem_wall {x y : Apartment φ} (hx : x ∉ wall φ) :
    x.facet = y.facet ↔ ∀ t ∈ Icc (0 : ℝ) 1, lineMap x y t ∉ wall φ := by
  constructor
  · intro h t ht hw
    have hC : x.facet.IsAlcove := isAlcove_facet_iff.mpr hx
    exact Set.disjoint_left.mp hC (lineMap_mem_carrier rfl h.symm ht) hw
  · intro h
    refine facet_eq_facet_iff.mpr fun α ↦ ?_
    simpa using AffineRoot.sign_eval_lineMap_eq_of_forall_ne_zero zero_le_one
      fun t ht hα ↦ h t ht (mem_wall_iff.mpr ⟨α, hα⟩)

/-! ### Discrete valuations: facets along segments and alcoves -/

section Discrete

variable [Finite ι]

/-- For a discrete valuation with finitely many roots, a segment leaving `x` towards `y` stays in
one facet for a short time: the points `x + t (y - x)` with `0 < t ≤ ε` share their facet. -/
theorem exists_forall_facet_lineMap_eq (hφ : φ.IsDiscrete) (x y : Apartment φ) :
    ∃ ε ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Ioc 0 ε, (lineMap x y t).facet = (lineMap x y ε).facet := by
  let W := {α : AffineRoot φ | ∃ t ∈ Icc (0 : ℝ) 1, lineMap x y t ∈ α.wall}
  have hW : W.Finite := AffineRoot.finite_setOf_exists_lineMap_mem_wall hφ x y
  -- The parameters at which an affine root not vanishing at `x` vanishes on the segment; each
  -- such root vanishes at most once.
  let Z := ⋃ α ∈ W, {t : ℝ | α.eval x ≠ 0 ∧ α.eval (lineMap x y t) = 0}
  have hZ : Z.Finite := hW.biUnion fun α _ ↦ Set.Subsingleton.finite fun t₁ h₁ t₂ h₂ ↦ by
    obtain ⟨ha, h₁⟩ := h₁
    have h₂ := h₂.2
    rw [AffineRoot.eval_lineMap, lineMap_apply_ring'] at h₁ h₂
    have hba : α.eval y - α.eval x ≠ 0 := fun h ↦ ha (by rw [h, mul_zero, zero_add] at h₁; exact h₁)
    exact mul_right_cancel₀ hba (by linarith)
  obtain ⟨c, hc0, hc⟩ :=
    TauCeti.exists_lt_forall_le_of_finite_inter_Ioo zero_lt_one (hZ.subset inter_subset_left)
  have hε : 0 < min (c / 2) 1 := lt_min (half_pos hc0) one_pos
  refine ⟨min (c / 2) 1, ⟨hε, min_le_right _ _⟩, fun t ht ↦ facet_eq_facet_iff.mpr fun α ↦ ?_⟩
  rcases eq_or_ne (α.eval x) 0 with h0 | h0
  · have hx : SignType.sign (α.eval x) = 0 := by simp [h0]
    rw [AffineRoot.sign_eval_lineMap (Or.inl hx) ⟨ht.1, ht.2.trans (min_le_right _ _)⟩,
      AffineRoot.sign_eval_lineMap (Or.inl hx) ⟨hε, min_le_right _ _⟩]
  · refine AffineRoot.sign_eval_lineMap_eq_of_forall_ne_zero ht.2 fun r hr hr0 ↦ ?_
    have hr0' : 0 < r := ht.1.trans_le hr.1
    have hr1 : r ≤ 1 := hr.2.trans (min_le_right _ _)
    have hrZ : r ∈ Z :=
      mem_biUnion (x := α) ⟨r, ⟨hr0'.le, hr1⟩, AffineRoot.mem_wall_iff.mpr hr0⟩ ⟨h0, hr0⟩
    linarith [hc r hrZ hr0', hr.2.trans (min_le_left _ _)]

/-- For a discrete valuation with finitely many roots, every facet lies in the closure of an
alcove. -/
theorem exists_isAlcove_le (hφ : φ.IsDiscrete) (F : Facet φ) :
    ∃ C : Facet φ, C.IsAlcove ∧ F ≤ C := by
  obtain ⟨x, rfl⟩ := facet_surjective F
  -- A direction on which no root vanishes.
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists (fun i ↦ P.root' i)
    fun i ↦ ⟨P.coroot i, by simp⟩
  obtain ⟨ε, hε, hconst⟩ := exists_forall_facet_lineMap_eq hφ x (v +ᵥ x)
  refine ⟨(lineMap x (v +ᵥ x) ε).facet, isAlcove_iff_sign_ne_zero.mpr fun α hα ↦ ?_,
    le_of_forall_lineMap_mem (y := lineMap x (v +ᵥ x) ε) (mem_carrier_facet x) fun t ht ↦ ?_⟩
  · -- An affine root vanishing at the parameters `ε / 2` and `ε` is constant along `v`.
    have h2 := congrArg (sign · α) (hconst (ε / 2) ⟨half_pos hε.1, half_le_self hε.1.le⟩)
    simp only [sign_facet] at hα h2
    rw [hα, sign_eq_zero_iff] at h2
    rw [sign_eq_zero_iff] at hα
    rw [AffineRoot.eval_lineMap, lineMap_apply_ring', AffineRoot.eval_vadd] at hα h2
    have : ε * P.root' α.gradient v = 0 := by linarith
    exact hv α.gradient ((mul_eq_zero.mp this).resolve_left hε.1.ne')
  · rw [mem_carrier, lineMap_lineMap_right]
    exact hconst _ ⟨mul_pos ht.1 hε.1, mul_le_of_le_one_left hε.1.le ht.2⟩

/-- For a discrete valuation with finitely many roots, the alcoves are exactly the maximal
facets. -/
theorem isAlcove_iff_isMax (hφ : φ.IsDiscrete) {F : Facet φ} : F.IsAlcove ↔ IsMax F := by
  refine ⟨IsAlcove.isMax, fun h ↦ ?_⟩
  obtain ⟨C, hC, hle⟩ := exists_isAlcove_le hφ F
  rwa [le_antisymm hle (h hle)]

end Discrete

/-! ### Rank zero -/

section RankZero

variable [IsEmpty ι]

/-- With no roots, the whole apartment is a single facet. -/
instance : Subsingleton (Facet φ) :=
  ⟨fun _ _ ↦ ext_sign isEmptyElim⟩

/-- With no roots, the single facet is an alcove. -/
theorem isAlcove_of_isEmpty (F : Facet φ) : F.IsAlcove :=
  isAlcove_iff_sign_ne_zero.mpr isEmptyElim

end RankZero

end Facet


/-! ### Special points -/

namespace Apartment

/-- A point `x` of the apartment is *special* if, for every root `a`, some wall through `x` has
gradient a positive multiple of `a`; equivalently, every root direction is the direction of a
wall through `x`. -/
def IsSpecial (x : Apartment φ) : Prop :=
  ∀ i, ∃ α : AffineRoot φ, x ∈ α.wall ∧ ∃ c : ℝ, 0 < c ∧ P.root α.gradient = c • P.root i

theorem isSpecial_iff {x : Apartment φ} :
    x.IsSpecial ↔
      ∀ i, ∃ α : AffineRoot φ, x ∈ α.wall ∧ ∃ c : ℝ, 0 < c ∧ P.root α.gradient = c • P.root i :=
  Iff.rfl

/-- Being special depends only on the facet: the walls through two points of one facet agree. -/
theorem IsSpecial.of_facet_eq {x y : Apartment φ} (hx : x.IsSpecial) (h : x.facet = y.facet) :
    y.IsSpecial := fun i ↦ by
  obtain ⟨α, hα, hgrad⟩ := hx i
  refine ⟨α, ?_, hgrad⟩
  rw [AffineRoot.mem_wall_iff, ← sign_eq_zero_iff, ← (facet_eq_facet_iff.mp h α), sign_eq_zero_iff]
  exact AffineRoot.mem_wall_iff.mp hα

/-- Once there is a root, a special point lies on a wall. -/
theorem IsSpecial.mem_wall [Nonempty ι] {x : Apartment φ} (hx : x.IsSpecial) : x ∈ Facet.wall φ :=
  let ⟨α, hα, _⟩ := hx (Classical.arbitrary ι)
  Facet.mem_wall_iff.mpr ⟨α, AffineRoot.mem_wall_iff.mp hα⟩

/-- Once there is a root, the facet of a special point is not an alcove. -/
theorem IsSpecial.not_isAlcove [Nonempty ι] {x : Apartment φ} (hx : x.IsSpecial) :
    ¬ x.facet.IsAlcove :=
  fun h ↦ Facet.isAlcove_facet_iff.mp h hx.mem_wall

/-- With no roots, every point is special. -/
theorem isSpecial_of_isEmpty [IsEmpty ι] (x : Apartment φ) : x.IsSpecial :=
  isEmptyElim

end Apartment

end TauCeti.BruhatTits
