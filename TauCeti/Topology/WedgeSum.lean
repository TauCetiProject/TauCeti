/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# The wedge sum of a family of pointed spaces

The wedge sum `⋁ᵢ Xᵢ` of a family of pointed spaces `(Xᵢ, xᵢ)` is the disjoint union of the
`Xᵢ` with all the base points `xᵢ` identified to a single wedge point, carrying the quotient
topology.  A wedge of circles is the basic example: its fundamental group is the free group on
the circles, computed from the Seifert--van Kampen theorem in
`TauCeti.AlgebraicTopology.FundamentalGroup.WedgeSum`.

The wedge point is added as a separate point before taking the quotient, so the wedge sum of the
empty family is a point rather than empty.  Concretely the wedge sum is the quotient of
`Unit ⊕ Σ i, X i` by the kernel of the normalization which replaces each base point by the extra
point; the quotient presentation is private, and the wedge sum is used through the wedge point
`TauCeti.WedgeSum.base`, the inclusions `TauCeti.WedgeSum.incl` of the summands, which points they
identify (`TauCeti.WedgeSum.incl_eq_incl_iff`), the induction principle `TauCeti.WedgeSum.ind` and
the universal property `TauCeti.WedgeSum.lift`.

## Main declarations

* `TauCeti.WedgeSum`: the wedge sum of a family of pointed spaces, with its wedge point
  `TauCeti.WedgeSum.base` and the inclusions `TauCeti.WedgeSum.incl` of the summands.
* `TauCeti.WedgeSum.isOpen_iff`: a set is open exactly when its preimage in every summand is.
* `TauCeti.WedgeSum.lift`: the universal property, with `TauCeti.WedgeSum.hom_ext`, and
  `TauCeti.WedgeSum.liftProd`, its form for maps out of `Z × ⋁ᵢ Xᵢ`, which builds homotopies out
  of a wedge sum.
* `TauCeti.WedgeSum.subtypeVal` and `TauCeti.WedgeSum.isOpenEmbedding_subtypeVal`: the wedge sum
  of open neighbourhoods of the base points is an open subspace of the whole wedge sum.
* `TauCeti.WedgeSum.proj`: the retraction of a wedge sum onto one summand, collapsing the others
  to the base point.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the wedge sum in "Operations on spaces".
-/

public section

noncomputable section

namespace TauCeti

open Set Topology

universe u v w

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- The normal form of a point of `Unit ⊕ Σ i, X i` for the wedge sum: the extra point and every
base point `x i` are sent to `none`, and every other point to itself.  Two points have the same
normal form exactly when the wedge sum identifies them. -/
private def wedgeNormalize (x : ∀ i, X i) (a : Unit ⊕ Σ i, X i) : Option (Σ i, X i) :=
  open Classical in a.elim (fun _ => none) fun p => if p.2 = x p.1 then none else some p

/-- The **wedge sum** of the pointed spaces `(X i, x i)`: their disjoint union with all the base
points identified to one wedge point.  It carries the quotient topology, and the wedge sum of the
empty family is a point.

The presentation as a quotient is private: points of the wedge sum come from
`TauCeti.WedgeSum.base` and `TauCeti.WedgeSum.incl`, which points they identify from
`TauCeti.WedgeSum.incl_eq_incl_iff` and `TauCeti.WedgeSum.incl_eq_base_iff`, maps out of it from
`TauCeti.WedgeSum.lift`, and statements about all of its points from `TauCeti.WedgeSum.ind`. -/
def WedgeSum (x : ∀ i, X i) : Type max u v :=
  Quotient (Setoid.ker (wedgeNormalize x))

namespace WedgeSum

variable {x : ∀ i, X i}

/-! The topology is transported from the private quotient; the instance is `@[no_expose]`, which
is what lets its body name the private constant. -/

@[no_expose] instance : TopologicalSpace (WedgeSum x) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.ker (wedgeNormalize x))))

/-- The wedge point of the wedge sum, to which all the base points are glued. -/
def base (x : ∀ i, X i) : WedgeSum x :=
  Quotient.mk _ (.inl ())

/-- The inclusion of the `i`-th summand into the wedge sum. -/
def incl (x : ∀ i, X i) (i : ι) : C(X i, WedgeSum x) :=
  ⟨fun y => Quotient.mk _ (.inr ⟨i, y⟩), continuous_quot_mk.comp (by fun_prop)⟩

private lemma incl_eq_incl_iff' {i j : ι} {y : X i} {z : X j} :
    incl x i y = incl x j z ↔ wedgeNormalize x (.inr ⟨i, y⟩) = wedgeNormalize x (.inr ⟨j, z⟩) :=
  Quotient.eq (r := Setoid.ker (wedgeNormalize x))

private lemma incl_eq_base_iff' {i : ι} {y : X i} :
    incl x i y = base x ↔ wedgeNormalize x (.inr ⟨i, y⟩) = wedgeNormalize x (.inl ()) :=
  Quotient.eq (r := Setoid.ker (wedgeNormalize x))

/-- A point of a summand is glued to the wedge point exactly when it is the base point. -/
@[simp]
lemma incl_eq_base_iff {i : ι} {y : X i} : incl x i y = base x ↔ y = x i := by
  rw [incl_eq_base_iff']
  simp only [wedgeNormalize, Sum.elim_inr, Sum.elim_inl]
  split_ifs with h <;> simp [h]

/-- The base point of every summand is glued to the wedge point. -/
@[simp]
lemma incl_apply_self (i : ι) : incl x i (x i) = base x :=
  incl_eq_base_iff.2 rfl

/-- Points of two summands are identified in the wedge sum exactly when both are base points or
they are the same point of the same summand. -/
lemma incl_eq_incl_iff {i j : ι} {y : X i} {z : X j} :
    incl x i y = incl x j z ↔ (y = x i ∧ z = x j) ∨ (⟨i, y⟩ : Σ i, X i) = ⟨j, z⟩ := by
  rw [incl_eq_incl_iff']
  simp only [wedgeNormalize, Sum.elim_inr]
  split_ifs with hy hz hz
  · simp [hy, hz]
  · refine iff_of_false (by simp) ?_
    rintro (⟨-, h⟩ | h)
    · exact hz h
    · obtain ⟨rfl, h⟩ := Sigma.mk.inj h
      exact hz ((eq_of_heq h).symm.trans hy)
  · refine iff_of_false (by simp) ?_
    rintro (⟨h, -⟩ | h)
    · exact hy h
    · obtain ⟨rfl, h⟩ := Sigma.mk.inj h
      exact hy ((eq_of_heq h).trans hz)
  · simp [hy]

@[simp]
lemma incl_inj {i : ι} {y z : X i} : incl x i y = incl x i z ↔ y = z := by
  rw [incl_eq_incl_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | h)
    · rfl
    · exact eq_of_heq (Sigma.mk.inj h).2
  · rintro rfl
    exact .inr rfl

lemma incl_injective (i : ι) : Function.Injective (incl x i) :=
  fun _ _ h => incl_inj.1 h

/-- Every point of the wedge sum is the wedge point or comes from a summand. -/
@[elab_as_elim]
lemma ind {p : WedgeSum x → Prop} (base : p (base x)) (incl : ∀ i (y : X i), p (incl x i y))
    (w : WedgeSum x) : p w := by
  induction w using Quotient.ind with
  | _ a => cases a with
    | inl u => exact base
    | inr q => exact incl q.1 q.2

instance : Inhabited (WedgeSum x) :=
  ⟨base x⟩

/-- The wedge sum of the empty family is a point. -/
instance [IsEmpty ι] : Subsingleton (WedgeSum x) := by
  have h (w : WedgeSum x) : w = base x := by
    induction w using ind with
    | base => rfl
    | incl i y => exact (IsEmpty.false i).elim
  exact ⟨fun v w => (h v).trans (h w).symm⟩

/-- **The wedge sum is a quotient of `Unit ⊕ Σ i, X i`.** -/
theorem isQuotientMap_sumElim :
    IsQuotientMap (Sum.elim (fun _ : Unit => base x) fun q : Σ i, X i => incl x q.1 q.2) := by
  have h : (Sum.elim (fun _ : Unit => base x) fun q : Σ i, X i => incl x q.1 q.2) =
      Quotient.mk (Setoid.ker (wedgeNormalize x)) := by
    funext a
    cases a <;> rfl
  rw [h]
  exact isQuotientMap_quot_mk

/-- A subset of the wedge sum is open exactly when its preimage in every summand is open. -/
theorem isOpen_iff {S : Set (WedgeSum x)} : IsOpen S ↔ ∀ i, IsOpen (incl x i ⁻¹' S) := by
  rw [← isQuotientMap_sumElim.isOpen_preimage, isOpen_sum_iff, isOpen_sigma_iff]
  exact and_iff_right (isOpen_discrete _)

section Lift

variable {Y : Type w} [TopologicalSpace Y]

/-- **The universal property of the wedge sum.**  Maps out of the summands which send every base
point to the same point assemble into a map out of the wedge sum. -/
def lift (f : ∀ i, C(X i, Y)) (y : Y) (hf : ∀ i, f i (x i) = y) : C(WedgeSum x, Y) :=
  ⟨Quotient.lift (Sum.elim (fun _ => y) fun q => f q.1 q.2) fun a b hab => by
      rcases a with _ | ⟨i, a⟩ <;> rcases b with _ | ⟨j, b⟩
      · rfl
      · simp only [Sum.elim_inl, Sum.elim_inr]
        rw [(incl_eq_base_iff.1 ((Quotient.eq (r := Setoid.ker (wedgeNormalize x))).2 hab.symm)),
          hf]
      · simp only [Sum.elim_inl, Sum.elim_inr]
        rw [(incl_eq_base_iff.1 ((Quotient.eq (r := Setoid.ker (wedgeNormalize x))).2 hab)), hf]
      · obtain ⟨rfl, rfl⟩ | h :=
          incl_eq_incl_iff.1 ((Quotient.eq (r := Setoid.ker (wedgeNormalize x))).2 hab)
        · simp only [Sum.elim_inr, hf]
        · rw [h],
    Continuous.quotient_lift (continuous_sum_dom.2 ⟨continuous_const,
      continuous_sigma fun i => (f i).continuous⟩) _⟩

@[simp]
lemma lift_incl (f : ∀ i, C(X i, Y)) (y : Y) (hf : ∀ i, f i (x i) = y) (i : ι) (z : X i) :
    lift f y hf (incl x i z) = f i z := (rfl)

@[simp]
lemma lift_base (f : ∀ i, C(X i, Y)) (y : Y) (hf : ∀ i, f i (x i) = y) :
    lift f y hf (base x) = y := (rfl)

/-- **Extensionality for maps out of the wedge sum.**  Two maps out of the wedge sum which agree
at the wedge point and on every summand are equal. -/
@[ext]
theorem hom_ext {f g : C(WedgeSum x, Y)} (hbase : f (base x) = g (base x))
    (h : ∀ i, f.comp (incl x i) = g.comp (incl x i)) : f = g := by
  refine ContinuousMap.ext fun w => ?_
  induction w using ind with
  | base => exact hbase
  | incl i y => exact DFunLike.congr_fun (h i) y

/-- **Maps out of `Z × ⋁ᵢ Xᵢ`.**  For a locally compact space `Z`, maps `Z × X i → Y` which agree
on `Z × {x i}` with a common map `Z → Y` assemble into a map out of the product of `Z` with the
wedge sum.  For `Z = I` this builds homotopies out of a wedge sum from homotopies of the summands
which keep the base points together. -/
def liftProd {Z : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z] (f : ∀ i, C(Z × X i, Y))
    (g : C(Z, Y)) (hf : ∀ i z, f i (z, x i) = g z) : C(Z × WedgeSum x, Y) :=
  (ContinuousMap.uncurry (lift (fun i => ((f i).comp ContinuousMap.prodSwap).curry) g fun i =>
    ContinuousMap.ext fun z => hf i z)).comp ContinuousMap.prodSwap

@[simp]
lemma liftProd_incl {Z : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    (f : ∀ i, C(Z × X i, Y)) (g : C(Z, Y)) (hf : ∀ i z, f i (z, x i) = g z) (z : Z) (i : ι)
    (a : X i) : liftProd f g hf (z, incl x i a) = f i (z, a) := (rfl)

@[simp]
lemma liftProd_base {Z : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    (f : ∀ i, C(Z × X i, Y)) (g : C(Z, Y)) (hf : ∀ i z, f i (z, x i) = g z) (z : Z) :
    liftProd f g hf (z, base x) = g z := (rfl)

end Lift

section Subspace

variable {S : ∀ i, Set (X i)} (hS : ∀ i, x i ∈ S i)

/-- The map from the wedge sum of subsets `S i ∋ x i` of the summands into the wedge sum of the
summands, induced by the inclusions. -/
def subtypeVal : C(WedgeSum fun i => (⟨x i, hS i⟩ : S i), WedgeSum x) :=
  lift (fun i => (incl x i).comp (ContinuousMap.subtypeVal (S i))) (base x) fun _ =>
    incl_apply_self _

@[simp]
lemma subtypeVal_incl (i : ι) (a : S i) : subtypeVal hS (incl _ i a) = incl x i a := (rfl)

@[simp]
lemma subtypeVal_base : subtypeVal hS (base _) = base x := (rfl)

/-- A point of a summand lies in the image of the wedge sum of the subsets `S i ∋ x i` exactly
when it lies in `S i`. -/
lemma incl_mem_range_subtypeVal_iff {i : ι} {z : X i} :
    incl x i z ∈ range (subtypeVal hS) ↔ z ∈ S i := by
  refine ⟨fun ⟨w, hw⟩ => ?_, fun hz => ⟨incl _ i ⟨z, hz⟩, rfl⟩⟩
  induction w using ind with
  | base => exact (incl_eq_base_iff.1 hw.symm) ▸ hS i
  | incl j a =>
    obtain ⟨-, rfl⟩ | h := incl_eq_incl_iff.1 hw
    · exact hS i
    · obtain ⟨rfl, h⟩ := Sigma.mk.inj h
      exact (eq_of_heq h) ▸ a.2

lemma base_mem_range_subtypeVal : base x ∈ range (subtypeVal hS) :=
  ⟨base _, rfl⟩

lemma subtypeVal_injective : Function.Injective (subtypeVal hS) := by
  intro v w hvw
  induction v using ind with
  | base =>
    induction w using ind with
    | base => rfl
    | incl j b =>
      rw [subtypeVal_base, subtypeVal_incl, eq_comm, incl_eq_base_iff] at hvw
      rw [eq_comm, incl_eq_base_iff]
      exact Subtype.ext hvw
  | incl i a =>
    induction w using ind with
    | base =>
      rw [subtypeVal_base, subtypeVal_incl, incl_eq_base_iff] at hvw
      rw [incl_eq_base_iff]
      exact Subtype.ext hvw
    | incl j b =>
      rw [subtypeVal_incl, subtypeVal_incl, incl_eq_incl_iff] at hvw
      rw [incl_eq_incl_iff]
      obtain ⟨ha, hb⟩ | h := hvw
      · exact .inl ⟨Subtype.ext ha, Subtype.ext hb⟩
      · obtain ⟨rfl, h⟩ := Sigma.mk.inj h
        exact .inr (congrArg (Sigma.mk i) (Subtype.ext (eq_of_heq h)))

/-- **A wedge of open neighbourhoods is an open subspace.**  For open subsets `S i ∋ x i` of the
summands, the wedge sum of the `S i` maps homeomorphically onto an open subset of the wedge sum
of the `X i`. -/
theorem isOpenEmbedding_subtypeVal (hSo : ∀ i, IsOpen (S i)) :
    IsOpenEmbedding (subtypeVal hS) := by
  refine .of_continuous_injective_isOpenMap (subtypeVal hS).continuous (subtypeVal_injective hS)
    fun O hO => isOpen_iff.2 fun i => ?_
  -- The preimage of the image of `O` in `X i` is the image of the preimage of `O` in `S i`.
  have hpre : incl x i ⁻¹' (subtypeVal hS '' O) =
      Subtype.val '' (incl (fun i => (⟨x i, hS i⟩ : S i)) i ⁻¹' O) := by
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hz : z ∈ S i := (incl_mem_range_subtypeVal_iff hS).1 ⟨w, hwz⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [mem_preimage, show incl _ i ⟨z, hz⟩ = w from (subtypeVal_injective hS) hwz.symm]
      exact hw
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ha, rfl⟩
  rw [hpre]
  exact (hSo i).isOpenMap_subtype_val _ ((isOpen_iff.1 hO) i)

end Subspace

section Proj

/-- The retraction of the wedge sum onto its `i`-th summand, collapsing every other summand to
the base point `x i`. -/
def proj (x : ∀ i, X i) (i : ι) : C(WedgeSum x, X i) :=
  open Classical in
  lift (fun j => if h : j = i then h ▸ ContinuousMap.id (X j) else ContinuousMap.const _ (x i))
    (x i) fun j => by
      split_ifs with h
      · subst h
        rfl
      · rfl

@[simp]
lemma proj_incl_self (i : ι) (z : X i) : proj x i (incl x i z) = z := by
  simp [proj]

@[simp]
lemma proj_incl_of_ne {i j : ι} (h : j ≠ i) (z : X j) : proj x i (incl x j z) = x i := by
  simp [proj, h]

@[simp]
lemma proj_base (i : ι) : proj x i (base x) = x i := (rfl)

/-- The retraction onto a summand is a left inverse of its inclusion. -/
@[simp]
lemma proj_comp_incl (i : ι) : (proj x i).comp (incl x i) = ContinuousMap.id (X i) := by
  ext z
  simp

end Proj

end WedgeSum

end TauCeti
