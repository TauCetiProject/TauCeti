/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import TauCeti.AlgebraicGeometry.AlgebraicCycle.Basic
public import TauCeti.AlgebraicGeometry.AlgebraicCycle.Principal
public import TauCeti.Topology.LocallyFinsupp.LocallyFiniteSum
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Cycles of dimension `k`, rational equivalence and Chow groups

This file defines the Chow groups `CH_k(X)` of a locally Noetherian scheme `X` as quotients of
Mathlib's algebraic cycles by rational equivalence, following
[Stacks, Section 42.19](https://stacks.math.columbia.edu/tag/02RV) and Fulton, *Intersection
Theory*, §1.3.

* `Chow.pointsOfDimension X k`: the points `x` of `X` whose closure has dimension `k`, that is,
  whose height for the specialization order (`x ≤ y ↔ y ⤳ x`) is the natural number `k`.
* `Chow.cyclesOfDimension X k`: the group `Z_k(X)` of `k`-cycles, the subgroup of
  `AlgebraicCycle X ℤ` of cycles supported on points of dimension `k`
  ([Stacks, Definition 42.8.1](https://stacks.math.columbia.edu/tag/02QR)). It vanishes for
  `k < 0`.
* `Chow.RatEquivFamily X k`: a family of integral closed subschemes `i_j : W_j ⟶ X` of dimension
  `k + 1`, with nonzero rational functions `r_j ∈ κ(W_j)ˣ`, whose closed supports `i_j(W_j)` form
  a locally finite family. Its cycle `Σ_j (i_j)_* div(r_j)`, with `div` the principal cycle
  `AlgebraicCycle.div`, is a locally finite sum; each pushforward is Mathlib's
  `AlgebraicCycle.map` with height weights, which along a closed immersion simply transports
  coefficients (`AlgebraicCycle.map_height_apply_of_isClosedImmersion`).
* `Chow.RatEquiv X k`: the subgroup of `Z_k(X)` of cycles rationally equivalent to zero, those of
  the form `Σ_j (i_j)_* div(r_j)` for such a family (`Chow.mem_ratEquiv_iff`)
  ([Stacks, Definition 42.19.1 and Remark 42.19.6](https://stacks.math.columbia.edu/tag/02RV)).
  Local finiteness is imposed on the supports `|W_j|`, not merely on the principal cycles: an
  infinite family of copies of one subscheme with `r_j = 1` is not allowed.
* `Chow.ChowGroup X k`: the Chow group `CH_k(X) = Z_k(X) / RatEquiv X k`, with the class map
  `Chow.cycleClass` and its universal property `Chow.ChowGroup.lift`.

No quasi-compactness or separation is imposed. For `X` locally of finite type over a field the
dimension formula shows that every sum `Σ_j (i_j)_* div(r_j)` as above is itself a `k`-cycle, so
the condition that a rationally trivial cycle lies in `Z_k(X)` is then automatic; it is part of the
definition here.

We also record the basic computations of Fulton, §1.3: `CH_k(X) = 0` for `k < 0` and for empty `X`,
`RatEquiv X k = 0` when `X` has no point of dimension `k + 1`, and `CH_0(X) ≃ ℤ` for a scheme with
exactly one point, such as the spectrum of a field.
-/

public section

open AlgebraicGeometry Order CategoryTheory Topology TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry.Chow

section Cycles

variable (X : Scheme.{u})

/-- The points of dimension `k` of a scheme: the points `x` whose height for the specialization
order is the natural number `k`. Since `x ≤ y ↔ y ⤳ x`, the height of `x` is the Krull dimension of
the closure of `x`. -/
def pointsOfDimension (k : ℤ) : Set X :=
  {x | ∃ n : ℕ, height x = n ∧ (n : ℤ) = k}

variable {X} in
/-- A point has dimension `k` exactly when its height is the natural number `k`. -/
@[simp]
lemma mem_pointsOfDimension {k : ℤ} {x : X} :
    x ∈ pointsOfDimension X k ↔ ∃ n : ℕ, height x = n ∧ (n : ℤ) = k :=
  Iff.rfl

/-- There are no points of negative dimension. -/
lemma pointsOfDimension_eq_empty_of_neg {k : ℤ} (hk : k < 0) : pointsOfDimension X k = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨n, _, hn⟩ ↦ by omega

/-- The group `Z_k(X)` of `k`-cycles: algebraic cycles all of whose points with nonzero coefficient
have dimension `k`. -/
def cyclesOfDimension (k : ℤ) : AddSubgroup (AlgebraicCycle X ℤ) :=
  Function.locallyFinsuppWithin.supported ℤ Set.univ (pointsOfDimension X k)

variable {X} in
/-- A cycle is a `k`-cycle exactly when its support consists of points of dimension `k`. -/
@[simp]
lemma mem_cyclesOfDimension_iff {k : ℤ} {α : AlgebraicCycle X ℤ} :
    α ∈ cyclesOfDimension X k ↔ α.support ⊆ pointsOfDimension X k :=
  Iff.rfl

/-- There are no nonzero cycles of negative dimension. -/
lemma cyclesOfDimension_eq_bot_of_neg {k : ℤ} (hk : k < 0) : cyclesOfDimension X k = ⊥ := by
  ext α
  rw [mem_cyclesOfDimension_iff, pointsOfDimension_eq_empty_of_neg X hk, AddSubgroup.mem_bot,
    Set.subset_empty_iff, Function.support_eq_empty_iff]
  exact ⟨fun h ↦ Function.locallyFinsuppWithin.ext (congrFun h),
    fun h ↦ h ▸ rfl⟩

end Cycles

section RatEquiv

/-- The data of a rational equivalence to zero in dimension `k` on `X`: integral closed subschemes
`i j : W j ⟶ X` of dimension `k + 1` with nonzero rational functions `r j`, such that the closed
supports `i j (W j)` form a locally finite family. Its cycle is `Σ_j (i j)_* div (r j)`
(`RatEquivFamily.cycle`). -/
structure RatEquivFamily (X : Scheme.{u}) (k : ℤ) where
  /-- The index type of the family. -/
  ι : Type u
  /-- The integral closed subschemes. -/
  W : ι → Scheme.{u}
  /-- The closed immersions of the subschemes into `X`. -/
  i (j : ι) : W j ⟶ X
  /-- Each `i j` is a closed immersion. -/
  [isClosedImmersion (j : ι) : IsClosedImmersion (i j)]
  /-- Each `W j` is integral. -/
  [isIntegral (j : ι) : IsIntegral (W j)]
  /-- Each `W j` has dimension `k + 1`: its generic point has height `k + 1`. -/
  genericPoint_mem (j : ι) : genericPoint (W j) ∈ pointsOfDimension (W j) (k + 1)
  /-- The nonzero rational functions on the subschemes. -/
  r (j : ι) : (W j).functionFieldˣ
  /-- The closed supports of the subschemes form a locally finite family. -/
  locallyFinite : LocallyFinite fun j ↦ Set.range (i j)

namespace RatEquivFamily

attribute [instance] isClosedImmersion isIntegral

variable {X : Scheme.{u}} {k : ℤ}

/-- A closed subscheme of a locally Noetherian scheme is locally Noetherian. -/
instance isLocallyNoetherian [IsLocallyNoetherian X] (F : RatEquivFamily X k) (j : F.ι) :
    IsLocallyNoetherian (F.W j) :=
  LocallyOfFiniteType.isLocallyNoetherian (F.i j)

variable [IsLocallyNoetherian X] (F : RatEquivFamily X k)

/-- The `j`-th summand `(i j)_* div (r j)` of the cycle of a family, Mathlib's pushforward of cycles
with height weights. -/
noncomputable def component (j : F.ι) : AlgebraicCycle X ℤ :=
  AlgebraicCycle.map (F.i j) height height (AlgebraicCycle.div (F.r j))

/-- At a point of `W j`, the `j`-th summand is the order of vanishing of `r j`. -/
@[simp]
lemma component_apply (j : F.ι) (y : F.W j) :
    F.component j (F.i j y) = (F.W j).ord (F.r j : (F.W j).functionField) y := by
  rw [component, AlgebraicCycle.map_height_apply_of_isClosedImmersion, AlgebraicCycle.div_apply]

/-- Away from `W j`, the `j`-th summand vanishes. -/
lemma component_apply_eq_zero_of_notMem_range (j : F.ι) {x : X} (hx : x ∉ Set.range (F.i j)) :
    F.component j x = 0 :=
  AlgebraicCycle.map_apply_eq_zero_of_notMem_range _ _ _ _ hx

/-- The `j`-th summand is supported on `W j`. -/
lemma support_component_subset (j : F.ι) : (F.component j).support ⊆ Set.range (F.i j) :=
  AlgebraicCycle.support_map_subset_range _ _ _ _

/-- The supports of the summands form a locally finite family. -/
lemma locallyFinite_support_component : LocallyFinite fun j ↦ (F.component j).support :=
  F.locallyFinite.subset F.support_component_subset

/-- The cycle `Σ_j (i j)_* div (r j)` of a family, a locally finite sum. -/
noncomputable def cycle : AlgebraicCycle X ℤ :=
  Function.locallyFinsupp.locallyFiniteSum F.component F.locallyFinite_support_component

/-- The coefficients of the cycle of a family are the (finite) sums of the coefficients of its
summands. -/
@[simp]
lemma cycle_apply (x : X) : F.cycle x = ∑ᶠ j, F.component j x :=
  Function.locallyFinsupp.locallyFiniteSum_apply _ _ x

/-- The empty family, whose cycle is zero. -/
private def empty (X : Scheme.{u}) (k : ℤ) : RatEquivFamily X k where
  ι := PEmpty
  W := PEmpty.elim
  i := fun j ↦ j.elim
  isClosedImmersion := fun j ↦ j.elim
  isIntegral := fun j ↦ j.elim
  genericPoint_mem := fun j ↦ j.elim
  r := fun j ↦ j.elim
  locallyFinite := locallyFinite_of_finite _

private lemma cycle_empty : (empty X k).cycle = 0 :=
  Function.locallyFinsupp.locallyFiniteSum_of_isEmpty (ι := PEmpty) _ _

/-- The disjoint union of two families, whose cycle is the sum of the two cycles. -/
private noncomputable def sum (G : RatEquivFamily X k) : RatEquivFamily X k where
  ι := F.ι ⊕ G.ι
  W := Sum.elim F.W G.W
  i
    | .inl j => F.i j
    | .inr j => G.i j
  isClosedImmersion
    | .inl j => F.isClosedImmersion j
    | .inr j => G.isClosedImmersion j
  isIntegral
    | .inl j => F.isIntegral j
    | .inr j => G.isIntegral j
  genericPoint_mem
    | .inl j => F.genericPoint_mem j
    | .inr j => G.genericPoint_mem j
  r
    | .inl j => F.r j
    | .inr j => G.r j
  locallyFinite := locallyFinite_sum.mpr ⟨F.locallyFinite, G.locallyFinite⟩

private lemma cycle_sum (G : RatEquivFamily X k) : (F.sum G).cycle = F.cycle + G.cycle := by
  -- The summands of `F.sum G` are those of `F` and of `G`, by unfolding the case split in `sum`.
  have h : (F.sum G).component = Sum.elim F.component G.component := by
    funext j
    rcases j with j | j <;> rfl
  have key : ∀ (c : (F.sum G).ι → AlgebraicCycle X ℤ) (hc : LocallyFinite fun j ↦ (c j).support),
      c = Sum.elim F.component G.component →
        Function.locallyFinsupp.locallyFiniteSum c hc = F.cycle + G.cycle := by
    rintro c hc rfl
    exact Function.locallyFinsupp.locallyFiniteSum_sumElim _ _ _ _ _
  exact key _ _ h

/-- The family with every rational function inverted, whose cycle is the negative. -/
private noncomputable def inv : RatEquivFamily X k where
  __ := F
  r j := (F.r j)⁻¹

private lemma component_inv (j : F.ι) : F.inv.component j = -F.component j := by
  ext x
  by_cases hx : x ∈ Set.range (F.i j)
  · obtain ⟨y, rfl⟩ := hx
    refine (F.inv.component_apply j y).trans ?_
    rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, F.component_apply j y,
      ← TauCeti.AlgebraicGeometry.Scheme.ord_inv, ← Units.val_inv_eq_inv_val]
    -- `F.inv` has the subschemes of `F` and the rational functions `(F.r j)⁻¹`, by definition.
    rfl
  · simp [F.component_apply_eq_zero_of_notMem_range j hx,
      F.inv.component_apply_eq_zero_of_notMem_range j hx]

private lemma cycle_inv : F.inv.cycle = -F.cycle := by
  have h : F.inv.component = fun j ↦ -F.component j := funext F.component_inv
  have key : ∀ (c : F.ι → AlgebraicCycle X ℤ) (hc : LocallyFinite fun j ↦ (c j).support),
      c = (fun j ↦ -F.component j) →
        Function.locallyFinsupp.locallyFiniteSum c hc = -F.cycle := by
    rintro c hc rfl
    exact Function.locallyFinsupp.locallyFiniteSum_neg _ _ _
  exact key _ _ h

end RatEquivFamily

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The subgroup `RatEquiv X k` of `k`-cycles rationally equivalent to zero: the cycles of the form
`Σ_j (i j)_* div (r j)` for a locally finite family of integral closed subschemes `W j` of
dimension `k + 1` and nonzero rational functions `r j` on them. -/
def RatEquiv (k : ℤ) : AddSubgroup (cyclesOfDimension X k) where
  carrier := {α | ∃ F : RatEquivFamily X k, F.cycle = α}
  zero_mem' := ⟨RatEquivFamily.empty X k, RatEquivFamily.cycle_empty⟩
  add_mem' := by
    rintro _ _ ⟨F, hF⟩ ⟨G, hG⟩
    exact ⟨F.sum G, by rw [RatEquivFamily.cycle_sum, hF, hG, AddSubgroup.coe_add]⟩
  neg_mem' := by
    rintro _ ⟨F, hF⟩
    exact ⟨F.inv, by rw [RatEquivFamily.cycle_inv, hF, AddSubgroup.coe_neg]⟩

variable {X} in
/-- A `k`-cycle is rationally equivalent to zero exactly when it is the cycle
`Σ_j (i j)_* div (r j)` of a locally finite family of integral closed subschemes of dimension
`k + 1` with nonzero rational functions. -/
lemma mem_ratEquiv_iff {k : ℤ} {α : cyclesOfDimension X k} :
    α ∈ RatEquiv X k ↔ ∃ F : RatEquivFamily X k, F.cycle = α :=
  Iff.rfl

/-- If `X` has no points of dimension `k + 1`, then no nonzero `k`-cycle is rationally equivalent
to zero. -/
lemma ratEquiv_eq_bot_of_pointsOfDimension_eq_empty {k : ℤ}
    (h : pointsOfDimension X (k + 1) = ∅) : RatEquiv X k = ⊥ := by
  rw [eq_bot_iff]
  rintro α ⟨F, hF⟩
  have : IsEmpty F.ι := ⟨fun j ↦ by
    have hj := F.genericPoint_mem j
    rw [mem_pointsOfDimension, ← Scheme.Hom.height_apply_eq_height (F.i j)] at hj
    exact (Set.eq_empty_iff_forall_notMem.mp h) _ hj⟩
  rw [AddSubgroup.mem_bot, ← Subtype.coe_inj, AddSubgroup.coe_zero, ← hF]
  exact Function.locallyFinsupp.locallyFiniteSum_of_isEmpty _ _

end RatEquiv

section ChowGroup

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The Chow group `CH_k(X)` of `k`-cycles modulo rational equivalence. -/
def ChowGroup (k : ℤ) : Type u :=
  cyclesOfDimension X k ⧸ RatEquiv X k

instance (k : ℤ) : AddCommGroup (ChowGroup X k) :=
  inferInstanceAs (AddCommGroup (cyclesOfDimension X k ⧸ RatEquiv X k))

variable {X}

/-- The class in the Chow group of a `k`-cycle. -/
noncomputable def cycleClass {k : ℤ} : cyclesOfDimension X k →+ ChowGroup X k :=
  QuotientAddGroup.mk' (RatEquiv X k)

/-- Every element of the Chow group is the class of a cycle. -/
lemma cycleClass_surjective {k : ℤ} :
    Function.Surjective (cycleClass : cyclesOfDimension X k → ChowGroup X k) :=
  QuotientAddGroup.mk'_surjective _

/-- The class of a cycle vanishes exactly when the cycle is rationally equivalent to zero. -/
@[simp]
lemma cycleClass_eq_zero_iff {k : ℤ} {α : cyclesOfDimension X k} :
    cycleClass α = 0 ↔ α ∈ RatEquiv X k :=
  QuotientAddGroup.eq_zero_iff α

/-- Two cycles have the same class exactly when their difference is rationally equivalent to
zero. -/
lemma cycleClass_eq_cycleClass_iff {k : ℤ} {α β : cyclesOfDimension X k} :
    cycleClass α = cycleClass β ↔ α - β ∈ RatEquiv X k := by
  rw [← sub_eq_zero, ← map_sub, cycleClass_eq_zero_iff]

namespace ChowGroup

/-- An additive map out of the `k`-cycles which vanishes on cycles rationally equivalent to zero
descends to the Chow group. -/
noncomputable def lift {k : ℤ} {A : Type*} [AddMonoid A] (f : cyclesOfDimension X k →+ A)
    (hf : RatEquiv X k ≤ f.ker) : ChowGroup X k →+ A :=
  QuotientAddGroup.lift (RatEquiv X k) f hf

/-- The descended map agrees with the original map on cycle classes. -/
@[simp]
lemma lift_cycleClass {k : ℤ} {A : Type*} [AddMonoid A] (f : cyclesOfDimension X k →+ A)
    (hf : RatEquiv X k ≤ f.ker) (α : cyclesOfDimension X k) : lift f hf (cycleClass α) = f α :=
  (rfl)

/-- Additive maps out of the Chow group are determined by their values on cycle classes. -/
@[ext]
lemma hom_ext {k : ℤ} {A : Type*} [AddMonoid A] {f g : ChowGroup X k →+ A}
    (h : f.comp cycleClass = g.comp cycleClass) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ h

variable (X)

/-- The Chow groups vanish in negative dimension. -/
lemma subsingleton_of_neg {k : ℤ} (hk : k < 0) : Subsingleton (ChowGroup X k) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨α, rfl⟩ := cycleClass_surjective a
  obtain ⟨β, rfl⟩ := cycleClass_surjective b
  have hbot := cyclesOfDimension_eq_bot_of_neg X hk
  have hα : (α : AlgebraicCycle X ℤ) ∈ (⊥ : AddSubgroup _) := hbot ▸ α.2
  have hβ : (β : AlgebraicCycle X ℤ) ∈ (⊥ : AddSubgroup _) := hbot ▸ β.2
  rw [AddSubgroup.mem_bot] at hα hβ
  rw [Subtype.ext (hα.trans hβ.symm)]

/-- The Chow groups of the empty scheme vanish. -/
instance [IsEmpty X] (k : ℤ) : Subsingleton (ChowGroup X k) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨α, rfl⟩ := cycleClass_surjective a
  obtain ⟨β, rfl⟩ := cycleClass_surjective b
  congr 1
  ext x
  exact isEmptyElim x

/-- On a scheme with exactly one point, evaluation of cycles at that point identifies the Chow
group of zero-cycles with `ℤ`: the point has dimension zero, and there are no subschemes of
dimension one to produce rational equivalences. -/
noncomputable def equivIntOfUnique [Unique X] : ChowGroup X 0 ≃+ ℤ :=
  have hdim (x : X) : height x = 0 :=
    height_eq_zero.mpr fun y _ ↦ (Subsingleton.elim x y).le
  have hbot : RatEquiv X 0 = ⊥ := ratEquiv_eq_bot_of_pointsOfDimension_eq_empty X <|
    Set.eq_empty_iff_forall_notMem.mpr fun x ⟨n, hn, hn1⟩ ↦ by
      rw [hdim x] at hn
      norm_cast at hn
      omega
  have htop : cyclesOfDimension X 0 = ⊤ :=
    eq_top_iff.mpr fun _ _ x _ ↦ ⟨0, hdim x, rfl⟩
  let eval : AlgebraicCycle X ℤ ≃+ ℤ :=
    { toFun c := c default
      invFun n :=
        { toFun _ := n
          supportWithinDomain' := Set.subset_univ _
          supportLocallyFiniteWithinDomain' _ _ := ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩ }
      left_inv c := by
        ext x
        rw [Subsingleton.elim x default]
        rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }
  ((QuotientAddGroup.quotientAddEquivOfEq hbot).trans QuotientAddGroup.quotientBot).trans <|
    ((AddEquiv.addSubgroupCongr htop).trans AddSubgroup.topEquiv).trans eval

/-- The identification `CH_0(X) ≃ ℤ` for a one-point scheme sends the class of a zero-cycle to its
coefficient at the point. -/
@[simp]
lemma equivIntOfUnique_cycleClass [Unique X] (α : cyclesOfDimension X 0) :
    equivIntOfUnique X (cycleClass α) = (α : AlgebraicCycle X ℤ) default :=
  (rfl)

/-- `CH_0(Spec K) ≃ ℤ` for a field `K`. -/
noncomputable example (K : Type u) [Field K] : ChowGroup (Spec (.of K)) 0 ≃+ ℤ :=
  equivIntOfUnique _

end ChowGroup

end ChowGroup

end TauCeti.AlgebraicGeometry.Chow
