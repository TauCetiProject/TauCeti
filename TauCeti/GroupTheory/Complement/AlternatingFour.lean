/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.CrossedProjection
public import TauCeti.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Normalized crossed projections from `alternatingGroup α` to `kleinFour α` in degree four

Let `α` be a finite type with `Nat.card α = 4`. Each point `a : α` determines the complement
`MulAction.stabilizer (alternatingGroup α) a` of `alternatingGroup.kleinFour α` in
`alternatingGroup α` (`alternatingGroup.isComplement'_kleinFour_stabilizer`), and hence a
normalized crossed projection

`alternatingGroup.kleinFourCrossedProjection hα4 a : alternatingGroup α → kleinFour α`.

Because `kleinFour α` acts sharply transitively on `α` (`alternatingGroup.kleinFourOrbitEquiv`)
and the complementary factor fixes `a`, the crossed projection `c_a` admits a direct geometric
description: `c_a g` is the unique element `v ∈ kleinFour α` such that `v • a = g • a`.

Composing `alternatingGroup.kleinFourComplementEquiv` with `Subgroup.crossedProjectionEquiv` shows
that `a ↦ c_a` (read additively) is a bijection between `α` and the set of normalized additive
`1`-cocycles `alternatingGroup α → Additive (kleinFour α)`, so there are exactly `4` such crossed
projections and none of them is a group homomorphism (since `kleinFour α` is the commutator
subgroup of `alternatingGroup α`).

Conjugating the stabilizer of `a` by `v ∈ kleinFour α` yields the stabilizer of `v • a`, and
multiplies `c_a` by the principal crossed map `g ↦ g • v / v`. Because `kleinFour α` acts sharply
transitively on `α`, `kleinFour α` permutes both the four complements and the four normalized
crossed projections sharply transitively.

## Main definitions

* `alternatingGroup.kleinFourCrossedProjection`: the normalized crossed projection
  `alternatingGroup α → kleinFour α` along `MulAction.stabilizer (alternatingGroup α) a`.
* `alternatingGroup.kleinFourCrossedProjectionEquiv`: the bijection between `α` and normalized
  additive `1`-cocycles `alternatingGroup α → Additive (kleinFour α)`.

## Main results

* `alternatingGroup.kleinFourCrossedProjection_eq_iff`: `c_a g = v ↔ v • a = g • a`.
* `alternatingGroup.exists_kleinFourCrossedProjection_mul_ne`: no `c_a` is multiplicative.
* `alternatingGroup.existsUnique_eq_kleinFourCrossedProjection`: every normalized multiplicative
  `1`-cocycle `alternatingGroup α → kleinFour α` equals `c_a` for a unique `a : α`.
* `alternatingGroup.kleinFourCrossedProjection_smul_point`:
  `c_{v • a} g = c_a g * (g • v / v)` for `v ∈ kleinFour α`.
* `alternatingGroup.existsUnique_principal_twist_of_isMulCocycle₁`: any two normalized crossed maps
  `alternatingGroup α → kleinFour α` differ by a unique principal crossed map `g ↦ g • v / v`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
-/

public section

open scoped IsMulCommutative Pointwise
open groupCohomology

namespace alternatingGroup

attribute [local instance] Subgroup.conjugationAction

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### Geometric characterization of the four crossed projections -/

/-- The normalized crossed projection `alternatingGroup α → kleinFour α` associated with the
point-stabilizer complement `MulAction.stabilizer (alternatingGroup α) a` when `Nat.card α = 4`. -/
noncomputable def kleinFourCrossedProjection (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) : kleinFour α :=
  (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection g

@[simp]
theorem kleinFourCrossedProjection_coe (hα4 : Nat.card α = 4) (a : α) (v : kleinFour α) :
    kleinFourCrossedProjection hα4 a v = v :=
  (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection_coe v

@[simp]
theorem kleinFourCrossedProjection_one (hα4 : Nat.card α = 4) (a : α) :
    kleinFourCrossedProjection hα4 a 1 = 1 :=
  (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection_coe 1

@[simp]
theorem kleinFourCrossedProjection_eq_one_iff (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) :
    kleinFourCrossedProjection hα4 a g = 1 ↔ g • a = a :=
  (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection_eq_one_iff g

theorem kleinFourCrossedProjection_mul_right_mem (hα4 : Nat.card α = 4) (a : α)
    (v : kleinFour α) {d : alternatingGroup α} (hd : d • a = a) :
    kleinFourCrossedProjection hα4 a ((v : alternatingGroup α) * d) = v :=
  (isComplement'_kleinFour_stabilizer hα4 a).crossedProjection_mul v ⟨d, hd⟩

/-- `kleinFourCrossedProjection hα4 a g` sends the basepoint `a` to `g • a`. -/
@[simp]
theorem kleinFourCrossedProjection_smul_self (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) :
    kleinFourCrossedProjection hα4 a g • a = g • a := by
  obtain ⟨⟨v, d⟩, rfl⟩ := (isComplement'_kleinFour_stabilizer hα4 a).surjective g
  have hd : (d : alternatingGroup α) • a = a := d.property
  simp only [kleinFourCrossedProjection, Subgroup.IsComplement'.crossedProjection_mul,
    mul_smul, hd, Subgroup.smul_def]

/-- `kleinFourCrossedProjection hα4 a g` is the inverse of orbit evaluation at `a` applied to
`g • a`. -/
theorem kleinFourCrossedProjection_apply (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) :
    kleinFourCrossedProjection hα4 a g = (kleinFourOrbitEquiv hα4 a).symm (g • a) :=
  ((kleinFourOrbitEquiv_symm_eq_iff hα4 a (g • a) _).mpr
    (kleinFourCrossedProjection_smul_self hα4 a g)).symm

/-- `kleinFourCrossedProjection hα4 a g` equals `v` if and only if `v • a = g • a`. -/
theorem kleinFourCrossedProjection_eq_iff (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) (v : kleinFour α) :
    kleinFourCrossedProjection hα4 a g = v ↔ v • a = g • a := by
  rw [kleinFourCrossedProjection_apply, kleinFourOrbitEquiv_symm_eq_iff]

/-- Right-multiplying `g` by `v ∈ kleinFour α` multiplies `c_a g` by `g • v`. -/
theorem kleinFourCrossedProjection_mul_coe (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) (v : kleinFour α) :
    kleinFourCrossedProjection hα4 a (g * v) = kleinFourCrossedProjection hα4 a g * g • v := by
  let _ := (kleinFour_isKleinFour hα4).isMulCommutative
  have hc : kleinFourCrossedProjection hα4 a (g * v) =
      g • kleinFourCrossedProjection hα4 a v * kleinFourCrossedProjection hα4 a g :=
    (isComplement'_kleinFour_stabilizer hα4 a).isMulCocycle₁_crossedProjection g v
  rw [hc, kleinFourCrossedProjection_coe, mul_comm]

/-- When `d` fixes `a`, `c_a (d * v) = d • v`, in contrast to `c_a (v * d) = v`. -/
theorem kleinFourCrossedProjection_mul_coe_of_stabilizer (hα4 : Nat.card α = 4) (a : α)
    {d : alternatingGroup α} (hd : d • a = a) (v : kleinFour α) :
    kleinFourCrossedProjection hα4 a (d * v) = d • v := by
  rw [kleinFourCrossedProjection_mul_coe,
    (kleinFourCrossedProjection_eq_one_iff hα4 a d).mpr hd, one_mul]

/-- None of the crossed projections `alternatingGroup α → kleinFour α` is multiplicative when
`Nat.card α = 4`, because `kleinFour α` is the commutator subgroup of `alternatingGroup α`. -/
theorem exists_kleinFourCrossedProjection_mul_ne (hα4 : Nat.card α = 4) (a : α) :
    ∃ g k : alternatingGroup α,
      kleinFourCrossedProjection hα4 a (g * k) ≠
        kleinFourCrossedProjection hα4 a g * kleinFourCrossedProjection hα4 a k := by
  by_contra! hmul
  let _ := (kleinFour_isKleinFour hα4).isMulCommutative
  let φ : alternatingGroup α →* kleinFour α :=
    { toFun := kleinFourCrossedProjection hα4 a
      map_one' := kleinFourCrossedProjection_one hα4 a
      map_mul' := hmul }
  have hcomm : commutator (alternatingGroup α) ≤ φ.ker :=
    Group.Abelianization.commutator_le_ker φ
  rw [← kleinFour_eq_commutator hα4] at hcomm
  have hsub : Subsingleton (kleinFour α) :=
    ⟨fun v₁ v₂ => by
      have hv₁ : v₁ = 1 := (kleinFourCrossedProjection_coe hα4 a v₁).symm.trans (hcomm v₁.property)
      have hv₂ : v₂ = 1 := (kleinFourCrossedProjection_coe hα4 a v₂).symm.trans (hcomm v₂.property)
      exact hv₁.trans hv₂.symm⟩
  have hcard := kleinFour_card_of_card_eq_four hα4
  have hle : Nat.card (kleinFour α) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
  omega

/-! ### Sharp transitive `V₄`-conjugacy of complements and crossed projections -/

/-- `kleinFour α` acts sharply transitively by conjugation on the point stabilizers in
`alternatingGroup α` when `Nat.card α = 4`. -/
theorem existsUnique_conj_kleinFour_stabilizer (hα4 : Nat.card α = 4) (a b : α) :
    ∃! v : kleinFour α,
      MulAut.conj (v : alternatingGroup α) • MulAction.stabilizer (alternatingGroup α) a =
        MulAction.stabilizer (alternatingGroup α) b := by
  have heq : ∀ v : kleinFour α,
      (MulAut.conj (v : alternatingGroup α) • MulAction.stabilizer (alternatingGroup α) a =
        MulAction.stabilizer (alternatingGroup α) b) ↔ v • a = b := by
    intro v
    rw [conj_smul_stabilizer, (stabilizer_injective_of_card_eq_four hα4).eq_iff]
    rfl
  simpa only [heq] using existsUnique_kleinFour_smul_eq hα4 a b

/-- Shifting the basepoint `a` by `v ∈ kleinFour α` multiplies `kleinFourCrossedProjection hα4 a`
by the principal crossed map `g ↦ g • v / v`. -/
theorem kleinFourCrossedProjection_smul_point (hα4 : Nat.card α = 4) (v : kleinFour α)
    (a : α) (g : alternatingGroup α) :
    kleinFourCrossedProjection hα4 (v • a) g =
      kleinFourCrossedProjection hα4 a g * (g • v / v) := by
  let _ := (kleinFour_isKleinFour hα4).isMulCommutative
  have hstab : MulAction.stabilizer (alternatingGroup α) (v • a) =
      MulAut.conj (v : alternatingGroup α) • MulAction.stabilizer (alternatingGroup α) a := by
    rw [conj_smul_stabilizer]
    rfl
  exact ((isComplement'_kleinFour_stabilizer hα4 a).eq_conj_smul_iff_crossedProjection_eq
    (isComplement'_kleinFour_stabilizer hα4 (v • a)) v).mp hstab g

/-- For any two points `a, b : α`, there is a unique `v ∈ kleinFour α` whose principal crossed map
`g ↦ g • v / v` twists `c_a` into `c_b`. -/
theorem existsUnique_kleinFourCrossedProjection_principal_twist (hα4 : Nat.card α = 4)
    (a b : α) :
    ∃! v : kleinFour α, ∀ g : alternatingGroup α,
      kleinFourCrossedProjection hα4 b g =
        kleinFourCrossedProjection hα4 a g * (g • v / v) := by
  let _ := (kleinFour_isKleinFour hα4).isMulCommutative
  have hiff : ∀ v : kleinFour α,
      (∀ g : alternatingGroup α,
        kleinFourCrossedProjection hα4 b g =
          kleinFourCrossedProjection hα4 a g * (g • v / v)) ↔
      MulAut.conj (v : alternatingGroup α) • MulAction.stabilizer (alternatingGroup α) a =
        MulAction.stabilizer (alternatingGroup α) b := by
    intro v
    simp only [kleinFourCrossedProjection]
    rw [← (isComplement'_kleinFour_stabilizer hα4 a).eq_conj_smul_iff_crossedProjection_eq
      (isComplement'_kleinFour_stabilizer hα4 b) v, eq_comm]
  simpa only [hiff] using existsUnique_conj_kleinFour_stabilizer hα4 a b

/-! ### Bijection with normalized `1`-cocycles -/

section Cocycle

variable [IsMulCommutative (kleinFour α)]

/-- Each `kleinFourCrossedProjection hα4 a` satisfies the multiplicative crossed identity for the
conjugation action of `alternatingGroup α` on `kleinFour α`. -/
theorem isMulCocycle₁_kleinFourCrossedProjection (hα4 : Nat.card α = 4) (a : α) :
    IsMulCocycle₁ (kleinFourCrossedProjection hα4 a) :=
  (isComplement'_kleinFour_stabilizer hα4 a).isMulCocycle₁_crossedProjection

/-- For `Nat.card α = 4`, the points of `α` correspond bijectively to normalized additive
`1`-cocycles `alternatingGroup α → Additive (kleinFour α)`. -/
noncomputable def kleinFourCrossedProjectionEquiv (hα4 : Nat.card α = 4) :
    α ≃ {c : alternatingGroup α → Additive (kleinFour α) //
      IsCocycle₁ c ∧ ∀ n : kleinFour α, c n = Additive.ofMul n} :=
  (kleinFourComplementEquiv hα4).trans (kleinFour α).crossedProjectionEquiv

@[simp]
theorem kleinFourCrossedProjectionEquiv_apply (hα4 : Nat.card α = 4) (a : α)
    (g : alternatingGroup α) :
    (kleinFourCrossedProjectionEquiv hα4 a).val g =
      Additive.ofMul (kleinFourCrossedProjection hα4 a g) := by
  have heq : kleinFourComplementEquiv hα4 a =
      ⟨MulAction.stabilizer (alternatingGroup α) a, isComplement'_kleinFour_stabilizer hα4 a⟩ :=
    Subtype.ext (kleinFourComplementEquiv_apply_coe hα4 a)
  rw [kleinFourCrossedProjectionEquiv, Equiv.trans_apply, heq,
    Subgroup.crossedProjectionEquiv_apply, kleinFourCrossedProjection]

@[simp]
theorem kleinFourCrossedProjectionEquiv_symm_stabilizer (hα4 : Nat.card α = 4)
    (c : {c : alternatingGroup α → Additive (kleinFour α) //
      IsCocycle₁ c ∧ ∀ n : kleinFour α, c n = Additive.ofMul n}) :
    MulAction.stabilizer (alternatingGroup α) ((kleinFourCrossedProjectionEquiv hα4).symm c) =
      zeroLocus c.property.1 := by
  rw [kleinFourCrossedProjectionEquiv, Equiv.symm_trans_apply,
    ← kleinFourComplementEquiv_apply_coe hα4, Equiv.apply_symm_apply,
    Subgroup.crossedProjectionEquiv_symm_apply]

/-- There are exactly `4` normalized additive crossed maps
`alternatingGroup α → Additive (kleinFour α)` when `Nat.card α = 4`. -/
theorem card_kleinFour_crossedProjection (hα4 : Nat.card α = 4) :
    Nat.card {c : alternatingGroup α → Additive (kleinFour α) //
      IsCocycle₁ c ∧ ∀ n : kleinFour α, c n = Additive.ofMul n} = 4 :=
  (Nat.card_congr (kleinFourCrossedProjectionEquiv hα4).symm).trans hα4

/-- Every normalized multiplicative `1`-cocycle `alternatingGroup α → kleinFour α` equals
`kleinFourCrossedProjection hα4 a` for a unique point `a : α` when `Nat.card α = 4`. -/
theorem existsUnique_eq_kleinFourCrossedProjection (hα4 : Nat.card α = 4)
    {c : alternatingGroup α → kleinFour α} (hc : IsMulCocycle₁ c)
    (hn : ∀ n : kleinFour α, c n = n) :
    ∃! a : α, c = kleinFourCrossedProjection hα4 a := by
  let cAdd : {f : alternatingGroup α → Additive (kleinFour α) //
      IsCocycle₁ f ∧ ∀ n : kleinFour α, f n = Additive.ofMul n} :=
    ⟨fun g => Additive.ofMul (c g), fun g k => congrArg Additive.ofMul (hc g k),
      fun n => congrArg Additive.ofMul (hn n)⟩
  refine ⟨(kleinFourCrossedProjectionEquiv hα4).symm cAdd, ?_, fun b hb => ?_⟩
  · funext g
    have hval := congrFun (congrArg Subtype.val
      ((kleinFourCrossedProjectionEquiv hα4).apply_symm_apply cAdd)) g
    rw [kleinFourCrossedProjectionEquiv_apply] at hval
    exact Additive.ofMul.injective hval.symm
  · apply (kleinFourCrossedProjectionEquiv hα4).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    funext g
    rw [kleinFourCrossedProjectionEquiv_apply]
    exact congrArg Additive.ofMul (congrFun hb.symm g)

/-- Any two normalized multiplicative crossed maps `alternatingGroup α → kleinFour α` differ by a
unique principal crossed map `g ↦ g • v / v` when `Nat.card α = 4`. -/
theorem existsUnique_principal_twist_of_isMulCocycle₁ (hα4 : Nat.card α = 4)
    {c c' : alternatingGroup α → kleinFour α}
    (hc : IsMulCocycle₁ c) (hn : ∀ n : kleinFour α, c n = n)
    (hc' : IsMulCocycle₁ c') (hn' : ∀ n : kleinFour α, c' n = n) :
    ∃! v : kleinFour α, ∀ g : alternatingGroup α, c' g = c g * (g • v / v) := by
  obtain ⟨a, rfl, -⟩ := existsUnique_eq_kleinFourCrossedProjection hα4 hc hn
  obtain ⟨b, rfl, -⟩ := existsUnique_eq_kleinFourCrossedProjection hα4 hc' hn'
  exact existsUnique_kleinFourCrossedProjection_principal_twist hα4 a b

end Cocycle

end alternatingGroup
