/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Dynamics.Transitive
public import Mathlib.GroupTheory.GroupAction.IterateAct
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Baire.Lemmas
import Mathlib.Data.Int.Interval
import TauCeti.GroupTheory.GroupAction.Orbit.Basic
import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.Topology.Homeomorph.Semiconj

/-!
# Points with dense orbits of topologically transitive actions

For a topologically transitive monoid action by continuous maps on a second-countable space, the
points with dense orbit form a residual set (`MulAction.setOf_dense_orbit_mem_residual`): if `b` is
a countable basis, a point has dense orbit exactly when it lies in each of the open sets
`⋃ m, (m • ·) ⁻¹' B`, `B ∈ b` nonempty (`MulAction.setOf_dense_orbit_eq_biInter`), which are dense
by transitivity. Even without transitivity this set is a `G_δ` (`MulAction.isGδ_setOf_dense_orbit`).
On a nonempty Baire space such a point therefore exists (`MulAction.exists_dense_orbit`). Conversely
a group action with a dense orbit is topologically transitive
(`MulAction.isTopologicallyTransitive_of_dense_orbit`).

For a homeomorphism `T` of a space `X`, transitivity of the `ℤ`-action is transitivity of the
action of `Subgroup.zpowers T` on `X`, and forward transitivity is transitivity of the
`ℕ`-action of `IterateMulAct T`. Forward transitivity of `T` and of `T.symm` are equivalent
(`Homeomorph.isTopologicallyTransitive_iterateMulAct_symm_iff`). On a Hausdorff space without
isolated points, `ℤ`-transitivity implies forward transitivity
(`Homeomorph.isTopologicallyTransitive_iterateMulAct_of_zpowers`): every nonempty open set returns
to itself at arbitrarily late times (`Homeomorph.exists_le_pow_apply_mem_of_zpowers`), since either
some `T ^ k !` fixes it pointwise, or it contains a smaller open set disjoint from its images under
`T ^ j`, `1 ≤ j ≤ k`, two disjoint open parts of which are joined by transitivity at a time beyond
`k`; such a late return of `U ∩ (T ^ n) ⁻¹' V` turns a negative time `n` from `U` to `V` into a
nonnegative one.

On a second-countable Baire `T₁` space without isolated points, which need not be Hausdorff, the
same conclusion follows through a point `x` with dense `ℤ`-orbit
(`Homeomorph.isTopologicallyTransitive_iterateMulAct_of_zpowers_of_baire`). Since there are no
isolated points, the orbit visits every nonempty open set `V` at infinitely many times `n ∈ ℤ`.
These times cannot be bounded above for one open set and bounded below for another: by transitivity
a nonempty open subset of the first is carried into the second, and its visiting times would be
bounded on both sides. So either every nonempty open set is visited at arbitrarily late times, and
then `T` is forward transitive, or every one at arbitrarily early times, and then `T.symm` is.

Hence the points whose forward and backward orbits are both dense form a residual set
(`Homeomorph.setOf_dense_range_iterate_and_symm_mem_residual`), which is a `G_δ`
(`Homeomorph.isGδ_setOf_dense_range_iterate_and_symm`) and so a dense `G_δ`, and the `ℤ`-action
is transitive exactly when such a point exists
(`Homeomorph.isTopologicallyTransitive_zpowers_iff_exists_dense_range_iterate_and_symm`); a dense
forward orbit alone already makes the `ℤ`-action transitive on any space
(`Homeomorph.isTopologicallyTransitive_zpowers_of_dense_range_iterate`). These hold in
particular for a homeomorphism of a nonempty compact metric space without isolated points.

## Main results

* `MulAction.setOf_dense_orbit_mem_residual`: for a topologically transitive action by continuous
  maps on a second-countable space, the points with dense orbit form a residual set.
* `MulAction.isGδ_setOf_dense_orbit`: for an action by continuous maps on a second-countable
  space, the points with dense orbit form a `G_δ` set.
* `MulAction.isTopologicallyTransitive_of_dense_orbit`: a group action with a dense orbit is
  topologically transitive.
* `Homeomorph.isTopologicallyTransitive_iterateMulAct_of_zpowers`: `ℤ`-transitivity of a
  homeomorphism implies forward transitivity on a Hausdorff space without isolated points.
* `Homeomorph.isTopologicallyTransitive_iterateMulAct_of_zpowers_of_baire`: the same on a
  second-countable Baire `T₁` space without isolated points.
* `Homeomorph.isTopologicallyTransitive_zpowers_iff_exists_dense_range_iterate_and_symm`: on a
  nonempty second-countable Baire `T₁` space without isolated points, `ℤ`-transitivity is
  equivalent to the existence of a point whose forward and backward orbits are both dense.
* `Homeomorph.setOf_dense_range_iterate_and_symm_mem_residual`: on a second-countable Baire `T₁`
  space without isolated points, if the `ℤ`-action is transitive, such points form a residual set,
  hence a dense set.
* `Homeomorph.isGδ_setOf_dense_range_iterate_and_symm`: on any second-countable space, such points
  form a `G_δ` set.
-/

public section

open Set Filter Topology TopologicalSpace

namespace MulAction

variable (M : Type*) {X : Type*} [TopologicalSpace X]

section SMul

variable [SMul M X]

/-- If `b` is a topological basis, a point has dense orbit exactly when its orbit meets every
nonempty `B ∈ b`. -/
@[to_additive /-- If `b` is a topological basis, a point has dense orbit exactly when its orbit
meets every nonempty `B ∈ b`. -/]
theorem setOf_dense_orbit_eq_biInter {b : Set (Set X)} (hb : IsTopologicalBasis b) :
    {x : X | Dense (orbit M x)} = ⋂ B ∈ {B ∈ b | B.Nonempty}, ⋃ m : M, (m • ·) ⁻¹' B := by
  ext x
  simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_preimage, hb.dense_iff, and_imp]
  exact forall₃_congr fun B _ _ ↦
    ⟨fun ⟨_, hB, m, hm⟩ ↦ ⟨m, by rwa [← hm] at hB⟩, fun ⟨m, hm⟩ ↦ ⟨_, hm, m, rfl⟩⟩

/-- For an action by continuous maps on a second-countable space, the points with dense orbit
form a `G_δ` set. -/
@[to_additive /-- For an action by continuous maps on a second-countable space, the points with
dense orbit form a `G_δ` set. -/]
theorem isGδ_setOf_dense_orbit [ContinuousConstSMul M X] [SecondCountableTopology X] :
    IsGδ {x : X | Dense (orbit M x)} := by
  obtain ⟨b, hbc, -, hb⟩ := exists_countable_basis X
  rw [setOf_dense_orbit_eq_biInter M hb]
  exact .biInter_of_isOpen (hbc.mono (sep_subset _ _)) fun B hB ↦
    isOpen_iUnion fun m ↦ (hb.isOpen hB.1).preimage (continuous_const_smul m)

end SMul

section MulAction

variable [Monoid M] [MulAction M X]

/-- For a topologically transitive action by continuous maps on a second-countable space, the
points with dense orbit form a residual set. -/
@[to_additive /-- For a topologically transitive action by continuous maps on a second-countable
space, the points with dense orbit form a residual set. -/]
theorem setOf_dense_orbit_mem_residual [ContinuousConstSMul M X] [SecondCountableTopology X]
    [IsTopologicallyTransitive M X] : {x : X | Dense (orbit M x)} ∈ residual X := by
  obtain ⟨b, hbc, -, hb⟩ := exists_countable_basis X
  rw [setOf_dense_orbit_eq_biInter M hb, countable_bInter_mem (hbc.mono (sep_subset _ _))]
  exact fun B hB ↦ residual_of_dense_open
    (isOpen_iUnion fun m ↦ (hb.isOpen hB.1).preimage (continuous_const_smul m))
    ((hb.isOpen hB.1).dense_iUnion_preimage_smul M hB.2)

/-- A topologically transitive action by continuous maps on a nonempty second-countable Baire
space has a point with dense orbit. -/
@[to_additive /-- A topologically transitive action by continuous maps on a nonempty
second-countable Baire space has a point with dense orbit. -/]
theorem exists_dense_orbit [ContinuousConstSMul M X] [SecondCountableTopology X] [BaireSpace X]
    [Nonempty X] [IsTopologicallyTransitive M X] : ∃ x : X, Dense (orbit M x) :=
  (dense_of_mem_residual (setOf_dense_orbit_mem_residual M)).nonempty

/-- A group action with a dense orbit is topologically transitive. -/
@[to_additive /-- An additive group action with a dense orbit is topologically transitive. -/]
theorem isTopologicallyTransitive_of_dense_orbit {G : Type*} [Group G] [MulAction G X] {x : X}
    (hx : Dense (orbit G x)) : IsTopologicallyTransitive G X := by
  refine ⟨fun {U V} hU hUne hV hVne ↦ ?_⟩
  obtain ⟨_, hu, g, rfl⟩ := hx.inter_open_nonempty U hU hUne
  obtain ⟨_, hv, h, rfl⟩ := hx.inter_open_nonempty V hV hVne
  exact ⟨h * g⁻¹, h • x, ⟨g • x, hu, by simp [mul_smul]⟩, hv⟩

end MulAction

end MulAction

namespace Dense

open MulAction

variable {X : Type*} [TopologicalSpace X]

/-- Without isolated points, a dense two-sided orbit visits every nonempty open set at infinitely
many times. -/
theorem infinite_setOf_zpow_apply_mem [T1Space X] [∀ x : X, (𝓝[≠] x).NeBot] {T : X ≃ₜ X}
    {x : X} (hx : Dense (orbit (Subgroup.zpowers T) x)) {V : Set X} (hV : IsOpen V)
    (hVne : V.Nonempty) : {n : ℤ | (T ^ n) x ∈ V}.Infinite := by
  intro hfin
  obtain ⟨_, hyV, hyo, hyS⟩ := (hx.sdiff_finite (hfin.image fun n : ℤ ↦ (T ^ n) x))
    |>.inter_open_nonempty V hV hVne
  obtain ⟨n, rfl⟩ := mem_orbit_zpowers_iff.1 hyo
  exact hyS ⟨n, hyV, (Homeomorph.smul_def _ _).symm⟩

end Dense

namespace Homeomorph

open MulAction

variable {X : Type*} [TopologicalSpace X]

/-- Forward transitivity of a homeomorphism implies forward transitivity of its inverse. -/
theorem isTopologicallyTransitive_iterateMulAct_symm (T : X ≃ₜ X)
    [h : IsTopologicallyTransitive (IterateMulAct ⇑T) X] :
    IsTopologicallyTransitive (IterateMulAct ⇑T.symm) X := by
  refine ⟨fun {U V} hU hUne hV hVne ↦ ?_⟩
  obtain ⟨⟨n⟩, _, ⟨v, hv, rfl⟩, hu⟩ := h.exists_smul_inter hV hVne hU hUne
  refine ⟨⟨n⟩, v, ⟨_, hu, ?_⟩, hv⟩
  simp only [IterateMulAct.mk_smul]
  exact (Function.LeftInverse.iterate (fun y ↦ T.symm_apply_apply y) n) v

/-- A homeomorphism is forward transitive exactly when its inverse is. -/
theorem isTopologicallyTransitive_iterateMulAct_symm_iff (T : X ≃ₜ X) :
    IsTopologicallyTransitive (IterateMulAct ⇑T.symm) X ↔
      IsTopologicallyTransitive (IterateMulAct ⇑T) X :=
  ⟨fun _ ↦ by
    have := isTopologicallyTransitive_iterateMulAct_symm T.symm
    rwa [Homeomorph.symm_symm] at this,
    fun _ ↦ isTopologicallyTransitive_iterateMulAct_symm T⟩

/-- If the two-sided orbit of `x` visits every nonempty open set at arbitrarily late times, then
`T` is forward transitive. -/
theorem isTopologicallyTransitive_iterateMulAct_of_not_bddAbove (T : X ≃ₜ X) (x : X)
    (h : ∀ V : Set X, IsOpen V → V.Nonempty → ¬BddAbove {n : ℤ | (T ^ n) x ∈ V}) :
    IsTopologicallyTransitive (IterateMulAct ⇑T) X := by
  refine ⟨fun {U V} hU hUne hV hVne ↦ ?_⟩
  obtain ⟨k, hk⟩ := nonempty_of_not_bddAbove (h U hU hUne)
  obtain ⟨j, hj, hkj⟩ := not_bddAbove_iff.1 (h V hV hVne) k
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m + k := ⟨(j - k).toNat, by omega⟩
  refine ⟨⟨m⟩, _, ⟨(T ^ k) x, hk, ?_⟩, hj⟩
  simp [zpow_add]

/-- A homeomorphism with a dense forward orbit has topologically transitive `ℤ`-action. -/
theorem isTopologicallyTransitive_zpowers_of_dense_range_iterate (T : X ≃ₜ X) {x : X}
    (hx : Dense (range fun n : ℕ ↦ T^[n] x)) :
    IsTopologicallyTransitive (Subgroup.zpowers T) X := by
  refine isTopologicallyTransitive_of_dense_orbit (x := x) (hx.mono ?_)
  rintro _ ⟨n, rfl⟩
  exact mem_orbit_zpowers_iff.2 ⟨n, by rw [zpow_natCast, Homeomorph.smul_def, Homeomorph.coe_pow]⟩

/-- **Late returns.** On a Hausdorff space without isolated points, if the `ℤ`-action of a
homeomorphism `T` is topologically transitive, every nonempty open set `W` returns to itself under
`T ^ n` for arbitrarily large `n : ℕ`. -/
theorem exists_le_pow_apply_mem_of_zpowers [T2Space X] [∀ x : X, (𝓝[≠] x).NeBot] (T : X ≃ₜ X)
    [h : IsTopologicallyTransitive (Subgroup.zpowers T) X] {W : Set X} (hW : IsOpen W)
    (hWne : W.Nonempty) (k : ℕ) : ∃ n : ℕ, k ≤ n ∧ ∃ w ∈ W, (T ^ n) w ∈ W := by
  -- If `T ^ k.factorial` fixes `W` pointwise, then `W` returns to itself at time `k.factorial * k`.
  by_cases hfix : ∀ w ∈ W, (T ^ k.factorial) w = w
  · obtain ⟨w, hw⟩ := hWne
    refine ⟨k.factorial * k, Nat.le_mul_of_pos_left k k.factorial_pos, w, hw, ?_⟩
    rwa [pow_mul, coe_pow, Function.iterate_fixed (hfix w hw) k]
  -- Otherwise some `y ∈ W` is fixed by no `T ^ j` with `1 ≤ j ≤ k`, so a neighbourhood `W'` of `y`
  -- in `W` is disjoint from its images under these powers.
  push Not at hfix
  obtain ⟨y, hyW, hy⟩ := hfix
  have hne (j : ℕ) (hj : j ∈ Finset.Icc 1 k) : (T ^ j) y ≠ y := fun hjy ↦ by
    obtain ⟨m, hm⟩ := Nat.dvd_factorial (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
    exact hy (by rw [hm, pow_mul, coe_pow]; exact Function.iterate_fixed hjy m)
  have hev : ∀ᶠ p in 𝓝 y ×ˢ 𝓝 y, ∀ j ∈ Finset.Icc 1 k, (T ^ j) p.1 ≠ p.2 := by
    rw [← nhds_prod_eq, eventually_all_finset]
    exact fun j hj ↦ (isOpen_ne_fun ((T ^ j).continuous.comp continuous_fst)
      continuous_snd).mem_nhds (hne j hj)
  obtain ⟨t, ht, hsep⟩ :=
    eventually_prod_self_iff (r := fun a b ↦ ∀ j ∈ Finset.Icc 1 k, (T ^ j) a ≠ b) |>.1 hev
  obtain ⟨W', hW'W, hW', hyW', hW't⟩ : ∃ W' ⊆ W, IsOpen W' ∧ y ∈ W' ∧ W' ⊆ t :=
    ⟨W ∩ interior t, inter_subset_left, hW.inter isOpen_interior,
      ⟨hyW, mem_interior_iff_mem_nhds.2 ht⟩, inter_subset_right.trans interior_subset⟩
  -- Transitivity between two disjoint nonempty open subsets of `W'` gives a nonzero return time
  -- of `W'`, which must exceed `k`.
  obtain ⟨z, hzW', hzy⟩ :=
    Filter.nonempty_of_mem (sdiff_mem_nhdsWithin_compl (hW'.mem_nhds hyW') {y})
  obtain ⟨u, v, hu, hv, hzu, hyv, huv⟩ := t2_separation (mem_singleton_iff.not.1 hzy)
  obtain ⟨⟨_, n, rfl⟩, _, ⟨b, ⟨hbW', hbv⟩, rfl⟩, haW', hau⟩ :=
    h.exists_smul_inter (hW'.inter hv) ⟨y, hyW', hyv⟩ (hW'.inter hu) ⟨z, hzW', hzu⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · exact (disjoint_left.1 huv (by simpa using hau) hbv).elim
  obtain ⟨m, hm0, a, ha, hma⟩ : ∃ m : ℕ, m ≠ 0 ∧ ∃ a ∈ W', (T ^ m) a ∈ W' := by
    obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
    · exact ⟨m, by omega, b, hbW', by simpa using haW'⟩
    · exact ⟨m, by omega, _, haW', by simpa [zpow_neg] using hbW'⟩
  rcases lt_or_ge k m with hkm | hmk
  · exact ⟨m, hkm.le, a, hW'W ha, hW'W hma⟩
  · exact (hsep a (hW't ha) _ (hW't hma) m (Finset.mem_Icc.2 ⟨by omega, hmk⟩) rfl).elim

/-- **`ℤ`-transitivity implies forward transitivity.** On a Hausdorff space without isolated
points, a homeomorphism whose `ℤ`-action is topologically transitive is forward transitive. -/
theorem isTopologicallyTransitive_iterateMulAct_of_zpowers [T2Space X] [∀ x : X, (𝓝[≠] x).NeBot]
    (T : X ≃ₜ X) [h : IsTopologicallyTransitive (Subgroup.zpowers T) X] :
    IsTopologicallyTransitive (IterateMulAct ⇑T) X := by
  refine ⟨fun {U V} hU hUne hV hVne ↦ ?_⟩
  obtain ⟨⟨_, n, rfl⟩, _, ⟨u, hu, rfl⟩, hv⟩ := h.exists_smul_inter hU hUne hV hVne
  -- A time `n < 0` from `U` to `V` is corrected by a return of `U ∩ (T ^ n) ⁻¹' V` to itself at a
  -- time `m ≥ -n`.
  obtain ⟨m, hm, w, ⟨hwU, -⟩, -, hmw⟩ := exists_le_pow_apply_mem_of_zpowers T
    (hU.inter (hV.preimage (T ^ n).continuous)) ⟨u, hu, hv⟩ n.natAbs
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j - m := ⟨(n + m).toNat, by omega⟩
  refine ⟨⟨j⟩, _, ⟨w, hwU, rfl⟩, ?_⟩
  have hj : T ^ (j : ℤ) = T ^ ((j : ℤ) - m) * T ^ m := by
    rw [← zpow_natCast T m, ← zpow_add, sub_add_cancel]
  simp only [IterateMulAct.mk_smul]
  rw [← coe_pow, ← zpow_natCast, hj, mul_apply]
  exact hmw

/-- On a second-countable space, the points whose forward and backward orbits under a
homeomorphism `T` are both dense form a `G_δ` set. -/
theorem isGδ_setOf_dense_range_iterate_and_symm [SecondCountableTopology X] (T : X ≃ₜ X) :
    IsGδ {x : X | Dense (range fun n : ℕ ↦ T^[n] x) ∧ Dense (range fun n : ℕ ↦ T.symm^[n] x)} := by
  have h₁ := isGδ_setOf_dense_orbit (IterateMulAct ⇑T) (X := X)
  have h₂ := isGδ_setOf_dense_orbit (IterateMulAct ⇑T.symm) (X := X)
  simp only [orbit_iterateMulAct] at h₁ h₂
  exact h₁.inter h₂

variable [T1Space X] [∀ x : X, (𝓝[≠] x).NeBot] [SecondCountableTopology X] [BaireSpace X]

/-- `ℤ`-transitivity implies forward transitivity on a second-countable Baire `T₁` space without
isolated points. This covers the non-Hausdorff second-countable Baire `T₁` spaces without isolated
points, which `isTopologicallyTransitive_iterateMulAct_of_zpowers` does not. -/
theorem isTopologicallyTransitive_iterateMulAct_of_zpowers_of_baire (T : X ≃ₜ X)
    [h : IsTopologicallyTransitive (Subgroup.zpowers T) X] :
    IsTopologicallyTransitive (IterateMulAct ⇑T) X := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun {U V} _ ⟨u, _⟩ ↦ isEmptyElim u⟩
  obtain ⟨x, hx⟩ := exists_dense_orbit (Subgroup.zpowers T) (X := X)
  have hinf V (hV : IsOpen V) (hVne : V.Nonempty) := hx.infinite_setOf_zpow_apply_mem hV hVne
  -- A set visited at bounded-above times and a set visited at bounded-below times cannot both
  -- exist: a nonempty open part of the first carried into the second would be visited at times
  -- bounded on both sides.
  have key : (∀ V : Set X, IsOpen V → V.Nonempty → ¬BddAbove {n : ℤ | (T ^ n) x ∈ V}) ∨
      ∀ V : Set X, IsOpen V → V.Nonempty → ¬BddBelow {n : ℤ | (T ^ n) x ∈ V} := by
    by_contra! hcon
    obtain ⟨⟨V₁, hV₁, hV₁ne, a, ha⟩, ⟨V₂, hV₂, hV₂ne, b, hb⟩⟩ := hcon
    obtain ⟨⟨_, n, rfl⟩, _, ⟨v, hv, rfl⟩, hv₂⟩ := h.exists_smul_inter hV₁ hV₁ne hV₂ hV₂ne
    refine hinf (V₁ ∩ (T ^ n) ⁻¹' V₂) (hV₁.inter (hV₂.preimage (T ^ n).continuous)) ⟨v, hv, hv₂⟩
      ((finite_Icc (b - n) a).subset fun m hm ↦ ⟨?_, ha hm.1⟩)
    have hm₂ : (T ^ (n + m)) x ∈ V₂ := by
      rw [zpow_add, Homeomorph.mul_apply]
      exact hm.2
    have : b ≤ n + m := hb hm₂
    omega
  rcases key with hA | hB
  · exact isTopologicallyTransitive_iterateMulAct_of_not_bddAbove T x hA
  · rw [← isTopologicallyTransitive_iterateMulAct_symm_iff]
    have hsymm (n : ℤ) : (T.symm ^ (-n)) x = (T ^ n) x := by simp [← inv_def]
    refine isTopologicallyTransitive_iterateMulAct_of_not_bddAbove T.symm x
      fun V hV hVne ⟨a, ha⟩ ↦ hB V hV hVne ⟨-a, fun n hn ↦ ?_⟩
    have : -n ≤ a := ha (by rwa [mem_ofPred_eq, hsymm])
    omega

/-- **Points with dense forward and backward orbits.** On a second-countable Baire `T₁` space
without isolated points, if the `ℤ`-action of a homeomorphism `T` is topologically transitive,
the points whose forward and backward orbits are both dense form a residual set. Together with
`isGδ_setOf_dense_range_iterate_and_symm` and `dense_of_mem_residual`, they form a dense `G_δ`. -/
theorem setOf_dense_range_iterate_and_symm_mem_residual (T : X ≃ₜ X)
    [IsTopologicallyTransitive (Subgroup.zpowers T) X] :
    {x : X | Dense (range fun n : ℕ ↦ T^[n] x) ∧ Dense (range fun n : ℕ ↦ T.symm^[n] x)} ∈
      residual X := by
  have hT := isTopologicallyTransitive_iterateMulAct_of_zpowers_of_baire T
  have hT' := (isTopologicallyTransitive_iterateMulAct_symm_iff T).2 hT
  have h₁ := setOf_dense_orbit_mem_residual (IterateMulAct ⇑T) (X := X)
  have h₂ := setOf_dense_orbit_mem_residual (IterateMulAct ⇑T.symm) (X := X)
  simp only [orbit_iterateMulAct] at h₁ h₂
  exact inter_mem h₁ h₂

/-- **Transitivity of a homeomorphism through dense orbits.** On a nonempty second-countable Baire
`T₁` space without isolated points, such as a nonempty compact metric space without isolated
points, the `ℤ`-action of a homeomorphism `T` is topologically transitive exactly when some point
has dense forward and backward orbits. -/
theorem isTopologicallyTransitive_zpowers_iff_exists_dense_range_iterate_and_symm [Nonempty X]
    (T : X ≃ₜ X) :
    IsTopologicallyTransitive (Subgroup.zpowers T) X ↔
      ∃ x : X, Dense (range fun n : ℕ ↦ T^[n] x) ∧ Dense (range fun n : ℕ ↦ T.symm^[n] x) :=
  ⟨fun _ ↦ (dense_of_mem_residual (setOf_dense_range_iterate_and_symm_mem_residual T)).nonempty,
    fun ⟨_, hx, _⟩ ↦ isTopologicallyTransitive_zpowers_of_dense_range_iterate T hx⟩

end Homeomorph
