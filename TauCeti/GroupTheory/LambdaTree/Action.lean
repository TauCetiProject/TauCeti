/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LambdaTree.GromovProduct
public import TauCeti.GroupTheory.LyndonLength.Basic

/-!
# Isometric actions on `Λ`-trees and their based length functions

An element `g` of a group acting on a set `X` is *elliptic* when it fixes a point, an
*inversion* when it fixes no point but `g ^ 2` does, and *hyperbolic* when neither `g` nor
`g ^ 2` fixes a point. The action is *free* when every nontrivial element is hyperbolic. For an
action on a `Λ`-tree by isometries these are the three kinds of isometries of a `Λ`-tree, and the
groups acting freely on `Λ`-trees are those studied through their free Lyndon length functions.

For an isometric action of `G` on a `Λ`-tree `X` with metric `d` and a base point `x`, the
*based length function* `g ↦ d x (g • x)` is a Lyndon length function on `G`
(`TauCeti.LambdaMetric.IsTree.basedLength`). Since `d x ((g⁻¹ * f) • x) = d (g • x) (f • x)`,
its Gromov products are the Gromov products `(g • x · f • x)_x` of the tree, so axiom (L3) is the
`0`-hyperbolicity of `Λ`-trees and (L4) is the fact that these Gromov products lie in `Λ`.

Squaring an isometry detects hyperbolicity:
`d x (g • x) < d x (g ^ 2 • x)` holds exactly when `g` is hyperbolic, whatever the base point
(`TauCeti.LambdaMetric.IsTree.dist_smul_lt_dist_sq_smul_iff`). If `d x (g ^ 2 • x) ≤ d x (g • x)`
then the branch point `w` of `[x, g⁻¹ • x]` and `[x, g • x]` is fixed by `g ^ 2`; conversely a
fixed point of `g ^ 2` bounds `d x (g ^ 2 • x)` by `0`-hyperbolicity. Consequently the based
length function is free, meaning it also satisfies (L5), exactly when the action is free
(`TauCeti.LambdaMetric.IsTree.isFree_basedLength_iff`). This is the easy half of Chiswell's
correspondence between free Lyndon length functions and free actions on `Λ`-trees.

The translation action of `Λ` on the `Λ`-tree `Λ` is free, with based length function at `0` the
absolute value. On `ℤ` the reflection `n ↦ 1 - n` is an inversion, and on a one-point space every
element is elliptic, so only the trivial group acts freely there.

## Main definitions

* `TauCeti.LambdaMetric.IsElliptic`, `TauCeti.LambdaMetric.IsInversion`,
  `TauCeti.LambdaMetric.IsHyperbolic`: elliptic elements, inversions and hyperbolic elements.
* `TauCeti.LambdaMetric.IsFreeAction`: every nontrivial element acts hyperbolically.
* `TauCeti.LambdaMetric.IsTree.basedLength`: the based length function `g ↦ d x (g • x)`.

## Main results

* `TauCeti.LambdaMetric.IsTree.exists_coe_eq_gromovProduct_basedLength`: the Gromov products of a
  based length function lie in `Λ`.
* `TauCeti.LambdaMetric.IsTree.dist_smul_lt_dist_sq_smul_iff`: `d x (g • x) < d x (g ^ 2 • x)` if
  and only if `g` is hyperbolic.
* `TauCeti.LambdaMetric.IsTree.isFree_basedLength_iff`: a based length function is free if and
  only if the action is free.
* `TauCeti.LambdaMetric.basedLength_self_zero`, `TauCeti.LambdaMetric.isFreeAction_self`: the
  translation action of `Λ` on itself is free, with based length function the absolute value.

## References

* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §§2.1 and 3.1.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §§4.3–4.4 and §5.
-/

public section

namespace TauCeti.LambdaMetric

variable {Λ G X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]

/-! ### Elliptic elements, inversions and hyperbolic elements -/

section Classification

variable [Monoid G] [MulAction G X] {g : G}

variable (X) in
/-- `g` is *elliptic* when it fixes a point of `X`. -/
def IsElliptic (g : G) : Prop :=
  ∃ x : X, g • x = x

variable (X) in
/-- `g` is an *inversion* when it fixes no point of `X` but `g ^ 2` does. -/
def IsInversion (g : G) : Prop :=
  ¬IsElliptic X g ∧ IsElliptic X (g ^ 2)

variable (X) in
/-- `g` is *hyperbolic* when neither `g` nor `g ^ 2` fixes a point of `X`. -/
def IsHyperbolic (g : G) : Prop :=
  ¬IsElliptic X g ∧ ¬IsElliptic X (g ^ 2)

variable (G X) in
/-- The action of `G` on `X` is *free* (and without inversions) when every nontrivial element is
hyperbolic. -/
def IsFreeAction : Prop :=
  ∀ g : G, g ≠ 1 → IsHyperbolic X g

theorem isElliptic_iff : IsElliptic X g ↔ ∃ x : X, g • x = x :=
  Iff.rfl

/-- An element is elliptic exactly when its set of fixed points is nonempty. -/
theorem isElliptic_iff_nonempty_fixedBy : IsElliptic X g ↔ (MulAction.fixedBy X g).Nonempty :=
  Iff.rfl

theorem isInversion_iff : IsInversion X g ↔ ¬IsElliptic X g ∧ IsElliptic X (g ^ 2) :=
  Iff.rfl

theorem isHyperbolic_iff : IsHyperbolic X g ↔ ¬IsElliptic X g ∧ ¬IsElliptic X (g ^ 2) :=
  Iff.rfl

theorem isFreeAction_iff : IsFreeAction G X ↔ ∀ g : G, g ≠ 1 → IsHyperbolic X g :=
  Iff.rfl

/-- A point fixed by `g` is fixed by every power of `g`. -/
theorem IsElliptic.pow (h : IsElliptic X g) (n : ℕ) : IsElliptic X (g ^ n) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, ?_⟩
  induction n with
  | zero => rw [pow_zero, one_smul]
  | succ n ih => rw [pow_succ, mul_smul, hx, ih]

@[simp]
theorem isElliptic_one [Nonempty X] : IsElliptic X (1 : G) :=
  ⟨Classical.arbitrary X, one_smul G _⟩

/-- An element is hyperbolic exactly when its square fixes no point. -/
theorem isHyperbolic_iff_not_isElliptic_sq : IsHyperbolic X g ↔ ¬IsElliptic X (g ^ 2) :=
  ⟨And.right, fun h => ⟨fun h' => h (h'.pow 2), h⟩⟩

/-- Every element is elliptic, an inversion or hyperbolic, and by definition only one of these. -/
theorem isElliptic_or_isInversion_or_isHyperbolic (g : G) :
    IsElliptic X g ∨ IsInversion X g ∨ IsHyperbolic X g := by
  rw [isInversion_iff, isHyperbolic_iff]
  tauto

/-- On a one-point space every element is elliptic, so only the trivial group acts freely. -/
theorem isFreeAction_iff_subsingleton [Nonempty X] [Subsingleton X] :
    IsFreeAction G X ↔ Subsingleton G := by
  refine ⟨fun h => ⟨fun g₁ g₂ => ?_⟩, fun _ g hg => (hg (Subsingleton.elim g 1)).elim⟩
  have hfix (g : G) : g = 1 := by
    by_contra hg
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (h g hg).1 ⟨x, Subsingleton.elim _ _⟩
  rw [hfix g₁, hfix g₂]

end Classification

/-- The reflection `n ↦ 1 - n` of `ℤ` is an inversion: it fixes no integer, and its square is the
identity. -/
theorem isInversion_subLeft_one : IsInversion ℤ (Equiv.subLeft (1 : ℤ)) := by
  refine ⟨fun ⟨n, hn⟩ => ?_, ⟨0, by simp [pow_two, Equiv.Perm.smul_def]⟩⟩
  rw [Equiv.Perm.smul_def, Equiv.subLeft_apply] at hn
  omega

/-! ### Based length functions -/

namespace IsTree

variable [Group G] [MulAction G X] {d : LambdaMetric Λ X} (hd : d.IsTree)
  (hG : d.IsIsometricAction G)
include hd hG

/-- The *based length function* `g ↦ d x (g • x)` of an isometric action on a `Λ`-tree, at the
base point `x`. Its Gromov products are the Gromov products of the translates of `x`, so it is a
Lyndon length function because `Λ`-trees are `0`-hyperbolic. -/
def basedLength (x : X) : LyndonLength G Λ where
  toFun g := d x (g • x)
  map_one' := by simp
  map_inv' g := hG.dist_inv_smul g x
  eq_of_lt' g f h hlt := by
    simp only [hG.dist_inv_mul_smul] at hlt ⊢
    -- The two smaller of the three Gromov products `(a · b)_x`, `(a · c)_x`, `(b · c)_x` agree.
    have h₁ := hd.min_dist_add_dist_sub_dist_le x (g • x) (f • x) (h • x)
    have h₂ := hd.min_dist_add_dist_sub_dist_le x (f • x) (g • x) (h • x)
    rw [d.symm (f • x) (g • x)] at h₂
    grind [min_le_iff]

@[simp]
theorem basedLength_apply (x : X) (g : G) :
    hd.basedLength hG x g = d x (g • x) :=
  (rfl)

/-- The Gromov products of a based length function lie in `Λ`: this is axiom (L4). -/
theorem exists_coe_eq_gromovProduct_basedLength (x : X) (g f : G) :
    ∃ c : Λ, (c : DivisibleHull Λ) = (hd.basedLength hG x).gromovProduct g f := by
  obtain ⟨c, hc⟩ := hd.even_dist_add_dist_sub_dist x (g • x) (f • x)
  refine ⟨c, (LyndonLength.coe_eq_gromovProduct_iff _).2 ?_⟩
  simp only [basedLength_apply, hG.dist_inv_mul_smul, hc, two_nsmul]

/-- If `g ^ 2` fixes a point, then `g ^ 2` moves every point at most as far as `g` does. -/
theorem dist_sq_smul_le_of_isElliptic_sq {g : G} (hg : IsElliptic X (g ^ 2)) (x : X) :
    d x (g ^ 2 • x) ≤ d x (g • x) := by
  -- For a point `q` fixed by `g ^ 2` with `d x (g • q) ≤ d x q`, compare the Gromov products of
  -- `g⁻¹ • x`, `q` and `g • x` at `x`.
  have key (q : X) (hq : g ^ 2 • q = q) (hle : d x (g • q) ≤ d x q) :
      d x (g ^ 2 • x) ≤ d x (g • x) := by
    have H := hd.min_dist_add_dist_sub_dist_le x (g⁻¹ • x) q (g • x)
    have e₁ : d (g⁻¹ • x) q = d x (g • q) := by rw [← hG.dist_smul_smul g, smul_inv_smul]
    have hq' : g • g • q = q := by rw [smul_smul, ← pow_two, hq]
    have e₂ : d q (g • x) = d x (g • q) := by
      conv_lhs => rw [← hq']
      rw [hG.dist_smul_smul g, d.symm]
    have e₃ : d (g⁻¹ • x) (g • x) = d x (g ^ 2 • x) := by
      rw [← hG.dist_smul_smul g, smul_inv_smul, pow_two, mul_smul]
    rw [e₁, e₂, e₃, hG.dist_inv_smul] at H
    grind [min_le_iff]
  obtain ⟨p, hp⟩ := hg
  by_cases hle : d x (g • p) ≤ d x p
  · exact key p hp hle
  -- Otherwise `g • p` is a fixed point of `g ^ 2` with the required property.
  have hgp : g • p = g ^ 2 • g • p := by rw [smul_smul, ← pow_succ, pow_succ', mul_smul, hp]
  refine key (g • p) hgp.symm ?_
  rw [smul_smul, ← pow_two, hp]
  exact (not_le.1 hle).le

/-- If `g ^ 2` moves a point `x` at most as far as `g` does, then `g ^ 2` fixes the point where
the segments `[x, g⁻¹ • x]` and `[x, g • x]` branch. -/
theorem isElliptic_sq_of_dist_sq_smul_le {g : G} {x : X} (h : d x (g ^ 2 • x) ≤ d x (g • x)) :
    IsElliptic X (g ^ 2) := by
  obtain ⟨w, hw, hinter⟩ := hd.exists_segment_inter_segment_eq x (g⁻¹ • x) (g • x)
  have hw' : w ∈ hd.segment x (g⁻¹ • x) ∩ hd.segment x (g • x) :=
    hinter ▸ hd.right_mem_segment x w
  have hσ := hd.isSegment_segment x (g • x)
  -- `2 • d x w = 2 • d x (g • x) - d x (g ^ 2 • x) ≥ d x (g • x)`.
  have hc := hd.two_nsmul_dist_eq hw hinter
  have e₀ : d (g⁻¹ • x) (g • x) = d x (g ^ 2 • x) := by
    rw [← hG.dist_smul_smul g, smul_inv_smul, pow_two, mul_smul]
  rw [e₀, hG.dist_inv_smul, two_nsmul] at hc
  have hw₁ := hd.mem_segment_iff.1 hw'.1
  have hw₂ := hd.mem_segment_iff.1 hw'.2
  rw [hG.dist_inv_smul] at hw₁
  -- `g • w` lies on `[x, g • x]`, at distance `d x (g • x) - d x w` from `x`.
  have e₁ : d x (g • w) = d w (g⁻¹ • x) := by rw [← hG.dist_smul_smul g⁻¹, inv_smul_smul, d.symm]
  have e₂ : d (g • w) (g • x) = d x w := by rw [hG.dist_smul_smul g, d.symm]
  have hgw : g • w ∈ hd.segment x (g • x) := hd.mem_segment_iff.2 (by grind)
  -- Since `d x (g • x) - d x w ≤ d x w`, it lies on `[x, w]`, hence on `[x, g⁻¹ • x]`.
  have hgw' : g • w ∈ hd.segment x (g⁻¹ • x) := by
    have : g • w ∈ hd.segment x w := hd.mem_segment_iff.2 <| by
      rw [hσ.dist_eq_abs_sub hgw hw'.2, abs_of_nonpos (by grind)]
      grind
    rw [← hinter] at this
    exact this.1
  -- Applying `g`, the point `g ^ 2 • w` lies on `[x, g • x]` at distance `d x w` from `x`, so it
  -- is `w`.
  have hgw₁ := hd.mem_segment_iff.1 hgw'
  rw [hG.dist_inv_smul] at hgw₁
  have e₃ : d (g • g • w) (g • x) = d x (g • w) := by rw [hG.dist_smul_smul g, d.symm]
  have e₄ : d x (g • g • w) = d (g • w) (g⁻¹ • x) := by
    rw [← hG.dist_smul_smul g⁻¹, inv_smul_smul, d.symm]
  have hggw : g • g • w ∈ hd.segment x (g • x) := hd.mem_segment_iff.2 (by grind)
  have hfix : d w (g • g • w) = 0 := by
    rw [hσ.dist_eq_abs_sub hw'.2 hggw, abs_eq_zero, sub_eq_zero]
    grind
  exact ⟨w, by rw [pow_two, mul_smul, ← d.eq_zero_iff.1 hfix]⟩

/-- `g ^ 2` moves a point strictly farther than `g` does exactly when `g` is hyperbolic. In
particular the comparison does not depend on the point. -/
theorem dist_smul_lt_dist_sq_smul_iff {g : G} (x : X) :
    d x (g • x) < d x (g ^ 2 • x) ↔ IsHyperbolic X g := by
  rw [isHyperbolic_iff_not_isElliptic_sq, ← not_le]
  exact not_congr ⟨hd.isElliptic_sq_of_dist_sq_smul_le hG,
    fun h => hd.dist_sq_smul_le_of_isElliptic_sq hG h x⟩

/-- A based length function is free exactly when the action is free: axiom (L5) for
`g ↦ d x (g • x)` says that every nontrivial element is hyperbolic. -/
theorem isFree_basedLength_iff (x : X) : (hd.basedLength hG x).IsFree ↔ IsFreeAction G X := by
  refine ⟨fun hl g hg => ?_, fun h => ⟨hd.exists_coe_eq_gromovProduct_basedLength hG x,
    fun g hg => ?_⟩⟩
  · have := hl.lt_map_sq g hg
    rwa [basedLength_apply, basedLength_apply, hd.dist_smul_lt_dist_sq_smul_iff hG] at this
  · rw [basedLength_apply, basedLength_apply, hd.dist_smul_lt_dist_sq_smul_iff hG]
    exact h g hg

end IsTree

/-! ### The translation action of `Λ` on itself -/

/-- The based length function of the translation action of `Λ` on itself, at `0`, is the absolute
value. -/
theorem basedLength_self_zero :
    (isTree_self (Λ := Λ)).basedLength isIsometricAction_self 0 = LyndonLength.absLength Λ := by
  ext a
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective a
  simp [self_apply]

/-- `Λ` acts freely on the `Λ`-tree `Λ` by translations. -/
theorem isFreeAction_self : IsFreeAction (Multiplicative Λ) Λ := by
  rw [← isTree_self.isFree_basedLength_iff isIsometricAction_self 0, basedLength_self_zero]
  exact LyndonLength.isFree_absLength

end TauCeti.LambdaMetric
