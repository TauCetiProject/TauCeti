/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit
public import TauCeti.Analysis.Normed.Module.Dual.Bimodule
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Analysis.Normed.Module.Dual.BidualApproximation
import TauCeti.Analysis.Normed.Module.Dual.Bilinear
import TauCeti.Analysis.Normed.Ring.ApproximateUnit

/-!
# Amenable Banach algebras and bounded approximate identities

A normed algebra `A` over `𝕜` is *amenable*, in the sense of B. E. Johnson, if for every Banach
`A`-bimodule `E` in the universe of `A` every bounded derivation `D : A → E*` into the dual
bimodule is inner. Here a bimodule is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`,
with `a · x = L a x` and `x · a = R a x`, and the dual `E*` carries the dual actions of
`TauCeti.Analysis.Normed.Module.Dual.Bimodule`: the left action is `dualAction R` and the right
action is `dualAction L`. A bounded derivation is a bounded operator `D` with
`D (a * b) = a · D b + D a · b`, and it is inner when `D a = a · φ - φ · a` for some `φ ∈ E*`.
Equivalently, the first bounded Hochschild cohomology `H¹(A, E*)` vanishes for every such `E` (see
`TauCeti.Analysis.Normed.Algebra.Amenable.Cohomology`).

This file defines `TauCeti.IsAmenable`, proves basic examples (`TauCeti.isAmenable_self`,
`TauCeti.isAmenable_of_subsingleton`), establishes universe-polymorphic bidual innerness
(`TauCeti.IsAmenable.exists_eq_bidual_dualAction_sub_dualAction`), and deduces that every amenable
normed algebra over `ℝ` or `ℂ` has a bounded two-sided approximate identity
(`TauCeti.IsAmenable.exists_isApproximateUnit`) by applying amenability to the canonical inclusion
`J_A : A →L[𝕜] A**` for the one-sided actions `(mul, 0)` and `(0, mul.flip)` and using bidual norm
approximation (`StrongDual.exists_neBot_eventually_norm_le_and_forall_tendsto`) and Dixon's
combination.

For innerness on invariant bidual kernels, see `TauCeti.Analysis.Normed.Algebra.Amenable.Bidual`,
and for Johnson's virtual and bounded approximate diagonal characterizations, see
`TauCeti.Analysis.Normed.Algebra.Amenable.Diagonal`.

## Main definitions

* `TauCeti.IsAmenable`: amenability of a normed algebra.

## Main results

* `TauCeti.isAmenable_self` and `TauCeti.isAmenable_of_subsingleton`: the base field and the zero
  algebra are amenable.
* `TauCeti.IsAmenable.exists_eq_bidual_dualAction_sub_dualAction`: every bounded derivation from an
  amenable normed algebra over `ℝ` or `ℂ` into the bidual `X**` of a normed `A`-bimodule `X` in
  the universe of `A` is inner.
* `TauCeti.IsAmenable.exists_isApproximateUnit`: every amenable normed algebra over `ℝ` or `ℂ` has
  a bounded two-sided approximate identity.

## Implementation notes

`IsAmenable 𝕜 A` quantifies over Banach bimodules in `Type u`, whereas for `X : Type u` and
`𝕜 : Type v` the dual `X* = X →L[𝕜] 𝕜` lies in `Type (max u v)`. When `A` is nontrivial,
Hahn–Banach supplies a nonzero `e` in the completion `Â` of `A` and `π ∈ Â*` with `π e = 1`,
exhibiting `X*` as a bounded bimodule retract of the Banach bimodule `X →L[𝕜] Â : Type u`; when `A`
is subsingleton, every derivation is zero. Thus `IsAmenable 𝕜 A` applies directly to derivations
into `X**` without requiring completeness of `A` or `X`, or tying `u` and `v`.

## References

* B. E. Johnson, *Cohomology in Banach algebras*, Mem. Amer. Math. Soc. 127 (1972).
* V. Runde, *Lectures on Amenability*, Springer, 2002, §2.1 and §2.2.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§2.8–2.9.
-/

public section

noncomputable section

universe u v

open Filter NormedSpace Topology ContinuousLinearMap

namespace TauCeti

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

section Amenable

variable (𝕜 : Type v) (A : Type u) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- A normed algebra `A` over `𝕜` is *amenable* if, for every Banach `A`-bimodule `E` in the
universe of `A`, every bounded derivation of `A` into the dual bimodule `E*` is inner.

The bimodule structure is given by bounded bilinear actions `L R : A →L[𝕜] E →L[𝕜] E`,
`a · x = L a x` and `x · a = R a x`, which need not be unital or contractive. The dual `E*` has
left action `dualAction R` and right action `dualAction L`. A bounded derivation is a bounded
operator `D : A →L[𝕜] E*` with `D (a * b) = a · D b + D a · b`, and it is inner when
`D a = a · φ - φ · a` for some `φ ∈ E*`. -/
def IsAmenable : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (L R : A →L[𝕜] E →L[𝕜] E), (∀ a b x, L (a * b) x = L a (L b x)) →
      (∀ a b x, R (a * b) x = R b (R a x)) → (∀ a b x, L a (R b x) = R b (L a x)) →
      ∀ D : A →L[𝕜] StrongDual 𝕜 E,
        (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
          ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ

variable {𝕜 A}

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- The characteristic property of amenability: for every Banach `A`-bimodule `E` in the universe
of `A`, every bounded derivation `D : A → E*` is inner. -/
theorem isAmenable_def : IsAmenable 𝕜 A ↔
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
      (L R : A →L[𝕜] E →L[𝕜] E), (∀ a b x, L (a * b) x = L a (L b x)) →
        (∀ a b x, R (a * b) x = R b (R a x)) → (∀ a b x, L a (R b x) = R b (L a x)) →
        ∀ D : A →L[𝕜] StrongDual 𝕜 E,
          (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
            ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  Iff.rfl

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- In an amenable normed algebra `A`, every bounded derivation `D` of `A` into the dual `E*` of a
Banach `A`-bimodule `E` in the universe of `A` is inner: `D a = a · φ - φ · a` for some
`φ ∈ E*`, where `E*` has left action `dualAction R` and right action `dualAction L`. -/
theorem IsAmenable.exists_eq_dualAction_sub_dualAction (h : IsAmenable 𝕜 A) {E : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (D : A →L[𝕜] StrongDual 𝕜 E)
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) :
    ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ :=
  h E L R hL hR hLR D hD

variable (𝕜 A) in
omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- Every subsingleton normed algebra (in particular, the zero algebra) is amenable. -/
theorem isAmenable_of_subsingleton [Subsingleton A] : IsAmenable 𝕜 A :=
  fun _ _ _ _ _ _ _ _ _ _ _ ↦ ⟨0, fun a ↦ by simp [Subsingleton.elim a 0]⟩

variable (𝕜) in
/-- Every nontrivially normed field is amenable over itself. -/
theorem isAmenable_self : IsAmenable 𝕜 𝕜 := by
  intro E _ _ _ L R hL hR hLR D hD
  have h1 : D 1 = dualAction R 1 (D 1) + dualAction L 1 (D 1) := by
    simpa only [mul_one] using hD 1 1
  have hRR : dualAction R 1 (dualAction R 1 (D 1)) = dualAction R 1 (D 1) := by
    rw [← dualAction_mul_apply_of_right hR, mul_one]
  have hLL : dualAction L 1 (dualAction L 1 (D 1)) = dualAction L 1 (D 1) := by
    rw [← dualAction_mul_apply_of_left hL, mul_one]
  have hRL : dualAction R 1 (dualAction L 1 (D 1)) = 0 := by
    have h := congrArg (dualAction R 1) h1
    rw [map_add, hRR] at h
    exact left_eq_add.mp h
  have hLR' : dualAction L 1 (dualAction R 1 (D 1)) = 0 := by
    rw [← dualAction_apply_dualAction_apply_comm hLR, hRL]
  refine ⟨dualAction R 1 (D 1) - dualAction L 1 (D 1), fun a ↦ ?_⟩
  have ha : a = a • (1 : 𝕜) := ((smul_eq_mul a 1).trans (mul_one a)).symm
  rw [ha, map_smul, map_smul, map_smul, smul_apply, smul_apply, ← smul_sub, map_sub, map_sub,
    hRR, hRL, hLR', hLL, sub_zero, zero_sub, sub_neg_eq_add, ← h1]

end Amenable

section ApproximateUnit

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- In an amenable normed algebra `A : Type u` over `𝕜 : Type v` (`ℝ` or `ℂ`), every bounded
derivation into the bidual `X**` of a normed `A`-bimodule `X : Type u` is inner, with no
completeness hypothesis on `A` or `X` and no universe constraint between `u` and `v`. -/
theorem IsAmenable.exists_eq_bidual_dualAction_sub_dualAction
    (h : IsAmenable 𝕜 A) {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {L R : A →L[𝕜] X →L[𝕜] X}
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (D : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X))
    (hD : ∀ a b, D (a * b) =
      dualAction (dualAction L) a (D b) + dualAction (dualAction R) b (D a)) :
    ∃ Φ : StrongDual 𝕜 (StrongDual 𝕜 X),
      ∀ a, D a = dualAction (dualAction L) a Φ - dualAction (dualAction R) a Φ := by
  by_cases hA : Subsingleton A
  · exact ⟨0, fun a ↦ by simp [hA.elim a 0]⟩
  -- When `A` is nontrivial, `UniformSpace.Completion A : Type u` is a nontrivial Banach space, and
  -- any functional `π ∈ Y*` with `π e = 1` exhibits `X* : Type (max u v)` as a bounded bimodule
  -- retract of the Banach bimodule `X →L[𝕜] Y : Type u`.
  rw [not_subsingleton_iff_nontrivial] at hA
  have : Nontrivial (UniformSpace.Completion A) :=
    (UniformSpace.Completion.coe_injective A).nontrivial
  suffices ∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y] [Nontrivial Y],
      ∃ Φ : StrongDual 𝕜 (StrongDual 𝕜 X),
        ∀ a, D a = dualAction (dualAction L) a Φ - dualAction (dualAction R) a Φ from
    this (UniformSpace.Completion A)
  intro Y _ _ _ _
  obtain ⟨e, he⟩ := exists_ne (0 : Y)
  obtain ⟨π, hπe⟩ := SeparatingDual.exists_eq_one (R := 𝕜) he
  let L₀ : A →L[𝕜] (X →L[𝕜] Y) →L[𝕜] (X →L[𝕜] Y) := (compL 𝕜 X X Y).flip ∘L R
  let R₀ : A →L[𝕜] (X →L[𝕜] Y) →L[𝕜] (X →L[𝕜] Y) := (compL 𝕜 X X Y).flip ∘L L
  have hL₀ (a b : A) (T : X →L[𝕜] Y) : L₀ (a * b) T = L₀ a (L₀ b T) := by
    ext x; simp [L₀, hR]
  have hR₀ (a b : A) (T : X →L[𝕜] Y) : R₀ (a * b) T = R₀ b (R₀ a T) := by
    ext x; simp [R₀, hL]
  have hLR₀ (a b : A) (T : X →L[𝕜] Y) : L₀ a (R₀ b T) = R₀ b (L₀ a T) := by
    ext x; simp [L₀, R₀, hLR]
  let p : (X →L[𝕜] Y) →L[𝕜] StrongDual 𝕜 X := compL 𝕜 X Y 𝕜 π
  let ι : StrongDual 𝕜 X →L[𝕜] (X →L[𝕜] Y) :=
    compL 𝕜 X 𝕜 Y ((ContinuousLinearMap.id 𝕜 𝕜).smulRight e)
  have hpι (f : StrongDual 𝕜 X) : p (ι f) = f := by ext x; simp [p, ι, hπe]
  have hpL (a : A) (T : X →L[𝕜] Y) : p (L₀ a T) = dualAction R a (p T) := by
    ext x; simp [p, L₀]
  have hpR (a : A) (T : X →L[𝕜] Y) : p (R₀ a T) = dualAction L a (p T) := by
    ext x; simp [p, R₀]
  have hιL (a : A) (f : StrongDual 𝕜 X) : ι (dualAction R a f) = L₀ a (ι f) := by
    ext x; simp [ι, L₀]
  have hιR (a : A) (f : StrongDual 𝕜 X) : ι (dualAction L a f) = R₀ a (ι f) := by
    ext x; simp [ι, R₀]
  let D₀ : A →L[𝕜] StrongDual 𝕜 (X →L[𝕜] Y) := precomp 𝕜 p ∘L D
  have hD₀ (a b : A) : D₀ (a * b) = dualAction R₀ a (D₀ b) + dualAction L₀ b (D₀ a) := by
    simp only [D₀, comp_apply, hD, map_add, precomp_dualAction_apply hpR,
      precomp_dualAction_apply hpL]
  obtain ⟨Ψ, hΨ⟩ := h.exists_eq_dualAction_sub_dualAction hL₀ hR₀ hLR₀ D₀ hD₀
  refine ⟨precomp 𝕜 ι Ψ, fun a ↦ ?_⟩
  have hDa : D a = precomp 𝕜 ι (D₀ a) := by ext f; simp [D₀, hpι]
  rw [hDa, hΨ a, map_sub, precomp_dualAction_apply hιR, precomp_dualAction_apply hιL]

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded right approximate identity. -/
private theorem IsAmenable.exists_tendsto_mul_left (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (a * ·) l (𝓝 a) := by
  -- Apply bidual innerness to `J_A : A →L[𝕜] A**` for the one-sided actions `(mul, 0)`.
  have hD (a b : A) : inclusionInDoubleDual 𝕜 A (a * b) =
      dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A)) a (inclusionInDoubleDual 𝕜 A b) +
        dualAction (dualAction (0 : A →L[𝕜] A →L[𝕜] A)) b (inclusionInDoubleDual 𝕜 A a) := by
    ext f; simp
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_bidual_dualAction_sub_dualAction
    (fun a b x ↦ by simp [mul_assoc]) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (inclusionInDoubleDual 𝕜 A) hD
  obtain ⟨l, hl, hle, ht⟩ := Φ.exists_neBot_eventually_norm_le_and_forall_tendsto
    (fun a ↦ ContinuousLinearMap.mul 𝕜 A a) id (fun a f ↦ by
      have ha := congr($(hΦ a) f)
      simpa only [sub_apply, dualAction_dualAction_apply_apply, zero_apply, comp_zero, map_zero,
        sub_zero, dual_def, id_eq] using ha.symm) le_rfl
  exact ⟨‖Φ‖, l, hl, hle, fun a ↦ (ht a).congr fun e ↦ mul_apply' 𝕜 A a e⟩

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded left approximate identity. -/
private theorem IsAmenable.exists_tendsto_mul_right (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.NeBot ∧ (∀ᶠ e in l, ‖e‖ ≤ C) ∧ ∀ a, Tendsto (· * a) l (𝓝 a) := by
  -- Apply bidual innerness to `-J_A : A →L[𝕜] A**` for the one-sided actions `(0, mul.flip)`.
  have hD (a b : A) : (-inclusionInDoubleDual 𝕜 A) (a * b) =
      dualAction (dualAction (0 : A →L[𝕜] A →L[𝕜] A)) a ((-inclusionInDoubleDual 𝕜 A) b) +
        dualAction (dualAction (ContinuousLinearMap.mul 𝕜 A).flip) b
          ((-inclusionInDoubleDual 𝕜 A) a) := by
    ext f; simp
  obtain ⟨Φ, hΦ⟩ := h.exists_eq_bidual_dualAction_sub_dualAction
    (fun _ _ _ ↦ by simp) (fun a b x ↦ by simp [mul_assoc]) (fun _ _ _ ↦ by simp)
    (-inclusionInDoubleDual 𝕜 A) hD
  obtain ⟨l, hl, hle, ht⟩ := Φ.exists_neBot_eventually_norm_le_and_forall_tendsto
    (fun a ↦ (ContinuousLinearMap.mul 𝕜 A).flip a) id (fun a f ↦ by
      have ha := congr($(hΦ a) f)
      simpa only [neg_apply, sub_apply, dualAction_dualAction_apply_apply, zero_apply, comp_zero,
        map_zero, zero_sub, neg_inj, dual_def, id_eq] using ha.symm) le_rfl
  exact ⟨‖Φ‖, l, hl, hle, fun a ↦ (ht a).congr fun _ ↦ by simp⟩

/-- Every amenable normed algebra over `ℝ` or `ℂ` has a bounded two-sided approximate identity. -/
theorem IsAmenable.exists_isApproximateUnit (h : IsAmenable 𝕜 A) :
    ∃ (C : ℝ) (l : Filter A), l.IsApproximateUnit ∧ ∀ᶠ e in l, ‖e‖ ≤ C := by
  obtain ⟨C, hleft⟩ := h.exists_tendsto_mul_right
  obtain ⟨D, hright⟩ := h.exists_tendsto_mul_left
  exact ⟨C + D + C * D, exists_isApproximateUnit_of_left_of_right hleft hright⟩

end ApproximateUnit

end TauCeti
