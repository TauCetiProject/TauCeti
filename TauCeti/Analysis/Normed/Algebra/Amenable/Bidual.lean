/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Basic
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Analysis.Normed.Module.Dual.Bidual
import TauCeti.Analysis.Normed.Module.Dual.Bilinear

/-!
# Bidual innerness for amenable normed algebras

This file establishes bidual innerness results for amenable normed algebras over `ℝ` or `ℂ`:

* `TauCeti.IsAmenable.exists_eq_bidual_dualAction_sub_dualAction`: every bounded derivation into
  the bidual `X**` of a normed `A`-bimodule `X` in the universe of `A` is inner, with no
  completeness assumption on `A` or `X` and no universe constraint between the scalar field and `A`.
* `TauCeti.IsAmenable.exists_mem_ker_precomp_precomp_eq_dualAction_sub`: for a bounded closed-range
  operator `T : X →L[𝕜] Y` between Banach spaces in `Type u` whose kernel is invariant under
  bounded bimodule actions `L` and `R` on `X`, the bidual identification
  `ContinuousLinearMap.bidualKerEquivKerPrecompPrecomp` identifies `(ker T)**` isometrically with
  `ker T**`, producing an implementing element in `ker T**` for any bounded derivation valued in
  `ker T**`.

## Main results

* `TauCeti.IsAmenable.exists_eq_bidual_dualAction_sub_dualAction`
* `TauCeti.IsAmenable.exists_mem_ker_precomp_precomp_eq_dualAction_sub`

## Implementation notes

`IsAmenable 𝕜 A` quantifies over Banach bimodules in `Type u`, whereas for `X : Type u` and
`𝕜 : Type v` the dual `X* = X →L[𝕜] 𝕜` lies in `Type (max u v)`. When `A` is nontrivial,
Hahn–Banach supplies a nonzero `e` in the completion `Â` of `A` and `π ∈ Â*` with `π e = 1`,
exhibiting `X*` as a bounded bimodule retract of the Banach bimodule `X →L[𝕜] Â : Type u`; when `A`
is subsingleton, every derivation is zero. Thus `IsAmenable 𝕜 A` applies directly to derivations
into `X**` without requiring completeness of `A` or `X`, or tying `u` and `v`.
-/

public section

noncomputable section

universe u v

open NormedSpace ContinuousLinearMap

namespace TauCeti

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

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

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- In an amenable normed algebra `A` over `ℝ` or `ℂ`, if `T : X →L[𝕜] Y` is a closed-range
operator between Banach spaces in `Type u` whose kernel is invariant under bounded bimodule actions
`L` and `R` on `X`, then every bounded derivation `D₀ : A →L[𝕜] X**` taking values in `ker T**` is
implemented by an element `N ∈ ker T**`. -/
theorem IsAmenable.exists_mem_ker_precomp_precomp_eq_dualAction_sub
    (h : IsAmenable 𝕜 A) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    {T : X →L[𝕜] Y} (hT : IsClosed (T.range : Set Y))
    {L R : A →L[𝕜] X →L[𝕜] X}
    (hL : ∀ a b x, L (a * b) x = L a (L b x))
    (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (hKL : ∀ a x, x ∈ T.ker → L a x ∈ T.ker)
    (hKR : ∀ a x, x ∈ T.ker → R a x ∈ T.ker)
    (D₀ : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X))
    (hD₀ : ∀ a b, D₀ (a * b) =
      dualAction (dualAction L) a (D₀ b) + dualAction (dualAction R) b (D₀ a))
    (hD₀_ker : ∀ a, D₀ a ∈
      (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) :
        StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 Y)).ker) :
    ∃ N : StrongDual 𝕜 (StrongDual 𝕜 X),
      N ∈ (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X) :
          StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 Y)).ker ∧
      ∀ a, D₀ a = dualAction (dualAction L) a N - dualAction (dualAction R) a N := by
  -- Phase 1: restrict the bimodule actions `L` and `R` to the invariant submodule `ker T`.
  let LK := L.restrictAction T.ker hKL
  let RK := R.restrictAction T.ker hKR
  have hLK : ∀ a b x, LK (a * b) x = LK a (LK b x) :=
    L.restrictAction_mul_apply_of_left hL T.ker hKL
  have hRK : ∀ a b x, RK (a * b) x = RK b (RK a x) :=
    R.restrictAction_mul_apply_of_right hR T.ker hKR
  have hLRK : ∀ a b x, LK a (RK b x) = RK b (LK a x) :=
    restrictAction_apply_comm hLR T.ker hKL hKR
  -- Phase 2: transport `D₀` across `(ker T)** ≃ₗᵢ ker T**` to a derivation into `(ker T)**`.
  let T₂ : StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 Y) :=
    precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 Y →L[𝕜] StrongDual 𝕜 X)
  let DK : A →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 T.ker) :=
    (T.bidualKerEquivKerPrecompPrecomp hT).symm.toLinearIsometry.toContinuousLinearMap ∘L
      D₀.codRestrict T₂.ker hD₀_ker
  have hDK_coe (a : A) : precomp 𝕜 (precomp 𝕜 T.ker.subtypeL) (DK a) = D₀ a := by
    rw [← T.coe_bidualKerEquivKerPrecompPrecomp hT]
    simp [DK]
  have hSL := precomp_precomp_dualAction_dualAction_apply (T := T.ker.subtypeL) (M := LK) (N := L)
    fun a x ↦ by simp [LK]
  have hSR := precomp_precomp_dualAction_dualAction_apply (T := T.ker.subtypeL) (M := RK) (N := R)
    fun a x ↦ by simp [RK]
  have hDK (a b : A) :
      DK (a * b) = dualAction (dualAction LK) a (DK b) + dualAction (dualAction RK) b (DK a) := by
    apply T.ker.bidualEquivDoubleAnnihilator.injective
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add, T.ker.coe_bidualEquivDoubleAnnihilator,
      hSL, hSR, hDK_coe]
    exact hD₀ a b
  -- Phase 3: apply bidual innerness on `ker T` and push the witness back into `ker T**`.
  obtain ⟨N₀, hN₀⟩ := h.exists_eq_bidual_dualAction_sub_dualAction hLK hRK hLRK DK hDK
  refine ⟨(T.bidualKerEquivKerPrecompPrecomp hT N₀ : StrongDual 𝕜 (StrongDual 𝕜 X)),
    (T.bidualKerEquivKerPrecompPrecomp hT N₀).property, fun a ↦ ?_⟩
  rw [T.coe_bidualKerEquivKerPrecompPrecomp hT, ← hSL, ← hSR, ← map_sub, ← hN₀ a, hDK_coe]

end TauCeti
