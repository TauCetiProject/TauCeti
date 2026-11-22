/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Basic
import TauCeti.Analysis.Normed.Module.Dual.Bidual

/-!
# Bidual kernel innerness for amenable normed algebras

For a bounded closed-range operator `T : X →L[𝕜] Y` between Banach spaces in `Type u` whose kernel
is invariant under bounded bimodule actions `L` and `R` on `X`, the bidual identification
`ContinuousLinearMap.bidualKerEquivKerPrecompPrecomp` identifies `(ker T)**` isometrically with
`ker T**`. Transporting a bounded derivation `D₀ : A →L[𝕜] X**` valued in `ker T**` across this
isometry and applying universe-polymorphic bidual innerness
(`TauCeti.IsAmenable.exists_eq_bidual_dualAction_sub_dualAction`) produces an implementing element
in `ker T**` (`TauCeti.IsAmenable.exists_mem_ker_precomp_precomp_eq_dualAction_sub`).

## Main results

* `TauCeti.IsAmenable.exists_mem_ker_precomp_precomp_eq_dualAction_sub`: every bounded derivation
  from an amenable normed algebra over `ℝ` or `ℂ` into `X**` taking values in `ker T**` for a
  closed-range operator `T` with bimodule-invariant kernel is implemented by an element of
  `ker T**`.
-/

public section

noncomputable section

universe u v

open ContinuousLinearMap

namespace TauCeti

-- Shorten instance search for submodules and operators on iterated duals.
attribute [local instance] ContinuousLinearMap.strongDualSeminormedAddCommGroup
  ContinuousLinearMap.strongDualNormedSpace
  ContinuousLinearMap.strongBidualSeminormedAddCommGroup
  ContinuousLinearMap.strongBidualNormedSpace

variable {𝕜 : Type v} {A : Type u} [RCLike 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

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
  have hSL := precomp_dualAction_apply (T := T.ker.subtypeL) (M := LK) (N := L)
    fun a x ↦ by simp [LK]
  have hSR := precomp_dualAction_apply (T := T.ker.subtypeL) (M := RK) (N := R)
    fun a x ↦ by simp [RK]
  have hDK (a b : A) :
      DK (a * b) = dualAction (dualAction LK) a (DK b) + dualAction (dualAction RK) b (DK a) := by
    apply T.ker.bidualEquivDoubleAnnihilator.injective
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add, T.ker.coe_bidualEquivDoubleAnnihilator,
      precomp_dualAction_apply hSL, precomp_dualAction_apply hSR, hDK_coe]
    exact hD₀ a b
  -- Phase 3: apply bidual innerness on `ker T` and push the witness back into `ker T**`.
  obtain ⟨N₀, hN₀⟩ := h.exists_eq_bidual_dualAction_sub_dualAction hLK hRK hLRK DK hDK
  refine ⟨(T.bidualKerEquivKerPrecompPrecomp hT N₀ : StrongDual 𝕜 (StrongDual 𝕜 X)),
    (T.bidualKerEquivKerPrecompPrecomp hT N₀).property, fun a ↦ ?_⟩
  rw [T.coe_bidualKerEquivKerPrecompPrecomp hT, ← precomp_dualAction_apply hSL,
    ← precomp_dualAction_apply hSR, ← map_sub, ← hN₀ a, hDK_coe]

end TauCeti
