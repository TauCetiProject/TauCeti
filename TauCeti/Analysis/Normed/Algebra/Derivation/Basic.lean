/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Bimodule

/-!
# Basic closure and restriction lemmas for bounded derivations

Let `A` be a normed algebra acting on a seminormed space `E` through bounded bilinear maps
`L R : A →L[𝕜] E →L[𝕜] E`, and let `D` be a bounded derivation from `A` into a bounded bimodule
or a dual bimodule `E*`. This file provides basic algebraic and submodule-restriction tools:

* subtracting an inner derivation from a bounded derivation preserves the derivation law
  (`TauCeti.derivation_sub_inner` and `TauCeti.derivation_sub_inner_dualAction`);
* restricting the values of a dual-valued bounded derivation to a jointly invariant submodule `p`
  preserves the derivation law for the restricted actions
  (`TauCeti.precomp_subtypeL_comp_derivation`);
* when the restriction to a jointly invariant submodule `p` is inner, Hahn–Banach extension
  produces a residual bounded derivation annihilating `p`
  (`TauCeti.exists_residual_derivation_of_restrict`).

## Main results

* `TauCeti.derivation_sub_inner` and `TauCeti.derivation_sub_inner_dualAction`: bounded derivations
  are closed under subtracting inner derivations.
* `TauCeti.precomp_subtypeL_comp_derivation`: restricting a dual-valued derivation to a jointly
  invariant submodule preserves its Leibniz law.
* `TauCeti.exists_residual_derivation_of_restrict`: Hahn–Banach reduction of a bounded derivation
  that is inner on a jointly invariant submodule to a residual derivation vanishing on that
  submodule.
-/

public section

noncomputable section

open ContinuousLinearMap

namespace TauCeti

section DerivationHelpers

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A] [Mul A]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Subtracting an inner derivation from a bounded derivation into a bounded bimodule yields a
bounded derivation. -/
theorem derivation_sub_inner {L R : A →L[𝕜] F →L[𝕜] F}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {D : A →L[𝕜] F}
    (hD : ∀ a b, D (a * b) = L a (D b) + R b (D a)) (x : F) (a b : A) :
    (D - (L.flip x - R.flip x)) (a * b) =
      L a ((D - (L.flip x - R.flip x)) b) + R b ((D - (L.flip x - R.flip x)) a) := by
  simp only [sub_apply, flip_apply, hD, hL, hR, hLR, map_sub]
  abel

/-- Subtracting an inner derivation from a bounded derivation into a dual bimodule yields a
bounded derivation. -/
theorem derivation_sub_inner_dualAction {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (ψ : StrongDual 𝕜 E) (a b : A) :
    (D - ((dualAction R).flip ψ - (dualAction L).flip ψ)) (a * b) =
      dualAction R a ((D - ((dualAction R).flip ψ - (dualAction L).flip ψ)) b) +
        dualAction L b ((D - ((dualAction R).flip ψ - (dualAction L).flip ψ)) a) :=
  derivation_sub_inner (dualAction_mul_apply_of_right hR)
    (dualAction_mul_apply_of_left hL) (dualAction_apply_dualAction_apply_comm hLR) hD ψ a b

/-- Restricting the values of a dual-valued bounded derivation to any jointly invariant submodule
preserves its Leibniz law for the restricted actions. -/
theorem precomp_subtypeL_comp_derivation {L R : A →L[𝕜] E →L[𝕜] E} (p : Submodule 𝕜 E)
    (hLp : ∀ a, ∀ x ∈ p, L a x ∈ p) (hRp : ∀ a, ∀ x ∈ p, R a x ∈ p)
    {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) (a b : A) :
    ((precomp 𝕜 p.subtypeL) ∘L D) (a * b) =
      dualAction (R.restrictAction p hRp) a (((precomp 𝕜 p.subtypeL) ∘L D) b) +
        dualAction (L.restrictAction p hLp) b (((precomp 𝕜 p.subtypeL) ∘L D) a) := by
  simp only [comp_apply, hD, map_add, precomp_apply, dualAction_restrictAction_comp_subtypeL]

/-- If a bounded derivation `D : A →L[𝕜] E*` restricts to an inner derivation on a jointly invariant
submodule `p`, Hahn–Banach produces a residual bounded derivation `D₁` annihilating `p`. -/
theorem exists_residual_derivation_of_restrict [IsRCLikeNormedField 𝕜]
    {L R : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (hR : ∀ a b x, R (a * b) x = R b (R a x))
    (hLR : ∀ a b x, L a (R b x) = R b (L a x))
    (p : Submodule 𝕜 E) (hLp : ∀ a, ∀ x ∈ p, L a x ∈ p) (hRp : ∀ a, ∀ x ∈ p, R a x ∈ p)
    {D : A →L[𝕜] StrongDual 𝕜 E}
    (hD : ∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a))
    (hp : ∃ ψ₀ : StrongDual 𝕜 p,
      ∀ a, (D a).comp p.subtypeL =
        dualAction (R.restrictAction p hRp) a ψ₀ -
        dualAction (L.restrictAction p hLp) a ψ₀) :
    ∃ (ψ : StrongDual 𝕜 E) (D₁ : A →L[𝕜] StrongDual 𝕜 E),
      (∀ a b, D₁ (a * b) = dualAction R a (D₁ b) + dualAction L b (D₁ a)) ∧
      (∀ a, ∀ x ∈ p, D₁ a x = 0) ∧
      (∀ a, D a = D₁ a + (dualAction R a ψ - dualAction L a ψ)) := by
  obtain ⟨ψ₀, hψ₀⟩ := hp
  obtain ⟨ψ, hψ⟩ := StrongDual.exists_extension p ψ₀
  have hψ_comp : ψ.comp p.subtypeL = ψ₀ := by ext x; exact hψ x
  refine ⟨ψ, D - ((dualAction R).flip ψ - (dualAction L).flip ψ),
    derivation_sub_inner_dualAction hL hR hLR hD ψ, fun a x hx ↦ ?_, fun a ↦ ?_⟩
  · have hcomp : (D a - (dualAction R a ψ - dualAction L a ψ)).comp p.subtypeL = 0 := by
      rw [sub_comp, sub_comp, hψ₀ a, ← dualAction_restrictAction_comp_subtypeL R p hRp a ψ,
        ← dualAction_restrictAction_comp_subtypeL L p hLp a ψ, hψ_comp, sub_self]
    simpa only [sub_apply, flip_apply, comp_apply, Submodule.subtypeL_apply, zero_apply] using
      congrArg (fun f : StrongDual 𝕜 p ↦ f ⟨x, hx⟩) hcomp
  · simp

end DerivationHelpers

end TauCeti
