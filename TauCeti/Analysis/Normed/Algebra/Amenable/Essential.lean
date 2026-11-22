/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Amenable.Basic
public import TauCeti.Analysis.Normed.Algebra.Derivation.Essential

/-!
# Reduction of amenability to essential bimodules

Let `A` be a normed algebra with a bounded two-sided approximate identity. This file proves that `A`
is amenable if and only if every bounded derivation into the dual of an essential Banach
`A`-bimodule (in the universe of `A`) is inner (`TauCeti.isAmenable_iff_essential`; Runde,
Proposition 2.1.5).

Given any Banach `A`-bimodule `E`, its two-sided essential part
`E_ess = ContinuousLinearMap.essentialBimoduleSubmodule L R` is a closed sub-bimodule that is
itself both left- and right-essential. Innerness on `E_ess` lifts back to `E` via
`TauCeti.exists_eq_dualAction_sub_dualAction_of_restrict_essential`.

## Main results

* `TauCeti.isAmenable_iff_essential`: a normed algebra with a bounded two-sided approximate
  identity is amenable if and only if every bounded derivation into the dual of an essential
  Banach bimodule is inner.

## References

* V. Runde, *Lectures on Amenability*, Springer, 2002, Proposition 2.1.5.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.8.
-/

public section

noncomputable section

universe u v

open Filter ContinuousLinearMap

namespace TauCeti

/-- **Reduction of amenability to essential bimodules** (Runde, Proposition 2.1.5). A normed
algebra with a bounded two-sided approximate identity is amenable if and only if every bounded
derivation into the dual of an essential Banach `A`-bimodule (in the universe of `A`) is inner. -/
theorem isAmenable_iff_essential {𝕜 : Type v} {A : Type u} [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] [ProperSpace 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    {l : Filter A} (hl : l.IsApproximateUnit) {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C) :
    IsAmenable 𝕜 A ↔
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
        (L R : A →L[𝕜] E →L[𝕜] E),
        (∀ a b x, L (a * b) x = L a (L b x)) →
        (∀ a b x, R (a * b) x = R b (R a x)) →
        (∀ a b x, L a (R b x) = R b (L a x)) →
        L.essentialSubmodule = ⊤ →
        R.essentialSubmodule = ⊤ →
        ∀ D : A →L[𝕜] StrongDual 𝕜 E,
          (∀ a b, D (a * b) = dualAction R a (D b) + dualAction L b (D a)) →
          ∃ φ : StrongDual 𝕜 E, ∀ a, D a = dualAction R a φ - dualAction L a φ := by
  have := hl.neBot
  rw [isAmenable_def]
  constructor
  · intro h E _ _ _ L R hL hR hLR _ _ D hD
    exact h E L R hL hR hLR D hD
  · intro h E _ _ _ L R hL hR hLR D hD
    let Eess := essentialBimoduleSubmodule L R
    have : CompleteSpace Eess := (isClosed_essentialBimoduleSubmodule L R).completeSpace_coe
    have hL_inv : ∀ a, ∀ x ∈ Eess, L a x ∈ Eess :=
      fun a _ hx ↦ apply_left_mem_essentialBimoduleSubmodule hLR a hx
    have hR_inv : ∀ a, ∀ x ∈ Eess, R a x ∈ Eess :=
      fun a _ hx ↦ apply_right_mem_essentialBimoduleSubmodule hLR a hx
    let Less : A →L[𝕜] Eess →L[𝕜] Eess := L.restrictAction Eess hL_inv
    let Ress : A →L[𝕜] Eess →L[𝕜] Eess := R.restrictAction Eess hR_inv
    have hLess : ∀ a b x, Less (a * b) x = Less a (Less b x) :=
      L.restrictAction_mul_apply_of_left hL Eess hL_inv
    have hRess : ∀ a b x, Ress (a * b) x = Ress b (Ress a x) :=
      R.restrictAction_mul_apply_of_right hR Eess hR_inv
    have hLRess : ∀ a b x, Less a (Ress b x) = Ress b (Less a x) :=
      restrictAction_apply_comm hLR Eess hL_inv hR_inv
    have hL_top : Less.essentialSubmodule = ⊤ :=
      essentialSubmodule_restrictAction_eq_top L hL hC hl.tendsto_mul_right Eess
        (essentialBimoduleSubmodule_le_left L R) hL_inv
    have hR_top : Ress.essentialSubmodule = ⊤ :=
      essentialSubmodule_restrictAction_eq_top_right R hR hC hl.tendsto_mul_left Eess
        (essentialBimoduleSubmodule_le_right L R) hR_inv
    let Dess : A →L[𝕜] StrongDual 𝕜 Eess := (precomp 𝕜 Eess.subtypeL) ∘L D
    have hDess := precomp_subtypeL_comp_derivation Eess hL_inv hR_inv hD
    obtain ⟨ψ₀, hψ₀⟩ := h Eess Less Ress hLess hRess hLRess hL_top hR_top Dess hDess
    exact exists_eq_dualAction_sub_dualAction_of_restrict_essential hL hR hLR hl hC D hD
      ⟨ψ₀, hψ₀⟩

end TauCeti
