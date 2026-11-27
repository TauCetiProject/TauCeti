/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Volume
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity

/-!
# The contact volume

Let `α` be a contact form on a manifold `M` of dimension `2 n + 1`. Its volume form `α ∧ (dα)ⁿ`
vanishes nowhere, and `hα.volumeOrientation hn` is the orientation on which it is positive
(`TauCeti.SmoothForm.IsContactForm.volumeOrientation`). The **contact volume** of `α` is

`vol(α) = ∫_M α ∧ (dα)ⁿ`

against that orientation (`TauCeti.SmoothForm.IsContactForm.contactVolume`). On a compact
nonempty manifold it is positive (`TauCeti.SmoothForm.IsContactForm.contactVolume_pos`). On a
noncompact manifold the volume form is not compactly supported, and the contact volume is the
junk value `0`.

Pullback commutes with the wedge product, wedge powers and the exterior derivative, so a smooth map
`f` pulls `β ∧ (dβ)ⁿ` back to `(f^* β) ∧ (d(f^* β))ⁿ`
(`TauCeti.SmoothForm.mpullback_wedge_wedgePow_mextDerivₗ`). By the change of variables formula, the
integral of `β ∧ (dβ)ⁿ` against any orientation is therefore unchanged by an orientation-preserving
diffeomorphism and changes sign under an orientation-reversing one
(`Diffeomorph.integralTopForm_wedge_wedgePow_mpullback_of_isOrientationPreservingAt`,
`Diffeomorph.integralTopForm_wedge_wedgePow_mpullback_of_isOrientationReversingAt`).

For contact forms this gives the transformation law of the contact volume. Let `e : M ≃ N` be a
diffeomorphism with `e^* β = f α` for a function `f`. By the scaling law
`(f α) ∧ (d(f α))ⁿ = fⁿ⁺¹ α ∧ (dα)ⁿ` (`TauCeti.SmoothForm.wedge_wedgePow_apply_of_eq_smul`), the map
`e` pulls the volume form of `β` back to `fⁿ⁺¹` times that of `α`. If `fⁿ⁺¹ > 0` everywhere, as for
a coorientation-preserving contactomorphism, then `e` preserves the two orientations and

`vol(β) = ∫_M fⁿ⁺¹ α ∧ (dα)ⁿ`

(`TauCeti.SmoothForm.IsContactForm.contactVolume_eq_integralTopForm_of_mpullback_eq_smul`); if
`fⁿ⁺¹ < 0` everywhere, `e` reverses them and the sign changes. In particular strict
contactomorphisms preserve the contact volume
(`Diffeomorph.IsStrictContactomorphism.contactVolume_eq`), and a constant multiple scales it by
the absolute value of the constant: `vol(c α) = |c|ⁿ⁺¹ vol(α)`
(`TauCeti.SmoothForm.IsContactForm.contactVolume_smul`).

**Gray stability does not hold for contact forms.** Gray's theorem
(`TauCeti.SmoothForm.exists_diffeotopy_mpullback_eq_pos_smul`) carries a family of contact forms on
a closed manifold to the initial form only up to a positive multiplier. The multiplier cannot be
removed. For `αₜ = (1 + t) α` the kernel does not move, but no diffeomorphism `Φ` satisfies
`Φ^* α₁ = α₀`: it would make `Φ` a strict contactomorphism from `α` to `2 α`, and on a compact
nonempty manifold a diffeomorphism pulling `c α` back to `α` forces `|c| = 1`, since
`vol(α) = vol(c α) = |c|ⁿ⁺¹ vol(α)` and `vol(α) > 0`
(`TauCeti.SmoothForm.IsContactForm.abs_eq_one_of_isStrictContactomorphism_smul`).

## Main definitions

* `TauCeti.SmoothForm.IsContactForm.contactVolume`: the integral of `α ∧ (dα)ⁿ` against the
  orientation of `α`.

## Main results

* `TauCeti.SmoothForm.mpullback_wedge_wedgePow_mextDerivₗ`:
  `f^* (β ∧ (dβ)ⁿ) = (f^* β) ∧ (d(f^* β))ⁿ`.
* `TauCeti.SmoothForm.mpullback_wedge_wedgePow_of_mpullback_eq_smul`: a map with `f^* β = g α` pulls
  `β ∧ (dβ)ⁿ` back to `gⁿ⁺¹ α ∧ (dα)ⁿ`.
* `Diffeomorph.integralTopForm_wedge_wedgePow_mpullback_of_isOrientationPreservingAt`,
  `Diffeomorph.integralTopForm_wedge_wedgePow_mpullback_of_isOrientationReversingAt`: the integral
  of `β ∧ (dβ)ⁿ` is unchanged up to sign by a diffeomorphism.
* `TauCeti.SmoothForm.IsContactForm.contactVolume_pos`: the contact volume of a compact nonempty
  contact manifold is positive.
* `TauCeti.SmoothForm.IsContactForm.contactVolume_eq_integralTopForm_of_mpullback_eq_smul`,
  `TauCeti.SmoothForm.IsContactForm.contactVolume_eq_neg_integralTopForm_of_mpullback_eq_smul`:
  the contact volume under a diffeomorphism with `e^* β = f α`.
* `Diffeomorph.IsStrictContactomorphism.contactVolume_eq`: strict contactomorphisms preserve the
  contact volume.
* `TauCeti.SmoothForm.IsContactForm.contactVolume_smul`: `vol(c α) = |c|ⁿ⁺¹ vol(α)`.
* `TauCeti.SmoothForm.IsContactForm.abs_eq_one_of_isStrictContactomorphism_smul`: on a compact
  nonempty manifold, a diffeomorphism pulling `c α` back to `α` forces `|c| = 1`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 (the volume form `α ∧ (dα)ⁿ`) and Theorem 2.2.2 (Gray stability).
* S. Courte and S. Guillermou, *Introduction to symplectic and contact geometry*, course notes,
  Université Grenoble Alpes (2018), Theorem 3.10 (Gray stability on closed manifolds).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {n : ℕ}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A smooth map pulls the volume form `β ∧ (dβ)ⁿ` of a one-form `β` back to the volume form
`(f^* β) ∧ (d(f^* β))ⁿ` of the pulled-back one-form. -/
theorem mpullback_wedge_wedgePow_mextDerivₗ (f : M → N) (hf : ContMDiff I J ∞ f)
    (β : SmoothForm J N ℝ 1) :
    mpullback f hf (wedge β ((mextDerivₗ J 1 β).wedgePow n)) =
      wedge (mpullback f hf β) ((mextDerivₗ I 1 (mpullback f hf β)).wedgePow n) := by
  rw [mpullback_wedge, mpullback_wedgePow, mextDerivₗ_mpullback]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Volume forms under a map with a multiplier.** If a smooth map `f` pulls `β` back to `g α`
for a differentiable function `g`, it pulls the volume form `β ∧ (dβ)ⁿ` back to
`gⁿ⁺¹ α ∧ (dα)ⁿ`. -/
theorem mpullback_wedge_wedgePow_of_mpullback_eq_smul {f : M → N} (hf : ContMDiff I J ∞ f)
    {α : SmoothForm I M ℝ 1} {β : SmoothForm J N ℝ 1} {g : M → ℝ}
    (hg : MDifferentiable I 𝓘(ℝ, ℝ) g) (hfβ : ∀ x, (mpullback f hf β).val x = g x • α.val x) :
    TauCeti.mpullback I J f (wedge β ((mextDerivₗ J 1 β).wedgePow n)).val =
      fun x ↦ g x ^ (n + 1) • (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x := by
  rw [← coe_mpullback f hf, mpullback_wedge_wedgePow_mextDerivₗ]
  exact funext fun x ↦ wedge_wedgePow_apply_of_eq_smul (hg x) hfβ

end SmoothForm

end TauCeti

namespace Diffeomorph

open TauCeti TauCeti.SmoothForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {n : ℕ} (e : M ≃ₘ⟮I, J⟯ N) {o : Manifold.Orientation I M (Fin (1 + 2 * n))}
  {o' : Manifold.Orientation J N (Fin (1 + 2 * n))}

/-- **The volume integral under an orientation-preserving diffeomorphism.** For any one-form `β`
and orientations `o`, `o'` preserved by `e`, the integral of `β ∧ (dβ)ⁿ` against `o'` is the
integral of the volume form `(e^* β) ∧ (d(e^* β))ⁿ` of the pulled-back form against `o`. -/
theorem integralTopForm_wedge_wedgePow_mpullback_of_isOrientationPreservingAt
    (ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt o o' e x) (β : SmoothForm J N ℝ 1) :
    integralTopForm o (wedge (mpullback e e.contMDiff β)
        ((mextDerivₗ I 1 (mpullback e e.contMDiff β)).wedgePow n)).val =
      integralTopForm o' (wedge β ((mextDerivₗ J 1 β).wedgePow n)).val := by
  rw [← mpullback_wedge_wedgePow_mextDerivₗ, coe_mpullback]
  exact e.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationPreservingAt ho
    (by simp)

/-- **The volume integral under an orientation-reversing diffeomorphism.** For any one-form `β`
and orientations `o`, `o'` reversed by `e`, the integral of `β ∧ (dβ)ⁿ` against `o'` is minus the
integral of the volume form `(e^* β) ∧ (d(e^* β))ⁿ` of the pulled-back form against `o`. -/
theorem integralTopForm_wedge_wedgePow_mpullback_of_isOrientationReversingAt
    (ho : ∀ x, Manifold.Orientation.IsOrientationReversingAt o o' e x) (β : SmoothForm J N ℝ 1) :
    integralTopForm o (wedge (mpullback e e.contMDiff β)
        ((mextDerivₗ I 1 (mpullback e e.contMDiff β)).wedgePow n)).val =
      -integralTopForm o' (wedge β ((mextDerivₗ J 1 β).wedgePow n)).val := by
  rw [← mpullback_wedge_wedgePow_mextDerivₗ, coe_mpullback]
  exact e.toHomeomorph.isOpenEmbedding.integralTopForm_mpullback_of_isOrientationReversingAt ho
    (by simp)

end Diffeomorph

namespace TauCeti

namespace SmoothForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {n : ℕ} {α : SmoothForm I M ℝ 1} {β : SmoothForm J N ℝ 1}

namespace IsContactForm

/-- The **contact volume** of a contact form `α` on a manifold of dimension `2 n + 1`: the integral
of its volume form `α ∧ (dα)ⁿ` against the orientation `hα.volumeOrientation hn` on which that form
is positive. It is positive on a compact nonempty manifold (`IsContactForm.contactVolume_pos`)
and is the junk value `0` on a noncompact one, where the volume form is not compactly
supported. -/
def contactVolume (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) : ℝ :=
  integralTopForm (hα.volumeOrientation hn) (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val

/-- The contact volume is the integral of `α ∧ (dα)ⁿ` against the orientation of `α`. -/
theorem contactVolume_def (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) :
    hα.contactVolume hn =
      integralTopForm (hα.volumeOrientation hn) (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val :=
  (rfl)

/-- **The contact volume is positive** on a compact nonempty manifold. -/
theorem contactVolume_pos [CompactSpace M] [Nonempty M] (hα : α.IsContactForm)
    (hn : finrank ℝ E = 2 * n + 1) : 0 < hα.contactVolume hn := by
  have : NeZero (1 + 2 * n) := ⟨by omega⟩
  rw [contactVolume_def, volumeOrientation_def]
  exact integralTopForm_ofTopForm_pos _ _ _

/-- **The contact volume under a diffeomorphism with a positive multiplier.** Let `α` and `β` be
contact forms on manifolds of dimension `2 n + 1`, and let `e : M ≃ N` be a diffeomorphism with
`e^* β = f α` and `fⁿ⁺¹ > 0` everywhere, for instance a coorientation-preserving contactomorphism
with multiplier `f > 0`. Then `vol(β) = ∫_M fⁿ⁺¹ α ∧ (dα)ⁿ`, the integral taken against the
orientation of `α`. -/
theorem contactVolume_eq_integralTopForm_of_mpullback_eq_smul (hβ : β.IsContactForm)
    (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) (hn' : finrank ℝ F = 2 * n + 1)
    (e : M ≃ₘ⟮I, J⟯ N) {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (he : ∀ x, (SmoothForm.mpullback e e.contMDiff β).val x = f x • α.val x)
    (hpos : ∀ x, 0 < f x ^ (n + 1)) :
    hβ.contactVolume hn' = integralTopForm (hα.volumeOrientation hn)
      (fun x ↦ f x ^ (n + 1) • (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x) := by
  -- The diffeomorphism pulls the volume form of `β` back to `fⁿ⁺¹` times that of `α`.
  have hvol := mpullback_wedge_wedgePow_of_mpullback_eq_smul (n := n) e.contMDiff hf he
  have ho : ∀ x, Manifold.Orientation.IsOrientationPreservingAt (hα.volumeOrientation hn)
      (hβ.volumeOrientation hn') e x := fun x ↦ by
    rw [volumeOrientation_def, volumeOrientation_def]
    exact Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
      (hpos x) (congrFun hvol x)
  rw [contactVolume_def,
    ← e.integralTopForm_wedge_wedgePow_mpullback_of_isOrientationPreservingAt ho,
    ← mpullback_wedge_wedgePow_mextDerivₗ, coe_mpullback, hvol]

/-- **The contact volume under a diffeomorphism with a negative multiplier.** Let `α` and `β` be
contact forms on manifolds of dimension `2 n + 1`, and let `e : M ≃ N` be a diffeomorphism with
`e^* β = f α` and `fⁿ⁺¹ < 0` everywhere, for instance a contactomorphism with multiplier `f < 0`
when `n` is even. Then `vol(β) = -∫_M fⁿ⁺¹ α ∧ (dα)ⁿ`, the integral taken against the orientation
of `α`. -/
theorem contactVolume_eq_neg_integralTopForm_of_mpullback_eq_smul (hβ : β.IsContactForm)
    (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) (hn' : finrank ℝ F = 2 * n + 1)
    (e : M ≃ₘ⟮I, J⟯ N) {f : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (he : ∀ x, (SmoothForm.mpullback e e.contMDiff β).val x = f x • α.val x)
    (hneg : ∀ x, f x ^ (n + 1) < 0) :
    hβ.contactVolume hn' = -integralTopForm (hα.volumeOrientation hn)
      (fun x ↦ f x ^ (n + 1) • (wedge α ((mextDerivₗ I 1 α).wedgePow n)).val x) := by
  have hvol := mpullback_wedge_wedgePow_of_mpullback_eq_smul (n := n) e.contMDiff hf he
  have ho : ∀ x, Manifold.Orientation.IsOrientationReversingAt (hα.volumeOrientation hn)
      (hβ.volumeOrientation hn') e x := fun x ↦ by
    rw [volumeOrientation_def, volumeOrientation_def]
    exact Manifold.Orientation.isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
      (hneg x) (congrFun hvol x)
  rw [contactVolume_def, ← neg_neg (integralTopForm _ _),
    ← e.integralTopForm_wedge_wedgePow_mpullback_of_isOrientationReversingAt ho,
    ← mpullback_wedge_wedgePow_mextDerivₗ, coe_mpullback, hvol]

/-- **Scaling of the contact volume.** Multiplying a contact form on a manifold of dimension
`2 n + 1` by a nonzero constant `c` multiplies its contact volume by `|c|ⁿ⁺¹`. For `n` even and
`c < 0` the orientation of `c α` is opposite to that of `α`, which turns the factor `cⁿ⁺¹` of the
volume forms into `|c|ⁿ⁺¹`. -/
theorem contactVolume_smul (hα : α.IsContactForm) {c : ℝ} (hc : c ≠ 0)
    (hn : finrank ℝ E = 2 * n + 1) :
    ((isContactForm_smul_iff hc).2 hα).contactVolume hn = |c| ^ (n + 1) * hα.contactVolume hn := by
  have hcα : ∀ x, (c • α).val x = c • α.val x := fun _ ↦ rfl
  rw [contactVolume_def, contactVolume_def, wedge_smul_wedgePow_mextDerivₗ_smul, Submodule.coe_smul,
    integralTopForm_smul]
  rcases (pow_ne_zero (n + 1) hc).lt_or_gt with hneg | hpos
  · rw [hα.volumeOrientation_eq_neg_of_eq_smul _ hn (fun _ ↦ mdifferentiableAt_const) hcα
      fun _ ↦ hneg, integralTopForm_neg, ← abs_pow, abs_of_neg hneg]
    ring
  · rw [hα.volumeOrientation_eq_of_eq_smul _ hn (fun _ ↦ mdifferentiableAt_const) hcα
      fun _ ↦ hpos, ← abs_pow, abs_of_pos hpos]

/-- **Strict contactomorphisms preserve the contact volume.** A diffeomorphism `e` with
`e^* β = α` between manifolds of dimension `2 n + 1` satisfies `vol(α) = vol(β)`. -/
theorem _root_.Diffeomorph.IsStrictContactomorphism.contactVolume_eq {e : M ≃ₘ⟮I, J⟯ N}
    (h : e.IsStrictContactomorphism α β) (hα : α.IsContactForm) (hβ : β.IsContactForm)
    (hn : finrank ℝ E = 2 * n + 1) (hn' : finrank ℝ F = 2 * n + 1) :
    hα.contactVolume hn = hβ.contactVolume hn' := by
  rw [hβ.contactVolume_eq_integralTopForm_of_mpullback_eq_smul hα hn hn' e (f := fun _ ↦ 1)
    mdifferentiable_const (fun x ↦ by rw [Diffeomorph.isStrictContactomorphism_def.1 h, one_smul])
    fun _ ↦ by simp, contactVolume_def]
  simp

/-- **Sharpness of Gray stability for contact forms.** On a compact nonempty manifold of dimension
`2 n + 1`, a diffeomorphism `e` pulling `c α` back to the contact form `α` forces `|c| = 1`: the
contact volumes satisfy `vol(α) = vol(c α) = |c|ⁿ⁺¹ vol(α)` with `vol(α) > 0`. So for the family
`αₜ = (1 + t) α`, whose kernel does not move, no diffeomorphism pulls `α₁ = 2 α` back to `α₀`, and
Gray stability carries contact forms to the initial form only up to a positive multiplier. -/
theorem abs_eq_one_of_isStrictContactomorphism_smul [CompactSpace M] [Nonempty M]
    (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * n + 1) {e : M ≃ₘ⟮I, I⟯ M} {c : ℝ}
    (h : e.IsStrictContactomorphism α (c • α)) : |c| = 1 := by
  have hc : c ≠ 0 := by
    rintro rfl
    obtain ⟨x⟩ := ‹Nonempty M›
    refine hα.apply_ne_zero x ?_
    rw [← Diffeomorph.isStrictContactomorphism_def.1 h, zero_smul, map_zero]
    rfl
  have hcα := (isContactForm_smul_iff hc).2 hα
  have hvol := h.contactVolume_eq hα hcα hn hn
  rw [contactVolume_smul hα hc hn] at hvol
  have hpow : (|c| ^ (n + 1) - 1) * hα.contactVolume hn = 0 := by
    rw [sub_mul, one_mul, ← hvol, sub_self]
  replace hpow := sub_eq_zero.1 ((mul_eq_zero.1 hpow).resolve_right (hα.contactVolume_pos hn).ne')
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg c) (Nat.succ_ne_zero n)).1 hpow

end IsContactForm

end SmoothForm

end TauCeti
