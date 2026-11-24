/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The Phragmén–Lindelöf principle on the upper half-plane

A function that is bounded on the open upper half-plane, holomorphic there and continuous up to
the real axis is bounded on the closed upper half-plane by any bound it satisfies on the real
axis. This is the rotation by `I` of Mathlib's right half-plane principle
`PhragmenLindelof.right_half_plane_of_bounded_on_real`, specialised to bounded functions.

It is the form of the maximum principle used for correlation functions that continue
analytically into the upper half-plane, such as those of ground states of C⋆-dynamics.
-/

public section

open Complex Filter Set

namespace TauCeti.PhragmenLindelof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {C : ℝ} {z : ℂ}

/-- **Phragmén–Lindelöf principle on the upper half-plane.** If `f` is bounded on the open upper
half-plane, holomorphic there, continuous on its closure, and bounded by `C` on the real axis,
then `f` is bounded by `C` on the closed upper half-plane. -/
theorem upper_half_plane_of_isBounded (hd : DiffContOnCl ℂ f {z | 0 < z.im})
    (hb : Bornology.IsBounded (f '' {z | 0 < z.im})) (hre : ∀ x : ℝ, ‖f x‖ ≤ C)
    (hz : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  -- rotate the right half-plane onto the upper half-plane by `w ↦ I * w`
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  have hmaps : MapsTo (fun w : ℂ => I * w) {w | 0 < w.re} {z | 0 < z.im} := fun w hw => by
    simpa using hw
  have hbound {w : ℂ} (hw : 0 < w.re) : ‖f (I * w)‖ ≤ M := hM _ (mem_image_of_mem f (hmaps hw))
  have h := PhragmenLindelof.right_half_plane_of_bounded_on_real (f := fun w => f (I * w))
    (C := C) (z := -I * z) (hd.comp (differentiable_id.const_mul I).diffContOnCl hmaps)
    ⟨0, two_pos, 0, Asymptotics.IsBigO.of_bound M (eventually_inf_principal.mpr <|
      .of_forall fun w hw => by simpa using hbound hw)⟩
    ⟨M, eventually_map.mpr <| (eventually_gt_atTop 0).mono fun x hx => hbound (by simpa)⟩
    (fun x => by rw [mul_left_comm, I_mul_I, mul_neg_one]; simpa using hre (-x))
    (by simpa using hz)
  rwa [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul] at h

end TauCeti.PhragmenLindelof
