/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RingTheory.Perfectoid.UniformTilt.Plus
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Theta

/-!
# Examples of Fontaine's map on the integral tilt

These examples test Fontaine's map `θ : W(B♭⁺) → B⁺` and the comparison `B♭⁺ ≃+* PreTilt B⁺ p`:

* for `B = ℂ_p` and a pseudouniformiser `ϖ` with compatible roots, `PreTilt.untilt` sends the image
  of `ϖ♭` to `ϖ`, and `θ [ϖ♭] = ϖ`;
* in mixed characteristic `θ` is not the sharp of the zeroth Witt coordinate, unlike in
  characteristic `p`: `θ p = p`, while the zeroth coordinate of `p` vanishes;
* `θ` needs no perfectoid hypothesis: it exists on `W(lim ℤ_p)` for `B = ℚ_p`, which is not
  perfectoid, and it is compatible with the inclusion `ℚ_p → ℂ_p`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.14(i).
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltTheta

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` is topologically nilpotent in `ℂ_p`, as `‖p‖ < 1`. -/
local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

/-- `p` is topologically nilpotent in `ℚ_p`, as `‖p‖ < 1`. -/
local instance : Fact (IsTopologicallyNilpotent (p : ℚ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one⟩

/-- `ℂ_p°` is a ring of integral elements. -/
theorem plusC : IsRingOfIntegralElements (powerBoundedSubring ℂ_[p]) :=
  isRingOfIntegralElements_powerBoundedSubring _

/-- `ℚ_p°` is a ring of integral elements. -/
theorem plusQ : IsRingOfIntegralElements (powerBoundedSubring ℚ_[p]) :=
  isRingOfIntegralElements_powerBoundedSubring _

/-- `p` is not a unit of `ℂ_p°`. -/
local instance : Fact ¬IsUnit (p : powerBoundedSubring ℂ_[p]) :=
  ⟨(plusC p).not_isUnit_natCast⟩

/-- `ℂ_p°` is `p`-adically complete. -/
local instance :
    IsAdicComplete (Ideal.span {(p : powerBoundedSubring ℂ_[p])}) (powerBoundedSubring ℂ_[p]) :=
  (plusC p).isAdicComplete_span_natCast

variable (ϖ : PseudoUniformizerRoots p ℂ_[p])

/-- `ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` as an element of the integral tilt of `ℂ_p`. -/
noncomputable def rootPlus : uniformTilt.plusSubring p (plusC p) :=
  ⟨uniformTilt.mk ϖ.root ϖ.root_succ_pow, UniformTiltPlus.mk_root_mem_plusSubring p ϖ⟩

/-- `PreTilt.untilt` sends the image of `ϖ♭` in `PreTilt ℂ_p° p` to `ϖ`. -/
theorem coe_untilt_plusEquivPreTilt_rootPlus :
    ((PreTilt.untilt (uniformTilt.plusEquivPreTilt (plusC p) (rootPlus p ϖ)) :
      powerBoundedSubring ℂ_[p]) : ℂ_[p]) = ϖ.root 0 := by
  rw [uniformTilt.coe_untilt_plusEquivPreTilt, rootPlus, uniformTilt.coeff_mk]

/-- `θ [ϖ♭] = ϖ` in `ℂ_p`. -/
theorem coe_theta_teichmuller_rootPlus :
    (uniformTilt.theta (plusC p) (WittVector.teichmuller p (rootPlus p ϖ)) : ℂ_[p]) = ϖ.root 0 := by
  rw [uniformTilt.coe_theta_teichmuller, rootPlus, uniformTilt.coeff_mk]

/-- In mixed characteristic `θ` is not the sharp of the zeroth Witt coordinate: the formula of
`uniformTilt.coe_theta_of_charP` fails for `ℂ_p` at `p`. -/
theorem coe_theta_natCast_ne :
    (uniformTilt.theta (plusC p) (p : WittVector p (uniformTilt.plusSubring p (plusC p))) : ℂ_[p]) ≠
      uniformTilt.coeff p ℂ_[p] 0 ((WittVector.coeff (p : WittVector p _) 0 :
        uniformTilt.plusSubring p (plusC p)) : uniformTilt p ℂ_[p]) := by
  rw [WittVector.coeff_p_zero, map_natCast, Subring.coe_natCast, Subring.coe_zero,
    uniformTilt.coeff_zero]
  exact Nat.cast_ne_zero.mpr hp.out.ne_zero

/-- `θ` is compatible with the inclusion of `ℚ_p`, which is not perfectoid, into `ℂ_p`. -/
theorem theta_natural_algebraMap (x : WittVector p (uniformTilt.plusSubring p (plusQ p))) :
    (uniformTilt.theta (plusC p) (WittVector.map (uniformTilt.plusMap (plusQ p) (plusC p)
      (algebraMap ℚ_[p] ℂ_[p]) (continuous_algebraMap ℚ_[p] ℂ_[p]) fun y hy ↦ by
        simpa [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, norm_algebraMap']
          using hy) x) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] (uniformTilt.theta (plusQ p) x) :=
  congrArg Subtype.val (RingHom.congr_fun (uniformTilt.theta_natural (plusQ p) (plusC p) _ _ _) x)

end TauCeti.Examples.UniformTiltTheta
