/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Subring
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Perfectoid.Plus
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Theta
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for Fontaine's map on the tilt of a uniform Tate ring

These checks evaluate Fontaine's map `θ : W(B♭⁺) → B⁺` for `B = ℂ_p` and `B⁺ = ℂ_p°`, on the
element `p♭ = (p ^ (1 / p ^ n))ₙ` of the integral tilt given by a compatible system of `p`-power
roots of `p`:

* `θ [p♭] = p`;
* `p - [p♭]` is a nonzero element of the kernel of `θ`, so `θ` is not injective;
* `θ` is surjective, as `ℂ_p` is perfectoid;
* in characteristic `p`, `θ` kills `p`, so it factors through `W(B♭⁺) ⧸ p = B♭⁺`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.14.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.UniformTiltTheta

variable (p : ℕ) [hp : Fact p.Prime]

/-- `p` is topologically nilpotent in `ℂ_p`, as `‖p‖ < 1`. -/
local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

/-- The ring of integral elements `ℂ_p°`. -/
local notation "hC" => isRingOfIntegralElements_powerBoundedSubring ℂ_[p]

/-- A compatible system `(p ^ (1 / p ^ n))ₙ` of `p`-power roots of `p` in `ℂ_p`. -/
private noncomputable def rootsOfP : Perfection ℂ_[p] p :=
  (Perfection.coeffMonoidHom_surjective
    (fun x ↦ IsAlgClosed.exists_pow_nat_eq x hp.out.pos) 0 (p : ℂ_[p])).choose

private theorem coeff_zero_rootsOfP : Perfection.coeffMonoidHom ℂ_[p] p 0 (rootsOfP p) = p :=
  (Perfection.coeffMonoidHom_surjective
    (fun x ↦ IsAlgClosed.exists_pow_nat_eq x hp.out.pos) 0 (p : ℂ_[p])).choose_spec

/-- The element `p♭ = (p ^ (1 / p ^ n))ₙ` of the integral tilt of `ℂ_p°`. -/
private noncomputable def pFlat : uniformTilt.plusSubring p hC :=
  ⟨uniformTilt.mk (fun n ↦ Perfection.coeffMonoidHom ℂ_[p] p n (rootsOfP p))
      (Perfection.coeffMonoidHom_pow_p' (rootsOfP p)),
    uniformTilt.mem_plusSubring_iff_coeff_zero.mpr <| by
      rw [uniformTilt.coeff_mk, coeff_zero_rootsOfP]
      exact natCast_mem _ p⟩

private theorem plusSharp_pFlat : (uniformTilt.plusSharp p hC (pFlat p) : ℂ_[p]) = p := by
  simp only [uniformTilt.coe_plusSharp, pFlat, uniformTilt.coeff_mk, coeff_zero_rootsOfP]

/-- `θ [p♭] = p`. -/
example : (uniformTilt.theta p hC (WittVector.teichmuller p (pFlat p)) : ℂ_[p]) = p := by
  rw [uniformTilt.theta_teichmuller, plusSharp_pFlat]

/-- `p - [p♭]` lies in the kernel of `θ`. -/
example : uniformTilt.theta p hC ((p : WittVector p (uniformTilt.plusSubring p hC)) -
    WittVector.teichmuller p (pFlat p)) = 0 := by
  rw [map_sub, map_natCast, uniformTilt.theta_teichmuller]
  exact sub_eq_zero.mpr (Subtype.ext (plusSharp_pFlat p).symm)

/-- `p - [p♭]` is nonzero: otherwise `p♭`, the zeroth Witt coordinate of `p` in characteristic
`p`, would vanish, while its sharp is `p ≠ 0`. So `θ` is not injective. -/
example : (p : WittVector p (uniformTilt.plusSubring p hC)) -
    WittVector.teichmuller p (pFlat p) ≠ 0 := by
  intro h0
  have h := congrArg (WittVector.coeff · 0) (sub_eq_zero.mp h0)
  simp only [WittVector.coeff_p_zero, WittVector.teichmuller_coeff_zero] at h
  have hs := plusSharp_pFlat p
  rw [← h, map_zero, ZeroMemClass.coe_zero] at hs
  exact Nat.cast_ne_zero.mpr hp.out.ne_zero hs.symm

/-- `θ` is surjective for `ℂ_p`, which is perfectoid. -/
example : Function.Surjective (uniformTilt.theta p hC) :=
  uniformTilt.surjective_theta hC (hC).exists_natCast_dvd_sub_pow

/-- In characteristic `p`, `θ` kills `p`. -/
example {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B] [CharP B p] [Nontrivial B]
    [Fact (IsTopologicallyNilpotent (p : B))] {Bplus : Subring B}
    (h : IsRingOfIntegralElements Bplus) :
    uniformTilt.theta p h (p : WittVector p (uniformTilt.plusSubring p h)) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

end TauCeti.Examples.UniformTiltTheta
