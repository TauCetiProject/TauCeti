/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.Frobenius
import Mathlib.LinearAlgebra.Trace
import TauCeti.Algebra.Module.Lattice

/-!
# Schur orthogonality for twisted translates of theta functions

Let `D = (B, χ)` be an Appell–Humbert datum for a full lattice `L` in a finite-dimensional complex
normed space `V`, with positive Riemann form `E`, let `Θ` be its space of theta functions, of
dimension `n`, and let `U_a` be the twisted translation by `a` in the dual `L^⊥` of `L` for `E`.
By Frobenius' dimension formula `n² = [L^⊥ : L]`
(`TauCeti.AppellHumbertData.IsPositive.finrank_thetaSpace_sq`), so `n = √[L^⊥ : L]`.

This file proves the **Schur orthogonality relation** for the twisted translates of theta
functions along the orbits of `L^⊥` on `L^⊥ / L`: if `a : T → L^⊥` is a finite family whose classes
modulo `L` are permuted by translation by every `t ∈ L^⊥`, then for all `f, g ∈ Θ` and `z, w ∈ V`

`n · ∑_{s ∈ T} (U_(-a_s) g) (z) · (U_(a_s) f) (w) = |T| · f (z) · g (w)`

(`TauCeti.AppellHumbertData.IsPositive.finrank_mul_sum_twistedTranslate_mul_twistedTranslate`).
For a set of representatives of `L^⊥ / L` it reads
`∑_q (U_(-q) g) (z) · (U_q f) (w) = n · f (z) · g (w)`
(`TauCeti.AppellHumbertData.IsPositive.sum_dualQuotient_twistedTranslate_mul_twistedTranslate`).
This is the relation that compares modules of functions stable under the twisted translations
with the theta functions they contain.

## Method

The relation is proved without building the theta group. For fixed `g` and `w`, the
endomorphism `f ↦ ∑_s (U_(a_s) f) (w) · U_(-a_s) g` of `Θ` is a sum of rank-one maps
`R_x : f ↦ (U_x f) (w) · U_(-x) g`. Conjugation by `U_t` sends `R_x` to `R_(x - t)`, and `R_x` only
depends on the class of `x` modulo `L`; so the sum commutes with every `U_t`, and is a scalar by
the irreducibility of `Θ` (`TauCeti.AppellHumbertData.IsPositive.exists_eq_smul_one_of_commute`).
The trace of `R_x` is `g (w)`, which determines the scalar.

## Provenance

The relation and its method are adapted from `New.IsAppellHumbert.sum_shift_mul_shift` (file
`src/Lib/Shimura/ThetaNormality/NormalGeneration.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC).
The source states it with the factor `√[L^⊥ : L]`, which is `n` by Frobenius' formula.

## References

* D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research, 1970, Chapter IV, §23
  (the theta group and its irreducible representation on the theta functions).
-/

public section

open Module

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  {D : AppellHumbertData L}

/-! ### Rank-one maps from pairs of translates -/

variable (D) in
/-- The rank-one endomorphism `R_x : f ↦ (U_x f) (w) · U_(-x) g` of the theta functions, for
`x ∈ L^⊥`. -/
private noncomputable def translatePairing (w : V) (g : D.thetaSpace)
    (x : D.riemannForm.dualSubmodule L) : Module.End ℂ D.thetaSpace :=
  ((LinearMap.proj w).comp ((D.twistedTranslate x).comp D.thetaSpace.subtype)).smulRight
    (D.twistedTranslateEnd (-x) g)

private theorem translatePairing_apply (w : V) (g : D.thetaSpace)
    (x : D.riemannForm.dualSubmodule L) (f : D.thetaSpace) :
    (D.translatePairing w g x f : V → ℂ) =
      D.twistedTranslate x f w • D.twistedTranslate (-(x : V)) g := by
  rw [translatePairing, LinearMap.smulRight_apply, Submodule.coe_smul,
    coe_twistedTranslateEnd_apply, Submodule.coe_neg, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.proj_apply]

/-- `R_x` only depends on the class of `x` modulo `L`. -/
private theorem translatePairing_eq_of_sub_mem (w : V) (g : D.thetaSpace)
    {x y : D.riemannForm.dualSubmodule L} (h : (x : V) - y ∈ L) :
    D.translatePairing w g x = D.translatePairing w g y := by
  set l : L := ⟨(x : V) - y, h⟩
  have hx : (x : V) = y + l := by simp [l]
  have hx' : -(x : V) = -(y : V) + ((-l : L) : V) := by
    simp only [l, Submodule.coe_neg]
    abel
  -- changing `y` by `l` multiplies `U_y f` by `exp (πi E (y, l)) χ (l)` and `U_(-y) g` by
  -- `exp (πi E (y, l)) χ (l)⁻¹`; the product of the two phases is `exp (2πi E (y, l)) = 1`
  have hphase : Complex.exp (Real.pi * Complex.I * D.riemannForm y l) *
      Complex.exp (Real.pi * Complex.I * D.riemannForm (-(y : V)) (-l : L)) = 1 := by
    have h1 := congrArg (fun c : Circle ↦ (c : ℂ))
      (DFunLike.congr_fun (D.riemannChar_eq_one_iff.mpr y.property) l)
    simp only [riemannChar_apply, Circle.coe_exp, _root_.one_apply, Circle.coe_one] at h1
    rw [← Complex.exp_add, ← h1]
    congr 1
    simp only [Submodule.coe_neg, map_neg, LinearMap.neg_apply, neg_neg]
    push_cast
    ring
  have hχ : (D.semichar l : ℂ) * D.semichar (-l) = 1 := by
    rw [semichar_apply_neg, Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero _)]
  ext f : 2
  rw [translatePairing_apply, translatePairing_apply, hx', hx,
    twistedTranslate_add_eq_smul_of_mem_thetaSpace f.property,
    twistedTranslate_add_eq_smul_of_mem_thetaSpace g.property, Pi.smul_apply, smul_eq_mul,
    smul_smul]
  calc _ = (Complex.exp (Real.pi * Complex.I * D.riemannForm y l) *
        Complex.exp (Real.pi * Complex.I * D.riemannForm (-(y : V)) (-l : L)) *
        ((D.semichar l : ℂ) * D.semichar (-l)) * D.twistedTranslate y f w) •
        D.twistedTranslate (-(y : V)) g := by
        congr 1
        ring
    _ = _ := by rw [hphase, hχ, one_mul, one_mul]

/-- Conjugation by `U_t` sends `R_x` to `R_(x - t)`. -/
private theorem twistedTranslateEnd_mul_translatePairing_mul (w : V) (g : D.thetaSpace)
    (x t : D.riemannForm.dualSubmodule L) :
    D.twistedTranslateEnd t * D.translatePairing w g x * D.twistedTranslateEnd (-t) =
      D.translatePairing w g (x - t) := by
  -- the phases `exp (-πi E (x, -t))` and `exp (-πi E (t, -x))` cancel, as `E` is alternating
  have hphase : Complex.exp (-(Real.pi * Complex.I * D.riemannForm x (-t : V))) *
      Complex.exp (-(Real.pi * Complex.I * D.riemannForm t (-x : V))) = 1 := by
    rw [← Complex.exp_add, map_neg, map_neg, D.riemannForm_swap (x : V) t]
    simp
  ext f : 2
  rw [mul_apply_eq_comp, mul_apply_eq_comp, coe_twistedTranslateEnd_apply,
    translatePairing_apply, map_smul, coe_twistedTranslateEnd_apply, Submodule.coe_neg,
    D.twistedTranslate_twistedTranslate, D.twistedTranslate_twistedTranslate,
    translatePairing_apply, Submodule.coe_sub, Pi.smul_apply, smul_eq_mul, smul_smul,
    ← sub_eq_add_neg, show (t : V) + -x = -(x - t) by abel]
  calc _ = (Complex.exp (-(Real.pi * Complex.I * D.riemannForm x (-t : V))) *
        Complex.exp (-(Real.pi * Complex.I * D.riemannForm t (-x : V))) *
        D.twistedTranslate (x - t : V) f w) • D.twistedTranslate (-((x : V) - t)) g := by
        congr 1
        ring
    _ = _ := by rw [hphase, one_mul]

/-- The trace of `R_x` is `g (w)`. -/
private theorem trace_translatePairing [FiniteDimensional ℂ D.thetaSpace] (w : V)
    (g : D.thetaSpace) (x : D.riemannForm.dualSubmodule L) :
    LinearMap.trace ℂ D.thetaSpace (D.translatePairing w g x) = (g : V → ℂ) w := by
  rw [translatePairing, LinearMap.trace_smulRight, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, coe_twistedTranslateEnd_apply, Submodule.coe_neg,
    twistedTranslate_twistedTranslate_neg, LinearMap.proj_apply]

/-! ### Schur orthogonality -/

section Orthogonality

variable [FiniteDimensional ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Schur orthogonality for twisted translates of theta functions.** Let `D` be a positive
Appell–Humbert datum for a full lattice `L`, with space of theta functions `Θ` of dimension
`n = √[L^⊥ : L]`, and let `a : T → L^⊥` be a finite family such that translation by every
`t ∈ L^⊥` permutes the classes of the `a_s` modulo `L`: some permutation `e` of `T` has
`t + a_s - a_(e s) ∈ L` for all `s`. Then for theta functions `f, g` and `z, w ∈ V`,
`n · ∑_s (U_(-a_s) g) (z) · (U_(a_s) f) (w) = |T| · f (z) · g (w)`. -/
theorem IsPositive.finrank_mul_sum_twistedTranslate_mul_twistedTranslate (hD : D.IsPositive)
    {T : Type*} [Fintype T] (a : T → D.riemannForm.dualSubmodule L)
    (ha : ∀ t : D.riemannForm.dualSubmodule L, ∃ e : Equiv.Perm T,
      ∀ s, (t : V) + a s - a (e s) ∈ L)
    {f g : V → ℂ} (hf : f ∈ D.thetaSpace) (hg : g ∈ D.thetaSpace) (z w : V) :
    (finrank ℂ D.thetaSpace : ℂ) *
        ∑ s, D.twistedTranslate (-(a s : V)) g z * D.twistedTranslate (a s) f w =
      Fintype.card T * f z * g w := by
  have := hD.finiteDimensional_thetaSpace
  set M := ∑ s, D.translatePairing w ⟨g, hg⟩ (a s) with hM
  -- `M` commutes with every `U_t`, as conjugation by `U_t` permutes its summands
  have hcomm (t : D.riemannForm.dualSubmodule L) : Commute (D.twistedTranslateEnd t) M := by
    obtain ⟨e, he⟩ := ha (-t)
    have hconj : D.twistedTranslateEnd t * M * D.twistedTranslateEnd (-t) = M := by
      simp only [hM, Finset.mul_sum, Finset.sum_mul, twistedTranslateEnd_mul_translatePairing_mul]
      refine (Finset.sum_congr rfl fun s _ ↦ translatePairing_eq_of_sub_mem w _ ?_).trans
        (Equiv.sum_comp e fun s ↦ D.translatePairing w ⟨g, hg⟩ (a s))
      convert he s using 1
      simp only [Submodule.coe_sub, Submodule.coe_neg]
      abel
    calc D.twistedTranslateEnd t * M = D.twistedTranslateEnd t * M *
          (D.twistedTranslateEnd (-t) * D.twistedTranslateEnd t) := by
          rw [twistedTranslateEnd_neg_mul, mul_one]
      _ = M * D.twistedTranslateEnd t := by rw [← mul_assoc, hconj]
  -- so `M` is a scalar `c`, and its trace `|T| · g (w)` is `c · n`
  obtain ⟨c, hc⟩ := hD.exists_eq_smul_one_of_commute hcomm
  have htrace : c * finrank ℂ D.thetaSpace = Fintype.card T * g w := by
    have h := congrArg (LinearMap.trace ℂ D.thetaSpace) hc
    simp only [hM, map_sum, trace_translatePairing, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, map_smul, LinearMap.trace_one, smul_eq_mul] at h
    exact h.symm
  -- evaluating `M f = c • f` at `z`
  have happly : ∑ s, D.twistedTranslate (a s) f w * D.twistedTranslate (-(a s : V)) g z =
      c * f z := by
    have h := congrArg (fun A : Module.End ℂ D.thetaSpace ↦ (A ⟨f, hf⟩ : V → ℂ) z) hc
    simpa [hM, translatePairing_apply] using h
  simp only [mul_comm (D.twistedTranslate (-(a _ : V)) g z), happly]
  linear_combination f z * htrace

/-- **Schur orthogonality over representatives of `L^⊥ / L`.** For a positive Appell–Humbert
datum with space of theta functions `Θ` of dimension `n`, theta functions `f, g` and `z, w ∈ V`,
`∑_q (U_(-q) g) (z) · (U_q f) (w) = n · f (z) · g (w)`, where `q` runs through a set of
representatives of `L^⊥ / L`. -/
theorem IsPositive.sum_dualQuotient_twistedTranslate_mul_twistedTranslate (hD : D.IsPositive)
    [Fintype D.DualQuotient] {f g : V → ℂ} (hf : f ∈ D.thetaSpace) (hg : g ∈ D.thetaSpace)
    (z w : V) :
    ∑ q : D.DualQuotient,
        D.twistedTranslate (-(q.out : V)) g z * D.twistedTranslate q.out f w =
      finrank ℂ D.thetaSpace * f z * g w := by
  -- translation by `t` permutes the classes `q ↦ q + [t]`
  have ha (t : D.riemannForm.dualSubmodule L) : ∃ e : Equiv.Perm D.DualQuotient,
      ∀ q : D.DualQuotient, (t : V) + q.out - (e q).out ∈ L := by
    refine ⟨Equiv.addRight (QuotientAddGroup.mk t), fun q ↦ ?_⟩
    have h : (QuotientAddGroup.mk (t + q.out) : D.DualQuotient) =
        QuotientAddGroup.mk (Equiv.addRight (QuotientAddGroup.mk t) q).out := by
      simp [add_comm]
    have hmem : ((-(t + q.out) + (Equiv.addRight (QuotientAddGroup.mk t) q).out :
        D.riemannForm.dualSubmodule L) : V) ∈ L := QuotientAddGroup.eq.mp h
    convert neg_mem hmem using 1
    simp only [Submodule.coe_add, Submodule.coe_neg]
    abel
  have h := hD.finrank_mul_sum_twistedTranslate_mul_twistedTranslate
    (fun q : D.DualQuotient ↦ q.out) ha hf hg z w
  have hcard : (Fintype.card D.DualQuotient : ℂ) = finrank ℂ D.thetaSpace ^ 2 := by
    rw [← Nat.cast_pow, hD.finrank_thetaSpace_sq, ← Submodule.natCard_quotient_submoduleOf,
      Nat.card_eq_fintype_card]
  have hn : (finrank ℂ D.thetaSpace : ℂ) ≠ 0 := by
    exact_mod_cast hD.finrank_thetaSpace_pos.ne'
  rw [hcard] at h
  exact mul_left_cancel₀ hn (by linear_combination h)

end Orthogonality

end TauCeti.AppellHumbertData
