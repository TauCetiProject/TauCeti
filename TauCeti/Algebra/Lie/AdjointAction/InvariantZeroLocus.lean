/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule
import TauCeti.Algebra.Lie.Killing.AdNilpotent
import TauCeti.Algebra.Lie.TracePowerPolynomial
import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
import TauCeti.LinearAlgebra.Trace.Nilpotent

/-!
# Ad-nilpotent elements are the common zeros of the invariant polynomials

Let `L` be a Lie algebra over a field `K` of characteristic zero. The polynomial functions on `L`
are the symmetric algebra `S(L*)` of the dual, a point `x : L` evaluating `p` through
`SymmetricAlgebra.lift (Module.Dual.eval K L x)`, and `L` acts on them through the coadjoint
action by derivations. Its invariants `S(L*)^L` (`TauCeti.SymmetricAlgebra.lieInvariants`) are
the invariant polynomial functions. This file proves that when `L` is finite-dimensional with
nondegenerate Killing form, an element `x` has nilpotent `ad x` exactly when every invariant
polynomial function with zero constant term vanishes at `x`
(`TauCeti.isNilpotent_ad_iff_forall_lift_eval_eq_zero`). That is, the ad-nilpotent elements form
the common zero locus of the invariants of positive degree.

Both directions hold more generally:

* **Invariants vanish on eigenvectors of nonzero eigenvalue.** If `M` is a Lie module and `x : M`
  satisfies `⁅y, x⁆ = a • x` for some `y : L` and some nonzero scalar `a`, then every invariant
  polynomial function on `M` with zero constant term vanishes at `x`
  (`TauCeti.SymmetricAlgebra.lift_eval_eq_zero_of_mem_lieInvariants`). For `p` homogeneous of
  degree `n`, invariance says the derivation by which `y` acts kills `p`. Evaluated at `x`, that
  derivation is multiplication by `-n * a` (Euler's identity, in the form
  `AlgHom.apply_derivationOfEnd_eq_mul_of_mem_homogeneousSubmodule`), so `n * a * p (x) = 0`.
  An ad-nilpotent element of a Lie algebra with nondegenerate Killing form is such an eigenvector:
  it is a bracket `x = ⁅x, t⁆` with itself (`TauCeti.exists_lie_eq_self_of_isNilpotent_ad`).
* **Vanishing invariants force nilpotence in every finite-dimensional module.** The trace-power
  polynomials `x ↦ tr (ρ_M(x) ^ m)` are invariant (`TauCeti.tracePowerPolynomial_mem_lieInvariants`)
  and homogeneous of degree `m`. If all invariants of positive degree vanish at `x`, then all
  traces of positive powers of `ρ_M(x)` vanish, so `ρ_M(x)` is nilpotent by the trace criterion
  `LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero`
  (`TauCeti.isNilpotent_toEnd_of_forall_lift_eval_eq_zero`).

Thus, pointwise, the nilpotent cone is the zero fibre of the map defined by the invariant
polynomial functions of positive degree. For the adjoint quotient `𝔤 → 𝔤 // G` of a group `G`,
this describes the points of its zero fibre wherever its invariant algebra is `S(𝔤*)^𝔤`.

## Main results

* `TauCeti.SymmetricAlgebra.lift_eval_eq_zero_of_mem_homogeneousLieInvariant`,
  `TauCeti.SymmetricAlgebra.lift_eval_eq_zero_of_mem_lieInvariants`: an invariant polynomial
  function of positive degree, respectively with zero constant term, vanishes at every
  eigenvector of a nonzero eigenvalue.
* `TauCeti.isNilpotent_toEnd_of_forall_lift_eval_eq_zero`: if every invariant polynomial function
  with zero constant term vanishes at `x`, then `x` acts nilpotently on every finite-dimensional
  module.
* `TauCeti.isNilpotent_ad_iff_forall_lift_eval_eq_zero`: in a finite-dimensional Lie algebra with
  nondegenerate Killing form, `ad x` is nilpotent exactly when every invariant polynomial function
  with zero constant term vanishes at `x`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1, for
  the invariant polynomial functions and the trace-power invariants.
* B. Kostant, *Lie group representations on polynomial rings*, Amer. J. Math. 85 (1963),
  327–404, for the nilpotent cone as the zero locus of the invariants of positive degree.
-/

public section

open LieAlgebra LieModule Module _root_.SymmetricAlgebra

namespace TauCeti

namespace SymmetricAlgebra

section Eigenvector

variable {R L M : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **A homogeneous invariant polynomial function of positive degree vanishes at every eigenvector
of a nonzero eigenvalue.** If `p` on the Lie module `M` is invariant and homogeneous of degree
`n ≠ 0`, and `⁅y, x⁆ = a • x` with `a ≠ 0`, then `p (x) = 0`. -/
theorem lift_eval_eq_zero_of_mem_homogeneousLieInvariant {n : ℕ} (hn : n ≠ 0)
    {p : _root_.SymmetricAlgebra R (Dual R M)} (hp : p ∈ homogeneousLieInvariant R L (Dual R M) n)
    {y : L} {x : M} {a : R} (hyx : ⁅y, x⁆ = a • x) (ha : a ≠ 0) :
    lift (Dual.eval R M x) p = 0 := by
  rw [mem_homogeneousLieInvariant] at hp
  -- evaluation at `x` turns the coadjoint action of `y` into multiplication by `-a`
  have h := (lift (Dual.eval R M x)).apply_derivationOfEnd_eq_mul_of_mem_homogeneousSubmodule
    (f := toEnd R L (Dual R M) y) (c := -a) (fun ξ ↦ by simp [hyx]) hp.2
  rw [← lieModuleDerivation_apply, mem_lieInvariants.mp hp.1 y, map_zero] at h
  simpa [hn, ha] using h.symm

/-- **An invariant polynomial function with zero constant term vanishes at every eigenvector of a
nonzero eigenvalue.** If `p` on the Lie module `M` is invariant with `algebraMapInv p = 0`, and
`⁅y, x⁆ = a • x` with `a ≠ 0`, then `p (x) = 0`. -/
theorem lift_eval_eq_zero_of_mem_lieInvariants {p : _root_.SymmetricAlgebra R (Dual R M)}
    (hp : p ∈ lieInvariants R L (Dual R M)) (hp₀ : algebraMapInv p = 0) {y : L} {x : M} {a : R}
    (hyx : ⁅y, x⁆ = a • x) (ha : a ≠ 0) :
    lift (Dual.eval R M x) p = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose (homogeneousSubmodule R (Dual R M)) p, map_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · -- the degree-zero component is the constant term
    have h₀ := congr($(projZeroRingHom_eq_algebraMap_comp_algebraMapInv R (Dual R M)) p)
    rw [GradedRing.projZeroRingHom_apply] at h₀
    rw [h₀, RingHom.comp_apply, RingHom.coe_coe, hp₀, map_zero, map_zero]
  · refine lift_eval_eq_zero_of_mem_homogeneousLieInvariant hn ?_ hyx ha
    exact mem_homogeneousLieInvariant.mpr ⟨decompose_mem_lieInvariants hp n, SetLike.coe_mem _⟩

end Eigenvector

end SymmetricAlgebra

open SymmetricAlgebra

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- **Vanishing invariants force nilpotence in every finite-dimensional module.** If every
invariant polynomial function on `L` with zero constant term vanishes at `x`, then `x` acts
nilpotently on every finite-dimensional Lie module: the invariants include the trace-power
polynomials `x ↦ tr (ρ_M(x) ^ m)`. -/
theorem isNilpotent_toEnd_of_forall_lift_eval_eq_zero (M : Type*) [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [LieRingModule L M] [LieModule K L M] {x : L}
    (h : ∀ p ∈ lieInvariants K L (Dual K L), algebraMapInv p = 0 → lift (Dual.eval K L x) p = 0) :
    IsNilpotent (toEnd K L M x) := by
  refine LinearMap.isNilpotent_iff_forall_trace_pow_eq_zero.mpr fun m hm ↦ ?_
  rw [← lift_eval_tracePowerPolynomial]
  refine h _ (tracePowerPolynomial_mem_lieInvariants (M := M) m) ?_
  -- a homogeneous element of positive degree lies in the irrelevant ideal
  have hirr := HomogeneousIdeal.mem_irrelevant_of_mem _ hm
    (tracePowerPolynomial_mem_homogeneousSubmodule (R := K) (L := L) (M := M) m)
  rwa [← HomogeneousIdeal.mem_iff, toIdeal_irrelevant_eq_ker_algebraMapInv, RingHom.mem_ker] at hirr

/-- **The ad-nilpotent elements are the common zeros of the invariants of positive degree.** In a
finite-dimensional Lie algebra with nondegenerate Killing form over a field of characteristic zero,
`ad x` is nilpotent exactly when every invariant polynomial function on `L` with zero constant term
vanishes at `x`. -/
theorem isNilpotent_ad_iff_forall_lift_eval_eq_zero [FiniteDimensional K L] [IsKilling K L]
    {x : L} :
    IsNilpotent (ad K L x) ↔
      ∀ p ∈ lieInvariants K L (Dual K L), algebraMapInv p = 0 → lift (Dual.eval K L x) p = 0 := by
  refine ⟨fun hx p hp hp₀ ↦ ?_, isNilpotent_toEnd_of_forall_lift_eval_eq_zero L⟩
  obtain ⟨t, ht⟩ := exists_lie_eq_self_of_isNilpotent_ad hx
  exact lift_eval_eq_zero_of_mem_lieInvariants hp hp₀ (y := t) (a := -1)
    (by rw [← lie_skew, ht, neg_one_smul]) (neg_ne_zero.mpr one_ne_zero)

end TauCeti
