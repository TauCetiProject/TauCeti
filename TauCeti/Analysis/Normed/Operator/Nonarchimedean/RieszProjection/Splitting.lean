/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent
public import Mathlib.Topology.Algebra.Module.Complement
import TauCeti.Algebra.Ring.SpectralIdempotent

/-!
# The closed splitting associated to a Riesz projection

For a Riesz projection `E` of `u` at `a` with nilpotence bound `h`, put `C = 1 - a • u`.
For every `n ≥ h`, the kernel of `C ^ n` is `range E` and its range is `ker E`.
These are topological complements, so the decomposition into the nilpotent and invertible
parts is a decomposition by closed submodules. In particular both kernels and ranges stabilise
at `h`, without any finite-dimensional or Noetherian assumption.

At a good zero of the Fredholm series of a row-compact operator, the stabilised kernel is
finitely generated and projective. This applies over coefficient rings with nilpotents and
includes order zero, when the kernel is zero and the complementary range is the whole module.
The topological complement can be used with `Submodule.prodEquivOfIsTopCompl` to obtain the
continuous linear equivalence from the product of the two summands to the original space.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A4.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap

variable {I R : Type*} [TopologicalSpace I] [NormedCommRing R]
  [TauCeti.NormedRing.IsTate R]

namespace IsRieszProjection

variable {u E : C₀(I, R) →L[R] C₀(I, R)} {a : R} {h n : ℕ}

/-- A Riesz projection remains one when its nilpotence bound is increased. -/
theorem of_le (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    IsRieszProjection u a n E := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine { hE with pow_mul_eq_zero := ?_ }
  rw [add_comm h k, pow_add, mul_assoc, hE.pow_mul_eq_zero, mul_zero]

/-- The kernels of the powers of `1 - a • u` stabilise at the nilpotence bound of a
Riesz projection. -/
theorem ker_pow_eq (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    LinearMap.ker (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) =
    LinearMap.ker (((1 - a • u) ^ h : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) := by
  rw [← (hE.of_le hn).range_eq_ker, hE.range_eq_ker]

/-- The range of every sufficiently large power of `1 - a • u` is the kernel of its
Riesz projection, hence the complementary spectral summand. -/
theorem range_pow_eq_ker (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) = LinearMap.ker (E : C₀(I, R) →ₗ[R] C₀(I, R)) := by
  have hEn := hE.of_le hn
  obtain ⟨w, hw, hw', -⟩ := hE.exists_inverse
  have h1 := _root_.IsIdempotentElem.one_sub_eq_pow_mul_pow hE.isIdempotentElem
    (A := C₀(I, R) →L[R] C₀(I, R)) hEn.pow_mul_eq_zero hw hw'
  have hzero : E * (1 - a • u) ^ n = 0 :=
    ((hE.commute_one_sub_smul.pow_left n).eq).symm.trans hEn.pow_mul_eq_zero
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, coe_coe]
  constructor
  · rintro ⟨y, rfl⟩
    simpa using congr($hzero y)
  · intro hx
    refine ⟨(w ^ n) x, ?_⟩
    have := congr($h1 x)
    simpa [hx] using this.symm

/-- The ranges of the powers of `1 - a • u` stabilise at the nilpotence bound of a
Riesz projection. -/
theorem range_pow_eq (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) =
    LinearMap.range (((1 - a • u) ^ h : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) := by
  rw [hE.range_pow_eq_ker hn, hE.range_pow_eq_ker le_rfl]

/-- The generalised eigenspace and the stabilised range of `1 - a • u` are topological
complements. -/
theorem isTopCompl_ker_range_pow (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    (LinearMap.ker (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))).IsTopCompl
    (LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← (hE.of_le hn).range_eq_ker, hE.range_pow_eq_ker hn]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl hE.isIdempotentElem

/-- Every stabilised range of `1 - a • u` is closed, even when the ambient module is
infinite-dimensional. -/
theorem isClosed_range_pow (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    IsClosed (LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) : Set C₀(I, R)) := by
  rw [hE.range_pow_eq_ker hn]
  exact E.isClosed_ker

/-- On the stabilised range, `1 - a • u` is a continuous linear automorphism. -/
theorem exists_equiv_range_pow (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    ∃ e : LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R)) ≃L[R]
      LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
        C₀(I, R) →ₗ[R] C₀(I, R)),
      ∀ x, (e x : C₀(I, R)) = (1 - a • u) x := by
  rw [hE.range_pow_eq_ker hn]
  obtain ⟨w, hw, hw', hEw, -⟩ := hE.exists_inverse
  have hC : ∀ x ∈ E.ker, (1 - a • u) x ∈ E.ker := by
    intro x hx
    have hx' : E x = 0 := hx
    have hc := congr($(hE.commute_one_sub_smul.eq) x)
    exact LinearMap.mem_ker.mpr (by
      simpa only [coe_coe, mul_apply_eq_comp, hx', map_zero] using hc.symm)
  have hwker : ∀ x ∈ E.ker, w x ∈ E.ker := by
    intro x _
    simpa using congr($hEw x)
  let f := (1 - a • u).restrict hC
  let g := w.restrict hwker
  refine ⟨ContinuousLinearEquiv.equivOfInverse f g ?_ ?_, ?_⟩
  · intro x
    apply Subtype.ext
    simpa [f, g, x.property] using congr($hw' (x : C₀(I, R)))
  · intro x
    apply Subtype.ext
    simpa [f, g, x.property] using congr($hw (x : C₀(I, R)))
  · intro x
    simp [f, ContinuousLinearEquiv.equivOfInverse_apply]

variable [DiscreteTopology I] [DecidableEq I] [IsUltrametricDist R]

/-- A Riesz projection of a row-compact operator is row compact, including when its
nilpotence bound is zero. -/
theorem isRowCompact (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) :
    E.IsRowCompact := by
  have hEq : E = (1 - (1 - a • u) ^ h) * E := by
    rw [sub_mul (α := C₀(I, R) →L[R] C₀(I, R)), one_mul, hE.pow_mul_eq_zero,
      sub_zero (G := C₀(I, R) →L[R] C₀(I, R))]
  rw [hEq, ← mul_neg_geom_sum (R := C₀(I, R) →L[R] C₀(I, R))]
  have hc : (1 - (1 - a • u)).IsRowCompact := by
    rw [sub_sub_cancel (G := C₀(I, R) →L[R] C₀(I, R))]
    exact hu.smul a
  exact (hc.comp_clm _).comp_clm E

variable [CompleteSpace R]

/-- The stabilised generalised eigenspace of a row-compact operator is finitely generated. -/
theorem finite_ker_pow (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) (hn : h ≤ n) :
    Module.Finite R (LinearMap.ker (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isRowCompact hu).finite_range_of_isIdempotentElem hE.isIdempotentElem

/-- The stabilised generalised eigenspace of a row-compact operator is projective over the
coefficient ring. No Noetherian hypothesis is needed. -/
theorem projective_ker_pow (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) (hn : h ≤ n) :
    Module.Projective R (LinearMap.ker (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isRowCompact hu).projective_range_of_isIdempotentElem hE.isIdempotentElem

end IsRieszProjection

end ContinuousLinearMap
