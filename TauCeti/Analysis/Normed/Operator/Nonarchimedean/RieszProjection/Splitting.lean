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
at `h`, without any finite-dimensional or Noetherian assumption. The named automorphism
`ContinuousLinearMap.IsRieszProjection.equivKer` restricts `C` to the complementary summand
`ker E`; its forward and inverse application lemmas identify both maps.

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

/-- The spectral operator `1 - a • u` as a continuous linear automorphism of the
complementary summand `ker E`, identified with every stabilised range by `range_pow_eq_ker`.
Its inverse is the restriction of the witness supplied by `IsRieszProjection.exists_inverse`. -/
noncomputable def equivKer (hE : IsRieszProjection u a h E) : E.ker ≃L[R] E.ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((1 - a • u).restrict (fun _ hx ↦ hE.mapsTo_ker_one_sub_smul hx))
    (hE.exists_inverse.choose.restrict (fun _ hx ↦ hE.mapsTo_ker_inverse hx))
    (fun x ↦ Subtype.ext (hE.inverse_one_sub_smul_apply x.property))
    (fun x ↦ Subtype.ext (hE.one_sub_smul_apply_inverse x.property))

/-- The complementary automorphism acts by the spectral operator. -/
@[simp]
theorem coe_equivKer_apply (hE : IsRieszProjection u a h E) (x : E.ker) :
    (hE.equivKer x : C₀(I, R)) = (1 - a • u) x :=
  (rfl)

/-- The inverse complementary automorphism acts by the chosen complementary inverse. -/
theorem coe_equivKer_symm_apply (hE : IsRieszProjection u a h E) (x : E.ker) :
    (hE.equivKer.symm x : C₀(I, R)) = hE.exists_inverse.choose x :=
  (rfl)

variable [DiscreteTopology I] [DecidableEq I] [IsUltrametricDist R]

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
