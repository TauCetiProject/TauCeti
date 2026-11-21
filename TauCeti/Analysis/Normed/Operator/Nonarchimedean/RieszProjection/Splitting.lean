/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Basic
public import TauCeti.Analysis.Normed.Operator.RowCompact.Idempotent
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# The closed splitting associated to a Riesz projection

For a Riesz projection `E` of `u` at `a` with nilpotence bound `h`, put `C = 1 - a • u`.
For every `n ≥ h`, the kernel of `C ^ n` is `range E` and its range is `ker E`.
These are topological complements, so the decomposition into the nilpotent and invertible
parts is a decomposition by closed submodules. In particular both kernels and ranges stabilise
For any Riesz projection of a row-compact operator, with no good-zero hypothesis, the stabilised
kernel is finitely generated and projective. This applies over coefficient rings with nilpotents
and includes order zero, when the kernel is zero and the complementary range is the whole module.
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
      C₀(I, R) →ₗ[R] C₀(I, R)) :=
  (isRieszProjection_def.mp hE).ker_pow_eq hn

/-- The range of every sufficiently large power of `1 - a • u` is the kernel of its
Riesz projection, hence the complementary spectral summand. -/
theorem range_pow_eq_ker (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) = LinearMap.ker (E : C₀(I, R) →ₗ[R] C₀(I, R)) :=
  (isRieszProjection_def.mp hE).range_pow_eq_ker hn

/-- The ranges of the powers of `1 - a • u` stabilise at the nilpotence bound of a
Riesz projection. -/
theorem range_pow_eq (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) =
    LinearMap.range (((1 - a • u) ^ h : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) :=
  (isRieszProjection_def.mp hE).range_pow_eq hn

/-- The generalised eigenspace and the stabilised range of `1 - a • u` are topological
complements. -/
theorem isTopCompl_ker_range_pow (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    (LinearMap.ker (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))).IsTopCompl
    (LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) :=
  (isRieszProjection_def.mp hE).isTopCompl_ker_range_pow hn

/-- Every stabilised range of `1 - a • u` is closed, even when the ambient module is
infinite-dimensional. -/
theorem isClosed_range_pow (hE : IsRieszProjection u a h E) (hn : h ≤ n) :
    IsClosed (LinearMap.range (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R)) : Set C₀(I, R)) :=
  (isRieszProjection_def.mp hE).isClosed_range_pow hn

variable [DiscreteTopology I] [DecidableEq I] [IsUltrametricDist R]

variable [CompleteSpace R]

/-- The stabilised generalised eigenspace of a row-compact operator is finitely generated. -/
theorem finite_ker_pow (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) (hn : h ≤ n) :
    Module.Finite R (LinearMap.ker (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isRowCompact hu).finite_range_of_isIdempotentElem
    (isRieszProjection_def.mp hE).isIdempotentElem

/-- The stabilised generalised eigenspace of a row-compact operator is projective over the
coefficient ring. No Noetherian hypothesis is needed. -/
theorem projective_ker_pow (hE : IsRieszProjection u a h E) (hu : u.IsRowCompact) (hn : h ≤ n) :
    Module.Projective R (LinearMap.ker (((1 - a • u) ^ n : C₀(I, R) →L[R] C₀(I, R)) :
      C₀(I, R) →ₗ[R] C₀(I, R))) := by
  rw [← (hE.of_le hn).range_eq_ker]
  exact (hE.isRowCompact hu).projective_range_of_isIdempotentElem
    (isRieszProjection_def.mp hE).isIdempotentElem

end IsRieszProjection

end ContinuousLinearMap
