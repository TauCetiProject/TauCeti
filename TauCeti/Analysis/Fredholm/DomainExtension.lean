/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.Analysis.Fredholm.Stabilization

/-!
# Kernel and cokernel of a finite domain extension

For an operator `T : E →L[𝕜] F` and extra directions `B : S →L[𝕜] F`, the
extended operator is `T.coprod B`, sending `(x, s)` to `T x + B s`.
The kernel and cokernel fit into the exact sequence

`0 → ker T → ker (T.coprod B) → S → coker T → coker (T.coprod B) → 0`.

The first three maps and their exactness are supplied by
`ContinuousLinearMap.kerCoprodHom`, `ContinuousLinearMap.parameterProj` and
`ContinuousLinearMap.parameterToCoker`. Here `cokerCoprodHom` completes the
sequence, without requiring the extended operator to be onto. Rank-nullity
then computes both the kernel growth and the loss of obstructions. For a
Fredholm `T` and finite-dimensional `S`, the index increases by `dim S`,
regardless of how many of the extra directions hit the old range.

In a weighted end problem, `S` is the space of free asymptotic variables and
`B` sends a variable to the operator applied to its cutoff extension. The
analytic prerequisite is that this is a bounded map into the unchanged
weighted target. The results here do not assert that prerequisite.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*,
  second edition, Appendix A.2 (Fredholm operators and stabilization).
-/

public section

open Module

namespace ContinuousLinearMap

section Algebra

variable {𝕜 E F S : Type*} [Ring 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  [AddCommGroup S] [Module 𝕜 S] [TopologicalSpace S]
  (T : E →L[𝕜] F) (B : S →L[𝕜] F)

/-- The canonical map from the cokernel of `T` onto the cokernel after
adjoining the domain directions `B`. -/
noncomputable def cokerCoprodHom : (F ⧸ T.range) →ₗ[𝕜] F ⧸ (T.coprod B).range :=
  Submodule.factor (by rw [range_coprod]; exact le_sup_left)

/-- The cokernel map preserves the representative in the common target. -/
@[simp]
theorem cokerCoprodHom_mk (y : F) :
    cokerCoprodHom T B (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  (rfl)

/-- Every obstruction class for the extended operator comes from an
obstruction class for the original operator. -/
theorem cokerCoprodHom_surjective : Function.Surjective (cokerCoprodHom T B) :=
  Submodule.factor_surjective (by rw [range_coprod]; exact le_sup_left)

/-- The obstructions removed by the extra directions are precisely the
image of those directions in the original cokernel. -/
@[simp]
theorem ker_cokerCoprodHom :
    LinearMap.ker (cokerCoprodHom T B) = LinearMap.range (parameterToCoker T B) := by
  simp only [cokerCoprodHom, Submodule.factor, Submodule.ker_mapQ,
    Submodule.comap_id, range_coprod, Submodule.map_sup, Submodule.mkQ_map_self,
    bot_sup_eq, range_parameterToCoker]

/-- Exactness at the original cokernel in the domain-extension sequence.
Together with `exact_kerCoprodHom_parameterProj`,
`exact_parameterProj_parameterToCoker`, and the injectivity and surjectivity
of the end maps, this gives the full six-term sequence. -/
theorem exact_parameterToCoker_cokerCoprodHom :
    Function.Exact (parameterToCoker T B) (cokerCoprodHom T B) :=
  LinearMap.exact_iff.mpr (ker_cokerCoprodHom T B)

end Algebra

section Dimension

variable {𝕜 E F S : Type*} [DivisionRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  [AddCommGroup S] [Module 𝕜 S] [TopologicalSpace S]
  (T : E →L[𝕜] F) (B : S →L[𝕜] F)

/-- Kernel growth is the dimension of the extra variables minus the
number of independent old obstructions they remove. -/
theorem finrank_ker_coprod_add_finrank_range_parameterToCoker
    [FiniteDimensional 𝕜 (T.coprod B).ker] [FiniteDimensional 𝕜 S] :
    finrank 𝕜 (T.coprod B).ker + finrank 𝕜 (LinearMap.range (parameterToCoker T B)) =
      finrank 𝕜 T.ker + finrank 𝕜 S := by
  have hproj := (parameterProj T B).toLinearMap.finrank_range_add_finrank_ker
  have hparam := (parameterToCoker T B).finrank_range_add_finrank_ker
  rw [finrank_ker_parameterProj] at hproj
  rw [ker_parameterToCoker] at hparam
  omega

/-- The extended cokernel is smaller by the rank of the parameter map
into the old cokernel. No finiteness of the extra-variable space is needed. -/
theorem finrank_coker_coprod_add_finrank_range_parameterToCoker
    [FiniteDimensional 𝕜 (F ⧸ T.range)] :
    finrank 𝕜 (F ⧸ (T.coprod B).range) +
      finrank 𝕜 (LinearMap.range (parameterToCoker T B)) = finrank 𝕜 (F ⧸ T.range) := by
  have h := (cokerCoprodHom T B).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (cokerCoprodHom_surjective T B),
    finrank_top, ker_cokerCoprodHom] at h
  exact h

end Dimension

section Fredholm

variable {𝕜 E F S : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup S] [NormedSpace 𝕜 S] [FiniteDimensional 𝕜 S]
  {T : E →L[𝕜] F}

/-- Adjoining finitely many domain variables increases the Fredholm index
by their dimension, whether or not the extension is surjective. -/
theorem IsFredholm.index_coprod (hT : IsFredholm T) (B : S →L[𝕜] F) :
    (T.coprod B).index = T.index + finrank 𝕜 S := by
  have := hT.finite_coker
  have := (hT.coprod_of_finiteDimensional B).finite_ker
  have hker := finrank_ker_coprod_add_finrank_range_parameterToCoker T B
  have hcoker := finrank_coker_coprod_add_finrank_range_parameterToCoker T B
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  omega

end Fredholm

end ContinuousLinearMap
