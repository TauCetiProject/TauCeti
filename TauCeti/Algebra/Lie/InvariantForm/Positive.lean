/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.TraceForm
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.SkewAdjoint
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef
public import TauCeti.Algebra.Lie.InvariantForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Reductive.Basic
import TauCeti.Algebra.Lie.SkewAdjoint

/-!
# Invariant forms, centre/derived splitting and Killing-form signs

A reflexive invariant bilinear form with anisotropic diagonal on a finite-dimensional
Lie algebra makes its centre and derived ideal orthogonal complementary ideals. The derived
algebra is semisimple, hence centreless, and the radical of the ambient algebra is its centre.
For a positive-definite symmetric invariant form over an ordered field, the Killing form is
nonpositive, has diagonal zero exactly on the centre, and is negative definite on the derived
algebra.

## Main results

* `LinearMap.BilinForm.le_center_of_isLieAbelian_of_anisotropic`: every abelian ideal is central
  when an invariant form has anisotropic diagonal.
* `LinearMap.BilinForm.isCompl_center_derivedSeries_one_of_anisotropic`: the centre and derived
  ideal complement one another for a reflexive invariant form with anisotropic diagonal.
* `LinearMap.BilinForm.isSemisimple_derivedSeries_one_of_anisotropic`: the derived algebra is
  semisimple under the same hypotheses.
* `LinearMap.BilinForm.hasCentralRadical_of_anisotropic`: the radical equals the centre under the
  same hypotheses.
* `LinearMap.BilinForm.killingForm_self_nonpos_of_posDef`: the Killing form is nonpositive on the
  diagonal for a positive-definite invariant form.
* `LinearMap.BilinForm.killingForm_self_eq_zero_iff_of_posDef`: its diagonal vanishes exactly on the
  centre.
* `LinearMap.BilinForm.killingForm_self_neg_of_posDef_of_notMem_center`:
  it is strictly negative on noncentral vectors.
* `LinearMap.BilinForm.killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero`:
  the derived algebra has negative-definite Killing form.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Definition 12.1.1, Lemma 12.1.2, Proposition 12.1.4, and Remark 12.2.14.
-/

public section

namespace LinearMap.BilinForm

open LieAlgebra

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

/-- Every abelian ideal is central in a Lie algebra with an invariant form with anisotropic
diagonal. -/
theorem le_center_of_isLieAbelian_of_anisotropic (B : LinearMap.BilinForm K L)
    (hani : B.toQuadraticMap.Anisotropic)
    (hinv : B.lieInvariant L)
    (I : LieIdeal K L) [IsLieAbelian I] : I ≤ center K L := by
  intro x hx
  apply (LieModule.mem_maxTrivSubmodule K L L x).mpr
  intro y
  have hxyI : ⁅x, y⁆ ∈ I := lie_mem_left K L I x y hx
  have hxx : ⁅x, ⁅x, y⁆⁆ = 0 := LieIdeal.lie_eq_zero_of_mem hx hxyI
  have hdiag : B ⁅x, y⁆ ⁅x, y⁆ = 0 := by
    rw [hinv, hxx, map_zero, neg_zero]
  have hxy : ⁅x, y⁆ = 0 := (B.anisotropic_toQuadraticMap_iff.mp hani) _ hdiag
  rw [← lie_skew y x, hxy, neg_zero]

section Field
variable {F : Type*} [Field F]
  [LieAlgebra F L] [FiniteDimensional F L]

/-- The centre and derived ideal complement one another when a finite-dimensional Lie algebra
has a reflexive invariant form with anisotropic diagonal. -/
theorem isCompl_center_derivedSeries_one_of_anisotropic (B : LinearMap.BilinForm F L)
    (hrefl : B.IsRefl) (hani : B.toQuadraticMap.Anisotropic)
    (hinv : B.lieInvariant L) :
    IsCompl (center F L) (derivedSeries F L 1) := by
  have hnd := nondegenerate_of_anisotropic B hani
  have hrestrict : (B.restrict (derivedSeries F L 1).toSubmodule).Nondegenerate := by
    rw [restrict_eq_compl₁₂]
    exact nondegenerate_of_anisotropic _
      (B.anisotropic_toQuadraticMap_compl₁₂ hani
        (derivedSeries F L 1).toSubmodule.subtype
        (derivedSeries F L 1).toSubmodule.injective_subtype)
  have hcompl : IsCompl (derivedSeries F L 1)
      (LieAlgebra.InvariantForm.orthogonal B hinv (derivedSeries F L 1)) := by
    rw [← LieSubmodule.isCompl_toSubmodule, LieAlgebra.InvariantForm.orthogonal_toSubmodule]
    exact B.isCompl_orthogonal_of_restrict_nondegenerate hrefl hrestrict
  rw [orthogonal_derivedSeries_one_eq_center B hnd.2 hinv] at hcompl
  exact hcompl.symm

/-- The derived algebra of a finite-dimensional Lie algebra with a reflexive invariant form
with anisotropic diagonal is semisimple. -/
theorem isSemisimple_derivedSeries_one_of_anisotropic (B : LinearMap.BilinForm F L)
    (hrefl : B.IsRefl) (hani : B.toQuadraticMap.Anisotropic)
    (hinv : B.lieInvariant L) :
    LieAlgebra.IsSemisimple F (derivedSeries F L 1) := by
  let D := derivedSeries F L 1
  let BD : LinearMap.BilinForm F D := B.compl₁₂ D.incl.toLinearMap D.incl.toLinearMap
  have hreflD : BD.IsRefl := hrefl.compl₁₂ D.incl.toLinearMap
  have haniD : BD.toQuadraticMap.Anisotropic :=
    B.anisotropic_toQuadraticMap_compl₁₂ hani D.incl.toLinearMap D.incl_injective
  have hinvD := hinv.compl₁₂ D.incl
  apply LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate BD
    (nondegenerate_of_anisotropic BD haniD) hinvD hreflD
  intro I hI habel
  -- Install the abelian-ideal hypothesis for the centrality criterion.
  let _ := habel
  have hle := le_center_of_isLieAbelian_of_anisotropic BD haniD hinvD I
  rw [D.center_eq_bot_of_isCompl_center
    (B.isCompl_center_derivedSeries_one_of_anisotropic hrefl hani hinv)] at hle
  exact hI.1 (le_antisymm hle bot_le)

/-- A finite-dimensional Lie algebra with a reflexive invariant form with anisotropic diagonal has
radical equal to its centre. -/
theorem hasCentralRadical_of_anisotropic (B : LinearMap.BilinForm F L)
    (hrefl : B.IsRefl) (hani : B.toQuadraticMap.Anisotropic)
    (hinv : B.lieInvariant L) :
    LieAlgebra.HasCentralRadical F L := by
  let _ := isSemisimple_derivedSeries_one_of_anisotropic B hrefl hani hinv
  exact TauCeti.hasCentralRadical_of_hasTrivialRadical_derivedSeries F L

end Field

section KillingForm

variable {F L : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [LieRing L] [LieAlgebra F L] [FiniteDimensional F L]

/-- The Killing form of a Lie algebra with a symmetric positive-definite invariant form
is nonpositive on the diagonal. -/
theorem killingForm_self_nonpos_of_posDef (B : LinearMap.BilinForm F L)
    (hsymm : LinearMap.BilinForm.IsSymm B)
    (hpos : B.toQuadraticMap.PosDef)
    (hinv : B.lieInvariant L) (x : L) :
    killingForm F L x x ≤ 0 := by
  rw [killingForm_apply_apply, ← Module.End.mul_eq_comp]
  exact trace_mul_self_nonpos_of_posDef B hsymm hpos (ad F L x)
    (TauCeti.LieAlgebra.ad_mem_skewAdjointSubmodule hinv x)

/-- The diagonal of the Killing form of a Lie algebra with a symmetric positive-definite
invariant form vanishes exactly on the centre. -/
theorem killingForm_self_eq_zero_iff_of_posDef (B : LinearMap.BilinForm F L)
    (hsymm : LinearMap.BilinForm.IsSymm B)
    (hpos : B.toQuadraticMap.PosDef)
    (hinv : B.lieInvariant L) (x : L) :
    killingForm F L x x = 0 ↔ x ∈ center F L := by
  rw [killingForm_apply_apply, ← Module.End.mul_eq_comp,
    trace_mul_self_eq_zero_iff_of_posDef B hsymm hpos (ad F L x)
      (TauCeti.LieAlgebra.ad_mem_skewAdjointSubmodule hinv x),
    ← self_module_ker_eq_center, LieModule.mem_ker, LinearMap.ext_iff]
  simp only [ad_apply, LinearMap.zero_apply]

/-- The Killing form of a Lie algebra with a symmetric positive-definite invariant form
is strictly negative on noncentral vectors. -/
theorem killingForm_self_neg_of_posDef_of_notMem_center (B : LinearMap.BilinForm F L)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    (hinv : B.lieInvariant L)
    (x : L) (hx : x ∉ center F L) : killingForm F L x x < 0 := by
  have hle := killingForm_self_nonpos_of_posDef B hsymm hpos hinv x
  have hne : killingForm F L x x ≠ 0 := fun h ↦
    hx ((killingForm_self_eq_zero_iff_of_posDef B hsymm hpos hinv x).mp h)
  exact lt_of_le_of_ne hle hne

/-- The Killing form of the derived algebra is strictly negative on nonzero vectors when
the ambient algebra has a symmetric positive-definite invariant form. -/
theorem killingForm_derivedSeries_one_self_neg_of_posDef_of_ne_zero (B : LinearMap.BilinForm F L)
    (hsymm : LinearMap.BilinForm.IsSymm B) (hpos : B.toQuadraticMap.PosDef)
    (hinv : B.lieInvariant L)
    (x : derivedSeries F L 1) (hx : x ≠ 0) :
    killingForm F (derivedSeries F L 1) x x < 0 := by
  let D := derivedSeries F L 1
  let BD : LinearMap.BilinForm F D := B.compl₁₂ D.incl.toLinearMap D.incl.toLinearMap
  have hsymmD := hsymm.compl₁₂ D.incl.toLinearMap
  have hposD : BD.toQuadraticMap.PosDef :=
    B.posDef_toQuadraticMap_compl₁₂ hpos D.incl.toLinearMap D.incl_injective
  have hinvD := hinv.compl₁₂ D.incl
  apply killingForm_self_neg_of_posDef_of_notMem_center BD hsymmD hposD hinvD x
  intro hcenter
  let _ := isSemisimple_derivedSeries_one_of_anisotropic B hsymm.isRefl hpos.anisotropic hinv
  rw [LieAlgebra.center_eq_bot] at hcenter
  exact hx ((LieSubmodule.mem_bot _).mp hcenter)

end KillingForm

end LinearMap.BilinForm
