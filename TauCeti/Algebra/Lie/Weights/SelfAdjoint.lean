/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Lie.Weights.Diagonalizable
import TauCeti.Algebra.Lie.Weights.Semisimple
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair

/-!
# Weight spaces of Lie modules acting by self-adjoint operators

Let a Lie algebra `L` act on a module `M` carrying a bilinear form `g` for which every operator
`⁅x, ·⁆` is self-adjoint, `g ⁅x, m⁆ n = g m ⁅x, n⁆`. This is the situation of an abelian
subspace `𝔞` of the `-1`-eigenspace `𝔭` of a Cartan involution `θ` of a real semisimple Lie
algebra `𝔤₀`, acting on `𝔤₀` by `ad` and self-adjoint for the inner product
`B_θ (X, Y) = -B (X, θ Y)`; the weight spaces are then the restricted root spaces.

Over a commutative ring without zero divisors, weight spaces for distinct weights are
`g`-orthogonal, and when `g` is left-separating and `2 ≠ 0` the operators commute: the action of a
bracket is both self-adjoint and skew-adjoint. When `g` is anisotropic and `L` is nilpotent,
Mathlib's generalized weight spaces `LieModule.genWeightSpace M χ` are the honest weight spaces
`LieModule.weightSpace M χ`. Over `ℝ`, with `M` finite-dimensional and `g` positive definite, each
operator is moreover diagonalizable (`LinearMap.IsSelfAdjoint.iSup_eigenspace_eq_top`), so the
weight spaces span `M`, the module is triangularizable, and for nilpotent `L` it is the internal
direct sum of its weight spaces.

## Main results

* `TauCeti.apply_eq_zero_of_mem_weightSpace`: weight spaces for distinct weights are orthogonal.
* `TauCeti.commute_toEnd_of_isSelfAdjoint`: the operators of the action commute.
* `TauCeti.genWeightSpace_eq_weightSpace_of_isSelfAdjoint`: for an anisotropic form and nilpotent
  `L`, the generalized weight spaces are the honest weight spaces.
* `TauCeti.iSup_weightSpace_eq_top_of_isSelfAdjoint`: over `ℝ`, the weight spaces span.
* `TauCeti.isTriangularizable_of_isSelfAdjoint`: over `ℝ`, the module is triangularizable.
* `TauCeti.isInternal_weightSpace_of_isSelfAdjoint`: over `ℝ`, for nilpotent `L`, `M` is the
  internal direct sum of its weight spaces.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Birkhäuser (2002), Ch. VI §4
  (the restricted root space decomposition).
-/

public section

namespace TauCeti

open LieModule Module

section CommRing

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] {g : LinearMap.BilinForm R M}

/-- **Weight spaces are orthogonal.** If every operator of a Lie module is self-adjoint for a
bilinear form `g`, then `g` vanishes between the weight spaces of distinct weights. -/
theorem apply_eq_zero_of_mem_weightSpace [NoZeroDivisors R]
    (hT : ∀ x : L, g.IsSelfAdjoint (toEnd R L M x)) {χ ψ : L → R} (hχψ : χ ≠ ψ) {m n : M}
    (hm : m ∈ weightSpace M χ) (hn : n ∈ weightSpace M ψ) : g m n = 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hχψ
  have h := hT x m n
  simp only [toEnd_apply_apply, (mem_weightSpace χ m).mp hm x, (mem_weightSpace ψ n).mp hn x,
    map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp (by linear_combination h : (χ x - ψ x) * g m n = 0)).resolve_left
    (sub_ne_zero.mpr hx)

/-- **Self-adjoint actions commute.** If every operator of a Lie module is self-adjoint for a
left-separating bilinear form, over a ring without zero divisors in which `2 ≠ 0`, then these
operators commute, so the action of every bracket `⁅x, y⁆` is zero. -/
theorem commute_toEnd_of_isSelfAdjoint [NoZeroDivisors R] [NeZero (2 : R)]
    (hg : g.SeparatingLeft) (hT : ∀ x : L, g.IsSelfAdjoint (toEnd R L M x)) (x y : L) :
    Commute (toEnd R L M x) (toEnd R L M y) := by
  have h (z : L) (m n : M) : g ⁅z, m⁆ n = g m ⁅z, n⁆ := hT z m n
  refine LinearMap.ext fun m ↦ sub_eq_zero.mp (hg _ fun n ↦ ?_)
  have h2 : (2 : R) * g ⁅⁅x, y⁆, m⁆ n = 0 := by
    have hxy := h ⁅x, y⁆ m n
    simp only [lie_lie, map_sub, LinearMap.sub_apply] at hxy ⊢
    linear_combination hxy + h x ⁅y, m⁆ n + h y m ⁅x, n⁆ - h y ⁅x, m⁆ n - h x m ⁅y, n⁆
  simpa [lie_lie] using (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **Generalized weight spaces are honest.** If every operator of a module over a nilpotent Lie
algebra is self-adjoint for an anisotropic bilinear form, then its generalized weight spaces are
its weight spaces. -/
theorem genWeightSpace_eq_weightSpace_of_isSelfAdjoint [LieRing.IsNilpotent L]
    (hg : ∀ m, g m m = 0 → m = 0) (hT : ∀ x : L, g.IsSelfAdjoint (toEnd R L M x)) (χ : L → R) :
    genWeightSpace M χ = weightSpace M χ :=
  genWeightSpace_eq_weightSpace_of_maxGenEigenspace_eq_eigenspace
    (fun x ↦ (hT x).maxGenEigenspace_eq_eigenspace hg) χ

end CommRing

section Real

variable {L M : Type*} [LieRing L] [LieAlgebra ℝ L] [AddCommGroup M] [Module ℝ M]
  [LieRingModule L M] [LieModule ℝ L M] [FiniteDimensional ℝ M] {g : LinearMap.BilinForm ℝ M}

/-- **Self-adjoint actions are diagonalizable.** If every operator of a finite-dimensional real
Lie module is self-adjoint for a positive definite bilinear form, then the module is spanned by
its weight spaces. -/
theorem iSup_weightSpace_eq_top_of_isSelfAdjoint (hpos : ∀ m, m ≠ 0 → 0 < g m m)
    (hT : ∀ x : L, g.IsSelfAdjoint (toEnd ℝ L M x)) : ⨆ χ : L → ℝ, weightSpace M χ = ⊤ := by
  have hsep : g.SeparatingLeft := fun m hm ↦ by_contra fun h ↦ (hpos m h).ne' (hm m)
  have h := iSup_iInf_eigenspace_eq_top_of_iSup_eigenspace_eq_top (toEnd ℝ L M)
    (fun x y _ ↦ commute_toEnd_of_isSelfAdjoint hsep hT x y)
    fun x ↦ (hT x).iSup_eigenspace_eq_top hpos
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule, ← h]
  refine iSup_congr fun χ ↦ SetLike.ext fun m ↦ ?_
  simp [mem_weightSpace]

/-- If every operator of a finite-dimensional real Lie module is self-adjoint for a positive
definite bilinear form, then the module is triangularizable. -/
theorem isTriangularizable_of_isSelfAdjoint (hpos : ∀ m, m ≠ 0 → 0 < g m m)
    (hT : ∀ x : L, g.IsSelfAdjoint (toEnd ℝ L M x)) : IsTriangularizable ℝ L M where
  maxGenEigenspace_eq_top x := by
    have hg (m : M) (hm : g m m = 0) : m = 0 := by_contra fun h ↦ (hpos m h).ne' hm
    simpa only [(hT x).maxGenEigenspace_eq_eigenspace hg] using
      (hT x).iSup_eigenspace_eq_top hpos

open scoped Classical in
/-- **The weight-space decomposition.** If every operator of a finite-dimensional real module over
a nilpotent Lie algebra is self-adjoint for a positive definite bilinear form, then the module is
the internal direct sum of its weight spaces. -/
theorem isInternal_weightSpace_of_isSelfAdjoint [LieRing.IsNilpotent L]
    (hpos : ∀ m, m ≠ 0 → 0 < g m m) (hT : ∀ x : L, g.IsSelfAdjoint (toEnd ℝ L M x)) :
    DirectSum.IsInternal fun χ : Weight ℝ L M ↦ (weightSpace M (χ : L → ℝ)).toSubmodule := by
  have := isTriangularizable_of_isSelfAdjoint hpos hT
  have hg (m : M) (hm : g m m = 0) : m = 0 := by_contra fun h ↦ (hpos m h).ne' hm
  simpa only [genWeightSpace_eq_weightSpace_of_isSelfAdjoint hg hT] using
    isInternal_genWeightSpace ℝ L M

end Real

end TauCeti
