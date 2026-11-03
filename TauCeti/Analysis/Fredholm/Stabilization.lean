/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Analysis.Normed.Operator.Splitting.Family
import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem

/-!
# Finite stabilization of Fredholm families

A Fredholm operator becomes surjective after adjoining a finite-dimensional subspace
of its target to its domain. For a continuous operator family one subspace works
throughout a neighbourhood. A fixed projection onto the stabilized kernel at the base
point gives invertible paired coordinates throughout a smaller neighbourhood.

`ContinuousLinearMap.kernelHomeomorph` then gives product charts on the stabilized
kernel locus with its subspace topology. Their fibre maps are linear, and
`ContinuousLinearMap.contDiffAt_kerSection` gives their inverse parametrizations the
regularity of a smooth operator family. In particular the stabilized kernel dimension
is locally constant, even when the original kernel dimension jumps. These are the
local finite-dimensional kernel models used in determinant line bundles.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix A.2 (Fredholm operators and determinant lines).
-/

public section

open Function Set Topology

namespace ContinuousLinearMap

variable {𝕜 E F S : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup S] [NormedSpace 𝕜 S] [FiniteDimensional 𝕜 S]

/-- Adjoining finitely many domain directions preserves Fredholmness. No surjectivity
of the enlarged operator is required. -/
theorem IsFredholm.coprod_of_finiteDimensional {T : E →L[𝕜] F} (hT : IsFredholm T)
    (B : S →L[𝕜] F) : IsFredholm (T.coprod B) := by
  have hker : (fst 𝕜 E S).ker = (⊥ : Submodule 𝕜 E).prod ⊤ := by
    ext p
    simp
  have : FiniteDimensional 𝕜 (fst 𝕜 E S).ker := by
    rw [hker]
    exact (Submodule.prodEquiv (⊥ : Submodule 𝕜 E) (⊤ : Submodule 𝕜 S)).symm.finiteDimensional
  have hf : IsFredholm (fst 𝕜 E S) :=
    isQuotientMap_fst.isFredholm
      (closedComplemented_ker_of_rightInverse (fst 𝕜 E S) (inl 𝕜 E S) (fun _ ↦ rfl))
      inferInstance
  have hB : (B ∘L snd 𝕜 E S).toLinearMap.HasFiniteRange :=
    LinearMap.HasFiniteRange.of_finite_dom.comp_right _
  simpa only [comp_fst_add_comp_snd] using (hT.comp hf).add_hasFiniteRange hB

variable [CompleteSpace E] [CompleteSpace F]
  {X : Type*} [TopologicalSpace X] {T : X → E →L[𝕜] F} {x₀ : X}

/-- A family continuous and Fredholm at one point admits a fixed finite-dimensional target
stabilizer and fixed kernel coordinate on a neighbourhood. Pairing the stabilized operator
with this coordinate is invertible there. For continuous families, `kernelHomeomorph`
supplies actual local product charts, with model the finite-dimensional stabilized kernel
at the base point.
No Fredholm hypothesis is imposed away from the base point. -/
theorem IsFredholm.exists_stabilization_kernel_coordinates (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) :
    ∃ S : Submodule 𝕜 F, FiniteDimensional 𝕜 S ∧
      ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
          ∀ x ∈ U, (((T x).coprod S.subtypeL).prod q).IsInvertible := by
  obtain ⟨pkg⟩ := hT₀.nonempty_fredholmPackage
  let S := pkg.decCodom.X₀
  let : FiniteDimensional 𝕜 S := pkg.decCodom.finite_X₀
  let : IsClosed (S : Set F) := pkg.decCodom.isTopCompl.isClosed'
  let A : X → (E × S) →L[𝕜] F := fun x ↦ (T x).coprod S.subtypeL
  have hsurj : Surjective (A x₀) := by
    apply LinearMap.range_eq_top.mp
    rw [range_coprod, Submodule.toLinearMap_subtypeL, Submodule.range_subtype, pkg.range_eq]
    exact pkg.decCodom.isTopCompl.isCompl.sup_eq_top
  have hfred : IsFredholm (A x₀) := hT₀.coprod_of_finiteDimensional S.subtypeL
  let q := Classical.choose hfred.closedComplemented_ker
  have hinv : ((A x₀).prod q).IsInvertible := by
    refine ⟨(A x₀).implicitCoordEquiv (LinearMap.range_eq_top.mpr hsurj)
      hfred.closedComplemented_ker, ?_⟩
    exact coe_implicitCoordEquiv _ _ _
  have hA : ContinuousAt A x₀ := hT.continuousLinearMapCoprod continuousAt_const
  obtain ⟨U, hU, hx₀, hUinv⟩ := exists_isOpen_isInvertible_prod hA hinv
  exact ⟨S, inferInstance, q, U, hU, hx₀, hUinv⟩

end ContinuousLinearMap
