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
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Finite stabilization of Fredholm families

A Fredholm operator becomes surjective after adjoining a finite-dimensional subspace
of its target to its domain. The subspace can be taken inside any dense subspace of the
target, so in Cauchy–Riemann gluing it can be spanned by smooth compactly supported
sections. For a continuous operator family one subspace works throughout a neighbourhood.
A fixed projection onto the stabilized kernel at the base point gives invertible paired
coordinates throughout a smaller neighbourhood.

`ContinuousLinearMap.kernelHomeomorph` then gives product charts on the stabilized
kernel locus with its subspace topology. Their fibre maps are linear, and
`ContinuousLinearMap.contDiffAt_kerSection` gives their inverse parametrizations the
regularity of a smooth operator family. In particular the stabilized kernel dimension
is locally constant, even when the original kernel dimension jumps. These are the
local finite-dimensional kernel models used in determinant line bundles.

The stabilized operator `T + inclusion_V`, paired with an invertible coordinate `q`, has a
right inverse `q.kerSection (T.coprod V.subtypeL)` normalized by `q = 0`. Wherever the cokernel
of `T` keeps the dimension of `V`, the stabilizer `V` is an exact topological complement of the
range of `T`, and the projection onto `V` along the range is the `V`-component of that right
inverse. In a family, these cokernel projections are therefore continuous, or `C^n`, with the
family on the parameters of constant cokernel rank. Where the rank jumps, `V` still makes the
stabilized operators surjective, but it is no longer complementary to the range.

## Main results

* `ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates`: a stabilizer inside a
  prescribed dense subspace, with invertible kernel coordinates on a neighbourhood.
* `ContinuousLinearMap.isTopCompl_of_isInvertible_prod_coprod`: a stabilizer whose dimension is
  at most the codimension of the range is a topological complement of the range.
* `ContinuousLinearMap.projectionOntoL_eq_snd_comp_kerSection_coprod`: the projection onto such a
  stabilizer along the range, as a component of the normalized right inverse.
* `ContinuousLinearMap.continuousAt_snd_comp_kerSection_coprod`,
  `ContinuousLinearMap.contDiffAt_snd_comp_kerSection_coprod`: that component varies continuously,
  or with the regularity of the family.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix A.2 (Fredholm operators and determinant lines).
-/

public section

open Function Set Topology
open Submodule (IsTopCompl)
open scoped ContDiff

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section FiniteDimensional

variable [CompleteSpace 𝕜] {S : Type*} [NormedAddCommGroup S] [NormedSpace 𝕜 S]
  [FiniteDimensional 𝕜 S]

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

end FiniteDimensional

section CokernelProjection

/-! ### The cokernel projection of a stabilized operator

Let `V` be a subspace of the target with `T.coprod V.subtypeL` surjective, and let `q` be a
coordinate on `E × V` whose pairing with that operator is invertible. Then
`q.kerSection (T.coprod V.subtypeL)` is the right inverse of the stabilized operator normalized by
`q = 0`. Its `V`-component projects onto `V` along the range of `T` as soon as the two subspaces
are complementary, which a dimension count detects. -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {T : E →L[𝕜] F} {V : Submodule 𝕜 F} {q : (E × V) →L[𝕜] G}

/-- The right inverse of a stabilized operator, normalized by `q`, splits each target vector into
a value of `T` and a vector of the stabilizer. -/
theorem apply_fst_kerSection_coprod_add_snd (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible)
    (y : F) :
    T (q.kerSection (T.coprod V.subtypeL) y).1 + (q.kerSection (T.coprod V.subtypeL) y).2 = y := by
  simpa using apply_kerSection_right (isInvertible_prod_comm.mp hinv) y

/-- When the stabilizer `V` is a complement of the range of `T`, the `V`-component of the right
inverse normalized by `q` is the projection onto `V` along the range. -/
theorem snd_kerSection_coprod_apply (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible)
    (hV : IsCompl V T.range) (y : F) :
    (q.kerSection (T.coprod V.subtypeL) y).2 = V.projectionOnto T.range hV y := by
  have hmem : T (q.kerSection (T.coprod V.subtypeL) y).1 ∈ T.range := ⟨_, rfl⟩
  conv_rhs => rw [← apply_fst_kerSection_coprod_add_snd hinv y]
  rw [map_add, Submodule.projectionOnto_apply_of_mem_right hV hmem,
    Submodule.projectionOnto_apply_left, zero_add]

/-- **A stabilizer of the right dimension is an exact cokernel complement.** If the stabilized
operator `T + inclusion_V` paired with `q` is invertible and `V` has dimension at most the
codimension of the range of `T`, then `V` is a topological complement of the range. The
stabilized operator is surjective, so this dimension bound holds exactly when the cokernel of `T`
has the dimension of `V`. -/
theorem isTopCompl_of_isInvertible_prod_coprod [FiniteDimensional 𝕜 V]
    (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible)
    (hrank : Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (F ⧸ T.range)) : IsTopCompl V T.range := by
  have hcodisj : Codisjoint T.range V := by
    refine codisjoint_iff.mpr (eq_top_iff.mpr fun y _ ↦ ?_)
    rw [← apply_fst_kerSection_coprod_add_snd hinv y]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (Submodule.coe_mem _)
  have hV : IsCompl V T.range :=
    (Submodule.isCompl_of_codisjoint_of_finrank_le hcodisj hrank).symm
  refine (Submodule.IsCompl.isTopCompl_iff_projectionOnto hV).mpr <|
    (snd 𝕜 E V ∘L q.kerSection (T.coprod V.subtypeL)).continuous.congr fun y ↦ ?_
  simp [snd_kerSection_coprod_apply hinv hV]

/-- The continuous projection onto an exact stabilizer `V` along the range of `T` is the
`V`-component of the right inverse of `T + inclusion_V` normalized by `q`. Through this formula
the projection inherits the regularity of an operator family; see
`ContinuousLinearMap.continuousAt_snd_comp_kerSection_coprod` and
`ContinuousLinearMap.contDiffAt_snd_comp_kerSection_coprod`. -/
theorem projectionOntoL_eq_snd_comp_kerSection_coprod
    (hinv : ((T.coprod V.subtypeL).prod q).IsInvertible) (hV : IsTopCompl V T.range) :
    V.projectionOntoL T.range hV = snd 𝕜 E V ∘L q.kerSection (T.coprod V.subtypeL) := by
  ext y
  simp [snd_kerSection_coprod_apply hinv hV.isCompl]

end CokernelProjection

section Family

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace E]
  {V : Submodule 𝕜 F} [CompleteSpace V] {q : (E × V) →L[𝕜] G}

/-- The stabilizer component of the normalized right inverse of `T x + inclusion_V` is continuous
at every parameter where the family is continuous and the pairing with `q` is invertible. -/
theorem continuousAt_snd_comp_kerSection_coprod {X : Type*} [TopologicalSpace X]
    {T : X → E →L[𝕜] F} {x : X} (hT : ContinuousAt T x)
    (hinv : (((T x).coprod V.subtypeL).prod q).IsInvertible) :
    ContinuousAt (fun y ↦ snd 𝕜 E V ∘L q.kerSection ((T y).coprod V.subtypeL)) x := by
  have hker := (contDiffAt_kerSection (n := 0) (isInvertible_prod_comm.mp hinv)).continuousAt
  exact continuousAt_const.clm_comp <| hker.comp
    (f := fun y ↦ (q, (T y).coprod V.subtypeL))
    (continuousAt_const.prodMk (hT.continuousLinearMapCoprod continuousAt_const))

/-- The stabilizer component of the normalized right inverse of `T x + inclusion_V` has the
regularity of the operator family, at every parameter where the pairing with `q` is invertible. -/
theorem contDiffAt_snd_comp_kerSection_coprod {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {T : X → E →L[𝕜] F} {x : X} {n : ℕ∞ω} (hT : ContDiffAt 𝕜 n T x)
    (hinv : (((T x).coprod V.subtypeL).prod q).IsInvertible) :
    ContDiffAt 𝕜 n (fun y ↦ snd 𝕜 E V ∘L q.kerSection ((T y).coprod V.subtypeL)) x := by
  have hcoprod : ContDiffAt 𝕜 n (fun y ↦ (T y).coprod V.subtypeL) x := by
    simp_rw [← comp_fst_add_comp_snd]
    exact (hT.clm_comp contDiffAt_const).add contDiffAt_const
  exact contDiffAt_const.clm_comp <|
    (contDiffAt_kerSection (isInvertible_prod_comm.mp hinv)).comp
      (f := fun y ↦ (q, (T y).coprod V.subtypeL)) x (contDiffAt_const.prodMk hcoprod)

end Family

variable [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F]
  {X : Type*} [TopologicalSpace X] {T : X → E →L[𝕜] F} {x₀ : X}

/-- A family continuous and Fredholm at one point admits a fixed finite-dimensional target
stabilizer and fixed kernel coordinate on a neighbourhood. The stabilizer can be chosen inside any
dense subspace `D` of the target, for instance a space of smooth compactly supported sections, and
it is then a topological complement of the range at the base point. Pairing the stabilized
operator with the coordinate is invertible on the neighbourhood. For continuous families,
`kernelHomeomorph` supplies actual local product charts, with model the finite-dimensional
stabilized kernel at the base point.
No Fredholm hypothesis is imposed away from the base point. At the parameters of the
neighbourhood where the cokernel keeps its dimension at the base point, the stabilizer stays an
exact complement of the range (`ContinuousLinearMap.isTopCompl_of_isInvertible_prod_coprod`). -/
theorem IsFredholm.exists_stabilization_kernel_coordinates (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) {D : Submodule 𝕜 F} (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ IsTopCompl S (T x₀).range ∧ FiniteDimensional 𝕜 S ∧
      ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
          ∀ x ∈ U, (((T x).coprod S.subtypeL).prod q).IsInvertible := by
  have := hT₀.finite_coker
  obtain ⟨S, hSD, hS⟩ := Submodule.exists_le_isTopCompl_of_dense hT₀.isClosed_range hD
  have : FiniteDimensional 𝕜 S :=
    ((T x₀).range.quotientEquivOfIsCompl S hS.isCompl).finiteDimensional
  have : IsClosed (S : Set F) := S.closed_of_finiteDimensional
  let A : X → (E × S) →L[𝕜] F := fun x ↦ (T x).coprod S.subtypeL
  have hsurj : Surjective (A x₀) := by
    apply LinearMap.range_eq_top.mp
    rw [range_coprod, Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
    exact hS.isCompl.sup_eq_top
  have hfred : IsFredholm (A x₀) := hT₀.coprod_of_finiteDimensional S.subtypeL
  let q := Classical.choose hfred.closedComplemented_ker
  have hinv : ((A x₀).prod q).IsInvertible := by
    refine ⟨(A x₀).implicitCoordEquiv (LinearMap.range_eq_top.mpr hsurj)
      hfred.closedComplemented_ker, ?_⟩
    exact coe_implicitCoordEquiv _ _ _
  have hA : ContinuousAt A x₀ := hT.continuousLinearMapCoprod continuousAt_const
  obtain ⟨U, hU, hx₀, hUinv⟩ := exists_isOpen_isInvertible_prod hA hinv
  exact ⟨S, hSD, hS.symm, inferInstance, q, U, hU, hx₀, hUinv⟩

end ContinuousLinearMap
