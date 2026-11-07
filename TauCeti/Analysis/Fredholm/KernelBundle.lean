/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Stabilization
public import TauCeti.Geometry.Manifold.VectorBundle.Kernel
import TauCeti.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Local bundles of stabilized Fredholm kernels

For a continuous family Fredholm at a base point, one finite-dimensional
subspace `S` of the target makes `T x + inclusion_S` surjective nearby. It can be
chosen inside any dense subspace of the target, such as smooth compactly supported
sections.
The kernels of these stabilized operators form a native vector bundle on
that neighbourhood, modelled on the finite-dimensional stabilized kernel
at the base point. Its total space has the subspace topology from the
product of the neighbourhood and `E × S`.

This supplies the kernel bundles whose top exterior powers enter the local
construction of Fredholm determinant lines. The unstabilized kernels may
jump in dimension; no bundle assertion about those kernels is made.
For a `C^n` family, the stabilized kernel bundle and its inclusion into the
ambient product are `C^n`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second
  edition, Appendix A.2 (finite stabilization and determinant bundles).

The stabilizer and complementary coordinate come from
`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates`.
-/

public section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace ContinuousLinearMap

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace X] {T : X → E →L[𝕜] F} {x₀ : X}

/-- A continuous family Fredholm at `x₀` has a finite target stabilizer, inside any
prescribed dense subspace `D`, whose kernels form a vector bundle on an open
neighbourhood of `x₀`. Both the stabilizer and the model kernel are finite
dimensional. The chosen global chart on that neighbourhood is
`TauCeti.kernelTrivialization`, with fibre coordinate `q` and inverse `kerSection`;
the total-space topology is induced from `U × (E × S)`. -/
theorem IsFredholm.exists_stabilization_kernel_vectorBundle (hT₀ : IsFredholm (T x₀))
    (hT : Continuous T) {D : Submodule 𝕜 F} (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ ∃ hS : FiniteDimensional 𝕜 S,
      letI := hS
      letI := FiniteDimensional.complete 𝕜 S
      ∃ _ : FiniteDimensional 𝕜 ((T x₀).coprod S.subtypeL).ker,
        ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
          ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
            ∃ h : ∀ x : U, (((T x).coprod S.subtypeL).prod q).IsInvertible,
              letI := TauCeti.kernelFiberBundle
                ((hT.comp continuous_subtype_val).continuousLinearMapCoprod continuous_const) h
              VectorBundle 𝕜 ((T x₀).coprod S.subtypeL).ker
                (fun x : U ↦ ((T x).coprod S.subtypeL).ker) := by
  obtain ⟨S, hSD, -, hS, q, U, hU, hx₀, hinv⟩ :=
    hT₀.exists_stabilization_kernel_coordinates hT.continuousAt hD
  let := hS
  let := FiniteDimensional.complete 𝕜 S
  exact ⟨S, hSD, hS, (hT₀.coprod_of_finiteDimensional S.subtypeL).finite_ker,
    q, U, hU, hx₀, fun x ↦ hinv x x.property,
    TauCeti.kernelVectorBundle (X := U)
      ((hT.comp continuous_subtype_val).continuousLinearMapCoprod continuous_const)
      (fun x ↦ hinv x x.property)⟩

variable {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
  [TopologicalSpace HX] {I : ModelWithCorners 𝕜 EX HX}
  [ChartedSpace HX X] {n : ℕ∞ω}

/-- A `C^n` family Fredholm at one point has a finite target stabilizer on an
open neighbourhood, with a `C^n` finite-rank kernel bundle and `C^n` inclusion
into the ambient product. The topology and charts are the native split-kernel
ones. No constant-rank hypothesis on the unstabilized kernels is required. -/
theorem IsFredholm.exists_stabilization_kernel_contMDiffVectorBundle
    (hT₀ : IsFredholm (T x₀)) (hT : ContMDiff I 𝓘(𝕜, E →L[𝕜] F) n T) :
    ∃ S : Submodule 𝕜 F, ∃ hS : FiniteDimensional 𝕜 S,
      letI := hS
      letI := FiniteDimensional.complete 𝕜 S
      ∃ _ : FiniteDimensional 𝕜 ((T x₀).coprod S.subtypeL).ker,
        ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
          ∃ U : TopologicalSpace.Opens X, x₀ ∈ U ∧
            ∃ h : ∀ x : U, (((T x).coprod S.subtypeL).prod q).IsInvertible,
              ∃ hA : ContMDiff I 𝓘(𝕜, (E × S) →L[𝕜] F) n
                  (fun x : U ↦ (T x).coprod S.subtypeL),
                letI := TauCeti.kernelFiberBundle hA.continuous h
                letI := TauCeti.kernelVectorBundle hA.continuous h
                ContMDiffVectorBundle n ((T x₀).coprod S.subtypeL).ker
                    (fun x : U ↦ ((T x).coprod S.subtypeL).ker) I ∧
                  ContMDiff (I.prod 𝓘(𝕜, ((T x₀).coprod S.subtypeL).ker))
                    (I.prod 𝓘(𝕜, E × S)) n
                    (fun p : TotalSpace ((T x₀).coprod S.subtypeL).ker
                      (fun x : U ↦ ((T x).coprod S.subtypeL).ker) ↦
                        (p.proj, (p.2 : E × S))) := by
  obtain ⟨S, hS, q, U, hU, hx₀, hinv⟩ :=
    hT₀.exists_stabilization_kernel_coordinates hT.continuous.continuousAt
  let := hS
  let := FiniteDimensional.complete 𝕜 S
  let V : TopologicalSpace.Opens X := ⟨U, hU⟩
  have hA : ContMDiff I 𝓘(𝕜, (E × S) →L[𝕜] F) n
      (fun x : V ↦ (T x).coprod S.subtypeL) :=
    (hT.comp contMDiff_subtype_val).clm_coprod contMDiff_const
  exact ⟨S, hS, (hT₀.coprod_of_finiteDimensional S.subtypeL).finite_ker,
    q, V, hx₀, fun x ↦ hinv x x.property, hA,
    TauCeti.kernelContMDiffVectorBundle hA.continuous _,
    TauCeti.contMDiff_kernel_inclusion hA _⟩

end ContinuousLinearMap
