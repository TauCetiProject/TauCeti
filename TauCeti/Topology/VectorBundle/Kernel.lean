/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Splitting.Family
public import Mathlib.Topology.FiberBundle.Constructions
public import TauCeti.Topology.VectorBundle.Subbundle

/-!
# The kernel bundle of a continuously split operator family

Suppose `A x : E →L[𝕜] F` is continuous and pairing it with one fixed map
`q : E →L[𝕜] G` is invertible at every base point. Then its kernels form a
vector bundle with model fibre `G`, with the topology induced from `X × E`.
The global trivialization reads a kernel vector through `q`; its inverse is
`ContinuousLinearMap.kerSection`. These are the native bundle structures on
local split-kernel coordinates, in particular those of stabilized Fredholm families.

Use `TauCeti.kernelFiberBundle` as a local instance, followed by
`TauCeti.kernelVectorBundle`. The topology on the total space is independent
of the splitting and of the model fibre. No finite-dimensionality is needed.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second
  edition, Appendix A.2, for stabilized kernels and determinant bundles.

The coordinates use `ContinuousLinearMap.kernelHomeomorph` and
`ContinuousLinearMap.kerSection`.
-/

public section

open Bundle Set Topology

namespace TauCeti

variable {𝕜 X E F G : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The total space of the kernels has the subspace topology from `X × E`,
independently of the model-fibre parameter. -/
instance instTopologicalSpaceTotalSpaceKernel (G : Type*) (A : X → E →L[𝕜] F) :
    TopologicalSpace (TotalSpace G fun x ↦ (A x).ker) :=
  subbundleTopology E (E := Trivial X E) (fun x ↦ (A x).ker)

variable [CompleteSpace E] {A : X → E →L[𝕜] F} {q : E →L[𝕜] G}
  (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible)

/-- A fixed complementary coordinate globally trivializes the kernel bundle.
The fibre coordinate is `q`, with inverse `kerSection`. -/
noncomputable def kernelTrivialization :
    Trivialization G (π G fun x ↦ (A x).ker) := by
  have he := (Trivial.homeomorphProd X E).isEmbedding.comp
    (isEmbedding_totalSpace_subbundle E G (E := Trivial X E) (fun x ↦ (A x).ker))
  let e : TotalSpace G (fun x ↦ (A x).ker) ≃ₜ {p : X × E | A p.1 p.2 = 0} :=
    { toFun := fun v ↦ ⟨(v.proj, v.2), v.2.property⟩
      invFun := fun p ↦ ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := he.continuous.subtype_mk _
      continuous_invFun := he.continuous_iff.mpr continuous_subtype_val }
  exact {
    toOpenPartialHomeomorph :=
      (e.trans (ContinuousLinearMap.kernelHomeomorph A q hA h)).toOpenPartialHomeomorph
    baseSet := univ
    open_baseSet := isOpen_univ
    source_eq := by simp
    target_eq := by simp
    proj_toFun := by
      intro v _
      exact congrArg Prod.fst (ContinuousLinearMap.kernelHomeomorph_apply hA h (e v)) }

@[simp]
theorem kernelTrivialization_baseSet : (kernelTrivialization hA h).baseSet = univ :=
  (rfl)

@[simp]
theorem kernelTrivialization_apply (v : TotalSpace G fun x ↦ (A x).ker) :
    kernelTrivialization hA h v = (v.proj, q v.2) := by
  exact ContinuousLinearMap.kernelHomeomorph_apply hA h ⟨(v.proj, v.2), v.2.property⟩

/-- The inverse chart's underlying domain vector is the kernel section. -/
@[simp]
theorem coe_kernelTrivialization_symm_apply (x : X) (v : G) :
    (((kernelTrivialization hA h).symm x v : (A x).ker) : E) =
      (A x).kerSection q v := by
  have hq : q ((kernelTrivialization hA h).symm x v) = v := by
    simpa only [kernelTrivialization_apply] using congrArg Prod.snd
      ((kernelTrivialization hA h).apply_mk_symm (mem_univ x) v)
  exact (ContinuousLinearMap.kerSection_apply_of_mem_ker (h x)
    ((kernelTrivialization hA h).symm x v).property).symm.trans (congrArg _ hq)

/-- Kernel coordinates are linear on each fibre. -/
instance isLinear_kernelTrivialization : (kernelTrivialization hA h).IsLinear 𝕜 where
  linear x _ := by
    constructor <;> intros <;> simp

/-- The kernel bundle with its global split-kernel chart. Install as a local instance. -/
@[instance_reducible]
noncomputable def kernelFiberBundle : FiberBundle G fun x ↦ (A x).ker where
  totalSpaceMk_isInducing' :=
    isInducing_totalSpaceMk_subbundle E G (E := Trivial X E) (fun x ↦ (A x).ker)
  trivializationAtlas' := {kernelTrivialization hA h}
  trivializationAt' _ := kernelTrivialization hA h
  mem_baseSet_trivializationAt' x := mem_univ x
  trivialization_mem_atlas' _ := mem_singleton _

/-- The chosen trivialization of the kernel bundle is its split-kernel chart. -/
theorem trivializationAt_kernelFiberBundle (x : X) :
    letI := kernelFiberBundle hA h
    trivializationAt G (fun x ↦ (A x).ker) x = kernelTrivialization hA h :=
  (rfl)

/-- With its subspace topology and split-kernel coordinates, the kernels form a vector bundle. -/
theorem kernelVectorBundle :
    letI := kernelFiberBundle hA h
    VectorBundle 𝕜 G fun x ↦ (A x).ker := by
  let := kernelFiberBundle hA h
  have he (e : Trivialization G (π G fun x ↦ (A x).ker))
      (he : MemTrivializationAtlas e) : e = kernelTrivialization hA h :=
    mem_singleton_iff.mp he.out
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro e he'
    obtain rfl := he e he'
    infer_instance
  · intro e e' he' he''
    obtain rfl := he e he'
    obtain rfl := he e' he''
    have hc (x : X) : (kernelTrivialization hA h).coordChangeL 𝕜
        (kernelTrivialization hA h) x = ContinuousLinearEquiv.refl 𝕜 G := by
      ext v
      rw [Trivialization.coordChangeL_apply']
      · simp
      · exact ⟨mem_univ x, mem_univ x⟩
    simp only [hc]
    exact continuous_const.continuousOn

end TauCeti
