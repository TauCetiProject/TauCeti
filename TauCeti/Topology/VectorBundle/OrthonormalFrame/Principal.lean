/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dimension.FactFinrank
public import TauCeti.Topology.FiberBundle.Principal.Basic
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic

/-!
# The orthonormal frame bundle as a principal bundle

Let `E → B` be a vector bundle over an `RCLike` field `𝕜` with finite-dimensional model fibre `F`
and fibre inner products with continuous norm, and let `V` be an inner product space with the
dimension of `F`. The orthonormal frames of `E` modelled on `V` form
`TauCeti.OrthonormalFrameBundle 𝕜 F E V`, a type of pairs of a base point and a frame. This file
presents the same frames as the fibres of a bundle `TauCeti.OrthonormalFrameBundle.Fiber 𝕜 F E V`
over `B`, with fibre over `b` the frames `V ≃ₗᵢ[𝕜] E b`, so that Mathlib's fibre bundle API and
Tau Ceti's principal bundle API (`TauCeti.PrincipalBundle`) apply. For `𝕜 = ℂ` this is the unitary
frame bundle of a Hermitian vector bundle, a principal `U(n)`-bundle; for `𝕜 = ℝ` it is the
orthonormal frame bundle of a Riemannian vector bundle, a principal `O(n)`-bundle. In both cases
the structure group is `unitary (V →L[𝕜] V)` with its operator-norm topology, acting on the right
by precomposition.

The total space of `Fiber 𝕜 F E V` is identified with `OrthonormalFrameBundle 𝕜 F E V`
(`TauCeti.OrthonormalFrameBundle.totalSpaceHomeomorph`) and carries the topology making this a
homeomorphism, the topology of pointwise convergence of frames. Each fibre carries the subspace
topology. The model fibre `F` is a parameter of `Fiber` because the topology of the total space of
`E`, and hence of the frames, is read through it.

Every trivialization of the frame bundle transports to a trivialization of `Fiber 𝕜 F E V`
(`Bundle.Trivialization.orthonormalFrameBundleFiber`), which is equivariant exactly when the
original one is equivariant over its base set. In particular the trivializations by Gram–Schmidt
local frames (`Bundle.Trivialization.orthonormalFrameBundle`) give equivariant trivializations. The
fibre bundle structure (`TauCeti.OrthonormalFrameBundle.instFiberBundleFiber`) takes as atlas the
Gram–Schmidt trivializations over the trivializations in the atlas of `E`, with preferred
trivialization at `x` the one over the preferred trivialization of `E` at `x`, so it is a principal
bundle (`TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`). The division map of any
principal bundle structure on `Fiber 𝕜 F E V` sends two frames `φ, ψ` of `E b` to the unitary
transformation `φ⁻¹ ∘ ψ` (`TauCeti.OrthonormalFrameBundle.division_eq`). The dimension condition
is supplied as an instance `Fact (Module.finrank 𝕜 V = Module.finrank 𝕜 F)`, which holds by
instance when `V = F` (`TauCeti.instFactFinrankEqSelf`).

## Main definitions

* `TauCeti.OrthonormalFrameBundle.Fiber 𝕜 F E V b`: the orthonormal frames of `E b` modelled on `V`.
* `TauCeti.OrthonormalFrameBundle.totalSpaceHomeomorph`: the total space of `Fiber 𝕜 F E V` is
  homeomorphic to `OrthonormalFrameBundle 𝕜 F E V`.
* `Bundle.Trivialization.orthonormalFrameBundleFiber`: a trivialization of the frame bundle as a
  trivialization of `Fiber 𝕜 F E V`.
* `TauCeti.OrthonormalFrameBundle.instFiberBundleFiber`,
  `TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`: `Fiber 𝕜 F E V` is a principal bundle
  with structure group `unitary (V →L[𝕜] V)`.

## Main results

* `Bundle.Trivialization.isEquivariant_orthonormalFrameBundleFiber_iff`: a trivialization of the
  frame bundle gives an equivariant trivialization of `Fiber 𝕜 F E V` exactly when it is
  equivariant over its base set.
* `TauCeti.OrthonormalFrameBundle.division_eq`: the division map is `φ⁻¹ ∘ ψ`.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 4 (principal bundles) and Chapter 5, §§4–5 (the principal bundle of orthonormal
  frames).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience (1963),
  Chapter I, §5.
-/

public section

noncomputable section

open Bundle Set MulOpposite

variable {𝕜 : Type*} [RCLike 𝕜] {B : Type*} {F : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

namespace TauCeti.OrthonormalFrameBundle

/-- The fibre over `b` of the orthonormal frame bundle of `E` modelled on `V`, as a family over the
base: the linear isometric equivalences `V ≃ₗᵢ[𝕜] E b`. The model fibre `F` of `E` determines the
topology of the total space (`TauCeti.OrthonormalFrameBundle.totalSpaceHomeomorph`). -/
@[ext]
structure Fiber (𝕜 : Type*) [RCLike 𝕜] (F : Type*) (E : B → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace 𝕜 (E x)] (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (b : B) where
  /-- Regard an orthonormal frame of `E b` as a point of the fibre over `b`. -/
  ofFrame ::
  /-- The orthonormal frame of `E b` underlying a point of the fibre over `b`. -/
  frame : V ≃ₗᵢ[𝕜] E b

namespace Fiber

/-- A point of the fibre is the frame it carries. -/
@[simp]
theorem ofFrame_frame {b : B} (φ : Fiber 𝕜 F E V b) : ofFrame φ.frame = φ :=
  rfl

/-- The frame carried by `ofFrame φ` is `φ`. -/
@[simp]
theorem frame_ofFrame {b : B} (φ : V ≃ₗᵢ[𝕜] E b) : (ofFrame φ : Fiber 𝕜 F E V b).frame = φ :=
  rfl

variable [CompleteSpace V]

/-- The right action of the unitary group `unitary (V →L[𝕜] V)` on the frames of a fibre by
precomposition: `op g` carries the frame `φ` to `φ ∘ g`. -/
instance instMulAction (b : B) : MulAction (unitary (V →L[𝕜] V))ᵐᵒᵖ (Fiber 𝕜 F E V b) where
  smul g φ := ofFrame ((Unitary.linearIsometryEquiv g.unop).trans φ.frame)
  -- By the definition of `smul`, both sides of each action law are points `ofFrame _`, so
  -- `congrArg ofFrame` reduces the law to an identity of linear isometric equivalences. In
  -- `mul_smul`, the frame of `h • φ` is by definition the composite that `trans_assoc` expects.
  one_smul φ := congrArg ofFrame <| by
    rw [unop_one, map_one, LinearIsometryEquiv.one_def, LinearIsometryEquiv.refl_trans]
  mul_smul g h φ := congrArg ofFrame <| by
    rw [unop_mul, map_mul, LinearIsometryEquiv.mul_def]
    exact LinearIsometryEquiv.trans_assoc _ _ _

/-- The action precomposes the frame with the unitary transformation. -/
@[simp]
theorem frame_smul_apply {b : B} (g : (unitary (V →L[𝕜] V))ᵐᵒᵖ) (φ : Fiber 𝕜 F E V b) (v : V) :
    (g • φ).frame v = φ.frame ((g.unop : V →L[𝕜] V) v) :=
  rfl

end Fiber

section TotalSpace

variable [CompleteSpace V]

/-- The total space of `Fiber 𝕜 F E V` is the type `OrthonormalFrameBundle 𝕜 F E V` of pairs of a
base point and a frame. -/
def totalSpaceEquiv :
    TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) ≃ OrthonormalFrameBundle 𝕜 F E V where
  toFun p := ⟨p.proj, p.2.frame⟩
  invFun p := ⟨p.proj, .ofFrame p.frame⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the total space with the frame bundle sends a point of the fibre over
`b` to the pair of `b` and its frame. -/
@[simp]
theorem totalSpaceEquiv_apply (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceEquiv p = ⟨p.proj, p.2.frame⟩ :=
  (rfl)

theorem proj_totalSpaceEquiv (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    (totalSpaceEquiv p).proj = p.proj :=
  (rfl)

@[simp]
theorem totalSpaceEquiv_symm_apply (p : OrthonormalFrameBundle 𝕜 F E V) :
    totalSpaceEquiv.symm p =
      (⟨p.proj, .ofFrame p.frame⟩ : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :=
  (rfl)

/-- The identification of the total space with the frame bundle intertwines the right actions of
the unitary group. -/
theorem totalSpaceEquiv_smul (g : (unitary (V →L[𝕜] V))ᵐᵒᵖ)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    totalSpaceEquiv (g • p) = g • totalSpaceEquiv p :=
  (rfl)

/-- The inverse identification of the frame bundle with the total space intertwines the right
actions of the unitary group. -/
theorem totalSpaceEquiv_symm_smul (g : (unitary (V →L[𝕜] V))ᵐᵒᵖ)
    (p : OrthonormalFrameBundle 𝕜 F E V) :
    totalSpaceEquiv.symm (g • p) =
      (g • totalSpaceEquiv.symm p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :=
  (rfl)

variable [TopologicalSpace (TotalSpace F E)]

/-- The topology on the total space of `Fiber 𝕜 F E V` making `totalSpaceEquiv` a homeomorphism
onto the orthonormal frame bundle with its topology of pointwise convergence of frames. -/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :=
  .induced totalSpaceEquiv inferInstance

/-- Each fibre of `Fiber 𝕜 F E V` carries the subspace topology of the total space. -/
instance instTopologicalSpaceFiber (b : B) : TopologicalSpace (Fiber 𝕜 F E V b) :=
  .induced (TotalSpace.mk (F := unitary (V →L[𝕜] V)) b) inferInstance

/-- The total space of `Fiber 𝕜 F E V` is homeomorphic to the orthonormal frame bundle
`OrthonormalFrameBundle 𝕜 F E V`. -/
def totalSpaceHomeomorph :
    TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) ≃ₜ OrthonormalFrameBundle 𝕜 F E V :=
  totalSpaceEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

@[simp]
theorem coe_totalSpaceHomeomorph :
    ⇑(totalSpaceHomeomorph : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) ≃ₜ _) =
      totalSpaceEquiv :=
  (rfl)

@[simp]
theorem coe_totalSpaceHomeomorph_symm :
    ⇑(totalSpaceHomeomorph : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) ≃ₜ _).symm =
      totalSpaceEquiv.symm :=
  (rfl)

end TotalSpace

end TauCeti.OrthonormalFrameBundle

namespace Bundle.Trivialization

open TauCeti TauCeti.OrthonormalFrameBundle

variable [CompleteSpace V] [TopologicalSpace (TotalSpace F E)] [TopologicalSpace B]

/-- A trivialization of the orthonormal frame bundle, as a trivialization of `Fiber 𝕜 F E V`: it
reads a frame `φ` of `E b` as `t ⟨b, φ⟩`. -/
def orthonormalFrameBundleFiber
    (t : Trivialization (unitary (V →L[𝕜] V)) (proj : OrthonormalFrameBundle 𝕜 F E V → B)) :
    Trivialization (unitary (V →L[𝕜] V)) (π (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :=
  t.compHomeomorph totalSpaceHomeomorph

variable (t : Trivialization (unitary (V →L[𝕜] V)) (proj : OrthonormalFrameBundle 𝕜 F E V → B))

@[simp]
theorem orthonormalFrameBundleFiber_apply
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    orthonormalFrameBundleFiber t p = t (totalSpaceEquiv p) :=
  (rfl)

@[simp]
theorem orthonormalFrameBundleFiber_symm_apply (q : B × unitary (V →L[𝕜] V)) :
    (orthonormalFrameBundleFiber t).toOpenPartialHomeomorph.symm q =
      totalSpaceEquiv.symm (t.toOpenPartialHomeomorph.symm q) :=
  (rfl)

@[simp]
theorem baseSet_orthonormalFrameBundleFiber : (orthonormalFrameBundleFiber t).baseSet = t.baseSet :=
  (rfl)

/-- A trivialization of the frame bundle gives an equivariant trivialization of `Fiber 𝕜 F E V`
exactly when, over its base set, it intertwines the right action of the unitary group on frames
with right multiplication on the fibre coordinate. -/
theorem isEquivariant_orthonormalFrameBundleFiber_iff :
    (orthonormalFrameBundleFiber t).IsEquivariant ↔
      ∀ p : OrthonormalFrameBundle 𝕜 F E V, p.proj ∈ t.baseSet →
        ∀ g : unitary (V →L[𝕜] V), (t (op g • p)).2 = (t p).2 * g :=
  ⟨fun h p hp g ↦ h.snd_apply_smul p.proj hp (.ofFrame p.frame) g,
    fun h ↦ ⟨fun b hb φ g ↦ h (totalSpaceEquiv ⟨b, φ⟩) hb g⟩⟩

/-- The Gram–Schmidt trivialization of the frame bundle over a linear trivialization of `E` gives
an equivariant trivialization of `Fiber 𝕜 F E V`. -/
instance isEquivariant_orthonormalFrameBundleFiber_orthonormalFrameBundle [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
    [FiniteDimensional 𝕜 V] (e : Trivialization F (π F E)) [e.IsLinear 𝕜] {ι : Type*} [Fintype ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] (c : Module.Basis ι 𝕜 F)
    (b : OrthonormalBasis ι 𝕜 V) :
    (orthonormalFrameBundleFiber (e.orthonormalFrameBundle c b)).IsEquivariant :=
  (isEquivariant_orthonormalFrameBundleFiber_iff _).2 fun p _ g ↦
    congrArg Prod.snd (e.orthonormalFrameBundle_smul c b g p)

end Bundle.Trivialization

namespace TauCeti.OrthonormalFrameBundle

section Principal

variable [CompleteSpace V] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace B] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContinuousFiberNorm F E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 V]

variable (𝕜 F E V) in
/-- The preferred trivialization of `Fiber 𝕜 F E V` at `x`: the Gram–Schmidt trivialization of the
frame bundle over the preferred trivialization of `E` at `x`, for the standard orthonormal basis of
`V` and a basis of `F` indexed alike. -/
def trivializationAtFiber (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F) (x : B) :
    Trivialization (unitary (V →L[𝕜] V)) (π (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :=
  ((trivializationAt F E x).orthonormalFrameBundle
    (Module.finBasisOfFinrankEq 𝕜 F h.symm) (stdOrthonormalBasis 𝕜 V)).orthonormalFrameBundleFiber

/-- The preferred trivialization of `Fiber 𝕜 F E V` at `x` transports the Gram–Schmidt
trivialization of the frame bundle over the preferred trivialization of `E` at `x`. -/
theorem trivializationAtFiber_def (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F) (x : B) :
    trivializationAtFiber 𝕜 F E V h x =
      ((trivializationAt F E x).orthonormalFrameBundle (Module.finBasisOfFinrankEq 𝕜 F h.symm)
        (stdOrthonormalBasis 𝕜 V)).orthonormalFrameBundleFiber :=
  (rfl)

@[simp]
theorem trivializationAtFiber_apply (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F) (x : B)
    (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    trivializationAtFiber 𝕜 F E V h x p = (trivializationAt F E x).orthonormalFrameBundle
      (Module.finBasisOfFinrankEq 𝕜 F h.symm) (stdOrthonormalBasis 𝕜 V) (totalSpaceEquiv p) :=
  (rfl)

@[simp]
theorem trivializationAtFiber_symm_apply (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F) (x : B)
    (q : B × unitary (V →L[𝕜] V)) :
    (trivializationAtFiber 𝕜 F E V h x).toOpenPartialHomeomorph.symm q =
      totalSpaceEquiv.symm (((trivializationAt F E x).orthonormalFrameBundle
        (Module.finBasisOfFinrankEq 𝕜 F h.symm)
        (stdOrthonormalBasis 𝕜 V)).toOpenPartialHomeomorph.symm q) :=
  (rfl)

@[simp]
theorem baseSet_trivializationAtFiber (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F) (x : B) :
    (trivializationAtFiber 𝕜 F E V h x).baseSet = (trivializationAt F E x).baseSet :=
  Trivialization.baseSet_orthonormalFrameBundle _ _ _

instance isEquivariant_trivializationAtFiber (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F)
    (x : B) : (trivializationAtFiber 𝕜 F E V h x).IsEquivariant :=
  Trivialization.isEquivariant_orthonormalFrameBundleFiber_orthonormalFrameBundle _ _ _

variable [hV : Fact (Module.finrank 𝕜 V = Module.finrank 𝕜 F)]

/-- When `V` has the dimension of the finite-dimensional model fibre `F`, the orthonormal frames
`Fiber 𝕜 F E V` form a fibre bundle with fibre the unitary group of `V`. Its atlas consists of the
Gram–Schmidt trivializations over the trivializations in the atlas of `E`, for all bases of `F` and
orthonormal bases of `V` indexed by `Fin (Module.finrank 𝕜 V)`, and its preferred trivialization at
`x` is `trivializationAtFiber`, the one over the preferred trivialization of `E` at `x`. -/
instance instFiberBundleFiber : FiberBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) where
  totalSpaceMk_isInducing' _ := ⟨rfl⟩
  trivializationAtlas' :=
    {t | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e)
      (c : Module.Basis (Fin (Module.finrank 𝕜 V)) 𝕜 F)
      (b : OrthonormalBasis (Fin (Module.finrank 𝕜 V)) 𝕜 V),
      t = (e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber}
  trivializationAt' := trivializationAtFiber 𝕜 F E V hV.out
  mem_baseSet_trivializationAt' x :=
    (baseSet_trivializationAtFiber (E := E) hV.out x).symm ▸ mem_baseSet_trivializationAt F E x
  trivialization_mem_atlas' x :=
    ⟨trivializationAt F E x, inferInstance, _, _, trivializationAtFiber_def hV.out x⟩

theorem trivializationAt_fiber (x : B) :
    trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) x =
      trivializationAtFiber 𝕜 F E V hV.out x :=
  rfl

/-- The preferred trivialization of `Fiber 𝕜 F E V` at `x` has the base set of the preferred
trivialization of `E` at `x`. -/
@[simp]
theorem baseSet_trivializationAt_fiber (x : B) :
    (trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) x).baseSet =
      (trivializationAt F E x).baseSet :=
  baseSet_trivializationAtFiber hV.out x

/-- When `V` has the dimension of the finite-dimensional model fibre `F`, the orthonormal frames
`Fiber 𝕜 F E V` form a principal bundle with structure group the unitary group of `V`, acting on
the right by precomposition. -/
instance instPrincipalBundleFiber : PrincipalBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) where
  isEquivariant_trivialization' _ ht := by
    obtain ⟨e, _, c, b, rfl⟩ := ht.out
    infer_instance

end Principal

section Division

variable [CompleteSpace V] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V))]
  [∀ b, TopologicalSpace (Fiber 𝕜 F E V b)] [FiberBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)]
  [PrincipalBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)]

/-- For any principal bundle structure on the orthonormal frames, such as
`TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`, the division map sends two frames
`φ, ψ` of `E b` to the unitary transformation `φ⁻¹ ∘ ψ` of `V`. -/
theorem division_eq {b : B} (φ ψ : Fiber 𝕜 F E V b) :
    PrincipalBundle.division (unitary (V →L[𝕜] V)) φ ψ =
      Unitary.linearIsometryEquiv.symm (ψ.frame.trans φ.frame.symm) := by
  refine PrincipalBundle.division_eq_iff.2 (Fiber.ext ?_)
  ext v
  simp

end Division

end TauCeti.OrthonormalFrameBundle

namespace Bundle.Trivialization

open TauCeti TauCeti.OrthonormalFrameBundle

variable [CompleteSpace V] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace B] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContinuousFiberNorm F E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 V]
  [Fact (Module.finrank 𝕜 V = Module.finrank 𝕜 F)]

/-- A trivialization belongs to the atlas of the orthonormal frame bundle `Fiber 𝕜 F E V` exactly
when it is the Gram–Schmidt trivialization over a trivialization in the atlas of `E`. -/
theorem memTrivializationAtlas_orthonormalFrameBundleFiber_iff
    (t : Trivialization (unitary (V →L[𝕜] V)) (π (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V))) :
    MemTrivializationAtlas t ↔
      ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e)
        (c : Module.Basis (Fin (Module.finrank 𝕜 V)) 𝕜 F)
        (b : OrthonormalBasis (Fin (Module.finrank 𝕜 V)) 𝕜 V),
        t = (e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber :=
  ⟨fun h ↦ h.out, fun h ↦ ⟨h⟩⟩

/-- The Gram–Schmidt trivialization of `Fiber 𝕜 F E V` over a trivialization in the atlas of `E`
belongs to the atlas of the orthonormal frame bundle. -/
instance memTrivializationAtlas_orthonormalFrameBundleFiber_orthonormalFrameBundle
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    (c : Module.Basis (Fin (Module.finrank 𝕜 V)) 𝕜 F)
    (b : OrthonormalBasis (Fin (Module.finrank 𝕜 V)) 𝕜 V) :
    MemTrivializationAtlas (e.orthonormalFrameBundle c b).orthonormalFrameBundleFiber :=
  ⟨⟨e, inferInstance, c, b, rfl⟩⟩

end Bundle.Trivialization
