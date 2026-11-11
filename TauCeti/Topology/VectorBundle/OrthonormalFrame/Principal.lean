/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

Every equivariant trivialization of the frame bundle (such as
`Bundle.Trivialization.orthonormalFrameBundle`, the trivialization by a Gram–Schmidt local frame)
transports to an equivariant trivialization of `Fiber 𝕜 F E V`
(`TauCeti.OrthonormalFrameBundle.fiberTrivialization`). The fibre bundle structure
(`TauCeti.OrthonormalFrameBundle.instFiberBundleFiber`) takes as atlas all equivariant
trivializations, with preferred trivialization at `x` the Gram–Schmidt trivialization over the
preferred trivialization of `E` at `x`, so it is a principal bundle
(`TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`). Its division map sends two frames
`φ, ψ` of `E b` to the unitary transformation `φ⁻¹ ∘ ψ`
(`TauCeti.OrthonormalFrameBundle.division_eq`). The dimension condition is supplied as an instance
`Fact (Module.finrank 𝕜 V = Module.finrank 𝕜 F)`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.Fiber 𝕜 F E V b`: the orthonormal frames of `E b` modelled on `V`.
* `TauCeti.OrthonormalFrameBundle.totalSpaceHomeomorph`: the total space of `Fiber 𝕜 F E V` is
  homeomorphic to `OrthonormalFrameBundle 𝕜 F E V`.
* `TauCeti.OrthonormalFrameBundle.fiberTrivialization`: a trivialization of the frame bundle as a
  trivialization of `Fiber 𝕜 F E V`.
* `TauCeti.OrthonormalFrameBundle.instFiberBundleFiber`,
  `TauCeti.OrthonormalFrameBundle.instPrincipalBundleFiber`: `Fiber 𝕜 F E V` is a principal bundle
  with structure group `unitary (V →L[𝕜] V)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.isEquivariant_fiberTrivialization`: equivariant trivializations
  of the frame bundle give equivariant trivializations of `Fiber 𝕜 F E V`.
* `TauCeti.OrthonormalFrameBundle.division_eq`: the division map is `φ⁻¹ ∘ ψ`.

## References

* D. Husemoller, *Fibre Bundles*, third edition, Graduate Texts in Mathematics 20, Springer
  (1994), Chapter 4 (principal bundles) and Chapter 5, §§4–5 (the principal bundle of orthonormal
  frames).
* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience (1963),
  Chapter I, §5.
-/

@[expose] public section

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
  one_smul φ := Fiber.ext <| by
    change (Unitary.linearIsometryEquiv (unop 1)).trans φ.frame = φ.frame
    rw [unop_one, map_one, LinearIsometryEquiv.one_def, LinearIsometryEquiv.refl_trans]
  mul_smul g h φ := Fiber.ext <| by
    change (Unitary.linearIsometryEquiv (unop (g * h))).trans φ.frame =
      (Unitary.linearIsometryEquiv g.unop).trans
        ((Unitary.linearIsometryEquiv h.unop).trans φ.frame)
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

@[simp]
theorem proj_totalSpaceEquiv (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    (totalSpaceEquiv p).proj = p.proj :=
  rfl

@[simp]
theorem frame_totalSpaceEquiv (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    (totalSpaceEquiv p).frame = p.2.frame :=
  rfl

@[simp]
theorem totalSpaceEquiv_symm_apply (p : OrthonormalFrameBundle 𝕜 F E V) :
    totalSpaceEquiv.symm p =
      (⟨p.proj, .ofFrame p.frame⟩ : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :=
  rfl

/-- The identification of the total space with the frame bundle intertwines the right actions of
the unitary group. -/
theorem totalSpaceEquiv_smul (g : (unitary (V →L[𝕜] V))ᵐᵒᵖ) {b : B} (φ : Fiber 𝕜 F E V b) :
    totalSpaceEquiv (⟨b, g • φ⟩ : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) =
      g • totalSpaceEquiv ⟨b, φ⟩ :=
  rfl

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
  rfl

@[simp]
theorem coe_totalSpaceHomeomorph_symm :
    ⇑(totalSpaceHomeomorph : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) ≃ₜ _).symm =
      totalSpaceEquiv.symm :=
  rfl

variable [TopologicalSpace B]

/-- A trivialization of the orthonormal frame bundle, as a trivialization of `Fiber 𝕜 F E V`: it
reads a frame `φ` of `E b` as `t ⟨b, φ⟩`. -/
def fiberTrivialization
    (t : Trivialization (unitary (V →L[𝕜] V)) (proj : OrthonormalFrameBundle 𝕜 F E V → B)) :
    Trivialization (unitary (V →L[𝕜] V)) (π (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :=
  t.compHomeomorph totalSpaceHomeomorph

variable (t : Trivialization (unitary (V →L[𝕜] V)) (proj : OrthonormalFrameBundle 𝕜 F E V → B))

@[simp]
theorem fiberTrivialization_apply (p : TotalSpace (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V)) :
    fiberTrivialization t p = t (totalSpaceEquiv p) :=
  rfl

@[simp]
theorem fiberTrivialization_symm_apply (q : B × unitary (V →L[𝕜] V)) :
    (fiberTrivialization t).toOpenPartialHomeomorph.symm q =
      totalSpaceEquiv.symm (t.toOpenPartialHomeomorph.symm q) :=
  rfl

@[simp]
theorem baseSet_fiberTrivialization : (fiberTrivialization t).baseSet = t.baseSet :=
  rfl

/-- A trivialization of the frame bundle that is equivariant for the right action of the unitary
group gives an equivariant trivialization of `Fiber 𝕜 F E V`. -/
theorem isEquivariant_fiberTrivialization
    (ht : ∀ (g : unitary (V →L[𝕜] V)) (p : OrthonormalFrameBundle 𝕜 F E V),
      t (op g • p) = ((t p).1, (t p).2 * g)) :
    (fiberTrivialization t).IsEquivariant where
  snd_apply_smul _ _ φ g := congrArg Prod.snd (ht g (totalSpaceEquiv ⟨_, φ⟩))

end TotalSpace

/-- The dimension condition of `TauCeti.OrthonormalFrameBundle.instFiberBundleFiber` holds when the
frames are modelled on the model fibre itself. -/
instance instFactFinrankEqSelf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Fact (Module.finrank R M = Module.finrank R M) :=
  ⟨rfl⟩

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
  fiberTrivialization ((trivializationAt F E x).orthonormalFrameBundle
    (Module.finBasisOfFinrankEq 𝕜 F h.symm) (stdOrthonormalBasis 𝕜 V))

theorem baseSet_trivializationAtFiber (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F) (x : B) :
    (trivializationAtFiber 𝕜 F E V h x).baseSet = (trivializationAt F E x).baseSet :=
  Trivialization.baseSet_orthonormalFrameBundle _ _ _

theorem isEquivariant_trivializationAtFiber (h : Module.finrank 𝕜 V = Module.finrank 𝕜 F)
    (x : B) : (trivializationAtFiber 𝕜 F E V h x).IsEquivariant :=
  isEquivariant_fiberTrivialization _ (Trivialization.orthonormalFrameBundle_smul _ _ _)

variable [hV : Fact (Module.finrank 𝕜 V = Module.finrank 𝕜 F)]

/-- When `V` has the dimension of the finite-dimensional model fibre `F`, the orthonormal frames
`Fiber 𝕜 F E V` form a fibre bundle with fibre the unitary group of `V`. Its atlas consists of all
trivializations equivariant for the right action of the unitary group, and its preferred
trivialization at `x` is `trivializationAtFiber`, the Gram–Schmidt trivialization over the
preferred trivialization of `E` at `x`. -/
instance instFiberBundleFiber : FiberBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) where
  totalSpaceMk_isInducing' _ := ⟨rfl⟩
  trivializationAtlas' := {t | t.IsEquivariant}
  trivializationAt' := trivializationAtFiber 𝕜 F E V hV.out
  mem_baseSet_trivializationAt' x :=
    (baseSet_trivializationAtFiber (E := E) hV.out x).symm ▸ mem_baseSet_trivializationAt F E x
  trivialization_mem_atlas' x := isEquivariant_trivializationAtFiber hV.out x

theorem trivializationAt_fiber (x : B) :
    trivializationAt (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) x =
      trivializationAtFiber 𝕜 F E V hV.out x :=
  rfl

/-- A trivialization belongs to the atlas of `Fiber 𝕜 F E V` exactly when it is equivariant. -/
theorem memTrivializationAtlas_fiber_iff
    (t : Trivialization (unitary (V →L[𝕜] V)) (π (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V))) :
    MemTrivializationAtlas t ↔ t.IsEquivariant :=
  ⟨fun h ↦ h.out, fun h ↦ ⟨h⟩⟩

/-- When `V` has the dimension of the finite-dimensional model fibre `F`, the orthonormal frames
`Fiber 𝕜 F E V` form a principal bundle with structure group the unitary group of `V`, acting on
the right by precomposition. -/
instance instPrincipalBundleFiber : PrincipalBundle (unitary (V →L[𝕜] V)) (Fiber 𝕜 F E V) :=
  ⟨fun _ h ↦ h.out⟩

/-- The division map of the orthonormal frame bundle sends two frames `φ, ψ` of `E b` to the
unitary transformation `φ⁻¹ ∘ ψ` of `V`. -/
theorem division_eq {b : B} (φ ψ : Fiber 𝕜 F E V b) :
    PrincipalBundle.division (unitary (V →L[𝕜] V)) φ ψ =
      Unitary.linearIsometryEquiv.symm (ψ.frame.trans φ.frame.symm) := by
  refine PrincipalBundle.division_eq_iff.2 (Fiber.ext ?_)
  ext v
  simp

end Principal

end TauCeti.OrthonormalFrameBundle
