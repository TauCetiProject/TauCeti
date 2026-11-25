/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.LinearPMap.Graph.Space
public import TauCeti.RepresentationTheory.Continuous.StronglyContinuous
public import TauCeti.RepresentationTheory.Continuous.Unitary.HilbertSum
public import TauCeti.RepresentationTheory.Continuous.WithLpProd

/-!
# The graph space of an equivariant closed operator

Let a monoid `G` act on normed spaces `E` and `F` by continuous representations `π` and `ρ`, and
let `f : E →ₗ.[𝕜] F` be an unbounded operator commuting with the actions
(`LinearPMap.IsEquivariant`): every `π g × ρ g` maps the graph of `f` into itself, that is, `π g`
preserves the domain of `f` and `f (π g x) = ρ g (f x)`. The graph space of `f`
(`LinearPMap.graphSpace`), the domain of `f` with the graph norm, then carries the representation
`π g × ρ g` (`LinearPMap.graphSpaceRepresentation`), which acts on the domain of `f` as `π` does.
For unitary representations on Hilbert spaces it is unitary for the graph inner product
`⟪x, y⟫ + ⟪f x, f y⟫` (`LinearPMap.isUnitary_graphSpaceRepresentation`), and it is strongly
continuous when `π` and `ρ` are (`LinearPMap.continuous_graphSpaceRepresentation_apply`). The
operator `f`, as the bounded map `f.graphSnd` on its graph space, becomes an intertwining map into
`ρ`
(`LinearPMap.graphSndIntertwiningMap`), whose kernel representation is the restriction of `π` to
the kernel of `f` (`LinearPMap.kerRepresentationGraphSndEquiv`).

This turns an equivariant closed operator, such as an invariant elliptic operator between
`L²`-sections with its Sobolev domain, into an intertwining map between strongly continuous unitary
representations on fixed Hilbert spaces; when `f` is closed and `E`, `F` are Hilbert spaces, the
graph space is a Hilbert space (`LinearPMap.IsClosed.completeSpace_graphSpace`). When this
intertwining map is Fredholm, its equivariant index `ContIntertwiningMap.equivariantIndex` is
defined. The same representations serve every bounded equivariant operator on the graph space,
such as an equivariant approximation of `f` in the norm of bounded operators from the graph space
to `F`.

The representation of `G` on the `L²` product `WithLp 2 (E × F)` used here is the direct sum
`ContRepresentation.withLpProd`.

## Main declarations

* `LinearPMap.IsEquivariant`: the operator `f` commutes with `π` and `ρ`.
* `LinearPMap.graphSpaceRepresentation`: the representation on the graph space of an equivariant
  operator.
* `LinearPMap.graphFstIntertwiningMap`, `LinearPMap.graphSndIntertwiningMap`: the inclusion into
  `E` and the operator `f`, as intertwining maps into `π` and `ρ`.
* `LinearPMap.kerRepresentationGraphSndEquiv`: the kernel representation of
  `LinearPMap.graphSndIntertwiningMap` is the restriction of `π` to the kernel of `f`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, §6 (equivariant elliptic operators and their index in `R(G)`).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer (2012), §1.1 (the graph scalar product of a closed operator).
-/

public section

open scoped InnerProductSpace ContRepresentation

namespace LinearPMap

open ContRepresentation

/-! ### Equivariant operators -/

section IsEquivariant

variable {R G E F : Type*} [Ring R] [Monoid G] [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module R E] [AddCommGroup F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [Module R F]

/-- A partial linear map `f` is **equivariant** for representations `π` and `ρ` when every
`π g × ρ g` maps the graph of `f` into itself, that is, `π g` preserves the domain of `f` and
`f (π g x) = ρ g (f x)` (`LinearPMap.IsEquivariant.of_map_apply`). -/
def IsEquivariant (f : E →ₗ.[R] F) (π : ContRepresentation R G E) (ρ : ContRepresentation R G F) :
    Prop :=
  ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph

variable {f : E →ₗ.[R] F} {π : ContRepresentation R G E} {ρ : ContRepresentation R G F}

/-- An operator is equivariant exactly when every `π g × ρ g` maps its graph into itself. -/
theorem isEquivariant_iff :
    f.IsEquivariant π ρ ↔ ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph :=
  Iff.rfl

/-- The domain of an equivariant operator is invariant. -/
theorem IsEquivariant.apply_mem_domain (hf : f.IsEquivariant π ρ) (g : G) (x : f.domain) :
    π g x ∈ f.domain :=
  mem_domain_of_mem_graph (hf g _ _ (f.mem_graph x))

/-- **Equivariance**: `f (π g x) = ρ g (f x)` on the domain of `f`. -/
theorem IsEquivariant.map_apply (hf : f.IsEquivariant π ρ) (g : G) (x : f.domain) :
    f ⟨π g x, hf.apply_mem_domain g x⟩ = ρ g (f x) :=
  ((image_iff (hf.apply_mem_domain g x)).2 (hf g _ _ (f.mem_graph x))).symm

/-- An operator whose domain is invariant under `π` and which satisfies `f (π g x) = ρ g (f x)` is
equivariant. -/
theorem IsEquivariant.of_map_apply (hdom : ∀ g (x : f.domain), π g x ∈ f.domain)
    (happ : ∀ g (x : f.domain), f ⟨π g x, hdom g x⟩ = ρ g (f x)) : f.IsEquivariant π ρ :=
  fun g _ _ h ↦ by
    obtain ⟨x, rfl, rfl⟩ := (f.mem_graph_iff).1 h
    rw [← happ g x]
    exact f.mem_graph ⟨π g x, hdom g x⟩

/-- The kernel of an equivariant operator is invariant. -/
theorem IsEquivariant.apply_mem_ker (hf : f.IsEquivariant π ρ) (g : G) {x : E} (hx : x ∈ f.ker) :
    π g x ∈ f.ker := by
  obtain ⟨y, rfl, hy⟩ := mem_ker_iff.1 hx
  refine mem_ker_iff.2 ⟨⟨π g y, hf.apply_mem_domain g y⟩, rfl, ?_⟩
  rw [hf.map_apply, hy]
  exact _root_.map_zero (ρ g)

end IsEquivariant

/-! ### The graph space of an equivariant operator -/

variable {𝕜 G E F : Type*} [NontriviallyNormedField 𝕜] [Monoid G] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E →ₗ.[𝕜] F)
  (π : ContRepresentation 𝕜 G E) (ρ : ContRepresentation 𝕜 G F)

variable {f π ρ} in
/-- The direct sum `π ⊕ ρ` preserves the graph space of an equivariant operator `f`. -/
theorem withLpProd_apply_mem_graphSpace (hf : f.IsEquivariant π ρ) (g : G)
    {z : WithLp 2 (E × F)} (hz : z ∈ f.graphSpace) : π.withLpProd 2 ρ g z ∈ f.graphSpace := by
  rw [withLpProd_apply, toLp_mem_graphSpace_iff]
  exact hf g _ _ ((f.mem_graphSpace_iff).1 hz)

/-- The representation of `G` on the graph space of an operator `f` commuting with `π` and `ρ`: the
restriction of the direct sum `π ⊕ ρ` to the graph space. On the domain of `f` it acts as `π`
(`LinearPMap.graphSpaceRepresentation_toGraphSpace`). -/
def graphSpaceRepresentation (hf : f.IsEquivariant π ρ) :
    ContRepresentation 𝕜 G f.graphSpace :=
  (π.withLpProd 2 ρ).subrepresentation f.graphSpace fun g _ hz ↦
    withLpProd_apply_mem_graphSpace hf g hz

variable {f π ρ} (hf : f.IsEquivariant π ρ)

@[simp]
theorem coe_graphSpaceRepresentation_apply (g : G) (z : f.graphSpace) :
    (f.graphSpaceRepresentation π ρ hf g z : WithLp 2 (E × F)) =
      WithLp.toLp 2 (π g (z : WithLp 2 (E × F)).fst, ρ g (z : WithLp 2 (E × F)).snd) :=
  (coe_subrepresentation_apply g z).trans (withLpProd_apply g _)

/-- The representation on the graph space acts on the domain of `f` as `π`. -/
@[simp]
theorem graphSpaceRepresentation_toGraphSpace (g : G) (x : f.domain) :
    f.graphSpaceRepresentation π ρ hf g (f.toGraphSpace x) =
      f.toGraphSpace ⟨π g x, hf.apply_mem_domain g x⟩ := by
  ext1
  simp [hf.map_apply]

/-- **The graph space representation is unitary** when `π` and `ρ` are. -/
theorem isUnitary_graphSpaceRepresentation {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {f : E →ₗ.[𝕜] F}
    {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (hf : f.IsEquivariant π ρ)
    (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) : (f.graphSpaceRepresentation π ρ hf).IsUnitary :=
  (hπ.withLpProd hρ).subrepresentation _

/-- **The graph space representation is strongly continuous** when `π` and `ρ` are. -/
theorem continuous_graphSpaceRepresentation_apply [TopologicalSpace G]
    (hπ : ∀ v, Continuous fun g ↦ π g v) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    (z : f.graphSpace) : Continuous fun g ↦ f.graphSpaceRepresentation π ρ hf g z :=
  continuous_subrepresentation_apply (continuous_withLpProd_apply hπ hρ) z

/-! ### The operator as an intertwining map -/

/-- The inclusion `(x, f x) ↦ x` of the graph space into `E`, as an intertwining map into `π`. -/
def graphFstIntertwiningMap : f.graphSpaceRepresentation π ρ hf →ⁱL π where
  toContinuousLinearMap := f.graphFst
  isIntertwining' g := by
    ext z
    simp

/-- The operator `f`, as the bounded map `(x, f x) ↦ f x` on its graph space, is an intertwining
map into `ρ`. -/
def graphSndIntertwiningMap : f.graphSpaceRepresentation π ρ hf →ⁱL ρ where
  toContinuousLinearMap := f.graphSnd
  isIntertwining' g := by
    ext z
    simp

@[simp]
theorem toContinuousLinearMap_graphFstIntertwiningMap :
    (graphFstIntertwiningMap hf).toContinuousLinearMap = f.graphFst :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_graphSndIntertwiningMap :
    (graphSndIntertwiningMap hf).toContinuousLinearMap = f.graphSnd :=
  (rfl)

@[simp]
theorem graphFstIntertwiningMap_apply (z : f.graphSpace) :
    graphFstIntertwiningMap hf z = (z : WithLp 2 (E × F)).fst :=
  f.graphFst_apply z

@[simp]
theorem graphSndIntertwiningMap_apply (z : f.graphSpace) :
    graphSndIntertwiningMap hf z = (z : WithLp 2 (E × F)).snd :=
  f.graphSnd_apply z

/-- **The kernel of `f` as a representation.** The kernel representation of the intertwining map
`LinearPMap.graphSndIntertwiningMap` is equivalent to the restriction of `π` to the kernel of `f`,
through the first projection, which is isometric (`LinearPMap.kerGraphSndEquiv`). -/
noncomputable def kerRepresentationGraphSndEquiv :
    (graphSndIntertwiningMap hf).kerRepresentation.Equiv
      (π.subrepresentation f.ker fun g _ hx ↦ hf.apply_mem_ker g hx) :=
  .mk ((LinearIsometryEquiv.ofEq _ _ (by rw [toContinuousLinearMap_graphSndIntertwiningMap])).trans
    f.kerGraphSndEquiv).toContinuousLinearEquiv fun g ↦ by
    ext z
    simp

@[simp]
theorem coe_kerRepresentationGraphSndEquiv_apply
    (z : (graphSndIntertwiningMap hf).toContinuousLinearMap.ker) :
    (kerRepresentationGraphSndEquiv hf z : E) = f.graphFst z := by
  simp [kerRepresentationGraphSndEquiv]

end LinearPMap
