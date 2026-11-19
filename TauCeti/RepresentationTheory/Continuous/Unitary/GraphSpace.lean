/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.GraphSpace
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.RepresentationTheory.Continuous.StronglyContinuous
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# The graph space of an equivariant closed operator

Let a monoid `G` act on Hilbert spaces `E` and `F` by unitary representations `π` and `ρ`, and let
`f : E →ₗ.[𝕜] F` be an unbounded operator commuting with the actions: every `π g × ρ g` maps the
graph of `f` into itself, that is, `π g` preserves the domain of `f` and `f (π g x) = ρ g (f x)`.
The graph space of `f` (`LinearPMap.graphSpace`), the domain of `f` with the graph inner product
`⟪x, y⟫ + ⟪f x, f y⟫`, then carries the representation `π g × ρ g`
(`LinearPMap.graphSpaceRepresentation`), which acts on the domain of `f` as `π` does. It is unitary
(`LinearPMap.isUnitary_graphSpaceRepresentation`) and strongly continuous when `π` and `ρ` are
(`LinearPMap.continuous_graphSpaceRepresentation_apply`). The operator `f`, as the bounded map
`f.graphSnd` on its graph space, becomes an intertwining map into `ρ`
(`LinearPMap.graphSndIntertwiningMap`), whose kernel representation is the restriction of `π` to
the kernel of `f` (`LinearPMap.kerRepresentationGraphSndEquiv`).

This turns an equivariant closed operator, such as an invariant elliptic operator between
`L²`-sections with its Sobolev domain, into an intertwining map between strongly continuous unitary
representations on fixed Hilbert spaces; when `f` is closed and `E`, `F` are complete, the graph
space is a Hilbert space (`LinearPMap.IsClosed.completeSpace_graphSpace`). When this intertwining
map is Fredholm, its equivariant index `ContIntertwiningMap.equivariantIndex` is defined. The same
representations serve every bounded equivariant operator on the graph space, such as an equivariant
approximation of `f` in the norm of bounded operators from the graph space to `F`.

The representation of `G` on the Hilbert direct sum `WithLp 2 (E × F)` used here is the direct sum
`ContRepresentation.withLpProd`, defined for every `L^p` product.

## Main declarations

* `ContRepresentation.withLpProd`: the direct sum `π ⊕ ρ` on `WithLp p (E × F)`, strongly
  continuous when `π` and `ρ` are (`ContRepresentation.continuous_withLpProd_apply`) and unitary
  for `p = 2` when `π` and `ρ` are (`ContRepresentation.IsUnitary.withLpProd`).
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

open scoped ENNReal InnerProductSpace ContRepresentation

/-! ### Direct sums of representations -/

namespace ContRepresentation

section WithLpProd

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {R G E F : Type*} [Ring R] [Monoid G]
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module R F]

/-- The **direct sum** `π ⊕ ρ` of two continuous representations, acting componentwise on the
`L^p` product `WithLp p (E × F)`. For `p = 2` it is the Hilbert direct sum, unitary when `π` and
`ρ` are (`ContRepresentation.IsUnitary.withLpProd`). -/
def withLpProd (π : ContRepresentation R G E) (ρ : ContRepresentation R G F) :
    ContRepresentation R G (WithLp p (E × F)) :=
  .ofMonoidHom
    { toFun g := (π g).withLpProdMap p (ρ g)
      map_one' := ContinuousLinearMap.ext fun x ↦ by
        simp only [map_one, ContinuousLinearMap.withLpProdMap_apply, one_apply_eq_self]
        exact WithLp.toLp_ofLp p x
      map_mul' g h := by
        ext x
        simp }

variable {p} {π : ContRepresentation R G E} {ρ : ContRepresentation R G F}

@[simp]
theorem withLpProd_apply (g : G) (x : WithLp p (E × F)) :
    π.withLpProd p ρ g x = WithLp.toLp p (π g x.fst, ρ g x.snd) :=
  ContinuousLinearMap.withLpProdMap_apply (π g) (ρ g) x

/-- The direct sum of two strongly continuous representations is strongly continuous. -/
theorem continuous_withLpProd_apply [TopologicalSpace G] (hπ : ∀ v, Continuous fun g ↦ π g v)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) (x : WithLp p (E × F)) :
    Continuous fun g ↦ π.withLpProd p ρ g x := by
  simp only [withLpProd_apply]
  exact (WithLp.prod_continuous_toLp p E F).comp ((hπ _).prodMk (hρ _))

end WithLpProd

/-- The Hilbert direct sum of two unitary representations is unitary. -/
theorem IsUnitary.withLpProd {𝕜 G E F : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (hπ : π.IsUnitary)
    (hρ : ρ.IsUnitary) : (π.withLpProd 2 ρ).IsUnitary :=
  (isUnitary_iff_norm_map _).2 fun g x ↦ by
    simp only [withLpProd_apply, WithLp.prod_norm_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
      hπ.norm_map, hρ.norm_map]

end ContRepresentation

/-! ### The graph space of an equivariant operator -/

namespace LinearPMap

open ContRepresentation

variable {𝕜 G E F : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (f : E →ₗ.[𝕜] F)
  (π : ContRepresentation 𝕜 G E) (ρ : ContRepresentation 𝕜 G F)

variable {f π ρ} in
/-- If every `π g × ρ g` maps the graph of `f` into itself, the direct sum `π ⊕ ρ` preserves the
graph space of `f`. -/
theorem withLpProd_apply_mem_graphSpace
    (hf : ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph) (g : G)
    {z : WithLp 2 (E × F)} (hz : z ∈ f.graphSpace) : π.withLpProd 2 ρ g z ∈ f.graphSpace := by
  rw [withLpProd_apply, toLp_mem_graphSpace_iff]
  exact hf g _ _ ((f.mem_graphSpace_iff).1 hz)

/-- The representation of `G` on the graph space of an operator `f` commuting with `π` and `ρ`, in
the sense that every `π g × ρ g` maps the graph of `f` into itself: the restriction of the Hilbert
direct sum `π ⊕ ρ` to the graph space. On the domain of `f` it acts as `π`
(`LinearPMap.graphSpaceRepresentation_toGraphSpace`). -/
def graphSpaceRepresentation (hf : ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph) :
    ContRepresentation 𝕜 G f.graphSpace :=
  (π.withLpProd 2 ρ).subrepresentation f.graphSpace fun g _ hz ↦
    withLpProd_apply_mem_graphSpace hf g hz

variable {f π ρ} (hf : ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph)

@[simp]
theorem coe_graphSpaceRepresentation_apply (g : G) (z : f.graphSpace) :
    (f.graphSpaceRepresentation π ρ hf g z : WithLp 2 (E × F)) =
      WithLp.toLp 2 (π g (z : WithLp 2 (E × F)).fst, ρ g (z : WithLp 2 (E × F)).snd) :=
  (coe_subrepresentation_apply g z).trans (withLpProd_apply g _)

/-- The domain of an equivariant operator is invariant. -/
theorem apply_mem_domain (hf : ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph) (g : G)
    (x : f.domain) : π g x ∈ f.domain :=
  mem_domain_of_mem_graph (hf g _ _ (f.mem_graph x))

/-- **Equivariance**: `f (π g x) = ρ g (f x)` on the domain of `f`. -/
theorem apply_apply_mem_domain (hf : ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph)
    (g : G) (x : f.domain) :
    f ⟨π g x, apply_mem_domain hf g x⟩ = ρ g (f x) :=
  ((image_iff (apply_mem_domain hf g x)).2 (hf g _ _ (f.mem_graph x))).symm

/-- The representation on the graph space acts on the domain of `f` as `π`. -/
theorem graphSpaceRepresentation_toGraphSpace (g : G) (x : f.domain) :
    f.graphSpaceRepresentation π ρ hf g (f.toGraphSpace x) =
      f.toGraphSpace ⟨π g x, apply_mem_domain hf g x⟩ := by
  ext1
  rw [coe_graphSpaceRepresentation_apply, coe_toGraphSpace, coe_toGraphSpace,
    apply_apply_mem_domain hf, WithLp.toLp_fst, WithLp.toLp_snd]

/-- **The graph space representation is unitary** when `π` and `ρ` are. -/
theorem isUnitary_graphSpaceRepresentation (hπ : π.IsUnitary) (hρ : ρ.IsUnitary) :
    (f.graphSpaceRepresentation π ρ hf).IsUnitary :=
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

/-- The kernel of an equivariant operator is invariant. -/
theorem apply_mem_ker (hf : ∀ g x y, (x, y) ∈ f.graph → (π g x, ρ g y) ∈ f.graph) (g : G)
    {x : E} (hx : x ∈ f.ker) : π g x ∈ f.ker := by
  obtain ⟨y, rfl, hy⟩ := mem_ker_iff.1 hx
  refine mem_ker_iff.2 ⟨⟨π g y, apply_mem_domain hf g y⟩, rfl, ?_⟩
  rw [apply_apply_mem_domain hf, hy]
  exact _root_.map_zero (ρ g)

/-- The first projection on the kernel of `LinearPMap.graphSndIntertwiningMap`, a linear isometric
equivalence onto the kernel of `f` (`LinearPMap.kerGraphSndEquiv`). -/
private noncomputable def kerGraphSndIntertwiningMapEquiv :
    (graphSndIntertwiningMap hf).toContinuousLinearMap.ker ≃ₗᵢ[𝕜] f.ker :=
  (LinearIsometryEquiv.ofEq _ _ (by rw [toContinuousLinearMap_graphSndIntertwiningMap])).trans
    f.kerGraphSndEquiv

private theorem coe_kerGraphSndIntertwiningMapEquiv
    (z : (graphSndIntertwiningMap hf).toContinuousLinearMap.ker) :
    (kerGraphSndIntertwiningMapEquiv hf z : E) = f.graphFst z := by
  rw [kerGraphSndIntertwiningMapEquiv, LinearIsometryEquiv.trans_apply, coe_kerGraphSndEquiv,
    LinearIsometryEquiv.coe_ofEq_apply]

/-- **The kernel of `f` as a representation.** The kernel representation of the intertwining map
`LinearPMap.graphSndIntertwiningMap` is equivalent to the restriction of `π` to the kernel of `f`,
through the first projection, which is isometric (`LinearPMap.kerGraphSndEquiv`). -/
noncomputable def kerRepresentationGraphSndEquiv :
    (graphSndIntertwiningMap hf).kerRepresentation.Equiv
      (π.subrepresentation f.ker fun g _ hx ↦ apply_mem_ker hf g hx) :=
  .mk (kerGraphSndIntertwiningMapEquiv hf).toContinuousLinearEquiv fun g ↦ by
    ext z
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      coe_kerGraphSndIntertwiningMapEquiv, coe_subrepresentation_apply,
      coe_kerGraphSndIntertwiningMapEquiv, graphFst_apply, graphFst_apply,
      ContIntertwiningMap.coe_kerRepresentation_apply, coe_graphSpaceRepresentation_apply,
      WithLp.toLp_fst]

@[simp]
theorem coe_kerRepresentationGraphSndEquiv_apply
    (z : (graphSndIntertwiningMap hf).toContinuousLinearMap.ker) :
    (kerRepresentationGraphSndEquiv hf z : E) = f.graphFst z :=
  coe_kerGraphSndIntertwiningMapEquiv hf z

end LinearPMap
