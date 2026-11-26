/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The graph space of a partial linear map

Let `f : E →ₗ.[𝕜] F` be a partial linear map between normed spaces. Its **graph space**
`f.graphSpace` is the graph `{(x, f x) | x ∈ dom f}`, regarded as a subspace of the `L²` product
`WithLp 2 (E × F)`, which is the Hilbert direct sum when `E` and `F` are inner product spaces. The
graph map `x ↦ (x, f x)` identifies the domain of `f` with it (`LinearPMap.toGraphSpace`), and
transports the graph norm `(‖x‖² + ‖f x‖²)^(1/2)` (`LinearPMap.norm_toGraphSpace_sq`). When `E`
and `F` are inner product spaces, this is the norm of the graph inner product
(`LinearPMap.inner_toGraphSpace`, in `TauCeti.Analysis.InnerProductSpace.LinearPMap.GraphSpace`).
The graph norm of `x` is at least `‖x‖` and `‖f x‖` and at most `‖x‖ + ‖f x‖`; convergence in it is
convergence of the vectors together with their images (`LinearPMap.tendsto_toGraphSpace_iff`).
When `E` and `F` are complete, `f` is closed exactly when the graph space is complete
(`LinearPMap.isClosed_iff_completeSpace_graphSpace`): the domain of a closed operator with its
graph norm is a Banach space, a Hilbert space when `E` and `F` are, and `f` becomes a bounded
operator on it (`LinearPMap.graphSnd`), of norm at most one.

This is how an unbounded operator, such as an elliptic differential operator on `L²` with its
Sobolev domain, is made into a bounded operator between fixed Hilbert spaces, to which the theory
of bounded Fredholm operators applies. The bounded operator has the same range as `f`
(`LinearPMap.range_graphSnd`), and its kernel is isometric to the kernel of `f`
(`LinearPMap.kerGraphSndEquiv`), since the graph norm of a vector of the kernel is its norm in `E`.

## Main declarations

* `LinearPMap.graphSpace`: the graph of `f` in `WithLp 2 (E × F)`.
* `LinearPMap.toGraphSpace`: the linear equivalence `x ↦ (x, f x)` from the domain of `f`.
* `LinearPMap.norm_toGraphSpace_sq`: the graph norm.
* `LinearPMap.norm_le_norm_toGraphSpace`, `LinearPMap.norm_apply_le_norm_toGraphSpace`,
  `LinearPMap.norm_toGraphSpace_le_norm_add_norm`: comparison of the graph norm with `‖x‖` and
  `‖f x‖`.
* `LinearPMap.norm_toGraphSpace_le_sqrt_one_add_sq_mul_norm`: if `‖f x‖ ≤ C ‖x‖`, the graph norm
  of `x` is at most `√(1 + C²) ‖x‖`; `ContinuousLinearMap.norm_toGraphSpace_toPMap_le` is the case
  of the restriction of a continuous linear map to a submodule.
* `LinearPMap.tendsto_toGraphSpace_iff`: convergence in the graph norm.
* `LinearPMap.graphFst` and `LinearPMap.graphSnd`: the inclusion of the graph space into `E` and
  the operator `f` itself, as continuous linear maps of norm at most one.
* `LinearPMap.isClosed_graphSpace_iff`: the graph space is closed exactly when `f` is.
* `LinearPMap.IsClosed.completeSpace_graphSpace`: the graph space of a closed operator between
  complete spaces is complete; between Hilbert spaces it is a Hilbert space.
* `LinearPMap.isClosed_iff_completeSpace_graphSpace`: between Banach spaces, `f` is closed exactly
  when its graph space is complete.
* `LinearPMap.kerGraphSndEquiv`: the kernel of `f.graphSnd` is isometric to the kernel of `f`.

## References

* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Graduate Texts in
  Mathematics 265, Springer (2012), §1.1 (the graph scalar product of a closed operator).
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Section III.5.2.
-/

public section

open Filter Topology

namespace LinearPMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The **graph space** of a partial linear map `f`: its graph `{(x, f x) | x ∈ dom f}` as a
subspace of the `L²` product `WithLp 2 (E × F)`. When `E` and `F` are inner product spaces this is
the Hilbert direct sum, and the graph space carries the graph inner product `⟪x, y⟫ + ⟪f x, f y⟫`
(`LinearPMap.inner_toGraphSpace`). -/
def graphSpace (f : E →ₗ.[𝕜] F) : Submodule 𝕜 (WithLp 2 (E × F)) :=
  f.graph.comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

variable (f : E →ₗ.[𝕜] F)

/-- A vector of `WithLp 2 (E × F)` lies in the graph space exactly when its pair of coordinates
lies in the graph. -/
@[simp]
theorem mem_graphSpace_iff {z : WithLp 2 (E × F)} :
    z ∈ f.graphSpace ↔ (z.fst, z.snd) ∈ f.graph :=
  Iff.rfl

/-- As a set, the graph space is the preimage of the graph under `WithLp.ofLp`. -/
theorem coe_graphSpace : (f.graphSpace : Set (WithLp 2 (E × F))) = WithLp.ofLp ⁻¹' f.graph :=
  Set.ext fun _ ↦ f.mem_graphSpace_iff

theorem toLp_mem_graphSpace_iff {x : E} {y : F} :
    WithLp.toLp 2 (x, y) ∈ f.graphSpace ↔ (x, y) ∈ f.graph :=
  Iff.rfl

/-- The pair `(x, f x)` lies in the graph space. -/
theorem toLp_mem_graphSpace (x : f.domain) : WithLp.toLp 2 ((x : E), f x) ∈ f.graphSpace :=
  f.mem_graph x

/-- The first coordinate of a vector of the graph space lies in the domain. -/
theorem fst_mem_domain_of_mem_graphSpace {z : WithLp 2 (E × F)} (hz : z ∈ f.graphSpace) :
    z.fst ∈ f.domain :=
  mem_domain_of_mem_graph hz

/-- The second coordinate of a vector of the graph space is the value of `f` at the first. -/
theorem apply_fst_eq_snd_of_mem_graphSpace {z : WithLp 2 (E × F)} (hz : z ∈ f.graphSpace) :
    f ⟨z.fst, f.fst_mem_domain_of_mem_graphSpace hz⟩ = z.snd :=
  ((image_iff (f.fst_mem_domain_of_mem_graphSpace hz)).2 hz).symm

/-- The graph map `x ↦ (x, f x)`, a linear equivalence from the domain of `f` onto its graph
space. Its inverse is the first projection. -/
def toGraphSpace : f.domain ≃ₗ[𝕜] f.graphSpace where
  toFun x := ⟨WithLp.toLp 2 ((x : E), f x), f.toLp_mem_graphSpace x⟩
  invFun z := ⟨(z : WithLp 2 (E × F)).fst, f.fst_mem_domain_of_mem_graphSpace z.property⟩
  map_add' x y := Subtype.ext <| by simp [← WithLp.toLp_add, LinearPMap.map_add]
  map_smul' c x := Subtype.ext <| by simp [← WithLp.toLp_smul, LinearPMap.map_smul]
  left_inv x := rfl
  right_inv z := Subtype.ext <| by
    simp [f.apply_fst_eq_snd_of_mem_graphSpace z.property, WithLp.ext_iff, Prod.ext_iff]

@[simp]
theorem coe_toGraphSpace (x : f.domain) :
    (f.toGraphSpace x : WithLp 2 (E × F)) = WithLp.toLp 2 ((x : E), f x) :=
  (rfl)

@[simp]
theorem coe_toGraphSpace_symm (z : f.graphSpace) :
    (f.toGraphSpace.symm z : E) = (z : WithLp 2 (E × F)).fst :=
  (rfl)

@[simp]
theorem apply_toGraphSpace_symm (z : f.graphSpace) :
    f (f.toGraphSpace.symm z) = (z : WithLp 2 (E × F)).snd :=
  f.apply_fst_eq_snd_of_mem_graphSpace z.property

/-- **The graph norm.** -/
theorem norm_toGraphSpace_sq (x : f.domain) :
    ‖f.toGraphSpace x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖f x‖ ^ 2 := by
  simp [← Submodule.norm_coe, WithLp.prod_norm_sq_eq_of_L2]

/-- The graph norm of a vector of the graph space, in terms of its coordinates. -/
theorem norm_graphSpace_sq (z : f.graphSpace) :
    ‖z‖ ^ 2 = ‖(z : WithLp 2 (E × F)).fst‖ ^ 2 + ‖(z : WithLp 2 (E × F)).snd‖ ^ 2 := by
  rw [← Submodule.norm_coe, WithLp.prod_norm_sq_eq_of_L2]

/-! ### The projections -/

/-- The inclusion of the graph space into `E`, sending `(x, f x)` to `x`. -/
def graphFst : f.graphSpace →L[𝕜] E :=
  WithLp.fstL 2 𝕜 E F ∘L f.graphSpace.subtypeL

/-- The operator `f` as a continuous linear map on its graph space, sending `(x, f x)` to `f x`. -/
def graphSnd : f.graphSpace →L[𝕜] F :=
  WithLp.sndL 2 𝕜 E F ∘L f.graphSpace.subtypeL

@[simp]
theorem graphFst_apply (z : f.graphSpace) : f.graphFst z = (z : WithLp 2 (E × F)).fst :=
  (rfl)

@[simp]
theorem graphSnd_apply (z : f.graphSpace) : f.graphSnd z = (z : WithLp 2 (E × F)).snd :=
  (rfl)

theorem graphFst_toGraphSpace (x : f.domain) : f.graphFst (f.toGraphSpace x) = x :=
  (rfl)

theorem graphSnd_toGraphSpace (x : f.domain) : f.graphSnd (f.toGraphSpace x) = f x :=
  (rfl)

/-- On the graph space, `f.graphSnd` is `f` read through the graph map. -/
theorem graphSnd_apply_eq_apply_toGraphSpace_symm (z : f.graphSpace) :
    f.graphSnd z = f (f.toGraphSpace.symm z) :=
  (f.apply_toGraphSpace_symm z).symm

theorem norm_graphFst_apply_le (z : f.graphSpace) : ‖f.graphFst z‖ ≤ ‖z‖ :=
  (WithLp.norm_fst_le (p := 2) (α := E) (β := F) z).trans_eq (Submodule.norm_coe z)

theorem norm_graphSnd_apply_le (z : f.graphSpace) : ‖f.graphSnd z‖ ≤ ‖z‖ :=
  (WithLp.norm_snd_le (p := 2) (α := E) (β := F) z).trans_eq (Submodule.norm_coe z)

theorem norm_graphFst_le : ‖f.graphFst‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
    simpa only [one_mul] using f.norm_graphFst_apply_le z

theorem norm_graphSnd_le : ‖f.graphSnd‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
    simpa only [one_mul] using f.norm_graphSnd_apply_le z

/-! ### Graph norm estimates -/

/-- The norm of a vector of the domain is at most its graph norm. -/
theorem norm_le_norm_toGraphSpace (x : f.domain) : ‖(x : E)‖ ≤ ‖f.toGraphSpace x‖ :=
  f.norm_graphFst_apply_le (f.toGraphSpace x)

/-- The norm of `f x` is at most the graph norm of `x`. -/
theorem norm_apply_le_norm_toGraphSpace (x : f.domain) : ‖f x‖ ≤ ‖f.toGraphSpace x‖ :=
  f.norm_graphSnd_apply_le (f.toGraphSpace x)

/-- The graph norm of `x` is at most `‖x‖ + ‖f x‖`. -/
theorem norm_toGraphSpace_le_norm_add_norm (x : f.domain) :
    ‖f.toGraphSpace x‖ ≤ ‖(x : E)‖ + ‖f x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), norm_toGraphSpace_sq]
  nlinarith [norm_nonneg (x : E), norm_nonneg (f x)]

variable {f} in
/-- If `‖f x‖ ≤ C ‖x‖`, then the graph norm of `x` is at most `√(1 + C²) ‖x‖`. When this holds on
the whole domain, the graph norm is equivalent to the norm of `E` there. -/
theorem norm_toGraphSpace_le_sqrt_one_add_sq_mul_norm {C : ℝ} {x : f.domain}
    (h : ‖f x‖ ≤ C * ‖(x : E)‖) : ‖f.toGraphSpace x‖ ≤ √(1 + C ^ 2) * ‖(x : E)‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), norm_toGraphSpace_sq, mul_pow,
    Real.sq_sqrt (by positivity)]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2]

variable {f} in
/-- An extension `g` of `f` has the same graph norm as `f` on the domain of `f`. -/
theorem norm_toGraphSpace_eq_of_le {g : E →ₗ.[𝕜] F} (h : f ≤ g) {x : f.domain} {y : g.domain}
    (hxy : (x : E) = y) : ‖g.toGraphSpace y‖ = ‖f.toGraphSpace x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_toGraphSpace_sq, norm_toGraphSpace_sq,
    ← hxy, ← h.2 hxy]

variable {f} in
/-- **Convergence in the graph norm.** Domain vectors `u i` converge to `x` in the graph norm
exactly when `u i → x` and `f (u i) → f x`. -/
theorem tendsto_toGraphSpace_iff {ι : Type*} {l : Filter ι} {u : ι → f.domain} {x : f.domain} :
    Tendsto (fun i ↦ f.toGraphSpace (u i)) l (𝓝 (f.toGraphSpace x)) ↔
      Tendsto (fun i ↦ (u i : E)) l (𝓝 (x : E)) ∧ Tendsto (fun i ↦ f (u i)) l (𝓝 (f x)) := by
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff,
    (WithLp.homeomorphProd 2 E F).isInducing.tendsto_nhds_iff, Prod.tendsto_iff]
  simp only [Function.comp_def, ← Homeomorph.coe_toEquiv, WithLp.toEquiv_homeomorphProd,
    WithLp.equiv_apply, coe_toGraphSpace]

/-- A vector of the graph space is determined by its first coordinate. -/
theorem graphFst_injective : Function.Injective f.graphFst := fun _ _ h ↦
  f.toGraphSpace.symm.injective (Subtype.ext h)

@[simp]
theorem range_graphFst : f.graphFst.range = f.domain := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨f.toGraphSpace ⟨x, hx⟩, rfl⟩⟩
  rintro ⟨z, rfl⟩
  exact f.fst_mem_domain_of_mem_graphSpace z.property

/-- The operator `f` and its bounded realization on the graph space have the same range. -/
@[simp]
theorem range_graphSnd : f.graphSnd.range = LinearMap.range f.toFun := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨f.toGraphSpace.symm z, (f.graphSnd_apply_eq_apply_toGraphSpace_symm z).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨f.toGraphSpace x, rfl⟩

/-- A vector of the graph space lies in the kernel of `f.graphSnd` exactly when its first
coordinate lies in the kernel of `f`. -/
theorem graphSnd_apply_eq_zero_iff (z : f.graphSpace) :
    f.graphSnd z = 0 ↔ f.graphFst z ∈ f.ker := by
  rw [graphSnd_apply_eq_apply_toGraphSpace_symm, ← coe_mem_ker_iff, coe_toGraphSpace_symm,
    graphFst_apply]

/-- The first projection maps the kernel of `f.graphSnd` onto the kernel of `f`. -/
theorem map_ker_graphSnd : f.graphSnd.ker.map (f.graphFst : f.graphSpace →ₗ[𝕜] E) =
    f.ker := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨z, hz, rfl⟩
    exact (f.graphSnd_apply_eq_zero_iff z).1 hz
  · obtain ⟨y, rfl, -⟩ := mem_ker_iff.1 hx
    exact ⟨f.toGraphSpace y, (f.graphSnd_apply_eq_zero_iff _).2 hx, rfl⟩

/-- On the kernel of `f.graphSnd` the graph norm is the norm of the first coordinate. -/
theorem norm_eq_norm_graphFst_of_graphSnd_eq_zero {z : f.graphSpace} (hz : f.graphSnd z = 0) :
    ‖z‖ = ‖f.graphFst z‖ := by
  have h := f.norm_graphSpace_sq z
  rw [graphSnd_apply] at hz
  rw [hz, norm_zero, zero_pow two_ne_zero, add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **The kernel of the bounded realization.** The first projection is a linear isometric
equivalence from the kernel of `f.graphSnd`, with the graph norm, onto the kernel of `f`, with the
norm of `E`. -/
noncomputable def kerGraphSndEquiv : f.graphSnd.ker ≃ₗᵢ[𝕜] f.ker where
  toLinearEquiv :=
    (f.graphSnd.ker.equivMapOfInjective (f.graphFst : f.graphSpace →ₗ[𝕜] E)
      f.graphFst_injective).trans (LinearEquiv.ofEq _ _ f.map_ker_graphSnd)
  norm_map' z := (f.norm_eq_norm_graphFst_of_graphSnd_eq_zero z.property).symm

@[simp]
theorem coe_kerGraphSndEquiv (z : f.graphSnd.ker) :
    (f.kerGraphSndEquiv z : E) = f.graphFst z :=
  (rfl)

/-! ### Closedness and completeness -/

/-- The graph space is closed in `WithLp 2 (E × F)` exactly when `f` is a closed operator. -/
theorem isClosed_graphSpace_iff :
    _root_.IsClosed (f.graphSpace : Set (WithLp 2 (E × F))) ↔ f.IsClosed := by
  rw [coe_graphSpace, LinearPMap.IsClosed]
  exact ⟨fun h ↦ by
    simpa [Set.preimage_preimage] using h.preimage (WithLp.prod_continuous_toLp 2 E F),
    fun h ↦ h.preimage (WithLp.prod_continuous_ofLp 2 E F)⟩

/-- **The graph space of a closed operator is complete.** For a closed operator between Banach
spaces the graph space is a Banach space, and a Hilbert space when `E` and `F` are. -/
theorem IsClosed.completeSpace_graphSpace [CompleteSpace E] [CompleteSpace F] {f : E →ₗ.[𝕜] F}
    (hf : f.IsClosed) : CompleteSpace f.graphSpace :=
  ((f.isClosed_graphSpace_iff.2 hf)).completeSpace_coe

/-- A partial linear map whose domain is complete for the graph norm is closed. -/
theorem isClosed_of_completeSpace_graphSpace (h : CompleteSpace f.graphSpace) : f.IsClosed :=
  f.isClosed_graphSpace_iff.1 (completeSpace_coe_iff_isComplete.1 h).isClosed

/-- **Closed operators are those with a complete graph space.** A partial linear map between
Banach spaces is closed exactly when its domain is complete for the graph norm. -/
theorem isClosed_iff_completeSpace_graphSpace [CompleteSpace E] [CompleteSpace F] :
    f.IsClosed ↔ CompleteSpace f.graphSpace :=
  ⟨IsClosed.completeSpace_graphSpace, f.isClosed_of_completeSpace_graphSpace⟩

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Graph norm of a bounded operator.** The restriction of a continuous linear map `T` to a
submodule `p` has graph norm at most `√(1 + ‖T‖²) ‖x‖`; together with
`LinearPMap.norm_le_norm_toGraphSpace` this makes it equivalent to the norm of `E` on `p`. -/
theorem norm_toGraphSpace_toPMap_le (T : E →L[𝕜] F) {p : Submodule 𝕜 E}
    (x : (T.toLinearMap.toPMap p).domain) :
    ‖(T.toLinearMap.toPMap p).toGraphSpace x‖ ≤ √(1 + ‖T‖ ^ 2) * ‖(x : E)‖ :=
  LinearPMap.norm_toGraphSpace_le_sqrt_one_add_sq_mul_norm
    ((congrArg norm ((T : E →ₗ[𝕜] F).toPMap_apply p x)).trans_le (T.le_opNorm x))

end ContinuousLinearMap
