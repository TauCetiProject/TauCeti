/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.AdjointComp
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint
public import TauCeti.Analysis.Normed.Operator.LinearPMap.ProdLp
public import TauCeti.LinearAlgebra.LinearPMap.DomainPow
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# The Hermitian dilation of an unbounded operator

A partially defined operator `T : E →ₗ.[𝕜] F` between Hilbert spaces determines the partially
defined operator on the Hilbert direct sum `WithLp 2 (E × F)` with block matrix

`D_T = [[0, T†], [T, 0]]`, `D_T (x, y) = (T† y, T x)`,

on the domain `dom T × dom T†`. When `T` is closed and densely defined, `D_T` is self-adjoint
(`LinearPMap.isSelfAdjoint_hermitianDilation`). This is how a closed operator between two
different spaces, such as an elliptic operator `P : H¹(E₀) → L²(E₁)` between sections of two
bundles, is turned into a self-adjoint operator on one space: the graded operator
`[[0, P†], [P, 0]]` on `L²(E₀ ⊕ E₁)`. The two diagonal blocks of its square are the
nonnegative self-adjoint operators `T†T` and `TT†` (`LinearPMap.adjointComp`), and its kernel is
`ker T × ker T†`. Since `ker T† = (range T)ᗮ` (`LinearPMap.orthogonal_range_eq_ker_adjoint`), the
kernel and the cokernel of `T` appear as the zero modes of `D_T` in the two summands.

For bounded operators between finite-dimensional spaces the same block matrix is
`LinearMap.hermitianDilation`. Here `D_T` is the direct sum `T ⊕ T†` of
`LinearPMap.withLpProdMap` followed by the swap of the two summands.

## Main declarations

* `LinearPMap.hermitianDilation`: the operator `(x, y) ↦ (T† y, T x)` on `dom T × dom T†`.
* `LinearPMap.mem_hermitianDilation_domain`: its domain is `dom T × dom T†`.
* `LinearPMap.hermitianDilation_apply_eq_swap`: `D_T` evaluates as `T ⊕ T†` followed by the swap.
* `LinearPMap.hermitianDilation_apply_toLp`: `D_T (x, y) = (T† y, T x)`.
* `LinearPMap.mem_graph_hermitianDilation_iff`: the graph of `D_T` in terms of the graphs of `T`
  and `T†`.
* `LinearPMap.norm_hermitianDilation_apply_sq`: `‖D_T (x, y)‖² = ‖T† y‖² + ‖T x‖²`.
* `LinearPMap.mem_ker_hermitianDilation`: `ker D_T = ker T × ker T†`.
* `LinearPMap.isFormalAdjoint_hermitianDilation`: `D_T` is symmetric when `T` is densely defined.
* `LinearPMap.adjoint_hermitianDilation`, `LinearPMap.isSelfAdjoint_hermitianDilation`: `D_T` is
  self-adjoint when `T` is closed and densely defined.
* `LinearPMap.mem_domainPow_two_hermitianDilation`,
  `LinearPMap.hermitianDilation_apply_hermitianDilation`: `D_T² = T†T ⊕ TT†`, with domain
  `dom (T†T) × dom (TT†)`.
* `LinearPMap.hasCore_hermitianDilation`: cores of `T` and of `T†` give a core of `D_T`.

The self-adjointness uses `T†† = T` for closed densely defined `T`
(`LinearPMap.adjoint_adjoint`).

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968), §9,
  where the operators `[[0, P*], [P, 0]]` of two elliptic operators are combined to compute the
  index of their external product.
-/

public section

noncomputable section

open scoped InnerProductSpace LinearPMap

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The *Hermitian dilation* `D_T = [[0, T†], [T, 0]]` of a partially defined operator `T`, the
operator `(x, y) ↦ (T† y, T x)` on the `L²` direct sum `WithLp 2 (E × F)`, defined on
`dom T × dom T†`: the direct sum `T ⊕ T†` followed by the swap of the two summands. -/
def hermitianDilation (T : E →ₗ.[𝕜] F) : WithLp 2 (E × F) →ₗ.[𝕜] WithLp 2 (E × F) :=
  (LinearIsometryEquiv.withLpProdComm 2 𝕜 F E).toLinearEquiv.toLinearMap.compPMap
    (T.withLpProdMap 2 T†)

variable {T : E →ₗ.[𝕜] F}

/-- The domain of the Hermitian dilation is `dom T × dom T†`. -/
@[simp]
theorem mem_hermitianDilation_domain {u : WithLp 2 (E × F)} :
    u ∈ T.hermitianDilation.domain ↔ u.fst ∈ T.domain ∧ u.snd ∈ T†.domain :=
  mem_withLpProdMap_domain

/-- The first component of a vector in the domain of the Hermitian dilation, as a vector of
`dom T`. -/
abbrev hermitianDilationFst (u : T.hermitianDilation.domain) : T.domain :=
  ⟨(u : WithLp 2 (E × F)).fst, (mem_hermitianDilation_domain.mp u.property).1⟩

/-- The second component of a vector in the domain of the Hermitian dilation, as a vector of
`dom T†`. -/
abbrev hermitianDilationSnd (u : T.hermitianDilation.domain) : T†.domain :=
  ⟨(u : WithLp 2 (E × F)).snd, (mem_hermitianDilation_domain.mp u.property).2⟩

/-- The Hermitian dilation evaluates as the direct sum `T ⊕ T†` followed by the swap of the two
summands. -/
theorem hermitianDilation_apply_eq_swap (u : (T.withLpProdMap 2 T†).domain) :
    T.hermitianDilation
        ⟨u, mem_hermitianDilation_domain.mpr (mem_withLpProdMap_domain.mp u.property)⟩ =
      WithLp.toLp 2 ((T.withLpProdMap 2 T† u).snd, (T.withLpProdMap 2 T† u).fst) := by
  -- `compPMap` evaluates by `g (f u)`, and the swap `withLpProdComm` exchanges the components.
  simp only [hermitianDilation, LinearMap.compPMap_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.withLpProdComm_apply]
  -- What is left is `⟨↑u, _⟩ = u`: `compPMap` keeps the domain, so this is subtype eta.
  rfl

/-- The first component of `D_T (x, y)` is `T† y`. -/
@[simp]
theorem fst_hermitianDilation_apply (u : T.hermitianDilation.domain) :
    (T.hermitianDilation u).fst = T† (hermitianDilationSnd u) := by
  have h := congrArg WithLp.fst (hermitianDilation_apply_eq_swap
    ⟨u, mem_withLpProdMap_domain.mpr (mem_hermitianDilation_domain (T := T) |>.mp u.property)⟩)
  rw [WithLp.toLp_fst, withLpProdMap_apply_snd] at h
  exact h

/-- The second component of `D_T (x, y)` is `T x`. -/
@[simp]
theorem snd_hermitianDilation_apply (u : T.hermitianDilation.domain) :
    (T.hermitianDilation u).snd = T (hermitianDilationFst u) := by
  have h := congrArg WithLp.snd (hermitianDilation_apply_eq_swap
    ⟨u, mem_withLpProdMap_domain.mpr (mem_hermitianDilation_domain (T := T) |>.mp u.property)⟩)
  rw [WithLp.toLp_snd, withLpProdMap_apply_fst] at h
  exact h

/-- The Hermitian dilation sends `(x, y)` to `(T† y, T x)`. -/
theorem hermitianDilation_apply (u : T.hermitianDilation.domain) :
    T.hermitianDilation u =
      WithLp.toLp 2 (T† (hermitianDilationSnd u), T (hermitianDilationFst u)) :=
  WithLp.ofLp_injective 2 (Prod.ext (fst_hermitianDilation_apply u) (snd_hermitianDilation_apply u))

/-- The Hermitian dilation on a pair `(x, y)` with `x ∈ dom T` and `y ∈ dom T†`. -/
theorem hermitianDilation_apply_toLp (x : T.domain) (y : T†.domain) :
    T.hermitianDilation ⟨WithLp.toLp 2 ((x : E), (y : F)),
      mem_hermitianDilation_domain.mpr ⟨x.property, y.property⟩⟩ =
      WithLp.toLp 2 (T† y, T x) :=
  hermitianDilation_apply _

/-- The graph norm identity `‖D_T (x, y)‖² = ‖T† y‖² + ‖T x‖²`. -/
theorem norm_hermitianDilation_apply_sq (u : T.hermitianDilation.domain) :
    ‖T.hermitianDilation u‖ ^ 2 =
      ‖T† (hermitianDilationSnd u)‖ ^ 2 + ‖T (hermitianDilationFst u)‖ ^ 2 := by
  rw [hermitianDilation_apply]
  exact WithLp.prod_norm_sq_eq_of_L2 _

/-- The graph of the Hermitian dilation: `((x, y), (a, b))` lies on it exactly when `(x, b)` lies
on the graph of `T` and `(y, a)` on the graph of `T†`. -/
theorem mem_graph_hermitianDilation_iff {z : WithLp 2 (E × F) × WithLp 2 (E × F)} :
    z ∈ T.hermitianDilation.graph ↔
      (z.1.fst, z.2.snd) ∈ T.graph ∧ (z.1.snd, z.2.fst) ∈ T†.graph := by
  refine Iff.trans ?_ (mem_graph_withLpProdMap_iff (z := (z.1, WithLp.toLp 2 (z.2.snd, z.2.fst))))
  rw [mem_graph_iff, mem_graph_iff]
  -- `D_T` is `T ⊕ T†` followed by the swap, so `D_T u = z.2` exactly when `(T ⊕ T†) u` is the
  -- swap of `z.2`. The two existentials range over the same type: `compPMap g f` is defined with
  -- `domain := f.domain`, so `T.hermitianDilation.domain` is by definition the domain
  -- `(T.withLpProdMap 2 T†).domain`, and `D_T` applies directly to its elements `u` below.
  refine exists_congr fun u ↦ and_congr_right fun _ ↦ ?_
  have hs : T.hermitianDilation u =
      WithLp.toLp 2 ((T.withLpProdMap 2 T† u).snd, (T.withLpProdMap 2 T† u).fst) :=
    hermitianDilation_apply_eq_swap (T := T) u
  rw [hs]
  constructor <;> intro h
  · rw [← h]
    exact WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simp))
  · rw [h]
    exact WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simp))

/-- The kernel of the Hermitian dilation is `ker T × ker T†`. -/
@[simp]
theorem mem_ker_hermitianDilation {u : WithLp 2 (E × F)} :
    u ∈ T.hermitianDilation.ker ↔ u.fst ∈ T.ker ∧ u.snd ∈ T†.ker := by
  simp only [mem_ker_iff, Subtype.exists]
  constructor
  · rintro ⟨u, hu, rfl, h⟩
    have hfst := congrArg WithLp.fst h
    have hsnd := congrArg WithLp.snd h
    exact ⟨⟨_, (mem_hermitianDilation_domain.mp hu).1, rfl,
        (snd_hermitianDilation_apply _).symm.trans hsnd⟩,
      ⟨_, (mem_hermitianDilation_domain.mp hu).2, rfl,
        (fst_hermitianDilation_apply _).symm.trans hfst⟩⟩
  · rintro ⟨⟨_, hx, rfl, hTx⟩, ⟨_, hy, rfl, hTy⟩⟩
    refine ⟨u, mem_hermitianDilation_domain.mpr ⟨hx, hy⟩, rfl,
      WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)⟩
    · simpa using hTy
    · simpa using hTx

/-- The domain of the Hermitian dilation is dense when the domains of `T` and of `T†` are. -/
theorem dense_hermitianDilation_domain (hT : Dense (T.domain : Set E))
    (hT' : Dense (T†.domain : Set F)) :
    Dense (T.hermitianDilation.domain : Set (WithLp 2 (E × F))) :=
  dense_withLpProdMap_domain hT hT'

/-- The Hermitian dilation of a densely defined operator is symmetric. -/
theorem isFormalAdjoint_hermitianDilation (hT : Dense (T.domain : Set E)) :
    T.hermitianDilation.IsFormalAdjoint T.hermitianDilation := by
  intro u v
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    fst_hermitianDilation_apply, snd_hermitianDilation_apply]
  rw [(adjoint_isFormalAdjoint hT) (hermitianDilationSnd u) (hermitianDilationFst v),
    ← (adjoint_isFormalAdjoint hT).symm (hermitianDilationFst u) (hermitianDilationSnd v),
    add_comm]

variable [CompleteSpace F]

/-- The Hermitian dilation of a closed densely defined operator is self-adjoint:
`[[0, T†], [T, 0]]† = [[0, T†], [T, 0]]`. -/
theorem adjoint_hermitianDilation (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    T.hermitianDilation† = T.hermitianDilation := by
  have hd' := dense_adjoint_domain hT.isClosable
  have hD := dense_hermitianDilation_domain hd hd'
  refine le_antisymm ?_ ((isFormalAdjoint_hermitianDilation hd).le_adjoint hD)
  -- A vector `w` in the domain of the adjoint pairs continuously with `D_T`; testing against
  -- `(x, 0)` and `(0, y)` shows `w.snd ∈ dom T†` and `w.fst ∈ dom T†† = dom T`.
  have key (w : T.hermitianDilation†.domain) :
      (∀ x : T.domain, ⟪(T.hermitianDilation† w).fst, (x : E)⟫_𝕜 =
        ⟪(w : WithLp 2 (E × F)).snd, T x⟫_𝕜) ∧
      ∀ y : T†.domain, ⟪(T.hermitianDilation† w).snd, (y : F)⟫_𝕜 =
        ⟪(w : WithLp 2 (E × F)).fst, T† y⟫_𝕜 := by
    constructor
    · intro x
      have h := (adjoint_isFormalAdjoint hD) w
        ⟨WithLp.toLp 2 ((x : E), ((0 : T†.domain) : F)),
          mem_hermitianDilation_domain.mpr ⟨x.property, (0 : T†.domain).property⟩⟩
      rw [hermitianDilation_apply_toLp, map_zero] at h
      simpa using h
    · intro y
      have h := (adjoint_isFormalAdjoint hD) w
        ⟨WithLp.toLp 2 (((0 : T.domain) : E), (y : F)),
          mem_hermitianDilation_domain.mpr ⟨(0 : T.domain).property, y.property⟩⟩
      rw [hermitianDilation_apply_toLp, map_zero] at h
      simpa using h
  have hsnd (w : T.hermitianDilation†.domain) : (w : WithLp 2 (E × F)).snd ∈ T†.domain :=
    mem_adjoint_domain_of_exists _ ⟨_, (key w).1⟩
  have hfst' (w : T.hermitianDilation†.domain) : (w : WithLp 2 (E × F)).fst ∈ T†.adjoint.domain :=
    mem_adjoint_domain_of_exists _ ⟨_, (key w).2⟩
  have hfst (w : T.hermitianDilation†.domain) : (w : WithLp 2 (E × F)).fst ∈ T.domain := by
    simpa only [adjoint_adjoint hT hd] using hfst' w
  refine ⟨fun w hw ↦ mem_hermitianDilation_domain.mpr ⟨hfst ⟨w, hw⟩, hsnd ⟨w, hw⟩⟩,
    fun w u hwu ↦ ?_⟩
  obtain ⟨u, hu⟩ := u
  obtain rfl : u = w := hwu.symm
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · simpa using (adjoint_apply_eq hd _ (key w).1).symm
  · simpa [← adjoint_apply_eq hd' ⟨_, hfst' w⟩ (key w).2] using
      adjoint_adjoint_apply hT hd (hermitianDilationFst ⟨w, hu⟩)

/-- **The Hermitian dilation of a closed densely defined operator is self-adjoint.** -/
theorem isSelfAdjoint_hermitianDilation (hT : T.IsClosed) (hd : Dense (T.domain : Set E)) :
    IsSelfAdjoint T.hermitianDilation :=
  adjoint_hermitianDilation hT hd

/-- The domain of `D_T²` is `dom (T†T) × dom (TT†)`. -/
theorem mem_domainPow_two_hermitianDilation (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    {u : WithLp 2 (E × F)} :
    u ∈ T.hermitianDilation.domainPow 2 ↔
      u.fst ∈ T.adjointComp.domain ∧ u.snd ∈ T†.adjointComp.domain := by
  simp only [mem_domainPow_succ, domainPow_zero, Submodule.mem_top, exists_prop, and_true,
    mem_hermitianDilation_domain, mem_adjointComp_domain, adjoint_adjoint hT hd,
    fst_hermitianDilation_apply, snd_hermitianDilation_apply]
  tauto

/-- `D_T² = T†T ⊕ TT†`: applying the Hermitian dilation twice applies `T†T` to the first
component and `TT†` to the second. -/
theorem hermitianDilation_apply_hermitianDilation (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {u : WithLp 2 (E × F)}
    (hu : u ∈ T.hermitianDilation.domainPow 2) :
    T.hermitianDilation ⟨T.hermitianDilation ⟨u, domainPow_succ_le_domain _ 1 hu⟩,
      domainPow_succ_le_domain _ 0 (apply_mem_domainPow hu)⟩ =
      WithLp.toLp 2 (T.adjointComp ⟨u.fst, ((mem_domainPow_two_hermitianDilation hT hd).mp hu).1⟩,
        T†.adjointComp ⟨u.snd, ((mem_domainPow_two_hermitianDilation hT hd).mp hu).2⟩) := by
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · simp only [WithLp.ofLp_fst, fst_hermitianDilation_apply, adjointComp_apply,
      hermitianDilationSnd, snd_hermitianDilation_apply]
  · simp only [WithLp.ofLp_snd, snd_hermitianDilation_apply, adjointComp_apply,
      hermitianDilationFst, fst_hermitianDilation_apply]
    exact (adjoint_adjoint_apply hT hd _).symm

/-- **Cores of the Hermitian dilation.** If `S` is a core of a closed densely defined operator `T`
and `S'` is a core of `T†`, then `S × S'` is a core of the Hermitian dilation. For instance,
smooth sections form a core of `[[0, P†], [P, 0]]` once they form cores of `P` and of `P†`. -/
theorem hasCore_hermitianDilation (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    {S : Submodule 𝕜 E} {S' : Submodule 𝕜 F} (hS : T.HasCore S) (hS' : T†.HasCore S') :
    T.hermitianDilation.HasCore
      ((S.prod S').comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap) := by
  set C := (S.prod S').comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  have hC (u : WithLp 2 (E × F)) : u ∈ C ↔ u.fst ∈ S ∧ u.snd ∈ S' := by
    simp [C, Submodule.mem_comap, Submodule.mem_prod]
  have hDc : T.hermitianDilation.IsClosed := (isSelfAdjoint_hermitianDilation hT hd).isClosed
  refine (hDc.hasCore_iff_graph_subset_closure (S := C) fun u hu ↦
    mem_hermitianDilation_domain.mpr
      ⟨hS.le_domain ((hC u).mp hu).1, hS'.le_domain ((hC u).mp hu).2⟩).mpr ?_
  -- The graphs of `T` and `T†` lie in the closures of the graphs of their restrictions to the
  -- cores.
  have hgT := (hT.hasCore_iff_graph_subset_closure hS.le_domain).mp hS
  have hgT' := ((adjoint_isClosed hd).hasCore_iff_graph_subset_closure hS'.le_domain).mp hS'
  -- The graph of the dilation is the image of the product of these graphs under a continuous map.
  let Φ : (E × F) × (F × E) → WithLp 2 (E × F) × WithLp 2 (E × F) :=
    fun q ↦ (WithLp.toLp 2 (q.1.1, q.2.1), WithLp.toLp 2 (q.2.2, q.1.2))
  have hΦ : Continuous Φ :=
    ((WithLp.prod_continuous_toLp 2 E F).comp (by fun_prop)).prodMk
      ((WithLp.prod_continuous_toLp 2 E F).comp (by fun_prop))
  have himage : Φ '' (((T.domRestrict S).graph : Set (E × F)) ×ˢ
      ((T†.domRestrict S').graph : Set (F × E))) ⊆ (T.hermitianDilation.domRestrict C).graph := by
    rintro _ ⟨⟨_, _⟩, ⟨hxa, hyb⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (mem_graph_iff' _).mp hxa
    obtain ⟨y, rfl⟩ := (mem_graph_iff' _).mp hyb
    have hu : WithLp.toLp 2 ((x : E), (y : F)) ∈ (T.hermitianDilation.domRestrict C).domain :=
      ⟨(hC _).mpr ⟨x.property.1, y.property.1⟩,
        mem_hermitianDilation_domain.mpr ⟨x.property.2, y.property.2⟩⟩
    -- All three restrictions evaluate by their unrestricted formulas, `(x, y) ↦ (T† y, T x)`.
    have hDu : T.hermitianDilation.domRestrict C ⟨_, hu⟩ = T.hermitianDilation ⟨_, hu.2⟩ :=
      domRestrict_apply rfl
    have hTx : T.domRestrict S x = T ⟨(x : E), x.property.2⟩ := domRestrict_apply rfl
    have hTy : T†.domRestrict S' y = T† ⟨(y : F), y.property.2⟩ := domRestrict_apply rfl
    refine (mem_graph_iff' _).mpr ⟨⟨_, hu⟩, ?_⟩
    rw [hDu, hTx, hTy, hermitianDilation_apply_toLp (T := T) ⟨_, x.property.2⟩ ⟨_, y.property.2⟩]
  intro p hp
  obtain ⟨hp₁, hp₂⟩ := mem_graph_hermitianDilation_iff.mp hp
  have hmem : ((p.1.fst, p.2.snd), (p.1.snd, p.2.fst)) ∈
      _root_.closure (((T.domRestrict S).graph : Set (E × F)) ×ˢ
        ((T†.domRestrict S').graph : Set (F × E))) := by
    rw [closure_prod_eq]
    exact ⟨hgT hp₁, hgT' hp₂⟩
  exact _root_.closure_mono himage (image_closure_subset_closure_image hΦ ⟨_, hmem, rfl⟩)

end LinearPMap
