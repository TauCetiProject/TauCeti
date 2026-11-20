/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.AdjointComp
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint
public import TauCeti.LinearAlgebra.LinearPMap.DomainPow

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
`LinearMap.hermitianDilation`.

## Main declarations

* `LinearPMap.hermitianDilation`: the operator `(x, y) ↦ (T† y, T x)` on `dom T × dom T†`.
* `LinearPMap.mem_hermitianDilation_domain`: its domain is `dom T × dom T†`.
* `LinearPMap.hermitianDilation_toLp`: `D_T (x, y) = (T† y, T x)`.
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
`dom T × dom T†`. -/
def hermitianDilation (T : E →ₗ.[𝕜] F) : WithLp 2 (E × F) →ₗ.[𝕜] WithLp 2 (E × F) where
  domain := (T.domain.prod T†.domain).comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  toFun :=
    let D := (T.domain.prod T†.domain).comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      ((T†.toFun ∘ₗ ((WithLp.sndₗ 2 𝕜 E F ∘ₗ D.subtype).codRestrict T†.domain fun u ↦ u.2.2)).prod
        (T.toFun ∘ₗ ((WithLp.fstₗ 2 𝕜 E F ∘ₗ D.subtype).codRestrict T.domain fun u ↦ u.2.1)))

variable {T : E →ₗ.[𝕜] F}

/-- The domain of the Hermitian dilation is `dom T × dom T†`. -/
@[simp]
theorem mem_hermitianDilation_domain {u : WithLp 2 (E × F)} :
    u ∈ T.hermitianDilation.domain ↔ u.fst ∈ T.domain ∧ u.snd ∈ T†.domain :=
  Iff.rfl

/-- The first component of a vector in the domain of the Hermitian dilation, as a vector of
`dom T`. -/
abbrev hermitianDilationFst (u : T.hermitianDilation.domain) : T.domain :=
  ⟨(u : WithLp 2 (E × F)).fst, (mem_hermitianDilation_domain.mp u.2).1⟩

/-- The second component of a vector in the domain of the Hermitian dilation, as a vector of
`dom T†`. -/
abbrev hermitianDilationSnd (u : T.hermitianDilation.domain) : T†.domain :=
  ⟨(u : WithLp 2 (E × F)).snd, (mem_hermitianDilation_domain.mp u.2).2⟩

/-- The Hermitian dilation sends `(x, y)` to `(T† y, T x)`. -/
theorem hermitianDilation_apply (u : T.hermitianDilation.domain) :
    T.hermitianDilation u =
      WithLp.toLp 2 (T† (hermitianDilationSnd u), T (hermitianDilationFst u)) :=
  (rfl)

/-- The first component of `D_T (x, y)` is `T† y`. -/
@[simp]
theorem fst_hermitianDilation_apply (u : T.hermitianDilation.domain) :
    (T.hermitianDilation u).fst = T† (hermitianDilationSnd u) :=
  (rfl)

/-- The second component of `D_T (x, y)` is `T x`. -/
@[simp]
theorem snd_hermitianDilation_apply (u : T.hermitianDilation.domain) :
    (T.hermitianDilation u).snd = T (hermitianDilationFst u) :=
  (rfl)

/-- The Hermitian dilation on a pair `(x, y)` with `x ∈ dom T` and `y ∈ dom T†`. -/
theorem hermitianDilation_toLp (x : T.domain) (y : T†.domain) :
    T.hermitianDilation ⟨WithLp.toLp 2 ((x : E), (y : F)),
      mem_hermitianDilation_domain.mpr ⟨x.2, y.2⟩⟩ =
      WithLp.toLp 2 (T† y, T x) :=
  (rfl)

/-- The graph norm identity `‖D_T (x, y)‖² = ‖T† y‖² + ‖T x‖²`. -/
theorem norm_hermitianDilation_apply_sq (u : T.hermitianDilation.domain) :
    ‖T.hermitianDilation u‖ ^ 2 =
      ‖T† (hermitianDilationSnd u)‖ ^ 2 + ‖T (hermitianDilationFst u)‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

/-- The kernel of the Hermitian dilation is `ker T × ker T†`. -/
@[simp]
theorem mem_ker_hermitianDilation {u : WithLp 2 (E × F)} :
    u ∈ T.hermitianDilation.ker ↔ u.fst ∈ T.ker ∧ u.snd ∈ T†.ker := by
  simp only [mem_ker_iff, Subtype.exists]
  constructor
  · rintro ⟨u, hu, rfl, h⟩
    have hfst := congrArg WithLp.fst h
    have hsnd := congrArg WithLp.snd h
    exact ⟨⟨_, hu.1, rfl, hsnd⟩, ⟨_, hu.2, rfl, hfst⟩⟩
  · rintro ⟨⟨x, hx, hux, hTx⟩, ⟨y, hy, huy, hTy⟩⟩
    have hu : u ∈ T.hermitianDilation.domain := by
      rw [mem_hermitianDilation_domain, hux, huy]
      exact ⟨hx, hy⟩
    refine ⟨u, hu, rfl, WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)⟩
    · rw [WithLp.ofLp_fst, fst_hermitianDilation_apply, WithLp.ofLp_zero, Prod.fst_zero, ← hTy]
      exact congrArg T† (Subtype.ext huy)
    · rw [WithLp.ofLp_snd, snd_hermitianDilation_apply, WithLp.ofLp_zero, Prod.snd_zero, ← hTx]
      exact congrArg T (Subtype.ext hux)

/-- The domain of the Hermitian dilation is dense when the domains of `T` and of `T†` are. -/
theorem dense_hermitianDilation_domain (hT : Dense (T.domain : Set E))
    (hT' : Dense (T†.domain : Set F)) :
    Dense (T.hermitianDilation.domain : Set (WithLp 2 (E × F))) := by
  have h : (T.hermitianDilation.domain : Set (WithLp 2 (E × F))) =
      WithLp.toLp 2 '' ((T.domain : Set E) ×ˢ (T†.domain : Set F)) := by
    ext u
    simp only [SetLike.mem_coe, mem_hermitianDilation_domain]
    constructor
    · intro hu
      exact ⟨WithLp.ofLp u, hu, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [h]
  exact (WithLp.toLp_surjective 2).denseRange.dense_image (WithLp.prod_continuous_toLp 2 E F)
    (hT.prod hT')

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
          mem_hermitianDilation_domain.mpr ⟨x.2, (0 : T†.domain).2⟩⟩
      rw [hermitianDilation_toLp, map_zero] at h
      simpa using h
    · intro y
      have h := (adjoint_isFormalAdjoint hD) w
        ⟨WithLp.toLp 2 (((0 : T.domain) : E), (y : F)),
          mem_hermitianDilation_domain.mpr ⟨(0 : T.domain).2, y.2⟩⟩
      rw [hermitianDilation_toLp, map_zero] at h
      simpa using h
  have hsnd (w : T.hermitianDilation†.domain) : (w : WithLp 2 (E × F)).snd ∈ T†.domain :=
    mem_adjoint_domain_of_exists _ ⟨_, (key w).1⟩
  have hfst' (w : T.hermitianDilation†.domain) : (w : WithLp 2 (E × F)).fst ∈ T†.adjoint.domain :=
    mem_adjoint_domain_of_exists _ ⟨_, (key w).2⟩
  have hfst (w : T.hermitianDilation†.domain) : (w : WithLp 2 (E × F)).fst ∈ T.domain := by
    simpa only [adjoint_adjoint hT hd] using hfst' w
  refine ⟨fun w hw ↦ ⟨hfst ⟨w, hw⟩, hsnd ⟨w, hw⟩⟩, fun w u hwu ↦ ?_⟩
  obtain ⟨u, hu⟩ := u
  obtain rfl : u = w := hwu.symm
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · rw [WithLp.ofLp_fst, WithLp.ofLp_fst, fst_hermitianDilation_apply]
    exact (adjoint_apply_eq hd _ (key w).1).symm
  · rw [WithLp.ofLp_snd, WithLp.ofLp_snd, snd_hermitianDilation_apply,
      ← adjoint_apply_eq hd' ⟨_, hfst' w⟩ (key w).2]
    exact (LinearPMap.ext_iff.mp (adjoint_adjoint hT hd)).2 (x := _) (hf := _) (hg := _)

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
    exact ((LinearPMap.ext_iff.mp (adjoint_adjoint hT hd)).2 (x := _) (hf := _) (hg := _)).symm

/-- **Cores of the Hermitian dilation.** If `S` is a core of a closed densely defined operator `T`
and `S'` is a core of `T†`, then `S × S'` is a core of the Hermitian dilation. For instance,
smooth sections form a core of `[[0, P†], [P, 0]]` once they form cores of `P` and of `P†`. -/
theorem hasCore_hermitianDilation (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    {S : Submodule 𝕜 E} {S' : Submodule 𝕜 F} (hS : T.HasCore S) (hS' : T†.HasCore S') :
    T.hermitianDilation.HasCore
      ((S.prod S').comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap) := by
  set C := (S.prod S').comap (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap
  have hDc : T.hermitianDilation.IsClosed := (isSelfAdjoint_hermitianDilation hT hd).isClosed
  have hRc : (T.hermitianDilation.domRestrict C).IsClosable :=
    hDc.isClosable.leIsClosable domRestrict_le
  refine ⟨fun u hu ↦ mem_hermitianDilation_domain.mpr ⟨hS.1 hu.1, hS'.1 hu.2⟩,
    le_antisymm ?_ ?_⟩
  · refine le_of_le_graph ?_
    rw [← hRc.graph_closure_eq_closure_graph]
    exact Submodule.topologicalClosure_minimal _ (le_graph_of_le domRestrict_le) hDc
  refine le_of_le_graph ?_
  rw [← hRc.graph_closure_eq_closure_graph]
  -- The graphs of `T` and `T†` are the closures of the graphs of their restrictions to the cores.
  have hgT : (T.graph : Set (E × F)) ⊆ _root_.closure ((T.domRestrict S).graph : Set (E × F)) := by
    rw [← Submodule.topologicalClosure_coe,
      (hT.isClosable.leIsClosable domRestrict_le).graph_closure_eq_closure_graph, hS.2]
  have hgT' :
      (T†.graph : Set (F × E)) ⊆ _root_.closure ((T†.domRestrict S').graph : Set (F × E)) := by
    rw [← Submodule.topologicalClosure_coe,
      ((adjoint_isClosed hd).isClosable.leIsClosable domRestrict_le).graph_closure_eq_closure_graph,
      hS'.2]
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
      ⟨⟨x.2.1, y.2.1⟩, mem_hermitianDilation_domain.mpr ⟨x.2.2, y.2.2⟩⟩
    -- Both restrictions evaluate by their defining formulas, `(x, y) ↦ (T† y, T x)`.
    exact (mem_graph_iff' _).mpr ⟨⟨_, hu⟩, rfl⟩
  intro p hp
  obtain ⟨u, rfl⟩ := (mem_graph_iff' _).mp hp
  have hmem : (((u : WithLp 2 (E × F)).fst, T (hermitianDilationFst u)),
      ((u : WithLp 2 (E × F)).snd, T† (hermitianDilationSnd u))) ∈
      _root_.closure (((T.domRestrict S).graph : Set (E × F)) ×ˢ
        ((T†.domRestrict S').graph : Set (F × E))) := by
    rw [closure_prod_eq]
    exact ⟨hgT (T.mem_graph (hermitianDilationFst u)), hgT' (T†.mem_graph (hermitianDilationSnd u))⟩
  have h := _root_.closure_mono himage (image_closure_subset_closure_image hΦ ⟨_, hmem, rfl⟩)
  rw [← Submodule.topologicalClosure_coe] at h
  exact h

end LinearPMap
