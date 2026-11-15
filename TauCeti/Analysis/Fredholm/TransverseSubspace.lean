/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.Normed.Operator.Fredholm.Open
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Transverse subspaces and Fredholm stability

Let `T₀ : E →L[𝕜] F` be a continuous linear operator from a normed space `E` into a Hilbert space
`F`, and let `V ≤ E` be a subspace transverse to `ker T₀` (`Disjoint V T₀.ker`, i.e.
`V ⊓ T₀.ker = ⊥`). Following Atiyah and Singer, consider for any operator `T : E →L[𝕜] F` the
coproduct operator
$$\Phi_T = (T \circ \iota_V) \oplus \iota_{(T₀(V))^{\perp}} : V \times (T₀(V))^{\perp} \to F.$$
Because the domain `V × (T₀(V))ᗮ` is independent of `T` and `T ↦ Φ_T` is continuous in operator
norm, invertibility of `Φ_T` is an open condition in `E →L[𝕜] F`:

* **Pointwise consequences of invertibility of `Φ_T`:** whenever `Φ_T` is invertible, `V` remains
  transverse to `ker T` (`Disjoint V T.ker`), `T` restricts to a topological isomorphism
  `V ≃L[𝕜] V.map T`, the image `V.map T` is closed and topologically complementary to the fixed
  orthogonal complement `(V.map T₀)ᗮ`, and `F ⧸ V.map T ≃L[𝕜] (V.map T₀)ᗮ`.
* **Openness at `T₀`:** when `E` and `F` are complete, `V` is closed, `V.map T₀` is closed, and
  `Disjoint V T₀.ker`, Banach's open mapping theorem makes `Φ_{T₀}` invertible, so `Φ_T` stays
  invertible for all `T` in an operator-norm neighborhood of `T₀`.
* **Finite-dimensional `V`:** when `V` is finite-dimensional and `Disjoint V T₀.ker`, closedness of
  `V` and `V.map T₀` is automatic, so `Disjoint V T.ker` and `(V.map T).IsTopCompl (V.map T₀)ᗮ`
  hold throughout a neighborhood of `T₀`.
* **Closed finite-codimension `V`:** when `V` is closed of finite codimension and `(V.map T₀)ᗮ` is
  finite-dimensional, invertibility of `Φ_T` forces `T` to be Fredholm (in particular, to have
  closed range) with
  $$\dim \ker T \le \operatorname{codim} V, \qquad
    \dim \operatorname{coker} T \le \dim (T₀(V))^{\perp},$$
  and index `T.index = finrank 𝕜 (E ⧸ V) - finrank 𝕜 (V.map T₀)ᗮ = T₀.index`. Consequently, kernel
  and cokernel dimensions drop by equal amounts from `T₀` to `T`. Specializing to `V = (T₀.ker)ᗮ`
  for a Fredholm operator `T₀` between Hilbert spaces yields Atiyah–Singer's geometric openness,
  upper semicontinuity, and index invariance package around `T₀`.

## Main declarations

* `ContinuousLinearMap.transverseCoprod`: the operator
  `(T.comp V.subtypeL).coprod (V.map T₀)ᗮ.subtypeL : (V × (V.map T₀)ᗮ) →L[𝕜] F`.
* `ContinuousLinearMap.disjoint_ker_of_isInvertible_transverseCoprod` and
  `ContinuousLinearMap.isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod`: transversality
  `Disjoint V T.ker` and topological splitting `(V.map T).IsTopCompl (V.map T₀)ᗮ`.
* `ContinuousLinearMap.restrictTransverseEquiv` and
  `ContinuousLinearMap.quotientMapEquivOrthogonal`: canonical equivalences `V ≃L[𝕜] V.map T` and
  `(F ⧸ V.map T) ≃L[𝕜] (V.map T₀)ᗮ`.
* `ContinuousLinearMap.isInvertible_transverseCoprod_self` and
  `ContinuousLinearMap.eventually_nhds_isInvertible_transverseCoprod`: invertibility of `Φ_{T₀}`
  and openness in `𝓝 T₀`.
* `ContinuousLinearMap.eventually_nhds_isInvertible_transverseCoprod_of_finiteDimensional`:
  neighborhood stability for finite-dimensional transverse subspaces.
* `ContinuousLinearMap.isFredholm_of_isInvertible_transverseCoprod`,
  `ContinuousLinearMap.finrank_ker_le_of_isInvertible_transverseCoprod`,
  `ContinuousLinearMap.finrank_coker_le_of_isInvertible_transverseCoprod`, and
  `ContinuousLinearMap.index_eq_of_isInvertible_transverseCoprod`: Fredholmness, dimension bounds,
  and index formula for closed finite-codimension transverse subspaces.
* `ContinuousLinearMap.IsFredholm.eventually_nhds_isInvertible_transverseCoprod_orthogonal_ker`:
  specialization to `V = (T₀.ker)ᗮ` for a Fredholm operator between Hilbert spaces.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. (2) **87**
  (1968), 484–530 (Appendix, pp. 519–520).
-/

public section

open Filter Function Module Submodule Topology
open scoped InnerProduct

namespace ContinuousLinearMap

/-! ### The transverse coproduct and its pointwise consequences -/

section Pointwise

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Given a reference operator `T₀ : E →L[𝕜] F` and a subspace `V ≤ E`, `T₀.transverseCoprod V T`
is the continuous linear map `(V × (V.map T₀)ᗮ) →L[𝕜] F` sending `(v, w) ↦ T v + w`. -/
noncomputable def transverseCoprod (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F) :
    (V × (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) →L[𝕜] F :=
  (T.comp V.subtypeL).coprod (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL

/-- Pointwise formula for `transverseCoprod`. -/
@[simp]
theorem transverseCoprod_apply (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) (T : E →L[𝕜] F)
    (p : V × (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) :
    T₀.transverseCoprod V T p = T p.1 + p.2 :=
  (rfl)

/-- Every continuous linear map `T` maps a submodule `V` into `V.map T`. -/
theorem mapsTo_map (T : E →L[𝕜] F) (V : Submodule 𝕜 E) :
    Set.MapsTo T V (V.map (T : E →ₗ[𝕜] F)) :=
  fun x hx ↦ ⟨x, hx, rfl⟩

/-- If `T₀.transverseCoprod V T` is invertible, `V` is disjoint from `ker T`. -/
theorem disjoint_ker_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    Disjoint V T.ker := by
  rw [Submodule.disjoint_def]
  intro v hv hTv
  have hv0 : T v = 0 := hTv
  have happ : T₀.transverseCoprod V T (⟨v, hv⟩, 0) = T₀.transverseCoprod V T 0 := by
    simp [hv0]
  exact congrArg Subtype.val (congrArg Prod.fst (hΦ.injective happ))

/-- Lattice-meet form of `disjoint_ker_of_isInvertible_transverseCoprod`. -/
theorem inf_ker_eq_bot_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    V ⊓ T.ker = ⊥ :=
  (disjoint_ker_of_isInvertible_transverseCoprod hΦ).eq_bot

/-- If `T₀.transverseCoprod V T` is invertible, then `T(V)` and `(T₀(V))ᗮ` are topological
complements in `F`. -/
theorem isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (V.map (T : E →ₗ[𝕜] F)).IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
  let W := V.map (T₀ : E →ₗ[𝕜] F)
  let f₁ : V →L[𝕜] F := T.comp V.subtypeL
  let f₂ : F →L[𝕜] V := .fst 𝕜 V Wᗮ ∘L (T₀.transverseCoprod V T).inverse
  have hleft : LeftInverse f₂ f₁ := fun u ↦ by
    have h := congrArg Prod.fst (hΦ.inverse_apply_self (u, (0 : Wᗮ)))
    simpa [f₁, f₂] using h
  have hrange : f₁.range = V.map (T : E →ₗ[𝕜] F) := by
    simp [f₁, LinearMap.range_comp]
  have hker : f₂.ker = Wᗮ := by
    ext y
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, f₂, comp_apply, coe_fst']
    constructor
    · intro hy
      have hinv := hΦ.self_apply_inverse y
      simp only [transverseCoprod_apply, hy, ZeroMemClass.coe_zero, map_zero, zero_add] at hinv
      exact hinv ▸ ((T₀.transverseCoprod V T).inverse y).2.2
    · intro hy
      have h := congrArg Prod.fst (hΦ.inverse_apply_self ((0 : V), (⟨y, hy⟩ : Wᗮ)))
      simpa using h
  exact hrange ▸ hker ▸ f₁.isTopCompl_range_ker_of_leftInverse f₂ hleft

/-- If `T₀.transverseCoprod V T` is invertible, then `V.map T` is closed in `F`. -/
theorem isClosed_map_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    IsClosed ((V.map (T : E →ₗ[𝕜] F)) : Set F) :=
  (isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod hΦ).isClosed

/-- If `T₀.transverseCoprod V T` is invertible, `T` restricts to a continuous linear equivalence
`V ≃L[𝕜] V.map T`. -/
noncomputable def restrictTransverseEquiv {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    V ≃L[𝕜] V.map (T : E →ₗ[𝕜] F) :=
  ContinuousLinearEquiv.equivOfInverse
    (T.restrict (T.mapsTo_map V))
    (.fst 𝕜 V (V.map (T₀ : E →ₗ[𝕜] F))ᗮ ∘L (T₀.transverseCoprod V T).inverse ∘L
      (V.map (T : E →ₗ[𝕜] F)).subtypeL)
    (fun u ↦ by
      have h := congrArg Prod.fst (hΦ.inverse_apply_self (u, 0))
      have hcoe : (T.restrict (T.mapsTo_map V) u : F) = T u := rfl
      simpa only [comp_apply, subtypeL_apply, hcoe, coe_fst',
        transverseCoprod_apply, ZeroMemClass.coe_zero, add_zero] using h)
    (fun y ↦ by
      obtain ⟨v, hv, hTv⟩ := y.2
      rw [ContinuousLinearMap.coe_coe] at hTv
      rw [← Subtype.coe_inj]
      have h := congrArg Prod.fst (hΦ.inverse_apply_self ((⟨v, hv⟩ : V), 0))
      simp only [transverseCoprod_apply, ZeroMemClass.coe_zero, add_zero, hTv] at h
      simp only [comp_apply, subtypeL_apply, coe_fst', h]
      exact hTv)

/-- `restrictTransverseEquiv` acts on `V` by `T`. -/
@[simp]
theorem coe_restrictTransverseEquiv_apply {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) (u : V) :
    (restrictTransverseEquiv hΦ u : F) = T u :=
  (rfl)

/-- If `T₀.transverseCoprod V T` is invertible, the restriction `V →L[𝕜] V.map T` of `T` is
invertible. -/
theorem isInvertible_restrict_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (T.restrict (T.mapsTo_map V)).IsInvertible :=
  ⟨restrictTransverseEquiv hΦ, rfl⟩

/-- If `T₀.transverseCoprod V T` is invertible, the quotient `F ⧸ V.map T` is continuously
linearly equivalent to the fixed orthogonal complement `(V.map T₀)ᗮ`. -/
noncomputable def quotientMapEquivOrthogonal {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (F ⧸ V.map (T : E →ₗ[𝕜] F)) ≃L[𝕜] (V.map (T₀ : E →ₗ[𝕜] F))ᗮ :=
  (V.map (T : E →ₗ[𝕜] F)).quotientEquivOfIsTopCompl (V.map (T₀ : E →ₗ[𝕜] F))ᗮ
    (isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod hΦ)

/-- Kernel dimension bound when `T₀.transverseCoprod V T` is invertible and `V` has finite
codimension. -/
theorem finrank_ker_le_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [V.CoFG] (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) := by
  have : FiniteDimensional 𝕜 (E ⧸ V) := inferInstance
  have hinj : Injective (V.mkQ.comp T.ker.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have hq : V.mkQ ((x : E) - (y : E)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hmem : (x : E) - (y : E) ∈ V := V.ker_mkQ ▸ LinearMap.mem_ker.mpr hq
    have hker : (x : E) - (y : E) ∈ T.ker := T.ker.sub_mem x.2 y.2
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp
      (disjoint_ker_of_isInvertible_transverseCoprod hΦ)) _ hmem hker)
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- Cokernel dimension bound when `T₀.transverseCoprod V T` is invertible and `(V.map T₀)ᗮ` is
finite-dimensional. -/
theorem finrank_coker_le_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
  let e := (quotientMapEquivOrthogonal hΦ).toLinearEquiv
  have : FiniteDimensional 𝕜 (F ⧸ V.map (T : E →ₗ[𝕜] F)) := e.symm.finiteDimensional
  have hle : V.map (T : E →ₗ[𝕜] F) ≤ T.range := LinearMap.map_le_range
  exact (LinearMap.finrank_le_finrank_of_surjective (Submodule.factor_surjective hle)).trans_eq
    e.finrank_eq

end Pointwise

/-! ### Fredholmness and index from a finite-codimension transverse subspace -/

section CoFG

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Fredholmness from a finite-codimension transverse subspace.** If `V ≤ E` is closed of finite
codimension, `(V.map T₀)ᗮ` is finite-dimensional, and `T₀.transverseCoprod V T` is invertible, then
`T` is Fredholm (and in particular `T.range` is closed). -/
theorem isFredholm_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E}
    (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    T.IsFredholm := by
  have hcompl := isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod hΦ
  have : (V.map (T : E →ₗ[𝕜] F)).CoFG :=
    Submodule.FG.cofg_of_isCompl hcompl.isCompl.symm .of_finite
  exact .of_isInvertible_restrict hV hcompl.isClosed (T.mapsTo_map V)
    (isInvertible_restrict_of_isInvertible_transverseCoprod hΦ)

/-- **Index formula from a finite-codimension transverse subspace.** Under the hypotheses of
`isFredholm_of_isInvertible_transverseCoprod`, the index of `T` equals
`finrank 𝕜 (E ⧸ V) - finrank 𝕜 (V.map T₀)ᗮ`, independent of `T`. -/
theorem index_eq_of_isInvertible_transverseCoprod {T₀ T : E →L[𝕜] F}
    {V : Submodule 𝕜 E} (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    T.index = (finrank 𝕜 (E ⧸ V) : ℤ) - finrank 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
  have hTF : T.IsFredholm := isFredholm_of_isInvertible_transverseCoprod hV hΦ
  have hVF : V.subtypeL.IsFredholm := V.isFredholm_subtypeL hV
  have hcomp_idx := hTF.index_comp hVF
  have hinj : Injective ((T ∘L V.subtypeL) : V →ₗ[𝕜] F) := by
    intro u₁ u₂ hu
    apply Subtype.ext
    have hker : (u₁ : E) - (u₂ : E) ∈ T.ker := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact hu
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp
      (disjoint_ker_of_isInvertible_transverseCoprod hΦ)) _ (V.sub_mem u₁.2 u₂.2) hker)
  have hcoker : finrank 𝕜 (F ⧸ ((T ∘L V.subtypeL) : V →ₗ[𝕜] F).range) =
      finrank 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
    rw [toLinearMap_comp, LinearMap.range_comp, Submodule.toLinearMap_subtypeL,
      Submodule.range_subtype]
    exact (quotientMapEquivOrthogonal hΦ).toLinearEquiv.finrank_eq
  rw [LinearMap.index_of_injective hinj, hcoker, Submodule.toLinearMap_subtypeL,
    LinearMap.index_subtype, ← T.index_def] at hcomp_idx
  omega

/-- Kernel and cokernel dimensions drop by equal amounts relative to `codim V` and
`dim (V.map T₀)ᗮ` whenever both `Φ_{T₀}` and `Φ_T` are invertible. -/
theorem finrank_ker_sub_eq_finrank_coker_sub_of_isInvertible_transverseCoprod
    {T₀ T : E →L[𝕜] F} {V : Submodule 𝕜 E} (hV : IsClosed (V : Set E)) [V.CoFG]
    [FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F))ᗮ]
    (hΦ₀ : (T₀.transverseCoprod V T₀).IsInvertible)
    (hΦ : (T₀.transverseCoprod V T).IsInvertible) :
    (finrank 𝕜 T₀.ker : ℤ) - finrank 𝕜 T.ker =
      (finrank 𝕜 (F ⧸ T₀.range) : ℤ) - finrank 𝕜 (F ⧸ T.range) := by
  have hidx₀ := index_eq_of_isInvertible_transverseCoprod hV hΦ₀
  have hidx := index_eq_of_isInvertible_transverseCoprod hV hΦ
  rw [T₀.index_eq_finrank_sub] at hidx₀
  rw [T.index_eq_finrank_sub] at hidx
  omega

end CoFG

/-! ### Operator-norm continuity and openness around `T₀` -/

section Normed

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `T ↦ T₀.transverseCoprod V T` is continuous in operator norm. -/
theorem continuous_transverseCoprod (T₀ : E →L[𝕜] F) (V : Submodule 𝕜 E) :
    Continuous (T₀.transverseCoprod V) := by
  have heq : T₀.transverseCoprod V = fun T : E →L[𝕜] F ↦
      T ∘L (V.subtypeL ∘L .fst 𝕜 V (V.map (T₀ : E →ₗ[𝕜] F))ᗮ) +
        (V.map (T₀ : E →ₗ[𝕜] F))ᗮ.subtypeL ∘L .snd 𝕜 V (V.map (T₀ : E →ₗ[𝕜] F))ᗮ := by
    funext T
    exact ContinuousLinearMap.ext fun _ ↦ rfl
  rw [heq]
  exact (continuous_id.clm_comp continuous_const).add continuous_const

section Complete

variable [CompleteSpace E] [CompleteSpace F]

/-- **Invertibility of `Φ_{T₀}`.** When `E` and `F` are complete, `V ≤ E` is closed, `V.map T₀` is
closed in `F`, and `Disjoint V T₀.ker`, the coproduct `T₀.transverseCoprod V T₀` is invertible. -/
theorem isInvertible_transverseCoprod_self (T₀ : E →L[𝕜] F) {V : Submodule 𝕜 E}
    (hV : IsClosed (V : Set E)) (hTV : IsClosed ((V.map (T₀ : E →ₗ[𝕜] F)) : Set F))
    (hdisj : Disjoint V T₀.ker) :
    (T₀.transverseCoprod V T₀).IsInvertible := by
  have : CompleteSpace V := hV.isComplete.completeSpace_coe
  let W := V.map (T₀ : E →ₗ[𝕜] F)
  have : W.HasOrthogonalProjection := Submodule.hasOrthogonalProjection_iff_isClosed.mpr hTV
  rw [ContinuousLinearMap.isInvertible_iff_bijective]
  refine ⟨?_, ?_⟩
  · -- Injectivity from `W ⊓ Wᗮ = ⊥` and `Disjoint V T₀.ker`.
    intro ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ h
    have huw : T₀ (u₁ - u₂ : V) + ((w₁ - w₂ : Wᗮ) : F) = 0 := by
      simpa only [transverseCoprod_apply, AddSubgroupClass.coe_sub, map_sub,
        add_sub_add_comm] using sub_eq_zero.mpr h
    have hmemW : T₀ (u₁ - u₂ : V) ∈ W := Submodule.mem_map_of_mem (u₁ - u₂).2
    have hmemWo : T₀ (u₁ - u₂ : V) ∈ Wᗮ := by
      rw [eq_neg_of_add_eq_zero_left huw]
      exact Wᗮ.neg_mem (w₁ - w₂).2
    have hTu0 : T₀ (u₁ - u₂ : V) = 0 :=
      (Submodule.mem_bot 𝕜).mp (W.inf_orthogonal_eq_bot ▸ ⟨hmemW, hmemWo⟩)
    have hu0 : (u₁ - u₂ : V) = 0 := Subtype.ext <|
      (Submodule.disjoint_def.mp hdisj) (u₁ - u₂).1 (u₁ - u₂).2 hTu0
    have hw0 : (w₁ - w₂ : Wᗮ) = 0 :=
      ZeroMemClass.coe_eq_zero.mp (by simpa only [hTu0, zero_add] using huw)
    exact Prod.ext (sub_eq_zero.mp hu0) (sub_eq_zero.mp hw0)
  · -- Surjectivity from the orthogonal decomposition `F = W ⊕ Wᗮ`.
    intro y
    obtain ⟨v, hv, hTv⟩ := Submodule.starProjection_apply_mem W y
    rw [ContinuousLinearMap.coe_coe] at hTv
    refine ⟨(⟨v, hv⟩, ⟨Wᗮ.starProjection y, Submodule.starProjection_apply_mem Wᗮ y⟩), ?_⟩
    simp only [transverseCoprod_apply, hTv, Submodule.starProjection_orthogonal, sub_apply,
      id_apply, add_sub_cancel]

/-- **Openness of the transverse-subspace condition.** Under the hypotheses of
`isInvertible_transverseCoprod_self`, `T₀.transverseCoprod V T` stays invertible for all `T` in an
operator-norm neighborhood of `T₀`. -/
theorem eventually_nhds_isInvertible_transverseCoprod (T₀ : E →L[𝕜] F) {V : Submodule 𝕜 E}
    (hV : IsClosed (V : Set E)) (hTV : IsClosed ((V.map (T₀ : E →ₗ[𝕜] F)) : Set F))
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, (T₀.transverseCoprod V T).IsInvertible :=
  (T₀.continuous_transverseCoprod V).continuousAt.eventually
    (T₀.isInvertible_transverseCoprod_self hV hTV hdisj).eventually_nhds

/-- **Finite-dimensional transverse subspace stability.** If `V ≤ E` is finite-dimensional and
`Disjoint V T₀.ker`, then `T₀.transverseCoprod V T₀` is invertible without explicit closedness
hypotheses. -/
theorem isInvertible_transverseCoprod_self_of_finiteDimensional (T₀ : E →L[𝕜] F)
    (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    (T₀.transverseCoprod V T₀).IsInvertible := by
  have : FiniteDimensional 𝕜 (V.map (T₀ : E →ₗ[𝕜] F)) := Module.Finite.map V (T₀ : E →ₗ[𝕜] F)
  exact T₀.isInvertible_transverseCoprod_self V.isClosed_of_finiteDimensional
    (V.map (T₀ : E →ₗ[𝕜] F)).isClosed_of_finiteDimensional hdisj

/-- **Finite-dimensional transverse subspace openness.** If `V ≤ E` is finite-dimensional and
`Disjoint V T₀.ker`, then `T₀.transverseCoprod V T` is invertible for all `T` near `T₀` (so in
particular `Disjoint V T.ker` and `(V.map T).IsTopCompl (V.map T₀)ᗮ` hold near `T₀`). -/
theorem eventually_nhds_isInvertible_transverseCoprod_of_finiteDimensional (T₀ : E →L[𝕜] F)
    (V : Submodule 𝕜 E) [FiniteDimensional 𝕜 V] (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T in 𝓝 T₀, (T₀.transverseCoprod V T).IsInvertible :=
  (T₀.continuous_transverseCoprod V).continuousAt.eventually
    (T₀.isInvertible_transverseCoprod_self_of_finiteDimensional V hdisj).eventually_nhds

/-- **Atiyah–Singer transverse-subspace stability for closed finite-codimension `V`.** If `V ≤ E`
is closed of finite codimension, `V.map T₀` is closed of finite codimension in `F`, and
`Disjoint V T₀.ker`, then for all `T` in an operator-norm neighborhood of `T₀`:
`T` is Fredholm, `Disjoint V T.ker`, `(V.map T).IsTopCompl (V.map T₀)ᗮ`, `T.index = T₀.index`,
`finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V)`, and `finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (F ⧸ V.map T₀)`. -/
theorem eventually_nhds_isFredholm_and_index_eq_of_transverse (T₀ : E →L[𝕜] F)
    {V : Submodule 𝕜 E} (hV : IsClosed (V : Set E)) [V.CoFG]
    (hTV : IsClosed ((V.map (T₀ : E →ₗ[𝕜] F)) : Set F)) [(V.map (T₀ : E →ₗ[𝕜] F)).CoFG]
    (hdisj : Disjoint V T₀.ker) :
    ∀ᶠ T : E →L[𝕜] F in 𝓝 T₀, T.IsFredholm ∧ Disjoint V T.ker ∧
      (V.map (T : E →ₗ[𝕜] F)).IsTopCompl (V.map (T₀ : E →ₗ[𝕜] F))ᗮ ∧
      T.index = T₀.index ∧
      finrank 𝕜 T.ker ≤ finrank 𝕜 (E ⧸ V) ∧
      finrank 𝕜 (F ⧸ T.range) ≤ finrank 𝕜 (F ⧸ V.map (T₀ : E →ₗ[𝕜] F)) := by
  let W := V.map (T₀ : E →ₗ[𝕜] F)
  have : W.HasOrthogonalProjection := Submodule.hasOrthogonalProjection_iff_isClosed.mpr hTV
  let eW : (F ⧸ W) ≃ₗ[𝕜] Wᗮ := W.quotientEquivOfIsCompl Wᗮ W.isCompl_orthogonal
  have : FiniteDimensional 𝕜 Wᗮ := eW.finiteDimensional
  have hΦ₀ := T₀.isInvertible_transverseCoprod_self hV hTV hdisj
  have hidx₀ := index_eq_of_isInvertible_transverseCoprod hV hΦ₀
  filter_upwards [T₀.eventually_nhds_isInvertible_transverseCoprod hV hTV hdisj] with T hΦ
  refine ⟨isFredholm_of_isInvertible_transverseCoprod hV hΦ,
    disjoint_ker_of_isInvertible_transverseCoprod hΦ,
    isTopCompl_map_orthogonal_of_isInvertible_transverseCoprod hΦ,
    (index_eq_of_isInvertible_transverseCoprod hV hΦ).trans hidx₀.symm,
    finrank_ker_le_of_isInvertible_transverseCoprod hΦ,
    (finrank_coker_le_of_isInvertible_transverseCoprod hΦ).trans_eq eW.symm.finrank_eq⟩

end Complete

end Normed

/-! ### Canonical specialization to `V = (T₀.ker)ᗮ` on Hilbert spaces -/

/-- Whenever `T₀.ker` admits an orthogonal projection, `T₀` maps `(T₀.ker)ᗮ` onto `T₀.range`. -/
theorem map_orthogonal_ker_eq_range {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    (T₀ : E →L[𝕜] F) [T₀.ker.HasOrthogonalProjection] :
    (T₀.ker)ᗮ.map (T₀ : E →ₗ[𝕜] F) = T₀.range := by
  refine le_antisymm LinearMap.map_le_range ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨(T₀.ker)ᗮ.starProjection x, Submodule.starProjection_apply_mem _ x, ?_⟩
  simp

namespace IsFredholm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {T₀ : E →L[𝕜] F}

/-- At a Fredholm operator `T₀` between Hilbert spaces, `T₀.transverseCoprod (T₀.ker)ᗮ T₀` is
invertible. -/
theorem isInvertible_transverseCoprod_orthogonal_ker_self (hT₀ : T₀.IsFredholm) :
    (T₀.transverseCoprod (T₀.ker)ᗮ T₀).IsInvertible := by
  refine T₀.isInvertible_transverseCoprod_self T₀.ker.isClosed_orthogonal ?_
    T₀.ker.orthogonal_disjoint.symm
  rw [T₀.map_orthogonal_ker_eq_range]
  exact hT₀.isClosed_range

/-- Near a Fredholm operator `T₀` between Hilbert spaces, `T₀.transverseCoprod (T₀.ker)ᗮ T` stays
invertible. -/
theorem eventually_nhds_isInvertible_transverseCoprod_orthogonal_ker (hT₀ : T₀.IsFredholm) :
    ∀ᶠ T in 𝓝 T₀, (T₀.transverseCoprod (T₀.ker)ᗮ T).IsInvertible :=
  (T₀.continuous_transverseCoprod (T₀.ker)ᗮ).continuousAt.eventually
    hT₀.isInvertible_transverseCoprod_orthogonal_ker_self.eventually_nhds

end IsFredholm

end ContinuousLinearMap

end
