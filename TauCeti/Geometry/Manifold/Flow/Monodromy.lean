/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.ReturnDerivative
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.LinearAlgebra.Projection.SplittingEquiv
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# The normal return derivative and the monodromy of a periodic orbit

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold, and let `p` return to
itself at time `T₀`. A function `g` with `dg_p (v p) ≠ 0` cuts out a local section through `p`
transverse to `v`, with tangent space `ker dg_p`. The linearized return map
`DP_p = TauCeti.returnDerivative v g T₀ p` maps `T_p M` into `ker dg_p` and kills `v p`, and its
restriction to `ker dg_p` is the normal return derivative
`N = TauCeti.normalReturnDerivative v g T₀ p h`, the linearization of the return map of the
section. Counted with algebraic multiplicity, the eigenvalues of `N` are the Floquet multipliers
of the orbit with one copy of the trivial multiplier `1` removed; so `N` itself has eigenvalue `1`
exactly when `1` is a multiple Floquet multiplier. `TauCeti.Geometry.Manifold.Flow.ReturnDerivative`
shows that the spectrum of `N` and of its powers depends neither on the section nor on the base
point; this file relates `N` to `DP_p` and to the monodromy of the orbit.

The main results are:

* `TauCeti.charpoly_returnDerivative_eq_X_mul`: since `T_p M = ker dg_p ⊕ ℝ v p` with `DP_p`
  mapping everything into the first summand, `charpoly DP_p = X * charpoly N`.
* `TauCeti.charpoly_mfderiv_flowOf_eq_X_sub_one_mul_charpoly_mapQ`,
  `TauCeti.charpoly_mfderiv_flowOf_eq_X_sub_one_mul_of_isCompl`: section-free and
  invariant-complement splittings `charpoly DΦ_{T₀} = (X - 1) * charpoly (DΦ_{T₀} / (ℝ ∙ v p))`.
* `TauCeti.charpoly_mfderiv_flowOf_eq_X_sub_one_mul`: the derivative `DΦ_{T₀}` of the time-`T₀`
  map of the flow at `p`, the monodromy of the first variational equation along the orbit, has
  characteristic polynomial `(X - 1) * charpoly N`; the factor `X - 1` comes from `DΦ_{T₀}` fixing
  `v p` (`TauCeti.mfderiv_flowOf_apply_self`). Thus `N` and the monodromy have the same
  eigenvalues other than `1`
  (`TauCeti.hasEigenvalue_normalReturnDerivative_iff_hasEigenvalue_mfderiv_flowOf`).
* `TauCeti.quotientEquivOfIsCompl_conj_mapQ_mfderiv_flowOf_eq_normalReturnDerivative`,
  `TauCeti.equivOfIsCompl_conj_normalReturnDerivative`: `Submodule.quotientEquivOfIsCompl`
  conjugates the quotient monodromy on `T_p M ⧸ (ℝ ∙ v p)` to `N`, and projection along `v p`
  (`Submodule.equivOfIsCompl`) conjugates `N` to the restriction of `DΦ_{T₀}` to any
  `DΦ_{T₀}`-invariant complement `ξ` of `ℝ ∙ v p`.
* `TauCeti.returnDerivative_eq_smul_of_mfderiv_flowOf_eq`: if the monodromy of a second field
  with the same closed orbit through `p` is that of `v` composed with a map acting as
  multiplication by `c` modulo `ℝ ∙ v p`, its linearized return map is `c • DP_p`.

As in `TauCeti.Geometry.Manifold.Flow.ReturnDerivative`, `T₀` need not be the least period, and the
return branch need not be the first return to the section.

## References

* G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, AMS Graduate Studies in
  Mathematics 140, 2012, §12.2 (the Poincaré map, its derivative and the monodromy matrix).
* J. Palis, W. de Melo, *Geometric Theory of Dynamical Systems*, Springer 1982, Chapter 3, §1.
-/

public section

noncomputable section

open Function Manifold Set Filter Polynomial
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x} {g : M → ℝ} {T₀ : ℝ} {p : M}

/-- **The linearized return map splits off the normal return derivative.** If the linearized
return map of a section transverse to `v` takes values in the tangent space `ker dg_p` of the
section, its characteristic polynomial is `X` times that of the normal return derivative. -/
theorem charpoly_returnDerivative_eq_X_mul (hgv : mvfderiv I g p (v p) ≠ 0)
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    (returnDerivative v g T₀ p).charpoly = X * (normalReturnDerivative v g T₀ p h).charpoly := by
  set K := LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)
  set A := returnDerivative v g T₀ p
  have hK : K ≤ K.comap A := fun w _ ↦ h (LinearMap.mem_range_self A w)
  -- `A` maps everything into `K`, so it induces zero on the line `T_p M ⧸ K`.
  have hQ : K.mapQ K A hK = 0 := by
    ext w
    simp only [LinearMap.coe_comp, comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact h (LinearMap.mem_range_self A w)
  have hsurj : Surjective (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ) :=
    LinearMap.surjective_of_ne_zero fun h0 ↦ hgv (LinearMap.congr_fun h0 (v p))
  have hrank : Module.finrank ℝ (TangentSpace I p ⧸ K) = 1 :=
    ((mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ).quotKerEquivOfSurjective
      hsurj).finrank_eq.trans (Module.finrank_self ℝ)
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ K A hK, hQ, LinearMap.charpoly_zero,
    hrank, pow_one, mul_comm, normalReturnDerivative_def]

section InvariantComplement

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p)
include hv hP hp

omit [FiniteDimensional ℝ E] in
/-- At a periodic point `p` with `flowOf v T₀ p = p`, the flow line `ℝ ∙ v p` is invariant under
the monodromy `DΦ_{T₀}`. -/
theorem span_singleton_le_comap_mfderiv_flowOf [CompleteSpace E] :
    (ℝ ∙ v p) ≤ (ℝ ∙ v p).comap (mfderiv I I (flowOf v T₀) p).toLinearMap := by
  -- The tangent spaces at `flowOf v T₀ p` and at `p` are both the model space `E`, so
  -- `congrArg v hp` is a well-typed equation of vectors in `E`.
  have hfix : mfderiv I I (flowOf v T₀) p (v p) = v p :=
    (mfderiv_flowOf_apply_self hv hP).trans (congrArg v hp)
  rw [Submodule.span_singleton_le_iff_mem]
  exact Submodule.mem_comap.2 <| by
    rw [ContinuousLinearMap.coe_coe, hfix]
    exact Submodule.mem_span_singleton_self (v p)

/-- **Section-free characteristic polynomial of the monodromy.** If `p` returns to itself at time
`T₀` with `v p ≠ 0`, the characteristic polynomial of `DΦ_{T₀}` splits as `X - 1` times that of the
quotient endomorphism induced on `T_p M ⧸ (ℝ ∙ v p)`. -/
theorem charpoly_mfderiv_flowOf_eq_X_sub_one_mul_charpoly_mapQ (hv0 : v p ≠ 0)
    {hL : (ℝ ∙ v p) ≤ (ℝ ∙ v p).comap (mfderiv I I (flowOf v T₀) p).toLinearMap} :
    (mfderiv I I (flowOf v T₀) p).toLinearMap.charpoly =
      (X - 1) *
        ((ℝ ∙ v p).mapQ (ℝ ∙ v p) (mfderiv I I (flowOf v T₀) p).toLinearMap hL).charpoly := by
  let Mo : Module.End ℝ (TangentSpace I p) := (mfderiv I I (flowOf v T₀) p).toLinearMap
  have hfix : Mo (v p) = v p := (mfderiv_flowOf_apply_self hv hP).trans (congrArg v hp)
  have hres : Mo.restrict (p := ℝ ∙ v p) (q := ℝ ∙ v p) hL = 1 := by
    ext ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.coe_restrict_apply, map_smul, hfix, one_apply_eq_self]
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (ℝ ∙ v p) Mo hL, hres,
    LinearMap.charpoly_one, finrank_span_singleton hv0, pow_one]

/-- **Characteristic polynomial of the monodromy on an invariant complement.** If `p` returns to
itself at time `T₀` with `v p ≠ 0`, `ξ` is a complement of `ℝ ∙ v p`, and `R : Module.End ℝ ξ`
agrees with `DΦ_{T₀}` on `ξ`, the characteristic polynomial of `DΦ_{T₀}` is `X - 1` times that of
`R`. -/
theorem charpoly_mfderiv_flowOf_eq_X_sub_one_mul_of_isCompl (hv0 : v p ≠ 0)
    {ξ : Submodule ℝ (TangentSpace I p)} (hξ : IsCompl ξ (ℝ ∙ v p))
    {R : Module.End ℝ ξ} (hR : ∀ w : ξ, (R w : TangentSpace I p) = mfderiv I I (flowOf v T₀) p w) :
    (mfderiv I I (flowOf v T₀) p).toLinearMap.charpoly = (X - 1) * R.charpoly := by
  have hL := span_singleton_le_comap_mfderiv_flowOf hv hP hp
  rw [charpoly_mfderiv_flowOf_eq_X_sub_one_mul_charpoly_mapQ hv hP hp hv0 (hL := hL),
    ← Submodule.quotientEquivOfIsCompl_conj_mapQ hξ hL hR, LinearEquiv.charpoly_conj]

end InvariantComplement

section Return

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0)
include hv hP hp hg hgv

/-- **Quotient-monodromy conjugacy to the normal return derivative.** For any local section
`{g = g p}` transverse to `v` at a periodic point `p`, identifying `T_p M ⧸ (ℝ ∙ v p)` with
`ker dg_p` via `Submodule.quotientEquivOfIsCompl` conjugates the quotient monodromy on
`T_p M ⧸ (ℝ ∙ v p)` to `TauCeti.normalReturnDerivative`. -/
theorem quotientEquivOfIsCompl_conj_mapQ_mfderiv_flowOf_eq_normalReturnDerivative
    {hL : (ℝ ∙ v p) ≤ (ℝ ∙ v p).comap (mfderiv I I (flowOf v T₀) p).toLinearMap}
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    ((ℝ ∙ v p).quotientEquivOfIsCompl _ (isCompl_ker_mvfderiv_span_singleton hgv).symm).conj
        ((ℝ ∙ v p).mapQ (ℝ ∙ v p) (mfderiv I I (flowOf v T₀) p).toLinearMap hL) =
      normalReturnDerivative v g T₀ p h := by
  -- The tangent spaces at `flowOf v T₀ p` and at `p` are both the model space `E`, so `DΦ_{T₀}`
  -- has type `Module.End ℝ (TangentSpace I p)` and `congrArg v hp` equates vectors in `E`.
  let Mo : Module.End ℝ (TangentSpace I p) := (mfderiv I I (flowOf v T₀) p).toLinearMap
  suffices ((ℝ ∙ v p).quotientEquivOfIsCompl _ (isCompl_ker_mvfderiv_span_singleton hgv).symm).conj
      ((ℝ ∙ v p).mapQ (ℝ ∙ v p) Mo hL) = normalReturnDerivative v g T₀ p h from this
  ext w
  have hform := mfderiv_flowTransition_apply hv hP (by rwa [hp]) (by rwa [hp]) w
  rw [congrArg v hp] at hform
  simp only [LinearEquiv.conj_apply_apply, Submodule.quotientEquivOfIsCompl_symm_apply,
    Submodule.mapQ_apply, Submodule.quotientEquivOfIsCompl_apply_mk]
  have hDP : returnDerivative v g T₀ p w ∈
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ) :=
    h (LinearMap.mem_range_self _ (w : TangentSpace I p))
  -- `Mo w` differs from the return derivative by a multiple of `v p`, which the projection kills.
  have hMo : Mo w =
      returnDerivative v g T₀ p w - mvfderiv I (flowHittingTime v g T₀ p) p w • v p := by
    rw [returnDerivative_apply]
    exact eq_sub_of_add_eq' hform.symm
  rw [hMo, map_sub, map_smul,
    Submodule.projectionOnto_apply_of_mem_right _ (Submodule.mem_span_singleton_self _),
    Submodule.projectionOnto_apply_of_mem_left _ hDP, smul_zero, sub_zero]
  exact (coe_normalReturnDerivative_apply w).symm

/-- **Invariant-complement monodromy conjugacy.** If `ξ` is any `DΦ_{T₀}`-invariant complement of
`ℝ ∙ v p` at a periodic point `p` and `R : Module.End ℝ ξ` agrees with `DΦ_{T₀}` on `ξ`, projection
along `v p` (`Submodule.equivOfIsCompl`) conjugates the normal return derivative on `ker dg_p` to
`R`. -/
theorem equivOfIsCompl_conj_normalReturnDerivative
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)}
    {ξ : Submodule ℝ (TangentSpace I p)} (hξ : IsCompl ξ (ℝ ∙ v p))
    {R : Module.End ℝ ξ} (hR : ∀ w : ξ, (R w : TangentSpace I p) = mfderiv I I (flowOf v T₀) p w) :
    (Submodule.equivOfIsCompl _ ξ (ℝ ∙ v p) (isCompl_ker_mvfderiv_span_singleton hgv) hξ).conj
        (normalReturnDerivative v g T₀ p h) = R := by
  have hL := span_singleton_le_comap_mfderiv_flowOf hv hP hp
  rw [Submodule.equivOfIsCompl_def, ← LinearEquiv.conj_trans, LinearEquiv.trans_apply,
    ← quotientEquivOfIsCompl_conj_mapQ_mfderiv_flowOf_eq_normalReturnDerivative hv hP hp hg hgv
      (hL := hL),
    LinearEquiv.conj_symm_conj, Submodule.quotientEquivOfIsCompl_conj_mapQ hξ hL hR]

/-- **The monodromy and the normal return derivative.** If `p` returns to itself at time `T₀`, the
characteristic polynomial of the derivative `DΦ_{T₀}` at `p` of the time-`T₀` map of the flow is
`X - 1` times that of the normal return derivative of any transverse section through `p`. The
factor `X - 1` comes from `DΦ_{T₀}` fixing `v p` (`TauCeti.mfderiv_flowOf_apply_self`). -/
theorem charpoly_mfderiv_flowOf_eq_X_sub_one_mul
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    (mfderiv I I (flowOf v T₀) p).toLinearMap.charpoly =
      (X - 1) * (normalReturnDerivative v g T₀ p h).charpoly := by
  have hv0 : v p ≠ 0 := fun h0 ↦ hgv (by rw [h0, map_zero])
  have hL := span_singleton_le_comap_mfderiv_flowOf hv hP hp
  rw [charpoly_mfderiv_flowOf_eq_X_sub_one_mul_charpoly_mapQ hv hP hp hv0 (hL := hL),
    ← quotientEquivOfIsCompl_conj_mapQ_mfderiv_flowOf_eq_normalReturnDerivative hv hP hp hg hgv
      (hL := hL),
    LinearEquiv.charpoly_conj]

/-- **The normal return derivative and the monodromy have the same eigenvalues other than
`1`.** If `p` returns to itself at time `T₀`, every `μ ≠ 1` is an eigenvalue of the normal return
derivative exactly when it is an eigenvalue of the derivative `DΦ_{T₀}` at `p` of the time-`T₀` map
of the flow. -/
theorem hasEigenvalue_normalReturnDerivative_iff_hasEigenvalue_mfderiv_flowOf
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} {μ : ℝ} (hμ : μ ≠ 1) :
    (normalReturnDerivative v g T₀ p h).HasEigenvalue μ ↔
      Module.End.HasEigenvalue (mfderiv I I (flowOf v T₀) p).toLinearMap μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_mfderiv_flowOf_eq_X_sub_one_mul hv hP hp hg hgv, IsRoot.def, IsRoot.def, eval_mul,
    eval_sub, eval_X, eval_one, mul_eq_zero, or_iff_right (sub_ne_zero.2 hμ)]

/-- **Rescaling the monodromy transversally rescales the linearized return map.** Let `w` be a
second `C¹` field with `w p = v p` along which `p` also returns at time `T₀`. If the monodromy of
`w` factors as `DΦ^w_{T₀} = DΦ^v_{T₀} ∘ D` through a map `D` of `T_p M` which acts as
multiplication by `c` modulo the flow line `ℝ ∙ v p`, then the linearized return maps of every
section `{g = g p}` transverse to `v` satisfy `DP^w_p = c • DP^v_p`. -/
theorem returnDerivative_eq_smul_of_mfderiv_flowOf_eq {w : (x : M) → TangentSpace I x}
    (hw : CMDiff 1 (fun y ↦ (⟨y, w y⟩ : TangentBundle I M))) (hPw : (T₀, p) ∈ flowDomain w)
    (hpw : flowOf w T₀ p = p) (hwv : w p = v p) {D : TangentSpace I p → TangentSpace I p} {c : ℝ}
    (hD : ∀ ξ, D ξ - c • ξ ∈ ℝ ∙ v p)
    (hM : ∀ ξ : TangentSpace I p,
      -- The tangent spaces at the two values are both the model space `E`.
      @Eq E (mfderiv I I (flowOf w T₀) p ξ) (mfderiv I I (flowOf v T₀) p (D ξ))) :
    returnDerivative w g T₀ p = c • returnDerivative v g T₀ p := by
  have hgw : mvfderiv I g p (w p) ≠ 0 := hwv ▸ hgv
  refine LinearMap.ext fun ξ ↦ ?_
  rw [LinearMap.smul_apply, ← sub_eq_zero]
  -- Both linearized return maps differ from the monodromies by multiples of the field at `p`.
  -- All tangent spaces are the model space `E`, in which the computation takes place.
  set α := mvfderiv I (flowHittingTime w g T₀ p) p ξ
  set β := mvfderiv I (flowHittingTime v g T₀ p) p ξ
  have hfix : mfderiv I I (flowOf v T₀) p (v p) = v p :=
    (mfderiv_flowOf_apply_self hv hP).trans (congrArg v hp)
  let V : E := v p
  let A : E := mfderiv I I (flowOf v T₀) p ξ
  let B : E := mfderiv I I (flowOf v T₀) p (D ξ)
  let Rw : E := returnDerivative w g T₀ p ξ
  let Rv : E := returnDerivative v g T₀ p ξ
  have e₁ : Rw = α • V + B :=
    (returnDerivative_apply ξ).trans <|
      (mfderiv_flowTransition_apply hw hPw (by rwa [hpw]) (by rwa [hpw]) ξ).trans <|
        congrArg₂ (fun a b : E ↦ α • a + b) ((congrArg w hpw).trans hwv) (hM ξ)
  have e₂ : Rv = β • V + A :=
    (returnDerivative_apply ξ).trans <|
      (mfderiv_flowTransition_apply hv hP (by rwa [hp]) (by rwa [hp]) ξ).trans <|
        congrArg (fun a : E ↦ β • a + A) (congrArg v hp)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hD ξ)
  have e₃ : B = c • A + r • V := by
    simp only [B, A, V]
    rw [show D ξ = c • ξ + r • v p by rw [hr, add_sub_cancel], map_add, map_smul, map_smul, hfix]
    -- The two sides are the same expression, with `+` and `•` taken in the tangent space at
    -- `flowOf v T₀ p` on the left and in `E` on the right; `TangentSpace I x` is by definition
    -- `E`, so they agree definitionally.
    rfl
  -- So their difference is a multiple `k • v p` of the field.
  set k := α - c * β + r
  have hdiff : Rw - c • Rv = k • V := by
    rw [e₁, e₂, e₃]
    module
  -- Both lie in the tangent space `ker dg_p` of the section, which does not contain `v p`.
  have hker : ∀ {u : (x : M) → TangentSpace I x}, CMDiff 1 (fun y ↦ (⟨y, u y⟩ :
      TangentBundle I M)) → (T₀, p) ∈ flowDomain u → flowOf u T₀ p = p →
      mvfderiv I g p (u p) ≠ 0 →
      mvfderiv I g p (returnDerivative u g T₀ p ξ) = 0 := fun hu hPu hpu hgu ↦
    LinearMap.mem_ker.1 (range_returnDerivative_le_ker hu hPu hpu hg hgu
      (LinearMap.mem_range_self _ ξ))
  let L : E →L[ℝ] ℝ := mvfderiv I g p
  have hk : k * L V = 0 := by
    have hRw : L Rw = 0 := hker hw hPw hpw hgw
    have hRv : L Rv = 0 := hker hv hP hp hgv
    have h := congrArg L hdiff
    rw [map_sub, map_smul, hRw, hRv, smul_zero, sub_zero, map_smul, smul_eq_mul] at h
    exact h.symm
  -- The goal is stated in `TangentSpace I p`, while `hdiff` is stated in `E` through the
  -- abbreviations `Rw` and `Rv`; the two types are definitionally equal, so `change` restates the
  -- goal in `E` and lets `hdiff` rewrite it.
  change Rw - c • Rv = 0
  rw [hdiff, (mul_eq_zero.1 hk).resolve_right hgv, zero_smul]

end Return

end TauCeti
