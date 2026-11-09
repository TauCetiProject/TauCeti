/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.ReturnDerivative
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# The normal return derivative of a periodic orbit

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold, and let `p` return to
itself at time `T₀`. A function `g` with `dg_p (v p) ≠ 0` cuts out a local section through `p`
transverse to `v`, with tangent space `ker dg_p`, and the return branch
`P = TauCeti.flowTransition v g T₀ p` flows points near `p` back into that section. Its derivative
`DP_p` maps `T_p M` into `ker dg_p` and kills `v p`. The **normal return derivative**
`TauCeti.normalReturnDeriv v g T₀ p` is the restriction of `DP_p` to `ker dg_p`: the linearization
of the return map of the section, whose eigenvalues are the Floquet multipliers of the orbit other
than the trivial multiplier `1` along the orbit.

The main results are:

* `TauCeti.charpoly_mfderiv_flowTransition_eq_X_mul`: since `T_p M = ker dg_p ⊕ ℝ v p` with `DP_p`
  zero on the second summand, `charpoly DP_p = X * charpoly N`. Hence the nonzero eigenvalues of
  `N` are those of `DP_p` (`TauCeti.hasEigenvalue_normalReturnDeriv_iff_of_ne_zero`); in
  particular `N` has the eigenvalue `1` exactly when `DP_p` does.
* `TauCeti.charpoly_normalReturnDeriv_eq`, `TauCeti.hasEigenvalue_normalReturnDeriv_iff`: the
  characteristic polynomial and the eigenvalues of `N` depend neither on the section nor on the
  base point along the orbit. This follows from the same statement for `DP_p`,
  `TauCeti.charpoly_mfderiv_flowTransition_eq`, by cancelling `X`.
* `TauCeti.normalReturnDeriv_zero`, `TauCeti.normalReturnDeriv_natCast_mul`: the normal derivative
  of the time-`0` transition is the identity, and that of the return branch at time `k * T₀` is
  `N ^ k`. So the `k`-th iterate of the return map has normal derivative `N ^ k`, whose
  characteristic polynomial is again independent of the choices
  (`TauCeti.charpoly_pow_normalReturnDeriv_eq`).
* `TauCeti.charpoly_mfderiv_flowOf_eq_X_sub_one_mul`: the derivative `DΦ_{T₀}` of the time-`T₀`
  map of the flow at `p`, the monodromy of the first variational equation along the orbit, fixes
  `v p` and has characteristic polynomial `(X - 1) * charpoly N`. Thus every eigenvalue
  `μ ≠ 1` of the monodromy is an eigenvalue of `N` and conversely
  (`TauCeti.hasEigenvalue_normalReturnDeriv_iff_of_ne_one`).

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
  {v : (x : M) → TangentSpace I x} {g g' : M → ℝ} {T T₀ : ℝ} {p q : M}

open Classical in
/-- **The normal return derivative.** The restriction of the derivative `DP_p` of the return branch
`flowTransition v g T₀ p` to the tangent space `ker dg_p` of the section cut out by `g`, as an
endomorphism of `ker dg_p`. When `p` returns to itself at time `T₀` and the section is transverse
to `v`, `DP_p` maps `ker dg_p` into itself and this is its restriction
(`TauCeti.coe_normalReturnDeriv_apply`); otherwise the value is `0`. -/
def normalReturnDeriv (v : (x : M) → TangentSpace I x) (g : M → ℝ) (T₀ : ℝ) (p : M) :
    Module.End ℝ (LinearMap.ker (mvfderiv I g p).toLinearMap) :=
  let A : Module.End ℝ (TangentSpace I p) := (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap
  if h : ∀ w ∈ LinearMap.ker (mvfderiv I g p).toLinearMap,
      A w ∈ LinearMap.ker (mvfderiv I g p).toLinearMap then A.restrict h else 0

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- The derivative of `g` is onto `ℝ`, since it does not vanish on `v p`. -/
private theorem surjective_mvfderiv (hgv : mvfderiv I g p (v p) ≠ 0) :
    Surjective (mvfderiv I g p) := fun c ↦
  ⟨(c / mvfderiv I g p (v p)) • v p, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hgv]⟩

section Return

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0)
include hv hP hp hg hgv

/-- **A return derivative lands in the section.** If `p` returns to itself at time `T₀`, the
derivative of the return branch to a transverse section through `p` takes values in `ker dg_p`. -/
theorem mvfderiv_mfderiv_flowTransition_apply_eq_zero (w : TangentSpace I p) :
    mvfderiv I g p (mfderiv I I (flowTransition v g T₀ p) p w) = 0 := by
  have h := mvfderiv_comp_mfderiv_flowTransition hv hP (by rwa [hp]) (by rwa [hp])
  rw [hp] at h
  exact DFunLike.congr_fun h w

/-- The normal return derivative is the restriction of the return derivative `DP_p` to the tangent
space `ker dg_p` of the section. -/
theorem coe_normalReturnDeriv_apply (w : LinearMap.ker (mvfderiv I g p).toLinearMap) :
    (normalReturnDeriv v g T₀ p w : TangentSpace I p) =
      mfderiv I I (flowTransition v g T₀ p) p w := by
  rw [normalReturnDeriv]
  split_ifs with h
  · -- `LinearMap.restrict` applies `DP_p`, read as an endomorphism of `T_p M`, to `w`.
    rfl
  · exact absurd (fun w _ ↦ LinearMap.mem_ker.2
      (mvfderiv_mfderiv_flowTransition_apply_eq_zero hv hP hp hg hgv w)) h

end Return

/-- **The time-`0` transition is the identity on the section to first order.** For a section
through `p` transverse to `v`, the normal derivative of the time-`0` transition is the identity:
along `ker dg_p` the hitting time does not change to first order, and the time-`0` map of the
flow is the identity. -/
theorem normalReturnDeriv_zero (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0) :
    normalReturnDeriv v g 0 p = 1 := by
  have h0 := mem_flowDomain_zero hv p
  have hp0 := flowOf_zero hv p
  ext w
  rw [coe_normalReturnDeriv_apply hv h0 hp0 hg hgv, one_apply_eq_self]
  have hform := mfderiv_flowTransition_apply hv h0 (by rwa [hp0]) (by rwa [hp0]) w
  rw [show flowOf v 0 = id from funext (flowOf_zero hv), mfderiv_id,
    ContinuousLinearMap.id_apply] at hform
  -- The tangent spaces at `id p` and at `p` are both the model space, so this equation is well
  -- typed; it holds by substituting `id p = p`.
  have hvp : ∀ x, x = p → v x = v p := by
    rintro x rfl
    rfl
  rw [hvp (id p) rfl] at hform
  have hker := mvfderiv_mfderiv_flowTransition_apply_eq_zero hv h0 hp0 hg hgv w
  rw [hform] at hker
  -- The hitting time does not change to first order along the section.
  have hτ : mvfderiv I (flowHittingTime v g 0 p) p w = 0 := by
    have hw : mvfderiv I g p w = 0 := LinearMap.mem_ker.1 w.2
    simpa [hw, hgv] using hker
  rw [hform, hτ, zero_smul, zero_add]

section Return

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0)
include hv hP hp hg hgv

/-- **The return derivative splits off the normal return derivative.** If `p` returns to itself
at time `T₀`, the characteristic polynomial of the derivative `DP_p` of the return branch is `X`
times that of the normal return derivative. -/
theorem charpoly_mfderiv_flowTransition_eq_X_mul :
    (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap.charpoly =
      X * (normalReturnDeriv v g T₀ p).charpoly := by
  set K := LinearMap.ker (mvfderiv I g p).toLinearMap
  let A : Module.End ℝ (TangentSpace I p) := (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap
  have hA : ∀ w, A w ∈ K := fun w ↦
    LinearMap.mem_ker.2 (mvfderiv_mfderiv_flowTransition_apply_eq_zero hv hP hp hg hgv w)
  have hK : K ≤ K.comap A := fun w _ ↦ hA w
  -- `A` maps everything into `K`, so it induces zero on the line `T_p M ⧸ K`.
  have hQ : K.mapQ K A hK = 0 := by
    ext w
    simp only [LinearMap.coe_comp, comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact hA w
  have hrank : Module.finrank ℝ (TangentSpace I p ⧸ K) = 1 :=
    ((mvfderiv I g p).toLinearMap.quotKerEquivOfSurjective
      (surjective_mvfderiv hgv)).finrank_eq.trans (Module.finrank_self ℝ)
  have hN : A.restrict hK = normalReturnDeriv v g T₀ p := by
    ext w
    rw [coe_normalReturnDeriv_apply hv hP hp hg hgv]
    -- `A` is `DP_p` read as an endomorphism of `T_p M`.
    rfl
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ K A hK, hQ, LinearMap.charpoly_zero,
    hrank, pow_one, hN, mul_comm]

/-- **The nonzero eigenvalues of the normal return derivative are those of the return
derivative.** In particular the normal return derivative has the eigenvalue `1` exactly when the
derivative `DP_p` of the return branch on all of `T_p M` does. -/
theorem hasEigenvalue_normalReturnDeriv_iff_of_ne_zero {μ : ℝ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (normalReturnDeriv v g T₀ p) μ ↔
      Module.End.HasEigenvalue (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_mfderiv_flowTransition_eq_X_mul hv hP hp hg hgv, IsRoot.def, IsRoot.def, eval_mul,
    eval_X, mul_eq_zero, or_iff_right hμ]

/-- **The normal return derivative of an iterate.** The return branch at time `k * T₀` is the
`k`-fold iterate of the return branch at time `T₀`, and its normal derivative is the `k`-th power
of the normal return derivative. -/
theorem normalReturnDeriv_natCast_mul (k : ℕ) :
    normalReturnDeriv v g (k * T₀) p = normalReturnDeriv v g T₀ p ^ k := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using normalReturnDeriv_zero hv hg hgv
  | succ k ih =>
    obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp k
    have hcomp := mfderiv_flowTransition_comp hv hkP hkp hg hgv hP hp hg hgv
    have hk : (k : ℝ) * T₀ + T₀ = ((k + 1 : ℕ) : ℝ) * T₀ := by push_cast; ring
    rw [hk] at hcomp
    obtain ⟨hk'P, hk'p⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp (k + 1)
    ext w
    rw [coe_normalReturnDeriv_apply hv hk'P hk'p hg hgv, ← hcomp, pow_succ', mul_apply_eq_comp,
      ← ih, coe_normalReturnDeriv_apply hv hP hp hg hgv,
      coe_normalReturnDeriv_apply hv hkP hkp hg hgv]
    -- Both sides apply `DP_p` at time `T₀` after `DP_p` at time `k * T₀`.
    rfl

/-- **The characteristic polynomial of the normal return derivative is independent of the section
and of the base point.** If the flow carries `p` to `q` at time `T` and `p` returns to itself at
time `T₀`, the normal return derivatives at time `T₀` of a section through `p` and of a section
through `q` have the same characteristic polynomial. -/
theorem charpoly_normalReturnDeriv_eq (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q)
    (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0) :
    (normalReturnDeriv v g T₀ p).charpoly = (normalReturnDeriv v g' T₀ q).charpoly := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  refine mul_left_cancel₀ (X_ne_zero (R := ℝ)) ?_
  rw [← charpoly_mfderiv_flowTransition_eq_X_mul hv hP hp hg hgv,
    ← charpoly_mfderiv_flowTransition_eq_X_mul hv hQ hq' hg' hg'v]
  exact charpoly_mfderiv_flowTransition_eq hv hT hq hP hp hg hgv hg' hg'v

/-- **The eigenvalues of the normal return derivative are independent of the section and of the
base point.** In particular, whether `1` is an eigenvalue of the normal return derivative depends
only on the orbit and on `T₀`. -/
theorem hasEigenvalue_normalReturnDeriv_iff (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q)
    (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0) (μ : ℝ) :
    Module.End.HasEigenvalue (normalReturnDeriv v g T₀ p) μ ↔
      Module.End.HasEigenvalue (normalReturnDeriv v g' T₀ q) μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    charpoly_normalReturnDeriv_eq hv hP hp hg hgv hT hq hg' hg'v]

/-- **Iterates of the normal return derivative.** For every `k`, the `k`-th powers of the normal
return derivatives at time `T₀` of a section through `p` and of a section through `q = flowOf v T p`
have the same characteristic polynomial. -/
theorem charpoly_pow_normalReturnDeriv_eq (hT : (T, p) ∈ flowDomain v) (hq : flowOf v T p = q)
    (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0) (k : ℕ) :
    (normalReturnDeriv v g T₀ p ^ k).charpoly = (normalReturnDeriv v g' T₀ q ^ k).charpoly := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp k
  obtain ⟨hkQ, hkq⟩ := flowOf_natCast_mul_of_flowOf_eq hv hQ hq' k
  rw [← normalReturnDeriv_natCast_mul hv hP hp hg hgv,
    ← normalReturnDeriv_natCast_mul hv hQ hq' hg' hg'v]
  exact charpoly_normalReturnDeriv_eq hv hkP hkp hg hgv hT hq hg' hg'v

/-- **The monodromy and the normal return derivative.** If `p` returns to itself at time `T₀`, the
derivative `DΦ_{T₀}` at `p` of the time-`T₀` map of the flow fixes `v p`, and its characteristic
polynomial is `X - 1` times that of the normal return derivative of any transverse section
through `p`. -/
theorem charpoly_mfderiv_flowOf_eq_X_sub_one_mul :
    (mfderiv I I (flowOf v T₀) p).toLinearMap.charpoly =
      (X - 1) * (normalReturnDeriv v g T₀ p).charpoly := by
  set K := LinearMap.ker (mvfderiv I g p).toLinearMap
  let Mo : Module.End ℝ (TangentSpace I p) := (mfderiv I I (flowOf v T₀) p).toLinearMap
  -- The tangent spaces at `flowOf v T₀ p` and at `p` are both the model space, so this equation
  -- is well typed; it holds by substituting `flowOf v T₀ p = p`.
  have hvp : ∀ x, x = p → v x = v p := by
    rintro x rfl
    rfl
  have hfix : Mo (v p) = v p := (mfderiv_flowOf_apply_self hv hP).trans (hvp _ hp)
  have hv0 : v p ≠ 0 := fun h ↦ hgv (by rw [h, map_zero])
  set L := ℝ ∙ v p
  have hL : L ≤ L.comap Mo := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Submodule.mem_comap, map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hres : Mo.restrict (p := L) (q := L) hL = 1 := by
    ext ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [LinearMap.coe_restrict_apply, map_smul, hfix, one_apply_eq_self]
  have hcompl : IsCompl L K :=
    ⟨(Submodule.disjoint_span_singleton_of_notMem hgv).symm,
      codisjoint_iff.2 (LinearMap.span_singleton_sup_ker_eq_top _ hgv)⟩
  let e := Submodule.quotientEquivOfIsCompl L K hcompl
  have hconj : e.conj (L.mapQ L Mo hL) = normalReturnDeriv v g T₀ p := by
    ext w
    have hform := mfderiv_flowTransition_apply hv hP (by rwa [hp]) (by rwa [hp]) w
    rw [hvp _ hp] at hform
    simp only [e, LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply,
      Submodule.quotientEquivOfIsCompl_apply_mk]
    let A : Module.End ℝ (TangentSpace I p) :=
      (mfderiv I I (flowTransition v g T₀ p) p).toLinearMap
    have hDP : A w ∈ K :=
      LinearMap.mem_ker.2 (mvfderiv_mfderiv_flowTransition_apply_eq_zero hv hP hp hg hgv w)
    -- `Mo w` differs from the return derivative by a multiple of `v p`, which the projection kills.
    have hMo : Mo w = A w - mvfderiv I (flowHittingTime v g T₀ p) p w • v p :=
      eq_sub_of_add_eq' hform.symm
    rw [hMo, map_sub, map_smul,
      Submodule.projectionOnto_apply_of_mem_right _ (Submodule.mem_span_singleton_self _),
      Submodule.projectionOnto_apply_of_mem_left _ hDP, smul_zero, sub_zero,
      coe_normalReturnDeriv_apply hv hP hp hg hgv]
    -- `A` is `DP_p` read as an endomorphism of `T_p M`.
    rfl
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ L Mo hL, hres,
    LinearMap.charpoly_one, finrank_span_singleton hv0, pow_one, ← LinearEquiv.charpoly_conj e,
    hconj]

/-- **The Floquet multipliers other than `1` are the eigenvalues of the normal return
derivative.** If `p` returns to itself at time `T₀`, every `μ ≠ 1` is an eigenvalue of the normal
return derivative exactly when it is an eigenvalue of the derivative `DΦ_{T₀}` at `p` of the
time-`T₀` map of the flow. -/
theorem hasEigenvalue_normalReturnDeriv_iff_of_ne_one {μ : ℝ} (hμ : μ ≠ 1) :
    Module.End.HasEigenvalue (normalReturnDeriv v g T₀ p) μ ↔
      Module.End.HasEigenvalue (mfderiv I I (flowOf v T₀) p).toLinearMap μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_mfderiv_flowOf_eq_X_sub_one_mul hv hP hp hg hgv, IsRoot.def, IsRoot.def, eval_mul,
    eval_sub, eval_X, eval_one, mul_eq_zero, or_iff_right (sub_ne_zero.2 hμ)]

end Return

end TauCeti
