/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.ReturnDerivative
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# The normal return derivative and the monodromy of a periodic orbit

Let `v` be a `C¹` vector field on a boundaryless finite-dimensional manifold, and let `p` return to
itself at time `T₀`. A function `g` with `dg_p (v p) ≠ 0` cuts out a local section through `p`
transverse to `v`, with tangent space `ker dg_p`. The linearized return map
`DP_p = TauCeti.returnDerivative v g T₀ p` maps `T_p M` into `ker dg_p` and kills `v p`, and its
restriction to `ker dg_p` is the normal return derivative
`N = TauCeti.normalReturnDerivative v g T₀ p h`, the linearization of the return map of the
section. Its eigenvalues are the Floquet multipliers of the orbit other than the trivial multiplier
`1` along the orbit. `TauCeti.Geometry.Manifold.Flow.ReturnDerivative` shows that the spectrum of
`N` depends neither on the section nor on the base point; this file relates `N` to `DP_p`, to its
iterates and to the monodromy of the orbit.

The main results are:

* `TauCeti.charpoly_returnDerivative_eq_X_mul`: since `T_p M = ker dg_p ⊕ ℝ v p` with `DP_p`
  mapping everything into the first summand, `charpoly DP_p = X * charpoly N`.
* `TauCeti.normalReturnDerivative_zero`, `TauCeti.normalReturnDerivative_natCast_mul`: the normal
  derivative of the time-`0` transition is the identity, and that of the return branch at time
  `k * T₀` is `N ^ k`. So the `k`-th iterate of the return map has normal derivative `N ^ k`,
  whose characteristic polynomial is again independent of the choices
  (`TauCeti.charpoly_pow_normalReturnDerivative_eq`).
* `TauCeti.charpoly_mfderiv_flowOf_eq_X_sub_one_mul`: the derivative `DΦ_{T₀}` of the time-`T₀`
  map of the flow at `p`, the monodromy of the first variational equation along the orbit, fixes
  `v p` and has characteristic polynomial `(X - 1) * charpoly N`. Thus every eigenvalue
  `μ ≠ 1` of the monodromy is an eigenvalue of `N` and conversely
  (`TauCeti.hasEigenvalue_normalReturnDerivative_iff_of_ne_one`).

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

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
/-- The derivative of `g` is onto `ℝ`, since it does not vanish on `v p`. -/
private theorem surjective_mvfderiv (hgv : mvfderiv I g p (v p) ≠ 0) :
    Surjective (mvfderiv I g p) := fun c ↦
  ⟨(c / mvfderiv I g p (v p)) • v p, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hgv]⟩

omit [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] in
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
  have hrank : Module.finrank ℝ (TangentSpace I p ⧸ K) = 1 :=
    ((mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ).quotKerEquivOfSurjective
      (surjective_mvfderiv hgv)).finrank_eq.trans (Module.finrank_self ℝ)
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ K A hK, hQ, LinearMap.charpoly_zero,
    hrank, pow_one, mul_comm]
  -- The normal return derivative is the restriction of `A` to `K`.
  rfl

/-- **The time-`0` transition is the identity on the section to first order.** For a section
through `p` transverse to `v`, the normal derivative of the time-`0` transition is the identity. -/
theorem normalReturnDerivative_zero (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hg : ContMDiffAt I 𝓘(ℝ) 1 g p) (hgv : mvfderiv I g p (v p) ≠ 0)
    {h : LinearMap.range (returnDerivative v g 0 p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    normalReturnDerivative v g 0 p h = 1 :=
  LinearMap.ext fun w ↦ Subtype.ext <|
    mfderiv_flowTransition_zero_apply_of_mvfderiv_eq_zero hv hg hgv (LinearMap.mem_ker.1 w.2)

section Return

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0)
include hv hP hp hg hgv

/-- **The normal return derivative of an iterate.** The return branch at time `k * T₀` is the
`k`-fold iterate of the return branch at time `T₀`, and its normal derivative is the `k`-th power
of the normal return derivative. -/
theorem normalReturnDerivative_natCast_mul (k : ℕ)
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)}
    {hk : LinearMap.range (returnDerivative v g (k * T₀) p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    normalReturnDerivative v g (k * T₀) p hk = normalReturnDerivative v g T₀ p h ^ k := by
  ext w
  rw [normalReturnDerivative, Module.End.pow_restrict, LinearMap.restrict_coe_apply,
    LinearMap.restrict_coe_apply]
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [pow_zero, Module.End.one_apply, returnDerivative_apply]
    simp only [Nat.cast_zero, zero_mul]
    exact mfderiv_flowTransition_zero_apply_of_mvfderiv_eq_zero hv hg hgv (LinearMap.mem_ker.1 w.2)
  · rw [returnDerivative_natCast_mul hv hP hp hg hgv hk0]

/-- **Iterates of the normal return derivative.** For every `k`, the `k`-th powers of the normal
return derivatives at time `T₀` of a section through `p` and of a section through `q = flowOf v T p`
have the same characteristic polynomial. -/
theorem charpoly_pow_normalReturnDerivative_eq (hT : (T, p) ∈ flowDomain v)
    (hq : flowOf v T p = q) (hg' : ContMDiffAt I 𝓘(ℝ) 1 g' q) (hg'v : mvfderiv I g' q (v q) ≠ 0)
    (k : ℕ)
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)}
    {h' : LinearMap.range (returnDerivative v g' T₀ q) ≤
      LinearMap.ker (mvfderiv I g' q : TangentSpace I q →ₗ[ℝ] ℝ)} :
    (normalReturnDerivative v g T₀ p h ^ k).charpoly =
      (normalReturnDerivative v g' T₀ q h' ^ k).charpoly := by
  obtain ⟨hQ, hq'⟩ := hq ▸ flowOf_flowOf_of_flowOf_eq hv hT hP hp
  obtain ⟨hkP, hkp⟩ := flowOf_natCast_mul_of_flowOf_eq hv hP hp k
  obtain ⟨hkQ, hkq⟩ := flowOf_natCast_mul_of_flowOf_eq hv hQ hq' k
  rw [← normalReturnDerivative_natCast_mul hv hP hp hg hgv k
      (hk := range_returnDerivative_le_ker hv hkP hkp hg hgv),
    ← normalReturnDerivative_natCast_mul hv hQ hq' hg' hg'v k
      (hk := range_returnDerivative_le_ker hv hkQ hkq hg' hg'v)]
  exact charpoly_normalReturnDerivative_eq hv hT hq hkP hkp hg hgv hg' hg'v

/-- **The monodromy and the normal return derivative.** If `p` returns to itself at time `T₀`, the
derivative `DΦ_{T₀}` at `p` of the time-`T₀` map of the flow fixes `v p`, and its characteristic
polynomial is `X - 1` times that of the normal return derivative of any transverse section
through `p`. -/
theorem charpoly_mfderiv_flowOf_eq_X_sub_one_mul
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    (mfderiv I I (flowOf v T₀) p).toLinearMap.charpoly =
      (X - 1) * (normalReturnDerivative v g T₀ p h).charpoly := by
  set K := LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)
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
    rw [LinearMap.coe_restrict_apply, map_smul, hfix, Module.End.one_apply]
  have hcompl : IsCompl L K :=
    ⟨(Submodule.disjoint_span_singleton_of_notMem hgv).symm,
      codisjoint_iff.2 (LinearMap.span_singleton_sup_ker_eq_top _ hgv)⟩
  let e := Submodule.quotientEquivOfIsCompl L K hcompl
  have hconj : e.conj (L.mapQ L Mo hL) = normalReturnDerivative v g T₀ p h := by
    ext w
    have hform := mfderiv_flowTransition_apply hv hP (by rwa [hp]) (by rwa [hp]) w
    rw [hvp _ hp] at hform
    simp only [e, LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply,
      Submodule.quotientEquivOfIsCompl_apply_mk]
    let A := returnDerivative v g T₀ p
    have hDP : A w ∈ K := h (LinearMap.mem_range_self A w)
    -- `Mo w` differs from the return derivative by a multiple of `v p`, which the projection kills.
    have hMo : Mo w = A w - mvfderiv I (flowHittingTime v g T₀ p) p w • v p :=
      eq_sub_of_add_eq' hform.symm
    rw [hMo, map_sub, map_smul,
      Submodule.projectionOnto_apply_of_mem_right _ (Submodule.mem_span_singleton_self _),
      Submodule.projectionOnto_apply_of_mem_left _ hDP, smul_zero, sub_zero]
    -- The normal return derivative is the restriction of `A` to `K`.
    rfl
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ L Mo hL, hres,
    LinearMap.charpoly_one, finrank_span_singleton hv0, pow_one, ← LinearEquiv.charpoly_conj e,
    hconj]

/-- **The Floquet multipliers other than `1` are the eigenvalues of the normal return
derivative.** If `p` returns to itself at time `T₀`, every `μ ≠ 1` is an eigenvalue of the normal
return derivative exactly when it is an eigenvalue of the derivative `DΦ_{T₀}` at `p` of the
time-`T₀` map of the flow. -/
theorem hasEigenvalue_normalReturnDerivative_iff_of_ne_one
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} {μ : ℝ} (hμ : μ ≠ 1) :
    (normalReturnDerivative v g T₀ p h).HasEigenvalue μ ↔
      Module.End.HasEigenvalue (mfderiv I I (flowOf v T₀) p).toLinearMap μ := by
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).trans
    (Iff.trans ?_ (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).symm)
  rw [charpoly_mfderiv_flowOf_eq_X_sub_one_mul hv hP hp hg hgv, IsRoot.def, IsRoot.def, eval_mul,
    eval_sub, eval_X, eval_one, mul_eq_zero, or_iff_right (sub_ne_zero.2 hμ)]

end Return

end TauCeti
