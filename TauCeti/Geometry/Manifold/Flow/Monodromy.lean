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
section. Counted with algebraic multiplicity, the eigenvalues of `N` are the Floquet multipliers
of the orbit with one copy of the trivial multiplier `1` removed; so `N` itself has eigenvalue `1`
exactly when `1` is a multiple Floquet multiplier. `TauCeti.Geometry.Manifold.Flow.ReturnDerivative`
shows that the spectrum of `N` and of its powers depends neither on the section nor on the base
point; this file relates `N` to `DP_p` and to the monodromy of the orbit.

The main results are:

* `TauCeti.charpoly_returnDerivative_eq_X_mul`: since `T_p M = ker dg_p ⊕ ℝ v p` with `DP_p`
  mapping everything into the first summand, `charpoly DP_p = X * charpoly N`.
* `TauCeti.charpoly_mfderiv_flowOf_eq_X_sub_one_mul`: the derivative `DΦ_{T₀}` of the time-`T₀`
  map of the flow at `p`, the monodromy of the first variational equation along the orbit, has
  characteristic polynomial `(X - 1) * charpoly N`; the factor `X - 1` comes from `DΦ_{T₀}` fixing
  `v p` (`TauCeti.mfderiv_flowOf_apply_self`). Thus `N` and the monodromy have the same
  eigenvalues other than `1`
  (`TauCeti.hasEigenvalue_normalReturnDerivative_iff_hasEigenvalue_mfderiv_flowOf`).

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

section Return

variable (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hP : (T₀, p) ∈ flowDomain v) (hp : flowOf v T₀ p = p) (hg : ContMDiffAt I 𝓘(ℝ) 1 g p)
  (hgv : mvfderiv I g p (v p) ≠ 0)
include hv hP hp hg hgv

/-- **The monodromy and the normal return derivative.** If `p` returns to itself at time `T₀`, the
characteristic polynomial of the derivative `DΦ_{T₀}` at `p` of the time-`T₀` map of the flow is
`X - 1` times that of the normal return derivative of any transverse section through `p`. The
factor `X - 1` comes from `DΦ_{T₀}` fixing `v p` (`TauCeti.mfderiv_flowOf_apply_self`). -/
theorem charpoly_mfderiv_flowOf_eq_X_sub_one_mul
    {h : LinearMap.range (returnDerivative v g T₀ p) ≤
      LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)} :
    (mfderiv I I (flowOf v T₀) p).toLinearMap.charpoly =
      (X - 1) * (normalReturnDerivative v g T₀ p h).charpoly := by
  set K := LinearMap.ker (mvfderiv I g p : TangentSpace I p →ₗ[ℝ] ℝ)
  let Mo : Module.End ℝ (TangentSpace I p) := (mfderiv I I (flowOf v T₀) p).toLinearMap
  -- The tangent spaces at `flowOf v T₀ p` and at `p` are both the model space `E`, so
  -- `congrArg v hp` is a well-typed equation of vectors in `E`.
  have hfix : Mo (v p) = v p := (mfderiv_flowOf_apply_self hv hP).trans (congrArg v hp)
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
  have hconj : e.conj (L.mapQ L Mo hL) = normalReturnDerivative v g T₀ p h := by
    ext w
    have hform := mfderiv_flowTransition_apply hv hP (by rwa [hp]) (by rwa [hp]) w
    -- As in `hfix`, both tangent spaces are the model space `E`, so this rewrite is well typed.
    rw [congrArg v hp] at hform
    simp only [e, LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      Submodule.quotientEquivOfIsCompl_symm_apply, Submodule.mapQ_apply,
      Submodule.quotientEquivOfIsCompl_apply_mk]
    have hDP : returnDerivative v g T₀ p w ∈ K :=
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
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ L Mo hL, hres,
    LinearMap.charpoly_one, finrank_span_singleton hv0, pow_one, ← LinearEquiv.charpoly_conj e,
    hconj]

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

end Return

end TauCeti
