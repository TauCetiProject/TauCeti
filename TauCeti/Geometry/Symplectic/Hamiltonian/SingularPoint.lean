/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero
public import TauCeti.Geometry.Symplectic.LinearReduction
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Nondegenerate points of positive rank

Let `F : E → G` be a `C²` map on a finite-dimensional symplectic vector space `(E, ω)`, the local
model of an integrable system near a point `x`. Write `U = ker dF_x` and `W = U^ω` for its
symplectic complement. The Hamiltonian vectors `X_{ℓ ∘ F}(x)`, for linear functionals `ℓ` on `G`,
span `W` (`TauCeti.SymplecticForm.orthogonal_ker_fderiv`), so `U` is coisotropic, `W ⊆ U`,
exactly when the functions `ℓ ∘ F` Poisson-commute at `x`
(`TauCeti.SymplecticForm.isCoisotropic_ker_fderiv_iff`). The **transversal space** at `x` is then
the reduced space `U ⧸ W` of linear symplectic reduction (`TauCeti.SymplecticForm.ReducedSpace`).
If `dF_x` has rank `r` and `dim E = 2 n`, it is a symplectic vector space of dimension
`2 (n - r)` (`TauCeti.SymplecticForm.finrank_reducedSpace_ker_fderiv`).

For `ℓ` vanishing on the image of `dF_x`, the function `ℓ ∘ F` is critical at `x`, so its Hessian
is a well-defined quadratic form on `E`. When the functions `ℓ' ∘ F` Poisson-commute with `ℓ ∘ F`
on a neighbourhood of `x`, the derivative of `d(ℓ ∘ F)(X_{ℓ' ∘ F}) = 0` at `x` shows that the
vectors `X_{ℓ' ∘ F}(x)` lie in the radical of that Hessian
(`TauCeti.SymplecticForm.polar_hessianQuadraticForm_hamiltonianVectorField_eq_zero`). Hence the
whole of `W` does (`TauCeti.SymplecticForm.polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal`),
and the restriction of the Hessian to `U` descends to a quadratic form on the transversal space
(`TauCeti.SymplecticForm.reducedQuadraticForm`). These transversal Hessians are the rank-zero data
of the singular point in the directions transverse to the orbit of the local Hamiltonian action.

Following Eliasson and Bolsinov–Fomenko, `x` is a **nondegenerate point** of `F`
(`TauCeti.SymplecticForm.IsNondegeneratePoint`) when the transversal Hessians form a nondegenerate
family on the transversal space, that is, their Hamiltonian endomorphisms generate a Cartan
subalgebra of `sp(U ⧸ W)`. The definition records the descent of the Hessians as a field, which
holds automatically for Poisson-commuting components
(`TauCeti.SymplecticForm.isNondegeneratePoint_iff_of_poissonBracket`). It extends the rank-zero
notion: at a critical point the transversal space is `E` itself and the definition agrees with
`TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint`
(`TauCeti.SymplecticForm.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint`). At a regular
point of a Poisson-commuting family of maximal rank `n` the transversal space is zero and the
point is nondegenerate (`TauCeti.SymplecticForm.isNondegeneratePoint_of_two_mul_finrank_range`).
Williamson's classification of the rank-zero data on the transversal space into elliptic,
hyperbolic and focus-focus blocks is thereby the classification of nondegenerate points of rank
`r`.

## Main definitions

* `TauCeti.SymplecticForm.reducedQuadraticForm ω U Q hQ`: the quadratic form `[u] ↦ Q u` on the
  reduced space `U ⧸ (U ∩ U^ω)`, for a quadratic form `Q` whose polar form vanishes on
  `(U ∩ U^ω) × U`.
* `TauCeti.SymplecticForm.IsNondegeneratePoint ω F x`: the transversal Hessians of `F` at `x`
  form a nondegenerate family on the transversal space.

## Main results

* `TauCeti.SymplecticForm.orthogonal_ker_fderiv`: `(ker dF_x)^ω` is spanned by the vectors
  `X_{ℓ ∘ F}(x)`.
* `TauCeti.SymplecticForm.isCoisotropic_ker_fderiv_iff`: `ker dF_x` is coisotropic exactly when
  the functions `ℓ ∘ F` Poisson-commute at `x`.
* `TauCeti.SymplecticForm.finrank_reducedSpace_ker_fderiv`: the transversal space has dimension
  `dim E - 2 rank dF_x`.
* `TauCeti.SymplecticForm.polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal`: the Hessians of
  critical functions `ℓ ∘ F` vanish on `(ker dF_x)^ω` for Poisson-commuting components.
* `TauCeti.SymplecticForm.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint`: at a critical
  point, nondegeneracy is rank-zero nondegeneracy.
* `TauCeti.SymplecticForm.isNondegeneratePoint_of_two_mul_finrank_range`: regular points of
  maximal rank are nondegenerate.

## References

* L. H. Eliasson, *Normal forms for Hamiltonian systems with Poisson commuting integrals —
  elliptic case*, Commentarii Mathematici Helvetici 65 (1990), 4–35.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
-/

public section

noncomputable section

open Module Filter Topology

namespace TauCeti.SymplecticForm

/-! ### Quadratic forms on a reduced space -/

section Reduced

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (ω : SymplecticForm V) (U : Submodule ℝ V)

/-- The polar form of `Q` restricted to `U`, as a bilinear form on `U`, kills the kernel of the
restriction of `ω` to `U` on either side when the polar form of `Q` vanishes on
`(U ∩ U^ω) × U`. -/
private theorem polar_comp_subtype_eq_zero {Q : QuadraticForm ℝ V}
    (hQ : ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U, QuadraticMap.polar Q w u = 0) {w : U}
    (hw : w ∈ LinearMap.ker (ω.toBilinForm.restrict U)) (u : U) :
    QuadraticMap.polar (Q.comp U.subtype) w u = 0 := by
  rw [mem_ker_restrict_iff] at hw
  simpa [QuadraticMap.polar] using hQ w ⟨w.2, hw⟩ u u.2

/-- The **quadratic form induced on the reduced space** `U ⧸ (U ∩ U^ω)` by a quadratic form `Q` on
`V` whose polar form vanishes on `(U ∩ U^ω) × U`: the form `[u] ↦ Q u`. -/
def reducedQuadraticForm (Q : QuadraticForm ℝ V)
    (hQ : ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U, QuadraticMap.polar Q w u = 0) :
    QuadraticForm ℝ (ω.ReducedSpace U) :=
  (2⁻¹ : ℝ) • LinearMap.BilinMap.toQuadraticMap
    (LinearMap.liftQ₂ (LinearMap.ker (ω.toBilinForm.restrict U))
      (LinearMap.ker (ω.toBilinForm.restrict U)) (QuadraticMap.polarBilin (Q.comp U.subtype))
      (fun _ hw ↦ LinearMap.ext fun u ↦ polar_comp_subtype_eq_zero ω U hQ hw u)
      (fun _ hw ↦ LinearMap.ext fun u ↦ by
        simpa [QuadraticMap.polar_comm] using polar_comp_subtype_eq_zero ω U hQ hw u))

/-- The defining formula `Q_red [u] = Q u` of the induced quadratic form on the reduced space. -/
@[simp]
theorem reducedQuadraticForm_mk (Q : QuadraticForm ℝ V)
    (hQ : ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U, QuadraticMap.polar Q w u = 0) (u : U) :
    ω.reducedQuadraticForm U Q hQ (Submodule.Quotient.mk u) = Q u := by
  change (2⁻¹ : ℝ) * QuadraticMap.polar (Q.comp U.subtype) u u = Q u
  rw [QuadraticMap.polar_self, QuadraticMap.comp_apply, Submodule.subtype_apply, nsmul_eq_mul]
  ring

/-- The reduced space of the whole space is identified with `V` by a linear symplectomorphism. -/
private def reducedSpaceTopEquiv : V ≃ₗ[ℝ] ω.ReducedSpace (⊤ : Submodule ℝ V) :=
  Submodule.topEquiv.symm.trans (Submodule.quotEquivOfEqBot _ (by
    refine eq_bot_iff.2 fun u hu ↦ ?_
    rw [mem_ker_restrict_iff, orthogonal_top] at hu
    simpa [Submodule.mem_bot] using hu)).symm

private theorem reducedSpaceTopEquiv_apply (v : V) :
    reducedSpaceTopEquiv ω v = Submodule.Quotient.mk ⟨v, Submodule.mem_top⟩ :=
  (rfl)

private theorem isSymplectomorphism_reducedSpaceTopEquiv :
    IsSymplectomorphism ω (ω.reduction ⊤) (reducedSpaceTopEquiv ω) := by
  rw [isSymplectomorphism_iff]
  intro v w
  rw [reducedSpaceTopEquiv_apply, reducedSpaceTopEquiv_apply, reduction_mk]

end Reduced

/-! ### The symplectic complement of `ker dF_x` -/

section Kernel

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] (ω : SymplecticForm E) {F : E → G} {x : E}

omit [FiniteDimensional ℝ E] in
/-- The derivative of `ℓ ∘ F` at a point of differentiability of `F`. -/
private theorem fderiv_clm_comp (ℓ : G →L[ℝ] ℝ) (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (ℓ ∘ F) x = ℓ.comp (fderiv ℝ F x) :=
  (ℓ.hasFDerivAt.comp x hF.hasFDerivAt).fderiv

/-- The Hamiltonian vector `X_{ℓ ∘ F}(x)` pairs with `v` to `ℓ (dF_x v)`. -/
theorem apply_hamiltonianVectorField_comp (ℓ : G →L[ℝ] ℝ) (hF : DifferentiableAt ℝ F x) (v : E) :
    ω (ω.hamiltonianVectorField (ℓ ∘ F) x) v = ℓ (fderiv ℝ F x v) := by
  rw [apply_hamiltonianVectorField, fderiv_clm_comp ℓ hF, ContinuousLinearMap.comp_apply]

/-- The symplectic complement of the span of the Hamiltonian vectors `X_{ℓ ∘ F}(x)` is the kernel
of `dF_x`. -/
theorem orthogonal_span_hamiltonianVectorField_comp (hF : DifferentiableAt ℝ F x) :
    ω.orthogonal (Submodule.span ℝ
        (Set.range fun ℓ : G →L[ℝ] ℝ ↦ ω.hamiltonianVectorField (ℓ ∘ F) x)) =
      (fderiv ℝ F x).ker := by
  ext v
  rw [mem_orthogonal_iff, LinearMap.mem_ker]
  constructor
  · intro h
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
    change ℓ (fderiv ℝ F x v) = 0
    rw [← apply_hamiltonianVectorField_comp ω ℓ hF]
    exact h _ (Submodule.subset_span ⟨ℓ, rfl⟩)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ℓ, rfl⟩ := hy
      rw [apply_hamiltonianVectorField_comp ω ℓ hF]
      exact (congrArg ℓ h).trans (map_zero ℓ)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]

/-- **The symplectic complement of `ker dF_x`** is spanned by the Hamiltonian vectors
`X_{ℓ ∘ F}(x)` of the functions `ℓ ∘ F`, for `ℓ` a continuous linear functional on `G`. -/
theorem orthogonal_ker_fderiv (hF : DifferentiableAt ℝ F x) :
    ω.orthogonal ((fderiv ℝ F x).ker) =
      Submodule.span ℝ (Set.range fun ℓ : G →L[ℝ] ℝ ↦ ω.hamiltonianVectorField (ℓ ∘ F) x) := by
  rw [← orthogonal_span_hamiltonianVectorField_comp ω hF, orthogonal_orthogonal]

/-- **`ker dF_x` is coisotropic exactly when the functions `ℓ ∘ F` Poisson-commute at `x`.** -/
theorem isCoisotropic_ker_fderiv_iff (hF : DifferentiableAt ℝ F x) :
    ω.IsCoisotropic ((fderiv ℝ F x).ker) ↔
      ∀ ℓ ℓ' : G →L[ℝ] ℝ, ω.poissonBracket (ℓ ∘ F) (ℓ' ∘ F) x = 0 := by
  rw [isCoisotropic_iff_le, orthogonal_ker_fderiv ω hF, Submodule.span_le, Set.range_subset_iff]
  refine forall_congr' fun ℓ' ↦ ?_
  rw [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  -- `{ℓ' ∘ F, ℓ ∘ F}(x) = -ℓ (dF_x X_{ℓ' ∘ F}(x))`.
  have hbr : ∀ ℓ : G →L[ℝ] ℝ, ω.poissonBracket (ℓ' ∘ F) (ℓ ∘ F) x =
      -ℓ (fderiv ℝ F x (ω.hamiltonianVectorField (ℓ' ∘ F) x)) := fun ℓ ↦ by
    rw [poissonBracket_def, ← apply_hamiltonianVectorField_comp ω ℓ hF, ω.neg_eq]
  simp only [hbr, neg_eq_zero]
  exact ⟨fun h ℓ ↦ by rw [h, map_zero], SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)⟩

/-- **The dimension of the transversal space.** If the functions `ℓ ∘ F` Poisson-commute at `x`,
the reduced space of `ker dF_x` has dimension `dim E - 2 rank dF_x`; for `dim E = 2 n` and rank
`r` this is `2 (n - r)`. -/
theorem finrank_reducedSpace_ker_fderiv (hF : DifferentiableAt ℝ F x)
    (hcomm : ∀ ℓ ℓ' : G →L[ℝ] ℝ, ω.poissonBracket (ℓ ∘ F) (ℓ' ∘ F) x = 0) :
    finrank ℝ (ω.ReducedSpace ((fderiv ℝ F x).ker)) +
        2 * finrank ℝ ((fderiv ℝ F x).range) = finrank ℝ E := by
  have h := ((isCoisotropic_ker_fderiv_iff ω hF).2 hcomm).finrank_reducedSpace_add_finrank
  have h' := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ F x : E →ₗ[ℝ] G)
  omega

end Kernel

/-! ### Hessians of critical functions along Hamiltonian vectors -/

section Hessian

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] (ω : SymplecticForm E) {F : E → G} {x : E}

/-- **The Hamiltonian vector of a commuting function lies in the radical of the Hessian.** If `f`
is `C²` and critical at `x`, and `H` is `C²` at `x` and Poisson-commutes with `f` on a
neighbourhood of `x`, then the Hessian of `f` at `x` pairs `X_H(x)` with every vector to zero.
Indeed `df(X_H) = -{H, f}` vanishes near `x`, and its derivative at `x` is
`v ↦ D²f_x(v, X_H(x))` because `df_x = 0`. -/
theorem polar_hessianQuadraticForm_hamiltonianVectorField_eq_zero {f H : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : fderiv ℝ f x = 0) (hH : ContDiffAt ℝ 2 H x)
    (hHf : ω.poissonBracket H f =ᶠ[𝓝 x] 0) (v : E) :
    QuadraticMap.polar (hessianQuadraticForm f x) (ω.hamiltonianVectorField H x) v = 0 := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdH := (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hX : DifferentiableAt ℝ (ω.hamiltonianVectorField H) x := by
    have hdef : ω.hamiltonianVectorField H =
        fun y ↦ ω.toBilinForm.toContinuousBilinearMap.inverse (fderiv ℝ H y) :=
      funext (hamiltonianVectorField_def ω H)
    rw [hdef]
    exact (ω.toBilinForm.toContinuousBilinearMap.inverse.hasFDerivAt.comp x
      hdH.hasFDerivAt).differentiableAt
  -- The function `y ↦ df_y (X_H y) = -{H, f}(y)` vanishes near `x`.
  have hzero : (fun y ↦ fderiv ℝ f y (ω.hamiltonianVectorField H y)) =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [hHf] with y hy
    rw [← apply_hamiltonianVectorField, ← neg_eq_zero, ω.neg_eq]
    simpa [poissonBracket_def] using hy
  have hderiv := hdf.hasFDerivAt.clm_apply hX.hasFDerivAt
  rw [hzero.hasFDerivAt_iff, hfx, ContinuousLinearMap.zero_comp, zero_add] at hderiv
  have h0 := congr($((hasFDerivAt_const (0 : ℝ) x).unique hderiv) v)
  simp only [zero_apply, ContinuousLinearMap.flip_apply] at h0
  rw [QuadraticMap.polar]
  simp only [hessianQuadraticForm_apply, map_add, add_apply]
  rw [hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    (ω.hamiltonianVectorField H x) v, ← h0]
  ring

/-- **Hessians of critical components vanish on `(ker dF_x)^ω`.** Let `F` be `C²` at `x` and let
`ℓ` vanish on the image of `dF_x`. If every function `ℓ' ∘ F` Poisson-commutes with `ℓ ∘ F` on a
neighbourhood of `x`, then the Hessian of `ℓ ∘ F` at `x` pairs every vector of the symplectic
complement of `ker dF_x` with every vector to zero. -/
theorem polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal (hF : ContDiffAt ℝ 2 F x)
    {ℓ : G →L[ℝ] ℝ} (hℓ : ℓ.comp (fderiv ℝ F x) = 0)
    (hcomm : ∀ ℓ' : G →L[ℝ] ℝ, ω.poissonBracket (ℓ' ∘ F) (ℓ ∘ F) =ᶠ[𝓝 x] 0) {w : E}
    (hw : w ∈ ω.orthogonal ((fderiv ℝ F x).ker)) (v : E) :
    QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w v = 0 := by
  have hd := hF.differentiableAt (by norm_num)
  rw [orthogonal_ker_fderiv ω hd] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ℓ', rfl⟩ := hy
    exact ω.polar_hessianQuadraticForm_hamiltonianVectorField_eq_zero
      (ℓ.contDiff.contDiffAt.comp x hF) (by rw [fderiv_clm_comp ℓ hd, hℓ])
      (ℓ'.contDiff.contDiffAt.comp x hF) (hcomm ℓ') v
  | zero => simp
  | add y z _ _ hy hz => rw [QuadraticMap.polar_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [QuadraticMap.polar_smul_left, hy, smul_zero]

end Hessian

/-! ### Nondegenerate points -/

section Nondegenerate

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] (ω : SymplecticForm E)

/-- A point `x` is a **nondegenerate point** of a `C²` map `F : E → G` on a symplectic vector space
`(E, ω)` when, writing `U = ker dF_x`, the Hessians at `x` of the critical functions `ℓ ∘ F`, for
`ℓ` vanishing on the image of `dF_x`, descend to the transversal space `U ⧸ (U ∩ U^ω)` and form a
nondegenerate family there: their Hamiltonian endomorphisms generate a Cartan subalgebra of its
symplectic Lie algebra. The descent holds automatically when the functions `ℓ ∘ F`
Poisson-commute near `x` (`TauCeti.SymplecticForm.isNondegeneratePoint_iff_of_poissonBracket`).
At a critical point of `F` this is `TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint`. -/
structure IsNondegeneratePoint (F : E → G) (x : E) : Prop where
  /-- The map is `C²` at the point. -/
  contDiffAt : ContDiffAt ℝ 2 F x
  /-- The Hessians of the critical functions `ℓ ∘ F` vanish on
  `(U ∩ U^ω) × U` for `U = ker dF_x`, so they descend to the transversal space. -/
  polar_hessianQuadraticForm_eq_zero : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (fderiv ℝ F x) = 0 →
    ∀ w ∈ (fderiv ℝ F x).ker ⊓ ω.orthogonal ((fderiv ℝ F x).ker),
      ∀ u ∈ (fderiv ℝ F x).ker,
        QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0
  /-- The transversal Hessians form a nondegenerate family on the transversal space. -/
  isNondegenerateQuadraticFamily :
    (ω.reduction ((fderiv ℝ F x).ker)).IsNondegenerateQuadraticFamily
      fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
        ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.1 ∘ F) x)
          (polar_hessianQuadraticForm_eq_zero ℓ.1 ℓ.2)

variable {ω} {F : E → G} {x : E}

/-- Unbundled form of `IsNondegeneratePoint`, with the derivative `dF_x` replaced by any `T`
equal to it. -/
private theorem isNondegeneratePoint_iff_of_fderiv_eq {T : E →L[ℝ] G} (hT : fderiv ℝ F x = T) :
    ω.IsNondegeneratePoint F x ↔ ContDiffAt ℝ 2 F x ∧
      ∃ hQ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ T.ker ⊓ ω.orthogonal T.ker, ∀ u ∈ T.ker,
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0,
        (ω.reduction T.ker).IsNondegenerateQuadraticFamily
          fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦
            ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.1 ∘ F) x) (hQ ℓ.1 ℓ.2) := by
  subst hT
  exact ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- Being a nondegenerate point depends only on the germ of the map at the point. -/
theorem IsNondegeneratePoint.congr_of_eventuallyEq {F' : E → G}
    (h : ω.IsNondegeneratePoint F x) (hF : F =ᶠ[𝓝 x] F') : ω.IsNondegeneratePoint F' x := by
  have hH : ∀ ℓ : G →L[ℝ] ℝ, hessianQuadraticForm (ℓ ∘ F) x = hessianQuadraticForm (ℓ ∘ F') x :=
    fun ℓ ↦ hessianQuadraticForm_congr_of_eventuallyEq (hF.fun_comp ℓ)
  obtain ⟨h₁, h₂, h₃⟩ := (isNondegeneratePoint_iff_of_fderiv_eq rfl).1 h
  simp only [hH] at h₂ h₃
  exact (isNondegeneratePoint_iff_of_fderiv_eq hF.fderiv_eq.symm).2
    ⟨h₁.congr_of_eventuallyEq hF.symm, h₂, h₃⟩

/-- **Nondegeneracy for Poisson-commuting components.** When the functions `ℓ ∘ F` pairwise
Poisson-commute near `x`, the transversal Hessians descend automatically, and `x` is a
nondegenerate point exactly when they form a nondegenerate family on the transversal space. -/
theorem isNondegeneratePoint_iff_of_poissonBracket (hF : ContDiffAt ℝ 2 F x)
    (hcomm : ∀ ℓ ℓ' : G →L[ℝ] ℝ, ω.poissonBracket (ℓ' ∘ F) (ℓ ∘ F) =ᶠ[𝓝 x] 0) :
    ω.IsNondegeneratePoint F x ↔
      (ω.reduction ((fderiv ℝ F x).ker)).IsNondegenerateQuadraticFamily
        fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
          ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.1 ∘ F) x)
            fun _ hw _ _ ↦ ω.polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal hF ℓ.2
              (hcomm ℓ.1) hw.2 _ :=
  ⟨fun h ↦ h.isNondegenerateQuadraticFamily, fun h ↦ ⟨hF, fun ℓ hℓ _ hw _ _ ↦
    ω.polar_hessianQuadraticForm_eq_zero_of_mem_orthogonal hF hℓ (hcomm ℓ) hw.2 _, h⟩⟩

/-- **Regular points of maximal rank are nondegenerate.** If the functions `ℓ ∘ F` Poisson-commute
near `x` and `dF_x` has rank `n` on a `2 n`-dimensional space, the transversal space is zero and
`x` is a nondegenerate point. -/
theorem isNondegeneratePoint_of_two_mul_finrank_range (hF : ContDiffAt ℝ 2 F x)
    (hcomm : ∀ ℓ ℓ' : G →L[ℝ] ℝ, ω.poissonBracket (ℓ' ∘ F) (ℓ ∘ F) =ᶠ[𝓝 x] 0)
    (h : 2 * finrank ℝ (fderiv ℝ F x).range = finrank ℝ E) : ω.IsNondegeneratePoint F x := by
  have hd := ω.finrank_reducedSpace_ker_fderiv (hF.differentiableAt (by norm_num))
    fun ℓ ℓ' ↦ (hcomm ℓ' ℓ).self_of_nhds
  have : Subsingleton (ω.ReducedSpace (fderiv ℝ F x).ker) :=
    Module.finrank_zero_iff (R := ℝ).1 (by omega)
  exact (isNondegeneratePoint_iff_of_poissonBracket hF hcomm).2
    (isNondegenerateQuadraticFamily_of_subsingleton _)

/-- Over the whole space, nondegeneracy of a family of reduced quadratic forms is nondegeneracy of
the original family. -/
private theorem isNondegenerateQuadraticFamily_reduction_iff_of_eq_top {ι : Type*}
    {U : Submodule ℝ E} (hU : U = ⊤) (Q : ι → QuadraticForm ℝ E)
    (hQ : ∀ i, ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U, QuadraticMap.polar (Q i) w u = 0) :
    (ω.reduction U).IsNondegenerateQuadraticFamily
        (fun i ↦ ω.reducedQuadraticForm U (Q i) (hQ i)) ↔
      ω.IsNondegenerateQuadraticFamily Q := by
  subst hU
  rw [← isNondegenerateQuadraticFamily_comp_iff (isSymplectomorphism_reducedSpaceTopEquiv ω)]
  congr! with i
  ext v
  simp [reducedSpaceTopEquiv_apply]

/-- **Comparison with rank zero.** At a critical point of `F`, the transversal space is the whole
space and `x` is a nondegenerate point exactly when it is a nondegenerate rank-zero point. -/
theorem isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h : fderiv ℝ F x = 0) :
    ω.IsNondegeneratePoint F x ↔ ω.IsNondegenerateRankZeroPoint F x := by
  have hker : (fderiv ℝ F x).ker = ⊤ := by
    rw [h]
    exact LinearMap.ker_zero
  -- The descent condition is vacuous since `⊤ ∩ ⊤^ω = 0`.
  have hpolar : ∀ ℓ : G →L[ℝ] ℝ, ∀ w ∈ (fderiv ℝ F x).ker ⊓
      ω.orthogonal ((fderiv ℝ F x).ker), ∀ u ∈ (fderiv ℝ F x).ker,
        QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0 := by
    intro ℓ w hw u _
    rw [hker, orthogonal_top, inf_bot_eq, Submodule.mem_bot] at hw
    rw [hw, QuadraticMap.polar_zero_left]
  -- Every functional vanishes on the image of `dF_x = 0`.
  have hspan : Submodule.span ℝ (Set.range fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦
      hessianQuadraticForm (ℓ.1 ∘ F) x) =
      Submodule.span ℝ (Set.range fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ F) x) := by
    congr 1
    ext Q
    exact ⟨fun ⟨ℓ, hℓ⟩ ↦ ⟨ℓ.1, hℓ⟩,
      fun ⟨ℓ, hℓ⟩ ↦ ⟨⟨ℓ, by rw [h, ContinuousLinearMap.comp_zero]⟩, hℓ⟩⟩
  have key := (isNondegenerateQuadraticFamily_reduction_iff_of_eq_top hker _
    fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (fderiv ℝ F x) = 0} ↦ hpolar ℓ.1).trans
      (isNondegenerateQuadraticFamily_iff_of_span_eq hspan)
  exact ⟨fun hx ↦ ⟨hx.contDiffAt, h, key.1 hx.isNondegenerateQuadraticFamily⟩,
    fun hx ↦ ⟨hx.contDiffAt, fun ℓ _ ↦ hpolar ℓ, key.2 hx.isNondegenerateQuadraticFamily⟩⟩

end Nondegenerate

end TauCeti.SymplecticForm
