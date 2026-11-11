/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

Nondegeneracy is a property of the singular point, not of the chosen coordinates on the source
or target. Composing `F` with a `C²` map `g` whose differential at `F x` is injective changes
neither `ker dF_x` nor, on it, the Hessians of the critical functions
(`TauCeti.hessianQuadraticForm_comp_apply_of_fderiv_apply_eq_zero`), so `x` is a nondegenerate
point of `g ∘ F` exactly when it is one of `F`
(`TauCeti.SymplecticForm.isNondegeneratePoint_comp_iff`). Precomposing with a `C²` map `φ` whose
differential at `y` is a linear symplectomorphism, for instance a canonical transformation, pulls
the Hessians of the critical functions back along `dφ_y`, and `dφ_y` induces a symplectomorphism of
transversal spaces carrying one family of transversal Hessians to the other
(`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_reduction_comp_iff`). So `y` is a
nondegenerate point of `F ∘ φ` exactly when `φ y` is one of `F`
(`TauCeti.SymplecticForm.isNondegeneratePoint_comp_iff_of_isSymplectomorphism`), and likewise for
nondegenerate rank-zero points.

## Main definitions

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
* `TauCeti.SymplecticForm.isNondegeneratePoint_comp_iff`: invariance under reparametrization of
  the values.
* `TauCeti.SymplecticForm.isNondegeneratePoint_comp_iff_of_isSymplectomorphism`,
  `TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_comp_iff_of_isSymplectomorphism`:
  invariance under maps whose differential is a linear symplectomorphism, such as canonical
  transformations.

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

/-! ### The symplectic complement of `ker dF_x` -/

section Kernel

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] (ω : SymplecticForm E) {F : E → G} {x : E}

/-- The Hamiltonian vector `X_{ℓ ∘ F}(x)` pairs with `v` to `ℓ (dF_x v)`. -/
theorem apply_hamiltonianVectorField_comp (ℓ : G →L[ℝ] ℝ) (hF : DifferentiableAt ℝ F x) (v : E) :
    ω (ω.hamiltonianVectorField (ℓ ∘ F) x) v = ℓ (fderiv ℝ F x v) := by
  rw [apply_hamiltonianVectorField, fderiv_comp x ℓ.differentiableAt hF, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply]

/-- The symplectic complement of the span of the Hamiltonian vectors `X_{ℓ ∘ F}(x)` is the kernel
of `dF_x`. -/
theorem orthogonal_span_hamiltonianVectorField_comp (hF : DifferentiableAt ℝ F x) :
    ω.orthogonal (Submodule.span ℝ
        (Set.range fun ℓ : G →L[ℝ] ℝ ↦ ω.hamiltonianVectorField (ℓ ∘ F) x)) =
      (fderiv ℝ F x).ker := by
  ext v
  rw [mem_orthogonal_span_iff, Set.forall_mem_range, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe]
  simp only [apply_hamiltonianVectorField_comp ω _ hF]
  exact ⟨SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ), fun h ℓ ↦ by rw [h, map_zero]⟩

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
      (ℓ.contDiff.contDiffAt.comp x hF)
      (by rw [fderiv_comp x ℓ.differentiableAt hd, ContinuousLinearMap.fderiv, hℓ])
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
equal to it, its kernel by any `U` equal to `ker T`, and the critical functionals `ℓ` with
`ℓ ∘ T = 0` by those satisfying any predicate `p` equivalent to this. -/
private theorem isNondegeneratePoint_iff_of_fderiv_eq {T : E →L[ℝ] G} (hT : fderiv ℝ F x = T)
    {U : Submodule ℝ E} (hU : T.ker = U) {p : (G →L[ℝ] ℝ) → Prop}
    (hp : ∀ ℓ, p ℓ ↔ ℓ.comp T = 0) :
    ω.IsNondegeneratePoint F x ↔ ContDiffAt ℝ 2 F x ∧
      ∃ hQ : ∀ ℓ : G →L[ℝ] ℝ, p ℓ → ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U,
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0,
        (ω.reduction U).IsNondegenerateQuadraticFamily
          fun ℓ : {ℓ : G →L[ℝ] ℝ // p ℓ} ↦
            ω.reducedQuadraticForm _ (hessianQuadraticForm (ℓ.1 ∘ F) x) (hQ ℓ.1 ℓ.2) := by
  obtain rfl : p = fun ℓ ↦ ℓ.comp T = 0 := funext fun ℓ ↦ propext (hp ℓ)
  subst hT hU
  exact ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- Being a nondegenerate point depends only on the germ of the map at the point. -/
theorem IsNondegeneratePoint.congr_of_eventuallyEq {F' : E → G}
    (h : ω.IsNondegeneratePoint F x) (hF : F =ᶠ[𝓝 x] F') : ω.IsNondegeneratePoint F' x := by
  have hH : ∀ ℓ : G →L[ℝ] ℝ, hessianQuadraticForm (ℓ ∘ F) x = hessianQuadraticForm (ℓ ∘ F') x :=
    fun ℓ ↦ hessianQuadraticForm_congr_of_eventuallyEq (hF.fun_comp ℓ)
  obtain ⟨h₁, h₂, h₃⟩ := (isNondegeneratePoint_iff_of_fderiv_eq rfl rfl fun _ ↦ Iff.rfl).1 h
  simp only [hH] at h₂ h₃
  exact (isNondegeneratePoint_iff_of_fderiv_eq hF.fderiv_eq.symm rfl fun _ ↦ Iff.rfl).2
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

/-- **Invariance under reparametrization of the values.** Composing `F` with a `C²` map `g` whose
differential at `F x` is injective preserves and reflects nondegenerate points: the kernel of the
differential, and hence the transversal space, does not change, and the transversal Hessians of
`g ∘ F` are those of `F`. -/
theorem isNondegeneratePoint_comp_iff {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    [FiniteDimensional ℝ G'] {g : G → G'} (hg : ContDiffAt ℝ 2 g (F x))
    (hinj : Function.Injective (fderiv ℝ g (F x))) (hF : ContDiffAt ℝ 2 F x) :
    ω.IsNondegeneratePoint (g ∘ F) x ↔ ω.IsNondegeneratePoint F x := by
  set T := fderiv ℝ F x
  set D := fderiv ℝ g (F x)
  have hgF : fderiv ℝ (g ∘ F) x = D.comp T :=
    fderiv_comp x (hg.differentiableAt (by norm_num)) (hF.differentiableAt (by norm_num))
  have hker : (D.comp T).ker = T.ker := by
    ext v
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    exact ⟨fun h ↦ hinj (by rw [h, map_zero]), fun h ↦ by rw [h, map_zero]⟩
  -- On `ker dF_x` the Hessian of `ℓ' ∘ g ∘ F` is the Hessian of `(ℓ' ∘ Dg) ∘ F`.
  have hH : ∀ ℓ' : G' →L[ℝ] ℝ, ∀ u ∈ T.ker,
      hessianQuadraticForm (ℓ' ∘ g ∘ F) x u = hessianQuadraticForm (ℓ'.comp D ∘ F) x u := by
    intro ℓ' u hu
    rw [← Function.comp_assoc, hessianQuadraticForm_comp_apply_of_fderiv_apply_eq_zero
      (ℓ'.contDiff.contDiffAt.comp _ hg) hF (LinearMap.mem_ker.1 hu), fderiv_comp _
      ℓ'.differentiableAt (hg.differentiableAt (by norm_num)), ℓ'.fderiv]
  have hpolar : ∀ ℓ' : G' →L[ℝ] ℝ, ∀ w ∈ T.ker, ∀ u ∈ T.ker,
      QuadraticMap.polar (hessianQuadraticForm (ℓ' ∘ g ∘ F) x) w u =
        QuadraticMap.polar (hessianQuadraticForm (ℓ'.comp D ∘ F) x) w u := fun ℓ' w hw u hu ↦ by
    simp only [QuadraticMap.polar, hH ℓ' _ (add_mem hw hu), hH ℓ' w hw, hH ℓ' u hu]
  -- Every functional on `G` factors through `Dg`, so `ℓ' ↦ ℓ' ∘ Dg` maps the critical functionals
  -- of `g ∘ F` onto those of `F`.
  obtain ⟨h, hh⟩ := (D : G →ₗ[ℝ] G').exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  have hfac : ∀ ℓ : G →L[ℝ] ℝ, (ℓ.comp (LinearMap.toContinuousLinearMap h)).comp D = ℓ := by
    intro ℓ
    ext w
    simpa using congr(ℓ ($hh w))
  let f : {ℓ' : G' →L[ℝ] ℝ // ℓ'.comp (D.comp T) = 0} → {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} :=
    fun ℓ' ↦ ⟨ℓ'.1.comp D, by rw [ContinuousLinearMap.comp_assoc]; exact ℓ'.2⟩
  have hf : Function.Surjective f := fun ℓ ↦ ⟨⟨ℓ.1.comp (LinearMap.toContinuousLinearMap h), by
    rw [← ContinuousLinearMap.comp_assoc, hfac, ℓ.2]⟩, Subtype.ext (hfac ℓ.1)⟩
  -- The transversal Hessians of `g ∘ F` are those of `F`, reindexed along `f`.
  have hN : ∀ (hQ₁ : ∀ ℓ' : G' →L[ℝ] ℝ, ℓ'.comp (D.comp T) = 0 →
        ∀ w ∈ T.ker ⊓ ω.orthogonal T.ker, ∀ u ∈ T.ker,
          QuadraticMap.polar (hessianQuadraticForm (ℓ' ∘ g ∘ F) x) w u = 0)
      (hQ₂ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ T.ker ⊓ ω.orthogonal T.ker, ∀ u ∈ T.ker,
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0),
      (ω.reduction T.ker).IsNondegenerateQuadraticFamily
      (fun ℓ' : {ℓ' : G' →L[ℝ] ℝ // ℓ'.comp (D.comp T) = 0} ↦ ω.reducedQuadraticForm T.ker
        (hessianQuadraticForm (ℓ'.1 ∘ g ∘ F) x) (hQ₁ ℓ'.1 ℓ'.2)) ↔
      (ω.reduction T.ker).IsNondegenerateQuadraticFamily
        fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦ ω.reducedQuadraticForm T.ker
          (hessianQuadraticForm (ℓ.1 ∘ F) x) (hQ₂ ℓ.1 ℓ.2) := fun hQ₁ hQ₂ ↦ by
    refine isNondegenerateQuadraticFamily_iff_of_span_eq (congrArg _ ?_)
    rw [← hf.range_comp]
    exact congrArg Set.range
      (funext fun ℓ' ↦ reducedQuadraticForm_congr _ _ _ _ fun u hu ↦ hH ℓ'.1 u hu)
  rw [isNondegeneratePoint_iff_of_fderiv_eq hgF hker fun _ ↦ Iff.rfl,
    isNondegeneratePoint_iff_of_fderiv_eq rfl rfl fun _ ↦ Iff.rfl]
  refine ⟨fun ⟨_, hQ₁, h⟩ ↦ ?_, fun ⟨_, hQ₂, h⟩ ↦ ?_⟩
  · have hQ₂ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ T.ker ⊓ ω.orthogonal T.ker, ∀ u ∈ T.ker,
        QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) x) w u = 0 := by
      intro ℓ hℓ w hw u hu
      rw [← hfac ℓ, ← hpolar _ w hw.1 u hu]
      exact hQ₁ _ (by rw [← ContinuousLinearMap.comp_assoc, hfac, hℓ]) w hw u hu
    exact ⟨hF, hQ₂, (hN hQ₁ hQ₂).1 h⟩
  · have hQ₁ : ∀ ℓ' : G' →L[ℝ] ℝ, ℓ'.comp (D.comp T) = 0 → ∀ w ∈ T.ker ⊓ ω.orthogonal T.ker,
        ∀ u ∈ T.ker, QuadraticMap.polar (hessianQuadraticForm (ℓ' ∘ g ∘ F) x) w u = 0 := by
      intro ℓ' hℓ' w hw u hu
      rw [hpolar ℓ' w hw.1 u hu]
      exact hQ₂ _ (f ⟨ℓ', hℓ'⟩).2 w hw u hu
    exact ⟨hg.comp x hF, hQ₁, (hN hQ₁ hQ₂).2 h⟩

/-- **Invariance under canonical transformations.** Let `φ : E' → E` be `C²` at `y`, with
differential at `y` a linear symplectomorphism `e` from `(E', ω')` to `(E, ω)`. Then `y` is a
nondegenerate point of `F ∘ φ` for `ω'` exactly when `φ y` is a nondegenerate point of `F` for
`ω`: `e` carries the kernel of the differential of `F ∘ φ` onto that of `F`, and the transversal
Hessians of `F ∘ φ` are those of `F` pulled back along the induced symplectomorphism of
transversal spaces. Only the differential of `φ` at `y` enters, so this applies in particular to a
`C²` canonical transformation `φ`. -/
theorem isNondegeneratePoint_comp_iff_of_isSymplectomorphism {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {ω' : SymplecticForm E'}
    {φ : E' → E} {y : E'} {e : E' ≃ₗ[ℝ] E} (he : IsSymplectomorphism ω' ω e)
    (hφ : ContDiffAt ℝ 2 φ y) (hφe : ∀ v, fderiv ℝ φ y v = e v)
    (hF : ContDiffAt ℝ 2 F (φ y)) :
    ω'.IsNondegeneratePoint (F ∘ φ) y ↔ ω.IsNondegeneratePoint F (φ y) := by
  obtain ⟨T, hT⟩ : ∃ T, fderiv ℝ F (φ y) = T := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U', (T.comp (fderiv ℝ φ y)).ker = U' := ⟨_, rfl⟩
  have hFφ : fderiv ℝ (F ∘ φ) y = T.comp (fderiv ℝ φ y) := by
    rw [← hT]
    exact fderiv_comp y (hF.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num))
  have hU : U'.map (e : E' →ₗ[ℝ] E) = T.ker := by
    ext v
    simp [← hU', Submodule.mem_map_equiv, hφe]
  -- The critical functionals of `F ∘ φ` are those of `F`.
  have hcrit : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (T.comp (fderiv ℝ φ y)) = 0 ↔ ℓ.comp T = 0 := by
    refine fun ℓ ↦ ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ by
      rw [← ContinuousLinearMap.comp_assoc, h, ContinuousLinearMap.zero_comp]⟩
    simpa [hφe] using congr($h (e.symm v))
  -- At these functionals, the Hessian of `ℓ ∘ F ∘ φ` is the pullback of that of `ℓ ∘ F` along `e`.
  have hH : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → hessianQuadraticForm (ℓ ∘ F ∘ φ) y =
      (hessianQuadraticForm (ℓ ∘ F) (φ y)).comp (e : E' →ₗ[ℝ] E) := by
    intro ℓ hℓ
    have hd : fderiv ℝ (ℓ ∘ F) (φ y) = 0 := by
      rw [fderiv_comp _ ℓ.differentiableAt (hF.differentiableAt (by norm_num)), ℓ.fderiv, hT, hℓ]
    rw [← Function.comp_assoc, hessianQuadraticForm_comp (ℓ.contDiff.contDiffAt.comp _ hF) hφ hd]
    ext v
    simp [hφe]
  have hQ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ((∀ w ∈ U' ⊓ ω'.orthogonal U', ∀ u ∈ U',
      QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F ∘ φ) y) w u = 0) ↔
        ∀ w ∈ T.ker ⊓ ω.orthogonal T.ker, ∀ u ∈ T.ker,
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) (φ y)) w u = 0) := fun ℓ hℓ ↦ by
    rw [hH ℓ hℓ]
    exact forall_polar_comp_eq_zero_iff he hU _
  -- The transversal Hessians of `F ∘ φ` are those of `F` pulled back along `e`.
  have hN : ∀ (hQ₁ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ U' ⊓ ω'.orthogonal U', ∀ u ∈ U',
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F ∘ φ) y) w u = 0)
      (hQ₂ : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp T = 0 → ∀ w ∈ T.ker ⊓ ω.orthogonal T.ker, ∀ u ∈ T.ker,
          QuadraticMap.polar (hessianQuadraticForm (ℓ ∘ F) (φ y)) w u = 0),
      (ω'.reduction U').IsNondegenerateQuadraticFamily
      (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦ ω'.reducedQuadraticForm U'
        (hessianQuadraticForm (ℓ.1 ∘ F ∘ φ) y) (hQ₁ ℓ.1 ℓ.2)) ↔
      (ω.reduction T.ker).IsNondegenerateQuadraticFamily
        fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp T = 0} ↦ ω.reducedQuadraticForm T.ker
          (hessianQuadraticForm (ℓ.1 ∘ F) (φ y)) (hQ₂ ℓ.1 ℓ.2) := fun hQ₁ hQ₂ ↦ by
    rw [← isNondegenerateQuadraticFamily_reduction_comp_iff he hU]
    exact Iff.of_eq (congrArg _ (funext fun ℓ ↦
      reducedQuadraticForm_congr _ _ _ _ fun u _ ↦ by rw [hH ℓ.1 ℓ.2]))
  rw [isNondegeneratePoint_iff_of_fderiv_eq hFφ hU' fun ℓ ↦ (hcrit ℓ).symm,
    isNondegeneratePoint_iff_of_fderiv_eq hT rfl fun _ ↦ Iff.rfl]
  refine and_congr ⟨fun _ ↦ hF, fun _ ↦ hF.comp y hφ⟩ ⟨fun ⟨hQ₁, h⟩ ↦ ?_, fun ⟨hQ₂, h⟩ ↦ ?_⟩
  · have hQ₂ := fun ℓ hℓ ↦ (hQ ℓ hℓ).1 (hQ₁ ℓ hℓ)
    exact ⟨hQ₂, (hN hQ₁ hQ₂).1 h⟩
  · have hQ₁ := fun ℓ hℓ ↦ (hQ ℓ hℓ).2 (hQ₂ ℓ hℓ)
    exact ⟨hQ₁, (hN hQ₁ hQ₂).2 h⟩

/-- **Invariance of nondegenerate rank-zero points under canonical transformations.** If
`φ : E' → E` is `C²` at `y`, with differential at `y` a linear symplectomorphism `e` from
`(E', ω')` to `(E, ω)`, then `y` is a nondegenerate rank-zero point of `F ∘ φ` for `ω'` exactly when
`φ y` is a nondegenerate rank-zero point of `F` for `ω`. -/
theorem isNondegenerateRankZeroPoint_comp_iff_of_isSymplectomorphism {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {ω' : SymplecticForm E'}
    {φ : E' → E} {y : E'} {e : E' ≃ₗ[ℝ] E} (he : IsSymplectomorphism ω' ω e)
    (hφ : ContDiffAt ℝ 2 φ y) (hφe : ∀ v, fderiv ℝ φ y v = e v)
    (hF : ContDiffAt ℝ 2 F (φ y)) :
    ω'.IsNondegenerateRankZeroPoint (F ∘ φ) y ↔ ω.IsNondegenerateRankZeroPoint F (φ y) := by
  have h0 : fderiv ℝ (F ∘ φ) y = 0 ↔ fderiv ℝ F (φ y) = 0 := by
    rw [fderiv_comp y (hF.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num))]
    refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ by
      rw [h, ContinuousLinearMap.zero_comp]⟩
    simpa [hφe] using congr($h (e.symm v))
  have key := isNondegeneratePoint_comp_iff_of_isSymplectomorphism he hφ hφe hF
  exact ⟨fun h ↦ (isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h0.1 h.fderiv_eq_zero)).1
      (key.1 ((isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h.fderiv_eq_zero).2 h)),
    fun h ↦ (isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h0.2 h.fderiv_eq_zero)).1
      (key.2 ((isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h.fderiv_eq_zero).2 h))⟩

end Nondegenerate

end TauCeti.SymplecticForm
