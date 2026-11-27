/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint
public import TauCeti.Geometry.Symplectic.Hamiltonian.SingularPoint.Williamson
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Nondegenerate points of positive rank on symplectic manifolds and their Williamson types

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M` and let `F : M → G` be a
map into a normed space, for instance the momentum map `F = (F₁, …, Fₙ) : M → ℝⁿ` of an integrable
system. At a point `x`, write `U = ker dF_x ⊆ T_x M`. For a linear functional `ℓ` on `G` vanishing
on the image of `dF_x`, the function `ℓ ∘ F` is critical at `x`, so its Hessian is an intrinsic
quadratic form on `T_x M` (`TauCeti.criticalHessian`). Following Eliasson and Bolsinov–Fomenko,
`x` is a **nondegenerate point** of `F`
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegeneratePoint`) when these Hessians descend to the
**transversal space** `U ⧸ (U ∩ U^σ)`, the linear symplectic reduction of `(T_x M, σ_x)` along
`U`, and form a nondegenerate family there: their Hamiltonian endomorphisms generate a Cartan
subalgebra of its symplectic Lie algebra. At a critical point the transversal space is all of
`T_x M`, and the notion is that of a nondegenerate rank-zero point.

This file transfers the linear notion `TauCeti.SymplecticForm.IsNondegeneratePoint`, which lives on
a symplectic vector space, to manifolds, and shows that it is intrinsic.

* On a boundaryless manifold, in the preferred chart at `x`, the notion is the linear one for the
  coordinate expression of `F` and the value of `σ` at `x`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_iff_comp_extChartAt_symm`).
* It is invariant under symplectic changes of coordinates: for boundaryless manifolds `M` and
  `N`, if `φ : N → M` is `C²` at `y`, has invertible differential there and pulls `σ` back to `τ`
  at `y`, then for `F` which is `C²` at `φ y`, the point `y` is a nondegenerate point of `F ∘ φ`
  for `τ` exactly when `φ y` is one of `F` for `σ`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_comp_right_iff`). The differential
  `dφ_y` is a linear symplectomorphism carrying `ker d(F ∘ φ)_y` onto `ker dF_(φ y)`, so it induces
  a symplectomorphism of transversal spaces
  (`TauCeti.SymplecticForm.reducedSpaceCongr`), and the second-order chain rule at a critical point
  (`TauCeti.criticalHessian_comp_apply`) identifies the transversal Hessians through it. The same
  holds for a parametrization `φ : E' → M` by a symplectic vector space `(E', ω₀)`, such as a
  Darboux chart, with the linear notion on the source
  (`TauCeti.SymplecticForm.isNondegeneratePoint_comp_right_iff`), so nondegeneracy may be checked
  in any symplectic coordinates.
* It depends only on the germ of `F`, and on a boundaryless manifold, at a critical point of `F`
  it is nondegeneracy of rank zero
  (`IsNondegenerate.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint`, in the namespace
  `TauCeti.SmoothTwoForm`). Since `dφ_y` is invertible, `y` is critical for `F ∘ φ` exactly when
  `φ y` is critical for `F` (`TauCeti.mvfderiv_comp_eq_zero_iff_of_isInvertible`), so the
  invariance of nondegenerate rank-zero points under symplectic changes of coordinates follows
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegenerateRankZeroPoint_comp_right_iff` and
  `TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_comp_right_iff`).

By Williamson's classification on the transversal space, a nondegenerate point `x` has a
**Williamson type** `(k_e, k_h, k_f)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.HasWilliamsonTypeAt hσ F x k_e k_h k_f`): in suitable
Darboux coordinates of the transversal space the transversal Hessians span the same space as `k_e`
elliptic blocks, `k_h` hyperbolic blocks and `k_f` focus-focus pairs. Every nondegenerate point has
a type and the type is unique
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegeneratePoint.exists_hasWilliamsonTypeAt`,
`TauCeti.SmoothTwoForm.IsNondegenerate.HasWilliamsonTypeAt.unique`). If `ker dF_x` is coisotropic,
as it is for Poisson-commuting components, `dF_x` has rank `r` and `dim M = 2 n`, then
`k_e + k_h + 2 k_f = n - r` (`HasWilliamsonTypeAt.two_mul_add_add_add_finrank_range_eq_finrank`,
in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`); at a critical point
`k_e + k_h + 2 k_f = n` (`HasWilliamsonTypeAt.two_mul_add_add_eq_finrank_of_mvfderiv_eq_zero`).
Like nondegeneracy, the type is intrinsic.

* On a boundaryless manifold, in the preferred chart at `x`, it is the linear type
  `TauCeti.SymplecticForm.HasWilliamsonTypeAt` of the coordinate expression of `F`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasWilliamsonTypeAt_iff_comp_extChartAt_symm`).
* It is invariant under symplectic changes of coordinates: with `φ` as above, `y` has type
  `(k_e, k_h, k_f)` for `F ∘ φ` exactly when `φ y` has this type for `F`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasWilliamsonTypeAt_comp_right_iff`), and the same holds
  for a parametrization by a symplectic vector space, such as a Darboux chart
  (`TauCeti.SymplecticForm.hasWilliamsonTypeAt_comp_right_iff`). The proof is that of the
  invariance of nondegeneracy: the symplectomorphism of transversal spaces induced by `dφ_y`
  carries one family of transversal Hessians to the other, and the Williamson type of a family is
  invariant under symplectomorphisms.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegeneratePoint hσ F x`: `F` is `C²` at `x` and the
  critical Hessians of the functions `ℓ ∘ F`, for `ℓ` vanishing on the image of `dF_x`, descend to
  the transversal space at `x` and form a nondegenerate family there.
* `TauCeti.SmoothTwoForm.IsNondegenerate.HasWilliamsonTypeAt hσ F x k_e k_h k_f`: `x` is a
  nondegenerate point of `F` whose transversal Hessians have Williamson type `(k_e, k_h, k_f)`.

## References

* L. H. Eliasson, *Normal forms for Hamiltonian systems with Poisson commuting integrals —
  elliptic case*, Commentarii Mathematici Helvetici 65 (1990), 4–35.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
-/

public section

noncomputable section

open Function Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### Nondegenerate points on manifolds -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace SmoothTwoForm.IsNondegenerate

variable (hσ : σ.IsNondegenerate)

/-- A point `x` is a **nondegenerate point** of a map `F : M → G` for a nondegenerate two-form `σ`
when `F` is `C²` at `x` and, writing `U = ker dF_x`, the critical Hessians at `x` of the functions
`ℓ ∘ F`, for `ℓ` vanishing on the image of `dF_x`, descend to the transversal space
`U ⧸ (U ∩ U^σ)` of `(T_x M, σ_x)` and form a nondegenerate family there: their Hamiltonian
endomorphisms generate a Cartan subalgebra of its symplectic Lie algebra. On a boundaryless
manifold, in the preferred chart this is `TauCeti.SymplecticForm.IsNondegeneratePoint`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isNondegeneratePoint_iff_comp_extChartAt_symm`), and at a
critical point of `F` it is
`TauCeti.SmoothTwoForm.IsNondegenerate.IsNondegenerateRankZeroPoint`. -/
structure IsNondegeneratePoint (F : M → G) (x : M) : Prop where
  /-- The map is `C²` at the point. -/
  contMDiffAt : ContMDiffAt I 𝓘(ℝ, G) 2 F x
  /-- The critical Hessians of the functions `ℓ ∘ F` with `ℓ ∘ dF_x = 0` vanish on
  `(U ∩ U^σ) × U` for `U = ker dF_x`, so they descend to the transversal space. -/
  polar_criticalHessian_eq_zero : ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (mvfderiv I F x) = 0 →
    ∀ w ∈ (mvfderiv I F x).ker ⊓ (hσ.symplecticFormAt x).orthogonal (mvfderiv I F x).ker,
      ∀ u ∈ (mvfderiv I F x).ker,
        QuadraticMap.polar (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap w u = 0
  /-- The transversal Hessians form a nondegenerate family on the transversal space. -/
  isNondegenerateQuadraticFamily :
    ((hσ.symplecticFormAt x).reduction (mvfderiv I F x).ker).IsNondegenerateQuadraticFamily
      fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (mvfderiv I F x) = 0} ↦
        (hσ.symplecticFormAt x).reducedQuadraticForm _
          (criticalHessian I (ℓ.val ∘ F) x).toBilinForm.toQuadraticMap
          (polar_criticalHessian_eq_zero ℓ.val ℓ.property)

variable {hσ} {F : M → G} {x : M}

/-- The manifold notion of a nondegenerate point, unbundled: `F` is `C²` at `x` and the
differential `dF_x` and the critical Hessians of the functions `ℓ ∘ F` are transversally
nondegenerate for `σ` at `x`. This is the manifold counterpart of
`TauCeti.SymplecticForm.isNondegeneratePoint_iff_of_fderiv_eq`. -/
theorem isNondegeneratePoint_iff_isTransversallyNondegenerate :
    hσ.IsNondegeneratePoint F x ↔ ContMDiffAt I 𝓘(ℝ, G) 2 F x ∧
      SymplecticForm.IsTransversallyNondegenerate (hσ.symplecticFormAt x) (mvfderiv I F x)
        fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap :=
  ⟨fun h ↦ ⟨h.contMDiffAt, h.polar_criticalHessian_eq_zero, h.isNondegenerateQuadraticFamily⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- Being a nondegenerate point depends only on the germ of the map at the point. -/
theorem IsNondegeneratePoint.congr_of_eventuallyEq {F' : M → G}
    (h : hσ.IsNondegeneratePoint F x) (hF : F =ᶠ[𝓝 x] F') : hσ.IsNondegeneratePoint F' x := by
  obtain ⟨h₁, h₂⟩ := isNondegeneratePoint_iff_isTransversallyNondegenerate.1 h
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F') x).toBilinForm.toQuadraticMap :=
    funext fun ℓ ↦ by rw [criticalHessian_congr_of_eventuallyEq (hF.fun_comp ℓ)]
  rw [hQ, hF.mvfderiv_eq] at h₂
  exact isNondegeneratePoint_iff_isTransversallyNondegenerate.2
    ⟨h₁.congr_of_eventuallyEq hF.symm, h₂⟩

/-! ### The Williamson type of a point -/

variable {kₑ kₕ k_f : ℕ}

variable (hσ) in
/-- A point `x` has **Williamson type** `(kₑ, kₕ, k_f)` for a map `F : M → G` and a nondegenerate
two-form `σ` when it is a nondegenerate point of `F` and the family of transversal Hessians, the
critical Hessians at `x` of the functions `ℓ ∘ F` with `ℓ ∘ dF_x = 0` descended to the transversal
space `U ⧸ (U ∩ U^σ)`, `U = ker dF_x`, has Williamson type `(kₑ, kₕ, k_f)`: in suitable Darboux
coordinates of the transversal space it spans the same space as `kₑ` elliptic blocks, `kₕ`
hyperbolic blocks and `k_f` focus-focus pairs. On a boundaryless manifold, in the preferred chart
this is `TauCeti.SymplecticForm.HasWilliamsonTypeAt`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasWilliamsonTypeAt_iff_comp_extChartAt_symm`). -/
def HasWilliamsonTypeAt (F : M → G) (x : M) (kₑ kₕ k_f : ℕ) : Prop :=
  ∃ h : hσ.IsNondegeneratePoint F x,
    ((hσ.symplecticFormAt x).reduction (mvfderiv I F x).ker).HasWilliamsonType
      (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (mvfderiv I F x) = 0} ↦
        (hσ.symplecticFormAt x).reducedQuadraticForm _
          (criticalHessian I (ℓ.val ∘ F) x).toBilinForm.toQuadraticMap
          (h.polar_criticalHessian_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f

/-- Unfolding `HasWilliamsonTypeAt`. -/
theorem hasWilliamsonTypeAt_iff :
    hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ∃ h : hσ.IsNondegeneratePoint F x,
      ((hσ.symplecticFormAt x).reduction (mvfderiv I F x).ker).HasWilliamsonType
        (fun ℓ : {ℓ : G →L[ℝ] ℝ // ℓ.comp (mvfderiv I F x) = 0} ↦
          (hσ.symplecticFormAt x).reducedQuadraticForm _
            (criticalHessian I (ℓ.val ∘ F) x).toBilinForm.toQuadraticMap
            (h.polar_criticalHessian_eq_zero ℓ.val ℓ.property)) kₑ kₕ k_f :=
  Iff.rfl

/-- The manifold notion of the Williamson type of a point, unbundled: `F` is `C²` at `x` and the
differential `dF_x` and the critical Hessians of the functions `ℓ ∘ F` have Williamson type
`(kₑ, kₕ, k_f)` for `σ` at `x`. This is the manifold counterpart of
`TauCeti.SymplecticForm.hasWilliamsonTypeAt_iff_of_fderiv_eq`. -/
theorem hasWilliamsonTypeAt_iff_hasTransversalWilliamsonType :
    hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔ ContMDiffAt I 𝓘(ℝ, G) 2 F x ∧
      SymplecticForm.HasTransversalWilliamsonType (hσ.symplecticFormAt x) (mvfderiv I F x)
        (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap)
        kₑ kₕ k_f :=
  ⟨fun ⟨h, ht⟩ ↦ ⟨h.contMDiffAt, SymplecticForm.hasTransversalWilliamsonType_iff.2
      ⟨⟨h.polar_criticalHessian_eq_zero, h.isNondegenerateQuadraticFamily⟩, ht⟩⟩,
    fun ⟨h₁, h⟩ ↦
      let ⟨⟨h₂, h₃⟩, ht⟩ := SymplecticForm.hasTransversalWilliamsonType_iff.1 h
      ⟨⟨h₁, h₂, h₃⟩, ht⟩⟩

/-- A point with a Williamson type is a nondegenerate point. -/
theorem HasWilliamsonTypeAt.isNondegeneratePoint (h : hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f) :
    hσ.IsNondegeneratePoint F x :=
  h.1

/-- **Existence of the Williamson type of a nondegenerate point.** Every nondegenerate point of `F`
has a Williamson type: by Williamson's classification on the transversal space, its transversal
Hessians span the same space as elliptic, hyperbolic and focus-focus blocks. -/
theorem IsNondegeneratePoint.exists_hasWilliamsonTypeAt (h : hσ.IsNondegeneratePoint F x) :
    ∃ kₑ kₕ k_f, hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f :=
  let ⟨kₑ, kₕ, k_f, ht⟩ := h.isNondegenerateQuadraticFamily.exists_hasWilliamsonType
  ⟨kₑ, kₕ, k_f, h, ht⟩

/-- A point is nondegenerate exactly when it has a Williamson type. -/
theorem isNondegeneratePoint_iff_exists_hasWilliamsonTypeAt :
    hσ.IsNondegeneratePoint F x ↔ ∃ kₑ kₕ k_f, hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f :=
  ⟨IsNondegeneratePoint.exists_hasWilliamsonTypeAt,
    fun ⟨_, _, _, h⟩ ↦ h.isNondegeneratePoint⟩

/-- **Uniqueness of the Williamson type of a point.** The numbers of elliptic, hyperbolic and
focus-focus components of a nondegenerate point of a map on a symplectic manifold are well
defined. -/
theorem HasWilliamsonTypeAt.unique {kₑ' kₕ' k_f' : ℕ} (h : hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f)
    (h' : hσ.HasWilliamsonTypeAt F x kₑ' kₕ' k_f') : kₑ = kₑ' ∧ kₕ = kₕ' ∧ k_f = k_f' :=
  h.2.unique h'.2

/-- **The Williamson type and the rank.** If `ker dF_x` is coisotropic for `σ` at `x`, as it is
when the functions `ℓ ∘ F` Poisson-commute at `x`, a point of Williamson type `(kₑ, kₕ, k_f)` at
which `dF_x` has rank `r` on a manifold modelled on a space of dimension `2 n` satisfies
`kₑ + kₕ + 2 k_f = n - r`: the transversal space has dimension `2 (n - r)`. -/
theorem HasWilliamsonTypeAt.two_mul_add_add_add_finrank_range_eq_finrank
    (h : hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f)
    (hU : (hσ.symplecticFormAt x).IsCoisotropic (mvfderiv I F x).ker) :
    2 * (kₑ + kₕ + 2 * k_f + finrank ℝ (mvfderiv I F x).range) = finrank ℝ E := by
  have hd : finrank ℝ ((hσ.symplecticFormAt x).ReducedSpace (mvfderiv I F x).ker) +
      finrank ℝ E = 2 * finrank ℝ (mvfderiv I F x).ker := hU.finrank_reducedSpace_add_finrank
  have hr : finrank ℝ (mvfderiv I F x).range + finrank ℝ (mvfderiv I F x).ker = finrank ℝ E :=
    LinearMap.finrank_range_add_finrank_ker (mvfderiv I F x : TangentSpace I x →ₗ[ℝ] G)
  have ht := h.2.two_mul_add_add_eq_finrank
  omega

/-- **The Williamson type of a critical point fills the dimension.** On a manifold modelled on a
space of dimension `2 n`, a critical point of `F` of Williamson type `(kₑ, kₕ, k_f)` satisfies
`kₑ + kₕ + 2 k_f = n`. -/
theorem HasWilliamsonTypeAt.two_mul_add_add_eq_finrank_of_mvfderiv_eq_zero
    (h : hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f) (h0 : mvfderiv I F x = 0) :
    2 * (kₑ + kₕ + 2 * k_f) = finrank ℝ E := by
  -- At a critical point the kernel is the whole tangent space, which is coisotropic, and the
  -- rank is zero.
  have hU : (mvfderiv I F x).ker = ⊤ := by
    rw [h0]
    exact LinearMap.ker_zero
  have hr : finrank ℝ (mvfderiv I F x).range = 0 := by
    simp [h0]
  simpa [hr] using h.two_mul_add_add_add_finrank_range_eq_finrank
    (hU ▸ SymplecticForm.isCoisotropic_top)

/-- The Williamson type of a point depends only on the germ of the map at the point. -/
theorem HasWilliamsonTypeAt.congr_of_eventuallyEq {F' : M → G}
    (h : hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f) (hF : F =ᶠ[𝓝 x] F') :
    hσ.HasWilliamsonTypeAt F' x kₑ kₕ k_f := by
  obtain ⟨h₁, h₂⟩ := hasWilliamsonTypeAt_iff_hasTransversalWilliamsonType.1 h
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F') x).toBilinForm.toQuadraticMap :=
    funext fun ℓ ↦ by rw [criticalHessian_congr_of_eventuallyEq (hF.fun_comp ℓ)]
  rw [hQ, hF.mvfderiv_eq] at h₂
  exact hasWilliamsonTypeAt_iff_hasTransversalWilliamsonType.2
    ⟨h₁.congr_of_eventuallyEq hF.symm, h₂⟩

section Boundaryless

variable [I.Boundaryless]

/-- **Nondegenerate points in the preferred chart.** On a boundaryless manifold, `x` is a
nondegenerate point of `F` exactly when the chart image of `x` is a nondegenerate point, in the
linear sense, of the coordinate expression of `F` in the preferred chart at `x`, for the value of
`σ` at `x` read on the model space. -/
theorem isNondegeneratePoint_iff_comp_extChartAt_symm :
    hσ.IsNondegeneratePoint F x ↔
      SymplecticForm.IsNondegeneratePoint (E := E) (hσ.symplecticFormAt x)
        (F ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦
        hessianQuadraticForm (ℓ ∘ F ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    funext fun ℓ ↦ by rw [toQuadraticMap_toBilinForm_criticalHessian, Function.comp_assoc]
  rw [isNondegeneratePoint_iff_isTransversallyNondegenerate, hQ,
    mvfderiv_eq_fderiv_comp_extChartAt_symm, contMDiffAt_iff_contDiffAt_comp_extChartAt_symm]
  exact (SymplecticForm.isNondegeneratePoint_iff_of_fderiv_eq rfl).symm

/-- **Comparison with rank zero.** On a boundaryless manifold, at a critical point of `F` the
transversal space is the whole tangent space, and `x` is a nondegenerate point exactly when it is
a nondegenerate rank-zero point. -/
theorem isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h : mvfderiv I F x = 0) :
    hσ.IsNondegeneratePoint F x ↔ hσ.IsNondegenerateRankZeroPoint F x := by
  rw [isNondegeneratePoint_iff_comp_extChartAt_symm,
    isNondegenerateRankZeroPoint_iff_comp_extChartAt_symm]
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm] at h
  exact SymplecticForm.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h

/-- **The Williamson type in the preferred chart.** On a boundaryless manifold, `x` has Williamson
type `(kₑ, kₕ, k_f)` for `F` exactly when the chart image of `x` has this type, in the linear
sense, for the coordinate expression of `F` in the preferred chart at `x` and the value of `σ` at
`x` read on the model space. -/
theorem hasWilliamsonTypeAt_iff_comp_extChartAt_symm :
    hσ.HasWilliamsonTypeAt F x kₑ kₕ k_f ↔
      SymplecticForm.HasWilliamsonTypeAt (E := E) (hσ.symplecticFormAt x)
        (F ∘ (extChartAt I x).symm) (extChartAt I x x) kₑ kₕ k_f := by
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I (ℓ ∘ F) x).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦
        hessianQuadraticForm (ℓ ∘ F ∘ (extChartAt I x).symm) (extChartAt I x x) :=
    funext fun ℓ ↦ by rw [toQuadraticMap_toBilinForm_criticalHessian, Function.comp_assoc]
  rw [hasWilliamsonTypeAt_iff_hasTransversalWilliamsonType, hQ,
    mvfderiv_eq_fderiv_comp_extChartAt_symm, contMDiffAt_iff_contDiffAt_comp_extChartAt_symm]
  exact (SymplecticForm.hasWilliamsonTypeAt_iff_of_fderiv_eq rfl).symm

/-! ### Symplectic changes of coordinates -/

section Comp

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace N]
  [ChartedSpace H' N] {φ : N → M} {y : N}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The common core of the invariance theorems: if `φ` is `C²` at `y` with invertible differential
`dφ_y`, which carries a symplectic form `η` on `T_y N` to `σ` at `φ y`, and `F` is `C²` at `φ y`,
then `dφ_y` is a linear symplectomorphism through which the differential of `F ∘ φ` is that of
`F`, and the critical Hessians of the functions `ℓ ∘ F ∘ φ` are those of the functions `ℓ ∘ F`. -/
private theorem exists_isSymplectomorphism_of_comp_right
    (η : SymplecticForm (TangentSpace I' y)) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hη : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      η u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    ∃ e : TangentSpace I' y ≃L[ℝ] TangentSpace I (φ y),
      SymplecticForm.IsSymplectomorphism η (hσ.symplecticFormAt (φ y)) e.toLinearEquiv ∧
      mvfderiv I' (F ∘ φ) y = (mvfderiv I F (φ y)).comp (e : TangentSpace I' y →L[ℝ] _) ∧
      ∀ ℓ : G →L[ℝ] ℝ, ℓ.comp (mvfderiv I F (φ y)) = 0 →
        (criticalHessian I' (ℓ ∘ F ∘ φ) y).toBilinForm.toQuadraticMap =
          (criticalHessian I (ℓ ∘ F) (φ y)).toBilinForm.toQuadraticMap.comp e.toLinearEquiv := by
  obtain ⟨e, he⟩ := hinv
  have hFd : MDifferentiableAt I 𝓘(ℝ, G) F (φ y) := hF.mdifferentiableAt two_ne_zero
  have hφd : MDifferentiableAt I' I φ y := hφ.mdifferentiableAt two_ne_zero
  refine ⟨e, SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ by simp [← hη, ← he], ?_,
    fun ℓ hℓ ↦ ?_⟩
  -- The differential of `F ∘ φ` is `dF ∘ dφ`.
  · rw [mvfderiv_comp y hFd hφd, ← he]
  -- For `ℓ` killing the image of `dF`, the chain rule identifies the Hessians through `dφ_y`.
  have hcrit : φ y ∈ criticalPoints I (ℓ ∘ F) := mem_criticalPoints.2 <|
    ContinuousLinearMap.ext fun v ↦ by simpa [ℓ.mvfderiv_comp_apply hFd] using congr($hℓ v)
  rw [← Function.comp_assoc, toQuadraticMap_toBilinForm_criticalHessian_comp
    (ℓ.contMDiff.contMDiffAt.comp _ hF) hφ hcrit, ← he,
    ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- The Williamson type of `φ y` for `F`, read through `dφ_y` on the unbundled data of `F ∘ φ` at
`y`. -/
private theorem hasWilliamsonTypeAt_iff_comp_right_aux
    (η : SymplecticForm (TangentSpace I' y)) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hη : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      η u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    (ContMDiffAt I' 𝓘(ℝ, G) 2 (F ∘ φ) y ∧
      SymplecticForm.HasTransversalWilliamsonType η (mvfderiv I' (F ∘ φ) y)
        (fun ℓ : G →L[ℝ] ℝ ↦ (criticalHessian I' (ℓ ∘ F ∘ φ) y).toBilinForm.toQuadraticMap)
        kₑ kₕ k_f) ↔
      hσ.HasWilliamsonTypeAt F (φ y) kₑ kₕ k_f := by
  obtain ⟨e, hsymp, hT, hQ⟩ := exists_isSymplectomorphism_of_comp_right η hφ hinv hη hF
  rw [hT, SymplecticForm.hasTransversalWilliamsonType_comp_iff e hsymp _ hQ,
    hasWilliamsonTypeAt_iff_hasTransversalWilliamsonType]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨hF, h⟩, fun ⟨_, h⟩ ↦ ⟨hF.comp y hφ, h⟩⟩

/-- **Invariance of the Williamson type under symplectic changes of coordinates.** Let `M` be
boundaryless, let `τ` be a nondegenerate two-form on a boundaryless manifold `N` and let
`φ : N → M` be `C²` at `y`, with invertible differential there, pulling `σ` back to `τ` at `y`.
For `F` which is `C²` at `φ y`, the point `y` has Williamson type `(kₑ, kₕ, k_f)` for `F ∘ φ` and
`τ` exactly when `φ y` has this type for `F` and `σ`. -/
theorem hasWilliamsonTypeAt_comp_right_iff [IsManifold I' ∞ N] {τ : SmoothTwoForm I' N}
    (hτ : τ.IsNondegenerate) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hστ : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      SmoothBundleForm.eval₂ τ y u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    hτ.HasWilliamsonTypeAt (F ∘ φ) y kₑ kₕ k_f ↔ hσ.HasWilliamsonTypeAt F (φ y) kₑ kₕ k_f := by
  refine Iff.trans ?_ (hasWilliamsonTypeAt_iff_comp_right_aux (hτ.symplecticFormAt y) hφ hinv
    (fun u w ↦ (hστ u w).trans (symplecticFormAt_apply hτ y u w).symm) hF)
  exact hasWilliamsonTypeAt_iff_hasTransversalWilliamsonType

/-- **The Williamson type in symplectic coordinates.** Let `φ : E' → M` be a map from a symplectic
vector space `(E', ω₀)` into the boundaryless manifold `M`, such as the inverse of a Darboux chart,
which is `C²` at `y`, has invertible differential there and pulls `σ` back to `ω₀` at `y`. For `F`
which is `C²` at `φ y`, the point `y` has Williamson type `(kₑ, kₕ, k_f)` for the coordinate
expression `F ∘ φ`, in the linear sense, exactly when `φ y` has this type for `F`. -/
theorem _root_.TauCeti.SymplecticForm.hasWilliamsonTypeAt_comp_right_iff
    (ω₀ : SymplecticForm E') {φ : E' → M} {y : E'} (hφ : ContMDiffAt 𝓘(ℝ, E') I 2 φ y)
    (hinv : (mfderiv 𝓘(ℝ, E') I φ y).IsInvertible)
    (hσω : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv 𝓘(ℝ, E') I φ y u)
      (mfderiv 𝓘(ℝ, E') I φ y w) = ω₀ u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    ω₀.HasWilliamsonTypeAt (F ∘ φ) y kₑ kₕ k_f ↔ hσ.HasWilliamsonTypeAt F (φ y) kₑ kₕ k_f := by
  refine Iff.trans ?_ (hasWilliamsonTypeAt_iff_comp_right_aux ω₀ hφ hinv hσω hF)
  -- On the model space, manifold smoothness, derivatives and Hessians are the usual ones.
  have hT : mvfderiv 𝓘(ℝ, E') (F ∘ φ) y = fderiv ℝ (F ∘ φ) y :=
    ContinuousLinearMap.ext fun v ↦ mvfderiv_eq_fderiv_apply _ y v
  have hQ : (fun ℓ : G →L[ℝ] ℝ ↦
      (criticalHessian 𝓘(ℝ, E') (ℓ ∘ F ∘ φ) y).toBilinForm.toQuadraticMap) =
      fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ (F ∘ φ)) y :=
    funext fun ℓ ↦ toQuadraticMap_toBilinForm_criticalHessian_modelSpace
  rw [SymplecticForm.hasWilliamsonTypeAt_iff_of_fderiv_eq rfl, hT, hQ,
    contMDiffAt_iff_contDiffAt]
  -- The two sides differ only in the instances on `E'` and on `TangentSpace 𝓘(ℝ, E') y`.
  exact Iff.rfl

/-- **Invariance under symplectic changes of coordinates.** Let `M` be boundaryless, let `τ` be a
nondegenerate two-form on a boundaryless manifold `N` and let `φ : N → M` be `C²` at `y`, with
invertible differential there, pulling `σ` back to `τ` at `y`. For `F` which is `C²` at `φ y`, the
point `y` is a nondegenerate point of `F ∘ φ` for `τ` exactly when `φ y` is one of `F` for `σ`. -/
theorem isNondegeneratePoint_comp_right_iff [IsManifold I' ∞ N] {τ : SmoothTwoForm I' N}
    (hτ : τ.IsNondegenerate) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hστ : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      SmoothBundleForm.eval₂ τ y u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    hτ.IsNondegeneratePoint (F ∘ φ) y ↔ hσ.IsNondegeneratePoint F (φ y) := by
  rw [isNondegeneratePoint_iff_exists_hasWilliamsonTypeAt,
    isNondegeneratePoint_iff_exists_hasWilliamsonTypeAt]
  exact exists₃_congr fun _ _ _ ↦ hasWilliamsonTypeAt_comp_right_iff hτ hφ hinv hστ hF

/-- **Nondegenerate points in symplectic coordinates.** Let `φ : E' → M` be a map from a symplectic
vector space `(E', ω₀)` into the boundaryless manifold `M`, such as the inverse of a Darboux chart,
which is `C²` at `y`, has invertible differential there and pulls `σ` back to `ω₀` at `y`. For `F`
which is `C²` at `φ y`, the point `y` is a nondegenerate point of the coordinate expression `F ∘ φ`,
in the linear sense, exactly when `φ y` is a nondegenerate point of `F`. -/
theorem _root_.TauCeti.SymplecticForm.isNondegeneratePoint_comp_right_iff
    (ω₀ : SymplecticForm E') {φ : E' → M} {y : E'} (hφ : ContMDiffAt 𝓘(ℝ, E') I 2 φ y)
    (hinv : (mfderiv 𝓘(ℝ, E') I φ y).IsInvertible)
    (hσω : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv 𝓘(ℝ, E') I φ y u)
      (mfderiv 𝓘(ℝ, E') I φ y w) = ω₀ u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    ω₀.IsNondegeneratePoint (F ∘ φ) y ↔ hσ.IsNondegeneratePoint F (φ y) := by
  rw [SymplecticForm.isNondegeneratePoint_iff_exists_hasWilliamsonTypeAt,
    isNondegeneratePoint_iff_exists_hasWilliamsonTypeAt]
  exact exists₃_congr fun _ _ _ ↦
    SymplecticForm.hasWilliamsonTypeAt_comp_right_iff ω₀ hφ hinv hσω hF

/-- **Invariance of rank-zero nondegeneracy under symplectic changes of coordinates.** Let `M` be
boundaryless, let `τ` be a nondegenerate two-form on a boundaryless manifold `N` and let
`φ : N → M` be `C²` at `y`, with invertible differential there, pulling `σ` back to `τ` at `y`.
For `F` which is `C²` at `φ y`, the point `y` is a nondegenerate rank-zero point of `F ∘ φ` for `τ`
exactly when `φ y` is one of `F` for `σ`. -/
theorem isNondegenerateRankZeroPoint_comp_right_iff [IsManifold I' ∞ N] {τ : SmoothTwoForm I' N}
    (hτ : τ.IsNondegenerate) (hφ : ContMDiffAt I' I 2 φ y)
    (hinv : (mfderiv I' I φ y).IsInvertible)
    (hστ : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv I' I φ y u) (mfderiv I' I φ y w) =
      SmoothBundleForm.eval₂ τ y u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    hτ.IsNondegenerateRankZeroPoint (F ∘ φ) y ↔ hσ.IsNondegenerateRankZeroPoint F (φ y) := by
  have h0 := mvfderiv_comp_eq_zero_iff_of_isInvertible (hF.mdifferentiableAt two_ne_zero) hinv
  by_cases h : mvfderiv I F (φ y) = 0
  · rw [← isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h0.2 h),
      ← isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h]
    exact isNondegeneratePoint_comp_right_iff hτ hφ hinv hστ hF
  · exact iff_of_false (fun h' ↦ h (h0.1 h'.mvfderiv_eq_zero)) fun h' ↦ h h'.mvfderiv_eq_zero

/-- **Nondegenerate rank-zero points in symplectic coordinates.** Let `φ : E' → M` be a map from a
symplectic vector space `(E', ω₀)` into the boundaryless manifold `M`, such as the inverse of a
Darboux chart, which is `C²` at `y`, has invertible differential there and pulls `σ` back to `ω₀`
at `y`. For `F` which is `C²` at `φ y`, the point `y` is a nondegenerate rank-zero point of the
coordinate expression `F ∘ φ`, in the linear sense, exactly when `φ y` is a nondegenerate rank-zero
point of `F`. -/
theorem _root_.TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_comp_right_iff
    (ω₀ : SymplecticForm E') {φ : E' → M} {y : E'} (hφ : ContMDiffAt 𝓘(ℝ, E') I 2 φ y)
    (hinv : (mfderiv 𝓘(ℝ, E') I φ y).IsInvertible)
    (hσω : ∀ u w, SmoothBundleForm.eval₂ σ (φ y) (mfderiv 𝓘(ℝ, E') I φ y u)
      (mfderiv 𝓘(ℝ, E') I φ y w) = ω₀ u w)
    (hF : ContMDiffAt I 𝓘(ℝ, G) 2 F (φ y)) :
    ω₀.IsNondegenerateRankZeroPoint (F ∘ φ) y ↔ hσ.IsNondegenerateRankZeroPoint F (φ y) := by
  -- On the model space, the manifold derivative is the usual one.
  have h0 : fderiv ℝ (F ∘ φ) y = 0 ↔ mvfderiv I F (φ y) = 0 := by
    rw [← mvfderiv_comp_eq_zero_iff_of_isInvertible (hF.mdifferentiableAt two_ne_zero) hinv]
    exact ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦
        (mvfderiv_eq_fderiv_apply _ y v).trans congr($h v),
      fun h ↦ ContinuousLinearMap.ext fun v ↦
        (mvfderiv_eq_fderiv_apply _ y v).symm.trans congr($h v)⟩
  by_cases h : mvfderiv I F (φ y) = 0
  · rw [← SymplecticForm.isNondegeneratePoint_iff_isNondegenerateRankZeroPoint (h0.2 h),
      ← isNondegeneratePoint_iff_isNondegenerateRankZeroPoint h]
    exact SymplecticForm.isNondegeneratePoint_comp_right_iff ω₀ hφ hinv hσω hF
  · exact iff_of_false (fun h' ↦ h (h0.1 h'.fderiv_eq_zero)) fun h' ↦ h h'.mvfderiv_eq_zero

end Comp

end Boundaryless

end SmoothTwoForm.IsNondegenerate

end TauCeti
