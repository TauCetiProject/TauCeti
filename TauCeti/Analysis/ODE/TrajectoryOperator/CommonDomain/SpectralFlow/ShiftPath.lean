/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SpectralFlow.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.InnerProductSpace.LinearPMap.CommonDomain
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The index of the trajectory operator along a path of shifts

Let `ι : D →L[ℝ] H` be a compact operator from a Banach space into a real Hilbert space and
`B : D →L[ℝ] H` an operator symmetric through `ι`, `⟪B x, ι y⟫ = ⟪ι x, B y⟫`, such as the
asymptotic operator `J₀ ∂ₜ + S` of the Floer equation with `D = H¹` and `H = L²`. For a continuous
real function `λ` with limits `c₋` at `-∞` and `c₊` at `∞`, at which the shifts `B - c₋ ι` and
`B - c₊ ι` are invertible, consider the path of shifts `A(s) = B - λ(s) ι`. Its crossings are the
times `s` at which `λ(s)` is an eigenvalue of the pencil, `B x = λ(s) ι x` for some `x ≠ 0`. This
file proves the index formula of Robbin and Salamon for these paths: the operator
`D_A u = (ι ∘ u)' + A u` from `L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` has as its index the
spectral flow `TauCeti.domainSpectralFlow ι A a b` of `A` over `[a, b]`, for every `a` far enough
to the left and every `b` far enough to the right
(`eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow` in the namespace
`TauCeti.WeakDerivStep`).

**Proof.** The values of `λ` lie in a bounded set, which contains only finitely many eigenvalues of
the pencil (`ContinuousLinearMap.finite_inter_setOf_not_isInvertible_smul_sub`), each of finite
multiplicity (`ContinuousLinearMap.finiteDimensional_ker_smul_sub`). Their eigenvectors span a
finite-dimensional subspace `V` of `D`, on which `ι` is injective since eigenvectors for distinct
eigenvalues have orthogonal images (`ContinuousLinearMap.inner_eq_zero_of_apply_eq_smul`). Let
`F = ι V`, and let `D'` be the closed subspace of the `x` with `ι x ⊥ F`. Then `D = V ⊕ D'` and
`H = F ⊕ Fᗮ`, and by the symmetry of `B` each shift `B - c ι` is block diagonal for these
splittings: it is `B_F - c` on `F ≅ V` and `B' - c ι'` from `D'` to `Fᗮ`. The second block is
invertible for every value `c` of `λ`, since its kernel would consist of eigenvectors in `D'`.
So `A` is conjugate to the direct sum of a path of symmetric operators on the finite-dimensional
space `F` and a path of invertible operators, for which the formula is
`eventually_index_familyDomainTrajectoryOperator_withLpProdMap_eq_domainSpectralFlow` in the
namespace `TauCeti.WeakDerivStep`, and the formula transports along the conjugation
(`eventually_index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_comp_comp_symm` in the
namespace `TauCeti.WeakDerivStep`).

These paths are the local model of the formula for general paths: a path `A` with invertible ends
is homotopic, with fixed ends, to a staircase whose horizontal pieces `s ↦ A(s) - c ι` are
invertible and whose vertical pieces are paths of shifts `A(t) - λ ι` of the kind treated here.

## Main results

In the namespace `TauCeti.WeakDerivStep`:

* `eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow`: the index of
  the trajectory operator of a path of shifts `B - λ(s) ι` is its spectral flow.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §4.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ι B : D →L[ℝ] H}

/-! ### The span of the eigenvectors for finitely many eigenvalues -/

section Eigenvectors

variable (ι B) in
/-- The span of the solutions of `B x = c • ι x` for `c` in a finite set `S`. -/
private def eigenSum (S : Finset ℝ) : Submodule ℝ D :=
  S.sup fun c ↦ (c • ι - B).ker

/-- `x` solves `B x = c • ι x` exactly when it lies in the kernel of `c • ι - B`. -/
private theorem mem_ker_smul_sub_iff {c : ℝ} {x : D} : x ∈ (c • ι - B).ker ↔ B x = c • ι x := by
  simp [sub_eq_zero, eq_comm (a := B x)]

private theorem ker_le_eigenSum {S : Finset ℝ} {c : ℝ} (hc : c ∈ S) :
    (c • ι - B).ker ≤ eigenSum ι B S :=
  Finset.le_sup (f := fun c ↦ (c • ι - B).ker) hc

private theorem finiteDimensional_eigenSum (hι : IsCompactOperator ι) {c₀ : ℝ}
    (h₀ : (c₀ • ι - B).IsInvertible) (S : Finset ℝ) : FiniteDimensional ℝ (eigenSum ι B S) :=
  have := fun c : ℝ ↦ ContinuousLinearMap.finiteDimensional_ker_smul_sub hι h₀ c
  Submodule.finiteDimensional_finset_sup _ _

/-- `ι` is injective on the span of the eigenvectors: their components for distinct eigenvalues
have orthogonal images under `ι`. -/
private theorem injective_eigenSum (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {c₀ : ℝ}
    (h₀ : Injective (c₀ • ι - B)) (S : Finset ℝ) :
    Injective ((ι : D →ₗ[ℝ] H) ∘ₗ (eigenSum ι B S).subtype) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨x, hx⟩ hιx
  replace hιx : ι x = 0 := by simpa using hιx
  rw [eigenSum, Finset.sup_eq_iSup, Submodule.mem_iSup_finset_iff_exists_sum] at hx
  obtain ⟨μ, rfl⟩ := hx
  have hμ (c : ℝ) : B (μ c) = c • ι (μ c) := mem_ker_smul_sub_iff.1 (μ c).property
  -- Each component is killed by `ι`, hence by `c₀ • ι - B`.
  have hzero (c : ℝ) (hc : c ∈ S) : (μ c : D) = 0 := by
    have h := congrArg (fun v ↦ ⟪ι (μ c), v⟫_ℝ) hιx
    simp only [map_sum, inner_sum, inner_zero_right] at h
    rw [Finset.sum_eq_single c (fun d _ hdc ↦ ContinuousLinearMap.inner_eq_zero_of_apply_eq_smul
      hSymm (Ne.symm hdc) (hμ c) (hμ d)) (fun h ↦ (h hc).elim)] at h
    have hι0 : ι (μ c) = 0 := inner_self_eq_zero.1 h
    refine h₀ ?_
    simp [hμ c, hι0]
  rw [Submodule.mem_bot, Submodule.mk_eq_zero]
  exact Finset.sum_eq_zero hzero

/-- `B` maps the span of the eigenvectors into its image under `ι`. -/
private theorem apply_mem_range_eigenSum {S : Finset ℝ} {x : D} (hx : x ∈ eigenSum ι B S) :
    B x ∈ LinearMap.range ((ι : D →ₗ[ℝ] H) ∘ₗ (eigenSum ι B S).subtype) := by
  have hle : eigenSum ι B S ≤ (LinearMap.range ((ι : D →ₗ[ℝ] H) ∘ₗ
      (eigenSum ι B S).subtype)).comap (B : D →ₗ[ℝ] H) := Finset.sup_le fun c hc y hy ↦ by
    exact ⟨⟨c • y, (eigenSum ι B S).smul_mem c (ker_le_eigenSum hc hy)⟩,
      by simp [mem_ker_smul_sub_iff.1 hy]⟩
  exact hle hx

end Eigenvectors

/-! ### The block decomposition along a finite-dimensional invariant subspace -/

section Splitting

variable (ι) (V : Submodule ℝ D)

/-- The image `F = ι V` of a subspace `V`. -/
private abbrev eigenImage : Submodule ℝ H := LinearMap.range ((ι : D →ₗ[ℝ] H) ∘ₗ V.subtype)

/-- The closed subspace `D'` of the `x` with `ι x ⊥ ι V`. -/
private abbrev eigenCompl : Submodule ℝ D := (eigenImage ι V)ᗮ.comap (ι : D →ₗ[ℝ] H)

private theorem isClosed_eigenCompl : IsClosed (eigenCompl ι V : Set D) :=
  (Submodule.isClosed_orthogonal _).preimage ι.continuous

variable [FiniteDimensional ℝ V]

private instance : CompleteSpace (eigenImage ι V) :=
  FiniteDimensional.completeSpace ℝ _

private instance [CompleteSpace D] : CompleteSpace (eigenCompl ι V) :=
  (isClosed_eigenCompl ι V).completeSpace_coe

variable {ι V} (hV : Injective ((ι : D →ₗ[ℝ] H) ∘ₗ V.subtype))

/-- The inverse `ι V → V ⊆ D` of `ι` on `V`. -/
private def eigenLift : eigenImage ι V →L[ℝ] D :=
  V.subtypeL ∘L ((LinearEquiv.ofInjective _ hV).symm.toContinuousLinearEquiv :
    eigenImage ι V →L[ℝ] V)

private theorem apply_eigenLift (f : eigenImage ι V) : ι (eigenLift hV f) = f := by
  have h := LinearEquiv.ofInjective_symm_apply (f := (ι : D →ₗ[ℝ] H) ∘ₗ V.subtype) (h := hV) f
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe] at h
  simpa [eigenLift] using h

private theorem eigenLift_mem (f : eigenImage ι V) : eigenLift hV f ∈ V :=
  ((LinearEquiv.ofInjective _ hV).symm f).property

variable (ι V) in
/-- The restriction `ι' : D' → Fᗮ` of `ι`. -/
private def complEmbedding : eigenCompl ι V →L[ℝ] (eigenImage ι V)ᗮ :=
  (eigenImage ι V)ᗮ.orthogonalProjectionOnto ∘L ι ∘L (eigenCompl ι V).subtypeL

private theorem isCompactOperator_complEmbedding (hι : IsCompactOperator ι) :
    IsCompactOperator (complEmbedding ι V) := by
  rw [complEmbedding, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (hι.comp_clm _).clm_comp _

private theorem coe_complEmbedding (d : eigenCompl ι V) :
    (complEmbedding ι V d : H) = ι d :=
  congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := (eigenImage ι V)ᗮ)
      ⟨ι d, d.property⟩)

/-- `x ↦ x - ι⁻¹ (P_F (ι x))`, the projection of `D` onto `D'` along `V`. -/
private def complProj : D →L[ℝ] eigenCompl ι V :=
  (ContinuousLinearMap.id ℝ D -
      eigenLift hV ∘L (eigenImage ι V).orthogonalProjectionOnto ∘L ι).codRestrict _ fun x ↦ by
    simp [Submodule.mem_comap, apply_eigenLift, Submodule.sub_starProjection_mem_orthogonal]

/-- The splitting `D ≃ V ⊕ D'`, with `V` identified with `F = ι V` through `ι`. -/
private def splitEquiv : D ≃L[ℝ] WithLp 2 (eigenImage ι V × eigenCompl ι V) :=
  .ofContinuousLinearMap
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap ∘L
      ((eigenImage ι V).orthogonalProjectionOnto ∘L ι).prod (complProj hV))
    ((eigenLift hV).coprod (eigenCompl ι V).subtypeL ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap)
    (ContinuousLinearMap.ext fun y ↦ by
      have hd : ι y.snd ∈ (eigenImage ι V)ᗮ := y.snd.property
      refine (WithLp.ofLp_injective 2) (Prod.ext ?_ (Subtype.ext ?_))
      · simp [apply_eigenLift, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hd]
      · simp [complProj, apply_eigenLift,
          Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hd])
    (ContinuousLinearMap.ext fun x ↦ by simp [complProj])

private theorem splitEquiv_symm_apply (y : WithLp 2 (eigenImage ι V × eigenCompl ι V)) :
    (splitEquiv hV).symm y = eigenLift hV y.fst + y.snd :=
  rfl

/-- The splitting intertwines `ι` with `1 ⊕ ι'`. -/
private theorem withLpProdMap_comp_splitEquiv :
    (1 : eigenImage ι V →L[ℝ] eigenImage ι V).withLpProdMap 2 (complEmbedding ι V) ∘L
        (splitEquiv hV : D →L[ℝ] WithLp 2 (eigenImage ι V × eigenCompl ι V)) =
      ((eigenImage ι V).orthogonalDecomposition : H →L[ℝ] _) ∘L ι := by
  refine ContinuousLinearMap.ext fun x ↦ (WithLp.ofLp_injective 2) (Prod.ext ?_ ?_)
  · simp [splitEquiv]
  · refine Subtype.ext ?_
    simp [splitEquiv, complProj, coe_complEmbedding, apply_eigenLift]

end Splitting

/-! ### The two blocks of a shift -/

section Blocks

variable {V : Submodule ℝ D} [FiniteDimensional ℝ V]
  (hV : Injective ((ι : D →ₗ[ℝ] H) ∘ₗ V.subtype))

variable (B) in
/-- The block `B_F = P_F ∘ B ∘ ι⁻¹` of `B` on `F = ι V`. -/
private def eigenBlock : eigenImage ι V →L[ℝ] eigenImage ι V :=
  (eigenImage ι V).orthogonalProjectionOnto ∘L B ∘L eigenLift hV

variable (ι B V) in
/-- The block `B' = P_{Fᗮ} ∘ B` of `B` from `D'` to `Fᗮ`. -/
private def complBlock : eigenCompl ι V →L[ℝ] (eigenImage ι V)ᗮ :=
  (eigenImage ι V)ᗮ.orthogonalProjectionOnto ∘L B ∘L (eigenCompl ι V).subtypeL

private theorem coe_eigenBlock (hB : ∀ v ∈ V, B v ∈ eigenImage ι V) (f : eigenImage ι V) :
    (eigenBlock B hV f : H) = B (eigenLift hV f) := by
  simp [eigenBlock, Submodule.starProjection_eq_self_iff.2 (hB _ (eigenLift_mem hV f))]

omit [FiniteDimensional ℝ V] in
/-- By symmetry, `B` maps `D'` into `Fᗮ`. -/
private theorem apply_mem_orthogonal (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (d : eigenCompl ι V) : B d ∈ (eigenImage ι V)ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe, ← hSymm]
  exact Submodule.inner_right_of_mem_orthogonal (hB v v.property) d.property

private theorem coe_complBlock (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (d : eigenCompl ι V) : (complBlock ι B V d : H) = B d :=
  congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := (eigenImage ι V)ᗮ)
      ⟨B d, apply_mem_orthogonal hB hSymm d⟩)

/-- **Block form of a shift.** Through the splittings `D ≃ F ⊕ D'` and `H ≃ F ⊕ Fᗮ`, the shift
`B - c • ι` is the block sum `(B_F - c) ⊕ (B' - c • ι')`. -/
private theorem comp_sub_smul_comp_splitEquiv_symm (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (c : ℝ) :
    ((eigenImage ι V).orthogonalDecomposition.toContinuousLinearEquiv : H →L[ℝ] _) ∘L
        (B - c • ι) ∘L ((splitEquiv hV).symm : _ →L[ℝ] D) =
      (eigenBlock B hV - c • 1).withLpProdMap 2 (complBlock ι B V - c • complEmbedding ι V) := by
  refine ContinuousLinearMap.ext fun y ↦ ?_
  have hBd := apply_mem_orthogonal hB hSymm y.snd
  have hd : ι y.snd ∈ (eigenImage ι V)ᗮ := y.snd.property
  refine (WithLp.ofLp_injective 2) (Prod.ext ?_ ?_) <;> refine Subtype.ext ?_ <;>
    simp [splitEquiv_symm_apply, apply_eigenLift, coe_eigenBlock hV hB, coe_complBlock hB hSymm,
      coe_complEmbedding, Submodule.starProjection_eq_self_iff.2 (hB _ (eigenLift_mem hV y.fst)),
      (Submodule.starProjection_apply_eq_zero_iff _).2 hBd,
      (Submodule.starProjection_apply_eq_zero_iff _).2 hd]

/-- If the shift `B - c • ι` is invertible, then so are both of its blocks. -/
private theorem isInvertible_blocks_sub_smul (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {c : ℝ} (hc : (B - c • ι).IsInvertible) :
    (eigenBlock B hV - c • 1).IsInvertible ∧
      (complBlock ι B V - c • complEmbedding ι V).IsInvertible :=
  ContinuousLinearMap.isInvertible_withLpProdMap_iff.1
    (comp_sub_smul_comp_splitEquiv_symm hV hB hSymm c ▸
      ContinuousLinearMap.isInvertible_equiv_comp.2
        (ContinuousLinearMap.isInvertible_comp_equiv.2 hc))

/-- The block `B_F - c` is symmetric. -/
private theorem isSymmetric_eigenBlock_sub_smul (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (c : ℝ) : ((eigenBlock B hV - c • 1 : eigenImage ι V →L[ℝ] eigenImage ι V) :
      eigenImage ι V →ₗ[ℝ] eigenImage ι V).IsSymmetric := fun f g ↦ by
  have h := hSymm (eigenLift hV f) (eigenLift hV g)
  rw [apply_eigenLift, apply_eigenLift] at h
  simp [Submodule.coe_inner, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    coe_eigenBlock hV hB, h]

/-- The block `B' - c • ι'` is symmetric through `ι'`. -/
private theorem inner_complBlock_sub_smul (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (c : ℝ)
    (x y : eigenCompl ι V) :
    ⟪(complBlock ι B V - c • complEmbedding ι V) x, complEmbedding ι V y⟫_ℝ =
      ⟪complEmbedding ι V x, (complBlock ι B V - c • complEmbedding ι V) y⟫_ℝ := by
  simp [Submodule.coe_inner, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    coe_complBlock hB hSymm, coe_complEmbedding, hSymm]

include hV in
/-- **Invertibility of the second block.** If some shift `c₀ • ι - B` is invertible and every
solution of `B x = c • ι x` lies in `V`, then `B' - c • ι'` is invertible. -/
private theorem isInvertible_complBlock_sub_smul [CompleteSpace D]
    (hι : IsCompactOperator ι) (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {c₀ : ℝ}
    (h₀ : (B - c₀ • ι).IsInvertible) {c : ℝ} (hc : ∀ x ∈ (c • ι - B).ker, x ∈ V) :
    (complBlock ι B V - c • complEmbedding ι V).IsInvertible := by
  -- The second block of the invertible shift at `c₀` is invertible.
  have h₀' : (c₀ • complEmbedding ι V - complBlock ι B V).IsInvertible := by
    rw [ContinuousLinearMap.isInvertible_sub_comm]
    exact (isInvertible_blocks_sub_smul hV hB hSymm h₀).2
  rw [ContinuousLinearMap.isInvertible_sub_comm,
    ContinuousLinearMap.isInvertible_smul_sub_iff_injective
      (isCompactOperator_complEmbedding hι) h₀',
    injective_iff_map_eq_zero]
  intro d hd
  -- A vector of `D'` in the kernel is an eigenvector, so it lies in `V`, and `ι d ∈ F ∩ Fᗮ`.
  have hd' : c • ι d = B d := by
    simpa [coe_complBlock hB hSymm, coe_complEmbedding, sub_eq_zero] using congrArg Subtype.val hd
  have hdV := hc d (mem_ker_smul_sub_iff.2 hd'.symm)
  have hι0 : ((ι : D →ₗ[ℝ] H) ∘ₗ V.subtype) ⟨d, hdV⟩ = 0 :=
    Submodule.disjoint_def.1 (eigenImage ι V).orthogonal_disjoint _ ⟨⟨d, hdV⟩, rfl⟩ d.property
  have hd0 : (⟨d, hdV⟩ : V) = 0 := hV (hι0.trans (map_zero _).symm)
  exact Subtype.ext (by simpa using congrArg Subtype.val hd0)

end Blocks

/-! ### The index formula -/

section IndexFormula

variable [CompleteSpace D] [CompleteSpace H]

/-- The index formula for a path of shifts `B - λ(s) ι`, given a finite-dimensional subspace `V`
on which `ι` is injective, which `B` maps into `ι V`, and which contains every solution of
`B x = λ(s) • ι x`. -/
private theorem eventually_index_eq_domainSpectralFlow_of_ker_le (hι : IsCompactOperator ι)
    (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {V : Submodule ℝ D} [FiniteDimensional ℝ V]
    (hV : Injective ((ι : D →ₗ[ℝ] H) ∘ₗ V.subtype)) (hB : ∀ v ∈ V, B v ∈ eigenImage ι V)
    {lam : ℝ → ℝ} (hlam : Continuous lam) {cbot ctop : ℝ} (hbot : Tendsto lam atBot (𝓝 cbot))
    (htop : Tendsto lam atTop (𝓝 ctop)) (hBbot : (B - cbot • ι).IsInvertible)
    (hBtop : (B - ctop • ι).IsInvertible) (hker : ∀ s, ∀ x ∈ (lam s • ι - B).ker, x ∈ V)
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) (hAL : AL =ᵐ[μ₀] fun s ↦ B - lam s • ι) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) ι AL).index =
        domainSpectralFlow ι (fun s ↦ B - lam s • ι) ab.1 ab.2 := by
  -- Through `W` and `U`, each shift `B - c • ι` is the block sum `Φ c`.
  have hΦ := comp_sub_smul_comp_splitEquiv_symm hV hB hSymm
  -- The second block differs from its limit at `∞` by `(c₊ - λ(s)) • ι'`.
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendsto hlam hbot htop
  have hc (T : ℝ) : ∃ c, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x,
      ‖((complBlock ι B V - lam s • complEmbedding ι V) -
        (complBlock ι B V - ctop • complEmbedding ι V)) x‖ ≤ c * ‖complEmbedding ι V x‖ := by
    refine ⟨|ctop| + M, ae_of_all _ fun s _ x ↦ ?_⟩
    rw [sub_sub_sub_cancel_left]
    simp only [FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul,
      Pi.smul_apply, ← sub_smul, norm_smul]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add (le_of_eq (Real.norm_eq_abs _)) (hM s))
  refine eventually_index_familyDomainTrajectoryOperator_eq_domainSpectralFlow_of_comp_comp_symm
    (splitEquiv hV) (eigenImage ι V).orthogonalDecomposition (withLpProdMap_comp_splitEquiv hV)
    AL hAL fun AL' hAL' ↦ ?_
  have hsplit : AL' =ᵐ[μ₀] fun s ↦ (eigenBlock B hV - lam s • 1).withLpProdMap 2
      (complBlock ι B V - lam s • complEmbedding ι V) := by
    filter_upwards [hAL'] with s hs
    rw [hs]
    exact hΦ (lam s)
  have hblk := eventually_index_familyDomainTrajectoryOperator_withLpProdMap_eq_domainSpectralFlow
    (isCompactOperator_complEmbedding (V := V) hι)
    (continuous_const.sub (hlam.smul continuous_const))
    (continuous_const.sub (hlam.smul continuous_const))
    (fun s ↦ isSymmetric_eigenBlock_sub_smul hV hB hSymm (lam s))
    (fun s ↦ inner_complBlock_sub_smul hB hSymm (lam s))
    (fun s ↦ isInvertible_complBlock_sub_smul hV hι hB hSymm hBbot (hker s))
    (isInvertible_blocks_sub_smul hV hB hSymm hBbot).1
    (isInvertible_blocks_sub_smul hV hB hSymm hBtop).1
    (isInvertible_blocks_sub_smul hV hB hSymm hBbot).2
    (isInvertible_blocks_sub_smul hV hB hSymm hBtop).2
    (tendsto_const_nhds.sub (hbot.smul_const _)) (tendsto_const_nhds.sub (htop.smul_const _))
    (tendsto_const_nhds.sub (hbot.smul_const _)) (tendsto_const_nhds.sub (htop.smul_const _))
    hc AL' hsplit
  filter_upwards [hblk] with ⟨a, b⟩ h
  rw [h]
  exact congrArg (domainSpectralFlow _ · a b) (funext fun s ↦ (hΦ (lam s)).symm)

/-- **The index is the spectral flow, along a path of shifts.** Let `ι : D → H` be a compact
operator from a Banach space into a real Hilbert space and `B : D → H` an operator symmetric
through `ι`. Let `λ` be a continuous real function with limits `c₋` at `-∞` and `c₊` at `∞`, at
which the shifts `B - c₋ • ι` and `B - c₊ • ι` are invertible. Then for every `a` far enough to the
left and every `b` far enough to the right, the index of `u ↦ (ι ∘ u)' + (B - λ(s) • ι) u` from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is the spectral flow of `s ↦ B - λ(s) • ι` from `a`
to `b`. -/
theorem eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow
    (hι : IsCompactOperator ι) (hSymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {lam : ℝ → ℝ}
    (hlam : Continuous lam) {cbot ctop : ℝ} (hbot : Tendsto lam atBot (𝓝 cbot))
    (htop : Tendsto lam atTop (𝓝 ctop)) (hBbot : (B - cbot • ι).IsInvertible)
    (hBtop : (B - ctop • ι).IsInvertible) (AL : Lp (D →L[ℝ] H) ∞ μ₀)
    (hAL : AL =ᵐ[μ₀] fun s ↦ B - lam s • ι) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) ι AL).index =
        domainSpectralFlow ι (fun s ↦ B - lam s • ι) ab.1 ab.2 := by
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendsto hlam hbot htop
  have h₀ : (cbot • ι - B).IsInvertible := ContinuousLinearMap.isInvertible_sub_comm.1 hBbot
  -- The values of `λ` lie in `[-M, M]`, which contains finitely many eigenvalues of the pencil.
  have hS := ContinuousLinearMap.finite_inter_setOf_not_isInvertible_smul_sub hι h₀
    (Metric.isBounded_Icc (-M) M)
  have := finiteDimensional_eigenSum hι h₀ hS.toFinset
  refine eventually_index_eq_domainSpectralFlow_of_ker_le hι hSymm (V := eigenSum ι B hS.toFinset)
    (injective_eigenSum hSymm h₀.bijective.1 _) (fun v hv ↦ apply_mem_range_eigenSum hv) hlam hbot
    htop hBbot hBtop (fun s x hx ↦ ?_) AL hAL
  by_cases hs : (lam s • ι - B).IsInvertible
  · have hx0 : (lam s • ι - B) x = (lam s • ι - B) 0 := by simpa using hx
    rw [hs.bijective.1 hx0]
    exact zero_mem _
  · refine ker_le_eigenSum (hS.mem_toFinset.2 ⟨mem_Icc.2 (abs_le.1 ?_), hs⟩) hx
    simpa using hM s

end IndexFormula

end TauCeti.WeakDerivStep
