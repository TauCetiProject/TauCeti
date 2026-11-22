/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.DifferentialOperator.Transpose.Basic
import TauCeti.Geometry.Manifold.VectorField.CoordinateFrame

/-!
# Existence of formal transposes on manifolds

Let `μ` be a measure on a boundaryless manifold `M`. A formal transpose of a linear operator `D`
on `C^∞(M)` is an operator `D'` with `∫ (D f) g dμ = ∫ f (D' g) dμ` whenever `f` or `g` has compact
support (`LinearMap.IsFormalTranspose`); it is the operator through which `D` acts on
distributions. This file proves that every differential operator of order at most `m`, in
Grothendieck's sense (`TauCeti.differentialOperators`), has a formal transpose of order at most `m`,
as soon as this holds for differentiation along smooth vector fields
(`LinearMap.exists_isFormalTranspose_of_forall_vectorFieldDerivation`). For the Riemannian volume
the transposes of vector fields come from the divergence theorem, which gives the transposes of all
differential operators
(`LinearMap.isFormalTranspose_formalTranspose_riemannianVolume_of_mem_differentialOperators`).

## The argument

Formal transposes glue (`LinearMap.exists_isFormalTranspose_of_forall_exists_nhds`): if near every
point `x` an operator `T_x` of order at most `m` satisfies `∫ (D f) g dμ = ∫ f (T_x g) dμ` for test
functions `g` supported near `x`, then for a smooth partition of unity `ρ_i` subordinate to these
neighbourhoods, with compact supports, `g ↦ ∑ᶠ i, T_i (ρ_i g)` is a formal transpose of `D` of
order at most `m`.

The local transposes are built by induction on the order. Near `x`, the cut-off coordinate
functions `u_j` and coordinate vector fields `X_j` of a chart are dual
(`TauCeti.Manifold.exists_eventually_sum_smul_mvfderiv_eq`), so the principal symbol of an
operator `D` of order at most `k` is that of

`P = (1 / k!) ∑ᵢ [⋯[D, u_{i 0}], …, u_{i (k - 1)}] 1 · X_{i 0} ∘ ⋯ ∘ X_{i (k - 1)}`,

summed over all `i : Fin k → Fin n`. The operator `P` has a formal transpose, as a sum of composites
of multiplication operators and vector fields. For a cutoff `χ` equal to `1` near `x` and supported
where the frame is dual, `(D - P) ∘ χ` has vanishing principal symbol, so it has order at most
`k - 1` and a formal transpose by induction. Hence so does `D ∘ χ`, and its transpose is a transpose
of `D` for test functions supported where `χ = 1`, since `D` is local.

## References

* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (differential operators and their adjoints).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (distributions and differential operators on manifolds).
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti
open scoped ContDiff Manifold Topology

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ### Gluing local transposes -/

section Glue

section Partition

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- A product of smooth functions is supported in the support of its left factor. -/
private theorem _root_.ContMDiffMap.tsupport_mul_subset_left {f g : C^∞⟮I, M; ℝ⟯} :
    tsupport (f * g : C^∞⟮I, M; ℝ⟯) ⊆ tsupport f := by
  rw [ContMDiffMap.coe_mul]
  exact _root_.tsupport_mul_subset_left

variable {ι : Type*} (ρ : SmoothPartitionOfUnity ι I M univ)
  (T : ι → C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) (hT : ∀ i g, tsupport (T i g) ⊆ tsupport g)

include hT in
/-- The pieces `T i (ρ i * g)` of a glued operator are supported in the supports of the functions
of the partition of unity, so they form a locally finite family. -/
private theorem locallyFinite_support_glue (g : C^∞⟮I, M; ℝ⟯) :
    LocallyFinite fun i ↦ Function.support (T i (ρ i * g)) :=
  ρ.locallyFinite.closure.subset fun i ↦ (subset_tsupport _).trans <| (hT i _).trans
    ContMDiffMap.tsupport_mul_subset_left

/-- The operator `g ↦ ∑ᶠ i, T i (ρ i * g)` glued from the operators `T i` along a smooth partition
of unity `ρ`. -/
private def glue : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ where
  toFun g := ⟨fun y ↦ ∑ᶠ i, T i (ρ i * g) y,
    contMDiff_finsum (fun i ↦ (T i (ρ i * g)).contMDiff) (locallyFinite_support_glue ρ T hT g)⟩
  map_add' g₁ g₂ := by
    ext y
    simp only [mul_add, map_add, ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coeFn_mk]
    exact finsum_add_distrib ((locallyFinite_support_glue ρ T hT g₁).point_finite y)
      ((locallyFinite_support_glue ρ T hT g₂).point_finite y)
  map_smul' c g := by
    ext y
    simp only [mul_smul_comm, map_smul, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      ContMDiffMap.coeFn_mk, RingHom.id_apply]
    exact (mul_finsum _ _).symm

private theorem glue_apply (g : C^∞⟮I, M; ℝ⟯) (y : M) :
    glue ρ T hT g y = ∑ᶠ i, T i (ρ i * g) y :=
  rfl

/-- Gluing operators of order at most `m` gives an operator of order at most `m`: if `g` lies in
`I_x ^ (m + 1)`, so does each `ρ i * g`, and every piece vanishes at `x`. -/
private theorem glue_mem_differentialOperators {m : ℕ}
    (hTm : ∀ i, T i ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    glue ρ T hT ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
  have hsep := ContMDiffMap.eq_zero_of_forall_mem_ker_evalAlgHom_smul_top (I := I) (M := M)
    (𝕜 := ℝ) (n := ∞)
  refine (mem_differentialOperators_iff_forall_apply_mem_smul_top
    (fun x : M ↦ (ContMDiffMap.evalAlgHom x : C^∞⟮I, M; ℝ⟯ →ₐ[ℝ] ℝ)) hsep).2 fun x g hg ↦ ?_
  rw [smul_eq_mul, Ideal.mul_top, ker_evalAlgHom_eq_smoothVanishingIdeal] at hg ⊢
  refine mem_smoothVanishingIdeal_iff.2 ?_
  rw [glue_apply]
  exact finsum_eq_zero_of_forall_eq_zero fun i ↦
    differentialOperators_apply_eq_zero_of_mem_smoothVanishingIdeal_pow (hTm i)
      (Ideal.mul_mem_left _ _ hg)

variable [MeasurableSpace M] {μ : Measure M}

/-- The glued operator is a formal transpose of `D` as soon as each `T i` is one for test
functions supported in the compact support of `ρ i`. -/
private theorem isFormalTranspose_glue [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯} (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    (hρ : ∀ i, HasCompactSupport (ρ i))
    (hDT : ∀ i (f g : C^∞⟮I, M; ℝ⟯), tsupport g ⊆ tsupport (ρ i) →
      ∫ y, D f y * g y ∂μ = ∫ y, f y * T i g y ∂μ) :
    D.IsFormalTranspose (glue ρ T hT) μ := by
  refine isFormalTranspose_iff.2 fun f g hfg ↦ ?_
  -- Only the finitely many pieces whose support meets the compact support `K` of `f` or of `g`
  -- contribute to either integral.
  obtain ⟨K, hK, hfgK⟩ : ∃ K, IsCompact K ∧ (tsupport f ⊆ K ∨ tsupport g ⊆ K) :=
    hfg.elim (fun hf ↦ ⟨_, hf, .inl subset_rfl⟩) fun hg ↦ ⟨_, hg, .inr subset_rfl⟩
  set F := (ρ.locallyFinite.closure.finite_nonempty_inter_compact hK).toFinset
  have hF {i : ι} {y : M} (hρy : y ∈ tsupport (ρ i)) (hy : y ∈ tsupport f ∩ tsupport g) :
      i ∈ F := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨y, hρy, hfgK.elim (· hy.1) (· hy.2)⟩
  have hgcs (i : ι) : HasCompactSupport (ρ i * g) :=
    (hρ i).mono' ((subset_tsupport _).trans ContMDiffMap.tsupport_mul_subset_left)
  have hleft (y : M) : D f y * g y = ∑ i ∈ F, D f y * (ρ i * g) y := by
    have h1 : g y = ∑ᶠ i, ρ i y * g y := by
      rw [← finsum_mul, ρ.sum_eq_one (mem_univ y), one_mul]
    rw [h1, mul_finsum]
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
    have hi' := Function.mem_support.1 hi
    refine hF (subset_tsupport _ (left_ne_zero_of_mul (right_ne_zero_of_mul hi')))
      ⟨hD f (subset_tsupport _ (left_ne_zero_of_mul hi')),
        subset_tsupport _ (right_ne_zero_of_mul (right_ne_zero_of_mul hi'))⟩
  have hright (y : M) : f y * glue ρ T hT g y = ∑ i ∈ F, f y * T i (ρ i * g) y := by
    rw [glue_apply, mul_finsum]
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
    have hi' := Function.mem_support.1 hi
    have hy := hT i _ (subset_tsupport _ (right_ne_zero_of_mul hi'))
    exact hF (ContMDiffMap.tsupport_mul_subset_left hy)
      ⟨subset_tsupport _ (left_ne_zero_of_mul hi'), tsupport_mulLeft_apply_subset (ρ i) g hy⟩
  simp_rw [hleft, hright]
  rw [integral_finsetSum _ fun i _ ↦ ContMDiffMap.integrable_apply_mul_of_tsupport_subset hD
      (.inr (hgcs i)),
    integral_finsetSum _ fun i _ ↦ ContMDiffMap.integrable_mul_apply_of_tsupport_subset (hT i)
      (.inr (hgcs i))]
  exact Finset.sum_congr rfl fun i _ ↦ hDT i f _ ContMDiffMap.tsupport_mul_subset_left

end Partition

variable [MeasurableSpace M] {μ : Measure M}

/-- **Formal transposes glue.** Let `D` be an operator on `C^∞(M)` that does not enlarge supports.
If near every point `D` has a formal transpose of order at most `m` for test functions supported
in a neighbourhood of that point, then `D` has a formal transpose of order at most `m` on all of
`M`. It is glued from the local transposes along a smooth partition of unity. -/
theorem exists_isFormalTranspose_of_forall_exists_nhds [SigmaCompactSpace M]
    [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ] {m : ℕ}
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯} (hD : ∀ f, tsupport (D f) ⊆ tsupport f)
    (h : ∀ x, ∃ U ∈ 𝓝 x,
      ∃ T ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
        ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport g → tsupport g ⊆ U →
          ∫ y, D f y * g y ∂μ = ∫ y, f y * T g y ∂μ) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
      D.IsFormalTranspose D' μ := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  choose U hU T hTm hDT using h
  -- Shrink each neighbourhood to a compact one, and take a partition of unity subordinate to
  -- their interiors, so that every function of the partition has compact support.
  choose K hKx hKU hK using fun x ↦ local_compact_nhds (hU x)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun x ↦ interior (K x)) (fun _ ↦ isOpen_interior)
    (fun x _ ↦ mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hKx x)⟩)
  have hρK (x : M) : tsupport (ρ x) ⊆ K x := (hρ x).trans interior_subset
  have hTs (x : M) (g : C^∞⟮I, M; ℝ⟯) : tsupport (T x g) ⊆ tsupport g :=
    tsupport_differentialOperators_apply_subset (hTm x) g
  refine ⟨glue ρ T hTs, glue_mem_differentialOperators ρ T hTs hTm,
    isFormalTranspose_glue ρ T hTs hD (fun x ↦ (hK x).of_isClosed_subset (isClosed_tsupport _)
      (hρK x)) fun x f g hg ↦ hDT x f g ?_ ((hg.trans (hρK x)).trans (hKU x))⟩
  exact (hK x).of_isClosed_subset (isClosed_tsupport _) (hg.trans (hρK x))

end Glue

/-! ### Composites of vector fields -/

/-- The composite `X (i 0) ∘ ⋯ ∘ X (i (k - 1))` of the derivations along the vector fields
`X (i l)`. -/
private def vectorFieldProd {ι : Type*} (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    {k : ℕ} → (Fin k → ι) → C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯
  | 0, _ => LinearMap.id
  | _ + 1, i => (vectorFieldDerivation (X (i 0)) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∘ₗ
      vectorFieldProd X (Fin.tail i)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem vectorFieldProd_succ {ι : Type*}
    (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {k : ℕ} (i : Fin (k + 1) → ι) :
    vectorFieldProd X i =
      (vectorFieldDerivation (X (i 0)) : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∘ₗ
        vectorFieldProd X (Fin.tail i) :=
  rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem vectorFieldProd_mem {ι : Type*}
    (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ {k : ℕ} (i : Fin k → ι),
      vectorFieldProd X i ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k
  | 0, _ => mem_differentialOperators_zero_iff.2 fun _ _ ↦ rfl
  | k + 1, i => by
    have h := comp_mem_differentialOperators
      (Derivation.mem_differentialOperators_one (vectorFieldDerivation (X (i 0))))
      (vectorFieldProd_mem X (Fin.tail i))
    rwa [Nat.add_comm 1 k, ← vectorFieldProd_succ] at h

/-- The principal symbol of `X (i 0) ∘ ⋯ ∘ X (i (k - 1))` is `ξ ↦ ∏ l, ξ (X (i l) y)`. -/
private theorem smoothPrincipalSymbol_vectorFieldProd {ι : Type*}
    (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : M} (hy : I.IsInteriorPoint y)
    (ξ : TangentSpace I y →L[ℝ] ℝ) :
    ∀ {k : ℕ} (i : Fin k → ι),
      smoothPrincipalSymbol I hy ⟨vectorFieldProd X i, vectorFieldProd_mem X i⟩ ξ =
        ∏ l, ξ (X (i l) y)
  | 0, _ => by
    rw [smoothPrincipalSymbol_eq_apply_one]
    simp [vectorFieldProd]
  | k + 1, i => by
    rw [smoothPrincipalSymbol_congr hy (Nat.add_comm 1 k).symm
      (D' := ⟨_, comp_mem_differentialOperators
        (Derivation.mem_differentialOperators_one (vectorFieldDerivation (X (i 0))))
        (vectorFieldProd_mem X (Fin.tail i))⟩) (vectorFieldProd_succ X i)]
    rw [smoothPrincipalSymbol_comp hy ⟨_, Derivation.mem_differentialOperators_one
      (vectorFieldDerivation (X (i 0)))⟩ ⟨_, vectorFieldProd_mem X (Fin.tail i)⟩,
      smoothPrincipalSymbol_vectorFieldDerivation, smoothPrincipalSymbol_vectorFieldProd X hy ξ,
      Fin.prod_univ_succ]
    simp [Fin.tail]

/-! ### Matching the principal symbol near a point -/

/-- The operator `(1 / k!) ∑ᵢ cᵢ X (i 0) ∘ ⋯ ∘ X (i (k - 1))`, summed over all `i : Fin k → ι`,
with coefficients `cᵢ = [⋯[D, u (i 0)], …, u (i (k - 1))] 1`. Where the differentials of the
functions `u j` form the dual coframe of the vector fields `X j`, it has the principal symbol
of `D`. -/
private def symbolOperator {ι : Type*} [Fintype ι] {k : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (u : ι → C^∞⟮I, M; ℝ⟯) (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  (k.factorial : ℝ)⁻¹ • ∑ i : Fin k → ι,
    mulLeft ℝ (commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k D (u ∘ i) 1) ∘ₗ
      vectorFieldProd X i

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem mulLeft_comp_vectorFieldProd_mem {ι : Type*}
    (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (c : C^∞⟮I, M; ℝ⟯) {k : ℕ}
    (i : Fin k → ι) :
    mulLeft ℝ c ∘ₗ vectorFieldProd X i ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k := by
  simpa using comp_mem_differentialOperators (mulLeft_mem_differentialOperators_zero c)
    (vectorFieldProd_mem X i)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem symbolOperator_mem {ι : Type*} [Fintype ι] {k : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (u : ι → C^∞⟮I, M; ℝ⟯) (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    symbolOperator D u X ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k :=
  Submodule.smul_mem _ _ (sum_mem fun i _ ↦ mulLeft_comp_vectorFieldProd_mem X _ i)

private theorem smoothPrincipalSymbol_symbolOperator {ι : Type*} [Fintype ι] {k : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (u : ι → C^∞⟮I, M; ℝ⟯) (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : M}
    (hy : I.IsInteriorPoint y) (ξ : TangentSpace I y →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hy ⟨symbolOperator D u X, symbolOperator_mem D u X⟩ ξ =
      (k.factorial : ℝ)⁻¹ * ∑ i : Fin k → ι,
        commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k D (u ∘ i) 1 y *
          ∏ l, ξ (X (i l) y) := by
  have h : (⟨symbolOperator D u X, symbolOperator_mem D u X⟩ :
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k) =
      (k.factorial : ℝ)⁻¹ • ∑ i : Fin k → ι, ⟨_, mulLeft_comp_vectorFieldProd_mem X
        (commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k D (u ∘ i) 1) i⟩ :=
    Subtype.ext (by simp [symbolOperator])
  rw [h, smoothPrincipalSymbol_smul, smoothPrincipalSymbol_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smoothPrincipalSymbol_congr hy (zero_add k).symm
      (D' := ⟨_, comp_mem_differentialOperators (mulLeft_mem_differentialOperators_zero _)
        (vectorFieldProd_mem X i)⟩) rfl,
    smoothPrincipalSymbol_comp hy ⟨_, mulLeft_mem_differentialOperators_zero _⟩
      ⟨_, vectorFieldProd_mem X i⟩, smoothPrincipalSymbol_eq_apply_one,
    smoothPrincipalSymbol_vectorFieldProd]
  simp

/-- Where `ξ = ∑ j, ξ (X j y) du_j(y)` for every covector `ξ`, the principal symbol of `D` at `y`
is that of `symbolOperator D u X`. -/
private theorem smoothPrincipalSymbol_eq_symbolOperator {ι : Type*} [Fintype ι] {k : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (u : ι → C^∞⟮I, M; ℝ⟯) (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : M}
    (hy : I.IsInteriorPoint y)
    (hu : ∀ ξ : TangentSpace I y →L[ℝ] ℝ, ∑ j, ξ (X j y) • mvfderiv I (u j) y = ξ)
    (ξ : TangentSpace I y →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hy D ξ =
      smoothPrincipalSymbol I hy ⟨symbolOperator D u X, symbolOperator_mem D u X⟩ ξ := by
  rw [smoothPrincipalSymbol_symbolOperator, smoothPrincipalSymbol_def]
  congr 1
  have hξ : (fun _ : Fin k ↦ ξ) = fun _ ↦ ∑ j, ξ (X j y) • mvfderiv I (u j) y :=
    funext fun _ ↦ (hu ξ).symm
  rw [hξ, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm,
    smoothCommutatorSymbol_mvfderiv hy D fun l ↦ u (i l)]
  simp only [RingHom.id_apply, Function.comp_def]

/-! ### Transposes by induction on the order -/

section Induction

variable [MeasurableSpace M] {μ : Measure M}

/-! ### Operators with transposes of a given order -/

/-- `D` has a formal transpose with respect to `μ` which is a differential operator of order at
most `m`. -/
private def HasTranspose (μ : Measure M) (m : ℕ) (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) : Prop :=
  ∃ D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
    D.IsFormalTranspose D' μ

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem HasTranspose.mono {m n : ℕ} {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (h : HasTranspose μ m D) (hmn : m ≤ n) : HasTranspose μ n D :=
  let ⟨D', hD', h⟩ := h
  ⟨D', differentialOperators_mono hmn hD', h⟩

private theorem HasTranspose.comp {m₁ m₂ : ℕ} {D₁ D₂ : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (h₁ : HasTranspose μ m₁ D₁) (h₂ : HasTranspose μ m₂ D₂)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m₂) :
    HasTranspose μ (m₁ + m₂) (D₁ ∘ₗ D₂) :=
  let ⟨D₁', hD₁', h₁⟩ := h₁
  let ⟨D₂', hD₂', h₂⟩ := h₂
  ⟨D₂' ∘ₗ D₁', by simpa [add_comm] using comp_mem_differentialOperators hD₂' hD₁',
    h₁.comp h₂ (tsupport_differentialOperators_apply_subset hD₂)
      (tsupport_differentialOperators_apply_subset hD₁')⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem hasTranspose_mulLeft (c : C^∞⟮I, M; ℝ⟯) : HasTranspose μ 0 (mulLeft ℝ c) :=
  ⟨_, mulLeft_mem_differentialOperators_zero c, isFormalTranspose_mulLeft c⟩

section Integrable

variable [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]

private theorem HasTranspose.add {m : ℕ} {D₁ D₂ : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (h₁ : HasTranspose μ m D₁) (h₂ : HasTranspose μ m D₂)
    (hD₁ : D₁ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (hD₂ : D₂ ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    HasTranspose μ m (D₁ + D₂) :=
  let ⟨D₁', hD₁', h₁⟩ := h₁
  let ⟨D₂', hD₂', h₂⟩ := h₂
  ⟨D₁' + D₂', add_mem hD₁' hD₂', h₁.add h₂ (tsupport_differentialOperators_apply_subset hD₁)
    (tsupport_differentialOperators_apply_subset hD₂)
    (tsupport_differentialOperators_apply_subset hD₁')
    (tsupport_differentialOperators_apply_subset hD₂')⟩

private theorem HasTranspose.sum {m : ℕ} {κ : Type*} (s : Finset κ)
    {D : κ → C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯} (h : ∀ i ∈ s, HasTranspose μ m (D i))
    (hD : ∀ i ∈ s, D i ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    HasTranspose μ m (∑ i ∈ s, D i) := by
  choose! D' hD' hT using h
  exact ⟨∑ i ∈ s, D' i, sum_mem hD', IsFormalTranspose.sum s hT
    (fun i hi ↦ tsupport_differentialOperators_apply_subset (hD i hi))
    (fun i hi ↦ tsupport_differentialOperators_apply_subset (hD' i hi))⟩

end Integrable

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem HasTranspose.smul {m : ℕ} {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (h : HasTranspose μ m D) (c : ℝ) : HasTranspose μ m (c • D) :=
  let ⟨D', hD', h⟩ := h
  ⟨c • D', Submodule.smul_mem _ c hD', h.smul c⟩

private theorem hasTranspose_vectorFieldProd {ι : Type*}
    (hX : ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      HasTranspose μ 1 (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯))
    (X : ι → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ {k : ℕ} (i : Fin k → ι), HasTranspose μ k (vectorFieldProd X i)
  | 0, _ => ⟨LinearMap.id, mem_differentialOperators_zero_iff.2 fun _ _ ↦ rfl,
      IsFormalTranspose.id⟩
  | k + 1, i => by
    have h := (hX (X (i 0))).comp (hasTranspose_vectorFieldProd hX X (Fin.tail i))
      (vectorFieldProd_mem X (Fin.tail i))
    rwa [Nat.add_comm 1 k, ← vectorFieldProd_succ] at h

/-- If `D ∘ χ` has a formal transpose `T`, then `T` is a formal transpose of `D` for test functions
supported where `χ = 1`, since `D` is local. -/
private theorem integral_apply_mul_eq_of_isFormalTranspose_comp_mulLeft {m : ℕ}
    {D T : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    {χ : C^∞⟮I, M; ℝ⟯} (hT : (D ∘ₗ mulLeft ℝ χ).IsFormalTranspose T μ)
    {f g : C^∞⟮I, M; ℝ⟯} (hg : HasCompactSupport g)
    (hgχ : tsupport g ⊆ interior {y | χ y = 1}) :
    ∫ y, D f y * g y ∂μ = ∫ y, f y * T g y ∂μ := by
  refine (integral_congr_ae (.of_forall fun y ↦ ?_)).trans (hT.integral_mul_eq (.inr hg))
  by_cases hgy : g y = 0
  · simp [hgy]
  have hy := hgχ (subset_tsupport _ hgy)
  -- Near `y` the function `χ` is `1`, so `f` and `χ f` have the same germ there.
  have hfχ : (f : M → ℝ) =ᶠ[𝓝 y] (χ * f : C^∞⟮I, M; ℝ⟯) := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    rw [ContMDiffMap.coe_mul, Pi.mul_apply, interior_subset hz, one_mul]
  rw [comp_apply, mulLeft_apply, differentialOperators_apply_eq_of_eventuallyEq hD hfχ]

variable [BoundarylessManifold I M] [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]

/-- **The local step.** If every operator of order at most `m` has a transpose of order at most
`m`, then an operator `D` of order at most `m + 1` has one near each point. Near `x`, the operator
`symbolOperator` has the principal symbol of `D`, so after a cutoff `χ` equal to `1` near `x` the
difference `(D - symbolOperator) ∘ χ` has order at most `m`. -/
private theorem exists_nhds_integral_apply_mul_eq
    (hX : ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      HasTranspose μ 1 (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯))
    {m : ℕ} (ih : ∀ D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
      HasTranspose μ m D)
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (m + 1)) (x : M) :
    ∃ U ∈ 𝓝 x,
      ∃ T ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (m + 1),
        ∀ f g : C^∞⟮I, M; ℝ⟯, HasCompactSupport g → tsupport g ⊆ U →
          ∫ y, D f y * g y ∂μ = ∫ y, f y * T g y ∂μ := by
  obtain ⟨u, X, hu⟩ := TauCeti.Manifold.exists_eventually_sum_smul_mvfderiv_eq (I := I) x
  obtain ⟨χ, -, hχu⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1 hu
  set c : C^∞⟮I, M; ℝ⟯ := ⟨χ, χ.contMDiff⟩
  set P := symbolOperator ⟨D, hD⟩ u X
  have hP := symbolOperator_mem ⟨D, hD⟩ u X
  -- The principal symbol of `(D - P) ∘ χ` vanishes: on `tsupport χ` the symbols of `D` and `P`
  -- agree, and off it `χ` vanishes.
  have hQ : (D - P) ∘ₗ mulLeft ℝ c ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
    refine (forall_smoothPrincipalSymbol_eq_zero_iff (m := m) ⟨(D - P) ∘ₗ mulLeft ℝ c,
      comp_mem_differentialOperators (m := m + 1) (k := 0) (sub_mem hD hP)
        (mulLeft_mem_differentialOperators_zero c)⟩).1 fun y ξ ↦ ?_
    rw [smoothPrincipalSymbol_comp _ ⟨_, sub_mem hD hP⟩
      ⟨_, mulLeft_mem_differentialOperators_zero c⟩, smoothPrincipalSymbol_eq_apply_one]
    by_cases hy : y ∈ tsupport χ
    · have h := smoothPrincipalSymbol_eq_symbolOperator ⟨D, hD⟩ u X
        BoundarylessManifold.isInteriorPoint (hχu hy) ξ
      have hsub : (⟨D - P, sub_mem hD hP⟩ :
          differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (m + 1)) =
          ⟨D, hD⟩ - ⟨P, hP⟩ :=
        Subtype.ext (Submodule.coe_sub _ ⟨D, hD⟩ ⟨P, hP⟩).symm
      rw [hsub, smoothPrincipalSymbol_sub, h, sub_self, zero_mul]
    · refine mul_eq_zero_of_right _ ?_
      rw [mulLeft_apply, mul_one]
      exact image_eq_zero_of_notMem_tsupport hy
  -- So `D ∘ χ = (D - P) ∘ χ + P ∘ χ` has a transpose of order at most `m + 1`.
  have hP' : HasTranspose μ (m + 1) P :=
    (HasTranspose.sum _ (fun i _ ↦ (hasTranspose_mulLeft _).comp
      (hasTranspose_vectorFieldProd hX X i) (vectorFieldProd_mem X i) |>.mono (by simp))
      fun i _ ↦ mulLeft_comp_vectorFieldProd_mem X _ i).smul _
  have hDc : D ∘ₗ mulLeft ℝ c = (D - P) ∘ₗ mulLeft ℝ c + P ∘ₗ mulLeft ℝ c := by
    rw [← add_comp, sub_add_cancel]
  obtain ⟨T, hT, hDT⟩ : HasTranspose μ (m + 1) (D ∘ₗ mulLeft ℝ c) := by
    rw [hDc]
    exact ((ih _ hQ).mono m.le_succ).add (hP'.comp (hasTranspose_mulLeft c)
        (mulLeft_mem_differentialOperators_zero c))
      (differentialOperators_le_succ m hQ)
      (comp_mem_differentialOperators hP (mulLeft_mem_differentialOperators_zero c))
  refine ⟨_, interior_mem_nhds.2 χ.eventuallyEq_one, T, hT, fun f g hg hgU ↦
    integral_apply_mul_eq_of_isFormalTranspose_comp_mulLeft hD hDT hg hgU⟩

/-- Every operator of order at most `m` has a formal transpose of order at most `m`, given this
for vector fields. -/
private theorem hasTranspose_of_mem_differentialOperators [SigmaCompactSpace M]
    (hX : ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      HasTranspose μ 1 (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯)) :
    ∀ {m : ℕ} {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯},
      D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m → HasTranspose μ m D
  | 0, D, hD => ⟨D, hD, isFormalTranspose_self_of_mem_differentialOperators_zero hD⟩
  | _ + 1, _, hD => exists_isFormalTranspose_of_forall_exists_nhds
      (tsupport_differentialOperators_apply_subset hD)
      (exists_nhds_integral_apply_mul_eq hX (fun _ ↦ hasTranspose_of_mem_differentialOperators hX)
        hD)

/-- **Existence of formal transposes.** On a boundaryless manifold, if differentiation along every
smooth vector field has a formal transpose of order at most one with respect to `μ`, then every
differential operator of order at most `m` on `C^∞(M)` has a formal transpose of order at most
`m` with respect to `μ`. -/
theorem exists_isFormalTranspose_of_forall_vectorFieldDerivation [SigmaCompactSpace M]
    (hX : ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      ∃ D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ 1,
        (vectorFieldDerivation X : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D' μ)
    {m : ℕ} {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) :
    ∃ D' ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m,
      D.IsFormalTranspose D' μ :=
  hasTranspose_of_mem_differentialOperators hX hD

end Induction

end LinearMap
