/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Diagonal
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.FormCore
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Spectral.Cutoff
import TauCeti.Analysis.Normed.Lp.Finsupp
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# A form core that is not a graph core

Every graph core of a symmetric operator bounded below is a form core
(`LinearPMap.HasCore.isFormCore`). The converse fails: the two are distinct density conditions.

On `ℓ²(ℕ, 𝕜)` let `S` be the diagonal operator `(S x)ₖ = 4ᵏ xₖ` on its maximal domain
`{x | (4ᵏ xₖ) ∈ ℓ²}` (`diagonalOperator`, an instance of `HilbertBasis.diagonalPMap`); it is
closed (`isClosed_diagonalOperator`). It is symmetric with lower bound `1`
(`isSymmetricBoundedBelow_diagonalOperator`), and with this bound its form norm is
`‖x‖_S ^ 2 = ∑ 4ᵏ |xₖ|²`. Let `w = (2⁻ᵏ)ₖ ∈ ℓ²`; the functional `x ↦ ⟪w, S x⟫ = ∑ 2ᵏ xₖ` is
continuous for the graph norm and nonzero, while it is unbounded for the form norm: the vectors
`v_M` with `(v_M)ₖ = 2⁻ᵏ / M` for `k < M` have `⟪w, S v_M⟫ = 1` and `‖v_M‖_S ^ 2 = 1 / M`. Its
kernel `D` in the domain of `S` (`kernelDomain`) is therefore

* a form core (`isFormCore_kernelDomain`): `x − ⟪w, S x⟫ v_M ∈ D` is within
  `|⟪w, S x⟫| / √M` of `x` in the form norm;
* not a graph core (`not_hasCore_kernelDomain`): the graph of `S` restricted to `D` lies in the
  closed set `{(u, v) | ⟪w, v⟫ = 0}`, which misses `(e₀, S e₀)`.
-/

public section

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal lp

namespace TauCeti.Examples.FormCore

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The diagonal operator `(S x)ₖ = 4ᵏ xₖ` on `ℓ²(ℕ, 𝕜)`, on its maximal domain
`{x ∈ ℓ² | (4ᵏ xₖ) ∈ ℓ²}`: the diagonal operator `HilbertBasis.diagonalPMap` with coefficients `4ᵏ`
in the standard Hilbert basis of `ℓ²(ℕ, 𝕜)` (`diagonalOperator_def`). -/
def diagonalOperator : ℓ²(ℕ, 𝕜) →ₗ.[𝕜] ℓ²(ℕ, 𝕜) :=
  (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)).diagonalPMap fun k ↦ (4 : 𝕜) ^ k

/-- The diagonal operator is `HilbertBasis.diagonalPMap` with coefficients `4ᵏ` in the standard
Hilbert basis of `ℓ²(ℕ, 𝕜)`. -/
theorem diagonalOperator_def :
    diagonalOperator 𝕜 =
      (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)).diagonalPMap fun k ↦ (4 : 𝕜) ^ k :=
  (rfl)

variable {𝕜}

@[simp]
theorem diagonalOperator_apply (x : (diagonalOperator 𝕜).domain) (k : ℕ) :
    (diagonalOperator 𝕜 x : ℓ²(ℕ, 𝕜)) k = (4 : 𝕜) ^ k * (x : ℓ²(ℕ, 𝕜)) k :=
  HilbertBasis.default_diagonalPMap_apply _ x k

/-- The standard basis vectors lie in the domain of the diagonal operator. -/
theorem default_mem_diagonalOperator_domain (k : ℕ) :
    (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) k ∈ (diagonalOperator 𝕜).domain :=
  HilbertBasis.self_mem_diagonalPMap_domain _ _ k

/-- The diagonal operator is closed. -/
theorem isClosed_diagonalOperator : (diagonalOperator 𝕜).IsClosed :=
  HilbertBasis.isClosed_diagonalPMap _ _

/-- `4ᵏ = 2ᵏ 2ᵏ`. -/
private theorem four_pow_eq {R : Type*} [CommSemiring R] (k : ℕ) :
    (4 : R) ^ k = 2 ^ k * 2 ^ k := by
  rw [← mul_pow]
  norm_num

/-- The diagonal operator is symmetric. -/
private theorem isFormalAdjoint_diagonalOperator :
    (diagonalOperator 𝕜).IsFormalAdjoint (diagonalOperator 𝕜) :=
  (HilbertBasis.isSelfAdjoint_diagonalPMap _ <|
    Pi.isSelfAdjoint.2 fun k => (IsSelfAdjoint.ofNat 4).pow k).isFormalAdjoint

/-- The standard basis vectors are eigenvectors of the diagonal operator, with the real
eigenvalues `4ᵏ`. -/
private theorem diagonalOperator_default (k : ℕ) :
    ∃ hk : (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) k ∈ (diagonalOperator 𝕜).domain,
      diagonalOperator 𝕜 ⟨(default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) k, hk⟩ =
        ((4 ^ k : ℝ) : 𝕜) • (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) k :=
  ⟨HilbertBasis.self_mem_diagonalPMap_domain _ _ k, by
    rw [RCLike.ofReal_pow, RCLike.ofReal_ofNat]
    exact HilbertBasis.diagonalPMap_apply_self _ _ k⟩

/-- The diagonal operator is symmetric with lower bound `1`. -/
theorem isSymmetricBoundedBelow_diagonalOperator :
    (diagonalOperator 𝕜).IsSymmetricBoundedBelow 1 where
  isFormalAdjoint := isFormalAdjoint_diagonalOperator
  mul_norm_sq_le_re_inner u :=
    isFormalAdjoint_diagonalOperator.mul_norm_sq_le_re_inner_of_hilbertBasis default
      diagonalOperator_default u fun k hk ↦ absurd hk (not_lt.2 (one_le_pow₀ (by norm_num)))

/-- The vector `w = (2⁻ᵏ)ₖ` of `ℓ²(ℕ, 𝕜)`. -/
def weightVector : ℓ²(ℕ, 𝕜) :=
  ⟨fun k => ((2 : 𝕜) ^ k)⁻¹, memℓp_gen <| by
    refine (summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).congr
      fun k => ?_
    norm_num [← inv_pow, ← pow_mul, pow_mul']⟩

@[simp]
theorem weightVector_apply (k : ℕ) : (weightVector : ℓ²(ℕ, 𝕜)) k = ((2 : 𝕜) ^ k)⁻¹ :=
  (rfl)

/-- `⟪w, S x⟫ = ∑ 2ᵏ xₖ`. -/
theorem inner_weightVector_diagonalOperator (x : (diagonalOperator 𝕜).domain) :
    ⟪(weightVector : ℓ²(ℕ, 𝕜)), diagonalOperator 𝕜 x⟫_𝕜 =
      ∑' k, (2 : 𝕜) ^ k * (x : ℓ²(ℕ, 𝕜)) k := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [weightVector_apply, diagonalOperator_apply, RCLike.inner_apply', map_inv₀, map_pow,
    RCLike.conj_ofNat]
  rw [four_pow_eq]
  field_simp

/-- The kernel `D` of `x ↦ ⟪w, S x⟫` in the domain of the diagonal operator. -/
def kernelDomain : Submodule 𝕜 ℓ²(ℕ, 𝕜) :=
  (LinearMap.ker ((innerₛₗ 𝕜 (weightVector : ℓ²(ℕ, 𝕜))) ∘ₗ (diagonalOperator 𝕜).toFun)).map
    (diagonalOperator 𝕜).domain.subtype

theorem kernelDomain_le_domain : kernelDomain (𝕜 := 𝕜) ≤ (diagonalOperator 𝕜).domain :=
  Submodule.map_subtype_le _ _

/-- A vector of the domain of `S` lies in `D` exactly when `⟪w, S x⟫ = 0`. -/
theorem mem_kernelDomain_iff (x : (diagonalOperator 𝕜).domain) :
    (x : ℓ²(ℕ, 𝕜)) ∈ kernelDomain ↔ ⟪(weightVector : ℓ²(ℕ, 𝕜)), diagonalOperator 𝕜 x⟫_𝕜 = 0 := by
  simp only [kernelDomain, Submodule.mem_map, LinearMap.mem_ker, LinearMap.comp_apply,
    innerₛₗ_apply_apply, Submodule.subtype_apply, SetLike.coe_eq_coe, LinearPMap.toFun_eq_coe,
    exists_eq_right]

/-- The entries of `v_M` vanish from `M` on. -/
private theorem hasFiniteSupport_testVector (M : ℕ) :
    (fun k ↦ if k < M then ((M : 𝕜) * 2 ^ k)⁻¹ else 0).HasFiniteSupport := by
  rw [Function.HasFiniteSupport]
  refine (Set.finite_lt_nat M).subset fun k hk => Set.mem_ofPred.2 ?_
  by_contra h
  exact Function.mem_support.1 hk (ite_eq_right h)

/-- The vector `v_M` of `ℓ²(ℕ, 𝕜)`, before it is placed in the domain of the diagonal operator. -/
private def testVectorL2 (M : ℕ) : ℓ²(ℕ, 𝕜) :=
  ⟨fun k => if k < M then ((M : 𝕜) * 2 ^ k)⁻¹ else 0, (hasFiniteSupport_testVector M).memℓp _⟩

private theorem testVectorL2_apply (M k : ℕ) :
    (testVectorL2 M : ℓ²(ℕ, 𝕜)) k = if k < M then ((M : 𝕜) * 2 ^ k)⁻¹ else 0 :=
  (rfl)

/-- The vector `v_M` with `(v_M)ₖ = 2⁻ᵏ / M` for `k < M` and `0` otherwise. -/
def testVector (M : ℕ) : (diagonalOperator 𝕜).domain :=
  ⟨testVectorL2 M, HilbertBasis.mem_diagonalPMap_domain_of_hasFiniteSupport _ _ <| by
    simpa only [HilbertBasis.inner_default_apply, testVectorL2_apply] using
      hasFiniteSupport_testVector M⟩

@[simp]
theorem testVector_apply (M k : ℕ) :
    ((testVector M : (diagonalOperator 𝕜).domain) : ℓ²(ℕ, 𝕜)) k =
      if k < M then ((M : 𝕜) * 2 ^ k)⁻¹ else 0 :=
  (rfl)

/-- `⟪w, S v_M⟫ = 1` for `M ≠ 0`. -/
theorem inner_weightVector_diagonalOperator_testVector {M : ℕ} (hM : M ≠ 0) :
    ⟪(weightVector : ℓ²(ℕ, 𝕜)), diagonalOperator 𝕜 (testVector M)⟫_𝕜 = 1 := by
  simp only [inner_weightVector_diagonalOperator, testVector_apply, mul_ite, mul_zero]
  rw [tsum_eq_sum (s := Finset.range M) fun k hk ↦ ite_eq_right (by simpa using hk),
    Finset.sum_ite_of_true fun k hk ↦ Finset.mem_range.1 hk]
  have h2 (k : ℕ) : (2 : 𝕜) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hM' : (M : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 hM
  simp only [mul_inv, mul_left_comm _ ((M : 𝕜)⁻¹), mul_inv_cancel₀ (h2 _), mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hM']

/-- `re ⟪S v_M, v_M⟫ = 1 / M`. -/
theorem re_inner_diagonalOperator_testVector (M : ℕ) :
    RCLike.re ⟪diagonalOperator 𝕜 (testVector M),
      ((testVector M : (diagonalOperator 𝕜).domain) : ℓ²(ℕ, 𝕜))⟫_𝕜 = (M : ℝ)⁻¹ := by
  have hterm (k : ℕ) : (4 : ℝ) ^ k *
      ‖((testVector M : (diagonalOperator 𝕜).domain) : ℓ²(ℕ, 𝕜)) k‖ ^ 2 =
      if k < M then ((M : ℝ) ^ 2)⁻¹ else 0 := by
    rw [testVector_apply]
    split_ifs with hk
    · have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simp [four_pow_eq, field]
    · simp
  have h := (isFormalAdjoint_diagonalOperator (𝕜 := 𝕜)).hasSum_re_inner_of_hilbertBasis default
    diagonalOperator_default (testVector M)
  simp only [HilbertBasis.inner_default_apply, hterm] at h
  refine h.tsum_eq.symm.trans ?_
  rw [tsum_eq_sum (s := Finset.range M) fun k hk ↦ ite_eq_right (by simpa using hk),
    Finset.sum_ite_of_true fun k hk ↦ Finset.mem_range.1 hk, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  rcases eq_or_ne M 0 with rfl | hM
  · simp
  · have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM
    field_simp

/-- The form norm of `v_M`, for the lower bound `1`, is `1 / √M`. -/
theorem norm_toFriedrichsSpace_testVector_sq (M : ℕ) :
    ‖LinearPMap.toFriedrichsSpace isSymmetricBoundedBelow_diagonalOperator
      (testVector M : (diagonalOperator 𝕜).domain)‖ ^ 2 = (M : ℝ)⁻¹ := by
  rw [LinearPMap.norm_toFriedrichsSpace_sq, re_inner_diagonalOperator_testVector]
  simp

/-- **A form core.** The kernel `D` of `x ↦ ⟪w, S x⟫` in the domain of the diagonal operator is a
form core: it is dense in the form completion. -/
theorem isFormCore_kernelDomain :
    LinearPMap.IsFormCore (isSymmetricBoundedBelow_diagonalOperator (𝕜 := 𝕜)) kernelDomain := by
  refine (LinearPMap.isFormCore_iff _).2 ⟨kernelDomain_le_domain, fun x ε hε => ?_⟩
  set c := ⟪(weightVector : ℓ²(ℕ, 𝕜)), diagonalOperator 𝕜 x⟫_𝕜
  obtain ⟨M, hM⟩ := exists_nat_gt (‖c‖ ^ 2 / ε ^ 2)
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hM
    exact absurd hM (not_lt.2 (by positivity))
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 (Nat.pos_of_ne_zero hM0)
  refine ⟨x - c • testVector M, (mem_kernelDomain_iff _).2 ?_, ?_⟩
  · simp [c, LinearPMap.map_sub, LinearPMap.map_smul, inner_sub_right, inner_smul_right,
      inner_weightVector_diagonalOperator_testVector hM0]
  · rw [sub_sub_cancel, map_smul, norm_smul]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    rw [mul_pow, norm_toFriedrichsSpace_testVector_sq]
    rw [div_lt_iff₀ (by positivity)] at hM
    field_simp
    linarith

/-- `⟪w, S e₀⟫ = 1` for the first vector `e₀` of the standard Hilbert basis. -/
theorem inner_weightVector_diagonalOperator_default_zero :
    ⟪(weightVector : ℓ²(ℕ, 𝕜)), diagonalOperator 𝕜
      ⟨(default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) 0, default_mem_diagonalOperator_domain 0⟩⟫_𝕜 = 1 := by
  have h : diagonalOperator 𝕜 ⟨(default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) 0,
      HilbertBasis.self_mem_diagonalPMap_domain _ _ 0⟩ =
      (4 : 𝕜) ^ 0 • (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) 0 :=
    HilbertBasis.diagonalPMap_apply_self _ _ 0
  rw [h, pow_zero, one_smul, ← inner_conj_symm, HilbertBasis.inner_default_apply,
    weightVector_apply]
  simp

/-- **Not a graph core.** The kernel `D` of `x ↦ ⟪w, S x⟫` is not a core of the diagonal operator,
which is closed (`isClosed_diagonalOperator`): the graph of the restriction of `S` to `D` lies in
the closed set `{(u, v) | ⟪w, v⟫ = 0}`, which does not contain `(e₀, S e₀)`. -/
theorem not_hasCore_kernelDomain : ¬(diagonalOperator 𝕜).HasCore kernelDomain := by
  intro h
  have hs : IsClosed {p : ℓ²(ℕ, 𝕜) × ℓ²(ℕ, 𝕜) | ⟪(weightVector : ℓ²(ℕ, 𝕜)), p.2⟫_𝕜 = 0} :=
    isClosed_eq (continuous_const.inner continuous_snd) continuous_const
  have hsub := h.graph_subset_of_isClosed hs (by
    intro p hp
    obtain ⟨y, -, hy₂⟩ := (LinearPMap.mem_graph_iff _).1 hp
    rw [Set.mem_ofPred_eq]
    have hy : (diagonalOperator 𝕜).domRestrict kernelDomain y =
        diagonalOperator 𝕜 ⟨y, y.property.2⟩ := LinearPMap.domRestrict_apply rfl
    rw [← hy₂, hy]
    exact (mem_kernelDomain_iff _).1 y.property.1)
  have := hsub ((diagonalOperator 𝕜).mem_graph ⟨(default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜)) 0,
    HilbertBasis.self_mem_diagonalPMap_domain _ _ 0⟩)
  simp only [Set.mem_ofPred_eq, inner_weightVector_diagonalOperator_default_zero] at this
  exact one_ne_zero this

end TauCeti.Examples.FormCore
