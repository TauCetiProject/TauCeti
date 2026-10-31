/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.Algebra.Module.ZLattice.Determinant
public import TauCeti.Algebra.Module.ZLattice.Quotient
public import TauCeti.Algebra.Module.ZLattice.Shell
import Mathlib.Data.Set.Card.Arithmetic

/-!
# The orthogonal direct sum of two lattices

For `ℤ`-submodules `L` of a real inner product space `E` and `M` of a real inner product space
`F`, the *orthogonal direct sum* `L ⊕ M` is the submodule `L × M` of the `L²` product
`WithLp 2 (E × F)`, whose inner product is `⟪(x, y), (x', y')⟫ = ⟪x, x'⟫ + ⟪y, y'⟫`
(`ZLattice.orthSum`).

The dual of an orthogonal direct sum is the orthogonal direct sum of the duals
(`ZLattice.dual_orthSum`). Consequently `L ⊕ M` is integral, even or unimodular exactly when both
`L` and `M` are; in particular each of the three predicates is preserved by orthogonal direct sums.

When `L` and `M` are full lattices in finite-dimensional spaces, so is `L ⊕ M`: the sum of the
`ℤ`-spans of two `ℝ`-bases is the `ℤ`-span of the product basis (`ZLattice.orthSum_span_basis`).
The Gram matrix of the product basis is block diagonal, so covolumes and determinants multiply:
`covolume (L ⊕ M) = covolume L * covolume M` and `det (L ⊕ M) = det L * det M`.

Since `‖(x, y)‖² = ‖x‖² + ‖y‖²`, a vector of `L ⊕ M` of squared norm `t` is a pair of vectors of
`L` and `M` of squared norms `s` and `t - s`, where `s ≤ t` runs over the finitely many squared
norms represented by `L`. The representation numbers of `L ⊕ M` are therefore the convolution
`r_{L ⊕ M}(t) = ∑_s r_L(s) * r_M(t - s)` of those of the summands; for even `L` this is the finite
sum `r_{L ⊕ M}(2m) = ∑_{i ≤ m} r_L(2i) * r_M(2(m - i))`, and for integral `L` the sum
`r_{L ⊕ M}(n) = ∑_{i ≤ n} r_L(i) * r_M(n - i)`.

Orthogonal direct sums build integral, even or unimodular lattices of large rank from small ones,
for instance the even unimodular lattice `E₈ ⊕ E₈` of rank `16`.

## Main definitions

* `ZLattice.orthSum L M`: the orthogonal direct sum of `L` and `M`, in `WithLp 2 (E × F)`.
* `ZLattice.orthSumEquivProd L M`: the identification of `L ⊕ M` with `L × M` as `ℤ`-modules.
* `ZLattice.quotientSmulOrthSumEquiv L M c`: the identification of `(L ⊕ M) / c (L ⊕ M)` with
  `(L / cL) × (M / cM)`.

## Main statements

* `ZLattice.dual_orthSum`: `(L ⊕ M)^∨ = L^∨ ⊕ M^∨`.
* `ZLattice.isIntegral_orthSum_iff`, `ZLattice.isEven_orthSum_iff`,
  `ZLattice.isUnimodular_orthSum_iff`: `L ⊕ M` is integral, even or unimodular if and only if
  both `L` and `M` are.
* `ZLattice.representationNumber_orthSum`, `ZLattice.representationNumber_orthSum_eq_sum`: the
  representation numbers of `L ⊕ M` are the convolution of those of `L` and `M`, summed over the
  squared norms `s ≤ t` represented by `L`, or over any finite set containing them.
* `ZLattice.IsEven.representationNumber_orthSum`,
  `ZLattice.IsIntegral.representationNumber_orthSum`: the convolution as a sum over
  `Finset.range` for even and for integral `L`.
* `ZLattice.covolume_orthSum`, `ZLattice.det_orthSum`: covolumes and determinants of full lattices
  multiply under orthogonal direct sums.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public section

open Module Submodule MeasureTheory WithLp
open scoped Pointwise RealInnerProductSpace

namespace ZLattice

section AddCommGroup

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]

/-- The orthogonal direct sum of lattices `L ⊆ E` and `M ⊆ F`: the vectors of the `L²` product
`WithLp 2 (E × F)` whose components lie in `L` and in `M` (`mem_orthSum`). -/
def orthSum (L : Submodule ℤ E) (M : Submodule ℤ F) : Submodule ℤ (WithLp 2 (E × F)) :=
  (L.prod M).comap (WithLp.linearEquiv 2 ℤ (E × F)).toLinearMap

variable {L L' : Submodule ℤ E} {M M' : Submodule ℤ F}

/-- A vector lies in the orthogonal direct sum exactly when its two components lie in the
summands. -/
@[simp]
theorem mem_orthSum {x : WithLp 2 (E × F)} : x ∈ orthSum L M ↔ x.fst ∈ L ∧ x.snd ∈ M :=
  (Iff.rfl)

/-- The orthogonal direct sum is monotone in each summand, and reflects inclusions. -/
@[simp]
theorem orthSum_le_orthSum_iff : orthSum L M ≤ orthSum L' M' ↔ L ≤ L' ∧ M ≤ M' := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩, fun ⟨hL, hM⟩ x hx ↦ ?_⟩
  · simpa using h (x := toLp 2 (x, 0)) (by simpa using hx)
  · simpa using h (x := toLp 2 (0, y)) (by simpa using hy)
  · rw [mem_orthSum] at hx ⊢
    exact ⟨hL hx.1, hM hx.2⟩

@[gcongr]
theorem orthSum_mono (hL : L ≤ L') (hM : M ≤ M') : orthSum L M ≤ orthSum L' M' :=
  orthSum_le_orthSum_iff.mpr ⟨hL, hM⟩

@[simp]
theorem orthSum_inj : orthSum L M = orthSum L' M' ↔ L = L' ∧ M = M' := by
  simp only [le_antisymm_iff, orthSum_le_orthSum_iff]
  tauto

variable (L M) in
/-- As a `ℤ`-module, the orthogonal direct sum `L ⊕ M` is the product `L × M`: a vector of `L ⊕ M`
corresponds to the pair of its components. -/
def orthSumEquivProd : orthSum L M ≃ₗ[ℤ] L × M :=
  ((WithLp.linearEquiv 2 ℤ (E × F)).ofSubmodule' (L.prod M)).trans (L.prodEquiv M)

@[simp]
theorem coe_orthSumEquivProd_apply_fst (x : orthSum L M) :
    ((orthSumEquivProd L M x).1 : E) = (x : WithLp 2 (E × F)).fst :=
  (rfl)

@[simp]
theorem coe_orthSumEquivProd_apply_snd (x : orthSum L M) :
    ((orthSumEquivProd L M x).2 : F) = (x : WithLp 2 (E × F)).snd :=
  (rfl)

@[simp]
theorem coe_orthSumEquivProd_symm_apply (p : L × M) :
    ((orthSumEquivProd L M).symm p : WithLp 2 (E × F)) = toLp 2 ((p.1 : E), (p.2 : F)) :=
  (rfl)

instance [TopologicalSpace E] [TopologicalSpace F] (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M] : DiscreteTopology (orthSum L M) :=
  .of_continuous_injective (f := fun x : orthSum L M ↦
      ((⟨x.1.fst, (mem_orthSum.mp x.2).1⟩ : L), (⟨x.1.snd, (mem_orthSum.mp x.2).2⟩ : M)))
    (by fun_prop) fun x y h ↦ by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (ofLp_injective 2 (Prod.ext h.1 h.2))

end AddCommGroup

/-! ### The quotient `(L ⊕ M) / c (L ⊕ M)` -/

section Quotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (L : Submodule ℤ E) (M : Submodule ℤ F) (c : ℕ)

/-- The quotient `(L ⊕ M) / c (L ⊕ M)` is `(L / cL) × (M / cM)`: the class of a vector of `L ⊕ M`
corresponds to the pair of classes of its components. -/
noncomputable def quotientSmulOrthSumEquiv :
    (orthSum L M ⧸ ((c : ℝ) • orthSum L M).submoduleOf (orthSum L M)) ≃ₗ[ℤ]
      (L ⧸ ((c : ℝ) • L).submoduleOf L) × (M ⧸ ((c : ℝ) • M).submoduleOf M) :=
  let f := ((((c : ℝ) • L).submoduleOf L).mkQ.prodMap (((c : ℝ) • M).submoduleOf M).mkQ) ∘ₗ
    (orthSumEquivProd L M).toLinearMap
  have hf : Function.Surjective f :=
    (Function.Surjective.prodMap (mkQ_surjective _) (mkQ_surjective _)).comp
      (orthSumEquivProd L M).surjective
  have hker : LinearMap.ker f = ((c : ℝ) • orthSum L M).submoduleOf (orthSum L M) := by
    ext x
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.prodMap_apply, mkQ_apply,
      Prod.mk_eq_zero, Quotient.mk_eq_zero, mem_smul_submoduleOf_iff]
    constructor
    · rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩
      exact ⟨(orthSumEquivProd L M).symm (w₁, w₂),
        (orthSumEquivProd L M).injective (by simp [hw₁, hw₂])⟩
    · rintro ⟨w, rfl⟩
      exact ⟨⟨(orthSumEquivProd L M w).1, by simp⟩, ⟨(orthSumEquivProd L M w).2, by simp⟩⟩
  (quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)

/-- The class of `x ∈ L ⊕ M` corresponds to the pair of classes of the components of `x`. -/
@[simp]
theorem quotientSmulOrthSumEquiv_mk (x : orthSum L M) :
    quotientSmulOrthSumEquiv L M c (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (orthSumEquivProd L M x).1,
        Submodule.Quotient.mk (orthSumEquivProd L M x).2) :=
  (rfl)

end Quotient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The dual of an orthogonal direct sum is the orthogonal direct sum of the duals. -/
@[simp]
theorem dual_orthSum (L : Submodule ℤ E) (M : Submodule ℤ F) :
    dual (orthSum L M) = orthSum (dual L) (dual M) := by
  ext x
  simp only [mem_dual, mem_orthSum, prod_inner_apply, ofLp_fst, ofLp_snd, and_imp]
  refine ⟨fun h ↦ ⟨fun y hy ↦ ?_, fun z hz ↦ ?_⟩, fun ⟨hL, hM⟩ y hy hz ↦ ?_⟩
  · simpa using h (toLp 2 (y, 0)) (by simpa using hy) (by simp)
  · simpa using h (toLp 2 (0, z)) (by simp) (by simpa using hz)
  · obtain ⟨a, ha⟩ := hL _ hy
    obtain ⟨b, hb⟩ := hM _ hz
    exact ⟨a + b, by rw [ha, hb, Int.cast_add]⟩

/-! ### Integral, even and unimodular orthogonal direct sums -/

section Predicates

variable {L : Submodule ℤ E} {M : Submodule ℤ F}

/-- An orthogonal direct sum is integral if and only if both summands are. -/
@[simp]
theorem isIntegral_orthSum_iff : IsIntegral (orthSum L M) ↔ IsIntegral L ∧ IsIntegral M := by
  simp only [isIntegral_iff_le_dual, dual_orthSum, orthSum_le_orthSum_iff]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
/-- An orthogonal direct sum is even if and only if both summands are. -/
@[simp]
theorem isEven_orthSum_iff : IsEven (orthSum L M) ↔ IsEven L ∧ IsEven M := by
  simp only [isEven_iff]
  refine ⟨fun h ↦ ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩, fun ⟨hL, hM⟩ x hx ↦ ?_⟩
  · simpa [prod_norm_sq_eq_of_L2] using h (toLp 2 (x, 0)) (by simpa using hx)
  · simpa [prod_norm_sq_eq_of_L2] using h (toLp 2 (0, y)) (by simpa using hy)
  · rw [mem_orthSum] at hx
    obtain ⟨a, ha⟩ := hL _ hx.1
    obtain ⟨b, hb⟩ := hM _ hx.2
    exact ⟨a + b, by rw [prod_norm_sq_eq_of_L2, ha, hb]; push_cast; ring⟩

/-- An orthogonal direct sum is unimodular if and only if both summands are. -/
@[simp]
theorem isUnimodular_orthSum_iff :
    IsUnimodular (orthSum L M) ↔ IsUnimodular L ∧ IsUnimodular M := by
  simp only [isUnimodular_iff_eq_dual, dual_orthSum, orthSum_inj]

end Predicates

/-! ### Representation numbers of an orthogonal direct sum -/

section RepresentationNumber

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

variable {L : Submodule ℤ E} {M : Submodule ℤ F} {t : ℝ}

/-- The shell of squared norm `t` of `L ⊕ M` is the union, over the squared norms `s ≤ t`
represented by `L`, of the pairs of a vector of `L` of squared norm `s` and a vector of `M` of
squared norm `t - s`. Any set `S` containing those squared norms may index the union. -/
theorem shell_orthSum_eq_biUnion {S : Set ℝ} (hS : representedNormsLE L t ⊆ S) :
    shell (orthSum L M) t = ⋃ s ∈ S, ofLp ⁻¹' (shell L s ×ˢ shell M (t - s)) := by
  ext x
  simp only [mem_shell, mem_orthSum, prod_norm_sq_eq_of_L2, Set.mem_iUnion, Set.mem_preimage,
    Set.mem_prod, ofLp_fst, ofLp_snd, exists_prop]
  refine ⟨fun ⟨⟨hx₁, hx₂⟩, hx⟩ ↦ ⟨‖x.fst‖ ^ 2, hS (norm_sq_mem_representedNormsLE hx₁ ?_),
    ⟨hx₁, rfl⟩, hx₂, by rw [← hx, add_sub_cancel_left]⟩, ?_⟩
  · rw [← hx]
    exact le_add_of_nonneg_right (by positivity)
  · rintro ⟨s, -, ⟨hx₁, hs⟩, hx₂, ht⟩
    exact ⟨⟨hx₁, hx₂⟩, by rw [hs, ht, add_sub_cancel]⟩

variable [ProperSpace E] [ProperSpace F] [DiscreteTopology L] [DiscreteTopology M]

/-- The representation numbers of an orthogonal direct sum are the convolution of those of the
summands: `r_{L ⊕ M}(t) = ∑_{s ∈ S} r_L(s) * r_M(t - s)` for any finite set `S` of real numbers
containing the squared norms `s ≤ t` represented by `L`. -/
theorem representationNumber_orthSum_eq_sum {S : Finset ℝ} (hS : representedNormsLE L t ⊆ S) :
    representationNumber (orthSum L M) t =
      ∑ s ∈ S, representationNumber L s * representationNumber M (t - s) := by
  have hdisj : (S : Set ℝ).PairwiseDisjoint fun s ↦
      (ofLp ⁻¹' (shell L s ×ˢ shell M (t - s)) : Set (WithLp 2 (E × F))) :=
    fun s _ s' _ hss' ↦ Set.disjoint_left.mpr fun _ hx hx' ↦
      hss' ((mem_shell.mp hx.1).2.symm.trans (mem_shell.mp hx'.1).2)
  have hfin (s : ℝ) : (ofLp ⁻¹' (shell L s ×ˢ shell M (t - s)) : Set (WithLp 2 (E × F))).Finite :=
    ((finite_shell L s).prod (finite_shell M _)).preimage (ofLp_injective 2).injOn
  rw [representationNumber_def, shell_orthSum_eq_biUnion hS,
    Set.Finite.ncard_biUnion (S : Set ℝ).toFinite (fun s _ ↦ hfin s) hdisj, finsum_mem_coe_finset]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Set.ncard_preimage_of_injective_subset_range (ofLp_injective 2)
      (by simp [(ofLp_surjective 2).range_eq]), Set.ncard_prod, representationNumber_def,
    representationNumber_def]

variable (L M) in
/-- The representation numbers of an orthogonal direct sum are the convolution of those of the
summands, summed over the finite set of squared norms `s ≤ t` represented by `L`:
`r_{L ⊕ M}(t) = ∑_{s ≤ t represented by L} r_L(s) * r_M(t - s)`. -/
theorem representationNumber_orthSum (t : ℝ) :
    representationNumber (orthSum L M) t =
      ∑ s ∈ (finite_representedNormsLE L t).toFinset,
        representationNumber L s * representationNumber M (t - s) :=
  representationNumber_orthSum_eq_sum (by simp)

/-- For an even lattice `L`, the representation numbers of `L ⊕ M` at even integers are the
convolution `r_{L ⊕ M}(2m) = ∑_{i ≤ m} r_L(2i) * r_M(2(m - i))`. -/
theorem IsEven.representationNumber_orthSum (hL : IsEven L) (m : ℕ) :
    representationNumber (orthSum L M) (2 * m) =
      ∑ i ∈ Finset.range (m + 1),
        representationNumber L (2 * i) * representationNumber M (2 * (m - i : ℕ)) := by
  rw [representationNumber_orthSum_eq_sum (S := (Finset.range (m + 1)).image fun i : ℕ ↦ 2 * i),
    Finset.sum_image fun i _ j _ h ↦ by simpa using h]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Nat.cast_sub (Finset.mem_range_succ_iff.mp hi), mul_sub]
  · intro s hs
    obtain ⟨hst, hs⟩ := mem_representedNormsLE.mp hs
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = 2 * k := by
      by_contra hk
      exact hs.ne_empty (hL.shell_eq_empty hk)
    have hkm : k ≤ m := by exact_mod_cast (by linarith : (k : ℝ) ≤ m)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_range_succ_iff.mpr hkm))

variable [InnerProductSpace ℝ E] in
/-- For an integral lattice `L`, the representation numbers of `L ⊕ M` at natural numbers are the
convolution `r_{L ⊕ M}(n) = ∑_{i ≤ n} r_L(i) * r_M(n - i)`. -/
theorem IsIntegral.representationNumber_orthSum (hL : IsIntegral L) (n : ℕ) :
    representationNumber (orthSum L M) n =
      ∑ i ∈ Finset.range (n + 1),
        representationNumber L i * representationNumber M (n - i : ℕ) := by
  rw [representationNumber_orthSum_eq_sum (S := (Finset.range (n + 1)).image fun i : ℕ ↦ (i : ℝ)),
    Finset.sum_image fun i _ j _ h ↦ by simpa using h]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Nat.cast_sub (Finset.mem_range_succ_iff.mp hi)]
  · intro s hs
    obtain ⟨hst, hs⟩ := mem_representedNormsLE.mp hs
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, s = k := by
      by_contra hk
      exact hs.ne_empty (hL.shell_eq_empty hk)
    have hkn : k ≤ n := by exact_mod_cast hst
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_range_succ_iff.mpr hkn))

end RepresentationNumber

/-! ### Full lattices -/

section FiniteDimensional

variable {ι κ : Type*}

/-- The orthogonal direct sum of the `ℤ`-spans of two bases is the `ℤ`-span of their product
basis of `WithLp 2 (E × F)`. -/
theorem orthSum_span_basis (b : Basis ι ℝ E) (c : Basis κ ℝ F) :
    orthSum (span ℤ (Set.range b)) (span ℤ (Set.range c)) =
      span ℤ (Set.range ((b.prod c).map (WithLp.linearEquiv 2 ℝ (E × F)).symm)) := by
  rw [orthSum, ← LinearMap.span_inl_union_inr, comap_equiv_eq_map_symm, map_span,
    Basis.coe_map, Set.range_comp, funext (Basis.prod_apply b c), Set.Sum.elim_range,
    Set.range_comp, Set.range_comp]
  rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L]
  [DiscreteTopology M] [IsZLattice ℝ M]

instance : IsZLattice ℝ (orthSum L M) where
  span_top := by
    obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
    obtain ⟨κ, _, _, c, rfl⟩ := exists_basis_span_eq ℝ M
    rw [orthSum_span_basis]
    exact ZSpan.span_top _

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The covolume of an orthogonal direct sum of full lattices is the product of the
covolumes. -/
@[simp]
theorem covolume_orthSum : covolume (orthSum L M) = covolume L * covolume M := by
  obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
  obtain ⟨κ, _, _, c, rfl⟩ := exists_basis_span_eq ℝ M
  rw [orthSum_span_basis]
  -- The Gram matrix of the product basis is block diagonal, so the squared covolumes multiply.
  have hgram : Matrix.gram ℝ ((b.prod c).map (WithLp.linearEquiv 2 ℝ (E × F)).symm) =
      Matrix.fromBlocks (Matrix.gram ℝ b) 0 0 (Matrix.gram ℝ c) := by
    ext (i | i) (j | j) <;> simp [Matrix.gram_apply]
  refine (pow_left_inj₀ (covolume_pos _ volume).le
    (mul_pos (covolume_pos _ volume) (covolume_pos _ volume)).le two_ne_zero).mp ?_
  rw [mul_pow, covolume_span_sq_eq_det_gram, covolume_span_sq_eq_det_gram,
    covolume_span_sq_eq_det_gram, hgram, Matrix.det_fromBlocks_zero₂₁]

/-- The determinant of an orthogonal direct sum of full lattices is the product of the
determinants. -/
@[simp]
theorem det_orthSum : det (orthSum L M) = det L * det M := by
  rw [det_def, det_def, det_def, covolume_orthSum, mul_pow]

end FiniteDimensional

end ZLattice
