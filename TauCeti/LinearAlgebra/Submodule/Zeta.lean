/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.Submodule.Prod.Index
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Sums over the submodules of finite index

For a module `N` over a ring `R`, the *submodule zeta function* is
`ζ_N(s) = ∑_M [N : M]^(-s)`, the sum over the submodules `M` of finite index in `N`, with values
in `[0, ∞]` (`Module.submoduleZeta`). For `N = R` it is the sum over the left ideals of finite
index.

Suppose that every left ideal of finite index in `R` is principal. A submodule `M` of finite index
of `R × N` is then determined by the ideal `R ∙ g` of its first coordinates, by its intersection
`M'` with `N`, and by the class modulo `M'` of some `n` with `(g, n) ∈ M`. Since
`[R × N : M] = [R : R ∙ g] [N : M']` and there are `[N : M']` classes, this gives
`ζ_{R × N}(s + 1) ≤ ζ_R(s + 1) ζ_N(s)` (`Module.submoduleZeta_prod_le`), and by induction on the
rank `ζ_{R^r}(r + μ) ≤ ζ_R(μ)^r` (`Module.submoduleZeta_pi_le`). Both bounds are proved here
only under the principality hypothesis. When `R` is a ring of integers or one of its completions,
Hey's formula computes the left side exactly; that formula is not proved here.

The same induction, over a commutative ring, shows that a submodule `M` of finite index in `R^r`
is the image of a lower triangular matrix `A` whose diagonal entries generate ideals of finite
index, and that `[R^r : M] = ∏ᵢ [R : (A i i)]`
(`Submodule.exists_isLowerTriangular_range_mulVecLin_eq`).

## Main declarations

* `Module.submoduleZeta`: the sum of `[N : M]^(-s)` over the submodules of finite index.
* `Module.countable_of_submoduleZeta_ne_top`: if `ζ_N(s)` is finite, then `N` has only countably
  many submodules of finite index.
* `Module.submoduleZeta_le_of_surjective`: a quotient has the smaller zeta function.
* `Module.submoduleZeta_prod_le`: `ζ_{R × N}(s + 1) ≤ ζ_R(s + 1) ζ_N(s)`.
* `Module.submoduleZeta_pi_le`: `ζ_{R^r}(r + μ) ≤ ζ_R(μ)^r`.
* `Submodule.exists_isLowerTriangular_range_mulVecLin_eq`: a submodule of finite index in `R^r` has
  a lower triangular basis matrix, and its index is the product of the indices of the diagonal
  entries.

## References

* E. Hey, *Analytische Zahlentheorie in Systemen hyperkomplexer Zahlen*, Dissertation,
  Göttingen, 1929 (the zeta function of a lattice).
* L. Solomon, *Zeta functions and integral representation theory*, Advances in Math. 26 (1977),
  306–326.

## Attribution

`Module.submoduleZeta`, `Module.submoduleZeta_le_of_surjective`, `Module.submoduleZeta_prod_le`
and `Module.submoduleZeta_pi_le` are adapted from `submoduleZeta`,
`submoduleZeta_le_of_surjective`, `submoduleZeta_prod_le` and `submoduleZeta_pi_le` in the file
`src/New/Spanning/RemainingTerms/Discriminants.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The triangular
basis is new here; grh-lean obtains a basis of a submodule of finite index from a Hermite normal
form over the integral finite adeles.
-/

public section

open scoped ENNReal

namespace Submodule

variable {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]

/-- Let `M` be a submodule of finite index of `R × N` and suppose that its ideal of first
coordinates is principal. Then there are `g : R` and `n : N` with `(g, n) ∈ M`, the ideal of
first coordinates is `R ∙ g`, `M` is spanned by `(g, n)` and its intersection `M'` with `N`, and
`[R × N : M] = [R : R ∙ g] [N : M']`. -/
private theorem exists_prod_decomposition {M : Submodule R (R × N)}
    (h : (M.map (LinearMap.fst R R N)).IsPrincipal) :
    ∃ (g : R) (n : N), (g, n) ∈ M ∧ M.map (LinearMap.fst R R N) = R ∙ g ∧
      M = (R ∙ (g, n)) ⊔ (M.comap (LinearMap.inr R R N)).map (LinearMap.inr R R N) ∧
      M.cardQuot = (R ∙ g).cardQuot * (M.comap (LinearMap.inr R R N)).cardQuot := by
  obtain ⟨g, hg⟩ := h.principal
  obtain ⟨⟨g', n⟩, hn, rfl⟩ : g ∈ M.map (LinearMap.fst R R N) :=
    hg ▸ mem_span_singleton_self g
  exact ⟨g', n, hn, hg, eq_span_singleton_sup_map_inr hn hg,
    by rw [cardQuot_eq_cardQuot_map_fst_mul_cardQuot_comap_inr, hg, LinearMap.fst_apply]⟩

end Submodule

namespace Module

variable (R N : Type*) [Ring R] [AddCommGroup N] [Module R N]

/-- The **submodule zeta function** `ζ_N(s) = ∑_M [N : M]^(-s)` of an `R`-module `N`: the sum over
the submodules `M` of finite index in `N` (those with `M.cardQuot ≠ 0`), with values in
`[0, ∞]`. For `N = R` it is the sum over the left ideals of finite index of `R`. -/
noncomputable def submoduleZeta (s : ℕ) : ℝ≥0∞ :=
  ∑' M : {M : Submodule R N // M.cardQuot ≠ 0}, (M.val.cardQuot : ℝ≥0∞)⁻¹ ^ s

theorem submoduleZeta_def (s : ℕ) :
    submoduleZeta R N s = ∑' M : {M : Submodule R N // M.cardQuot ≠ 0},
      (M.val.cardQuot : ℝ≥0∞)⁻¹ ^ s :=
  (rfl)

/-- The submodule zeta function is antitone in the exponent. -/
theorem submoduleZeta_antitone : Antitone (submoduleZeta R N) := fun _ _ hst ↦
  tsum_le_tsum fun M ↦ pow_le_pow_of_le_one zero_le
    (ENNReal.inv_le_one.2 (Nat.one_le_cast.2 (Nat.pos_of_ne_zero M.property))) hst

variable {R N} {N' : Type*} [AddCommGroup N'] [Module R N']

/-- If the zeta function of `N` is finite at some exponent, then `N` has only countably many
submodules of finite index, since each of them contributes a positive term to the sum. -/
theorem countable_of_submoduleZeta_ne_top {s : ℕ} (h : submoduleZeta R N s ≠ ∞) :
    Countable {M : Submodule R N // M.cardQuot ≠ 0} :=
  Set.countable_univ_iff.1 <| (Summable.countable_support_ennreal h).mono fun _ _ ↦
    pow_ne_zero _ (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))

/-- If `N` maps onto `N'`, then the zeta function of `N'` is at most that of `N`. -/
theorem submoduleZeta_le_of_surjective {f : N →ₗ[R] N'} (hf : Function.Surjective f) (s : ℕ) :
    submoduleZeta R N' s ≤ submoduleZeta R N s := by
  -- Pulling back is an injection of the submodules of finite index that keeps the index.
  have h_index (M : Submodule R N') : (M.comap f).cardQuot = M.cardQuot :=
    Submodule.cardQuot_comap_of_surjective hf M
  let pull (M : {M : Submodule R N' // M.cardQuot ≠ 0}) : {M : Submodule R N // M.cardQuot ≠ 0} :=
    ⟨M.val.comap f, (h_index M.val).trans_ne M.property⟩
  have h_inj : Function.Injective pull := fun M₁ M₂ h_eq ↦
    Subtype.ext (Submodule.comap_injective_of_surjective hf (congrArg Subtype.val h_eq))
  calc submoduleZeta R N' s = ∑' M, ((pull M).val.cardQuot : ℝ≥0∞)⁻¹ ^ s :=
        tsum_congr fun M ↦ by simp only [pull, h_index]
    _ ≤ submoduleZeta R N s :=
      tsum_comp_le_tsum_of_injective h_inj fun M ↦ (M.val.cardQuot : ℝ≥0∞)⁻¹ ^ s

/-- Linearly equivalent modules have the same zeta function. -/
theorem submoduleZeta_congr (e : N ≃ₗ[R] N') (s : ℕ) :
    submoduleZeta R N s = submoduleZeta R N' s :=
  le_antisymm (submoduleZeta_le_of_surjective e.symm.surjective s)
    (submoduleZeta_le_of_surjective e.surjective s)

/-- Summing `[N : M]^(-(s + 1))` over the `[N : M]` classes modulo a submodule `M` of finite
index gives `[N : M]^(-s)`. -/
private theorem tsum_quotient_cardQuot_inv_pow {M : Submodule R N} (hM : M.cardQuot ≠ 0) (s : ℕ) :
    ∑' _ : N ⧸ M, (M.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) = (M.cardQuot : ℝ≥0∞)⁻¹ ^ s := by
  have : Finite (N ⧸ M) := Nat.finite_of_card_ne_zero (by rwa [← Submodule.cardQuot_apply])
  have h_card : (ENat.card (N ⧸ M) : ℝ≥0∞) = M.cardQuot := by
    rw [ENat.card_eq_coe_natCard, Submodule.cardQuot_apply, ENat.toENNReal_coe]
  rw [ENNReal.tsum_const, h_card, pow_succ', ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hM) (ENNReal.natCast_ne_top _), one_mul]

/-- **The zeta function of `R × N`.** If every left ideal of finite index of `R` is principal,
then `ζ_{R × N}(s + 1) ≤ ζ_R(s + 1) ζ_N(s)`. -/
theorem submoduleZeta_prod_le
    (h_principal : ∀ I : Submodule R R, I.cardQuot ≠ 0 → I.IsPrincipal) (s : ℕ) :
    submoduleZeta R (R × N) (s + 1) ≤ submoduleZeta R R (s + 1) * submoduleZeta R N s := by
  -- A submodule `M` of finite index is determined by the ideal `R ∙ g` of its first coordinates,
  -- by its intersection `M'` with `N`, and by the class modulo `M'` of some `n` with `(g, n) ∈ M`;
  -- there are `[N : M']` classes, and `[R × N : M] = [R : R ∙ g] [N : M']`.
  choose gen h_gen using fun I : {I : Submodule R R // I.cardQuot ≠ 0} ↦
    (h_principal I.val I.property).principal
  let Data : Type _ := Σ (_ : {I : Submodule R R // I.cardQuot ≠ 0})
    (M' : {M' : Submodule R N // M'.cardQuot ≠ 0}), N ⧸ M'.val
  let build : Data → Submodule R (R × N) := fun ⟨I, M', c⟩ ↦
    (R ∙ (gen I, c.out)) ⊔ M'.val.map (LinearMap.inr R R N)
  let weight : Data → ℝ≥0∞ := fun ⟨I, M', _⟩ ↦
    (I.val.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) * (M'.val.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1)
  have h_data (M : {M : Submodule R (R × N) // M.cardQuot ≠ 0}) :
      ∃ d : Data, build d = M.val ∧ weight d = (M.val.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) := by
    have h_index := Submodule.cardQuot_eq_cardQuot_map_fst_mul_cardQuot_comap_inr M.val
    obtain ⟨hI, hM'⟩ := mul_ne_zero_iff.1 (h_index.symm.trans_ne M.property)
    let I : {I : Submodule R R // I.cardQuot ≠ 0} := ⟨M.val.map (LinearMap.fst R R N), hI⟩
    obtain ⟨⟨g, n⟩, hn, hg⟩ : gen I ∈ M.val.map (LinearMap.fst R R N) :=
      (h_gen I).ge (Submodule.mem_span_singleton_self _)
    let M' : {M' : Submodule R N // M'.cardQuot ≠ 0} := ⟨M.val.comap (LinearMap.inr R R N), hM'⟩
    let c : N ⧸ M'.val := Submodule.Quotient.mk n
    have h_congr : c.out - n ∈ M'.val := (Submodule.Quotient.eq _).1 c.out_eq
    have h_mem : (gen I, c.out) ∈ M.val := by simpa [← hg] using M.val.add_mem hn h_congr
    refine ⟨⟨I, M', c⟩, (Submodule.eq_span_singleton_sup_map_inr h_mem (h_gen I)).symm, ?_⟩
    rw [h_index, Nat.cast_mul, ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _))
      (.inl (ENNReal.natCast_ne_top _)), mul_pow]
  choose data h_build h_weight using h_data
  have h_inj : Function.Injective data := fun M₁ M₂ h_eq ↦
    Subtype.ext (by rw [← h_build, h_eq, h_build])
  have h_classes (M' : {M' : Submodule R N // M'.cardQuot ≠ 0}) :
      ∑' _ : N ⧸ M'.val, (M'.val.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) = (M'.val.cardQuot : ℝ≥0∞)⁻¹ ^ s :=
    tsum_quotient_cardQuot_inv_pow M'.property s
  calc submoduleZeta R (R × N) (s + 1)
    _ = ∑' M, weight (data M) := tsum_congr fun M ↦ (h_weight M).symm
    _ ≤ ∑' d, weight d := tsum_comp_le_tsum_of_injective h_inj weight
    _ = submoduleZeta R R (s + 1) * submoduleZeta R N s := by
      simp only [Data, weight, tsum_sigma', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
        submoduleZeta_def, h_classes]

/-- **Sums over the submodules of finite index of `R^r`.** If every left ideal of finite index
of `R` is principal, then `∑_M [R^r : M]^(-(r + μ)) ≤ (∑_I [R : I]^(-μ))^r`, the sums running
over the submodules `M` of finite index of `R^r` and over the left ideals `I` of finite index of
`R`. -/
theorem submoduleZeta_pi_le
    (h_principal : ∀ I : Submodule R R, I.cardQuot ≠ 0 → I.IsPrincipal) (r μ : ℕ) :
    submoduleZeta R (Fin r → R) (r + μ) ≤ submoduleZeta R R μ ^ r := by
  induction r with
  | zero =>
    let top : {M : Submodule R (Fin 0 → R) // M.cardQuot ≠ 0} := ⟨⊤, by simp⟩
    rw [submoduleZeta_def,
      tsum_eq_single top fun M hM ↦ absurd (Subtype.ext (Subsingleton.elim M.val top.val)) hM]
    simp [top]
  | succ r ih =>
    calc submoduleZeta R (Fin (r + 1) → R) (r + 1 + μ)
      _ = submoduleZeta R (R × (Fin r → R)) (r + μ + 1) := by
        rw [add_right_comm]
        exact (submoduleZeta_congr (Fin.consLinearEquiv R fun _ ↦ R) _).symm
      _ ≤ submoduleZeta R R (r + μ + 1) * submoduleZeta R (Fin r → R) (r + μ) :=
        submoduleZeta_prod_le h_principal _
      _ ≤ submoduleZeta R R μ * submoduleZeta R R μ ^ r :=
        mul_le_mul' (submoduleZeta_antitone R R (by omega)) ih
      _ = submoduleZeta R R μ ^ (r + 1) := (pow_succ' _ r).symm

end Module

namespace Submodule

variable {R : Type*} [CommRing R] {r : ℕ}

/-- The matrix with first column `e (g, n)` and further columns `e (0, A'.col j)`, where
`e : R × R^r ≃ R^(r+1)` puts a first coordinate in front. -/
private def consMatrix (g : R) (n : Fin r → R) (A' : Matrix (Fin r) (Fin r) R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun i j ↦
    (Fin.cons (Fin.cons g n) fun j ↦ Fin.cons 0 (A'.col j) : Fin (r + 1) → Fin (r + 1) → R) j i

private theorem consMatrix_zero_zero (g : R) (n : Fin r → R) (A' : Matrix (Fin r) (Fin r) R) :
    consMatrix g n A' 0 0 = g := rfl

private theorem consMatrix_succ_succ (g : R) (n : Fin r → R) (A' : Matrix (Fin r) (Fin r) R)
    (i j : Fin r) : consMatrix g n A' i.succ j.succ = A' i j := rfl

private theorem consMatrix_zero_succ (g : R) (n : Fin r → R) (A' : Matrix (Fin r) (Fin r) R)
    (j : Fin r) : consMatrix g n A' 0 j.succ = 0 := rfl

private theorem isLowerTriangular_consMatrix (g : R) (n : Fin r → R)
    {A' : Matrix (Fin r) (Fin r) R} (hA' : A'.IsLowerTriangular) :
    (consMatrix g n A').IsLowerTriangular := by
  intro i j hij
  replace hij : i < j := OrderDual.toDual_lt_toDual.1 hij
  induction j using Fin.cases with
  | zero => exact absurd hij (Fin.not_lt_zero i)
  | succ j =>
    induction i using Fin.cases with
    | zero => exact consMatrix_zero_succ g n A' j
    | succ i => exact (consMatrix_succ_succ g n A' i j).trans (hA' (Fin.succ_lt_succ_iff.1 hij))

/-- The columns of `consMatrix g n A'` span the image under `R × R^r ≃ R^(r+1)` of the span of
`(g, n)` and of the image of `A'` in the second factor. -/
private theorem range_mulVecLin_consMatrix (g : R) (n : Fin r → R)
    (A' : Matrix (Fin r) (Fin r) R) :
    LinearMap.range (consMatrix g n A').mulVecLin =
      ((R ∙ (g, n)) ⊔ (LinearMap.range A'.mulVecLin).map (LinearMap.inr R R (Fin r → R))).map
        (Fin.consLinearEquiv R fun _ : Fin (r + 1) ↦ R).toLinearMap := by
  have h_col : (consMatrix g n A').col =
      Fin.cons (Fin.consLinearEquiv R (fun _ : Fin (r + 1) ↦ R) (g, n))
        fun j ↦ Fin.consLinearEquiv R (fun _ : Fin (r + 1) ↦ R) (0, A'.col j) := by
    -- `consMatrix` is defined column by column as these `Fin.cons` vectors, and
    -- `Fin.consLinearEquiv` applies `Fin.cons`, so both sides agree by definition.
    funext j i
    rfl
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin, h_col, Fin.range_cons, span_insert, map_sup,
    map_span, Set.image_singleton, ← map_comp, map_span, ← Set.range_comp]
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, Function.comp_def, LinearMap.inr_apply]

/-- **A triangular basis of a submodule of finite index.** Let `R` be a commutative ring whose
ideals of finite index are principal, and `M` a submodule of finite index of `R^r`. Then `M` is
the image of a lower triangular `r × r` matrix `A`, and `[R^r : M]` is the product of the indices
`[R : (A i i)]` of the ideals generated by its diagonal entries. -/
theorem exists_isLowerTriangular_range_mulVecLin_eq
    (h_principal : ∀ I : Ideal R, I.cardQuot ≠ 0 → I.IsPrincipal) (M : Submodule R (Fin r → R))
    (hM : M.cardQuot ≠ 0) :
    ∃ A : Matrix (Fin r) (Fin r) R, A.IsLowerTriangular ∧
      LinearMap.range A.mulVecLin = M ∧ M.cardQuot = ∏ i, (Ideal.span {A i i}).cardQuot := by
  induction r with
  | zero =>
    refine ⟨0, fun i ↦ i.elim0, Subsingleton.elim _ _, ?_⟩
    rw [Subsingleton.elim M ⊤, cardQuot_top, Finset.univ_eq_empty, Finset.prod_empty]
  | succ r ih =>
    set e := Fin.consLinearEquiv R fun _ : Fin (r + 1) ↦ R
    set M₁ := M.comap e.toLinearMap
    have hM₁ : M₁.cardQuot = M.cardQuot := cardQuot_comap_of_surjective e.surjective M
    obtain ⟨hI, hM'⟩ := mul_ne_zero_iff.1
      ((cardQuot_eq_cardQuot_map_fst_mul_cardQuot_comap_inr M₁).symm.trans_ne (hM₁.trans_ne hM))
    obtain ⟨g, n, -, -, h_eq, h_index⟩ := exists_prod_decomposition (h_principal _ hI)
    obtain ⟨A', hA'_tri, hA'_range, hA'_index⟩ := ih _ hM'
    refine ⟨consMatrix g n A', isLowerTriangular_consMatrix g n hA'_tri, ?_, ?_⟩
    · rw [range_mulVecLin_consMatrix, hA'_range, ← h_eq]
      exact map_comap_eq_of_surjective e.surjective M
    · rw [← hM₁, h_index, hA'_index, Fin.prod_univ_succ, consMatrix_zero_zero]
      simp only [consMatrix_succ_succ]

end Submodule
