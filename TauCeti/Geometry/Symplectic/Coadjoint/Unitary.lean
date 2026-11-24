/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.UnitaryGroup.Kostant
public import TauCeti.Geometry.Symplectic.Coadjoint
public import TauCeti.Geometry.Symplectic.Orientation

import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Symplectic.Transport
import TauCeti.LinearAlgebra.Complex.Orientation

/-!
# Root planes, dimension and orientation of the coadjoint orbits of `U(n)`

Identify `𝔲(n)*` with the Hermitian matrices by the trace pairing `⟨H, X⟩ = -i tr(H X)`
(`TauCeti.unitaryTracePairing`). Every coadjoint orbit of `U(n)` meets the diagonal, so it passes
through a covector `ν_s = ⟨diag(s), ·⟩` for a real tuple `s` (`TauCeti.unitaryTorusDualInclusion`).
This file computes the Kirillov–Kostant–Souriau form `ω_s([X], [Y]) = ν_s ⁅X, Y⁆` on the algebraic
tangent model `𝔲(n) ⧸ 𝔲(n)_s` of that orbit (`Module.Dual.kksSymplecticForm`) explicitly, and with
it the dimension and the symplectic orientation of the orbit.

In matrix entries the form is
`ω_s([X], [Y]) = ∑ₐ ∑_b (sₐ - s_b) Im (X_(a b) Y_(b a))`
(`TauCeti.kksForm_unitaryTorusDualInclusion_mk`). The stabilizer `𝔲(n)_s` consists of the
`X ∈ 𝔲(n)` with `X_(j k) = 0` whenever `s_j ≠ s_k`
(`TauCeti.mem_lieAnnihilator_unitaryTorusDualInclusion_iff`), so the tangent model is described
by the entries `X_(j k)` over the pairs `(j, k)` with `s_k < s_j`. These entries are complex
coordinates on it (`TauCeti.unitaryRootCoordinates s`), and in them

`ω_s(u, v) = ∑_(s_k < s_j) 2 (s_j - s_k) Im (conj (u_(j k)) v_(j k))`

(`TauCeti.kksForm_unitaryTorusDualInclusion_eq_sum`). The coordinate `(j, k)` is the root plane
spanned by the classes of the root vectors `z E_(j k) - conj z E_(k j)`
(`TauCeti.unitaryRootVector`): distinct root planes are `ω_s`-orthogonal, and on one plane
`ω_s([z E_(j k) - …], [w E_(j k) - …]) = 2 (s_j - s_k) Im (conj z w)`
(`TauCeti.kksForm_unitaryTorusDualInclusion_mk_unitaryRootVector`).

Consequently:

* **Dimension.** The tangent model has real dimension the number of ordered pairs `(j, k)` with
  `s_j ≠ s_k` (`TauCeti.finrank_quotient_lieAnnihilator_unitaryTorusDualInclusion`), and the
  stabilizer the number of pairs with `s_j = s_k`
  (`TauCeti.finrank_lieAnnihilator_unitaryTorusDualInclusion`). If the distinct values of `s`
  have multiplicities `m₁, …, m_r`, these are `n² - ∑ mᵢ²` and `∑ mᵢ²`.
* **Compatible complex structure.** Since every coefficient `2 (s_j - s_k)` is positive,
  multiplication of the coordinates by `i` (`TauCeti.unitaryRootComplexStructure s`) is a complex
  structure compatible with `ω_s` (`TauCeti.compatible_unitaryRootComplexStructure`).
* **Orientation.** Hence the root-plane basis `([E_(j k) - E_(k j)], [i E_(j k) + i E_(k j)])`
  over the pairs with `s_k < s_j`, in any order of the pairs
  (`TauCeti.unitaryRootBasis s`), is positive for the symplectic orientation of `ω_s`
  (`TauCeti.orientation_unitaryRootBasis`).

The positive coordinates are the entries `X_(j k)` with `s_j > s_k`, so they depend on `s` and
not on an ordering of the index type: for `s` strictly decreasing along an ordering of `ι` they
are the entries above the diagonal, and for other orderings of the values of `s` they are not.
The orientation is thus computed from `ω_s` itself, not taken from a fixed complex structure on
the matrix entries.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. **14** (1982),
  1–15, §1.
-/

public section

noncomputable section

open Matrix Module Complex ComplexConjugate

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Root vectors -/

/-- The **root vectors** `z E_(j k) - conj z E_(k j)` of `𝔲(n)`, as a real linear map of `z ∈ ℂ`.
For `j ≠ k` its range is the real root plane of the pair `{j, k}`. -/
def unitaryRootVector (j k : ι) : ℂ →ₗ[ℝ] unitaryLieAlgebra ι where
  toFun z := ⟨single j k z - single k j (conj z), by
    rw [mem_unitaryLieAlgebra_iff, conjTranspose_sub, conjTranspose_single, conjTranspose_single]
    simp only [star_def, conj_conj, neg_sub]⟩
  map_add' z w := Subtype.ext (by simp [single_add]; abel)
  map_smul' c z := Subtype.ext (by
    ext a b
    simp [single, real_smul, mul_sub])

@[simp]
theorem coe_unitaryRootVector_apply (j k : ι) (z : ℂ) :
    (unitaryRootVector j k z : Matrix ι ι ℂ) = single j k z - single k j (conj z) :=
  (rfl)

/-- For pairs `(j, k)` and `(a, b)` on which `s` decreases, the root vector of `(j, k)` has entry
`z` at `(j, k)` and vanishes at every other such pair. -/
theorem unitaryRootVector_apply_of_lt (s : ι → ℝ) {j k a b : ι} (hjk : s k < s j)
    (hab : s b < s a) (z : ℂ) :
    (unitaryRootVector j k z : Matrix ι ι ℂ) a b = if j = a ∧ k = b then z else 0 := by
  have h : ¬(k = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hjk hab
  simp only [coe_unitaryRootVector_apply, Matrix.sub_apply, single, of_apply, h, ite_false,
    sub_zero]

/-! ### The stabilizer of a diagonal covector -/

/-- **The coadjoint stabilizer of `⟨diag(s), ·⟩` in `𝔲(n)`**: `X` stabilizes it exactly when its
entries `X_(j k)` vanish whenever `s_j ≠ s_k`, that is when `X` is block diagonal for the
eigenspaces of `diag(s)`. -/
theorem mem_lieAnnihilator_unitaryTorusDualInclusion_iff {s : ι → ℝ}
    {X : unitaryLieAlgebra ι} :
    X ∈ lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s) ↔
      ∀ j k, s j ≠ s k → (X : Matrix ι ι ℂ) j k = 0 := by
  rw [unitaryTorusDualInclusion_apply, mem_lieAnnihilator_unitaryTracePairing_iff]
  constructor
  · intro h j k hjk
    have h' := congr_fun (congr_fun h j) k
    rw [mul_diagonal, diagonal_mul] at h'
    have hne : (s j : ℂ) - s k ≠ 0 := sub_ne_zero.mpr (ofReal_injective.ne hjk)
    exact (mul_eq_zero.mp (by linear_combination -h' : ((s j : ℂ) - s k) * _ = 0)).resolve_left
      hne
  · intro h
    ext j k
    rw [mul_diagonal, diagonal_mul]
    by_cases hjk : s j = s k
    · rw [hjk, mul_comm]
    · rw [h j k hjk, zero_mul, mul_zero]

/-! ### The Kirillov–Kostant–Souriau form in matrix entries -/

/-- **The KKS form of a diagonal covector in matrix entries**: on the tangent model of the
coadjoint orbit through `⟨diag(s), ·⟩`,
`ω([X], [Y]) = ∑ₐ ∑_b (sₐ - s_b) Im (X_(a b) Y_(b a))`. -/
theorem kksForm_unitaryTorusDualInclusion_mk (s : ι → ℝ) (X Y : unitaryLieAlgebra ι) :
    (unitaryTorusDualInclusion ι s).kksForm (Submodule.Quotient.mk X) (Submodule.Quotient.mk Y) =
      ∑ a, ∑ b, (s a - s b) * ((X : Matrix ι ι ℂ) a b * (Y : Matrix ι ι ℂ) b a).im := by
  rw [Module.Dual.kksForm_mk, unitaryTorusDualInclusion_apply_apply]
  simp only [LieSubalgebra.coe_bracket, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, sub_im,
    im_sum,
    mul_sub, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
  -- Exchanging the two summation indices in the second sum turns it into `∑ₐ ∑_b s_b Im (…)`.
  rw [Finset.sum_comm
    (f := fun a b => s a * ((Y : Matrix ι ι ℂ) a b * (X : Matrix ι ι ℂ) b a).im)]
  simp only [mul_comm ((Y : Matrix ι ι ℂ) _ _)]

/-- Symmetrization of the entry formula: the summand of `kksForm_unitaryTorusDualInclusion_mk` is
symmetric in `(a, b)` for skew-Hermitian `X, Y`, and vanishes when `sₐ = s_b`, so the double sum
is twice the sum over the pairs with `s_b < sₐ`. -/
private theorem sum_sum_sub_mul_im_eq (s : ι → ℝ) (X Y : unitaryLieAlgebra ι) :
    ∑ a, ∑ b, (s a - s b) * ((X : Matrix ι ι ℂ) a b * (Y : Matrix ι ι ℂ) b a).im =
      ∑ p : {p : ι × ι // s p.2 < s p.1}, 2 * (s p.val.1 - s p.val.2) *
        (conj ((X : Matrix ι ι ℂ) p.val.1 p.val.2) * (Y : Matrix ι ι ℂ) p.val.1 p.val.2).im := by
  set f : ι × ι → ℝ := fun p =>
    (s p.1 - s p.2) * ((X : Matrix ι ι ℂ) p.1 p.2 * (Y : Matrix ι ι ℂ) p.2 p.1).im
  have hX := coe_unitaryLieAlgebra_apply_swap X
  have hY := coe_unitaryLieAlgebra_apply_swap Y
  -- The summand is symmetric under exchanging `a` and `b`.
  have hswap (p : ι × ι) : f p.swap = f p := by
    simp only [f, Prod.fst_swap, Prod.snd_swap, hX p.1 p.2, hY p.1 p.2]
    simp only [mul_im, neg_re, neg_im, conj_re, conj_im]
    ring
  -- Split the pairs by the sign of `s a - s b`; the pairs with `s a = s b` contribute nothing.
  have hsplit (p : ι × ι) : f p =
      (if s p.2 < s p.1 then f p else 0) + (if s p.1 < s p.2 then f p else 0) := by
    rcases lt_trichotomy (s p.1) (s p.2) with h | h | h
    · simp [h, h.not_gt]
    · simp [f, h]
    · simp [h, h.not_gt]
  have hlt : ∑ p : ι × ι, (if s p.1 < s p.2 then f p else 0) =
      ∑ p : ι × ι, (if s p.2 < s p.1 then f p else 0) := by
    refine Fintype.sum_equiv (Equiv.prodComm ι ι) _ _ fun p => ?_
    rw [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hswap p]
  rw [← Fintype.sum_prod_type f, Fintype.sum_congr _ _ hsplit, Finset.sum_add_distrib, hlt,
    ← two_mul, ← Finset.sum_filter,
    Finset.sum_subtype (p := fun p : ι × ι => s p.2 < s p.1) _ (fun p => by simp),
    Finset.mul_sum]
  refine Fintype.sum_congr _ _ fun p => ?_
  simp only [f, hY p.val.1 p.val.2]
  simp only [mul_im, neg_re, neg_im, conj_re, conj_im]
  ring

/-! ### Complex coordinates on the tangent model -/

/-- The entries `X_(j k)` of `X ∈ 𝔲(n)` over the pairs `(j, k)` with `s_k < s_j`. -/
private def rootEntries (s : ι → ℝ) :
    unitaryLieAlgebra ι →ₗ[ℝ] ({p : ι × ι // s p.2 < s p.1} → ℂ) :=
  LinearMap.pi fun p => entryLinearMap ℝ ℂ p.val.1 p.val.2 ∘ₗ (unitaryLieAlgebra ι).incl.toLinearMap

@[simp]
private theorem rootEntries_apply (s : ι → ℝ) (X : unitaryLieAlgebra ι)
    (p : {p : ι × ι // s p.2 < s p.1}) : rootEntries s X p = (X : Matrix ι ι ℂ) p.val.1 p.val.2
        := by
  simp [rootEntries]

private theorem ker_rootEntries (s : ι → ℝ) :
    LinearMap.ker (rootEntries s) =
      (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule := by
  ext X
  rw [LinearMap.mem_ker, LieSubalgebra.mem_toSubmodule,
    mem_lieAnnihilator_unitaryTorusDualInclusion_iff, funext_iff]
  simp only [rootEntries_apply, Pi.zero_apply]
  refine ⟨fun h j k hjk => ?_, fun h p => h _ _ p.property.ne'⟩
  rcases hjk.lt_or_gt with hjk | hjk
  · -- For `s j < s k`, the entry `X_(j k)` is `-conj X_(k j)`, and `X_(k j)` is a coordinate.
    rw [coe_unitaryLieAlgebra_apply_swap X k j, h ⟨(k, j), hjk⟩, map_zero, neg_zero]
  · exact h ⟨(j, k), hjk⟩

private theorem rootEntries_unitaryRootVector (s : ι → ℝ) (p : {p : ι × ι // s p.2 < s p.1})
    (z : ℂ) : rootEntries s (unitaryRootVector p.val.1 p.val.2 z) = Pi.single p z := by
  funext q
  rw [Pi.single_apply, rootEntries_apply, unitaryRootVector_apply_of_lt s p.property q.property z]
  refine if_congr ?_ rfl rfl
  rw [Subtype.ext_iff, Prod.ext_iff, eq_comm (a := q.val.1), eq_comm (a := q.val.2)]

private theorem rootEntries_surjective (s : ι → ℝ) : Function.Surjective (rootEntries s) :=
  fun f => ⟨∑ p, unitaryRootVector p.val.1 p.val.2 (f p),
    by simp only [map_sum, rootEntries_unitaryRootVector, Finset.univ_sum_single]⟩

variable (s : ι → ℝ)

/-- **Complex coordinates on the tangent model of a coadjoint orbit of `U(n)`.** At the covector
`⟨diag(s), ·⟩`, the class of `X ∈ 𝔲(n)` modulo the stabilizer is determined by the entries
`X_(j k)` over the pairs `(j, k)` with `s_k < s_j`, and these entries are arbitrary: the map
`[X] ↦ (X_(j k))` is a real linear equivalence. -/
def unitaryRootCoordinates (s : ι → ℝ) :
    (unitaryLieAlgebra ι ⧸
        (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) ≃ₗ[ℝ]
      ({p : ι × ι // s p.2 < s p.1} → ℂ) :=
  (Submodule.quotEquivOfEq _ _ (ker_rootEntries s).symm).trans
    ((rootEntries s).quotKerEquivOfSurjective (rootEntries_surjective s))

@[simp]
theorem unitaryRootCoordinates_mk (X : unitaryLieAlgebra ι) (p : {p : ι × ι // s p.2 < s p.1}) :
    unitaryRootCoordinates s (Submodule.Quotient.mk X) p = (X : Matrix ι ι ℂ) p.val.1 p.val.2 := by
  rw [unitaryRootCoordinates, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, rootEntries_apply]

/-- The root vectors of the pairs with `s_k < s_j` are the coordinate vectors of
`TauCeti.unitaryRootCoordinates s`. -/
@[simp]
theorem unitaryRootCoordinates_mk_unitaryRootVector (p : {p : ι × ι // s p.2 < s p.1}) (z : ℂ) :
    unitaryRootCoordinates s (Submodule.Quotient.mk (unitaryRootVector p.val.1 p.val.2 z)) =
      Pi.single p z :=
  rootEntries_unitaryRootVector s p z

/-- The inverse of `TauCeti.unitaryRootCoordinates s` sends coordinates `f` to the class of the sum
of the root vectors with parameters `f p`. -/
@[simp]
theorem unitaryRootCoordinates_symm_apply (f : {p : ι × ι // s p.2 < s p.1} → ℂ) :
    (unitaryRootCoordinates s).symm f =
      Submodule.Quotient.mk (∑ p, unitaryRootVector p.val.1 p.val.2 (f p)) := by
  rw [LinearEquiv.symm_apply_eq, ← Submodule.mkQ_apply, map_sum, map_sum]
  simp only [Submodule.mkQ_apply, unitaryRootCoordinates_mk_unitaryRootVector,
    Finset.univ_sum_single]

/-- **The KKS form of a coadjoint orbit of `U(n)` in root coordinates**: at `⟨diag(s), ·⟩`,
`ω(u, v) = ∑_(s_k < s_j) 2 (s_j - s_k) Im (conj (u_(j k)) v_(j k))`, a sum of positive multiples of
the standard area forms of the coordinate planes. -/
theorem kksForm_unitaryTorusDualInclusion_eq_sum (x y : unitaryLieAlgebra ι ⧸
    (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) :
    (unitaryTorusDualInclusion ι s).kksForm x y =
      ∑ p : {p : ι × ι // s p.2 < s p.1}, 2 * (s p.val.1 - s p.val.2) *
        (conj (unitaryRootCoordinates s x p) * unitaryRootCoordinates s y p).im := by
  induction x using Submodule.Quotient.induction_on
  induction y using Submodule.Quotient.induction_on
  rw [kksForm_unitaryTorusDualInclusion_mk, sum_sum_sub_mul_im_eq]
  simp only [unitaryRootCoordinates_mk]

/-- **The root planes are `ω`-orthogonal, with explicit areas**: for pairs `p = (j, k)` and
`q = (l, m)` on which `s` decreases, the classes of the root vectors satisfy
`ω([z E_(j k) - …], [w E_(l m) - …]) = 2 (s_j - s_k) Im (conj z w)` if `p = q`, and `0`
otherwise. -/
theorem kksForm_unitaryTorusDualInclusion_mk_unitaryRootVector
    (p q : {p : ι × ι // s p.2 < s p.1}) (z w : ℂ) :
    (unitaryTorusDualInclusion ι s).kksForm
        (Submodule.Quotient.mk (unitaryRootVector p.val.1 p.val.2 z))
        (Submodule.Quotient.mk (unitaryRootVector q.val.1 q.val.2 w)) =
      if p = q then 2 * (s p.val.1 - s p.val.2) * (conj z * w).im else 0 := by
  rw [kksForm_unitaryTorusDualInclusion_eq_sum, unitaryRootCoordinates_mk_unitaryRootVector,
    unitaryRootCoordinates_mk_unitaryRootVector, Finset.sum_eq_single p]
  · split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]
  · intro r _ hr
    simp [Pi.single_apply, hr]
  · simp

/-! ### Dimension -/

/-- The tangent model has twice as many real dimensions as there are pairs with `s_k < s_j`. -/
theorem finrank_quotient_lieAnnihilator_unitaryTorusDualInclusion_eq_two_mul :
    finrank ℝ (unitaryLieAlgebra ι ⧸
        (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) =
      2 * Fintype.card {p : ι × ι // s p.2 < s p.1} := by
  rw [(unitaryRootCoordinates s).finrank_eq, finrank_pi_fintype, Finset.sum_const,
    finrank_real_complex, smul_eq_mul, Finset.card_univ, mul_comm]

/-- **The dimension of a coadjoint orbit of `U(n)`**: at `⟨diag(s), ·⟩` the tangent model has real
dimension the number of ordered pairs `(j, k)` with `s_j ≠ s_k`. If the distinct values of `s`
have multiplicities `m₁, …, m_r`, this is `n² - ∑ mᵢ²`. -/
theorem finrank_quotient_lieAnnihilator_unitaryTorusDualInclusion :
    finrank ℝ (unitaryLieAlgebra ι ⧸
        (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) =
      Fintype.card {p : ι × ι // s p.1 ≠ s p.2} := by
  rw [finrank_quotient_lieAnnihilator_unitaryTorusDualInclusion_eq_two_mul, two_mul]
  -- The pairs with `s_j ≠ s_k` are those with `s_k < s_j` and their transposes.
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun p => ne_iff_lt_or_gt.trans or_comm),
    Fintype.card_subtype_or_disjoint _ _ fun _ hp hq x hx => lt_asymm (hp x hx) (hq x hx),
    Fintype.card_congr ((Equiv.prodComm ι ι).subtypeEquiv fun _ => Iff.rfl :
      {p : ι × ι // s p.1 < s p.2} ≃ {p : ι × ι // s p.2 < s p.1})]

/-- **The dimension of the coadjoint stabilizer** of `⟨diag(s), ·⟩` in `𝔲(n)` is the number of
ordered pairs `(j, k)` with `s_j = s_k`: the sum `∑ mᵢ²` of the squares of the multiplicities of
the values of `s`. -/
theorem finrank_lieAnnihilator_unitaryTorusDualInclusion :
    finrank ℝ (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule =
      Fintype.card {p : ι × ι // s p.1 = s p.2} := by
  have h := Submodule.finrank_quotient_add_finrank
    (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule
  rw [finrank_quotient_lieAnnihilator_unitaryTorusDualInclusion, finrank_unitaryLieAlgebra,
    ← Fintype.card_prod] at h
  have hc : Fintype.card {p : ι × ι // s p.1 = s p.2} + Fintype.card {p : ι × ι // s p.1 ≠ s p.2} =
      Fintype.card (ι × ι) := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl fun p : ι × ι => s p.1 = s p.2)
  omega

/-! ### The compatible complex structure and the orientation -/

/-- **The complex structure of a coadjoint orbit of `U(n)` at a diagonal covector**: multiplication
of the root coordinates `TauCeti.unitaryRootCoordinates s` by `i`. It is compatible with the KKS
form (`TauCeti.compatible_unitaryRootComplexStructure`). -/
def unitaryRootComplexStructure : AlmostComplexStructure (unitaryLieAlgebra ι ⧸
    (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) :=
  (AlmostComplexStructure.ofComplexModule ({p : ι × ι // s p.2 < s p.1} → ℂ)).transport
    (unitaryRootCoordinates s).symm

@[simp]
theorem unitaryRootCoordinates_unitaryRootComplexStructure (x : unitaryLieAlgebra ι ⧸
    (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) :
    unitaryRootCoordinates s (unitaryRootComplexStructure s x) =
      I • unitaryRootCoordinates s x := by
  rw [unitaryRootComplexStructure, AlmostComplexStructure.transport_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, AlmostComplexStructure.ofComplexModule_apply]

/-- The complex structure multiplies the parameter of a root vector by `i`. -/
@[simp]
theorem unitaryRootComplexStructure_mk_unitaryRootVector (p : {p : ι × ι // s p.2 < s p.1})
    (z : ℂ) :
    unitaryRootComplexStructure s (Submodule.Quotient.mk (unitaryRootVector p.val.1 p.val.2 z)) =
      Submodule.Quotient.mk (unitaryRootVector p.val.1 p.val.2 (I * z)) := by
  apply (unitaryRootCoordinates s).injective
  rw [unitaryRootCoordinates_unitaryRootComplexStructure,
    unitaryRootCoordinates_mk_unitaryRootVector, unitaryRootCoordinates_mk_unitaryRootVector,
    ← Pi.single_smul, smul_eq_mul]

/-- **The KKS form of a coadjoint orbit of `U(n)` is compatible with its root complex structure**:
`ω(J u, J v) = ω(u, v)` and `ω(u, J u) = ∑ 2 (s_j - s_k) |u_(j k)|² > 0` for `u ≠ 0`. -/
theorem compatible_unitaryRootComplexStructure :
    (unitaryTorusDualInclusion ι s).kksSymplecticForm.Compatible
      (unitaryRootComplexStructure s) := by
  rw [SymplecticForm.compatible_iff, SymplecticForm.invariant_iff]
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · simp only [Module.Dual.kksSymplecticForm_toBilinForm]
    rw [kksForm_unitaryTorusDualInclusion_eq_sum, kksForm_unitaryTorusDualInclusion_eq_sum]
    refine Fintype.sum_congr _ _ fun p => ?_
    simp only [unitaryRootCoordinates_unitaryRootComplexStructure, Pi.smul_apply, smul_eq_mul,
      map_mul, conj_I]
    -- The factors `-i` and `i` cancel: `(-i a) (i b) = a b` since `i² = -1`.
    rw [show -I * conj (unitaryRootCoordinates s x p) * (I * unitaryRootCoordinates s y p) =
        conj (unitaryRootCoordinates s x p) * unitaryRootCoordinates s y p by
      linear_combination
        -(conj (unitaryRootCoordinates s x p) * unitaryRootCoordinates s y p) * I_sq]
  · have hx' : unitaryRootCoordinates s x ≠ 0 := by
      rwa [Ne, LinearEquiv.map_eq_zero_iff]
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hx'
    simp only [Module.Dual.kksSymplecticForm_toBilinForm]
    rw [kksForm_unitaryTorusDualInclusion_eq_sum]
    -- Each summand is `2 (s_j - s_k) |u_(j k)|²`.
    have hterm (q : {p : ι × ι // s p.2 < s p.1}) :
        2 * (s q.val.1 - s q.val.2) * (conj (unitaryRootCoordinates s x q) *
          unitaryRootCoordinates s (unitaryRootComplexStructure s x) q).im =
        2 * (s q.val.1 - s q.val.2) * normSq (unitaryRootCoordinates s x q) := by
      rw [unitaryRootCoordinates_unitaryRootComplexStructure, Pi.smul_apply, smul_eq_mul,
        mul_left_comm, ← normSq_eq_conj_mul_self, I_mul_im, ofReal_re]
    simp only [hterm]
    refine Finset.sum_pos' (fun q _ => ?_) ⟨p, Finset.mem_univ _, ?_⟩
    · exact mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr q.property.le)) (normSq_nonneg _)
    · exact mul_pos (mul_pos two_pos (sub_pos.mpr p.property)) (normSq_pos.mpr hp)

/-- **The root-plane basis of the tangent model** of the coadjoint orbit through `⟨diag(s), ·⟩`:
for each pair `p = (j, k)` with `s_k < s_j`, the classes of `E_(j k) - E_(k j)` (index `(p, 0)`)
and of `i E_(j k) + i E_(k j)` (index `(p, 1)`). -/
def unitaryRootBasis : Basis ({p : ι × ι // s p.2 < s p.1} × Fin 2) ℝ (unitaryLieAlgebra ι ⧸
    (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) :=
  (Pi.basisFun ℂ {p : ι × ι // s p.2 < s p.1}).complexToReal.map (unitaryRootCoordinates s).symm

@[simp]
theorem unitaryRootBasis_apply_zero (p : {p : ι × ι // s p.2 < s p.1}) :
    unitaryRootBasis s (p, 0) = Submodule.Quotient.mk (unitaryRootVector p.val.1 p.val.2 1) := by
  rw [unitaryRootBasis, Basis.map_apply, LinearEquiv.symm_apply_eq,
    unitaryRootCoordinates_mk_unitaryRootVector, Basis.complexToReal_apply, Pi.basisFun_apply]
  simp

@[simp]
theorem unitaryRootBasis_apply_one (p : {p : ι × ι // s p.2 < s p.1}) :
    unitaryRootBasis s (p, 1) = Submodule.Quotient.mk (unitaryRootVector p.val.1 p.val.2 I) := by
  rw [unitaryRootBasis, Basis.map_apply, LinearEquiv.symm_apply_eq,
    unitaryRootCoordinates_mk_unitaryRootVector, Basis.complexToReal_apply, Pi.basisFun_apply]
  simp [← Pi.single_smul]

/-- **The symplectic orientation of a coadjoint orbit of `U(n)`.** At `⟨diag(s), ·⟩`, the
root-plane basis `([E_(j k) - E_(k j)], [i E_(j k) + i E_(k j)])` over the pairs with
`s_k < s_j`, listed in any order `e` of these pairs, is positive for the symplectic orientation of
the KKS form. -/
theorem orientation_unitaryRootBasis {n k : ℕ} (e : {p : ι × ι // s p.2 < s p.1} ≃ Fin n)
    (hk : finrank ℝ (unitaryLieAlgebra ι ⧸
      (lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTorusDualInclusion ι s)).toSubmodule) = k)
    (h : n * 2 = k) :
    (((unitaryRootBasis s).reindex (e.prodCongr (Equiv.refl (Fin 2)))).reindex
        (finProdFinEquiv.trans (finCongr h))).orientation =
      (unitaryTorusDualInclusion ι s).kksSymplecticForm.orientation hk := by
  refine ((SymplecticForm.compatible_iff _ _).mp
    (compatible_unitaryRootComplexStructure s)).2.orientation_reindex (fun i => ?_) hk h
  simp only [Basis.reindex_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Prod.map_apply, id_eq, unitaryRootBasis_apply_zero, unitaryRootBasis_apply_one]
  rw [unitaryRootComplexStructure_mk_unitaryRootVector, mul_one]

end TauCeti
