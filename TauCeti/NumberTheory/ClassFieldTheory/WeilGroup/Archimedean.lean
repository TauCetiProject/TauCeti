/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The archimedean Weil groups

The Weil group of `ℂ` is `W_ℂ = ℂˣ`. The Weil group of `ℝ` is the nonsplit extension
`1 → ℂˣ → W_ℝ → Gal(ℂ/ℝ) → 1` realised inside the unit group of Hamilton's quaternions `ℍ` as
`W_ℝ = ℂˣ ∪ jℂˣ`, where `ℂ ⊆ ℍ` is spanned by `1` and `i`. In `W_ℝ` we have `j² = -1` and
`j z j⁻¹ = conj z` for `z ∈ ℂˣ`. It is a topological group with the subspace topology of `ℍˣ`,
and `ℂˣ` is an open subgroup whose complement is `jℂˣ`.

The norm `W_ℝ → ℝˣ` sends `z ↦ |z|²` and `j ↦ -1`; on a quaternion `q ∈ W_ℝ` it is
`q.re² + q.imI² - q.imJ² - q.imK²`. It is a surjective continuous homomorphism whose kernel is the
commutator subgroup, so it identifies the abelianization of `W_ℝ` with `ℝˣ`. The extension does
not split: every element outside `ℂˣ` squares to its norm, a negative real number, so no element
outside `ℂˣ` has order two.

## Main definitions

* `TauCeti.ClassFieldTheory.WeilGroupComplex`: the Weil group `ℂˣ` of `ℂ`.
* `TauCeti.ClassFieldTheory.realWeilSubgroup`: the subgroup `ℂˣ ∪ jℂˣ` of `ℍˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal`: the Weil group of `ℝ`, the subgroup above as a type.
* `TauCeti.ClassFieldTheory.WeilGroupReal.includeComplex`: the inclusion `W_ℂ → W_ℝ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.j`: the element `j`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.norm`: the norm `W_ℝ → ℝˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.abelianizationEquiv`: `W_ℝ^{ab} ≃* ℝˣ`.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.j_sq`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.j_mul_includeComplex_mul_inv_j`: `j² = -1` and
  `j z j⁻¹ = conj z`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.exists_includeComplex_or_j_mul`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.j_mul_includeComplex_notMem_range`: `W_ℝ` is the
  disjoint union of `ℂˣ` and `jℂˣ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.isOpenEmbedding_includeComplex`: `ℂˣ` is an open
  subgroup of `W_ℝ`, with its own topology.
* `TauCeti.ClassFieldTheory.WeilGroupReal.ker_norm`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.norm_surjective`: the norm is surjective with kernel the
  commutator subgroup.
* `TauCeti.ClassFieldTheory.WeilGroupReal.sq_eq_of_notMem_range`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.sq_ne_one_of_notMem_range`: an element outside `ℂˣ`
  squares to its norm, which is negative; so the extension does not split.

## References

* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.3.
* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open Quaternion
open scoped commutatorElement

/-- **The Weil group of `ℂ`**: the multiplicative group `ℂˣ`. -/
abbrev WeilGroupComplex : Type := ℂˣ

/-- The quaternions in `ℂˣ ∪ jℂˣ`, the subgroup of `ℍˣ` underlying the Weil group of `ℝ`. Here
`ℂ ⊆ ℍ` is spanned by `1` and `i`, and `jℂ` by `j` and `k`. -/
def realWeilSubgroup : Subgroup ℍˣ where
  carrier := {q | ((q : ℍ).imJ = 0 ∧ (q : ℍ).imK = 0) ∨ ((q : ℍ).re = 0 ∧ (q : ℍ).imI = 0)}
  mul_mem' := by
    rintro a b (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) (⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩) <;> simp [*]
  one_mem' := by simp
  inv_mem' := by
    rintro a (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) <;> simp [Quaternion.inv_def, *]

/-- A unit quaternion lies in `realWeilSubgroup` exactly when it lies in `ℂ` or in `jℂ`. -/
theorem mem_realWeilSubgroup {q : ℍˣ} :
    q ∈ realWeilSubgroup ↔
      ((q : ℍ).imJ = 0 ∧ (q : ℍ).imK = 0) ∨ ((q : ℍ).re = 0 ∧ (q : ℍ).imI = 0) :=
  Iff.rfl

/-- **The Weil group of `ℝ`**: the group `ℂˣ ∪ jℂˣ ⊆ ℍˣ`, with the subspace topology. -/
abbrev WeilGroupReal : Type := realWeilSubgroup

namespace WeilGroupReal

/-- Elements of `W_ℝ` are equal when the underlying quaternions are. -/
theorem ext_iff {v w : WeilGroupReal} : v = w ↔ ((v : ℍˣ) : ℍ) = ((w : ℍˣ) : ℍ) :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext (Units.ext h)⟩

/-- The underlying quaternion of an element of `W_ℝ` depends continuously on it. -/
theorem continuous_coe_quaternion : Continuous fun w : WeilGroupReal ↦ ((w : ℍˣ) : ℍ) :=
  Units.continuous_val.comp continuous_subtype_val

/-- **The inclusion `W_ℂ → W_ℝ`**, through `ℂ ⊆ ℍ`. -/
def includeComplex : WeilGroupComplex →* WeilGroupReal :=
  (Units.map (Quaternion.ofComplex : ℂ →* ℍ)).codRestrict realWeilSubgroup fun _ ↦
    Or.inl ⟨rfl, rfl⟩

/-- The inclusion `W_ℂ → W_ℝ` is `ℂ ⊆ ℍ` on underlying quaternions. -/
@[simp]
theorem coe_includeComplex (z : WeilGroupComplex) :
    ((includeComplex z : ℍˣ) : ℍ) = ((z : ℂ) : ℍ) :=
  (rfl)

/-- The element `j` of `W_ℝ`. -/
def j : WeilGroupReal :=
  ⟨Units.mk0 ⟨0, 0, 1, 0⟩ fun h ↦ by simpa using congrArg QuaternionAlgebra.imJ h,
    Or.inr ⟨rfl, rfl⟩⟩

/-- The underlying quaternion of `j` is the quaternion unit `j`. -/
@[simp]
theorem coe_j : ((j : ℍˣ) : ℍ) = ⟨0, 0, 1, 0⟩ :=
  (rfl)

/-- The inclusion `W_ℂ → W_ℝ` is injective. -/
theorem includeComplex_injective : Function.Injective includeComplex := fun z w h ↦ by
  rw [ext_iff, coe_includeComplex, coe_includeComplex] at h
  exact Units.ext (Quaternion.ofComplex.toRingHom.injective h)

/-- **`j² = -1`** in `W_ℝ`. -/
theorem j_sq : j ^ 2 = includeComplex (-1) := by
  rw [ext_iff, pow_two]
  ext <;> simp

/-- **Conjugation by `j` is complex conjugation**: `j z j⁻¹ = conj z`. -/
theorem j_mul_includeComplex_mul_inv_j (z : WeilGroupComplex) :
    j * includeComplex z * j⁻¹ = includeComplex (star z) := by
  rw [mul_inv_eq_iff_eq_mul, ext_iff]
  ext <;> simp

/-- **`W_ℝ = ℂˣ ∪ jℂˣ`**: every element of `W_ℝ` lies in `ℂˣ` or in `jℂˣ`. -/
theorem exists_includeComplex_or_j_mul (w : WeilGroupReal) :
    (∃ z, includeComplex z = w) ∨ ∃ z, j * includeComplex z = w := by
  obtain ⟨q, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩ := w
  · refine Or.inl ⟨Units.mk0 ⟨(q : ℍ).re, (q : ℍ).imI⟩ fun h ↦ q.ne_zero ?_, ?_⟩
    · ext <;> simp_all [Complex.ext_iff]
    · rw [ext_iff]
      ext <;> simp [h₁, h₂]
  · refine Or.inr ⟨Units.mk0 ⟨(q : ℍ).imJ, -(q : ℍ).imK⟩ fun h ↦ q.ne_zero ?_, ?_⟩
    · ext <;> simp_all [Complex.ext_iff]
    · rw [ext_iff]
      ext <;> simp [h₁, h₂]

/-- **`ℂˣ` and `jℂˣ` are disjoint**: no element of `jℂˣ` lies in `ℂˣ`. -/
theorem j_mul_includeComplex_notMem_range (z : WeilGroupComplex) :
    j * includeComplex z ∉ includeComplex.range := by
  rintro ⟨w, hw⟩
  rw [ext_iff] at hw
  have h₁ := congrArg QuaternionAlgebra.imJ hw
  have h₂ := congrArg QuaternionAlgebra.imK hw
  simp only [coe_includeComplex, imJ_coeComplex, Subgroup.coe_mul, Units.val_mul, coe_j, imJ_mul,
    mul_zero, imK_coeComplex, sub_self, re_coeComplex, one_mul, zero_add, imI_coeComplex, zero_mul,
    add_zero, imK_mul, zero_sub, zero_eq_neg] at h₁ h₂
  exact z.ne_zero (Complex.ext h₁.symm h₂)

/-! ### The norm -/

/-- The quadratic form `q.re² + q.imI² - q.imJ² - q.imK²` on `W_ℝ` is nowhere zero, since it is
`±|q|²` on `ℂ ∪ jℂ`. -/
private theorem normForm_ne_zero (w : WeilGroupReal) :
    ((w : ℍˣ) : ℍ).re ^ 2 + ((w : ℍˣ) : ℍ).imI ^ 2 - ((w : ℍˣ) : ℍ).imJ ^ 2 -
      ((w : ℍˣ) : ℍ).imK ^ 2 ≠ 0 := by
  obtain ⟨q, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)⟩ := w <;>
  · have h := Quaternion.normSq_ne_zero.2 q.ne_zero
    rw [Quaternion.normSq_def'] at h
    simp only [h₁, h₂] at h ⊢
    contrapose h
    linarith

/-- **The norm `W_ℝ → ℝˣ`**, sending `z ∈ ℂˣ` to `|z|²` and `j` to `-1`. On a quaternion `q` it is
`q.re² + q.imI² - q.imJ² - q.imK²`. -/
def norm : WeilGroupReal →* ℝˣ where
  toFun w := Units.mk0 _ (normForm_ne_zero w)
  map_one' := by ext; simp
  map_mul' := by
    rintro ⟨a, (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩)⟩ ⟨b, (⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩)⟩ <;>
    · ext
      simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, Quaternion.re_mul,
        Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, ha₁, ha₂, hb₁, hb₂]
      ring

/-- The norm of `q ∈ W_ℝ` is `q.re² + q.imI² - q.imJ² - q.imK²`. -/
theorem coe_norm (w : WeilGroupReal) :
    (norm w : ℝ) = ((w : ℍˣ) : ℍ).re ^ 2 + ((w : ℍˣ) : ℍ).imI ^ 2 - ((w : ℍˣ) : ℍ).imJ ^ 2 -
      ((w : ℍˣ) : ℍ).imK ^ 2 :=
  (rfl)

/-- The norm of `z ∈ ℂˣ` is `|z|²`. -/
@[simp]
theorem coe_norm_includeComplex (z : WeilGroupComplex) :
    (norm (includeComplex z) : ℝ) = Complex.normSq z := by
  simp [coe_norm, Complex.normSq_apply, sq]

/-- The norm of `j` is `-1`. -/
@[simp]
theorem norm_j : norm j = -1 := by
  ext
  simp [coe_norm]

/-- The norm is continuous. -/
theorem continuous_norm : Continuous norm := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  simp only [Function.comp_def, coe_norm]
  have h := continuous_coe_quaternion
  exact ((((Quaternion.continuous_re.comp h).pow 2).add
    ((Quaternion.continuous_imI.comp h).pow 2)).sub ((Quaternion.continuous_imJ.comp h).pow 2)).sub
    ((Quaternion.continuous_imK.comp h).pow 2)

/-- The norm on `jℂˣ` is negative. -/
theorem coe_norm_neg_of_notMem_range {w : WeilGroupReal} (hw : w ∉ includeComplex.range) :
    (norm w : ℝ) < 0 := by
  obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := exists_includeComplex_or_j_mul w
  · exact absurd ⟨z, rfl⟩ hw
  · rw [map_mul, norm_j, Units.val_mul, coe_norm_includeComplex, Units.val_neg, Units.val_one,
      neg_one_mul, neg_lt_zero]
    exact Complex.normSq_pos.2 z.ne_zero

/-- **The norm is surjective**: `|·|²` covers the positive reals, and `j` contributes the sign. -/
theorem norm_surjective : Function.Surjective norm := by
  intro r
  obtain ⟨z, hz⟩ : ∃ z : WeilGroupComplex, Complex.normSq z = |(r : ℝ)| := by
    refine ⟨Units.mk0 (Real.sqrt |(r : ℝ)| : ℂ) ?_, ?_⟩
    · simp
    · simp [Complex.normSq_ofReal, Real.mul_self_sqrt (abs_nonneg _)]
  rcases lt_or_gt_of_ne r.ne_zero with h | h
  · refine ⟨j * includeComplex z, Units.ext ?_⟩
    simp [hz, abs_of_neg h]
  · refine ⟨includeComplex z, Units.ext ?_⟩
    simp [hz, abs_of_pos h]

/-- **The extension does not split**: an element `w` of `W_ℝ` outside `ℂˣ` squares to its norm,
a negative real number (`coe_norm_neg_of_notMem_range`). -/
theorem sq_eq_of_notMem_range {w : WeilGroupReal} (hw : w ∉ includeComplex.range) :
    w ^ 2 = includeComplex (Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) (norm w)) := by
  obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := exists_includeComplex_or_j_mul w
  · exact absurd ⟨z, rfl⟩ hw
  · rw [ext_iff]
    ext <;> simp [coe_norm, sq] <;> ring

/-- **No element outside `ℂˣ` has order two**, so `W_ℝ → W_ℝ / ℂˣ` has no section. -/
theorem sq_ne_one_of_notMem_range {w : WeilGroupReal} (hw : w ∉ includeComplex.range) :
    w ^ 2 ≠ 1 := by
  rw [sq_eq_of_notMem_range hw, ← map_one includeComplex, includeComplex_injective.ne_iff]
  intro h
  have := congrArg (fun u : ℂˣ ↦ (u : ℂ).re) h
  simp only [Units.coe_map, MonoidHom.coe_ofClass, Complex.coe_algebraMap, Complex.ofReal_re,
    Units.val_one, Complex.one_re] at this
  linarith [coe_norm_neg_of_notMem_range hw]

/-- The commutator of `j` and `z ∈ ℂˣ` is `conj z / z`. -/
theorem commutatorElement_j_includeComplex (z : WeilGroupComplex) :
    (⁅j, includeComplex z⁆ : WeilGroupReal) = includeComplex (star z * z⁻¹) := by
  rw [commutatorElement_def, j_mul_includeComplex_mul_inv_j, map_mul, map_inv]

/-- **The norm induces the abelianization**: its kernel is the commutator subgroup of `W_ℝ`. The
kernel is the unit circle in `ℂˣ`, and every `z` with `|z| = 1` is the commutator
`⁅j, conj s⁆ = s / conj s = s²` for a square root `s` of `z`. -/
theorem ker_norm : norm.ker = commutator WeilGroupReal := by
  refine le_antisymm (fun w hw ↦ ?_) (Group.Abelianization.commutator_le_ker norm)
  rw [MonoidHom.mem_ker] at hw
  obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := exists_includeComplex_or_j_mul w
  · have hz : Complex.normSq z = 1 := by
      rw [← coe_norm_includeComplex, hw, Units.val_one]
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = z := ⟨_, Complex.cpow_nat_inv_pow (z : ℂ) two_ne_zero⟩
    have hs₀ : s ≠ 0 := by rintro rfl; exact z.ne_zero (by simp [← hs])
    have hss : (starRingEnd ℂ) s * s = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_eq_one,
        ← pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) two_ne_zero, ← map_pow, hs, hz]
    have h : includeComplex z = ⁅j, includeComplex (star (Units.mk0 s hs₀))⁆ := by
      rw [commutatorElement_j_includeComplex]
      congr 1
      ext
      simp only [Units.val_mul, Units.coe_star, Units.val_mk0, star_star, Units.val_inv_eq_inv_val,
        Complex.star_def]
      rw [← hs, eq_mul_inv_iff_mul_eq₀ (by simpa using hs₀)]
      linear_combination s * hss
    rw [h]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · exact absurd hw (by
      have := coe_norm_neg_of_notMem_range (j_mul_includeComplex_notMem_range z)
      intro h; rw [h, Units.val_one] at this; linarith)

/-- **The abelianization of `W_ℝ` is `ℝˣ`**, through the norm. -/
def abelianizationEquiv : Group.Abelianization WeilGroupReal ≃* ℝˣ :=
  (QuotientGroup.quotientMulEquivOfEq ker_norm.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective norm norm_surjective)

@[simp]
theorem abelianizationEquiv_of (w : WeilGroupReal) :
    abelianizationEquiv (Group.Abelianization.of w) = norm w :=
  (rfl)

/-! ### Topology -/

/-- An element of `W_ℝ` lies in `ℂˣ` exactly when its `j`- and `k`-coordinates vanish. -/
theorem mem_range_includeComplex_iff {w : WeilGroupReal} :
    w ∈ includeComplex.range ↔ ((w : ℍˣ) : ℍ).imJ = 0 ∧ ((w : ℍˣ) : ℍ).imK = 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    simp
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := exists_includeComplex_or_j_mul w
    · exact ⟨z, rfl⟩
    · simp only [Subgroup.coe_mul, Units.val_mul, coe_j, coe_includeComplex, imJ_mul,
        imJ_coeComplex, mul_zero, imK_coeComplex, sub_self, re_coeComplex, one_mul, zero_add,
        imI_coeComplex, zero_mul, add_zero, imK_mul, zero_sub, neg_eq_zero] at h
      exact absurd (Complex.ext h.1 h.2) z.ne_zero

/-- **`ℂˣ` is an open subgroup of `W_ℝ`**: its complement `jℂˣ` is closed. -/
theorem isOpen_range_includeComplex : IsOpen (includeComplex.range : Set WeilGroupReal) := by
  have h : (includeComplex.range : Set WeilGroupReal)ᶜ =
      {w : WeilGroupReal | ((w : ℍˣ) : ℍ).re = 0 ∧ ((w : ℍˣ) : ℍ).imI = 0} := by
    ext w
    simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_range_includeComplex_iff, Set.mem_ofPred_eq]
    refine ⟨fun hw ↦ w.2.resolve_left hw, fun hw hw' ↦ ((w : ℍˣ)).ne_zero ?_⟩
    ext <;> simp [hw.1, hw.2, hw'.1, hw'.2]
  rw [← isClosed_compl_iff, h]
  exact (isClosed_eq (Quaternion.continuous_re.comp continuous_coe_quaternion)
    continuous_const).inter
    (isClosed_eq (Quaternion.continuous_imI.comp continuous_coe_quaternion) continuous_const)

/-- **`ℂˣ` is an open subgroup of `W_ℝ`, with its own topology**: the inclusion is an open
embedding. -/
theorem isOpenEmbedding_includeComplex : Topology.IsOpenEmbedding includeComplex := by
  refine ⟨⟨?_, includeComplex_injective⟩, isOpen_range_includeComplex⟩
  have hι : Topology.IsInducing fun w : WeilGroupReal ↦ ((w : ℍˣ) : ℍ) :=
    Units.isEmbedding_val₀.isInducing.comp Topology.IsInducing.subtypeVal
  rw [← hι.of_comp_iff]
  have hc : Topology.IsEmbedding fun z : ℂ ↦ (z : ℍ) :=
    Function.LeftInverse.isEmbedding (f := fun q : ℍ ↦ (⟨q.re, q.imI⟩ : ℂ))
      (fun z ↦ by simp)
      (Complex.equivRealProdCLM.symm.continuous.comp
        (Quaternion.continuous_re.prodMk Quaternion.continuous_imI))
      Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional
  exact hc.isInducing.comp Units.isEmbedding_val₀.isInducing
end WeilGroupReal

end TauCeti.ClassFieldTheory
