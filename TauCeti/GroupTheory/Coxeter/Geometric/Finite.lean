/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Normed.Module.QuadraticMap
import TauCeti.GroupTheory.Coxeter.Geometric.Transport
import TauCeti.Topology.Algebra.QuadraticForm.Continuity

/-!
# Finite Coxeter groups and positive definite forms

Let `cs : CoxeterSystem M W` be a Coxeter system with Coxeter matrix `M` on an arbitrary index type
`I`, and let `B = CoxeterMatrix.geometricForm M` be the canonical bilinear form on `I →₀ ℝ`, with
`B(αᵢ, αⱼ) = -cos (π / M i j)` on the simple roots `αᵢ`. This file proves the finiteness criterion
for Coxeter groups: `W` is finite exactly when `I` is finite and `B` is positive definite
(`CoxeterSystem.finite_iff_geometricForm_posDef`). It is the starting point of the classification
of finite Coxeter groups, which classifies the positive definite Coxeter matrices instead.

**A finite Coxeter group has a positive definite form.** Averaging the coordinate inner product
over `W` gives a `W`-invariant symmetric positive definite form `B'`. Invariance under the `i`-th
simple reflection, which negates `αᵢ` and fixes the hyperplane `B(αᵢ, ·) = 0`, forces
`B'(αᵢ, ·) = cᵢ B(αᵢ, ·)` with `cᵢ = B'(αᵢ, αᵢ) > 0`. By symmetry of both forms `cᵢ = cⱼ` whenever
`B(αᵢ, αⱼ) ≠ 0`, so `B` is the pullback of `B'` along the rescaling `αᵢ ↦ cᵢ^(-1/2) αᵢ`, and is
positive definite. The last two steps use only a positive definite form invariant under the simple
reflections, on an arbitrary index set (`CoxeterMatrix.geometricForm_posDef_of_invariant`); the
average supplies one for a finite group (`CoxeterSystem.geometricForm_posDef_of_finite`).

**A positive definite form gives a finite Coxeter group.** Let `C` be the chamber of the vectors
`x` with `B(αᵢ, x) > 0` for every `i`. The sign criterion
(`CoxeterSystem.geometricRepresentation_single_neg_iff`) shows that `C` and `ρ(w) C` are disjoint
for `w ≠ 1` (`CoxeterSystem.eq_one_of_forall_geometricForm_pos`), and this holds for every Coxeter
system. When `I` is finite and `B` is positive definite, `C` is a nonempty open cone, the unit set
`D = {x | B(x, x) < 1}` is bounded and `W`-invariant, and every `ρ(w)` preserves Lebesgue measure,
being of determinant `±1`. The sets `ρ(w) (C ∩ D)` are then pairwise disjoint subsets of `D` of
one common positive measure, so there are only finitely many of them
(`CoxeterSystem.finite_of_geometricForm_posDef`). Here `ρ`, `C` and `D` are read in the coordinates
`I → ℝ` of `CoxeterSystem.geometricRepresentationFun`, where Lebesgue measure lives.

Positive definiteness passes to the restriction of `M` along an injective map of index types
(`CoxeterMatrix.geometricForm_posDef_of_injective`), and a positive definite form has no infinite
entry (`CoxeterMatrix.ne_zero_of_geometricForm_posDef`), since `B` vanishes at `αᵢ + αⱼ` when
`M i j = 0` and `i ≠ j`.

## Main results

* `CoxeterMatrix.geometricForm_posDef_of_invariant`: a positive definite form invariant under the
  simple reflections makes the canonical form positive definite.
* `CoxeterMatrix.geometricForm_posDef_of_injective`: positive definiteness of the canonical form
  passes to restricted Coxeter matrices.
* `CoxeterMatrix.ne_zero_of_geometricForm_posDef`: a positive definite canonical form has no
  infinite entry.
* `CoxeterSystem.eq_one_of_forall_geometricForm_pos`: an element of `W` that maps a vector of the
  chamber into the chamber is the identity.
* `CoxeterSystem.geometricForm_posDef_of_finite`: the canonical form of a finite Coxeter group is
  positive definite.
* `CoxeterSystem.finite_of_geometricForm_posDef`: a Coxeter group with finitely many generators and
  positive definite canonical form is finite.
* `CoxeterSystem.finite_iff_geometricForm_posDef`: **the finiteness criterion**.

## References

* M. W. Davis, *The Geometry and Topology of Coxeter Groups*, Princeton University Press (2008),
  Lemma 6.6.1 and Theorem 6.12.9.
-/

public section

open Finsupp (single)

namespace CoxeterMatrix

variable {I : Type*} (M : CoxeterMatrix I)

/-- The canonical form pairs a positive vector with a vector of the chamber positively. -/
private theorem geometricForm_pos_of_pos {u x : I →₀ ℝ} (hu : 0 < u)
    (hx : ∀ i, 0 < M.geometricForm (single i 1) x) : 0 < M.geometricForm u x := by
  have hsum : M.geometricForm u x = ∑ i ∈ u.support, u i * M.geometricForm (single i 1) x := by
    conv_lhs => rw [← u.sum_single]
    simp only [Finsupp.sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, Finsupp.smul_single_one]
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hu.ne'
  rw [hsum]
  refine Finset.sum_pos' (fun j _ ↦ mul_nonneg (hu.le j) (hx j).le) ⟨i, hi, mul_pos ?_ (hx i)⟩
  exact lt_of_le_of_ne (hu.le i) (Finsupp.mem_support_iff.mp hi).symm

/-- A form invariant under the `i`-th simple reflection is proportional to the canonical form on the
`i`-th simple root: `B'(αᵢ, y) = B'(αᵢ, αᵢ) B(αᵢ, y)`. -/
private theorem apply_single_eq_mul_geometricForm (B' : LinearMap.BilinForm ℝ (I →₀ ℝ)) (i : I)
    (h : ∀ y, B' (M.geometricReflection i (single i 1)) (M.geometricReflection i y) =
      B' (single i 1) y) (y : I →₀ ℝ) :
    B' (single i 1) y = B' (single i 1) (single i 1) * M.geometricForm (single i 1) y := by
  have hy := h y
  rw [M.geometricReflection_apply_single_self, M.geometricReflection_apply i y, map_neg,
    LinearMap.neg_apply, map_sub, map_smul, smul_eq_mul] at hy
  linarith

/-- **A positive definite form preserved by the simple reflections makes the canonical form
positive definite.** Let `B'` be a positive definite bilinear form on `I →₀ ℝ` invariant under every
simple reflection; after symmetrizing, `B'(αᵢ, ·) = cᵢ B(αᵢ, ·)` with `cᵢ = B'(αᵢ, αᵢ) > 0`, and the
canonical form is the pullback of `B'` along the rescaling `αᵢ ↦ cᵢ^(-1/2) αᵢ`, hence positive
definite. The index set is arbitrary. -/
theorem geometricForm_posDef_of_invariant {B' : LinearMap.BilinForm ℝ (I →₀ ℝ)}
    (hpos : B'.toQuadraticMap.PosDef)
    (hinv : ∀ i x y, B' (M.geometricReflection i x) (M.geometricReflection i y) = B' x y) :
    M.geometricForm.toQuadraticMap.PosDef := by
  -- the symmetrization of `B'` is still positive definite and invariant
  set S := B' + B'.flip
  have hS (x y : I →₀ ℝ) : S x y = B' x y + B' y x := by simp [S]
  have hSsymm (x y : I →₀ ℝ) : S x y = S y x := by rw [hS, hS, add_comm]
  have hSpos (x : I →₀ ℝ) (hx : x ≠ 0) : 0 < S x x := by
    simpa [hS] using add_pos (hpos x hx) (hpos x hx)
  set c : I → ℝ := fun i ↦ S (single i 1) (single i 1)
  have hc (i : I) : 0 < c i := hSpos _ (Finsupp.single_ne_zero.mpr one_ne_zero)
  have hrow (i : I) (y : I →₀ ℝ) : S (single i 1) y = c i * M.geometricForm (single i 1) y :=
    M.apply_single_eq_mul_geometricForm S i
      (fun y ↦ by rw [hS, hS, hinv, hinv]) y
  let Δ := Finsupp.linearCombination ℝ fun i ↦ single i (√(c i))⁻¹
  have hΔ : LinearIndependent ℝ fun i ↦ single i (√(c i))⁻¹ :=
    Finsupp.linearIndependent_single_of_ne_zero fun i ↦
      inv_ne_zero (Real.sqrt_pos.mpr (hc i)).ne'
  have hform : M.geometricForm = S.compl₁₂ Δ Δ := by
    refine LinearMap.BilinForm.ext_basis Finsupp.basisSingleOne fun i j ↦ ?_
    simp only [Finsupp.coe_basisSingleOne, LinearMap.compl₁₂_apply, Δ,
      Finsupp.linearCombination_single, one_smul]
    rw [← Finsupp.smul_single_one i (√(c i))⁻¹, ← Finsupp.smul_single_one j (√(c j))⁻¹,
      map_smul, map_smul, LinearMap.smul_apply, hrow, smul_eq_mul, smul_eq_mul]
    by_cases hij : M.geometricForm (single i 1) (single j 1) = 0
    · simp [hij]
    -- `cᵢ = cⱼ` by symmetry of `S` and of the canonical form
    have hcij : c i = c j := mul_right_cancel₀ hij <| by
      rw [← hrow, hSsymm, hrow, M.geometricForm_comm]
    rw [← hcij]
    field_simp
    rw [Real.sq_sqrt (hc i).le, div_self (hc i).ne']
  intro x hx
  rw [LinearMap.BilinMap.toQuadraticMap_apply, hform, LinearMap.compl₁₂_apply]
  exact hSpos _ fun h ↦ hx (linearIndependent_iff.mp hΔ x h)

/-- **Positive definiteness passes to restricted Coxeter matrices**: along an injective map of index
types along which the Coxeter matrices agree, such as the inclusion of a subset of the index set or
a bijection, a positive definite canonical form pulls back to a positive definite one. -/
theorem geometricForm_posDef_of_injective {I' : Type*} {M' : CoxeterMatrix I'} {f : I → I'}
    (hf : ∀ i j, M i j = M' (f i) (f j)) (hinj : Function.Injective f)
    (hB : M'.geometricForm.toQuadraticMap.PosDef) : M.geometricForm.toQuadraticMap.PosDef :=
  fun x hx ↦ by
    have hfx : x.mapDomain f ≠ 0 :=
      (Finsupp.mapDomain_injective hinj).ne_iff' Finsupp.mapDomain_zero |>.mpr hx
    simpa [geometricForm_mapDomain_mapDomain hf] using hB _ hfx

/-- **A positive definite canonical form has no infinite entry**: at an entry `M i j = 0`, read as
`∞`, with `i ≠ j`, the canonical form vanishes at `αᵢ + αⱼ`. -/
theorem ne_zero_of_geometricForm_posDef (hB : M.geometricForm.toQuadraticMap.PosDef) (i j : I) :
    M i j ≠ 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  intro h0
  have hne : single i (1 : ℝ) + single j 1 ≠ 0 := fun h ↦ by
    simpa [Finsupp.single_apply, hij.symm] using DFunLike.congr_fun h i
  have h := hB _ hne
  rw [LinearMap.BilinMap.toQuadraticMap_apply] at h
  simp [M.geometricForm_comm (single j 1) (single i 1), h0] at h

/-- When the canonical form is positive definite and `I` is finite, the chamber is nonempty: some
vector pairs positively with every simple root. -/
private theorem exists_forall_geometricForm_pos [Finite I]
    (hB : M.geometricForm.toQuadraticMap.PosDef) :
    ∃ x : I →₀ ℝ, ∀ i, 0 < M.geometricForm (single i 1) x := by
  have := Fintype.ofFinite I
  let L : (I →₀ ℝ) →ₗ[ℝ] (I → ℝ) := LinearMap.pi fun i ↦ M.geometricForm (single i 1)
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun x hx ↦ by_contra fun hx0 ↦ (hB x hx0).ne' ?_
    have hflip : M.geometricForm.flip x = 0 :=
      Finsupp.basisSingleOne.ext fun i ↦ by simpa [L] using congrFun hx i
    simpa using LinearMap.congr_fun hflip x
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hL
    fun _ ↦ 1
  refine ⟨x, fun i ↦ ?_⟩
  have hxi := congrFun hx i
  simp only [L, LinearMap.pi_apply] at hxi
  rw [hxi]
  exact one_pos

/-- In coordinates, when the canonical form is positive definite, there is a nonempty open set of
vectors of the chamber on which the canonical quadratic form is less than one. -/
private theorem exists_isOpen_chamber [Finite I] (hB : M.geometricForm.toQuadraticMap.PosDef) :
    ∃ U : Set (I → ℝ), IsOpen U ∧ U.Nonempty ∧
      (∀ x ∈ U, ∀ i,
        0 < M.geometricForm (single i 1) ((Finsupp.linearEquivFunOnFinite ℝ ℝ I).symm x)) ∧
      ∀ x ∈ U,
        M.geometricForm.toQuadraticMap ((Finsupp.linearEquivFunOnFinite ℝ ℝ I).symm x) < 1 := by
  have := Fintype.ofFinite I
  set e := Finsupp.linearEquivFunOnFinite ℝ ℝ I
  set Q := M.geometricForm.toQuadraticMap.comp e.symm.toLinearMap
  refine ⟨{x | ∀ i, 0 < M.geometricForm (single i 1) (e.symm x)} ∩ {x | Q x < 1}, ?_, ?_,
    fun x hx ↦ hx.1, fun x hx ↦ hx.2⟩
  · refine IsOpen.inter ?_ (isOpen_lt Q.continuous continuous_const)
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const
      ((M.geometricForm (single i 1)).comp e.symm.toLinearMap).continuous_of_finiteDimensional
  -- rescale a vector of the chamber into the unit set of the form
  obtain ⟨x, hx⟩ := M.exists_forall_geometricForm_pos hB
  have hQx : 0 ≤ Q (e x) := by simpa [Q] using hB.nonneg x
  set t := (√(Q (e x) + 1))⁻¹
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  refine ⟨t • e x, fun i ↦ ?_, ?_⟩
  · simpa [map_smul] using mul_pos ht (hx i)
  · rw [Set.mem_ofPred_eq, QuadraticMap.map_smul, smul_eq_mul, ← mul_inv, Real.mul_self_sqrt
      (by linarith), inv_mul_lt_iff₀ (by linarith)]
    linarith

end CoxeterMatrix

namespace CoxeterSystem

variable {I W : Type*} [Group W] {M : CoxeterMatrix I} (cs : CoxeterSystem M W)

/-! ### The chamber -/

/-- **The chamber meets its translates only for the identity.** If a vector `x` and its image
`ρ(w) x` both lie in the chamber, the set of vectors pairing positively with every simple root, then
`w = 1`. No finiteness or definiteness hypothesis is needed. -/
theorem eq_one_of_forall_geometricForm_pos {w : W} {x : I →₀ ℝ}
    (hx : ∀ i, 0 < M.geometricForm (single i 1) x)
    (hwx : ∀ i, 0 < M.geometricForm (single i 1) (cs.geometricRepresentation w x)) : w = 1 := by
  by_contra hw
  -- a right descent `i` of `w⁻¹` makes `ρ(w⁻¹) αᵢ` negative
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one (inv_ne_one.mpr hw)
  have hneg := (cs.geometricRepresentation_single_neg_iff w⁻¹ i).mpr hi
  have h := hwx i
  rw [← cs.geometricForm_geometricRepresentation w⁻¹, ← mul_apply_eq_comp, ← map_mul,
    inv_mul_cancel, map_one, one_apply_eq_self] at h
  have hpos := M.geometricForm_pos_of_pos (neg_pos.mpr hneg) hx
  rw [map_neg, LinearMap.neg_apply] at hpos
  linarith

/-! ### Finite Coxeter groups have positive definite forms -/

include cs in
/-- **The canonical form of a finite Coxeter group is positive definite.** Averaging the coordinate
inner product over `W` gives a positive definite form invariant under the simple reflections, to
which `CoxeterMatrix.geometricForm_posDef_of_invariant` applies. -/
theorem geometricForm_posDef_of_finite [Finite W] : M.geometricForm.toQuadraticMap.PosDef := by
  have : Finite I := .of_injective _ cs.simple_injective
  have := Fintype.ofFinite I
  have := Fintype.ofFinite W
  set ρ := cs.geometricRepresentation
  set e := Finsupp.linearEquivFunOnFinite ℝ ℝ I
  let B' : LinearMap.BilinForm ℝ (I →₀ ℝ) :=
    ∑ w : W, (dotProductBilin ℝ ℝ).compl₁₂ (e.toLinearMap ∘ₗ ρ w) (e.toLinearMap ∘ₗ ρ w)
  have hB' (x y : I →₀ ℝ) : B' x y = ∑ w, e (ρ w x) ⬝ᵥ e (ρ w y) := by simp [B']
  have hnn (v : I → ℝ) : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _
  have hinv (g : W) (x y : I →₀ ℝ) : B' (ρ g x) (ρ g y) = B' x y := by
    simp only [hB', ← mul_apply_eq_comp, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ ↦ rfl
  refine M.geometricForm_posDef_of_invariant (B' := B') (fun x hx ↦ ?_) fun i x y ↦ ?_
  · -- the term `w = 1` of the average is already positive
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hB']
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun w _ ↦ hnn _) (Finset.mem_univ 1))
    rw [map_one, one_apply_eq_self]
    exact (hnn _).lt_of_ne' (mt dotProduct_self_eq_zero.mp (e.map_ne_zero_iff.mpr hx))
  · rw [← cs.geometricRepresentation_simple]
    exact hinv _ _ _

/-! ### Positive definite forms give finite Coxeter groups -/

section Finite

variable [Finite I]

/-- The transported geometric representation has determinant `±1`, its simple reflections being
involutions. -/
private theorem abs_det_geometricRepresentationFun (w : W) :
    |LinearMap.det (cs.geometricRepresentationFun w)| = 1 := by
  induction w using cs.simple_induction with
  | simple i =>
    have h : LinearMap.det (cs.geometricRepresentationFun (cs.simple i)) *
        LinearMap.det (cs.geometricRepresentationFun (cs.simple i)) = 1 := by
      rw [← map_mul, ← map_mul, cs.simple_mul_simple_self, map_one, map_one]
    rcases mul_self_eq_one_iff.mp h with h | h <;> simp [h]
  | one => simp
  | mul w w' hw hw' => rw [map_mul, map_mul, abs_mul, hw, hw', mul_one]

include cs in
/-- **A Coxeter group with finitely many generators and positive definite canonical form is
finite.** -/
theorem finite_of_geometricForm_posDef (hB : M.geometricForm.toQuadraticMap.PosDef) :
    Finite W := by
  have := Fintype.ofFinite I
  set e := Finsupp.linearEquivFunOnFinite ℝ ℝ I
  set ρ := cs.geometricRepresentationFun
  set Q := M.geometricForm.toQuadraticMap.comp e.symm.toLinearMap
  have hρ (w : W) (x : I → ℝ) : e.symm (ρ w x) = cs.geometricRepresentation w (e.symm x) := by
    rw [cs.geometricRepresentationFun_apply, LinearEquiv.conj_apply_apply,
      LinearEquiv.symm_apply_apply]
  have hQ (w : W) (x : I → ℝ) : Q (ρ w x) = Q x := by
    simp [Q, hρ, cs.geometricForm_geometricRepresentation]
  obtain ⟨U, hUo, hUne, hUC, hUQ⟩ := M.exists_isOpen_chamber hB
  -- the translates `ρ(w) U = ρ(w⁻¹)⁻¹ U` are disjoint, of measure `vol U`, inside `{Q ≤ 1}`
  set A : W → Set (I → ℝ) := fun w ↦ ρ w⁻¹ ⁻¹' U
  have hdet (w : W) : LinearMap.det (ρ w) ≠ 0 :=
    abs_ne_zero.mp ((cs.abs_det_geometricRepresentationFun w).symm ▸ one_ne_zero)
  have hvol (w : W) : MeasureTheory.volume (A w) = MeasureTheory.volume U := by
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ (hdet _), abs_inv,
      cs.abs_det_geometricRepresentationFun, inv_one, ENNReal.ofReal_one, one_mul]
  have hdisj : Pairwise (Function.onFun Disjoint A) := fun w w' hne ↦
      Set.disjoint_left.mpr fun x hx hx' ↦ by
    refine hne (inv_mul_eq_one.mp (cs.eq_one_of_forall_geometricForm_pos (hUC _ hx) ?_)).symm
    rw [hρ, ← mul_apply_eq_comp, ← map_mul, mul_assoc, mul_inv_cancel, mul_one, ← hρ]
    exact hUC _ hx'
  have hsub : ⋃ w, A w ⊆ {x | ‖Q x‖ ≤ 1} := Set.iUnion_subset fun w x hx ↦ by
    have h := hUQ _ hx
    have h0 : 0 ≤ Q x := by simpa [Q] using hB.nonneg (e.symm x)
    rw [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_nonneg h0]
    exact (hQ w⁻¹ x ▸ h).le
  have hQaniso : Q.Anisotropic := fun x hx ↦ e.symm.injective <| by
    simpa using hB.anisotropic (e.symm x) (by simpa [Q] using hx)
  have hfin := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion MeasureTheory.volume
    (hUo.measure_pos MeasureTheory.volume hUne)
    (fun w ↦ (hUo.preimage (ρ w⁻¹).continuous_of_finiteDimensional).measurableSet) hdisj
    (ne_top_of_le_ne_top
      (hQaniso.isCompact_setOf_norm_apply_le_of_continuous Q.continuous 1).measure_lt_top.ne
      (MeasureTheory.measure_mono hsub))
  exact Set.finite_univ_iff.mp (hfin.subset fun w _ ↦ (hvol w).ge)

end Finite

include cs in
/-- **The finiteness criterion for Coxeter groups.** A Coxeter group is finite exactly when its
index set is finite and its canonical bilinear form is positive definite. The index set is
arbitrary. -/
theorem finite_iff_geometricForm_posDef :
    Finite W ↔ Finite I ∧ M.geometricForm.toQuadraticMap.PosDef :=
  ⟨fun _ ↦ ⟨.of_injective _ cs.simple_injective, cs.geometricForm_posDef_of_finite⟩,
    fun ⟨_, hB⟩ ↦ cs.finite_of_geometricForm_posDef hB⟩

end CoxeterSystem
