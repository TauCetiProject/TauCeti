/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AlgebraicIndependent.BaseChange
public import TauCeti.RingTheory.KrullDimension.FiniteType
public import TauCeti.RingTheory.MvPolynomial.GenericShear

/-!
# Linear Noether normalization

Over an arbitrary field, Mathlib's `exists_finite_inj_algHom_of_fg` proves Noether normalization via
Nagata's nonlinear exponential shears `Xⱼ ↦ Xⱼ + X₀ ^ (r ^ j)`. Over an *infinite* field `k`, the
normalizing parameters can be chosen to be `k`-linear combinations of any prescribed finite tuple
of generators `x₀, …, xₙ₋₁` of a nontrivial `k`-algebra `A` (`TauCeti.exists_linear_normalization`),
and in fact as the first `d` entries of an invertible linear change of coordinates `M *ᵥ x`
(`TauCeti.exists_linear_normalization_units`), where `d` is the Krull dimension of `A`.

The inductive elimination step holds over any commutative ring `R`: if `p(x₀, …, xᵣ) = 0` for a
polynomial `p` whose top homogeneous part evaluates at `i.insertNth 1 a` to a unit of `R`, then
after setting `zⱼ = x_{i.succAbove j} - aⱼ • xᵢ`, the eliminated element `xᵢ` is integral over the
image of `R[Z₀, …, Zᵣ₋₁]` (`TauCeti.isIntegralElem_aeval_shear`), and integrality and
module-finiteness descend from `MvPolynomial.aeval x` to `MvPolynomial.aeval z`
(`TauCeti.isIntegral_aeval_shear`, `TauCeti.finite_aeval_shear`). Over an infinite field `k`,
`TauCeti.exists_eval_insertNth_homogeneousComponent_ne_zero` supplies such a shear direction `a` for
any nonzero polynomial relation among the `xⱼ`.

Because the normalizing parameters `yᵢ = ∑ⱼ Cᵢⱼ • xⱼ` are `k`-linear combinations of the `xⱼ`,
their matrix `C` automatically has `k`-linearly independent rows
(`AlgebraicIndependent.linearIndependent_row`), and the `yᵢ` remain inside any `k`-submodule
containing the `xⱼ` (`TauCeti.exists_linear_normalization_mem`, such as a fixed homogeneous
component `𝒜 e` of a graded algebra). Moreover, a single normalizing matrix `C` remains valid after
extending scalars along any flat algebra, and in particular along any field extension `K / k`
(`TauCeti.linear_normalization_tmul_one`, `TauCeti.linear_normalization_tensorProduct_field`).

## Main results

* `TauCeti.isIntegralElem_aeval_shear`, `TauCeti.isIntegral_aeval_shear`,
  `TauCeti.finite_aeval_shear`, `TauCeti.finite_aeval_of_adjoin_eq_top`: shear elimination and
  generator-wise module-finiteness over a commutative ring.
* `TauCeti.exists_linear_normalization_units_of_finite`,
  `TauCeti.exists_linear_normalization_units`: invertible linear change of coordinates whose first
  `d` entries normalize `A`.
* `TauCeti.exists_linear_normalization_of_finite`: linear Noether normalization for a nontrivial
  `k`-algebra finite over `k[x₀, …, xₙ₋₁]`.
* `TauCeti.exists_linear_normalization`: linear Noether normalization in prescribed algebra
  generators `x : Fin n → A` over an infinite field `k`.
* `TauCeti.exists_linear_normalization_mem`: submodule-preserving refinement (yielding homogeneous
  parameters of degree `e` when applied to `S = 𝒜 e`).
* `TauCeti.linear_normalization_tmul_one`,
  `TauCeti.linear_normalization_tensorProduct_field`: persistence of the normalizing matrix `C`
  under flat base change and field extensions.

## References

* J. S. Milne, *Algebraic Geometry*, Lemma 2.43, Theorem 2.44, Theorem 2.45, Lemma 2.46, and
  Remark 2.47.
* J. S. Milne, *A Primer of Commutative Algebra*, Theorem 8.3 and Remark 8.4.
* [Stacks Project, Tag 00OW](https://stacks.math.columbia.edu/tag/00OW)
* [Stacks Project, Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)
-/

public section

open scoped TensorProduct
open MvPolynomial Matrix

namespace TauCeti

section Shear

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {r : ℕ}

/-- **Shear integrality over a commutative ring.** If `p(x) = 0` for `x : Fin (r + 1) → A` and the
top homogeneous component of `p` evaluates at `i.insertNth 1 a` to a unit of `R`, then `x i` is
integral over `R[Z₀, …, Zᵣ₋₁]` acting via `Zⱼ ↦ x (i.succAbove j) - a j • x i`. -/
theorem isIntegralElem_aeval_shear {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
    {i : Fin (r + 1)} {a : Fin r → R} (hp : aeval x p = 0)
    (hu : IsUnit (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p))) :
    (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom.IsIntegralElem (x i) := by
  let u : Rˣ := hu.unit
  let q : Polynomial (MvPolynomial (Fin r) R) :=
    Polynomial.C (C (↑u⁻¹ : R)) * shearToPolynomial i a p
  have hmonic : q.Monic := by
    refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one p.totalDegree
      ((Polynomial.natDegree_C_mul_le _ _).trans (p.natDegree_shearToPolynomial_le i a)) ?_
    rw [Polynomial.coeff_C_mul, p.coeff_shearToPolynomial_totalDegree i a, ← hu.unit_spec,
      ← map_mul, Units.inv_mul, map_one]
  refine ⟨q, hmonic, ?_⟩
  dsimp only [q]
  rw [Polynomial.eval₂_mul, AlgHom.toRingHom_eq_coe, p.eval₂_aeval_shearToPolynomial i a _ (x i)]
  have hpt : (i.insertNth (x i) fun j ↦ x (i.succAbove j) - a j • x i + a j • x i) = x := by
    funext k
    refine Fin.succAboveCases i ?_ (fun j ↦ ?_) k <;> simp
  rw [hpt, hp, mul_zero]

/-- Under the hypotheses of `isIntegralElem_aeval_shear`, every coordinate `x k` is integral over
`R[Z₀, …, Zᵣ₋₁]` acting via `Zⱼ ↦ x (i.succAbove j) - a j • x i`. -/
theorem isIntegralElem_aeval_shear_apply {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
    {i : Fin (r + 1)} {a : Fin r → R} (hp : aeval x p = 0)
    (hu : IsUnit (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)))
    (k : Fin (r + 1)) :
    (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom.IsIntegralElem (x k) := by
  set f := (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom
  refine Fin.succAboveCases i (isIntegralElem_aeval_shear hp hu) (fun j ↦ ?_) k
  have hz : f.IsIntegralElem (x (i.succAbove j) - a j • x i) := by
    simpa [f] using RingHom.isIntegralElem_map f (x := X j)
  have ha : f.IsIntegralElem (a j • x i) := by
    have hc : f.IsIntegralElem (algebraMap R A (a j)) := by
      simpa [f] using RingHom.isIntegralElem_map f (x := C (a j))
    simpa [Algebra.smul_def] using
      RingHom.IsIntegralElem.mul f hc (isIntegralElem_aeval_shear hp hu)
  simpa using RingHom.IsIntegralElem.add f hz ha

/-- **Descent of integrality along a good shear.** If `A` is integral over `R[x₀, …, xᵣ]` and `x`
satisfies a relation `p(x) = 0` whose top homogeneous part is a unit in direction `i.insertNth 1 a`,
then `A` is integral over `R[x (i.succAbove 0) - a 0 • x i, …]`. -/
theorem isIntegral_aeval_shear {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
    {i : Fin (r + 1)} {a : Fin r → R} (hp : aeval x p = 0)
    (hu : IsUnit (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)))
    (hx : (aeval (R := R) x).toRingHom.IsIntegral) :
    (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom.IsIntegral := by
  algebraize [(aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom]
  have hrange : ∀ q : MvPolynomial (Fin (r + 1)) R,
      IsIntegral (MvPolynomial (Fin r) R) (aeval x q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      have hc : aeval x (C c) = algebraMap (MvPolynomial (Fin r) R) A (C c) := by
        simp [RingHom.algebraMap_toAlgebra]
      rw [hc]
      exact isIntegral_algebraMap
    | add q₁ q₂ h₁ h₂ =>
      rw [map_add]
      exact h₁.add h₂
    | mul_X q₁ k h₁ =>
      rw [map_mul, aeval_X]
      exact h₁.mul (isIntegralElem_aeval_shear_apply hp hu k)
  let g : MvPolynomial (Fin (r + 1)) R →+* integralClosure (MvPolynomial (Fin r) R) A :=
    (aeval (R := R) x).toRingHom.codRestrict
      (integralClosure (MvPolynomial (Fin r) R) A).toSubring hrange
  intro t
  obtain ⟨P, hP_monic, hP_eval⟩ := hx t
  have ht : IsIntegral (integralClosure (MvPolynomial (Fin r) R) A) t := by
    refine ⟨P.map g, hP_monic.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hg : (algebraMap (integralClosure (MvPolynomial (Fin r) R) A) A).comp g =
        (aeval (R := R) x).toRingHom :=
      RingHom.ext fun _ ↦ rfl
    rwa [hg]
  exact isIntegral_trans _ ht

/-- **Descent of module-finiteness along a good shear.** Under the hypotheses of
`isIntegral_aeval_shear`, if `MvPolynomial.aeval x` is module-finite, then so is the sheared map
`MvPolynomial.aeval (fun j ↦ x (i.succAbove j) - a j • x i)`. -/
theorem finite_aeval_shear {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
    {i : Fin (r + 1)} {a : Fin r → R} (hp : aeval x p = 0)
    (hu : IsUnit (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)))
    (hx : (aeval (R := R) x).Finite) :
    (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).Finite := by
  have hint := isIntegral_aeval_shear hp hu hx.to_isIntegral
  have hcomp₁ : algebraMap R A =
      (aeval (R := R) x).toRingHom.comp (algebraMap R (MvPolynomial (Fin (r + 1)) R)) :=
    RingHom.ext fun c ↦ by simp
  have hftA : (algebraMap R A).FiniteType := by
    rw [hcomp₁]
    exact hx.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType R (MvPolynomial (Fin (r + 1)) R)))
  have hcomp₂ : algebraMap R A =
      ((aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom).comp
        (algebraMap R (MvPolynomial (Fin r) R)) :=
    RingHom.ext fun c ↦ by simp
  exact hint.to_finite (RingHom.FiniteType.of_comp_finiteType (hcomp₂ ▸ hftA))

/-- If a finite family `x : ι → A` generates `A` over `R` and every `x j` is integral over
`R[Y_σ]` via `MvPolynomial.aeval y`, then `MvPolynomial.aeval y` is module-finite. -/
theorem finite_aeval_of_adjoin_eq_top {ι σ : Type*} [Finite ι] {x : ι → A}
    (hx : Algebra.adjoin R (Set.range x) = ⊤) {y : σ → A}
    (hint : ∀ j, (aeval (R := R) y).toRingHom.IsIntegralElem (x j)) :
    (aeval (R := R) y).Finite := by
  algebraize [(aeval (R := R) y).toRingHom]
  have htop : Algebra.adjoin (MvPolynomial σ R) (Set.range x) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have ha : a ∈ Algebra.adjoin R (Set.range x) := hx ▸ Algebra.mem_top
    refine Algebra.adjoin_induction (fun b hb ↦ Algebra.subset_adjoin hb) (fun c ↦ ?_)
      (fun _ _ _ _ h₁ h₂ ↦ Subalgebra.add_mem _ h₁ h₂)
      (fun _ _ _ _ h₁ h₂ ↦ Subalgebra.mul_mem _ h₁ h₂) ha
    have hc : algebraMap R A c = algebraMap (MvPolynomial σ R) A (MvPolynomial.C c) := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [hc]
    exact Subalgebra.algebraMap_mem _ _
  have hfg : (⊤ : Subalgebra (MvPolynomial σ R) A).toSubmodule.FG := by
    rw [← htop]
    exact fg_adjoin_of_finite (Set.finite_range x) <| by rintro _ ⟨j, rfl⟩; exact hint j
  rw [Algebra.top_toSubmodule] at hfg
  exact Module.finite_def.mpr hfg

end Shear

section BlockShearUnit

private def liftShearMatrix {R : Type*} [CommRing R] {r : ℕ}
    (B : Matrix (Fin r) (Fin r) R) (v : Fin r → R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of <| Fin.lastCases (Pi.single (Fin.last r) 1) fun j ↦ Fin.lastCases (v j) (B j)

private theorem liftShearMatrix_one {R : Type*} [CommRing R] {r : ℕ} :
    liftShearMatrix (1 : Matrix (Fin r) (Fin r) R) 0 = 1 := by
  ext k m
  refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> refine Fin.lastCases ?_ (fun l ↦ ?_) m
  · simp [liftShearMatrix]
  · simp [liftShearMatrix, Fin.castSucc_ne_last, (Fin.castSucc_ne_last l).symm]
  · simp [liftShearMatrix, Fin.castSucc_ne_last]
  · simp [liftShearMatrix, Matrix.one_apply]

private theorem liftShearMatrix_mul {R : Type*} [CommRing R] {r : ℕ}
    (B₁ B₂ : Matrix (Fin r) (Fin r) R) (v₁ v₂ : Fin r → R) :
    liftShearMatrix B₁ v₁ * liftShearMatrix B₂ v₂ =
      liftShearMatrix (B₁ * B₂) (B₁ *ᵥ v₂ + v₁) := by
  ext k m
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun j ↦ ?_) k <;> refine Fin.lastCases ?_ (fun l ↦ ?_) m
  · simp [liftShearMatrix, Fin.castSucc_ne_last]
  · simp [liftShearMatrix, Fin.castSucc_ne_last]
  · simp [liftShearMatrix, Matrix.mulVec, dotProduct]
  · simp [liftShearMatrix, Fin.castSucc_ne_last, Matrix.mul_apply]

private def liftShearUnit {R : Type*} [CommRing R] {r : ℕ}
    (u : (Matrix (Fin r) (Fin r) R)ˣ) (a : Fin r → R) :
    (Matrix (Fin (r + 1)) (Fin (r + 1)) R)ˣ where
  val := liftShearMatrix u.val (-(u.val *ᵥ a))
  inv := liftShearMatrix u⁻¹.val a
  val_inv := by
    rw [liftShearMatrix_mul, Units.mul_inv, add_neg_cancel, liftShearMatrix_one]
  inv_val := by
    rw [liftShearMatrix_mul, Units.inv_mul, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec, neg_add_cancel, liftShearMatrix_one]

private theorem sum_liftShearUnit_smul {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    {r d : ℕ} (u : (Matrix (Fin r) (Fin r) R)ˣ) (a : Fin r → R) (x : Fin (r + 1) → A)
    (hd : d ≤ r) (i : Fin d) :
    (∑ m : Fin (r + 1),
        (liftShearUnit u a).val (Fin.castLE (Nat.le_succ_of_le hd) i) m • x m) =
      ∑ l : Fin r, u.val (Fin.castLE hd i) l • (x l.castSucc - a l • x (Fin.last r)) := by
  have hcast : Fin.castLE (Nat.le_succ_of_le hd) i = (Fin.castLE hd i).castSucc :=
    Fin.ext rfl
  rw [hcast, Fin.sum_univ_castSucc]
  simp only [liftShearUnit, liftShearMatrix, Matrix.of_apply, Fin.lastCases_castSucc,
    Fin.lastCases_last, Pi.neg_apply, Matrix.mulVec, dotProduct, neg_smul, Finset.sum_smul,
    mul_smul, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, smul_sub]

end BlockShearUnit

section InfiniteField

variable {k A : Type*} [Field k] [Infinite k] [CommRing A] [Algebra k A]

/-- **Invertible-coordinate linear Noether normalization (finite presentation form).** Let `k` be an
infinite field and `A` be a nontrivial `k`-algebra that is module-finite over `k[x₀, …, xₙ₋₁]`.
Then there exist `d ≤ n` and an invertible matrix `M : (Matrix (Fin n) (Fin n) k)ˣ` such that the
first `d` entries of `M *ᵥ x` are algebraically independent over `k`, make `A` a finite module over
`k[X₀, …, X_{d-1}]`, and witness `ringKrullDim A = d`. -/
theorem exists_linear_normalization_units_of_finite [Nontrivial A] {n : ℕ} (x : Fin n → A)
    (hx : (aeval (R := k) x).Finite) :
    ∃ (d : ℕ) (hd : d ≤ n) (M : (Matrix (Fin n) (Fin n) k)ˣ),
      let y : Fin d → A := fun i ↦ ∑ j, (M : Matrix (Fin n) (Fin n) k) (Fin.castLE hd i) j • x j
      AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim A = d := by
  induction n with
  | zero =>
    have hind : AlgebraicIndependent k x :=
      algebraicIndependent_empty_type_iff.mpr (algebraMap k A).injective
    refine ⟨0, le_rfl, 1, ?_⟩
    have hy : (fun i : Fin 0 ↦ ∑ j : Fin 0,
        ((1 : (Matrix (Fin 0) (Fin 0) k)ˣ) : Matrix (Fin 0) (Fin 0) k)
          (Fin.castLE le_rfl i) j • x j) = x := funext finZeroElim
    simp only [hy, Nat.cast_zero]
    exact ⟨hind, hx, by
      simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial
        (aeval (R := k) x).toRingHom (algebraicIndependent_iff_injective_aeval.mp hind)
        hx.to_isIntegral⟩
  | succ r ih =>
    by_cases hind : AlgebraicIndependent k x
    · refine ⟨r + 1, le_rfl, 1, ?_⟩
      have hy : (fun i : Fin (r + 1) ↦ ∑ j : Fin (r + 1),
          ((1 : (Matrix (Fin (r + 1)) (Fin (r + 1)) k)ˣ) : Matrix (Fin (r + 1)) (Fin (r + 1)) k)
            (Fin.castLE le_rfl i) j • x j) = x := by
        funext i
        simp [Matrix.one_apply]
      rw [hy]
      exact ⟨hind, hx, by
        simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial
          (aeval (R := k) x).toRingHom (algebraicIndependent_iff_injective_aeval.mp hind)
          hx.to_isIntegral⟩
    · rw [_root_.algebraicIndependent_iff] at hind
      push Not at hind
      obtain ⟨p, hp0, hp⟩ := hind
      obtain ⟨a, ha⟩ := exists_eval_insertNth_homogeneousComponent_ne_zero hp (Fin.last r)
      let z : Fin r → A := fun j ↦ x j.castSucc - a j • x (Fin.last r)
      have hz : (aeval (R := k) z).Finite := by
        simpa only [z, Fin.succAbove_last] using finite_aeval_shear hp0 ha.isUnit hx
      obtain ⟨d, hd, M', hy_ind, hy_fin, hdim⟩ := ih z hz
      refine ⟨d, Nat.le_succ_of_le hd, liftShearUnit M' a, ?_⟩
      have hy_eq : (fun i : Fin d ↦ ∑ m : Fin (r + 1),
          (liftShearUnit M' a : Matrix (Fin (r + 1)) (Fin (r + 1)) k)
            (Fin.castLE (Nat.le_succ_of_le hd) i) m • x m) =
          fun i : Fin d ↦ ∑ l : Fin r, (M' : Matrix (Fin r) (Fin r) k) (Fin.castLE hd i) l • z l :=
        funext fun i ↦ sum_liftShearUnit_smul M' a x hd i
      rw [hy_eq]
      exact ⟨hy_ind, hy_fin, hdim⟩

/-- **Invertible-coordinate linear Noether normalization.** Over an infinite field `k`, for any
nontrivial `k`-algebra `A` generated by `x : Fin n → A`, there exist `d ≤ n` and an invertible
matrix `M : (Matrix (Fin n) (Fin n) k)ˣ` whose first `d` transformed coordinates normalize `A`,
while the full transformed tuple `M *ᵥ x` generates `A`. -/
theorem exists_linear_normalization_units [Nontrivial A] {n : ℕ} (x : Fin n → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    ∃ (d : ℕ) (hd : d ≤ n) (M : (Matrix (Fin n) (Fin n) k)ˣ),
      let z : Fin n → A := fun i ↦ ∑ j, (M : Matrix (Fin n) (Fin n) k) i j • x j
      let y : Fin d → A := fun i ↦ z (Fin.castLE hd i)
      Algebra.adjoin k (Set.range z) = ⊤ ∧
        AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim A = d := by
  have hsurj : Function.Surjective (aeval (R := k) x) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hx]
  obtain ⟨d, hd, M, hy_ind, hy_fin, hdim⟩ :=
    exists_linear_normalization_units_of_finite x (RingHom.Finite.of_surjective _ hsurj)
  refine ⟨d, hd, M, ?_, hy_ind, hy_fin, hdim⟩
  rw [eq_top_iff, ← hx]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨l, rfl⟩
  have hinv : x l = ∑ i : Fin n, M⁻¹.val l i • (∑ j : Fin n, M.val i j • x j) := by
    calc
      x l = ∑ j : Fin n, (M⁻¹.val * M.val) l j • x j := by
        simp [Matrix.one_apply]
      _ = ∑ j : Fin n, (∑ i : Fin n, M⁻¹.val l i * M.val i j) • x j := by
        simp [Matrix.mul_apply]
      _ = ∑ i : Fin n, M⁻¹.val l i • (∑ j : Fin n, M.val i j • x j) := by
        simp_rw [Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
  rw [hinv]
  refine Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.smul_mem _ ?_ (M⁻¹.val l i)
  exact Algebra.subset_adjoin ⟨i, rfl⟩

/-- **Linear Noether normalization (finite presentation form).** Let `k` be an infinite field and
`A` be a nontrivial `k`-algebra that is module-finite over `k[x₀, …, xₙ₋₁]`. Then there exist
`d ≤ n` and `C : Matrix (Fin d) (Fin n) k` such that `yᵢ = ∑ⱼ Cᵢⱼ • xⱼ` is algebraically
independent over `k`, makes `A` module-finite over `k[X₀, …, X_{d-1}]`, and satisfies
`ringKrullDim A = d`. -/
theorem exists_linear_normalization_of_finite [Nontrivial A] {n : ℕ} (x : Fin n → A)
    (hx : (aeval (R := k) x).Finite) :
    ∃ (d : ℕ) (_ : d ≤ n) (C : Matrix (Fin d) (Fin n) k),
      let y : Fin d → A := fun i ↦ ∑ j, C i j • x j
      AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim A = d := by
  obtain ⟨d, hd, M, hy_ind, hy_fin, hdim⟩ := exists_linear_normalization_units_of_finite x hx
  exact ⟨d, hd, (M : Matrix (Fin n) (Fin n) k).submatrix (Fin.castLE hd) id, hy_ind, hy_fin, hdim⟩

/-- **Linear Noether normalization in prescribed generators.** Let `k` be an infinite field and `A`
be a nontrivial `k`-algebra generated by `x : Fin n → A`. Then there exist `d ≤ n` and a matrix
`C : Matrix (Fin d) (Fin n) k` such that the `k`-linear combinations `yᵢ = ∑ⱼ Cᵢⱼ • xⱼ` are
algebraically independent over `k`, make `A` a finite `k[X₀, …, X_{d-1}]`-module via `Xᵢ ↦ yᵢ`,
and satisfy `ringKrullDim A = d`. -/
theorem exists_linear_normalization [Nontrivial A] {n : ℕ} (x : Fin n → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    ∃ (d : ℕ) (_ : d ≤ n) (C : Matrix (Fin d) (Fin n) k),
      let y : Fin d → A := fun i ↦ ∑ j, C i j • x j
      AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim A = d := by
  have hsurj : Function.Surjective (aeval (R := k) x) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hx]
  exact exists_linear_normalization_of_finite x (RingHom.Finite.of_surjective _ hsurj)

/-- **Submodule-preserving linear Noether normalization.** If the generators `xⱼ` of `A` all belong
to a `k`-submodule `S : Submodule k A` (for instance, a fixed homogeneous component `S = 𝒜 e` of a
graded `k`-algebra), then the normalizing linear combinations `yᵢ = ∑ⱼ Cᵢⱼ • xⱼ` also belong to
`S`. -/
theorem exists_linear_normalization_mem [Nontrivial A] {n : ℕ} (x : Fin n → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤) (S : Submodule k A) (hxS : ∀ j, x j ∈ S) :
    ∃ (d : ℕ) (_ : d ≤ n) (C : Matrix (Fin d) (Fin n) k),
      let y : Fin d → A := fun i ↦ ∑ j, C i j • x j
      (∀ i, y i ∈ S) ∧ AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧
        ringKrullDim A = d := by
  obtain ⟨d, hd, C, hy_ind, hy_fin, hdim⟩ := exists_linear_normalization x hx
  exact ⟨d, hd, C, fun i ↦ S.sum_mem fun j _ ↦ S.smul_mem (C i j) (hxS j), hy_ind, hy_fin, hdim⟩

end InfiniteField

section BaseChange

/-- **Flat base change of a linear Noether normalization.** If `C` normalizes `A` over `R` via the
linear combinations `yᵢ = ∑ⱼ Cᵢⱼ • xⱼ`, then for every flat `R`-algebra `S` the same matrix `C`
normalizes `S ⊗[R] A` via `y_{S,i} = ∑ⱼ Cᵢⱼ • (1 ⊗ₜ xⱼ)`. -/
theorem linear_normalization_tmul_one {ι κ R A : Type*} [Fintype κ] (S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [CommRing A] [Algebra R A]
    {C : Matrix ι κ R} {x : κ → A}
    (hy_ind : AlgebraicIndependent R fun i ↦ ∑ j, C i j • x j)
    (hy_fin : (aeval (R := R) fun i ↦ ∑ j, C i j • x j).Finite) :
    AlgebraicIndependent S (fun i ↦ ∑ j, C i j • ((1 : S) ⊗ₜ[R] x j)) ∧
      (aeval (R := S) fun i ↦ ∑ j, C i j • ((1 : S) ⊗ₜ[R] x j)).Finite := by
  have heq : (fun i ↦ ∑ j, C i j • ((1 : S) ⊗ₜ[R] x j)) =
      fun i ↦ (1 : S) ⊗ₜ[R] (∑ j, C i j • x j) := by
    funext i
    simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  rw [heq]
  exact ⟨hy_ind.tmul_one S, finite_aeval_tmul_one S hy_fin⟩

/-- **Field-extension stability of linear Noether normalization.** Over any field `k` and any field
extension `K / k`, a matrix `C : Matrix (Fin d) (Fin n) k` whose linear combinations normalize a
`k`-algebra `A` continues to normalize `K ⊗[k] A` with the same dimension `d`. -/
theorem linear_normalization_tensorProduct_field {k A : Type*} (K : Type*) [Field k] [Field K]
    [Algebra k K] [CommRing A] [Algebra k A] {d n : ℕ}
    {C : Matrix (Fin d) (Fin n) k} {x : Fin n → A}
    (hy_ind : AlgebraicIndependent k fun i ↦ ∑ j, C i j • x j)
    (hy_fin : (aeval (R := k) fun i ↦ ∑ j, C i j • x j).Finite) :
    let yK : Fin d → K ⊗[k] A := fun i ↦ ∑ j, C i j • ((1 : K) ⊗ₜ[k] x j)
    AlgebraicIndependent K yK ∧ (aeval (R := K) yK).Finite ∧ ringKrullDim (K ⊗[k] A) = d := by
  obtain ⟨hindK, hfinK⟩ := linear_normalization_tmul_one K hy_ind hy_fin
  refine ⟨hindK, hfinK, ?_⟩
  simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial
    (aeval (R := K) fun i ↦ ∑ j, C i j • ((1 : K) ⊗ₜ[k] x j)).toRingHom
    (algebraicIndependent_iff_injective_aeval.mp hindK) hfinK.to_isIntegral

end BaseChange

end TauCeti
