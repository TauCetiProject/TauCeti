/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.LinearAlgebra.Matrix.BlockSucc
import TauCeti.LinearAlgebra.Matrix.LastRowTransvection
import TauCeti.RingTheory.AlgebraicIndependent.BaseChange
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic
import TauCeti.RingTheory.MvPolynomial.GenericShear
import TauCeti.RingTheory.MvPolynomial.LineRestriction
import TauCeti.RingTheory.TensorProduct.MvPolynomial

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
after setting `zⱼ = x_{i.succAbove j} - aⱼ • xᵢ`, the eliminated element `xᵢ` and hence all `xₖ`
are integral over the image of `R[Z₀, …, Zᵣ₋₁]` (`TauCeti.isIntegralElem_aeval_shear_self`,
`TauCeti.isIntegralElem_aeval_shear`), and integrality and module-finiteness descend from
`MvPolynomial.aeval x` to `MvPolynomial.aeval z` (`TauCeti.isIntegral_aeval_shear`,
`TauCeti.finite_aeval_shear`). Over an infinite field `k`,
`TauCeti.exists_eval_insertNth_homogeneousComponent_ne_zero` supplies such a shear direction `a` for
any nonzero polynomial relation among the `xⱼ`.

Because the normalizing parameters `yᵢ = ∑ⱼ Cᵢⱼ • xⱼ` are `k`-linear combinations of the `xⱼ`,
their matrix `C` automatically has `k`-linearly independent rows
(`AlgebraicIndependent.linearIndependent_row`), and the `yᵢ` remain inside any `k`-submodule
containing the `xⱼ` (such as a fixed homogeneous component of a graded algebra). Moreover, a single
normalizing matrix `C` remains valid after extending scalars along any field extension `K / k`
(`TauCeti.linear_normalization_tensorProduct_field`).

## Main results

* `TauCeti.isIntegralElem_aeval_shear_self`, `TauCeti.isIntegralElem_aeval_shear`,
  `TauCeti.isIntegral_aeval_shear`, `TauCeti.finite_aeval_shear`: shear elimination and descent of
  integrality and module-finiteness over a commutative ring.
* `TauCeti.exists_linear_normalization_units_of_finite`,
  `TauCeti.exists_linear_normalization_units`: invertible linear change of coordinates whose first
  `d` entries normalize `A`.
* `TauCeti.exists_linear_normalization_of_finite`: linear Noether normalization for a nontrivial
  `k`-algebra finite over `k[x₀, …, xₙ₋₁]`.
* `TauCeti.exists_linear_normalization`: linear Noether normalization in prescribed algebra
  generators `x : Fin n → A` over an infinite field `k`.
* `TauCeti.linear_normalization_tensorProduct_field`: persistence of the normalizing matrix `C`
  under field extensions.

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
theorem isIntegralElem_aeval_shear_self {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
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

/-- Under the hypotheses of `isIntegralElem_aeval_shear_self`, every coordinate `x k` is integral
over `R[Z₀, …, Zᵣ₋₁]` acting via `Zⱼ ↦ x (i.succAbove j) - a j • x i`. -/
theorem isIntegralElem_aeval_shear {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
    {i : Fin (r + 1)} {a : Fin r → R} (hp : aeval x p = 0)
    (hu : IsUnit (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)))
    (k : Fin (r + 1)) :
    (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom.IsIntegralElem (x k) := by
  set f := (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom
  refine Fin.succAboveCases i (isIntegralElem_aeval_shear_self hp hu) (fun j ↦ ?_) k
  have hz : f.IsIntegralElem (x (i.succAbove j) - a j • x i) := by
    simpa [f] using RingHom.isIntegralElem_map f (x := X j)
  have ha : f.IsIntegralElem (a j • x i) := by
    have hc : f.IsIntegralElem (algebraMap R A (a j)) := by
      simpa [f] using RingHom.isIntegralElem_map f (x := C (a j))
    simpa [Algebra.smul_def] using
      RingHom.IsIntegralElem.mul f hc (isIntegralElem_aeval_shear_self hp hu)
  simpa using RingHom.IsIntegralElem.add f hz ha

/-- **Descent of integrality along a good shear.** If `A` is integral over `R[x₀, …, xᵣ]` and `x`
satisfies a relation `p(x) = 0` whose top homogeneous part is a unit in direction `i.insertNth 1 a`,
then `A` is integral over `R[x (i.succAbove 0) - a 0 • x i, …]`. -/
theorem isIntegral_aeval_shear {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
    {i : Fin (r + 1)} {a : Fin r → R} (hp : aeval x p = 0)
    (hu : IsUnit (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)))
    (hx : (aeval (R := R) x).toRingHom.IsIntegral) :
    (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom.IsIntegral := by
  algebraize [(aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).toRingHom,
    (aeval (R := R) x).toRingHom]
  have hrange : ∀ q : MvPolynomial (Fin (r + 1)) R,
      IsIntegral (MvPolynomial (Fin r) R) (algebraMap (MvPolynomial (Fin (r + 1)) R) A q) := by
    intro q
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
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
      exact h₁.mul (isIntegralElem_aeval_shear hp hu k)
  exact fun t ↦ isIntegral_trans_common hrange (hx t)

/-- **Descent of module-finiteness along a good shear.** Under the hypotheses of
`isIntegral_aeval_shear`, if `MvPolynomial.aeval x` is module-finite, then so is the sheared map
`MvPolynomial.aeval (fun j ↦ x (i.succAbove j) - a j • x i)`. -/
theorem finite_aeval_shear {x : Fin (r + 1) → A} {p : MvPolynomial (Fin (r + 1)) R}
    {i : Fin (r + 1)} {a : Fin r → R} (hp : aeval x p = 0)
    (hu : IsUnit (eval (i.insertNth 1 a) (homogeneousComponent p.totalDegree p)))
    (hx : (aeval (R := R) x).Finite) :
    (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).Finite := by
  have hint := isIntegral_aeval_shear hp hu hx.to_isIntegral
  have hftA : (algebraMap R A).FiniteType := by
    rw [← (aeval (R := R) x).comp_algebraMap]
    exact hx.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType R (MvPolynomial (Fin (r + 1)) R)))
  rw [← (aeval (R := R) fun j ↦ x (i.succAbove j) - a j • x i).comp_algebraMap] at hftA
  exact hint.to_finite (RingHom.FiniteType.of_comp_finiteType hftA)

end Shear

section InfiniteField

variable {k A : Type*} [Field k] [Infinite k] [CommRing A] [Algebra k A]

/-- **Invertible-coordinate linear Noether normalization (module-finite form).** Let `k` be an
infinite field and `A` be a nontrivial `k`-algebra that is module-finite over `k[x₀, …, xₙ₋₁]`.
Then there exist `d ≤ n` and an invertible matrix `M : (Matrix (Fin n) (Fin n) k)ˣ` such that the
first `d` entries of `M *ᵥ x` are algebraically independent over `k`, make `A` a finite module over
`k[X₀, …, X_{d-1}]`, and witness `ringKrullDim A = d`. -/
theorem exists_linear_normalization_units_of_finite [Nontrivial A] {n : ℕ} (x : Fin n → A)
    (hx : (aeval (R := k) x).Finite) :
    ∃ (d : ℕ) (hd : d ≤ n) (M : (Matrix (Fin n) (Fin n) k)ˣ),
      let y : Fin d → A := fun i ↦ ∑ j, (M : Matrix (Fin n) (Fin n) k) (Fin.castLE hd i) j • x j
      AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim A = d := by
  have hid {m : ℕ} (w : Fin m → A) (hw : (aeval (R := k) w).Finite)
      (hind : AlgebraicIndependent k w) :
      ∃ (d : ℕ) (hd : d ≤ m) (M : (Matrix (Fin m) (Fin m) k)ˣ),
        let y : Fin d → A := fun i ↦ ∑ j, (M : Matrix (Fin m) (Fin m) k) (Fin.castLE hd i) j • w j
        AlgebraicIndependent k y ∧ (aeval (R := k) y).Finite ∧ ringKrullDim A = d := by
    refine ⟨m, le_rfl, 1, ?_⟩
    have hy : (fun i : Fin m ↦ ∑ j : Fin m,
        ((1 : (Matrix (Fin m) (Fin m) k)ˣ) : Matrix (Fin m) (Fin m) k)
          (Fin.castLE le_rfl i) j • w j) = w := by
      funext i; simp [Matrix.one_apply]
    rw [hy]
    exact ⟨hind, hw, by
      simpa using ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial
        (aeval (R := k) w).toRingHom (algebraicIndependent_iff_injective_aeval.mp hind)
        hw.to_isIntegral⟩
  induction n with
  | zero =>
    exact hid x hx (algebraicIndependent_empty_type_iff.mpr (algebraMap k A).injective)
  | succ r ih =>
    by_cases hind : AlgebraicIndependent k x
    · exact hid x hx hind
    · rw [_root_.algebraicIndependent_iff] at hind
      push Not at hind
      obtain ⟨p, hp0, hp⟩ := hind
      obtain ⟨a, ha⟩ := exists_eval_insertNth_homogeneousComponent_ne_zero hp (Fin.last r)
      let z : Fin r → A := fun j ↦ x j.castSucc - a j • x (Fin.last r)
      have hz : (aeval (R := k) z).Finite := by
        simpa only [z, Fin.succAbove_last] using finite_aeval_shear hp0 ha.isUnit hx
      obtain ⟨d, hd, M', hy_ind, hy_fin, hdim⟩ := ih z hz
      let S : (Matrix (Fin (r + 1)) (Fin (r + 1)) k)ˣ :=
        { val := (lastRowTransvection r (-a))ᵀ
          inv := (lastRowTransvection r a)ᵀ
          val_inv := by
            rw [← Matrix.transpose_mul, lastRowTransvection_mul_lastRowTransvection,
              add_neg_cancel, lastRowTransvection_zero, Matrix.transpose_one]
          inv_val := by
            rw [← Matrix.transpose_mul, lastRowTransvection_mul_lastRowTransvection,
              neg_add_cancel, lastRowTransvection_zero, Matrix.transpose_one] }
      let U : (Matrix (Fin (r + 1)) (Fin (r + 1)) k)ˣ :=
        Units.map (Matrix.blockSuccMonoidHom k r) M' * S
      refine ⟨d, Nat.le_succ_of_le hd, U, ?_⟩
      have hy_eq : (fun i : Fin d ↦ ∑ m : Fin (r + 1),
          (U : Matrix (Fin (r + 1)) (Fin (r + 1)) k)
            (Fin.castLE (Nat.le_succ_of_le hd) i) m • x m) =
          fun i : Fin d ↦
            ∑ l : Fin r, (M' : Matrix (Fin r) (Fin r) k) (Fin.castLE hd i) l • z l := by
        funext i
        let i₀ : Fin r := Fin.castLE hd i
        have hcast : Fin.castLE (Nat.le_succ_of_le hd) i = i₀.castSucc := by ext; simp [i₀]
        have hU_val : (U : Matrix (Fin (r + 1)) (Fin (r + 1)) k) =
            Matrix.blockSucc M'.val * (lastRowTransvection r (-a))ᵀ := by
          simp [U, S]
        have hU_cast (j : Fin r) : (U : Matrix (Fin (r + 1)) (Fin (r + 1)) k)
            i₀.castSucc j.castSucc = M'.val i₀ j := by
          rw [hU_val, Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp [lastRowTransvection_apply, Matrix.one_apply, Fin.castSucc_inj]
        have hU_last : (U : Matrix (Fin (r + 1)) (Fin (r + 1)) k)
            i₀.castSucc (Fin.last r) = -∑ l : Fin r, M'.val i₀ l * a l := by
          rw [hU_val, Matrix.mul_apply, Fin.sum_univ_castSucc]
          simp [lastRowTransvection_apply]
        rw [hcast, Fin.sum_univ_castSucc]
        simp only [hU_cast, hU_last, i₀, z, sub_eq_add_neg, smul_add, smul_neg,
          Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_smul, Finset.sum_smul, mul_smul]
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

/-- **Linear Noether normalization (module-finite form).** Let `k` be an infinite field and
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

end InfiniteField

section BaseChange

/-- **Field-extension stability of linear Noether normalization.** Over any field `k` and any field
extension `K / k`, a matrix `C : Matrix ι κ k` whose linear combinations normalize a `k`-algebra
`A` continues to normalize `K ⊗[k] A` with Krull dimension `Nat.card ι`. -/
theorem linear_normalization_tensorProduct_field {ι κ k A : Type*} [Finite ι] [Fintype κ]
    (K : Type*) [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
    {C : Matrix ι κ k} {x : κ → A}
    (hy_ind : AlgebraicIndependent k fun i ↦ ∑ j, C i j • x j)
    (hy_fin : (aeval (R := k) fun i ↦ ∑ j, C i j • x j).Finite) :
    let yK : ι → K ⊗[k] A := fun i ↦ ∑ j, C i j • ((1 : K) ⊗ₜ[k] x j)
    AlgebraicIndependent K yK ∧ (aeval (R := K) yK).Finite ∧
      ringKrullDim (K ⊗[k] A) = Nat.card ι := by
  have heq : (fun i ↦ ∑ j, C i j • ((1 : K) ⊗ₜ[k] x j)) =
      fun i ↦ (1 : K) ⊗ₜ[k] (∑ j, C i j • x j) := by
    funext i
    simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  have hindK : AlgebraicIndependent K (fun i ↦ ∑ j, C i j • ((1 : K) ⊗ₜ[k] x j)) := by
    rw [heq]
    exact hy_ind.one_tmul K
  have hfinK : (aeval (R := K) fun i ↦ ∑ j, C i j • ((1 : K) ⊗ₜ[k] x j)).Finite := by
    rw [heq]
    exact finite_aeval_one_tmul K hy_fin
  exact ⟨hindK, hfinK, ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial
    (aeval (R := K) fun i ↦ ∑ j, C i j • ((1 : K) ⊗ₜ[k] x j)).toRingHom
    (algebraicIndependent_iff_injective_aeval.mp hindK) hfinK.to_isIntegral⟩

end BaseChange

end TauCeti
