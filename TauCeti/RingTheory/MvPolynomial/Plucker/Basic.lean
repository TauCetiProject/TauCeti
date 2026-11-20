/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Tuple
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Data.Fin.Tuple.Sort
public import TauCeti.Data.Finsupp.MonomialOrder.DegRevLex
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import TauCeti.Order.Hom.Lex
public import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Preorder.Finite
import TauCeti.GroupTheory.Perm.Subgroup

/-!
# Maximal minors, Plücker evaluation and quadratic straightening relations

For the generic `n × d` matrix, `TauCeti.maximalMinor R I` (`I : Fin d ↪o Fin n`) is monic under
row-major `MonomialOrder.lex` with leading exponent `TauCeti.maximalMinorDiagonalExponent I`.
Evaluation (`TauCeti.pluckerEval R n d`) on variables indexed by `(Lex (Fin d ↪o Fin n))ᵒᵈ`
(`TauCeti.pluckerVar`) has image `TauCeti.maximalMinorSubalgebra R n d` and kernel
`TauCeti.pluckerIdeal R n d` (`TauCeti.isPrime_pluckerIdeal`,
`TauCeti.quotientPluckerIdealAlgEquiv`).

For `hIJ : ¬ I ≤ J`, shuffling `{a | k ≤ a}` of `I` against `{a | a ≤ k}` of `J` at
`k = TauCeti.pluckerPivot hIJ` yields a homogeneous quadric
`TauCeti.pluckerQuadric R hIJ ∈ TauCeti.pluckerIdeal R n d` (`TauCeti.pluckerQuadrics R n d`),
monic for `TauCeti.MonomialOrder.degRevLex` when `toLex I < toLex J` with leading term
`X (pluckerVar I) * X (pluckerVar J)`, recovering the three-term relation for `d = 2`
(`TauCeti.pluckerQuadric_fin_two`, `TauCeti.pluckerQuadric_ofStrictMono_pair`).

## References

* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, GTM 227, Springer, 2005, Ch. 14.
* B. Sturmfels, *Algorithms in Invariant Theory*, 2nd ed., Springer, 2008, §3.1, Theorem 3.1.7.
* W. V. D. Hodge and D. Pedoe, *Methods of Algebraic Geometry*, Vol. II, CUP, 1952.
-/

public section

namespace TauCeti

open Equiv Finset MvPolynomial
open scoped _root_.MonomialOrder

variable {n d : ℕ}

/-! ### Generic maximal minors and diagonal leading terms -/

section MaximalMinor

variable (R : Type*) [CommRing R]

/-- The **maximal minor** of the generic `n × d` matrix on an increasing `d`-tuple of rows
`I : Fin d ↪o Fin n` and all `d` columns. -/
noncomputable def maximalMinor (I : Fin d ↪o Fin n) : MvPolynomial (Fin n × Fin d) R :=
  Matrix.mvPolynomialMinor R I id

theorem maximalMinor_def (I : Fin d ↪o Fin n) :
    maximalMinor R I = Matrix.mvPolynomialMinor R I id := (rfl)

@[simp]
theorem maximalMinor_zero (I : Fin 0 ↪o Fin n) : maximalMinor R I = 1 :=
  Matrix.mvPolynomialMinor_zero I id

/-- Maximal minors are the Plücker coordinates of the columns of the generic `n × d` matrix. -/
theorem maximalMinor_eq_plucker_col (I : Fin d ↪o Fin n) :
    maximalMinor R I =
      plucker (Matrix.mvPolynomialX (Fin n) (Fin d) R).col (Set.powersetCard.ofFinEmbEquiv I) := by
  rw [maximalMinor_def, Matrix.mvPolynomialMinor_eq_det_submatrix, ← Matrix.det_transpose,
    plucker_apply, Equiv.symm_apply_apply]; rfl

@[simp]
theorem aeval_maximalMinor {S : Type*} [CommRing S] [Algebra R S] (A : Matrix (Fin n) (Fin d) S)
    (I : Fin d ↪o Fin n) :
    aeval (fun ij : Fin n × Fin d ↦ A ij.1 ij.2) (maximalMinor R I) = (A.submatrix I id).det :=
  Matrix.aeval_mvPolynomialMinor R A I id

@[simp]
theorem map_maximalMinor {S : Type*} [CommRing S] (f : R →+* S) (I : Fin d ↪o Fin n) :
    map f (maximalMinor R I) = maximalMinor S I := Matrix.map_mvPolynomialMinor f I id

theorem isHomogeneous_maximalMinor (I : Fin d ↪o Fin n) : (maximalMinor R I).IsHomogeneous d := by
  simpa [maximalMinor_def] using Matrix.isHomogeneous_mvPolynomialMinor R I (id : Fin d → Fin d)

/-- The `d × d` determinantal ideal of the generic `n × d` matrix is spanned by maximal minors. -/
theorem determinantalIdeal_eq_span_range_maximalMinor (n d : ℕ) :
    determinantalIdeal R (Fin n) (Fin d) (Fin d) = Ideal.span (Set.range (maximalMinor R)) := by
  rw [determinantalIdeal_eq_span_orderEmbedding]
  congr 1; ext f
  simp only [Set.mem_ofPred_eq, Set.mem_range, maximalMinor_def]
  exact ⟨fun ⟨r, c, h⟩ ↦ ⟨r, c.strictMono.eq_id ▸ h⟩, fun ⟨r, h⟩ ↦ ⟨r, .refl _, h⟩⟩

/-- The exponent of the main diagonal `∏_(c < d) z_(I c, c)` of `maximalMinor R I` in the
row-major lexicographically ordered variables `Fin n ×ₗ Fin d`. -/
noncomputable def maximalMinorDiagonalExponent (I : Fin d ↪o Fin n) : Fin n ×ₗ Fin d →₀ ℕ :=
  ∑ c : Fin d, Finsupp.single (toLex (I c, c)) 1

theorem maximalMinorDiagonalExponent_def (I : Fin d ↪o Fin n) :
    maximalMinorDiagonalExponent I = ∑ c : Fin d, Finsupp.single (toLex (I c, c)) 1 := (rfl)

@[simp]
theorem maximalMinorDiagonalExponent_apply (I : Fin d ↪o Fin n) (r : Fin n) (c : Fin d) :
    maximalMinorDiagonalExponent I (toLex (r, c)) = if I c = r then 1 else 0 := by
  rw [maximalMinorDiagonalExponent_def, Finsupp.finsetSum_apply,
    Fintype.sum_eq_single c fun c' hc' ↦ Finsupp.single_eq_of_ne fun h ↦
      hc' (congrArg (fun x ↦ (ofLex x).2) h).symm]
  by_cases h : I c = r <;> simp [h, toLex.injective.eq_iff]

@[simp]
theorem degree_maximalMinorDiagonalExponent (I : Fin d ↪o Fin n) :
    (maximalMinorDiagonalExponent I).degree = d := by simp [maximalMinorDiagonalExponent_def]

theorem maximalMinorDiagonalExponent_injective :
    Function.Injective (maximalMinorDiagonalExponent (n := n) (d := d)) := fun I J h ↦
  DFunLike.ext I J fun c ↦ by_contra fun hne ↦ by
    simpa [Ne.symm hne] using congrArg (fun e ↦ e (toLex (I c, c))) h

@[simp]
theorem monic_rename_toLex_maximalMinor (I : Fin d ↪o Fin n) :
    _root_.MonomialOrder.lex.Monic (rename toLex (maximalMinor R I)) :=
  Matrix.monic_rename_toLex_mvPolynomialMinor R I.strictMono strictMono_id

@[simp]
theorem degree_rename_toLex_maximalMinor [Nontrivial R] (I : Fin d ↪o Fin n) :
    _root_.MonomialOrder.lex.degree (rename toLex (maximalMinor R I)) =
      maximalMinorDiagonalExponent I :=
  Matrix.degree_rename_toLex_mvPolynomialMinor R I.strictMono strictMono_id

variable {R}

@[simp]
theorem leadingTerm_rename_toLex_maximalMinor (I : Fin d ↪o Fin n) :
    _root_.MonomialOrder.lex.leadingTerm (rename toLex (maximalMinor R I)) =
      monomial (maximalMinorDiagonalExponent I) 1 := by
  nontriviality R
  rw [_root_.MonomialOrder.leadingTerm, degree_rename_toLex_maximalMinor,
    (monic_rename_toLex_maximalMinor R I).leadingCoeff_eq_one]

@[simp]
theorem maximalMinor_ne_zero [Nontrivial R] (I : Fin d ↪o Fin n) : maximalMinor R I ≠ 0 :=
  fun h ↦ (monic_rename_toLex_maximalMinor R I).ne_zero (by rw [h, map_zero])

theorem maximalMinor_injective (R : Type*) [CommRing R] [Nontrivial R] :
    Function.Injective (maximalMinor (n := n) (d := d) R) := fun I J h ↦
  maximalMinorDiagonalExponent_injective <| by
    simpa only [degree_rename_toLex_maximalMinor] using
      congrArg (fun p ↦ _root_.MonomialOrder.lex.degree (rename toLex p)) h

end MaximalMinor

/-! ### Plücker variables, evaluation, ideal and subalgebra -/

/-- Equivalence identifying `I : Fin d ↪o Fin n` with its Plücker variable index in
`(Lex (Fin d ↪o Fin n))ᵒᵈ`, making `TauCeti.MonomialOrder.degRevLex` isotonic with `Lex`:
`X (pluckerVar I) < X (pluckerVar J) ↔ toLex I < toLex J`. -/
def pluckerVar : (Fin d ↪o Fin n) ≃ (Lex (Fin d ↪o Fin n))ᵒᵈ := toLex.trans OrderDual.toDual

theorem pluckerVar_def :
    (pluckerVar : (Fin d ↪o Fin n) ≃ (Lex (Fin d ↪o Fin n))ᵒᵈ) = toLex.trans OrderDual.toDual :=
  (rfl)

@[simp]
theorem pluckerVar_lt_iff {I J : Fin d ↪o Fin n} :
    pluckerVar I < pluckerVar J ↔ toLex J < toLex I := Iff.rfl

@[simp]
theorem pluckerVar_le_iff {I J : Fin d ↪o Fin n} :
    pluckerVar I ≤ pluckerVar J ↔ toLex J ≤ toLex I := Iff.rfl

theorem degRevLex_single_pluckerVar_lt_iff {I J : Fin d ↪o Fin n} :
    Finsupp.single (pluckerVar I) 1 ≺[MonomialOrder.degRevLex] Finsupp.single (pluckerVar J) 1 ↔
      toLex I < toLex J := MonomialOrder.degRevLex_single_lt_iff

theorem degRevLex_single_pluckerVar_le_iff {I J : Fin d ↪o Fin n} :
    Finsupp.single (pluckerVar I) 1 ≼[MonomialOrder.degRevLex] Finsupp.single (pluckerVar J) 1 ↔
      toLex I ≤ toLex J := MonomialOrder.degRevLex_single_le_iff

section PluckerIdeal

variable (R : Type*) [CommRing R]

/-- Evaluation of Plücker variables at the generic maximal minors `maximalMinor R I`. -/
noncomputable def pluckerEval (n d : ℕ) :
    MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R →ₐ[R] MvPolynomial (Fin n × Fin d) R :=
  aeval fun v ↦ maximalMinor R (pluckerVar.symm v)

theorem pluckerEval_def (n d : ℕ) :
    pluckerEval R n d = aeval fun v ↦ maximalMinor R (pluckerVar.symm v) := (rfl)

@[simp]
theorem pluckerEval_X (v : (Lex (Fin d ↪o Fin n))ᵒᵈ) :
    pluckerEval R n d (X v) = maximalMinor R (pluckerVar.symm v) := by simp [pluckerEval_def]

theorem pluckerEval_X_pluckerVar (I : Fin d ↪o Fin n) :
    pluckerEval R n d (X (pluckerVar I)) = maximalMinor R I := by simp [pluckerEval_def]

/-- The subalgebra of `MvPolynomial (Fin n × Fin d) R` generated by the maximal minors of the
generic `n × d` matrix, i.e. the Grassmannian coordinate subalgebra over `R`. -/
noncomputable def maximalMinorSubalgebra (n d : ℕ) :
    Subalgebra R (MvPolynomial (Fin n × Fin d) R) :=
  Algebra.adjoin R (Set.range (maximalMinor R))

theorem maximalMinorSubalgebra_def (n d : ℕ) :
    maximalMinorSubalgebra R n d = Algebra.adjoin R (Set.range (maximalMinor R)) := (rfl)

theorem maximalMinor_mem_maximalMinorSubalgebra (I : Fin d ↪o Fin n) :
    maximalMinor R I ∈ maximalMinorSubalgebra R n d := Algebra.subset_adjoin ⟨I, rfl⟩

@[simp]
theorem maximalMinorSubalgebra_zero (n : ℕ) : maximalMinorSubalgebra R n 0 = ⊥ := by
  rw [maximalMinorSubalgebra_def, eq_bot_iff]
  exact Algebra.adjoin_le (by rintro _ ⟨I, rfl⟩; exact Algebra.mem_bot.2 ⟨1, by simp⟩)

@[simp]
theorem range_pluckerEval (n d : ℕ) : (pluckerEval R n d).range = maximalMinorSubalgebra R n d := by
  simp [pluckerEval_def, aeval_range, maximalMinorSubalgebra_def, Set.range_comp']

/-- The **Plücker ideal**: the ideal of polynomial relations among the `d × d` maximal minors of
the generic `n × d` matrix over `R`. -/
noncomputable def pluckerIdeal (n d : ℕ) : Ideal (MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :=
  RingHom.ker (pluckerEval R n d)

theorem pluckerIdeal_def (n d : ℕ) : pluckerIdeal R n d = RingHom.ker (pluckerEval R n d) := (rfl)

@[simp]
theorem mem_pluckerIdeal_iff {f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R} :
    f ∈ pluckerIdeal R n d ↔ pluckerEval R n d f = 0 := Iff.rfl

/-- For `d = 0`, the unique Plücker variable evaluates to `1`, so `pluckerIdeal R n 0` is generated
by `X (pluckerVar .ofIsEmpty) - 1`. -/
theorem pluckerIdeal_zero (n : ℕ) :
    pluckerIdeal R n 0 = Ideal.span {X (pluckerVar OrderEmbedding.ofIsEmpty) - 1} := by
  let v₀ : (Lex (Fin 0 ↪o Fin n))ᵒᵈ := pluckerVar OrderEmbedding.ofIsEmpty
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.2 (by rintro _ rfl; simp))
  have hmod (g : MvPolynomial (Lex (Fin 0 ↪o Fin n))ᵒᵈ R) :
      g - C (constantCoeff (pluckerEval R n 0 g)) ∈ Ideal.span {X v₀ - 1} := by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add _ _ hp hq => simpa only [map_add, sub_add_sub_comm] using add_mem hp hq
    | mul_X p v hp =>
      have hv : v = v₀ := pluckerVar.symm.injective (DFunLike.ext _ _ fun i ↦ Fin.elim0 i)
      rw [hv, map_mul, pluckerEval_X_pluckerVar, maximalMinor_zero, mul_one]
      have hsub : p * X v₀ - C (constantCoeff (pluckerEval R n 0 p)) =
          p * (X v₀ - 1) + (p - C (constantCoeff (pluckerEval R n 0 p))) := by ring
      exact hsub ▸ add_mem (Ideal.mul_mem_left _ p (Ideal.subset_span rfl)) hp
  simpa [(mem_pluckerIdeal_iff R).1 hf] using hmod f

/-- Over an integral domain, the Plücker ideal is prime. -/
instance isPrime_pluckerIdeal [IsDomain R] (n d : ℕ) : (pluckerIdeal R n d).IsPrime :=
  RingHom.ker_isPrime _

/-- First isomorphism theorem for `pluckerEval`: the quotient by `pluckerIdeal R n d` is isomorphic
as an `R`-algebra to `maximalMinorSubalgebra R n d`. -/
noncomputable def quotientPluckerIdealAlgEquiv (n d : ℕ) :
    (MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R ⧸ pluckerIdeal R n d) ≃ₐ[R]
      maximalMinorSubalgebra R n d :=
  (Ideal.quotientKerEquivRange (pluckerEval R n d)).trans
    (Subalgebra.equivOfEq _ _ (range_pluckerEval R n d))

@[simp]
theorem coe_quotientPluckerIdealAlgEquiv_mk (n d : ℕ)
    (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :
    (quotientPluckerIdealAlgEquiv R n d (Ideal.Quotient.mk (pluckerIdeal R n d) f) :
      MvPolynomial (Fin n × Fin d) R) = pluckerEval R n d f :=
  congrArg Subtype.val
    (Ideal.quotientKerAlgEquivOfSurjective_mk (pluckerEval R n d).rangeRestrict_surjective f)

theorem map_pluckerEval {S : Type*} [CommRing S] (φ : R →+* S)
    (f : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :
    map φ (pluckerEval R n d f) = pluckerEval S n d (map φ f) := by
  simp [pluckerEval_def, aeval_def, algebraMap_eq, map_eval₂, Function.comp_def]

end PluckerIdeal

/-! ### Lifting arbitrary row tuples and quadratic straightening relations -/

section Straightening

/-- Lift a row tuple `r : Fin d → Fin n` to a signed Plücker variable if injective, else `0`. -/
noncomputable def pluckerLift (R : Type*) [CommRing R] (r : Fin d → Fin n) :
    MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R :=
  if hr : Function.Injective r then
    Perm.sign (Tuple.sort r) • X (pluckerVar
      (OrderEmbedding.ofStrictMono (r ∘ Tuple.sort r) (Tuple.strictMono_comp_sort hr)))
  else 0

theorem pluckerLift_of_injective (R : Type*) [CommRing R] {r : Fin d → Fin n}
    (hr : Function.Injective r) :
    pluckerLift R r = Perm.sign (Tuple.sort r) •
      X (pluckerVar (OrderEmbedding.ofStrictMono (r ∘ Tuple.sort r)
        (Tuple.strictMono_comp_sort hr))) := dite_eq_left hr

@[simp]
theorem pluckerLift_of_not_injective (R : Type*) [CommRing R] {r : Fin d → Fin n}
    (hr : ¬ Function.Injective r) : pluckerLift R r = 0 := dite_eq_right hr

@[simp]
theorem pluckerEval_pluckerLift (R : Type*) [CommRing R] (r : Fin d → Fin n) :
    pluckerEval R n d (pluckerLift R r) = Matrix.mvPolynomialMinor R r id := by
  rw [pluckerLift]; split_ifs with hr
  · let I := OrderEmbedding.ofStrictMono (r ∘ Tuple.sort r) (Tuple.strictMono_comp_sort hr)
    have hrI : ⇑I ∘ ⇑(Tuple.sort r)⁻¹ = r := funext fun _ ↦ by
      simp [I, OrderEmbedding.coe_ofStrictMono]
    rw [Units.smul_def, map_zsmul, pluckerEval_X_pluckerVar, maximalMinor_def, ← Units.smul_def,
      ← Perm.sign_inv (Tuple.sort r), ← Matrix.mvPolynomialMinor_comp_perm_left R I id _, hrI]
  · rw [map_zero, Matrix.mvPolynomialMinor_eq_zero_of_not_injective_left hr]

@[simp]
theorem pluckerLift_coe (R : Type*) [CommRing R] (I : Fin d ↪o Fin n) :
    pluckerLift R ⇑I = X (pluckerVar I) := by
  simp only [pluckerLift, I.injective, dite_true, Tuple.sort_eq_refl_iff_monotone.2 I.monotone,
    Perm.sign_refl, one_smul]
  exact congrArg (fun J ↦ X (pluckerVar J)) (DFunLike.ext _ _ fun _ ↦ rfl)

/-- Permuting `r` by `σ : Perm (Fin d)` scales `pluckerLift R r` by `Perm.sign σ`. -/
theorem pluckerLift_comp_perm (R : Type*) [CommRing R] (r : Fin d → Fin n) (σ : Perm (Fin d)) :
    pluckerLift R (r ∘ σ) = Perm.sign σ • pluckerLift R r := by
  by_cases hr : Function.Injective r
  · have hrσ : Function.Injective (r ∘ σ) := hr.comp σ.injective
    have hcomp : (r ∘ σ) ∘ Tuple.sort (r ∘ σ) = r ∘ Tuple.sort r :=
      Tuple.comp_sort_eq_comp_sort_of_range_eq hrσ (σ.surjective.range_comp r)
    have hsort : Tuple.sort (r ∘ σ) = σ⁻¹ * Tuple.sort r :=
      eq_inv_mul_iff_mul_eq.2 (Equiv.ext fun x ↦ hr (congrFun hcomp x))
    rw [pluckerLift_of_injective R hrσ, pluckerLift_of_injective R hr, smul_smul]
    exact congrArg₂ (· • ·) (by rw [hsort, map_mul, Perm.sign_inv])
      (congrArg (fun J ↦ X (pluckerVar J)) (DFunLike.ext _ _ (congrFun hcomp)))
  · have hrσ : ¬ Function.Injective (r ∘ σ) :=
      fun h ↦ hr (by simpa [Function.comp_def] using h.comp σ.symm.injective)
    rw [pluckerLift_of_not_injective R hrσ, pluckerLift_of_not_injective R hr, smul_zero]

/-- Swapping the two entries of a `Fin 2` row tuple negates `pluckerLift`. -/
theorem pluckerLift_pair_swap (R : Type*) [CommRing R] (x y : Fin n) :
    pluckerLift R ![x, y] = -pluckerLift R ![y, x] := by
  have h : ![x, y] = ![y, x] ∘ Equiv.swap (0 : Fin 2) 1 := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  rw [h, pluckerLift_comp_perm, Perm.sign_swap (by decide)]; simp [Units.smul_def]

theorem isHomogeneous_pluckerLift (R : Type*) [CommRing R] (r : Fin d → Fin n) :
    (pluckerLift R r).IsHomogeneous 1 := by
  rw [pluckerLift]; split_ifs
  · rw [Units.smul_def, ← mem_homogeneousSubmodule]
    exact zsmul_mem ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R _)) _
  · exact isHomogeneous_zero _ R 1

@[simp]
theorem map_pluckerLift {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (r : Fin d → Fin n) : map φ (pluckerLift R r) = pluckerLift S r := by
  rw [pluckerLift, pluckerLift]; split_ifs <;> simp [Units.smul_def]

/-- The first column index `k` at which `J k < I k`, witnessing `¬ I ≤ J`. -/
noncomputable def pluckerPivot {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) : Fin d :=
  (univ.filter fun c ↦ J c < I c).min' <| by
    rw [OrderEmbedding.le_def] at hIJ; push Not at hIJ
    obtain ⟨c, hc⟩ := hIJ; exact ⟨c, mem_filter.2 ⟨mem_univ c, hc⟩⟩

theorem apply_pluckerPivot_lt {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    J (pluckerPivot hIJ) < I (pluckerPivot hIJ) :=
  (mem_filter.1 (min'_mem (univ.filter fun c ↦ J c < I c) _)).2

theorem pluckerPivot_le_of_lt {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) {c : Fin d}
    (hc : J c < I c) : pluckerPivot hIJ ≤ c :=
  min'_le (univ.filter fun c ↦ J c < I c) c (mem_filter.2 ⟨mem_univ c, hc⟩)

theorem le_of_lt_pluckerPivot {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) {c : Fin d}
    (hc : c < pluckerPivot hIJ) : I c ≤ J c :=
  le_of_not_gt fun hJc ↦ hc.not_ge (pluckerPivot_le_of_lt hIJ hJc)

/-- Tail `{a : Fin d // ¬ a < pluckerPivot hIJ}` of `I`-columns participating in the shuffle. -/
abbrev PluckerLeftTail {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) : Type :=
  {a : Fin d // ¬ a < pluckerPivot hIJ}

/-- Initial segment `{a : Fin d // ¬ pluckerPivot hIJ < a}` of `J`-columns in the shuffle. -/
abbrev PluckerRightInit {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) : Type :=
  {a : Fin d // ¬ pluckerPivot hIJ < a}

/-- Left row tuple for a shuffle `σ`: keeps `I c` for `c < pluckerPivot hIJ` and inserts
`σ ∘ Sum.inl`-shuffled entries for `pluckerPivot hIJ ≤ c`. -/
noncomputable def pluckerLeftRow {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) : Fin d → Fin n :=
  Sum.elim (fun a : {a : Fin d // a < pluckerPivot hIJ} ↦ I a.val)
    (Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val) ∘
      σ ∘ Sum.inl) ∘ (Equiv.sumCompl (· < pluckerPivot hIJ)).symm

theorem pluckerLeftRow_def {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) :
    pluckerLeftRow hIJ σ =
      Sum.elim (fun a : {a : Fin d // a < pluckerPivot hIJ} ↦ I a.val)
        (Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val) ∘
          σ ∘ Sum.inl) ∘ (Equiv.sumCompl (· < pluckerPivot hIJ)).symm := (rfl)

theorem pluckerLeftRow_apply_of_lt {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) {c : Fin d}
    (hc : c < pluckerPivot hIJ) : pluckerLeftRow hIJ σ c = I c := by
  simp [pluckerLeftRow_def, Equiv.sumCompl, hc]

theorem pluckerLeftRow_apply_of_le {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) {c : Fin d}
    (hc : pluckerPivot hIJ ≤ c) :
    pluckerLeftRow hIJ σ c =
      Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val)
        (σ (Sum.inl ⟨c, not_lt.2 hc⟩)) := by simp [pluckerLeftRow_def, Equiv.sumCompl, not_lt.2 hc]

/-- Right row tuple for a shuffle `σ`: keeps `J c` for `pluckerPivot hIJ < c` and inserts
`σ ∘ Sum.inr`-shuffled entries for `c ≤ pluckerPivot hIJ`. -/
noncomputable def pluckerRightRow {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) : Fin d → Fin n :=
  Sum.elim (fun a : {a : Fin d // pluckerPivot hIJ < a} ↦ J a.val)
    (Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val) ∘
      σ ∘ Sum.inr) ∘ (Equiv.sumCompl (pluckerPivot hIJ < ·)).symm

theorem pluckerRightRow_def {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) :
    pluckerRightRow hIJ σ =
      Sum.elim (fun a : {a : Fin d // pluckerPivot hIJ < a} ↦ J a.val)
        (Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val) ∘
          σ ∘ Sum.inr) ∘ (Equiv.sumCompl (pluckerPivot hIJ < ·)).symm := (rfl)

theorem pluckerRightRow_apply_of_lt {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) {c : Fin d}
    (hc : pluckerPivot hIJ < c) : pluckerRightRow hIJ σ c = J c := by
  simp [pluckerRightRow_def, Equiv.sumCompl, hc]

theorem pluckerRightRow_apply_of_le {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) {c : Fin d}
    (hc : c ≤ pluckerPivot hIJ) :
    pluckerRightRow hIJ σ c =
      Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val)
        (σ (Sum.inr ⟨c, not_lt.2 hc⟩)) := by simp [pluckerRightRow_def, Equiv.sumCompl, not_lt.2 hc]

/-- Finset of `(PluckerLeftTail hIJ, PluckerRightInit hIJ)`-shuffles, i.e. permutations `σ`
strictly increasing on both summands in `Lex`. -/
noncomputable def pluckerShuffleFinset {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    Finset (Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) :=
  univ.filter fun σ ↦ StrictMono (toLex ∘ ⇑σ ∘ Sum.inl) ∧ StrictMono (toLex ∘ ⇑σ ∘ Sum.inr)

theorem pluckerShuffleFinset_def {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    pluckerShuffleFinset hIJ =
      univ.filter fun σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ) ↦
        StrictMono (toLex ∘ ⇑σ ∘ Sum.inl) ∧ StrictMono (toLex ∘ ⇑σ ∘ Sum.inr) := (rfl)

@[simp]
theorem mem_pluckerShuffleFinset {I J : Fin d ↪o Fin n} {hIJ : ¬ I ≤ J}
    {σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)} :
    σ ∈ pluckerShuffleFinset hIJ ↔
      StrictMono (toLex ∘ ⇑σ ∘ Sum.inl) ∧ StrictMono (toLex ∘ ⇑σ ∘ Sum.inr) := by
  simp [pluckerShuffleFinset_def]

theorem one_mem_pluckerShuffleFinset {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    (1 : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)) ∈ pluckerShuffleFinset hIJ :=
  mem_pluckerShuffleFinset.2
    ⟨fun _ _ h ↦ Sum.Lex.inl_lt_inl_iff.2 h, fun _ _ h ↦ Sum.Lex.inr_lt_inr_iff.2 h⟩

@[simp]
theorem pluckerLeftRow_one {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    pluckerLeftRow hIJ 1 = ⇑I := funext fun c ↦ by
  by_cases hc : c < pluckerPivot hIJ
  · exact pluckerLeftRow_apply_of_lt hIJ 1 hc
  · simp [pluckerLeftRow_apply_of_le hIJ 1 (not_lt.1 hc)]

@[simp]
theorem pluckerRightRow_one {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    pluckerRightRow hIJ 1 = ⇑J := funext fun c ↦ by
  by_cases hc : pluckerPivot hIJ < c
  · exact pluckerRightRow_apply_of_lt hIJ 1 hc
  · simp [pluckerRightRow_apply_of_le hIJ 1 (not_lt.1 hc)]

private theorem isComplement_pluckerShuffleFinset {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    Subgroup.IsComplement
      (pluckerShuffleFinset hIJ : Set (Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)))
      (Perm.sumCongrHom (PluckerLeftTail hIJ) (PluckerRightInit hIJ)).range := by
  convert Perm.isComplement_setOf_strictMono_toLex_sumCongrHom_range
    (PluckerLeftTail hIJ) (PluckerRightInit hIJ) using 1
  ext σ; simp

private theorem card_lt_pluckerShuffle {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    Fintype.card (Fin d) <
      Fintype.card (PluckerLeftTail hIJ) + Fintype.card (PluckerRightInit hIJ) := by
  simp [PluckerLeftTail, PluckerRightInit, Fintype.card_subtype, not_lt, Finset.filter_le_eq_Ici,
    Finset.filter_ge_eq_Iic]; omega

/-- The **quadratic Plücker straightening relation** attached to `hIJ : ¬ I ≤ J`, obtained by
shuffling `{a | k ≤ a}` of `I` with `{a | a ≤ k}` of `J` at `k = pluckerPivot hIJ`. -/
noncomputable def pluckerQuadric (R : Type*) [CommRing R] {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R :=
  ∑ σ ∈ pluckerShuffleFinset hIJ,
    Perm.sign σ • (pluckerLift R (pluckerLeftRow hIJ σ) * pluckerLift R (pluckerRightRow hIJ σ))

theorem pluckerQuadric_def (R : Type*) [CommRing R] {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    pluckerQuadric R hIJ = ∑ σ ∈ pluckerShuffleFinset hIJ, Perm.sign σ •
      (pluckerLift R (pluckerLeftRow hIJ σ) * pluckerLift R (pluckerRightRow hIJ σ)) := (rfl)

/-- Every quadratic Plücker straightening relation belongs to `pluckerIdeal R n d`. -/
theorem pluckerQuadric_mem_pluckerIdeal (R : Type*) [CommRing R] {I J : Fin d ↪o Fin n}
    (hIJ : ¬ I ≤ J) : pluckerQuadric R hIJ ∈ pluckerIdeal R n d := by
  rw [mem_pluckerIdeal_iff, pluckerQuadric_def, map_sum]
  simp_rw [Units.smul_def, map_zsmul, map_mul, pluckerEval_pluckerLift, ← Units.smul_def]
  exact Matrix.sum_sign_smul_mvPolynomialMinor_mul_mvPolynomialMinor_eq_zero R id
    (Equiv.sumCompl (· < pluckerPivot hIJ)).symm (Equiv.sumCompl (pluckerPivot hIJ < ·)).symm
    (fun a ↦ I a.val) (fun a ↦ J a.val)
    (Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val))
    (card_lt_pluckerShuffle hIJ) (isComplement_pluckerShuffleFinset hIJ)

/-- Every quadratic Plücker straightening relation is homogeneous of degree `2`. -/
theorem isHomogeneous_pluckerQuadric (R : Type*) [CommRing R] {I J : Fin d ↪o Fin n}
    (hIJ : ¬ I ≤ J) : (pluckerQuadric R hIJ).IsHomogeneous 2 := by
  rw [pluckerQuadric_def, ← mem_homogeneousSubmodule]
  refine sum_mem fun σ _ ↦ ?_; rw [Units.smul_def]
  exact zsmul_mem ((mem_homogeneousSubmodule _ _).2
    ((isHomogeneous_pluckerLift R _).mul (isHomogeneous_pluckerLift R _))) _

@[simp]
theorem map_pluckerQuadric {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J) :
    map φ (pluckerQuadric R hIJ) = pluckerQuadric S hIJ := by
  simp [pluckerQuadric_def, Units.smul_def]

private theorem toLex_sorted_pluckerLeftRow_lt {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    {σ : Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ)}
    (hσ : σ ∈ pluckerShuffleFinset hIJ) (hne : σ ≠ 1)
    (hr₁ : Function.Injective (pluckerLeftRow hIJ σ)) :
    toLex (OrderEmbedding.ofStrictMono (pluckerLeftRow hIJ σ ∘ Tuple.sort (pluckerLeftRow hIJ σ))
      (Tuple.strictMono_comp_sort hr₁)) < toLex I := by
  set r₁ := pluckerLeftRow hIJ σ with hr₁_def
  set I' := OrderEmbedding.ofStrictMono (r₁ ∘ Tuple.sort r₁) (Tuple.strictMono_comp_sort hr₁)
  obtain ⟨hσl, hσr⟩ := mem_pluckerShuffleFinset.1 hσ
  obtain ⟨a₀, b₀, hab⟩ := Perm.exists_apply_inl_eq_inr_of_strictMono_toLex_of_ne_one hσl hσr hne
  have hr₁_a₀ : r₁ a₀.val < I (pluckerPivot hIJ) :=
    (by rw [hr₁_def, pluckerLeftRow_apply_of_le hIJ σ (not_lt.1 a₀.property), hab, Sum.elim_inr] :
      r₁ a₀.val = J b₀.val).trans_lt
      ((J.monotone (le_of_not_gt b₀.property)).trans_lt (apply_pluckerPivot_lt hIJ))
  refine OrderEmbedding.toLex_lt_of_forall_lt_mem_range (k := pluckerPivot hIJ)
    (fun c hc ↦ by
      simp only [I', OrderEmbedding.coe_ofStrictMono, Tuple.range_comp_sort,
        ← pluckerLeftRow_apply_of_lt hIJ σ hc]
      exact ⟨c, rfl⟩) ?_
  rw [← Tuple.lt_card_lt_iff_apply_lt_of_monotone I'.monotone]
  have hcard_eq : #{x : Fin d | I' x < I (pluckerPivot hIJ)} =
      #{x : Fin d | r₁ x < I (pluckerPivot hIJ)} := by
    rw [card_filter, card_filter]
    convert Equiv.sum_comp (Tuple.sort r₁) (fun x ↦ if r₁ x < I (pluckerPivot hIJ) then 1 else 0)
    rfl
  have hle := card_le_card (s := insert a₀.val (univ.filter (· < pluckerPivot hIJ)))
    (t := univ.filter (fun x ↦ r₁ x < I (pluckerPivot hIJ))) fun x hx ↦ by
      rcases mem_insert.1 hx with rfl | hx
      · exact mem_filter.2 ⟨mem_univ _, hr₁_a₀⟩
      · have hxk := (mem_filter.1 hx).2
        exact mem_filter.2 ⟨mem_univ _,
          (pluckerLeftRow_apply_of_lt hIJ σ hxk).trans_lt (I.strictMono hxk)⟩
  rw [card_insert_of_notMem (by simpa using a₀.property), Finset.filter_gt_eq_Iio,
      Fin.card_Iio] at hle
  exact hcard_eq ▸ Nat.lt_of_succ_le hle

/-- Separating `1` splits `pluckerQuadric R hIJ` into `X (pluckerVar I) * X (pluckerVar J)` plus
the non-identity shuffles. -/
theorem pluckerQuadric_eq_mul_add_sum_erase (R : Type*) [CommRing R] {I J : Fin d ↪o Fin n}
    (hIJ : ¬ I ≤ J) [DecidableEq (Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ))] :
    pluckerQuadric R hIJ = X (pluckerVar I) * X (pluckerVar J) +
      ∑ σ ∈ (pluckerShuffleFinset hIJ).erase 1, Perm.sign σ •
        (pluckerLift R (pluckerLeftRow hIJ σ) * pluckerLift R (pluckerRightRow hIJ σ)) := by
  rw [pluckerQuadric_def, ← add_sum_erase _ _ (one_mem_pluckerShuffleFinset hIJ), map_one, one_smul,
    pluckerLeftRow_one, pluckerRightRow_one, pluckerLift_coe, pluckerLift_coe]

/-- Separating `1` splits `pluckerQuadric R hIJ` into its diagonal monomial plus non-identity
shuffles. -/
theorem pluckerQuadric_eq_monomial_add_sum_erase (R : Type*) [CommRing R] {I J : Fin d ↪o Fin n}
    (hIJ : ¬ I ≤ J) [DecidableEq (Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ))] :
    pluckerQuadric R hIJ =
      monomial (Finsupp.single (pluckerVar I) 1 + Finsupp.single (pluckerVar J) 1) 1 +
        ∑ σ ∈ (pluckerShuffleFinset hIJ).erase 1, Perm.sign σ •
          (pluckerLift R (pluckerLeftRow hIJ σ) * pluckerLift R (pluckerRightRow hIJ σ)) := by
  rw [pluckerQuadric_eq_mul_add_sum_erase, X, X, monomial_mul_monomial, one_mul]

private theorem degree_sum_erase_pluckerShuffleFinset_lt (R : Type*) [CommRing R]
    {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    [DecidableEq (Perm (PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ))] (hlt : toLex I < toLex J) :
    MonomialOrder.degRevLex.degree
        (∑ σ ∈ (pluckerShuffleFinset hIJ).erase 1, Perm.sign σ •
          (pluckerLift R (pluckerLeftRow hIJ σ) * pluckerLift R (pluckerRightRow hIJ σ)))
      ≺[MonomialOrder.degRevLex]
        Finsupp.single (pluckerVar I) 1 + Finsupp.single (pluckerVar J) 1 := by
  have hzero : (0 : (Lex (Fin d ↪o Fin n))ᵒᵈ →₀ ℕ) ≺[MonomialOrder.degRevLex]
      Finsupp.single (pluckerVar I) 1 + Finsupp.single (pluckerVar J) 1 :=
    (MonomialOrder.degRevLex_lt_iff.trans DegRevLex.lt_iff).2 (Or.inl (by simp))
  refine lt_of_le_of_lt MonomialOrder.degRevLex.degree_sum_le
    ((Finset.sup_lt_iff (by simpa using hzero)).2 fun σ hσ ↦ ?_)
  obtain ⟨hne, hσT⟩ := mem_erase.1 hσ
  by_cases hl : Function.Injective (pluckerLeftRow hIJ σ)
  · by_cases hr : Function.Injective (pluckerRightRow hIJ σ)
    · set I' := OrderEmbedding.ofStrictMono
        (pluckerLeftRow hIJ σ ∘ Tuple.sort (pluckerLeftRow hIJ σ)) (Tuple.strictMono_comp_sort hl)
      set J' := OrderEmbedding.ofStrictMono
        (pluckerRightRow hIJ σ ∘ Tuple.sort (pluckerRightRow hIJ σ)) (Tuple.strictMono_comp_sort hr)
      have hterm : Perm.sign σ •
          (pluckerLift R (pluckerLeftRow hIJ σ) * pluckerLift R (pluckerRightRow hIJ σ)) =
          monomial (Finsupp.single (pluckerVar I') 1 + Finsupp.single (pluckerVar J') 1)
            (((Perm.sign σ * Perm.sign (Tuple.sort (pluckerLeftRow hIJ σ)) *
              Perm.sign (Tuple.sort (pluckerRightRow hIJ σ)) : ℤˣ) : ℤ) : R) := by
        simp only [pluckerLift, hl, hr, dite_true, I', J', X, Units.smul_def, smul_monomial,
          zsmul_eq_mul, mul_one, monomial_mul_monomial, Units.val_mul, Int.cast_mul, mul_assoc]
      exact hterm ▸ lt_of_le_of_lt (MonomialOrder.degRevLex.degree_monomial_le _)
        (MonomialOrder.degRevLex_single_add_single_lt_of_max_lt <|
          (max_eq_left (pluckerVar_le_iff.2 hlt.le)).trans_lt
            ((pluckerVar_lt_iff.2 (toLex_sorted_pluckerLeftRow_lt hIJ hσT hne hl)).trans_le
              (le_max_left _ _)))
    · simpa [pluckerLift, hr] using hzero
  · simpa [pluckerLift, hl] using hzero

private theorem pluckerPivot_fin_two {I J : Fin 2 ↪o Fin n} (hIJ : ¬ I ≤ J)
    (hlt : toLex I < toLex J) : pluckerPivot hIJ = 1 := by
  obtain ⟨c, hceq, hclt⟩ := OrderEmbedding.toLex_lt_iff.1 hlt
  have h0 : I 0 ≤ J 0 := if hc : c = 0 then (hc ▸ hclt).le else (hceq 0 (Fin.pos_of_ne_zero hc)).le
  have : pluckerPivot hIJ ≠ 0 := fun h ↦ (h ▸ apply_pluckerPivot_lt hIJ).not_ge h0
  exact Fin.ext (by omega)

private noncomputable def pluckerFinThreeEquiv {I J : Fin 2 ↪o Fin n} {hIJ : ¬ I ≤ J}
    (hpiv : pluckerPivot hIJ = 1) : Fin 3 ≃ PluckerLeftTail hIJ ⊕ PluckerRightInit hIJ where
  toFun := ![Sum.inl ⟨1, by simp [hpiv]⟩, Sum.inr ⟨0, by simp [hpiv]⟩, Sum.inr ⟨1, by simp [hpiv]⟩]
  invFun := Sum.elim (fun _ ↦ 0) (fun b ↦ if b.val = 0 then 1 else 2)
  left_inv i := by fin_cases i <;> rfl
  right_inv := by
    rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · obtain rfl : a = 1 := Fin.ext (by simp [hpiv, Fin.lt_def] at ha; omega); rfl
    · fin_cases b <;> rfl

private theorem sumElim_pluckerFinThreeEquiv {I J : Fin 2 ↪o Fin n} {hIJ : ¬ I ≤ J}
    (hpiv : pluckerPivot hIJ = 1) (i : Fin 3) :
    Sum.elim (fun a : PluckerLeftTail hIJ ↦ I a.val) (fun b : PluckerRightInit hIJ ↦ J b.val)
      (pluckerFinThreeEquiv hpiv i) = ![I 1, J 0, J 1] i := by fin_cases i <;> rfl

private theorem pluckerShuffleFinset_fin_two {I J : Fin 2 ↪o Fin n} {hIJ : ¬ I ≤ J}
    (hpiv : pluckerPivot hIJ = 1) :
    pluckerShuffleFinset hIJ =
      ({1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 0 2} : Finset (Perm (Fin 3))).map
        (pluckerFinThreeEquiv hpiv).permCongr.toEmbedding := by
  have hmono : StrictMono (toLex ∘ pluckerFinThreeEquiv hpiv) :=
    Fin.strictMono_iff_lt_succ.2 <| Fin.forall_fin_two.2
      ⟨Sum.Lex.sep _ _, Sum.Lex.inr_lt_inr_iff.2 (Subtype.mk_lt_mk.2 (by decide))⟩
  have hfilter : univ.filter (fun τ : Perm (Fin 3) ↦ τ 1 < τ 2) =
      {1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 0 2} := by decide
  rw [← hfilter]; ext σ; simp only [mem_pluckerShuffleFinset, mem_map, mem_filter, mem_univ,
    true_and, Equiv.coe_toEmbedding]
  refine ⟨fun ⟨_, hσr⟩ ↦ ⟨(pluckerFinThreeEquiv hpiv).permCongr.symm σ,
      hmono.lt_iff_lt.1 (by
        simp only [Function.comp_apply, Equiv.permCongr_symm, Equiv.permCongr_apply,
          Equiv.symm_symm, Equiv.apply_symm_apply]
        exact hσr (a := ⟨0, by simp [hpiv]⟩) (b := ⟨1, by simp [hpiv]⟩)
          (Subtype.mk_lt_mk.2 (by decide))),
      (pluckerFinThreeEquiv hpiv).permCongr.apply_symm_apply σ⟩, ?_⟩
  rintro ⟨τ, hτ, rfl⟩
  refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ hab ↦ by
      have := Subtype.mk_lt_mk.1 hab; simp [hpiv, Fin.lt_def] at ha hb; omega,
    fun ⟨a, ha⟩ ⟨b, hb⟩ hab ↦ ?_⟩
  have := Subtype.mk_lt_mk.1 hab
  obtain rfl : a = 0 := Fin.ext (by omega); obtain rfl : b = 1 := Fin.ext (by omega)
  simpa [pluckerFinThreeEquiv, Equiv.permCongr_apply] using hmono hτ

private theorem pluckerLeftRow_permCongr_finThree {I J : Fin 2 ↪o Fin n} {hIJ : ¬ I ≤ J}
    (hpiv : pluckerPivot hIJ = 1) (τ : Perm (Fin 3)) :
    pluckerLeftRow hIJ ((pluckerFinThreeEquiv hpiv).permCongr τ) =
      ![I 0, ![I 1, J 0, J 1] (τ 0)] :=
  funext <| Fin.forall_fin_two.2 ⟨pluckerLeftRow_apply_of_lt hIJ _ (by simp [hpiv]), by
    rw [pluckerLeftRow_apply_of_le hIJ _ (by simp [hpiv]), Matrix.cons_val_one,
      ← sumElim_pluckerFinThreeEquiv hpiv]; congr 1⟩

private theorem pluckerRightRow_permCongr_finThree {I J : Fin 2 ↪o Fin n} {hIJ : ¬ I ≤ J}
    (hpiv : pluckerPivot hIJ = 1) (τ : Perm (Fin 3)) :
    pluckerRightRow hIJ ((pluckerFinThreeEquiv hpiv).permCongr τ) =
      ![![I 1, J 0, J 1] (τ 1), ![I 1, J 0, J 1] (τ 2)] :=
  funext <| Fin.forall_fin_two.2 ⟨by
    rw [pluckerRightRow_apply_of_le hIJ _ (by simp [hpiv]), Matrix.cons_val_zero,
      ← sumElim_pluckerFinThreeEquiv hpiv]; congr 1, by
    rw [pluckerRightRow_apply_of_le hIJ _ (by simp [hpiv]), Matrix.cons_val_one,
      ← sumElim_pluckerFinThreeEquiv hpiv]; congr 1⟩

/-- **Three-term Plücker relation for `2 × 2` maximal minors.** For incomparable
`I, J : Fin 2 ↪o Fin n` with `toLex I < toLex J` (equivalently `I 0 < J 0 < J 1 < I 1`),
`pluckerQuadric R hIJ` equals
`X_{I 0, I 1} X_{J 0, J 1} - X_{I 0, J 1} X_{J 0, I 1} + X_{I 0, J 0} X_{J 1, I 1}`. -/
theorem pluckerQuadric_fin_two (R : Type*) [CommRing R] {I J : Fin 2 ↪o Fin n}
    (hIJ : ¬ I ≤ J) (hlt : toLex I < toLex J) :
    pluckerQuadric R hIJ =
      X (pluckerVar I) * X (pluckerVar J) -
        pluckerLift R ![I 0, J 1] * pluckerLift R ![J 0, I 1] +
        pluckerLift R ![I 0, J 0] * pluckerLift R ![J 1, I 1] := open Classical in by
  have hpiv := pluckerPivot_fin_two hIJ hlt
  have hs1 : Perm.sign (Equiv.swap 0 1 : Perm (Fin 3)) = -1 := Perm.sign_swap (by decide)
  have hs2 : Perm.sign (Equiv.swap 0 1 * Equiv.swap 0 2 : Perm (Fin 3)) = 1 := by
    rw [map_mul, hs1, Perm.sign_swap (by decide)]; decide
  have hvec (K : Fin 2 ↪o Fin n) : ![K 0, K 1] = ⇑K := funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  rw [pluckerQuadric_def, pluckerShuffleFinset_fin_two hpiv, sum_map]
  simp only [Equiv.coe_toEmbedding, Perm.sign_permCongr,
    pluckerLeftRow_permCongr_finThree hpiv, pluckerRightRow_permCongr_finThree hpiv]
  rw [sum_insert (by decide), sum_pair (by decide)]
  simp only [map_one, one_smul, Perm.coe_one, id_eq, Perm.mul_apply, Equiv.swap_apply_def,
    Fin.reduceEq, ite_true, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hs1, hs2, Units.smul_def,
    Units.val_neg, Units.val_one, neg_smul]
  rw [hvec I, hvec J, pluckerLift_coe, pluckerLift_coe,
    pluckerLift_pair_swap R (I 1) (J 1), pluckerLift_pair_swap R (I 1) (J 0)]
  ring

/-- **Explicit three-term Grassmann–Plücker relation** on `a < b < c < e` in `Fin n`: for
`I = ![a, e]` and `J = ![b, c]`,
`pluckerQuadric R hIJ = X_{a, e} X_{b, c} - X_{a, c} X_{b, e} + X_{a, b} X_{c, e}`. -/
theorem pluckerQuadric_ofStrictMono_pair (R : Type*) [CommRing R] {a b c e : Fin n}
    (hab : a < b) (hbc : b < c) (hce : c < e) {hae : StrictMono ![a, e]} {hbc' : StrictMono ![b, c]}
    (hIJ : ¬ OrderEmbedding.ofStrictMono ![a, e] hae ≤ OrderEmbedding.ofStrictMono ![b, c] hbc') :
    pluckerQuadric R hIJ =
      X (pluckerVar (OrderEmbedding.ofStrictMono ![a, e] hae)) *
        X (pluckerVar (OrderEmbedding.ofStrictMono ![b, c] hbc')) -
        X (pluckerVar (OrderEmbedding.ofStrictMono ![a, c]
          (strictMono_vecEmpty.vecCons (hab.trans hbc)))) *
          X (pluckerVar (OrderEmbedding.ofStrictMono ![b, e]
            (strictMono_vecEmpty.vecCons (hbc.trans hce)))) +
        X (pluckerVar (OrderEmbedding.ofStrictMono ![a, b] (strictMono_vecEmpty.vecCons hab))) *
          X (pluckerVar (OrderEmbedding.ofStrictMono ![c, e]
            (strictMono_vecEmpty.vecCons hce))) := by
  have hlift {x y : Fin n} (h : StrictMono ![x, y]) :
      pluckerLift R ![x, y] = X (pluckerVar (OrderEmbedding.ofStrictMono ![x, y] h)) := by
    simpa only [OrderEmbedding.coe_ofStrictMono] using
      pluckerLift_coe R (OrderEmbedding.ofStrictMono ![x, y] h)
  rw [pluckerQuadric_fin_two R hIJ
    (OrderEmbedding.toLex_lt_iff.2 ⟨0, fun j hj ↦ (Fin.not_lt_zero j hj).elim, hab⟩)]
  simp only [OrderEmbedding.coe_ofStrictMono, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hlift (strictMono_vecEmpty.vecCons (hab.trans hbc)),
    hlift (strictMono_vecEmpty.vecCons (hbc.trans hce)),
    hlift (strictMono_vecEmpty.vecCons hab), hlift (strictMono_vecEmpty.vecCons hce)]

@[simp]
theorem monic_pluckerQuadric (R : Type*) [CommRing R] {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (hlt : toLex I < toLex J) : MonomialOrder.degRevLex.Monic (pluckerQuadric R hIJ) := by
  classical
  nontriviality R
  rw [pluckerQuadric_eq_monomial_add_sum_erase]
  exact (MonomialOrder.degRevLex.monic_monomial.2 rfl).add_of_lt <| by
    simpa [MonomialOrder.degRevLex.degree_monomial] using
      degree_sum_erase_pluckerShuffleFinset_lt R hIJ hlt

@[simp]
theorem degree_pluckerQuadric (R : Type*) [CommRing R] [Nontrivial R] {I J : Fin d ↪o Fin n}
    (hIJ : ¬ I ≤ J) (hlt : toLex I < toLex J) :
    MonomialOrder.degRevLex.degree (pluckerQuadric R hIJ) =
      Finsupp.single (pluckerVar I) 1 + Finsupp.single (pluckerVar J) 1 := by
  classical
  rw [pluckerQuadric_eq_monomial_add_sum_erase, MonomialOrder.degRevLex.degree_add_of_lt]
  · simp [MonomialOrder.degRevLex.degree_monomial]
  · simpa [MonomialOrder.degRevLex.degree_monomial] using
      degree_sum_erase_pluckerShuffleFinset_lt R hIJ hlt

@[simp]
theorem leadingTerm_pluckerQuadric {R : Type*} [CommRing R] {I J : Fin d ↪o Fin n} (hIJ : ¬ I ≤ J)
    (hlt : toLex I < toLex J) :
    MonomialOrder.degRevLex.leadingTerm (pluckerQuadric R hIJ) =
      X (pluckerVar I) * X (pluckerVar J) := by
  nontriviality R
  rw [_root_.MonomialOrder.leadingTerm, degree_pluckerQuadric R hIJ hlt,
    (monic_pluckerQuadric R hIJ hlt).leadingCoeff_eq_one, X, X, monomial_mul_monomial, one_mul]

/-- The set of quadratic Plücker straightening relations for incomparable `(I, J)` with
`toLex I < toLex J`. -/
noncomputable def pluckerQuadrics (R : Type*) [CommRing R] (n d : ℕ) :
    Set (MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R) :=
  {g | ∃ (I J : Fin d ↪o Fin n) (hIJ : ¬ I ≤ J), toLex I < toLex J ∧ pluckerQuadric R hIJ = g}

theorem pluckerQuadrics_def (R : Type*) [CommRing R] (n d : ℕ) :
    pluckerQuadrics R n d = {g | ∃ (I J : Fin d ↪o Fin n) (hIJ : ¬ I ≤ J),
      toLex I < toLex J ∧ pluckerQuadric R hIJ = g} := (rfl)

@[simp]
theorem mem_pluckerQuadrics_iff {R : Type*} [CommRing R]
    {g : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R} :
    g ∈ pluckerQuadrics R n d ↔
      ∃ (I J : Fin d ↪o Fin n) (hIJ : ¬ I ≤ J), toLex I < toLex J ∧ pluckerQuadric R hIJ = g :=
  Iff.rfl

@[simp]
theorem image_map_pluckerQuadrics {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (n d : ℕ) : MvPolynomial.map φ '' pluckerQuadrics R n d = pluckerQuadrics S n d := by
  ext g; simp only [Set.mem_image, mem_pluckerQuadrics_iff]
  exact ⟨fun ⟨_, ⟨I, J, hIJ, hlt, h1⟩, h2⟩ ↦
      ⟨I, J, hIJ, hlt, by rw [← h2, ← h1, map_pluckerQuadric]⟩,
    fun ⟨I, J, hIJ, hlt, h⟩ ↦ ⟨_, ⟨I, J, hIJ, hlt, rfl⟩, h ▸ map_pluckerQuadric φ hIJ⟩⟩

theorem pluckerQuadrics_subset_pluckerIdeal (R : Type*) [CommRing R] (n d : ℕ) :
    pluckerQuadrics R n d ⊆ pluckerIdeal R n d := fun _ ⟨_, _, hIJ, _, h⟩ ↦
  h ▸ pluckerQuadric_mem_pluckerIdeal R hIJ

theorem monic_of_mem_pluckerQuadrics {R : Type*} [CommRing R]
    {g : MvPolynomial (Lex (Fin d ↪o Fin n))ᵒᵈ R} (hg : g ∈ pluckerQuadrics R n d) :
    MonomialOrder.degRevLex.Monic g := by
  obtain ⟨_, _, hIJ, hlt, rfl⟩ := hg; exact monic_pluckerQuadric R hIJ hlt

end Straightening

end TauCeti
