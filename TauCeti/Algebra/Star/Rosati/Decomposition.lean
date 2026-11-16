/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Algebra.Star.Rosati.Basic
public import TauCeti.RingTheory.CentralIdempotent
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.CentralSimple.Real
import TauCeti.Algebra.Star.Rosati.MatrixFactor
import TauCeti.RingTheory.Semisimple.Star

/-!
# Real Rosati decomposition and positivity comparison

A finite-dimensional real star algebra `E` equipped with a cyclic linear functional
`t : E →ₗ[ℝ] ℝ` satisfying `t (x * star x) > 0` for all `x ≠ 0` is semisimple and decomposes
into a finite product of real, complex, and quaternionic matrix algebras carrying their standard
adjoints (transpose on `ℝ`, conjugate transpose on `ℂ` and `ℍ[ℝ]`), in such a way that
`TauCeti.IsRosatiPositive t` agrees with positive definiteness in every factor.

## Main results

* `TauCeti.isProperStar_of_trace_mul_star_pos`: a real-linear functional strictly positive on
  `x * star x` makes an involutive star proper.
* `TauCeti.isSemisimpleRing_of_trace_mul_star_pos`: a finite-dimensional real star algebra with
  a real-linear functional strictly positive on `x * star x` is semisimple.
* `TauCeti.star_mem_centralIdempotents`: the involution preserves central idempotents.
* `TauCeti.star_coord_idempotent_eq_self`: positivity prevents the involution from permuting or
  mixing the simple factors of a product decomposition.
* `TauCeti.realRosatiDecomposition`: the real Rosati normal form and positivity comparison.

## Implementation notes

The proof proceeds in four stages:

1. **Semisimplicity.** Positivity on `x * star x` gives `IsProperStar E`, so finite dimensionality
   over `ℝ` (`IsArtinianRing.of_finite`) and `TauCeti.isSemisimpleRing_of_isProperStar` yield
   `IsSemisimpleRing E`.  Wedderburn–Artin
   (`IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`) then splits `E` into a
   finite product of matrix rings over finite-dimensional real division algebras `D i`.
2. **Factor invariance.** Every coordinate central idempotent `δ i` is sent by `star` to a central
   idempotent; positivity rules out `e (star (δ i)) i = 0`, and orthogonality `δ i * δ j = 0` then
   forces `star (δ i) = δ i`.  Thus `star` restricts to a positive involution on each simple factor
   and `IsRosatiPositive t` splits coordinatewise.
3. **Single-factor standardization.** Each `D i` is isomorphic as an `ℝ`-algebra to `ℝ`, `ℂ`, or
   `ℍ[ℝ]` (`TauCeti.nonempty_algEquiv_real_or_complex_or_quaternion`), and
   `TauCeti.exists_star_algEquiv_matrix_real`, `exists_star_algEquiv_matrix_complex`, and
   `exists_star_algEquiv_matrix_quaternion` standardize each factor.
4. **Block grouping.** Grouping the factors by division-algebra type and reindexing via
   `AlgEquiv.piCongrLeft'` produces the three-way product normal form.

Neither `[StarModule ℝ E]` nor star-invariance `∀ x, t (star x) = t x` is needed as a hypothesis:
real-linearity of `star` follows from `TauCeti.starModule_of_trace_mul_star_pos`, and
symmetrization is handled internally on each factor.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *Algorithms for abelian varieties*, §4.3.2, Proposition 4.10.
-/

public section

open scoped Matrix ComplexOrder _root_.Quaternion

namespace TauCeti

/-! ### Properness, semisimplicity, and invariance of simple factors -/

section SemisimpleAndFactors

/-- A real-linear functional strictly positive on `x * star x` forces an involutive star to be
proper (`star x * x = 0 → x = 0`). -/
theorem isProperStar_of_trace_mul_star_pos {E : Type*} [NonUnitalNonAssocSemiring E]
    [Module ℝ E] [InvolutiveStar E] (t : E →ₗ[ℝ] ℝ)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) : IsProperStar E where
  eq_zero_of_star_mul_self_eq_zero {x} hx := by
    by_contra hx0
    by_cases hsx : star x = 0
    · have h := hpos x hx0
      rw [hsx, mul_zero, map_zero] at h
      exact lt_irrefl 0 h
    · have h := hpos (star x) hsx
      rw [star_star, hx, map_zero] at h
      exact lt_irrefl 0 h

/-- A finite-dimensional real star algebra with a linear functional strictly positive on
`x * star x` is semisimple. -/
theorem isSemisimpleRing_of_trace_mul_star_pos {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    [Module.Finite ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) : IsSemisimpleRing E := by
  have : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  have : IsProperStar E := isProperStar_of_trace_mul_star_pos t hpos
  exact isSemisimpleRing_of_isProperStar E

/-- The star involution preserves central idempotents. -/
theorem star_mem_centralIdempotents {R : Type*} [Ring R] [StarRing R] {e : R}
    (he : e ∈ centralIdempotents R) : star e ∈ centralIdempotents R := by
  refine mem_centralIdempotents.mpr ⟨?_, Subring.mem_center_iff.mpr fun x ↦ ?_⟩
  · rw [IsIdempotentElem, ← star_mul, (isIdempotentElem_of_mem_centralIdempotents he).eq]
  · calc x * star e = star (e * star x) := by rw [star_mul, star_star]
      _ = star (star x * e) := by rw [mul_comm_of_mem_centralIdempotents he]
      _ = star e * x := by rw [star_mul, star_star]

/-- Positivity prevents the involution from permuting or mixing simple factors: every coordinate
central idempotent `e.symm (Pi.single i 1)` of a product of simple rings is fixed by `star`. -/
theorem star_coord_idempotent_eq_self {E : Type*} [Ring E] [Module ℝ E] [StarRing E]
    {ι : Type*} [DecidableEq ι] (A : ι → Type*) [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]
    (e : E ≃+* ∀ i, A i) (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x))
    (i : ι) :
    star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1) := by
  let δ : ι → E := fun k ↦ e.symm (Pi.single k 1)
  have hmem : ∀ k : ι, e (star (δ k)) ∈ centralIdempotents (∀ j, A j) := fun k ↦ by
    have hpi : Pi.single k (1 : A k) ∈ centralIdempotents (∀ j, A j) :=
      (mem_centralIdempotents_pi A).mpr fun j ↦ by
        by_cases hjk : j = k
        · subst hjk; simpa using one_mem_centralIdempotents (R := A j)
        · simpa [Pi.single_eq_of_ne hjk] using zero_mem_centralIdempotents (R := A j)
    exact e.map_mem_centralIdempotents
      (star_mem_centralIdempotents (e.symm.map_mem_centralIdempotents hpi))
  have h01 : ∀ k j : ι, e (star (δ k)) j = 0 ∨ e (star (δ k)) j = 1 := fun k j ↦ by
    have hj := (mem_centralIdempotents_pi A).mp (hmem k) j
    rwa [centralIdempotents_eq_pair (A j), Set.mem_insert_iff, Set.mem_singleton_iff] at hj
  have hdiag : ∀ k : ι, e (star (δ k)) k = 1 := fun k ↦ (h01 k k).resolve_left fun h0 ↦ by
    have hδne : δ k ≠ 0 := fun hzero ↦
      one_ne_zero (α := A k) (by simpa [δ] using congrFun (congrArg e hzero) k)
    have hprod : δ k * star (δ k) = 0 := e.injective <| funext fun j ↦ by
      rw [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply]
      have hδe : e (δ k) = Pi.single k 1 := e.apply_symm_apply _
      rw [hδe]
      by_cases hjk : j = k
      · subst hjk; rw [Pi.single_eq_same, one_mul]; exact h0
      · simp [Pi.single_eq_of_ne hjk]
    have hp := hpos (δ k) hδne
    rw [hprod, map_zero] at hp
    exact lt_irrefl 0 hp
  have hoff : ∀ j : ι, j ≠ i → e (star (δ i)) j = 0 := fun j hji ↦ by
    have horth : δ i * δ j = 0 := e.injective <| funext fun k ↦ by
      rw [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply]
      dsimp only [δ]; rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      by_cases hki : k = i
      · subst hki; simp [Pi.single_eq_of_ne hji.symm]
      · simp [Pi.single_eq_of_ne hki]
    have hst : star (δ j) * star (δ i) = 0 := by rw [← star_mul, horth, star_zero]
    have hcoord := congrFun (congrArg e hst) j
    rw [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply, hdiag j, one_mul] at hcoord
    exact hcoord
  refine e.injective (funext fun j ↦ ?_)
  rw [RingEquiv.apply_symm_apply]
  by_cases hji : j = i
  · subst hji; simpa using hdiag j
  · rw [Pi.single_eq_of_ne hji]; exact hoff j hji

end SemisimpleAndFactors

/-! ### Factor-wise induced star structure and block grouping -/

section FactorAssembly

/-- Nominal wrapper around a simple factor `A` so we can equip it with the induced factor
involution without colliding with `Matrix.instStarRing`. -/
@[ext]
private structure FactorCopy (A : Type*) where
  val : A

private instance {A : Type*} [Zero A] : Zero (FactorCopy A) := ⟨⟨0⟩⟩
private instance {A : Type*} [One A] : One (FactorCopy A) := ⟨⟨1⟩⟩
private instance {A : Type*} [Add A] : Add (FactorCopy A) := ⟨fun x y ↦ ⟨x.val + y.val⟩⟩
private instance {A : Type*} [Neg A] : Neg (FactorCopy A) := ⟨fun x ↦ ⟨-x.val⟩⟩
private instance {A : Type*} [Mul A] : Mul (FactorCopy A) := ⟨fun x y ↦ ⟨x.val * y.val⟩⟩
private instance {A : Type*} [SMul ℝ A] : SMul ℝ (FactorCopy A) := ⟨fun r x ↦ ⟨r • x.val⟩⟩

private instance instRingFactorCopy {A : Type*} [Ring A] : Ring (FactorCopy A) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc _ _ _ := FactorCopy.ext (add_assoc _ _ _)
  zero_add _ := FactorCopy.ext (zero_add _)
  add_zero _ := FactorCopy.ext (add_zero _)
  neg_add_cancel _ := FactorCopy.ext (neg_add_cancel _)
  add_comm _ _ := FactorCopy.ext (add_comm _ _)
  left_distrib _ _ _ := FactorCopy.ext (left_distrib _ _ _)
  right_distrib _ _ _ := FactorCopy.ext (right_distrib _ _ _)
  zero_mul _ := FactorCopy.ext (zero_mul _)
  mul_zero _ := FactorCopy.ext (mul_zero _)
  mul_assoc _ _ _ := FactorCopy.ext (mul_assoc _ _ _)
  one_mul _ := FactorCopy.ext (one_mul _)
  mul_one _ := FactorCopy.ext (mul_one _)

private instance instModuleFactorCopy {A : Type*} [Ring A] [Algebra ℝ A] :
    Module ℝ (FactorCopy A) where
  one_smul _ := FactorCopy.ext (one_smul _ _)
  mul_smul _ _ _ := FactorCopy.ext (mul_smul _ _ _)
  smul_zero _ := FactorCopy.ext (smul_zero _)
  smul_add _ _ _ := FactorCopy.ext (smul_add _ _ _)
  add_smul _ _ _ := FactorCopy.ext (add_smul _ _ _)
  zero_smul _ := FactorCopy.ext (zero_smul _ _)

private instance instAlgebraFactorCopy {A : Type*} [Ring A] [Algebra ℝ A] :
    Algebra ℝ (FactorCopy A) where
  algebraMap :=
    { toFun r := ⟨algebraMap ℝ A r⟩
      map_one' := FactorCopy.ext (map_one _)
      map_mul' _ _ := FactorCopy.ext (map_mul _ _ _)
      map_zero' := FactorCopy.ext (map_zero _)
      map_add' _ _ := FactorCopy.ext (map_add _ _ _) }
  commutes' r x := FactorCopy.ext (Algebra.commutes r x.val)
  smul_def' r x := FactorCopy.ext (Algebra.smul_def r x.val)

/-- Canonical `ℝ`-algebra isomorphism `FactorCopy A ≃ₐ[ℝ] A`. -/
private def factorCopyEquiv (A : Type*) [Ring A] [Algebra ℝ A] : FactorCopy A ≃ₐ[ℝ] A where
  toFun := FactorCopy.val
  invFun := FactorCopy.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- When `star` fixes every coordinate central idempotent `e.symm (Pi.single i 1)`, `star` acts
coordinatewise via `a ↦ e (star (e.symm (Pi.single i a))) i`. -/
private theorem apply_star_eq_coord {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
    (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (x : E) (i : ι) :
    e (star x) i = e (star (e.symm (Pi.single i (e x i)))) i := by
  have hmul : e.symm (Pi.single i 1) * x = e.symm (Pi.single i (e x i)) :=
    e.injective <| funext fun j ↦ by
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, Pi.mul_apply]
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
  have hst : star x * e.symm (Pi.single i 1) = star (e.symm (Pi.single i (e x i))) := by
    rw [← hmul, star_mul, hδ i]
  calc e (star x) i = e (star x) i * (1 : A i) := (mul_one _).symm
    _ = e (star x * e.symm (Pi.single i 1)) i := by
        rw [map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_same]
    _ = e (star (e.symm (Pi.single i (e x i)))) i := by rw [hst]

/-- When `star` fixes every coordinate central idempotent, `star` sends each coordinate slice
`e.symm (Pi.single i a)` back into the same coordinate slice. -/
private theorem apply_star_single {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
    (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (i : ι) (a : A i) :
    e (star (e.symm (Pi.single i a))) =
      Pi.single i (e (star (e.symm (Pi.single i a))) i) := by
  have hmul : e.symm (Pi.single i 1) * e.symm (Pi.single i a) = e.symm (Pi.single i a) :=
    e.injective <| funext fun j ↦ by
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, Pi.mul_apply]
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
  have hst : star (e.symm (Pi.single i a)) =
      star (e.symm (Pi.single i a)) * e.symm (Pi.single i 1) := by
    conv_lhs => rw [← hmul, star_mul, hδ i]
  funext j
  by_cases hji : j = i
  · subst hji; simp
  · conv_lhs => rw [hst]
    rw [map_mul, Pi.mul_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne hji,
      Pi.single_eq_of_ne hji, mul_zero]

/-- Induced `StarRing` structure on the `i`-th factor wrapper `FactorCopy (A i)`. -/
private abbrev inducedFactorStarRing {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
    (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (i : ι) : StarRing (FactorCopy (A i)) where
  star x := ⟨e (star (e.symm (Pi.single i x.val))) i⟩
  star_involutive x := by
    apply FactorCopy.ext
    dsimp only
    have h1 := apply_star_single e hδ i x.val
    have h2 : e.symm (Pi.single i (e (star (e.symm (Pi.single i x.val))) i)) =
        star (e.symm (Pi.single i x.val)) := by
      rw [← h1, AlgEquiv.symm_apply_apply]
    rw [h2, star_star, AlgEquiv.apply_symm_apply, Pi.single_eq_same]
  star_mul x y := by
    apply FactorCopy.ext
    dsimp only
    have hmul : e.symm (Pi.single i (x.val * y.val)) =
        e.symm (Pi.single i x.val) * e.symm (Pi.single i y.val) := by
      rw [← map_mul]; congr 1; ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
    exact (by rw [hmul, star_mul, map_mul, Pi.mul_apply] :
      e (star (e.symm (Pi.single i (x.val * y.val)))) i = _)
  star_add x y := by
    apply FactorCopy.ext
    dsimp only
    exact (by rw [Pi.single_add, map_add, star_add, map_add, Pi.add_apply] :
      e (star (e.symm (Pi.single i (x.val + y.val)))) i = _)

/-- Restriction of a linear functional `t : E →ₗ[ℝ] ℝ` to the `i`-th factor `FactorCopy (A i)`. -/
private def factorTrace {E : Type*} [Ring E] [Algebra ℝ E]
    {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
    (e : E ≃ₐ[ℝ] ∀ i, A i) (t : E →ₗ[ℝ] ℝ) (i : ι) : FactorCopy (A i) →ₗ[ℝ] ℝ where
  toFun x := t (e.symm (Pi.single i x.val))
  map_add' x y := by
    have h : (x + y).val = x.val + y.val := rfl
    rw [h, Pi.single_add, map_add, map_add]
  map_smul' r x := by
    have h : (r • x).val = r • x.val := rfl
    have hsm : Pi.single i (r • x.val) = r • Pi.single i x.val := by
      ext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
    rw [h, hsm, map_smul, map_smul, RingHom.id_apply]

/-- The factor trace `factorTrace e t i` inherits cyclicity from `t`. -/
private theorem factorTrace_cyclic {E : Type*} [Ring E] [Algebra ℝ E]
    {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
    (e : E ≃ₐ[ℝ] ∀ i, A i) (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x)) (i : ι) (x y : FactorCopy (A i)) :
    factorTrace e t i (x * y) = factorTrace e t i (y * x) := by
  have hmul : ∀ u v : A i, e.symm (Pi.single i (u * v)) =
      e.symm (Pi.single i u) * e.symm (Pi.single i v) := fun u v ↦ by
    rw [← map_mul]; congr 1; ext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [Pi.single_eq_of_ne hji]
  have h1 : (x * y).val = x.val * y.val := rfl
  have h2 : (y * x).val = y.val * x.val := rfl
  simp only [factorTrace, LinearMap.coe_mk, AddHom.coe_mk, h1, h2, hmul, hcyclic]

/-- The factor trace `factorTrace e t i` inherits strict positivity on `x * star x` from `t`. -/
private theorem factorTrace_pos {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    {ι : Type*} [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℝ (A i)]
    (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (t : E →ₗ[ℝ] ℝ) (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) (i : ι) :
    letI := inducedFactorStarRing e hδ i
    ∀ x : FactorCopy (A i), x ≠ 0 → 0 < factorTrace e t i (x * star x) := by
  let _ := inducedFactorStarRing e hδ i
  intro x hx
  have ha : x.val ≠ 0 := fun h0 ↦ hx (FactorCopy.ext h0)
  have hne : e.symm (Pi.single i x.val) ≠ 0 := fun h0 ↦
    ha (by simpa using congrFun (congrArg e h0) i)
  have hmul : e.symm (Pi.single i (x * star x).val) =
      e.symm (Pi.single i x.val) * star (e.symm (Pi.single i x.val)) :=
    e.injective <| funext fun j ↦ by
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
        apply_star_single e hδ i x.val, Pi.mul_apply]
      by_cases hji : j = i
      · subst hji; simp; rfl
      · simp [Pi.single_eq_of_ne hji]
  have hval : factorTrace e t i (x * star x) = t (e.symm (Pi.single i (x * star x).val)) := rfl
  rw [hval, hmul]
  exact hpos (e.symm (Pi.single i x.val)) hne

/-- Expansion of `t (s * x * star x)` as the sum of factor traces across a finite product
decomposition whose coordinate central idempotents are `star`-fixed. -/
private theorem trace_mul_mul_star_eq_sum_factorTrace {E : Type*} [Ring E] [Algebra ℝ E]
    [StarRing E] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (t : E →ₗ[ℝ] ℝ) (s x : E) :
    letI := inducedFactorStarRing e hδ
    t (s * x * star x) =
      ∑ i : ι, factorTrace e t i (⟨e s i⟩ * ⟨e x i⟩ * star ⟨e x i⟩) := by
  let _ := inducedFactorStarRing e hδ
  have heq : s * x * star x = ∑ i : ι,
      e.symm (Pi.single i (e s i * e x i * e (star (e.symm (Pi.single i (e x i)))) i)) := by
    refine e.injective (funext fun j ↦ ?_)
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same, map_mul, map_mul, Pi.mul_apply,
        Pi.mul_apply, apply_star_eq_coord e hδ x j]
    · intro i _ hij
      rw [AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  conv_lhs => rw [heq, map_sum]
  rfl

/-- Splitting of `IsRosatiPositive t` across the factors of a finite product decomposition
whose coordinate central idempotents are `star`-fixed. -/
private theorem isRosatiPositive_pi_iff {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    {ι : Type*} [Finite ι] [DecidableEq ι] {A : ι → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] (e : E ≃ₐ[ℝ] ∀ i, A i)
    (hδ : ∀ i : ι, star (e.symm (Pi.single i 1)) = e.symm (Pi.single i 1))
    (t : E →ₗ[ℝ] ℝ) (s : E) :
    letI := inducedFactorStarRing e hδ
    IsRosatiPositive t s ↔ ∀ i : ι, IsRosatiPositive (factorTrace e t i) ⟨e s i⟩ := by
  let _ := Fintype.ofFinite ι
  let _ := inducedFactorStarRing e hδ
  have hsa : IsSelfAdjoint s ↔ ∀ i : ι, IsSelfAdjoint (⟨e s i⟩ : FactorCopy (A i)) :=
    ⟨fun hs i ↦ FactorCopy.ext (by rw [← apply_star_eq_coord e hδ s i, hs.star_eq] :
        e (star (e.symm (Pi.single i (e s i)))) i = e s i),
      fun hs ↦ e.injective (funext fun i ↦ by
        rw [apply_star_eq_coord e hδ s i]; exact congrArg FactorCopy.val (hs i))⟩
  rw [isRosatiPositive_iff]
  simp only [isRosatiPositive_iff, forall_and, ← hsa]
  refine and_congr_right fun _ ↦ ⟨fun h i a ha ↦ ?_, fun h x hx ↦ ?_⟩
  · have ha0 : a.val ≠ 0 := fun h0 ↦ ha (FactorCopy.ext h0)
    have hx : e.symm (Pi.single i a.val) ≠ 0 := fun h0 ↦
      ha0 (by simpa using congrFun (congrArg e h0) i)
    have h1 := h (e.symm (Pi.single i a.val)) hx
    rw [trace_mul_mul_star_eq_sum_factorTrace e hδ, Finset.sum_eq_single i] at h1
    · simpa only [AlgEquiv.apply_symm_apply, Pi.single_eq_same] using h1
    · intro j _ hji
      have hz : (⟨e (e.symm (Pi.single i a.val)) j⟩ : FactorCopy (A j)) = 0 :=
        FactorCopy.ext (by rw [AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne hji]; rfl)
      rw [hz, mul_zero, zero_mul, map_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · rw [trace_mul_mul_star_eq_sum_factorTrace e hδ]
    have hex : ∃ i₀ : ι, (⟨e x i₀⟩ : FactorCopy (A i₀)) ≠ 0 := by
      by_contra hall
      push Not at hall
      refine hx (e.injective ?_)
      rw [map_zero]
      exact funext fun i ↦ congrArg FactorCopy.val (hall i)
    obtain ⟨i₀, hi₀⟩ := hex
    refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, h i₀ ⟨e x i₀⟩ hi₀⟩
    rcases eq_or_ne (⟨e x i⟩ : FactorCopy (A i)) 0 with h0 | hne
    · rw [h0, mul_zero, zero_mul, map_zero]
    · exact (h i ⟨e x i⟩ hne).le

/-- Per-factor normal-form data classifying a single simple matrix factor as real, complex, or
quaternionic with standard adjoint and matching positivity. -/
private inductive FactorNormalForm (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A]
    (t : A →ₗ[ℝ] ℝ) (d : ℕ) where
  | real (e : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ)
      (hstar : ∀ x : A, e (star x) = star (e x))
      (hpos : ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef)
  | complex (e : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ)
      (hstar : ∀ x : A, e (star x) = star (e x))
      (hpos : ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef)
  | quaternion (e : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ])
      (hstar : ∀ x : A, e (star x) = star (e x))
      (hpos : ∀ s : A, IsRosatiPositive t s ↔
        (e s).IsHermitian ∧ ∀ v : Fin d → ℍ[ℝ], v ≠ 0 →
          0 < (∑ j, ∑ k, star (v j) * (e s) j k * v k).re)

/-- Every matrix algebra over a finite-dimensional real division algebra carrying a cyclic
positive trace admits a `FactorNormalForm`. -/
private theorem nonempty_factorNormalForm {A D : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [DivisionRing D] [Algebra ℝ D] [Module.Finite ℝ D] {d : ℕ}
    (φ : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) D) (t : A →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    Nonempty (FactorNormalForm A t d) := by
  rcases nonempty_algEquiv_real_or_complex_or_quaternion D with hR | hC | hH
  · obtain ⟨ψ⟩ := hR
    obtain ⟨e, hs, hp⟩ := exists_star_algEquiv_matrix_real (φ.trans ψ.mapMatrix) t hcyclic hpos
    exact ⟨FactorNormalForm.real e hs hp⟩
  · obtain ⟨ψ⟩ := hC
    obtain ⟨e, hs, hp⟩ := exists_star_algEquiv_matrix_complex (φ.trans ψ.mapMatrix) t hcyclic hpos
    exact ⟨FactorNormalForm.complex e hs hp⟩
  · obtain ⟨ψ⟩ := hH
    obtain ⟨e, hs, hp⟩ :=
      exists_star_algEquiv_matrix_quaternion (φ.trans ψ.mapMatrix) t hcyclic hpos
    exact ⟨FactorNormalForm.quaternion e hs hp⟩

private def FactorNormalForm.tag {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {t : A →ₗ[ℝ] ℝ} {d : ℕ} : FactorNormalForm A t d → Fin 3
  | .real .. => 0
  | .complex .. => 1
  | .quaternion .. => 2

private def FactorNormalForm.realEquiv {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {t : A →ₗ[ℝ] ℝ} {d : ℕ} : (nf : FactorNormalForm A t d) → nf.tag = 0 →
      A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ
  | .real e _ _, _ => e
  | .complex .., h => nomatch h
  | .quaternion .., h => nomatch h

private def FactorNormalForm.complexEquiv {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {t : A →ₗ[ℝ] ℝ} {d : ℕ} : (nf : FactorNormalForm A t d) → nf.tag = 1 →
      A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ
  | .real .., h => nomatch h
  | .complex e _ _, _ => e
  | .quaternion .., h => nomatch h

private def FactorNormalForm.quatEquiv {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {t : A →ₗ[ℝ] ℝ} {d : ℕ} : (nf : FactorNormalForm A t d) → nf.tag = 2 →
      A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ]
  | .real .., h => nomatch h
  | .complex .., h => nomatch h
  | .quaternion e _ _, _ => e

private theorem FactorNormalForm.realEquiv_eq {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {t : A →ₗ[ℝ] ℝ} {d : ℕ} {nf : FactorNormalForm A t d} (h0 : nf.tag = 0)
    {e : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℝ} {hs hp} (h : nf = .real e hs hp) :
    nf.realEquiv h0 = e := by
  subst h; rfl

private theorem FactorNormalForm.complexEquiv_eq {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {t : A →ₗ[ℝ] ℝ} {d : ℕ} {nf : FactorNormalForm A t d} (h1 : nf.tag = 1)
    {e : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ} {hs hp} (h : nf = .complex e hs hp) :
    nf.complexEquiv h1 = e := by
  subst h; rfl

private theorem FactorNormalForm.quatEquiv_eq {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {t : A →ₗ[ℝ] ℝ} {d : ℕ} {nf : FactorNormalForm A t d} (h2 : nf.tag = 2)
    {e : A ≃ₐ[ℝ] Matrix (Fin d) (Fin d) ℍ[ℝ]} {hs hp} (h : nf = .quaternion e hs hp) :
    nf.quatEquiv h2 = e := by
  subst h; rfl

/-- Splitting a product of standardized factors `(∀ i, A i)` into the three-way product of real,
complex, and quaternionic blocks indexed by the subtypes `{i // (nf i).tag = 0, 1, 2}`. -/
private noncomputable def splitProductEquiv {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)] {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ}
    (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) :
    (∀ i, A i) ≃ₐ[ℝ]
      ((∀ i : {i // (nf i).tag = 0}, Matrix (Fin (d i.1)) (Fin (d i.1)) ℝ) ×
        (∀ i : {i // (nf i).tag = 1}, Matrix (Fin (d i.1)) (Fin (d i.1)) ℂ) ×
        (∀ i : {i // (nf i).tag = 2}, Matrix (Fin (d i.1)) (Fin (d i.1)) ℍ[ℝ])) where
  toFun x :=
    (fun i ↦ (nf i.1).realEquiv i.2 (x i.1),
      fun i ↦ (nf i.1).complexEquiv i.2 (x i.1),
      fun i ↦ (nf i.1).quatEquiv i.2 (x i.1))
  invFun y i :=
    match h : nf i with
    | .real e _ _ => e.symm (y.1 ⟨i, by simp [FactorNormalForm.tag, h]⟩)
    | .complex e _ _ => e.symm (y.2.1 ⟨i, by simp [FactorNormalForm.tag, h]⟩)
    | .quaternion e _ _ => e.symm (y.2.2 ⟨i, by simp [FactorNormalForm.tag, h]⟩)
  left_inv x := funext fun i ↦ by
    dsimp only
    split
    · rename_i e _ _ h
      rw [FactorNormalForm.realEquiv_eq _ h, AlgEquiv.symm_apply_apply]
    · rename_i e _ _ h
      rw [FactorNormalForm.complexEquiv_eq _ h, AlgEquiv.symm_apply_apply]
    · rename_i e _ _ h
      rw [FactorNormalForm.quatEquiv_eq _ h, AlgEquiv.symm_apply_apply]
  right_inv y := by
    rcases y with ⟨yR, yC, yH⟩
    refine Prod.ext (funext fun ⟨i, hi⟩ ↦ ?_)
      (Prod.ext (funext fun ⟨i, hi⟩ ↦ ?_) (funext fun ⟨i, hi⟩ ↦ ?_))
    · dsimp only
      split
      · rename_i e _ _ h
        rw [FactorNormalForm.realEquiv_eq hi h, AlgEquiv.apply_symm_apply]
      · rename_i h; simp [FactorNormalForm.tag, h] at hi
      · rename_i h; simp [FactorNormalForm.tag, h] at hi
    · dsimp only
      split
      · rename_i h; simp [FactorNormalForm.tag, h] at hi
      · rename_i e _ _ h
        rw [FactorNormalForm.complexEquiv_eq hi h, AlgEquiv.apply_symm_apply]
      · rename_i h; simp [FactorNormalForm.tag, h] at hi
    · dsimp only
      split
      · rename_i h; simp [FactorNormalForm.tag, h] at hi
      · rename_i h; simp [FactorNormalForm.tag, h] at hi
      · rename_i e _ _ h
        rw [FactorNormalForm.quatEquiv_eq hi h, AlgEquiv.apply_symm_apply]
  map_mul' _ _ := Prod.ext (funext fun _ ↦ map_mul _ _ _)
    (Prod.ext (funext fun _ ↦ map_mul _ _ _) (funext fun _ ↦ map_mul _ _ _))
  map_add' _ _ := Prod.ext (funext fun _ ↦ map_add _ _ _)
    (Prod.ext (funext fun _ ↦ map_add _ _ _) (funext fun _ ↦ map_add _ _ _))
  commutes' r := Prod.ext (funext fun _ ↦ AlgEquiv.commutes _ r)
    (Prod.ext (funext fun _ ↦ AlgEquiv.commutes _ r) (funext fun _ ↦ AlgEquiv.commutes _ r))

private theorem splitProductEquiv_star {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)] {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ}
    (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) (x : ∀ i, A i) :
    splitProductEquiv nf (star x) = star (splitProductEquiv nf x) := by
  refine Prod.ext (funext fun ⟨i, hi⟩ ↦ ?_)
    (Prod.ext (funext fun ⟨i, hi⟩ ↦ ?_) (funext fun ⟨i, hi⟩ ↦ ?_))
  · cases h : nf i with
    | real e hs _ =>
      have heq := FactorNormalForm.realEquiv_eq hi h
      simp only [splitProductEquiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk, Prod.fst_star, Pi.star_apply,
        heq, hs]
    | complex _ _ _ => simp [FactorNormalForm.tag, h] at hi
    | quaternion _ _ _ => simp [FactorNormalForm.tag, h] at hi
  · cases h : nf i with
    | real _ _ _ => simp [FactorNormalForm.tag, h] at hi
    | complex e hs _ =>
      have heq := FactorNormalForm.complexEquiv_eq hi h
      simp only [splitProductEquiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk, Prod.snd_star, Prod.fst_star,
        Pi.star_apply, heq, hs]
    | quaternion _ _ _ => simp [FactorNormalForm.tag, h] at hi
  · cases h : nf i with
    | real _ _ _ => simp [FactorNormalForm.tag, h] at hi
    | complex _ _ _ => simp [FactorNormalForm.tag, h] at hi
    | quaternion e hs _ =>
      have heq := FactorNormalForm.quatEquiv_eq hi h
      simp only [splitProductEquiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk, Prod.snd_star, Pi.star_apply,
        heq, hs]

private theorem splitProductEquiv_pos {n : ℕ} {A : Fin n → Type*} [∀ i, Ring (A i)]
    [∀ i, Algebra ℝ (A i)] [∀ i, StarRing (A i)] {t : ∀ i, A i →ₗ[ℝ] ℝ} {d : Fin n → ℕ}
    (nf : ∀ i, FactorNormalForm (A i) (t i) (d i)) (x : ∀ i, A i) :
    (∀ i, IsRosatiPositive (t i) (x i)) ↔
      (∀ i, ((splitProductEquiv nf x).1 i).PosDef) ∧
      (∀ i, ((splitProductEquiv nf x).2.1 i).PosDef) ∧
      (∀ i, ((splitProductEquiv nf x).2.2 i).IsHermitian ∧
        ∀ v : Fin (d i.1) → ℍ[ℝ], v ≠ 0 →
          0 < (∑ j, ∑ k, star (v j) * ((splitProductEquiv nf x).2.2 i) j k * v k).re) := by
  constructor
  · intro hx
    refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ?_⟩
    · cases h : nf i with
      | real e _ hp =>
        simp only [splitProductEquiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk,
          FactorNormalForm.realEquiv_eq hi h]
        exact (hp (x i)).mp (hx i)
      | complex _ _ _ => simp [FactorNormalForm.tag, h] at hi
      | quaternion _ _ _ => simp [FactorNormalForm.tag, h] at hi
    · cases h : nf i with
      | real _ _ _ => simp [FactorNormalForm.tag, h] at hi
      | complex e _ hp =>
        simp only [splitProductEquiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk,
          FactorNormalForm.complexEquiv_eq hi h]
        exact (hp (x i)).mp (hx i)
      | quaternion _ _ _ => simp [FactorNormalForm.tag, h] at hi
    · cases h : nf i with
      | real _ _ _ => simp [FactorNormalForm.tag, h] at hi
      | complex _ _ _ => simp [FactorNormalForm.tag, h] at hi
      | quaternion e _ hp =>
        simp only [splitProductEquiv, AlgEquiv.coe_mk, Equiv.coe_fn_mk,
          FactorNormalForm.quatEquiv_eq hi h]
        exact (hp (x i)).mp (hx i)
  · rintro ⟨hR, hC, hH⟩ i
    cases h : nf i with
    | real e _ hp =>
      have hi : (nf i).tag = 0 := by simp [FactorNormalForm.tag, h]
      exact (hp (x i)).mpr ((congrArg (· (x i)) (FactorNormalForm.realEquiv_eq hi h)) ▸ hR ⟨i, hi⟩)
    | complex e _ hp =>
      have hi : (nf i).tag = 1 := by simp [FactorNormalForm.tag, h]
      exact (hp (x i)).mpr
        ((congrArg (· (x i)) (FactorNormalForm.complexEquiv_eq hi h)) ▸ hC ⟨i, hi⟩)
    | quaternion e _ hp =>
      have hi : (nf i).tag = 2 := by simp [FactorNormalForm.tag, h]
      exact (hp (x i)).mpr ((congrArg (· (x i)) (FactorNormalForm.quatEquiv_eq hi h)) ▸ hH ⟨i, hi⟩)

end FactorAssembly

/-! ### The real Rosati decomposition -/

section MainTheorem

/-- **Real Rosati decomposition and positivity comparison.** A finite-dimensional real star
algebra with a cyclic linear functional `t : E →ₗ[ℝ] ℝ` strictly positive on `x * star x` is
isomorphic as a real star algebra to a finite product of real, complex, and quaternionic matrix
algebras of positive sizes carrying their standard adjoints (transpose on `ℝ`, conjugate
transpose on `ℂ` and `ℍ[ℝ]`), in such a way that `IsRosatiPositive t` agrees with positive
definiteness in every factor.

Neither `[StarModule ℝ E]` nor star-invariance `∀ x, t (star x) = t x` is needed as a hypothesis:
real-linearity of `star` is automatic (`TauCeti.starModule_of_trace_mul_star_pos`), and
symmetrizing `t` leaves `IsRosatiPositive t` unchanged. -/
theorem realRosatiDecomposition {E : Type*} [Ring E] [Algebra ℝ E] [StarRing E]
    [Module.Finite ℝ E] (t : E →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : E, t (x * y) = t (y * x))
    (hpos : ∀ x : E, x ≠ 0 → 0 < t (x * star x)) :
    ∃ (nR nC nH : ℕ) (dR : Fin nR → ℕ) (dC : Fin nC → ℕ) (dH : Fin nH → ℕ),
      (∀ i, 0 < dR i) ∧ (∀ i, 0 < dC i) ∧ (∀ i, 0 < dH i) ∧
      ∃ e : E ≃ₐ[ℝ]
          ((∀ i : Fin nR, Matrix (Fin (dR i)) (Fin (dR i)) ℝ) ×
            (∀ i : Fin nC, Matrix (Fin (dC i)) (Fin (dC i)) ℂ) ×
            (∀ i : Fin nH, Matrix (Fin (dH i)) (Fin (dH i)) ℍ[ℝ])),
        (∀ x : E, e (star x) = star (e x)) ∧
        ∀ s : E, IsRosatiPositive t s ↔
          (∀ i, ((e s).1 i).PosDef) ∧
          (∀ i, ((e s).2.1 i).PosDef) ∧
          (∀ i, ((e s).2.2 i).IsHermitian ∧
            ∀ v : Fin (dH i) → ℍ[ℝ], v ≠ 0 →
              0 < (∑ j, ∑ k, star (v j) * ((e s).2.2 i) j k * v k).re) := by
  have : IsSemisimpleRing E := isSemisimpleRing_of_trace_mul_star_pos t hpos
  obtain ⟨n, D, d, _, _, _, hd, ⟨eW⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite ℝ E
  let A : Fin n → Type _ := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)
  have hsimple : ∀ i : Fin n, IsSimpleRing (A i) := fun i ↦ by
    have : NeZero (d i) := hd i; infer_instance
  have hδ : ∀ i : Fin n, star (eW.symm (Pi.single i 1)) = eW.symm (Pi.single i 1) :=
    fun i ↦ star_coord_idempotent_eq_self A eW.toRingEquiv t hpos i
  let _ : ∀ i : Fin n, StarRing (FactorCopy (A i)) := inducedFactorStarRing eW hδ
  let nf : ∀ i : Fin n, FactorNormalForm (FactorCopy (A i)) (factorTrace eW t i) (d i) := fun i ↦
    Classical.choice (nonempty_factorNormalForm (factorCopyEquiv (A i)) (factorTrace eW t i)
      (factorTrace_cyclic eW t hcyclic i) (factorTrace_pos eW hδ t hpos i))
  let eR := Fintype.equivFin {i : Fin n // (nf i).tag = 0}
  let eC := Fintype.equivFin {i : Fin n // (nf i).tag = 1}
  let eH := Fintype.equivFin {i : Fin n // (nf i).tag = 2}
  let eWrap : E ≃ₐ[ℝ] ∀ i : Fin n, FactorCopy (A i) :=
    eW.trans (AlgEquiv.piCongrRight fun i ↦ (factorCopyEquiv (A i)).symm)
  have heWrap : ∀ (y : E) (i : Fin n), eWrap y i = ⟨eW y i⟩ := fun y i ↦ by
    simp [eWrap, factorCopyEquiv]
  let eReindex := AlgEquiv.prodCongr
    (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 0} ↦
      Matrix (Fin (d i.1)) (Fin (d i.1)) ℝ) eR)
    (AlgEquiv.prodCongr
      (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 1} ↦
        Matrix (Fin (d i.1)) (Fin (d i.1)) ℂ) eC)
      (AlgEquiv.piCongrLeft' ℝ (fun i : {i // (nf i).tag = 2} ↦
        Matrix (Fin (d i.1)) (Fin (d i.1)) ℍ[ℝ]) eH))
  let e := (eWrap.trans (splitProductEquiv nf)).trans eReindex
  refine ⟨_, _, _, fun i ↦ d (eR.symm i).1, fun i ↦ d (eC.symm i).1, fun i ↦ d (eH.symm i).1,
    fun i ↦ Nat.pos_of_ne_zero (hd (eR.symm i).1).out,
    fun i ↦ Nat.pos_of_ne_zero (hd (eC.symm i).1).out,
    fun i ↦ Nat.pos_of_ne_zero (hd (eH.symm i).1).out, e, ?_, ?_⟩
  · intro x
    have hwrap : eWrap (star x) = star (eWrap x) := funext fun i ↦ by
      rw [heWrap, Pi.star_apply, heWrap]
      exact FactorCopy.ext (apply_star_eq_coord eW hδ x i)
    have hsp := splitProductEquiv_star nf (eWrap x)
    have he_eq : ∀ y : E, e y = eReindex (splitProductEquiv nf (eWrap y)) := fun _ ↦ rfl
    rw [he_eq, he_eq, hwrap, hsp]
    rfl
  · intro s
    rw [isRosatiPositive_pi_iff eW hδ t s]
    simp_rw [← heWrap s]
    exact (splitProductEquiv_pos nf (eWrap s)).trans
      (and_congr eR.symm.forall_congr_right.symm
        (and_congr eC.symm.forall_congr_right.symm eH.symm.forall_congr_right.symm))

end MainTheorem

end TauCeti
