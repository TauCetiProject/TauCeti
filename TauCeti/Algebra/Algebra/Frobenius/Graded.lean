/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import TauCeti.Algebra.Algebra.Frobenius.Handle
public import TauCeti.RingTheory.GradedAlgebra.TensorProduct
public import TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Graded and even-supported Frobenius algebras

This file develops the degree theory of Frobenius algebras on internally `ℤ`-graded algebras over
an arbitrary commutative semiring `R`, without assuming a field, negation, commutativity, or a
basis.

## Main results

* `TauCeti.isHomogeneous_algebraLinearMap_of_gradedAlgebra`,
  `TauCeti.isHomogeneous_trivialGrading_neg_iff`, `TauCeti.even_of_isHomogeneous_ne_zero`: unit
  degree, vanishing characterization of trace degree, and evenness of the degree on even-supported
  modules.
* `Coalgebra.IsFrobenius.isHomogeneous_comul_iff_isHomogeneous_counit`: `deg Δ = d ↔ deg ε = -d`.
* `Coalgebra.handleElement_mem_grade`, `Coalgebra.IsFrobenius.handleElement_mem_grade_of_counit`,
  `Coalgebra.isHomogeneous_mul'_comp_comul`, `Coalgebra.isHomogeneous_mul'_comp_comul_pow`: degree
  of the handle element and iterated handle operator.
* `LinearMap.isHomogeneous_frobeniusCoalgebra_comul`, `LinearMap.traceDualBasis_mem_grade`:
  reconstructed comultiplication degree and homogeneous trace-dual bases.
* `TauCeti.odd_eq_bot_iff_of_isHomogeneous_linearEquiv`,
  `TauCeti.isHomogeneous_comp_linearEquiv_iff`,
  `TauCeti.odd_tensorProduct_piece_eq_bot`, `TauCeti.isHomogeneous_dualDistrib_tmul`,
  `TauCeti.odd_baseChange_eq_bot`, `TauCeti.isHomogeneous_dualBaseChange`,
  `TauCeti.baseChange_basis_mem_grade`, `TauCeti.isHomogeneous_dualBaseChange_graded`,
  `Coalgebra.IsFrobenius.isHomogeneous_baseChange_comul`,
  `Coalgebra.IsFrobenius.isHomogeneous_tensorProduct_comul`: compatibility with degree-zero
  equivalences, tensor products, and scalar extension.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
* J. Goertz, A. Marino, P. Wedrich, *The gl(N) web algebra and foams* (v1), Example 2.9,
  Lemma 3.32, Definition 3.35.
-/

public section

open scoped DirectSum TensorProduct

/-! ### Unit map degree and degree-vanishing criteria -/

namespace TauCeti

section Unit

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- The unit map `Algebra.linearMap R A` of an internally `ℤ`-graded algebra is homogeneous of
degree zero from the trivial grading of `R`. -/
theorem isHomogeneous_algebraLinearMap_of_gradedAlgebra :
    TauCeti.LinearMap.IsHomogeneous (Algebra.linearMap R A) (trivialGrading R R) 𝒜 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p r hr
  rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
  · rw [zero_add, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact (𝒜 0).smul_mem r (SetLike.one_mem_graded 𝒜)
  · simp

/-- A linear functional `ε : M →ₗ[R] R` is homogeneous of degree `-d` into the trivial grading
of `R` if and only if it vanishes on every homogeneous piece of degree `p ≠ d`. -/
theorem isHomogeneous_trivialGrading_neg_iff {M : Type*} [AddCommMonoid M] [Module R M]
    (ℳ : ℤ → Submodule R M) (ε : M →ₗ[R] R) (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous ε ℳ (trivialGrading R R) (-d) ↔
      ∀ (p : ℤ), p ≠ d → ∀ x ∈ ℳ p, ε x = 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  refine ⟨fun h p hp x hx ↦ ((mem_trivialGrading_iff R R).mp (h p x hx)).resolve_left (by omega),
    fun h p x hx ↦ (mem_trivialGrading_iff R R).mpr ?_⟩
  by_cases hp : p = d
  · exact Or.inl (by omega)
  · exact Or.inr (h p hp x hx)

/-- If a nonzero functional on an internally `ℤ`-graded module has degree `-d` and the module has
even support, then `d` is even. -/
theorem even_of_isHomogeneous_ne_zero {M : Type*} [AddCommMonoid M] [Module R M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    (heven : ∀ p : ℤ, Odd p → ℳ p = ⊥) {ε : M →ₗ[R] R} {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε ℳ (trivialGrading R R) (-d)) (hne : ε ≠ 0) :
    Even d := by
  by_contra hnot
  have hodd : Odd d := Int.not_even_iff_odd.mp hnot
  apply hne
  refine (InternalGrading.ofDecomposition ℳ).linearMap_ext fun p x hx ↦ ?_
  rw [InternalGrading.ofDecomposition_piece] at hx
  by_cases hp : p = d
  · subst hp; rw [heven p hodd] at hx; simp [(Submodule.mem_bot R).mp hx]
  · rw [_root_.LinearMap.zero_apply]
    exact (isHomogeneous_trivialGrading_neg_iff ℳ ε d).mp hε p hp x hx

private theorem mem_of_decompose_eq_zero {M : Type*} [AddCommMonoid M] [Module R M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ] {k : ℤ} {v : M}
    (h : ∀ n ≠ k, (DirectSum.decompose ℳ v n : M) = 0) : v ∈ ℳ k := by
  classical
  rw [← DirectSum.sum_support_decompose ℳ v]
  refine Submodule.sum_mem _ fun n _ ↦ ?_
  by_cases hn : n = k
  · exact hn ▸ (DirectSum.decompose ℳ v n).2
  · rw [h n hn]; exact Submodule.zero_mem _

end Unit

end TauCeti

/-! ### Degree duality between comultiplication and counit -/

namespace Coalgebra

section HandleDegree

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] [CoalgebraStruct R A]

/-- If comultiplication is homogeneous of degree `d`, then the handle element lies in degree `d`. -/
theorem handleElement_mem_grade {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d) :
    handleElement R A ∈ 𝒜 d := by
  rw [handleElement_def]
  simpa only [zero_add, add_zero] using
    (TauCeti.isHomogeneous_mul'_of_gradedAlgebra 𝒜).map_mem
      (hΔ.map_mem (SetLike.one_mem_graded 𝒜))

/-- If comultiplication is homogeneous of degree `d`, then the handle operator `m ∘ Δ` is
homogeneous of degree `d`. -/
theorem isHomogeneous_mul'_comp_comul {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous
      (LinearMap.mul' R A ∘ₗ comul (R := R) (A := A)) 𝒜 𝒜 d := by
  simpa only [add_zero] using (TauCeti.isHomogeneous_mul'_of_gradedAlgebra 𝒜).comp hΔ

/-- If comultiplication is homogeneous of degree `d`, then the `g`-fold handle operator
`(m ∘ Δ) ^ g` is homogeneous of degree `g * d`. -/
theorem isHomogeneous_mul'_comp_comul_pow {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d) (g : ℕ) :
    TauCeti.LinearMap.IsHomogeneous
      ((LinearMap.mul' R A ∘ₗ comul (R := R) (A := A)) ^ g) 𝒜 𝒜 (g * d) := by
  induction g with
  | zero =>
    simpa only [pow_zero, Module.End.one_eq_id, Nat.cast_zero, zero_mul] using
      TauCeti.LinearMap.isHomogeneous_id 𝒜
  | succ g ih =>
    have hdeg : (g : ℤ) * d + d = ((g + 1 : ℕ) : ℤ) * d := by push_cast; ring
    rw [pow_succ', ← hdeg]
    exact (isHomogeneous_mul'_comp_comul 𝒜 hΔ).comp ih

end HandleDegree

namespace IsFrobenius

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

private noncomputable def degProj (n : ℤ) : A →ₗ[R] A :=
  (𝒜 n).subtype ∘ₗ DirectSum.component R ℤ (fun i ↦ 𝒜 i) n ∘ₗ
    (DirectSum.decomposeLinearEquiv (R := R) 𝒜).toLinearMap

private theorem degProj_apply_of_mem {n p : ℤ} {a : A} (ha : a ∈ 𝒜 p) :
    degProj 𝒜 n a = if p = n then a else 0 := by
  change (DirectSum.decompose 𝒜 a n : A) = if p = n then a else 0
  by_cases h : p = n
  · subst h; simp [DirectSum.decompose_of_mem_same 𝒜 ha]
  · simp [h, DirectSum.decompose_of_mem_ne 𝒜 ha h]

variable [Coalgebra R A] [IsFrobenius R A]

/-- For a Frobenius algebra on an internally `ℤ`-graded algebra, comultiplication is homogeneous
of degree `d` if and only if the counit is homogeneous of degree `-d`. -/
theorem isHomogeneous_comul_iff_isHomogeneous_counit (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (comul (R := R) (A := A)) 𝒜
        ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
          (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d ↔
      TauCeti.LinearMap.IsHomogeneous (counit (R := R) (A := A)) 𝒜
        (TauCeti.trivialGrading R R) (-d) := by
  classical
  let G := TauCeti.InternalGrading.ofDecomposition 𝒜
  let G₂ := G.tensorProduct G
  constructor
  · intro hΔ
    rw [TauCeti.isHomogeneous_trivialGrading_neg_iff]
    intro p hp x hx
    have h1 : comul (R := R) (1 : A) ∈ G₂.piece d := by
      simpa only [zero_add] using hΔ.map_mem (SetLike.one_mem_graded 𝒜)
    have hproj_eq :
        (degProj 𝒜 0).rTensor A (comul (R := R) (1 : A)) =
          (degProj 𝒜 d).lTensor A (comul (R := R) (1 : A)) := by
      refine G.tensorProduct_piece_le G
        (C := LinearMap.eqLocus ((degProj 𝒜 0).rTensor A) ((degProj 𝒜 d).lTensor A))
        (fun r u hu v hv ↦ ?_) h1
      simp only [G, TauCeti.InternalGrading.ofDecomposition_piece] at hu hv
      rw [LinearMap.mem_eqLocus, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        degProj_apply_of_mem 𝒜 hu, degProj_apply_of_mem 𝒜 hv]
      by_cases hr : r = 0
      · subst hr; simp
      · have hne : d - r ≠ d := by omega
        simp [hr, hne]
    let t₀ : A ⊗[R] A := (degProj 𝒜 0).rTensor A (comul (R := R) (1 : A))
    have hrid : _root_.TensorProduct.rid R A ((counit (R := R) (A := A)).lTensor A t₀) = 1 := by
      have hcomm (t : A ⊗[R] A) :
          _root_.TensorProduct.rid R A
              ((counit (R := R) (A := A)).lTensor A ((degProj 𝒜 0).rTensor A t)) =
            degProj 𝒜 0
              (_root_.TensorProduct.rid R A ((counit (R := R) (A := A)).lTensor A t)) := by
        induction t using TensorProduct.inductionOn with
        | tmul u v => simp
        | add t u ht hu => simp_all
      rw [hcomm, Coalgebra.lTensor_counit_comul, _root_.TensorProduct.rid_tmul, one_smul,
        degProj_apply_of_mem 𝒜 (SetLike.one_mem_graded 𝒜)]
      simp
    have hmul_comul_one :
        (LinearMap.mulLeft R x).rTensor A (comul (R := R) (1 : A)) = comul (R := R) x := by
      have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦ f (x ⊗ₜ[R] 1))
        (right_eq_comul_comp_mul' (R := R) (A := A))
      simp only [right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
        mul_one] at h
      rw [← h]
      induction comul (R := R) (1 : A) using TensorProduct.inductionOn with
      | tmul u v => simp
      | add t u ht hu => simp_all [TensorProduct.tmul_add]
    have hzero : _root_.TensorProduct.lid R A
          ((counit (R := R) (A := A)).rTensor A ((LinearMap.mulLeft R x).rTensor A t₀)) = 0 := by
      have hcomm (t : A ⊗[R] A) :
          _root_.TensorProduct.lid R A ((counit (R := R) (A := A)).rTensor A
              ((LinearMap.mulLeft R x).rTensor A ((degProj 𝒜 d).lTensor A t))) =
            degProj 𝒜 d (_root_.TensorProduct.lid R A ((counit (R := R) (A := A)).rTensor A
              ((LinearMap.mulLeft R x).rTensor A t))) := by
        induction t using TensorProduct.inductionOn with
        | tmul u v => simp
        | add t u ht hu => simp_all
      change _root_.TensorProduct.lid R A ((counit (R := R) (A := A)).rTensor A
        ((LinearMap.mulLeft R x).rTensor A ((degProj 𝒜 0).rTensor A (comul (R := R) (1 : A))))) = 0
      rw [hproj_eq, hcomm, hmul_comul_one, Coalgebra.rTensor_counit_comul,
        _root_.TensorProduct.lid_tmul, one_smul, degProj_apply_of_mem 𝒜 hx]
      simp [hp]
    have hswap (t : A ⊗[R] A) :
        counit (R := R) (_root_.TensorProduct.lid R A
            ((counit (R := R) (A := A)).rTensor A ((LinearMap.mulLeft R x).rTensor A t))) =
          counit (R := R)
            (x * _root_.TensorProduct.rid R A ((counit (R := R) (A := A)).lTensor A t)) := by
      induction t using TensorProduct.inductionOn with
      | tmul u v => simp [mul_comm]
      | add t u ht hu => simp_all [mul_add]
    have hres := hswap t₀
    rw [hzero, map_zero, hrid, mul_one] at hres
    exact hres.symm
  · intro hε
    have hε_vanish := (TauCeti.isHomogeneous_trivialGrading_neg_iff 𝒜 _ d).mp hε
    have hpair_zero : ∀ {m k : ℤ}, m + k ≠ 2 * d →
        ∀ {t z : A ⊗[R] A}, t ∈ G₂.piece m → z ∈ G₂.piece k → traceTensorEquiv R A t z = 0 := by
      intro m k hmk t z ht hz
      refine G.tensorProduct_piece_le G
        (C := LinearMap.ker ((traceTensorEquiv R A).toLinearMap.flip z))
        (fun r t₁ ht₁ t₂ ht₂ ↦ ?_) ht
      rw [LinearMap.mem_ker, LinearMap.flip_apply, LinearEquiv.coe_coe]
      refine G.tensorProduct_piece_le G
        (C := LinearMap.ker (traceTensorEquiv R A (t₁ ⊗ₜ[R] t₂))) (fun s x hx y hy ↦ ?_) hz
      simp only [G, TauCeti.InternalGrading.ofDecomposition_piece] at ht₁ ht₂ hx hy
      rw [LinearMap.mem_ker, traceTensorEquiv_tmul]
      by_cases h1 : s + r = d
      · rw [hε_vanish _ (by omega) _ (SetLike.mul_mem_graded ht₂ hy), mul_zero]
      · rw [hε_vanish _ h1 _ (SetLike.mul_mem_graded hx ht₁), zero_mul]
    rw [TauCeti.LinearMap.isHomogeneous_def]
    intro p a ha
    have hcomul_zero : ∀ {k : ℤ}, p + k ≠ d →
        ∀ {z : A ⊗[R] A}, z ∈ G₂.piece k → traceTensorEquiv R A (comul (R := R) a) z = 0 := by
      intro k hpk z hz
      refine G.tensorProduct_piece_le G
        (C := LinearMap.ker (traceTensorEquiv R A (comul (R := R) a))) (fun s x hx y hy ↦ ?_) hz
      simp only [G, TauCeti.InternalGrading.ofDecomposition_piece] at hx hy
      rw [LinearMap.mem_ker, traceTensorEquiv_comul]
      have hdeg : s + p + (k - s) = p + k := by omega
      exact hε_vanish _ hpk _ (hdeg ▸ SetLike.mul_mem_graded (SetLike.mul_mem_graded hx ha) hy)
    refine TauCeti.mem_of_decompose_eq_zero G₂.piece fun n hn ↦ ?_
    apply (traceTensorEquiv R A).injective
    rw [map_zero]
    refine G₂.linearMap_ext fun k z hz ↦ ?_
    rw [LinearMap.zero_apply]
    by_cases hnk : n + k = 2 * d
    · have hsum := congrArg (fun t ↦ traceTensorEquiv R A t z)
        (DirectSum.sum_support_decompose G₂.piece (comul (R := R) a))
      rw [hcomul_zero (by omega) hz, map_sum, LinearMap.sum_apply, Finset.sum_eq_single n] at hsum
      · exact hsum
      · intro m _ hmn
        exact hpair_zero (by omega) (DirectSum.decompose G₂.piece (comul (R := R) a) m).2 hz
      · intro hnot; simp [DFinsupp.notMem_support_iff.mp hnot]
    · exact hpair_zero hnk (DirectSum.decompose G₂.piece (comul (R := R) a) n).2 hz

/-- If the counit of a Frobenius algebra is homogeneous of degree `-d`, then its handle element
lies in degree `d`. -/
theorem handleElement_mem_grade_of_counit {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d)) :
    Coalgebra.handleElement R A ∈ 𝒜 d :=
  Coalgebra.handleElement_mem_grade 𝒜
    ((isHomogeneous_comul_iff_isHomogeneous_counit 𝒜 d).mpr hε)

end IsFrobenius

end Coalgebra

/-! ### Trace-reconstructed comultiplication and homogeneous dual bases -/

namespace LinearMap

section GradedFrobeniusCoalgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- The comultiplication reconstructed from a perfect trace of degree `-d` is homogeneous of
degree `d`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul [Module.Finite R A] [Module.Projective R A]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε 𝒜 (TauCeti.trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous ε.frobeniusCoalgebra.comul 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d := by
  let : Coalgebra R A := ε.frobeniusCoalgebra
  have := ε.frobeniusCoalgebra_isFrobenius
  refine (Coalgebra.IsFrobenius.isHomogeneous_comul_iff_isHomogeneous_counit 𝒜 d).mpr ?_
  simpa only [Coalgebra.counit, frobeniusCoalgebra_counit] using hε

/-- For a perfect trace of degree `-d`, the trace-dual basis of a finite homogeneous basis `b`
with `b i ∈ 𝒜 (deg i)` is homogeneous, with `traceDualBasis ε b i ∈ 𝒜 (d - deg i)`. -/
theorem traceDualBasis_mem_grade (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε 𝒜 (TauCeti.trivialGrading R R) (-d))
    {ι : Type*} [Finite ι] (b : Module.Basis ι R A) (deg : ι → ℤ)
    (hb : ∀ i, b i ∈ 𝒜 (deg i)) (i : ι) :
    traceDualBasis ε b i ∈ 𝒜 (d - deg i) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hε_vanish := (TauCeti.isHomogeneous_trivialGrading_neg_iff 𝒜 ε d).mp hε
  have hrepr_zero : ∀ {q : ℤ}, q ≠ deg i → ∀ {a : A}, a ∈ 𝒜 q → b.repr a i = 0 := by
    intro q hq a ha
    have hdec := congrArg (Coalgebra.IsFrobenius.degProj 𝒜 (deg i)) (b.sum_repr a).symm
    rw [Coalgebra.IsFrobenius.degProj_apply_of_mem 𝒜 ha, ite_eq_right (fun h ↦ absurd h hq),
      map_sum] at hdec
    have hcoord := congrArg (b.coord i) hdec.symm
    simp only [map_sum, map_smul, map_zero, Module.Basis.coord_apply] at hcoord
    rw [Finset.sum_eq_single i] at hcoord
    · simpa [Coalgebra.IsFrobenius.degProj_apply_of_mem 𝒜 (hb i)] using hcoord
    · intro j _ hji
      rw [Coalgebra.IsFrobenius.degProj_apply_of_mem 𝒜 (hb j)]
      split_ifs <;> simp [b.repr_self, hji]
    · intro hnot; exact absurd (Finset.mem_univ i) hnot
  set v : A := traceDualBasis ε b i
  refine TauCeti.mem_of_decompose_eq_zero 𝒜 fun n hn ↦ ?_
  apply ((mul R A).compr₂ ε).toPerfPair.injective
  rw [map_zero]
  refine (TauCeti.InternalGrading.ofDecomposition 𝒜).linearMap_ext fun q a ha ↦ ?_
  rw [TauCeti.InternalGrading.ofDecomposition_piece] at ha
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply]
  by_cases hnq : n + q = d
  · have hsum := congrArg (fun x ↦ ε (x * a)) (DirectSum.sum_support_decompose 𝒜 v)
    rw [traceDualBasis_mul, hrepr_zero (by omega) ha, Finset.sum_mul, map_sum,
      Finset.sum_eq_single n] at hsum
    · exact hsum
    · intro m _ hmn
      exact hε_vanish (m + q) (by omega) _ (SetLike.mul_mem_graded (DirectSum.decompose 𝒜 v m).2 ha)
    · intro hnot; simp [DFinsupp.notMem_support_iff.mp hnot]
  · exact hε_vanish (n + q) hnq _ (SetLike.mul_mem_graded (DirectSum.decompose 𝒜 v n).2 ha)

end GradedFrobeniusCoalgebra

end LinearMap

/-! ### Even support and compatibility with isomorphisms, tensor products, and scalar extension -/

namespace TauCeti

section Comparisons

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]

private theorem isHomogeneous_linearEquiv_symm (e : M ≃ₗ[R] N)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap ℳ 𝒩 0) :
    TauCeti.LinearMap.IsHomogeneous e.symm.toLinearMap 𝒩 ℳ 0 := by
  have he' : TauCeti.LinearMap.IsHomogeneous e.toLinearMap
      (InternalGrading.ofDecomposition ℳ).piece (InternalGrading.ofDecomposition 𝒩).piece 0 := by
    simpa only [InternalGrading.ofDecomposition_piece] using he
  simpa only [InternalGrading.ofDecomposition_piece] using he'.linearEquiv_symm

/-- A degree-zero linear equivalence between internally `ℤ`-graded modules preserves and reflects
even support. -/
theorem odd_eq_bot_iff_of_isHomogeneous_linearEquiv (e : M ≃ₗ[R] N)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap ℳ 𝒩 0) :
    (∀ p : ℤ, Odd p → ℳ p = ⊥) ↔ (∀ p : ℤ, Odd p → 𝒩 p = ⊥) := by
  have hsymm := isHomogeneous_linearEquiv_symm ℳ 𝒩 e he
  refine ⟨fun hM p hp ↦ (Submodule.eq_bot_iff _).mpr fun y hy ↦ ?_,
    fun hN p hp ↦ (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_⟩
  · have hmem : e.symm y ∈ ℳ p := by
      simpa only [add_zero, LinearEquiv.coe_coe] using hsymm.map_mem hy
    rw [hM p hp] at hmem
    simpa [(Submodule.mem_bot R).mp hmem] using (e.apply_symm_apply y).symm
  · have hmem : e x ∈ 𝒩 p := by simpa only [add_zero, LinearEquiv.coe_coe] using he.map_mem hx
    rw [hN p hp] at hmem
    exact e.injective (by simpa using (Submodule.mem_bot R).mp hmem)

/-- Pulling back a linear functional along a degree-zero linear equivalence preserves and reflects
its degree into the trivial grading. -/
theorem isHomogeneous_comp_linearEquiv_iff (e : M ≃ₗ[R] N)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap ℳ 𝒩 0) (ε : N →ₗ[R] R) (q : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (ε ∘ₗ e.toLinearMap) ℳ (trivialGrading R R) q ↔
      TauCeti.LinearMap.IsHomogeneous ε 𝒩 (trivialGrading R R) q := by
  have hsymm := isHomogeneous_linearEquiv_symm ℳ 𝒩 e he
  refine ⟨fun h ↦ TauCeti.LinearMap.isHomogeneous_def.mpr fun p y hy ↦ ?_,
    fun h ↦ by simpa only [zero_add] using h.comp he⟩
  have hmem : e.symm y ∈ ℳ p := by
    simpa only [add_zero, LinearEquiv.coe_coe] using hsymm.map_mem hy
  simpa only [_root_.LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply] using
    h.map_mem hmem

end Comparisons

section TensorProduct

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]

/-- The total-degree tensor product of two even-supported internally `ℤ`-graded modules is
even-supported. -/
theorem odd_tensorProduct_piece_eq_bot
    (hM : ∀ p : ℤ, Odd p → ℳ p = ⊥) (hN : ∀ p : ℤ, Odd p → 𝒩 p = ⊥)
    {n : ℤ} (hn : Odd n) :
    ((InternalGrading.ofDecomposition ℳ).tensorProduct
      (InternalGrading.ofDecomposition 𝒩)).piece n = ⊥ := by
  rw [eq_bot_iff]
  refine (InternalGrading.ofDecomposition ℳ).tensorProduct_piece_le
    (InternalGrading.ofDecomposition 𝒩) (C := ⊥) fun p x hx y hy ↦ ?_
  simp only [InternalGrading.ofDecomposition_piece] at hx hy
  rw [Submodule.mem_bot]
  rcases Int.even_or_odd p with ⟨m, rfl⟩ | hp
  · rcases hn with ⟨k, rfl⟩
    rw [hN _ ⟨k - m, by ring⟩] at hy
    rw [(Submodule.mem_bot R).mp hy, TensorProduct.tmul_zero]
  · rw [hM p hp] at hx
    rw [(Submodule.mem_bot R).mp hx, TensorProduct.zero_tmul]

/-- The tensor product of traces of degrees `-d₁` and `-d₂` has degree `-(d₁ + d₂)` for the
total-degree tensor-product grading. -/
theorem isHomogeneous_dualDistrib_tmul {εM : M →ₗ[R] R} {εN : N →ₗ[R] R} {d₁ d₂ : ℤ}
    (hM : TauCeti.LinearMap.IsHomogeneous εM ℳ (trivialGrading R R) (-d₁))
    (hN : TauCeti.LinearMap.IsHomogeneous εN 𝒩 (trivialGrading R R) (-d₂)) :
    TauCeti.LinearMap.IsHomogeneous
      (TensorProduct.dualDistrib R M N (εM ⊗ₜ[R] εN))
      ((InternalGrading.ofDecomposition ℳ).tensorProduct
        (InternalGrading.ofDecomposition 𝒩)).piece
      (trivialGrading R R) (-(d₁ + d₂)) := by
  rw [isHomogeneous_trivialGrading_neg_iff]
  intro n hn z hz
  refine (InternalGrading.ofDecomposition ℳ).tensorProduct_piece_le
    (InternalGrading.ofDecomposition 𝒩)
    (C := _root_.LinearMap.ker (TensorProduct.dualDistrib R M N (εM ⊗ₜ[R] εN)))
    (fun p x hx y hy ↦ ?_) hz
  simp only [InternalGrading.ofDecomposition_piece] at hx hy
  rw [_root_.LinearMap.mem_ker, TensorProduct.dualDistrib_apply]
  by_cases hp : p = d₁
  · rw [(isHomogeneous_trivialGrading_neg_iff 𝒩 εN d₂).mp hN (n - p) (by omega) y hy, mul_zero]
  · rw [(isHomogeneous_trivialGrading_neg_iff ℳ εM d₁).mp hM p hp x hx, zero_mul]

end TensorProduct

section BaseChange

variable {R : Type*} (S : Type*) {M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] (ℳ : ℤ → Submodule R M)

/-- Extending scalars to a degree-zero `R`-algebra `S` preserves even support. -/
theorem odd_baseChange_eq_bot (hM : ∀ p : ℤ, Odd p → ℳ p = ⊥) {p : ℤ} (hp : Odd p) :
    (ℳ p).baseChange S = ⊥ := by
  rw [hM p hp, Submodule.baseChange_bot]

/-- Extending scalars preserves the degree of a linear functional into the trivial grading. -/
theorem isHomogeneous_dualBaseChange {ε : M →ₗ[R] R} {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε ℳ (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (Module.Dual.baseChange S ε)
      (fun p ↦ (ℳ p).baseChange S) (trivialGrading S S) (-d) := by
  rw [isHomogeneous_trivialGrading_neg_iff]
  intro p hp z hz
  have hle : (ℳ p).baseChange S ≤ _root_.LinearMap.ker (Module.Dual.baseChange S ε) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, _root_.LinearMap.mem_ker, TensorProduct.mk_apply,
      Module.Dual.baseChange_apply_tmul,
      (isHomogeneous_trivialGrading_neg_iff ℳ ε d).mp hε p hp x hx, zero_smul]
  exact hle hz

/-- Base change of a homogeneous basis to a degree-zero `R`-algebra `S` remains homogeneous in the
same degrees. -/
theorem baseChange_basis_mem_grade {ι : Type*} (b : Module.Basis ι R M) (deg : ι → ℤ)
    (hb : ∀ i, b i ∈ ℳ (deg i)) (i : ι) :
    b.baseChange S i ∈ (ℳ (deg i)).baseChange S := by
  rw [Module.Basis.baseChange_apply]
  exact Submodule.tmul_mem_baseChange_of_mem (1 : S) (hb i)

/-- Over a `ℤ`-graded commutative `R`-algebra `S` (with grading `𝓢`), the base-changed trace
`Module.Dual.baseChange S ε` is homogeneous of degree `-d` from the total-degree grading
`𝓢 ⊗ ℳ` into `𝓢`. -/
theorem isHomogeneous_dualBaseChange_graded (𝓢 : ℤ → Submodule R S)
    [DirectSum.Decomposition 𝓢] [DirectSum.Decomposition ℳ] {ε : M →ₗ[R] R} {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε ℳ (trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous ((Module.Dual.baseChange S ε).restrictScalars R)
      ((InternalGrading.ofDecomposition 𝓢).tensorProduct
        (InternalGrading.ofDecomposition ℳ)).piece 𝓢 (-d) := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro n z hz
  refine (InternalGrading.ofDecomposition 𝓢).tensorProduct_piece_le
    (InternalGrading.ofDecomposition ℳ)
    (C := (𝓢 (n + -d)).comap ((Module.Dual.baseChange S ε).restrictScalars R))
    (fun p s hs x hx ↦ ?_) hz
  simp only [InternalGrading.ofDecomposition_piece] at hs hx
  rw [Submodule.mem_comap, _root_.LinearMap.coe_restrictScalars, Module.Dual.baseChange_apply_tmul]
  by_cases hnp : n - p = d
  · exact (show p = n + -d by omega) ▸ (𝓢 p).smul_mem (ε x) hs
  · rw [(isHomogeneous_trivialGrading_neg_iff ℳ ε d).mp hε (n - p) hnp x hx, zero_smul]
    exact Submodule.zero_mem _

end BaseChange

end TauCeti

namespace Coalgebra.IsFrobenius

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
  [Coalgebra R A] [IsFrobenius R A]

/-- Scalar extension of a graded Frobenius algebra along a degree-zero `R`-algebra `S` preserves the
degree of comultiplication. -/
theorem isHomogeneous_baseChange_comul {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := S) (A := S ⊗[R] A))
      (fun p ↦ (𝒜 p).baseChange S)
      ((TauCeti.InternalGrading.ofDecomposition (fun p ↦ (𝒜 p).baseChange S)).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition (fun p ↦ (𝒜 p).baseChange S))).piece d := by
  have hcounit : Coalgebra.counit (R := S) (A := S ⊗[R] A) =
      Module.Dual.baseChange S (Coalgebra.counit (R := R) (A := A)) :=
    TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ rfl
  refine (isHomogeneous_comul_iff_isHomogeneous_counit (fun p ↦ (𝒜 p).baseChange S) d).mpr ?_
  rw [hcounit]
  exact TauCeti.isHomogeneous_dualBaseChange S 𝒜 hε

end BaseChange

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] [Coalgebra R A] [IsFrobenius R A]
  (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] [Coalgebra R B] [IsFrobenius R B]

/-- The tensor product of two graded Frobenius algebras with counits of degrees `-d₁` and `-d₂`
has comultiplication homogeneous of degree `d₁ + d₂` for the total-degree tensor-product
grading. -/
theorem isHomogeneous_tensorProduct_comul {d₁ d₂ : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d₁))
    (hB : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := B)) ℬ
      (TauCeti.trivialGrading R R) (-d₂)) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A ⊗[R] B))
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition ℬ)).piece
      ((TauCeti.InternalGrading.ofDecomposition
        ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
          (TauCeti.InternalGrading.ofDecomposition ℬ)).piece).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition
          ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
            (TauCeti.InternalGrading.ofDecomposition ℬ)).piece)).piece (d₁ + d₂) := by
  have hcounit : Coalgebra.counit (R := R) (A := A ⊗[R] B) =
      _root_.TensorProduct.dualDistrib R A B
        (Coalgebra.counit (R := R) (A := A) ⊗ₜ[R] Coalgebra.counit (R := R) (A := B)) :=
    _root_.TensorProduct.ext' fun _ _ ↦ by simp [TensorProduct.counit_tmul, mul_comm]
  refine (isHomogeneous_comul_iff_isHomogeneous_counit
    ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
      (TauCeti.InternalGrading.ofDecomposition ℬ)).piece (d₁ + d₂)).mpr ?_
  rw [hcounit]
  exact TauCeti.isHomogeneous_dualDistrib_tmul 𝒜 ℬ hA hB

end TensorProduct

end Coalgebra.IsFrobenius
