/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import TauCeti.Algebra.Algebra.Frobenius.Handle
public import TauCeti.Algebra.Module.GradedModule.Trivial
public import TauCeti.RingTheory.GradedAlgebra.TensorProduct
import TauCeti.Algebra.Coalgebra.BaseChange
import TauCeti.Algebra.DirectSum.Component
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.Algebra.Module.GradedModule.BaseChange
import TauCeti.Algebra.Module.GradedModule.Dual.TensorProduct

/-!
# Graded and even-supported Frobenius algebras

This file develops the degree theory of Frobenius algebras on internally `ℤ`-graded algebras over
an arbitrary commutative semiring `R`. The `Coalgebra` and `Coalgebra.IsFrobenius` results
(degree duality between comultiplication and counit, handle degrees, and compatibility with scalar
extension and tensor products) do not assume a field, negation, commutativity, or a basis; the
trace-reconstruction and trace-dual basis results
(`LinearMap.isHomogeneous_frobeniusCoalgebra_comul` and `LinearMap.traceDualBasis_mem_grade`)
assume a commutative algebra `A`.

## Main results

* `TauCeti.Coalgebra.handleElement_mem_grade`,
  `TauCeti.Coalgebra.IsFrobenius.handleElement_mem_grade_of_counit`,
  `TauCeti.Coalgebra.isHomogeneous_mul'_comp_comul`,
  `TauCeti.Coalgebra.isHomogeneous_mul'_comp_comul_pow`: degree of the handle element and iterated
  handle operator.
* `TauCeti.Coalgebra.IsFrobenius.isHomogeneous_comul_iff_isHomogeneous_counit`:
  `deg Δ = d ↔ deg ε = -d`.
* `LinearMap.isHomogeneous_frobeniusCoalgebra_comul`, `LinearMap.traceDualBasis_mem_grade`:
  reconstructed comultiplication degree and homogeneous trace-dual bases (for commutative `A`).
* `TauCeti.Coalgebra.IsFrobenius.isHomogeneous_baseChange_comul`,
  `TauCeti.Coalgebra.IsFrobenius.isHomogeneous_tensorProduct_comul`: compatibility of
  comultiplication degree with scalar extension and tensor products.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
* Goertz–Marino–Wedrich, *Monoidal 2-categories from foam evaluation*, arXiv:2602.11120v1,
  Example 2.9, Lemma 3.32, Definition 3.35.
-/

public section

open scoped DirectSum TensorProduct

/-! ### Handle degree and degree duality between comultiplication and counit -/

namespace TauCeti.Coalgebra

section HandleDegree

variable {R A : Type*} [CommSemiring R]

/-- If comultiplication is homogeneous of degree `d`, then the handle element lies in degree `d`. -/
theorem handleElement_mem_grade [NonAssocSemiring A] [Module R A] [SMulCommClass R A A]
    [IsScalarTower R A A] (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜]
    [SetLike.GradedOne 𝒜] [SetLike.GradedMul 𝒜] [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d) :
    handleElement R A ∈ 𝒜 d := by
  rw [handleElement_def]
  simpa only [zero_add, add_zero] using
    (TauCeti.isHomogeneous_mul' 𝒜).map_mem (hΔ.map_mem (SetLike.one_mem_graded 𝒜))

/-- If comultiplication is homogeneous of degree `d`, then the handle operator `m ∘ Δ` is
homogeneous of degree `d`. -/
theorem isHomogeneous_mul'_comp_comul [NonUnitalNonAssocSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] (𝒜 : ℤ → Submodule R A)
    [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜] [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous
      (LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A)) 𝒜 𝒜 d := by
  simpa only [add_zero] using (TauCeti.isHomogeneous_mul' 𝒜).comp hΔ

/-- If comultiplication is homogeneous of degree `d`, then the `g`-fold handle operator
`(m ∘ Δ) ^ g` is homogeneous of degree `g * d`. -/
theorem isHomogeneous_mul'_comp_comul_pow [NonUnitalNonAssocSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] (𝒜 : ℤ → Submodule R A)
    [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜] [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d) (g : ℕ) :
    TauCeti.LinearMap.IsHomogeneous
      ((LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A)) ^ g) 𝒜 𝒜 (g * d) := by
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

section DegreeDuality

variable {R A : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜]
  [SetLike.GradedOne 𝒜] [SetLike.GradedMul 𝒜] [Coalgebra R A] [Coalgebra.IsFrobenius R A]

omit [SetLike.GradedMul 𝒜] in
private theorem isHomogeneous_counit_of_comul (d : ℤ)
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d) := by
  let G := TauCeti.InternalGrading.ofDecomposition 𝒜
  rw [TauCeti.isHomogeneous_trivialGrading_iff]
  intro p hp x hx
  -- Since `Δ 1` has total degree `d`, projecting its left leg to degree `0` agrees with
  -- projecting its right leg to degree `d`.
  have h1 : Coalgebra.comul (R := R) (1 : A) ∈ (G.tensorProduct G).piece d := by
    simpa only [zero_add] using hΔ.map_mem (SetLike.one_mem_graded 𝒜)
  have hproj_eq :
      (TauCeti.homogeneousComponent 𝒜 0).rTensor A (Coalgebra.comul (R := R) (1 : A)) =
        (TauCeti.homogeneousComponent 𝒜 d).lTensor A
          (Coalgebra.comul (R := R) (1 : A)) := by
    refine G.tensorProduct_piece_le G
      (C := LinearMap.eqLocus ((TauCeti.homogeneousComponent 𝒜 0).rTensor A)
        ((TauCeti.homogeneousComponent 𝒜 d).lTensor A)) (fun r u hu v hv ↦ ?_) h1
    simp only [G, TauCeti.InternalGrading.ofDecomposition_piece] at hu hv
    rw [LinearMap.mem_eqLocus, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    by_cases hr : r = 0
    · subst hr
      rw [TauCeti.homogeneousComponent_apply_of_mem 𝒜 hu,
        TauCeti.homogeneousComponent_apply_of_mem 𝒜 (by simpa only [sub_zero] using hv)]
    · rw [TauCeti.homogeneousComponent_apply_of_mem_ne 𝒜 hu hr,
        TauCeti.homogeneousComponent_apply_of_mem_ne 𝒜 hv (by omega),
        TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  set t₀ : A ⊗[R] A :=
    (TauCeti.homogeneousComponent 𝒜 0).rTensor A (Coalgebra.comul (R := R) (1 : A)) with ht₀
  -- Contracting the right leg of `t₀` with `counit` recovers `1` (which lies in degree `0`).
  have hrid :
      TensorProduct.rid R A ((Coalgebra.counit (R := R) (A := A)).lTensor A t₀) = 1 := by
    have hcomm (t : A ⊗[R] A) :
        TensorProduct.rid R A ((Coalgebra.counit (R := R) (A := A)).lTensor A
            ((TauCeti.homogeneousComponent 𝒜 0).rTensor A t)) =
          TauCeti.homogeneousComponent 𝒜 0
            (TensorProduct.rid R A
              ((Coalgebra.counit (R := R) (A := A)).lTensor A t)) := by
      induction t using TensorProduct.inductionOn with
      | tmul u v => simp
      | add t u ht hu => simp_all
    rw [ht₀, hcomm, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul,
      TauCeti.homogeneousComponent_apply_of_mem 𝒜 (SetLike.one_mem_graded 𝒜)]
  -- Multiplying the left leg by `x` and contracting with `counit` projects `x` to degree `d`,
  -- which vanishes because `p ≠ d`.
  have hzero :
      TensorProduct.lid R A ((Coalgebra.counit (R := R) (A := A)).rTensor A
        ((LinearMap.mulLeft R x).rTensor A t₀)) = 0 := by
    have hcomm (t : A ⊗[R] A) :
        TensorProduct.lid R A ((Coalgebra.counit (R := R) (A := A)).rTensor A
            ((LinearMap.mulLeft R x).rTensor A
              ((TauCeti.homogeneousComponent 𝒜 d).lTensor A t))) =
          TauCeti.homogeneousComponent 𝒜 d (TensorProduct.lid R A
            ((Coalgebra.counit (R := R) (A := A)).rTensor A
              ((LinearMap.mulLeft R x).rTensor A t))) := by
      induction t using TensorProduct.inductionOn with
      | tmul u v => simp
      | add t u ht hu => simp_all
    rw [hproj_eq, hcomm, comul_mul_left x 1, mul_one, Coalgebra.rTensor_counit_comul,
      TensorProduct.lid_tmul, one_smul,
      TauCeti.homogeneousComponent_apply_of_mem_ne 𝒜 hx (by omega)]
  -- Comparing the two contractions of `t₀` under `counit` yields `counit x = 0`.
  have hswap (t : A ⊗[R] A) :
      Coalgebra.counit (R := R) (TensorProduct.lid R A
          ((Coalgebra.counit (R := R) (A := A)).rTensor A
            ((LinearMap.mulLeft R x).rTensor A t))) =
        Coalgebra.counit (R := R)
          (x * TensorProduct.rid R A
            ((Coalgebra.counit (R := R) (A := A)).lTensor A t)) := by
    induction t using TensorProduct.inductionOn with
    | tmul u v => simp [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
    | add t u ht hu => simp_all [mul_add]
  have hres := hswap t₀
  rw [hzero, map_zero, hrid, mul_one] at hres
  exact hres.symm

omit [SetLike.GradedOne 𝒜] in
private theorem traceTensorEquiv_eq_zero_of_add_ne {d m k : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d))
    (hmk : m + k ≠ 2 * d) {t z : A ⊗[R] A}
    (ht : t ∈ ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
      (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece m)
    (hz : z ∈ ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
      (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece k) :
    LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A)) t z = 0 := by
  let G := TauCeti.InternalGrading.ofDecomposition 𝒜
  have hε_vanish := (TauCeti.isHomogeneous_trivialGrading_iff 𝒜 _ (-d)).mp hε
  refine G.tensorProduct_piece_le G
    (C := LinearMap.ker
      ((LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A))).toLinearMap.flip z))
    (fun r t₁ ht₁ t₂ ht₂ ↦ ?_) ht
  rw [LinearMap.mem_ker, LinearMap.flip_apply, LinearEquiv.coe_coe]
  refine G.tensorProduct_piece_le G
    (C := LinearMap.ker
      (LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A)) (t₁ ⊗ₜ[R] t₂)))
    (fun s x hx y hy ↦ ?_) hz
  simp only [G, TauCeti.InternalGrading.ofDecomposition_piece] at ht₁ ht₂ hx hy
  rw [LinearMap.mem_ker, LinearMap.traceTensorEquiv_tmul]
  by_cases h1 : s + r = d
  · rw [hε_vanish _ (by omega) _ (SetLike.mul_mem_graded ht₂ hy), mul_zero]
  · rw [hε_vanish _ (by omega) _ (SetLike.mul_mem_graded hx ht₁), zero_mul]

omit [SetLike.GradedOne 𝒜] in
private theorem traceTensorEquiv_comul_eq_zero_of_add_ne {d p k : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d))
    (hpk : p + k ≠ d) {a : A} (ha : a ∈ 𝒜 p) {z : A ⊗[R] A}
    (hz : z ∈ ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
      (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece k) :
    LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A))
      (Coalgebra.comul (R := R) a) z = 0 := by
  let G := TauCeti.InternalGrading.ofDecomposition 𝒜
  have hε_vanish := (TauCeti.isHomogeneous_trivialGrading_iff 𝒜 _ (-d)).mp hε
  refine G.tensorProduct_piece_le G
    (C := LinearMap.ker (LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A))
      (Coalgebra.comul (R := R) a))) (fun s x hx y hy ↦ ?_) hz
  simp only [G, TauCeti.InternalGrading.ofDecomposition_piece] at hx hy
  have hcomul := LinearMap.traceTensorEquiv_comul_of_isFrobenius
    (Coalgebra.counit (R := R) (A := A)) ‹Coalgebra R A› rfl inferInstance a x y
  rw [LinearMap.mem_ker, hcomul]
  have hdeg : s + p + (k - s) = p + k := by omega
  exact hε_vanish _ (by omega) _
    (hdeg ▸ SetLike.mul_mem_graded (SetLike.mul_mem_graded hx ha) hy)

omit [SetLike.GradedOne 𝒜] in
private theorem isHomogeneous_comul_of_counit (d : ℤ)
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d := by
  let G := TauCeti.InternalGrading.ofDecomposition 𝒜
  let G₂ := G.tensorProduct G
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p a ha
  exact TauCeti.mem_of_forall_pairing_eq_zero G₂.piece G₂.piece
    (B := (LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A))).toLinearMap)
    (LinearMap.traceTensorEquiv (Coalgebra.counit (R := R) (A := A))).injective
    (D := 2 * d)
    (fun {_ _} hmk {_} ht {_} hz ↦ traceTensorEquiv_eq_zero_of_add_ne 𝒜 hε hmk ht hz)
    (fun {_} hpk {_} hz ↦ traceTensorEquiv_comul_eq_zero_of_add_ne 𝒜 hε (by omega) ha hz)

/-- For a Frobenius algebra on an internally `ℤ`-graded algebra, comultiplication is homogeneous
of degree `d` if and only if the counit is homogeneous of degree `-d`. -/
theorem isHomogeneous_comul_iff_isHomogeneous_counit (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
          (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (TauCeti.trivialGrading R R) (-d) :=
  ⟨isHomogeneous_counit_of_comul 𝒜 d, isHomogeneous_comul_of_counit 𝒜 d⟩

/-- If the counit of a Frobenius algebra is homogeneous of degree `-d`, then its handle element
lies in degree `d`. -/
theorem handleElement_mem_grade_of_counit {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d)) :
    handleElement R A ∈ 𝒜 d :=
  handleElement_mem_grade 𝒜 ((isHomogeneous_comul_iff_isHomogeneous_counit 𝒜 d).mpr hε)

end DegreeDuality

end IsFrobenius

end TauCeti.Coalgebra

/-! ### Trace-reconstructed comultiplication and homogeneous dual bases -/

namespace LinearMap

section GradedFrobeniusCoalgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- On an internally `ℤ`-graded commutative algebra, the comultiplication reconstructed from a
perfect trace of degree `-d` is homogeneous of degree `d`. -/
theorem isHomogeneous_frobeniusCoalgebra_comul [Module.Finite R A] [Module.Projective R A]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε 𝒜 (TauCeti.trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous ε.frobeniusCoalgebra.comul 𝒜
      ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition 𝒜)).piece d := by
  let : Coalgebra R A := ε.frobeniusCoalgebra
  have := ε.frobeniusCoalgebra_isFrobenius
  refine (TauCeti.Coalgebra.IsFrobenius.isHomogeneous_comul_iff_isHomogeneous_counit 𝒜 d).mpr ?_
  simpa only [Coalgebra.counit, frobeniusCoalgebra_counit] using hε

/-- On an internally `ℤ`-graded commutative algebra with a perfect trace of degree `-d`, the
trace-dual basis of a finite homogeneous basis `b` with `b i ∈ 𝒜 (deg i)` is homogeneous, with
`traceDualBasis ε b i ∈ 𝒜 (d - deg i)`. -/
theorem traceDualBasis_mem_grade (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε 𝒜 (TauCeti.trivialGrading R R) (-d))
    {ι : Type*} [Finite ι] (b : Module.Basis ι R A) (deg : ι → ℤ)
    (hb : ∀ i, b i ∈ 𝒜 (deg i)) (i : ι) :
    traceDualBasis ε b i ∈ 𝒜 (d - deg i) := by
  have hε_vanish := (TauCeti.isHomogeneous_trivialGrading_iff 𝒜 ε (-d)).mp hε
  exact TauCeti.mem_of_forall_pairing_eq_zero 𝒜 𝒜
    (B := (mul R A).compr₂ ε) ((mul R A).compr₂ ε).toPerfPair.injective (D := d)
    (fun {m k} hmk {_} hx {_} hy ↦
      hε_vanish (m + k) (by omega) _ (SetLike.mul_mem_graded hx hy))
    (fun {k} hk {a} ha ↦ by
      rw [compr₂_apply, mul_apply_apply, traceDualBasis_mul]
      exact b.repr_eq_zero_of_mem_of_ne hb (by omega) ha)

end GradedFrobeniusCoalgebra

end LinearMap

/-! ### Compatibility of comultiplication degree with scalar extension and tensor products -/

namespace TauCeti.Coalgebra.IsFrobenius

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
  [Coalgebra R A] [Coalgebra.IsFrobenius R A]

/-- Scalar extension of a graded Frobenius algebra along a degree-zero `R`-algebra `S` preserves the
degree of comultiplication. -/
theorem isHomogeneous_baseChange_comul {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (TauCeti.trivialGrading R R) (-d)) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := S) (A := S ⊗[R] A))
      (fun p ↦ (𝒜 p).baseChange S)
      ((TauCeti.InternalGrading.ofDecomposition (fun p ↦ (𝒜 p).baseChange S)).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition (fun p ↦ (𝒜 p).baseChange S))).piece d := by
  refine (isHomogeneous_comul_iff_isHomogeneous_counit (fun p ↦ (𝒜 p).baseChange S) d).mpr ?_
  rw [TauCeti.Coalgebra.baseChange_counit S]
  exact TauCeti.isHomogeneous_dualBaseChange S 𝒜 hε

end BaseChange

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Semiring B] [Algebra R B]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] [Coalgebra R A] [Coalgebra.IsFrobenius R A]
  (ℬ : ℤ → Submodule R B) [GradedAlgebra ℬ] [Coalgebra R B] [Coalgebra.IsFrobenius R B]

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
      (((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
        (TauCeti.InternalGrading.ofDecomposition ℬ)).tensorProduct
        ((TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
          (TauCeti.InternalGrading.ofDecomposition ℬ))).piece (d₁ + d₂) := by
  let G := (TauCeti.InternalGrading.ofDecomposition 𝒜).tensorProduct
    (TauCeti.InternalGrading.ofDecomposition ℬ)
  have hcounit : Coalgebra.counit (R := R) (A := A ⊗[R] B) =
      TensorProduct.dualDistrib R A B
        (Coalgebra.counit (R := R) (A := A) ⊗ₜ[R]
          Coalgebra.counit (R := R) (A := B)) :=
    TensorProduct.ext' fun _ _ ↦ by simp [TensorProduct.counit_tmul, mul_comm]
  have hcomul := (isHomogeneous_comul_iff_isHomogeneous_counit G.piece (d₁ + d₂)).mpr (by
    rw [hcounit, neg_add]
    exact TauCeti.isHomogeneous_dualDistrib_tmul 𝒜 ℬ hA hB)
  simpa only [TauCeti.InternalGrading.ofDecomposition_self] using hcomul

end TensorProduct

end TauCeti.Coalgebra.IsFrobenius
