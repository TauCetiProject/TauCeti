/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import TauCeti.Algebra.Algebra.Frobenius.Coalgebra.Transport
public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.Algebra.Module.GradedModule.Dual.TensorProduct
public import TauCeti.Algebra.Module.GradedModule.Trivial

/-!
# Graded Frobenius coalgebras and even-supported gradings

This file develops the degree theory of `ℤ`-graded Frobenius coalgebras and proves its closure
under algebra equivalences, tensor products, and extension of scalars (over both trivially graded
and `ℤ`-graded base algebras).

In TQFT and foam evaluation (such as `𝔰𝔩₂` and `𝔤𝔩_N` link homology), state spaces and local ring
models carry `ℤ`-gradings concentrated in even degrees (`TauCeti.parityGrading 𝒜 1 = ⊥`). On a
Frobenius coalgebra graded by `𝒜`, attaching a handle multiplies by `Coalgebra.handleElem`, so a
counit of degree `-d` corresponds to a coproduct and handle element of degree `d` (with `d = 2 * c`
even whenever `A` is nontrivial and even-supported).

## Main definitions

* `TauCeti.tensorProductGradedAlgebra`: unsigned total-degree `GradedAlgebra` on `A ⊗[R] B`
  (`instance_reducible` so it cannot conflict with `GradedAlgebra.baseChange`).

## Main results

* `TauCeti.parityGrading_trivialGrading_one`,
  `TauCeti.parityGrading_one_eq_bot_iff_of_isHomogeneous_zero`,
  `TauCeti.parityGrading_tensorProduct_one_eq_bot`, `TauCeti.parityGrading_baseChange_one_eq_bot`:
  even support is preserved by trivial gradings, degree-zero equivalences, tensor products, and base
  change.
* `Coalgebra.exists_eq_neg_two_mul_of_parityGrading_one_eq_bot`,
  `Coalgebra.isHomogeneous_counit_of_isHomogeneous_comul`,
  `Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul`: counit-coproduct degree
  duality and evenness of counit degree.
* `Coalgebra.isHomogeneous_handleOp`, `Coalgebra.handleElem_mem_graded`,
  `LinearMap.traceDualBasis_mem_graded`: degrees of handle operator, handle element, and dual bases.
* `TauCeti.InternalGrading.isHomogeneous_tensorTensorTensorComm`,
  `Coalgebra.isHomogeneous_counit_tensorProduct`, `Coalgebra.isHomogeneous_comul_tensorProduct`,
  `Coalgebra.isHomogeneous_counit_baseChange`, `Coalgebra.isHomogeneous_comul_baseChange`,
  `Coalgebra.isHomogeneous_counit_gradedBaseChange`, `Coalgebra.handleElem_gradedBaseChange_mem`.

## References

* F. Goertz, L. Marino, P. Wedrich, *Filtered foams and deformations in link homology*,
  `arXiv:2602.11120v1`, §§2–3.
* M. Khovanov, *Link homology and Frobenius extensions*, Fund. Math. 190 (2006), 179–190.
-/

public section

noncomputable section

open scoped DirectSum TensorProduct

/-! ### Even-supported gradings and unsigned tensor products of graded algebras -/

namespace TauCeti

section EvenSupport

/-- The trivial integer grading is concentrated in degree `0`, hence supported in even degrees. -/
@[simp] theorem parityGrading_trivialGrading_one (R M : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] : parityGrading (trivialGrading R M) 1 = ⊥ :=
  parityGrading_one_eq_bot_iff.mpr fun _ => trivialGrading_eq_bot R M (by omega)

/-- A degree-zero homogeneous linear equivalence transfers vanishing of the odd parity piece from
target to source. -/
theorem parityGrading_one_eq_bot_of_isHomogeneous_zero {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N] [Module S N]
    {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {e : M ≃ₗ[S] N}
    (he : LinearMap.IsHomogeneous e.toLinearMap ℳ 𝒩 0) (hN : parityGrading 𝒩 1 = ⊥) :
    parityGrading ℳ 1 = ⊥ := by
  rw [parityGrading_one_eq_bot_iff] at hN ⊢
  refine fun k => (Submodule.eq_bot_iff _).mpr fun x hx => e.injective ?_
  have hex : e x ∈ 𝒩 (2 * k + 1) := by simpa using he.map_mem hx
  simpa [hN k] using hex

/-- Even support (`parityGrading · 1 = ⊥`) is invariant under degree-zero homogeneous linear
equivalences of internally graded modules. -/
theorem parityGrading_one_eq_bot_iff_of_isHomogeneous_zero {R S M N : Type*}
    [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
    [AddCommMonoid N] [Module R N] [Module S N]
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {e : M ≃ₗ[S] N}
    (he : LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) :
    parityGrading G.piece 1 = ⊥ ↔ parityGrading H.piece 1 = ⊥ :=
  ⟨parityGrading_one_eq_bot_of_isHomogeneous_zero he.linearEquiv_symm,
    parityGrading_one_eq_bot_of_isHomogeneous_zero he⟩

/-- The tensor product of two even-supported internally `ℤ`-graded modules is even-supported. -/
theorem parityGrading_tensorProduct_one_eq_bot {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}
    (hG : parityGrading G.piece 1 = ⊥) (hH : parityGrading H.piece 1 = ⊥) :
    parityGrading (G.tensorProduct H).piece 1 = ⊥ :=
  parityGrading_one_eq_bot_iff.mpr fun k => le_bot_iff.mp <|
    G.tensorProduct_piece_le H fun p x hx y hy => by
      rcases Int.even_or_odd p with ⟨m, rfl⟩ | hp
      · rw [eq_bot_of_parityGrading_one_eq_bot hH ⟨k - m, by ring⟩, Submodule.mem_bot] at hy
        simp [hy]
      · rw [eq_bot_of_parityGrading_one_eq_bot hG hp, Submodule.mem_bot] at hx; simp [hx]

/-- Base change preserves even support of an integer-indexed family of submodules. -/
theorem parityGrading_baseChange_one_eq_bot {R S M : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] {ℳ : ℤ → Submodule R M}
    (h : parityGrading ℳ 1 = ⊥) : parityGrading (fun i : ℤ => (ℳ i).baseChange S) 1 = ⊥ := by
  rw [parityGrading_one_eq_bot_iff] at h ⊢; intro k; simp [h k]

end EvenSupport

/-- Membership in `InternalGrading.dualPiece q` is equivalent to homogeneity of degree `q` into the
trivial grading of the base ring. -/
theorem InternalGrading.mem_dualPiece_iff_isHomogeneous_trivialGrading {R M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] (G : InternalGrading R M ℤ) (q : ℤ)
    (φ : Module.Dual R M) :
    φ ∈ G.dualPiece q ↔ LinearMap.IsHomogeneous φ G.piece (trivialGrading R R) q := by
  rw [G.mem_dualPiece_iff, LinearMap.isHomogeneous_def]
  refine ⟨fun hφ p x hx => (mem_trivialGrading_iff R R).mpr ?_, fun hφ p x hx hp =>
    ((mem_trivialGrading_iff R R).mp (hφ p x hx)).resolve_left (by omega)⟩
  exact if hp : p + q = 0 then Or.inl hp else Or.inr (hφ p x hx (by omega))

/-- Multiplication on a `ℤ`-graded `R`-algebra is homogeneous of degree `0` from the total-degree
tensor-product grading to `𝒜`. -/
theorem isHomogeneous_mul' {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] :
    LinearMap.IsHomogeneous (_root_.LinearMap.mul' R A)
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece 𝒜 0 := by
  let G := InternalGrading.ofDecomposition 𝒜
  refine LinearMap.isHomogeneous_def.mpr fun n z hz => ?_
  rw [add_zero]
  refine G.tensorProduct_piece_le G (C := (𝒜 n).comap (_root_.LinearMap.mul' R A))
    (fun p x hx y hy => ?_) hz
  rw [InternalGrading.ofDecomposition_piece] at hx hy
  exact (show p + (n - p) = n by omega) ▸ SetLike.mul_mem_graded hx hy

private theorem mul_mem_tensorProduct_ofDecomposition {R A B : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    {i j : ℤ} {z₁ z₂ : A ⊗[R] B}
    (hz₁ : z₁ ∈ ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece i)
    (hz₂ : z₂ ∈ ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece j) :
    z₁ * z₂ ∈ ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece (i + j) := by
  let GA := InternalGrading.ofDecomposition 𝒜; let GB := InternalGrading.ofDecomposition ℬ
  refine GA.tensorProduct_piece_le GB
    (C := ((GA.tensorProduct GB).piece (i + j)).comap (_root_.LinearMap.mulRight R z₂))
    (fun p a₁ ha₁ b₁ hb₁ => GA.tensorProduct_piece_le GB
      (C := ((GA.tensorProduct GB).piece (i + j)).comap
        (_root_.LinearMap.mulLeft R (a₁ ⊗ₜ[R] b₁))) (fun q a₂ ha₂ b₂ hb₂ => ?_) hz₂) hz₁
  rw [InternalGrading.ofDecomposition_piece] at ha₁ ha₂ hb₁ hb₂
  rw [Submodule.mem_comap, _root_.LinearMap.mulLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
    show i + j = (p + q) + ((i - p) + (j - q)) by ring]
  exact GA.tmul_mem_tensorProduct GB (by simpa [GA] using SetLike.mul_mem_graded ha₁ ha₂)
    (by simpa [GB] using SetLike.mul_mem_graded hb₁ hb₂)

/-- The total-degree grading turns the ordinary tensor product `A ⊗[R] B` of two `ℤ`-graded
`R`-algebras into a `ℤ`-graded `R`-algebra (`instance_reducible` rather than a global instance so
it cannot form an instance diamond with `GradedAlgebra.baseChange`). -/
@[instance_reducible]
def tensorProductGradedAlgebra {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    GradedAlgebra (((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ)).piece) :=
  let GA := InternalGrading.ofDecomposition 𝒜; let GB := InternalGrading.ofDecomposition ℬ
  { one_mem := by
      change (1 : A) ⊗ₜ[R] (1 : B) ∈ (GA.tensorProduct GB).piece (0 + 0)
      exact GA.tmul_mem_tensorProduct GB (by simpa [GA] using SetLike.one_mem_graded 𝒜)
        (by simpa [GB] using SetLike.one_mem_graded ℬ)
    mul_mem := fun _ _ _ _ => mul_mem_tensorProduct_ofDecomposition 𝒜 ℬ
    decompose' := DirectSum.decompose (GA.tensorProduct GB).piece
    left_inv := DirectSum.Decomposition.left_inv
    right_inv := DirectSum.Decomposition.right_inv }

/-- The fourfold tensor-product interchange `tensorTensorTensorComm` is homogeneous of degree `0`
with respect to total-degree tensor-product gradings. -/
theorem InternalGrading.isHomogeneous_tensorTensorTensorComm {R A B : Type*} [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ) :
    LinearMap.IsHomogeneous
      (_root_.TensorProduct.tensorTensorTensorComm R A A B B).toLinearMap
      ((GA.tensorProduct GA).tensorProduct (GB.tensorProduct GB)).piece
      ((GA.tensorProduct GB).tensorProduct (GA.tensorProduct GB)).piece 0 := by
  refine LinearMap.isHomogeneous_def.mpr fun n z hz => ?_; rw [add_zero]
  let target := ((GA.tensorProduct GB).tensorProduct (GA.tensorProduct GB)).piece n
  refine (GA.tensorProduct GA).tensorProduct_piece_le (GB.tensorProduct GB)
    (C := target.comap (_root_.TensorProduct.tensorTensorTensorComm R A A B B).toLinearMap)
    (fun p t₁ ht₁ t₂ ht₂ => GA.tensorProduct_piece_le GA
      (C := target.comap ((_root_.TensorProduct.tensorTensorTensorComm R A A B B).toLinearMap ∘ₗ
        (_root_.TensorProduct.mk R (A ⊗[R] A) (B ⊗[R] B)).flip t₂))
      (fun q a₁ ha₁ a₂ ha₂ => GB.tensorProduct_piece_le GB
        (C := target.comap ((_root_.TensorProduct.tensorTensorTensorComm R A A B B).toLinearMap ∘ₗ
          _root_.TensorProduct.mk R (A ⊗[R] A) (B ⊗[R] B) (a₁ ⊗ₜ[R] a₂)))
        (fun r b₁ hb₁ b₂ hb₂ => ?_) ht₂) ht₁) hz
  change (a₁ ⊗ₜ[R] b₁) ⊗ₜ[R] (a₂ ⊗ₜ[R] b₂) ∈ target
  rw [show target = ((GA.tensorProduct GB).tensorProduct (GA.tensorProduct GB)).piece
    ((q + r) + ((p - q) + (n - p - r))) by dsimp [target]; congr 1; ring]
  exact (GA.tensorProduct GB).tmul_mem_tensorProduct (GA.tensorProduct GB)
    (GA.tmul_mem_tensorProduct GB ha₁ hb₁) (GA.tmul_mem_tensorProduct GB ha₂ hb₂)

end TauCeti

/-! ### Degree parity and counit-coproduct degree duality -/

section GradedCoalgebra

open TauCeti

/-- On a nontrivial internally `ℤ`-graded coalgebra supported in even degrees, any homogeneous
degree `d` of the counit is even (`d = -2 * c`). -/
theorem Coalgebra.exists_eq_neg_two_mul_of_parityGrading_one_eq_bot {R A : Type*}
    [CommSemiring R] [AddCommMonoid A] [Nontrivial A] [Module R A] [Coalgebra R A]
    (G : InternalGrading R A ℤ) (hparity : parityGrading G.piece 1 = ⊥) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) G.piece
      (trivialGrading R R) d) : ∃ c : ℤ, d = -2 * c := by
  by_contra hd
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have hzero : (Coalgebra.counit (R := R) (A := A)) = 0 := G.linearMap_ext fun p x hx => by
    by_cases hp : p + d = 0
    · have hodd : Odd p := Int.not_even_iff_odd.mp fun ⟨c, hc⟩ => hd ⟨c, by omega⟩
      rw [eq_bot_of_parityGrading_one_eq_bot hparity hodd, Submodule.mem_bot] at hx; simp [hx]
    · exact ((mem_trivialGrading_iff R R).mp (hε.map_mem hx)).resolve_left hp
  have h := congrArg (_root_.TensorProduct.lid R A) (Coalgebra.rTensor_counit_comul (R := R) a)
  exact ha (by simpa [hzero] using h.symm)

private theorem rid_lTensor_counitPiece_comul {R A : Type*}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    (G : InternalGrading R A ℤ) {d p : ℤ} {a : A}
    (hΔa : Coalgebra.comul (R := R) a ∈ (G.tensorProduct G).piece (p + d))
    (ε₀ : Module.Dual R A)
    (hε₀_eq : ∀ {y : A}, y ∈ G.piece d → ε₀ y = Coalgebra.counit (R := R) y)
    (hε₀_zero : ∀ {r : ℤ} {y : A}, y ∈ G.piece r → r ≠ d → ε₀ y = 0) (ha : a ∈ G.piece p) :
    ((_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε₀.lTensor A)
      (Coalgebra.comul (R := R) a) = a := by
  let ε : Module.Dual R A := Coalgebra.counit
  let g₁ : A ⊗[R] A →ₗ[R] A := (_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε₀.lTensor A
  let proj : A →ₗ[R] A := (G.piece p).subtype ∘ₗ DirectSum.component R ℤ (fun q => G.piece q) p ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap
  let g₂ : A ⊗[R] A →ₗ[R] A := proj ∘ₗ (_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε.lTensor A
  have hle : (G.tensorProduct G).piece (p + d) ≤ LinearMap.eqLocus g₁ g₂ :=
    G.tensorProduct_piece_le G fun q u hu v hv => by
      change ε₀ v • u = (DirectSum.decompose G.piece (ε v • u) p : A)
      by_cases hqp : q = p
      · subst hqp; rw [hε₀_eq (by simpa using hv),
          DirectSum.decompose_of_mem_same G.piece ((G.piece q).smul_mem (ε v) hu)]
      · rw [hε₀_zero hv (by omega), zero_smul,
          DirectSum.decompose_of_mem_ne G.piece ((G.piece q).smul_mem (ε v) hu) hqp]
  refine (hle hΔa).trans ?_
  simp only [g₂, proj, LinearMap.comp_apply, LinearEquiv.coe_coe, ε,
    Coalgebra.lTensor_counit_comul, _root_.TensorProduct.rid_tmul, one_smul]
  exact DirectSum.decompose_of_mem_same G.piece ha

/-- On any internally `ℤ`-graded coalgebra, if `comul` is homogeneous of degree `d`, then `counit`
is homogeneous of degree `-d`. -/
theorem Coalgebra.isHomogeneous_counit_of_isHomogeneous_comul {R A : Type*}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    (G : InternalGrading R A ℤ) {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) G.piece
      (G.tensorProduct G).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) G.piece
      (trivialGrading R R) (-d) := by
  let ε : Module.Dual R A := Coalgebra.counit
  let ε₀sub : G.dualPiece (-d) := (G.dualPieceEquiv (-d)).symm (ε ∘ₗ (G.piece (- -d)).subtype)
  let ε₀ : Module.Dual R A := ε₀sub
  have hε₀_eq {y : A} (hy : y ∈ G.piece d) : ε₀ y = ε y := by
    simpa [ε₀, ε₀sub] using G.dualPieceEquiv_symm_apply_coe (-d)
      (ε ∘ₗ (G.piece (- -d)).subtype) ⟨y, by simpa using hy⟩
  have hε₀_zero {r : ℤ} {y : A} (hy : y ∈ G.piece r) (hr : r ≠ d) : ε₀ y = 0 :=
    (G.mem_dualPiece_iff (-d) ε₀).mp ε₀sub.2 r y hy (by omega)
  let g₁ : A ⊗[R] A →ₗ[R] A := (_root_.TensorProduct.rid R A).toLinearMap ∘ₗ ε₀.lTensor A
  have hconv : ε ∘ₗ g₁ = ε₀ ∘ₗ (_root_.TensorProduct.lid R A).toLinearMap ∘ₗ ε.rTensor A :=
    TensorProduct.ext' fun _ _ => by simp [g₁, mul_comm]
  have hε_eq : ε = ε₀ := G.linearMap_ext fun p a ha => by
    have hc := LinearMap.congr_fun hconv (Coalgebra.comul (R := R) a)
    rw [LinearMap.comp_apply, show g₁ (Coalgebra.comul (R := R) a) = a from
      rid_lTensor_counitPiece_comul G (hΔ.map_mem ha) ε₀ hε₀_eq hε₀_zero ha] at hc
    simpa [ε, Coalgebra.rTensor_counit_comul] using hc
  rw [← G.mem_dualPiece_iff_isHomogeneous_trivialGrading, show Coalgebra.counit = ε from rfl, hε_eq]
  exact ε₀sub.2

private def lidCounitMulLeft {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [CoalgebraStruct R A] : A →ₗ[R] A ⊗[R] A →ₗ[R] A where
  toFun a := (_root_.TensorProduct.lid R A).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) ∘ₗ _root_.LinearMap.mulLeft R a).rTensor A
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp [add_mul, add_smul]
  map_smul' _ _ := TensorProduct.ext' fun _ _ => by simp [mul_smul]

private theorem isHomogeneous_lidCounitMulLeft {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] [CoalgebraStruct R A] {d p : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) (-d)) {a : A} (ha : a ∈ 𝒜 p) :
    TauCeti.LinearMap.IsHomogeneous (lidCounitMulLeft (R := R) a)
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece 𝒜 (p - d) := by
  let G := InternalGrading.ofDecomposition 𝒜
  refine TauCeti.LinearMap.isHomogeneous_def.mpr fun m z hz =>
    G.tensorProduct_piece_le G (C := (𝒜 (m + (p - d))).comap (lidCounitMulLeft (R := R) a))
      (fun q u hu v hv => ?_) hz
  rw [InternalGrading.ofDecomposition_piece] at hu hv
  simp only [Submodule.mem_comap, lidCounitMulLeft, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    _root_.LinearMap.mulLeft_apply, _root_.TensorProduct.lid_tmul]
  by_cases hpq : p + q + -d = 0
  · exact (show m - q = m + (p - d) by omega) ▸
      (𝒜 (m - q)).smul_mem (Coalgebra.counit (R := R) (a * u)) hv
  · simp [((mem_trivialGrading_iff R R).mp (hε.map_mem (SetLike.mul_mem_graded ha hu))).resolve_left
      hpq]

/-- On a `ℤ`-graded Frobenius coalgebra whose counit has degree `-d`, the Casimir tensor
`comul 1` has total degree `d`. -/
theorem Coalgebra.IsFrobenius.comul_one_mem_graded {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) (-d)) :
    Coalgebra.comul (R := R) (1 : A) ∈
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d := by
  classical
  let G := InternalGrading.ofDecomposition 𝒜
  let f : A →ₗ[R] A ⊗[R] A →ₗ[R] A := lidCounitMulLeft (R := R)
  let c := Coalgebra.comul (R := R) (1 : A)
  change c ∈ (G.tensorProduct G).piece d
  rw [← DirectSum.sum_support_decompose (G.tensorProduct G).piece c]
  refine Submodule.sum_mem _ fun n hn => ?_
  by_cases hnd : n = d
  · exact hnd ▸ (DirectSum.decompose (G.tensorProduct G).piece c n).2
  · exfalso; apply DFinsupp.mem_support_iff.mp hn; ext
    refine tensor_eq_of_forall_lid_rTensor_counit_mulLeft fun a => ?_
    let zn : A ⊗[R] A := DirectSum.decompose (G.tensorProduct G).piece c n
    have hF : f.flip zn = 0 := G.linearMap_ext fun p b hb => by
      have hb' : b ∈ 𝒜 p := by simpa [G] using hb
      have hdecomp := (isHomogeneous_lidCounitMulLeft 𝒜 hε hb').map_decompose n c
      change f.flip zn b = (DirectSum.decompose 𝒜 (f b c) (n + (p - d)) : A) at hdecomp
      have hf1 : f b c = b := by
        simpa [f, c, lidCounitMulLeft] using lid_rTensor_counit_mulLeft_comul (R := R) b 1
      rw [LinearMap.zero_apply, hdecomp, hf1, DirectSum.decompose_of_mem_ne 𝒜 hb' (by omega)]
    simpa [f, lidCounitMulLeft, zn] using DFunLike.congr_fun hF a

/-- **Degree duality for graded Frobenius coalgebras**: on a `ℤ`-graded Frobenius coalgebra `A`
(without commutativity or projectivity assumptions on `A`), the counit has degree `-d` if and only
if the coproduct has degree `d`. -/
theorem Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (trivialGrading R R) (-d) ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece d := by
  let G := InternalGrading.ofDecomposition 𝒜
  refine ⟨fun hε => TauCeti.LinearMap.isHomogeneous_def.mpr fun p a ha => ?_, fun hΔ => ?_⟩
  · rw [comul_eq_rTensor_mulLeft_comul_one]
    have hmulLeft : TauCeti.LinearMap.IsHomogeneous (_root_.LinearMap.mulLeft R a) G.piece G.piece
        p := TauCeti.LinearMap.isHomogeneous_def.mpr fun q x hx => by
      rw [InternalGrading.ofDecomposition_piece] at hx ⊢
      exact add_comm p q ▸ SetLike.mul_mem_graded ha hx
    have hrTensor : TauCeti.LinearMap.IsHomogeneous ((_root_.LinearMap.mulLeft R a).rTensor A)
        (G.tensorProduct G).piece (G.tensorProduct G).piece p := by
      simpa [LinearMap.rTensor] using
        hmulLeft.tensorProduct (TauCeti.LinearMap.isHomogeneous_id G.piece)
    simpa [add_comm] using hrTensor.map_mem (comul_one_mem_graded 𝒜 hε)
  · simpa [G] using Coalgebra.isHomogeneous_counit_of_isHomogeneous_comul G (by simpa [G] using hΔ)

/-- `InternalGrading` form of `Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul`,
stated directly with `(G.tensorProduct G).piece`. -/
theorem Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul_piece {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] (G : InternalGrading R A ℤ) [GradedAlgebra G.piece]
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) G.piece
        (trivialGrading R R) (-d) ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) G.piece
        (G.tensorProduct G).piece d := by
  convert isHomogeneous_counit_iff_isHomogeneous_comul G.piece d using 3
  congr 2 <;> refine InternalGrading.ext fun p => ?_ <;> rw [InternalGrading.ofDecomposition_piece]

/-- Even-degree specialization (`-2 * c` and `2 * c`) of
`Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul`. -/
theorem Coalgebra.IsFrobenius.isHomogeneous_counit_neg_two_mul_iff_isHomogeneous_comul_two_mul
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A)
    [GradedAlgebra 𝒜] [Coalgebra R A] [Coalgebra.IsFrobenius R A] (c : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (trivialGrading R R) (-2 * c) ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece (2 * c) := by
  simpa [neg_mul] using isHomogeneous_counit_iff_isHomogeneous_comul 𝒜 (2 * c)

/-- For the Frobenius coalgebra reconstructed from a perfect trace `ε` on a finite projective
commutative graded `R`-algebra, `ε` has degree `-d` if and only if the reconstructed coproduct has
degree `d`. -/
theorem LinearMap.isHomogeneous_frobeniusCoalgebra_comul_iff {R A : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] [Module.Finite R A] [Module.Projective R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]
    (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (letI := ε.frobeniusCoalgebra; Coalgebra.comul (R := R)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece d ↔
      TauCeti.LinearMap.IsHomogeneous ε 𝒜 (trivialGrading R R) (-d) := by
  let := ε.frobeniusCoalgebra; have := ε.frobeniusCoalgebra_isFrobenius
  rw [← Coalgebra.IsFrobenius.isHomogeneous_counit_iff_isHomogeneous_comul,
    ε.frobeniusCoalgebra_counit]

/-! ### Degrees of the handle operator, handle element, and trace-dual basis -/

/-- When the coproduct of a `ℤ`-graded `R`-algebra `A` is homogeneous of degree `d`, the handle
operator `Coalgebra.handleOp R A` is homogeneous of degree `d`. -/
theorem Coalgebra.isHomogeneous_handleOp {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.handleOp R A) 𝒜 𝒜 d :=
  TauCeti.LinearMap.isHomogeneous_def.mpr fun _ _ ha => by
    simpa [Coalgebra.handleOp_apply] using (TauCeti.isHomogeneous_mul' 𝒜).map_mem (hΔ.map_mem ha)

/-- When the coproduct of a `ℤ`-graded `R`-algebra `A` is homogeneous of degree `d`, the handle
element `Coalgebra.handleElem R A` lies in `𝒜 d`. -/
theorem Coalgebra.handleElem_mem_graded {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d) : Coalgebra.handleElem R A ∈ 𝒜 d := by
  simpa [← Coalgebra.handleOp_one] using
    (Coalgebra.isHomogeneous_handleOp 𝒜 hΔ).map_mem (SetLike.one_mem_graded 𝒜)

/-- On a `ℤ`-graded Frobenius coalgebra whose counit has degree `-d`, the handle element lies in
`𝒜 d`, and its `g`-th power lies in `𝒜 (g • d)`. -/
theorem Coalgebra.IsFrobenius.handleElem_pow_mem_graded {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    [Coalgebra R A] [Coalgebra.IsFrobenius R A] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) (-d)) (g : ℕ) : Coalgebra.handleElem R A ^ g ∈ 𝒜 (g • d) :=
  SetLike.pow_mem_graded g
    (Coalgebra.handleElem_mem_graded 𝒜 ((isHomogeneous_counit_iff_isHomogeneous_comul 𝒜 d).mp hε))

/-- If `ε : A →ₗ[R] R` is a homogeneous perfect trace of degree `-d` and `b` is a homogeneous
basis with `b i ∈ 𝒜 (deg i)`, then the `i`-th trace-dual basis element lies in `𝒜 (d - deg i)`. -/
theorem LinearMap.traceDualBasis_mem_graded {R A ι : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair] [Finite ι]
    (b : Module.Basis ι R A) {deg : ι → ℤ} (hb : ∀ i, b i ∈ 𝒜 (deg i)) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous ε 𝒜 (trivialGrading R R) (-d)) (i : ι) :
    ε.traceDualBasis b i ∈ 𝒜 (d - deg i) := by
  classical
  let w := ε.traceDualBasis b i
  suffices hw : w = DirectSum.decompose 𝒜 w (d - deg i) by
    rw [show ε.traceDualBasis b i = w from rfl, hw]; exact (DirectSum.decompose 𝒜 w (d - deg i)).2
  refine ((mul R A).compr₂ ε).toPerfPair.injective (b.ext fun j => ?_)
  simp only [toPerfPair_apply, compr₂_apply, mul_apply_apply]
  have hkill {q : ℤ} {x : A} (hx : x ∈ 𝒜 q) (hq : q ≠ d - deg j) : ε (x * b j) = 0 :=
    ((mem_trivialGrading_iff R R).mp
      (hε.map_mem (SetLike.mul_mem_graded hx (hb j)))).resolve_left (by omega)
  by_cases hij : deg j = deg i
  · conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 w]
    rw [Finset.sum_mul, map_sum, Finset.sum_eq_single (d - deg i)]
    · exact fun q _ hq => hkill (DirectSum.decompose 𝒜 w q).2 (by omega)
    · intro hnotMem
      rw [DFinsupp.notMem_support_iff.mp hnotMem, ZeroMemClass.coe_zero, zero_mul, map_zero]
  · rw [show w * b j = ε.traceDualBasis b i * b j from rfl, ε.traceDualBasis_mul,
      b.repr_self_apply, ite_eq_right (fun h : j = i => hij (h ▸ rfl)),
      hkill (DirectSum.decompose 𝒜 w (d - deg i)).2 (by omega)]

end GradedCoalgebra

/-! ### Compatibility with graded equivalences, tensor products, and scalar extensions -/

section Compatibility

open TauCeti

/-- A counit-preserving degree-zero algebra equivalence preserves homogeneity of the counit at any
degree `d`. -/
theorem AlgEquiv.isHomogeneous_counit_iff {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (e : A ≃ₐ[R] B) (he_hom : TauCeti.LinearMap.IsHomogeneous e.toLinearMap 𝒜 ℬ 0)
    (he_counit : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
        (trivialGrading R R) d ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := B)) ℬ
        (trivialGrading R R) d := by
  have he_equiv : TauCeti.LinearMap.IsHomogeneous e.toLinearEquiv.toLinearMap
      (InternalGrading.ofDecomposition 𝒜).piece (InternalGrading.ofDecomposition ℬ).piece 0 := by
    simpa using he_hom
  have hsymm : TauCeti.LinearMap.IsHomogeneous e.toLinearEquiv.symm.toLinearMap ℬ 𝒜 0 := by
    simpa using he_equiv.linearEquiv_symm
  simp only [TauCeti.LinearMap.isHomogeneous_def]
  refine ⟨fun hA p b hb => ?_, fun hB p a ha => ?_⟩
  · simpa [← he_counit (e.symm b)] using hA p (e.symm b) (by simpa using hsymm.map_mem hb)
  · simpa [he_counit a] using hB p (e a) (by simpa using he_hom.map_mem ha)

/-- A counit-preserving degree-zero algebra equivalence between Frobenius coalgebras with internal
`ℤ`-gradings preserves homogeneity of the coproduct at any degree `d`. -/
theorem AlgEquiv.isHomogeneous_comul_iff {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] [Coalgebra R A] [Coalgebra R B]
    [Coalgebra.IsFrobenius R A] [Coalgebra.IsFrobenius R B]
    (e : A ≃ₐ[R] B) (he_hom : TauCeti.LinearMap.IsHomogeneous e.toLinearMap 𝒜 ℬ 0)
    (he_counit : ∀ a, Coalgebra.counit (R := R) (e a) = Coalgebra.counit (R := R) a) (d : ℤ) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
        ((InternalGrading.ofDecomposition 𝒜).tensorProduct
          (InternalGrading.ofDecomposition 𝒜)).piece d ↔
      TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := B)) ℬ
        ((InternalGrading.ofDecomposition ℬ).tensorProduct
          (InternalGrading.ofDecomposition ℬ)).piece d := by
  let GA := InternalGrading.ofDecomposition 𝒜; let GB := InternalGrading.ofDecomposition ℬ
  let ec := e.toFrobeniusCoalgEquiv he_counit
  have he_GA : TauCeti.LinearMap.IsHomogeneous e.toLinearEquiv.toLinearMap GA.piece GB.piece 0 := by
    simpa [GA, GB] using he_hom
  have hsymm : TauCeti.LinearMap.IsHomogeneous e.symm.toLinearMap GB.piece GA.piece 0 :=
    he_GA.linearEquiv_symm
  have hcoe : LinearMap.ofClass ec = e.toLinearMap := by ext; simp [ec]
  have hcoe_symm : LinearMap.ofClass ec.symm = e.symm.toLinearMap := by ext; simp [ec]
  have hB_eq : Coalgebra.comul (R := R) (A := B) =
      _root_.TensorProduct.map e.toLinearMap e.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := A) ∘ₗ e.symm.toLinearMap := LinearMap.ext fun b => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hcoe, CoalgHomClass.map_comp_comul_apply]
    simp [ec]
  have hA_eq : Coalgebra.comul (R := R) (A := A) =
      _root_.TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := B) ∘ₗ e.toLinearMap := LinearMap.ext fun a => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hcoe_symm, CoalgHomClass.map_comp_comul_apply]
    simp [ec]
  refine ⟨fun hA => ?_, fun hB => ?_⟩
  · have hA' : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) GA.piece
        (GA.tensorProduct GA).piece d := by simpa [GA] using hA
    rw [hB_eq]; simpa [GB] using (he_GA.tensorProduct he_GA).comp (hA'.comp hsymm)
  · have hB' : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := B)) GB.piece
        (GB.tensorProduct GB).piece d := by simpa [GB] using hB
    rw [hA_eq]; simpa [GA] using (hsymm.tensorProduct hsymm).comp (hB'.comp he_GA)

/-- On a tensor product `A ⊗[R] B` of internally `ℤ`-graded coalgebras, homogeneous counits of
degrees `dA` and `dB` tensor to a homogeneous counit of degree `dA + dB`. -/
theorem Coalgebra.isHomogeneous_counit_tensorProduct {R A B : Type*} [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ) {dA dB : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) GA.piece
      (trivialGrading R R) dA)
    (hB : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := B)) GB.piece
      (trivialGrading R R) dB) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A ⊗[R] B))
      (GA.tensorProduct GB).piece (trivialGrading R R) (dA + dB) := by
  rw [← (GA.tensorProduct GB).mem_dualPiece_iff_isHomogeneous_trivialGrading,
    TensorProduct.counit_eq_dualDistrib]
  exact GA.dualDistrib_tmul_mem_dualPiece GB
    ((GA.mem_dualPiece_iff_isHomogeneous_trivialGrading dA _).mpr hA)
    ((GB.mem_dualPiece_iff_isHomogeneous_trivialGrading dB _).mpr hB)

/-- On a tensor product `A ⊗[R] B` of internally `ℤ`-graded coalgebras, homogeneous coproducts of
degrees `dA` and `dB` tensor to a homogeneous coproduct of degree `dA + dB`. -/
theorem Coalgebra.isHomogeneous_comul_tensorProduct {R A B : Type*} [CommSemiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B]
    (GA : InternalGrading R A ℤ) (GB : InternalGrading R B ℤ) {dA dB : ℤ}
    (hA : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) GA.piece
      (GA.tensorProduct GA).piece dA)
    (hB : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := B)) GB.piece
      (GB.tensorProduct GB).piece dB) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A ⊗[R] B))
      (GA.tensorProduct GB).piece
      ((GA.tensorProduct GB).tensorProduct (GA.tensorProduct GB)).piece (dA + dB) := by
  have hdef : Coalgebra.comul (R := R) (A := A ⊗[R] B) =
      (TensorProduct.tensorTensorTensorComm R A A B B).toLinearMap ∘ₗ
        _root_.TensorProduct.map (Coalgebra.comul (R := R) (A := A))
          (Coalgebra.comul (R := R) (A := B)) := TensorProduct.ext' fun _ _ => rfl
  rw [hdef]; simpa using (GA.isHomogeneous_tensorTensorTensorComm GB).comp (hA.tensorProduct hB)

/-- Extending scalars from `R` to a trivially graded commutative `R`-algebra `S` preserves
homogeneity of the counit for `GradedAlgebra.baseChange`. -/
theorem Coalgebra.isHomogeneous_counit_baseChange {R S A : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
    (𝒜 : ℤ → Submodule R A) {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := S) (A := S ⊗[R] A))
      (fun i : ℤ => (𝒜 i).baseChange S) (trivialGrading S S) d :=
  TauCeti.LinearMap.isHomogeneous_def.mpr fun p z hz => by
    by_cases hp : p + d = 0
    · simp [hp]
    · refine (mem_trivialGrading_iff S S).mpr <| Or.inr <|
        (show (𝒜 p).baseChange S ≤ LinearMap.ker (Coalgebra.counit (R := S) (A := S ⊗[R] A)) by
          rw [Submodule.baseChange_eq_span, Submodule.span_le]
          rintro - ⟨a, ha, rfl⟩
          simp [LinearMap.mem_ker, TensorProduct.counit_baseChange_eq_dualBaseChange,
            ((mem_trivialGrading_iff R R).mp (hε.map_mem ha)).resolve_left hp]) hz

/-- Extending scalars of a `ℤ`-graded `R`-algebra-coalgebra `A` from `R` to a trivially graded
commutative `R`-algebra `S` preserves homogeneity of the coproduct for
`GradedAlgebra.baseChange`. -/
theorem Coalgebra.isHomogeneous_comul_baseChange {R S A : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [Semiring A] [Algebra R A]
    (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] [CoalgebraStruct R A] {d : ℤ}
    (hΔ : TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := R) (A := A)) 𝒜
      ((InternalGrading.ofDecomposition 𝒜).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d) :
    TauCeti.LinearMap.IsHomogeneous (Coalgebra.comul (R := S) (A := S ⊗[R] A))
      (fun i : ℤ => (𝒜 i).baseChange S)
      ((InternalGrading.ofDecomposition (fun i : ℤ => (𝒜 i).baseChange S)).tensorProduct
        (InternalGrading.ofDecomposition (fun i : ℤ => (𝒜 i).baseChange S))).piece d := by
  let GA := InternalGrading.ofDecomposition 𝒜
  let GSA := InternalGrading.ofDecomposition (fun i : ℤ => (𝒜 i).baseChange S)
  let φ : A ⊗[R] A →ₗ[R] (S ⊗[R] A) ⊗[S] (S ⊗[R] A) :=
    ((_root_.TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A
      A).toLinearMap.restrictScalars R) ∘ₗ
      _root_.TensorProduct.mk R (S ⊗[S] S) (A ⊗[R] A) ((1 : S) ⊗ₜ[S] (1 : S))
  refine TauCeti.LinearMap.isHomogeneous_def.mpr fun n z hz => ?_
  let target := (GSA.tensorProduct GSA).piece (n + d)
  refine (show (𝒜 n).baseChange S ≤ target.comap (Coalgebra.comul (R := S) (A := S ⊗[R] A)) from ?_)
    hz
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro - ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, _root_.TensorProduct.mk_apply,
    TensorProduct.comul_tmul, CommSemiring.comul_apply]
  refine GA.tensorProduct_piece_le GA (C := (target.restrictScalars R).comap φ)
    (fun p a₁ ha₁ a₂ ha₂ => ?_) (hΔ.map_mem ha)
  rw [InternalGrading.ofDecomposition_piece] at ha₁ ha₂
  have h1 : (1 : S) ⊗ₜ[R] a₁ ∈ GSA.piece p := by
    simpa [GSA] using Submodule.tmul_mem_baseChange_of_mem (1 : S) ha₁
  have h2 : (1 : S) ⊗ₜ[R] a₂ ∈ GSA.piece (n + d - p) := by
    simpa [GSA] using Submodule.tmul_mem_baseChange_of_mem (1 : S) ha₂
  simpa [φ, target] using GSA.tmul_mem_tensorProduct GSA h1 h2

/-- Extending scalars along a `ℤ`-graded commutative `R`-algebra `S` (such as a polynomial ground
ring `R[h]` in equivariant foam evaluation): if the counit of `A` has degree `d` into
`trivialGrading R R`, then the `S`-linear counit of `S ⊗[R] A` is homogeneous of degree `d` from the
total-degree grading of `S ⊗[R] A` into `𝒮`. -/
theorem Coalgebra.isHomogeneous_counit_gradedBaseChange {R S A : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
    (𝒮 : ℤ → Submodule R S) [DirectSum.Decomposition 𝒮]
    (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜] {d : ℤ}
    (hε : TauCeti.LinearMap.IsHomogeneous (Coalgebra.counit (R := R) (A := A)) 𝒜
      (trivialGrading R R) d) :
    TauCeti.LinearMap.IsHomogeneous
      ((Coalgebra.counit (R := S) (A := S ⊗[R] A)).restrictScalars R)
      ((InternalGrading.ofDecomposition 𝒮).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece 𝒮 d := by
  let GS := InternalGrading.ofDecomposition 𝒮; let GA := InternalGrading.ofDecomposition 𝒜
  refine TauCeti.LinearMap.isHomogeneous_def.mpr fun n z hz =>
    GS.tensorProduct_piece_le GA
      (C := (𝒮 (n + d)).comap ((Coalgebra.counit (R := S) (A := S ⊗[R] A)).restrictScalars R))
      (fun p s hs a ha => ?_) hz
  rw [InternalGrading.ofDecomposition_piece] at hs ha
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply,
    TensorProduct.counit_baseChange_eq_dualBaseChange, Module.Dual.baseChange_apply_tmul]
  by_cases hqd : n - p + d = 0
  · exact (show p = n + d by omega) ▸ (𝒮 p).smul_mem (Coalgebra.counit (R := R) a) hs
  · simp [((mem_trivialGrading_iff R R).mp (hε.map_mem ha)).resolve_left hqd]

/-- On `S ⊗[R] A` over a `ℤ`-graded commutative `R`-algebra `S`, if `Coalgebra.handleElem R A` lies
in `𝒜 d`, then `Coalgebra.handleElem S (S ⊗[R] A)` has total degree `d` in
`(GS.tensorProduct GA).piece`. -/
theorem Coalgebra.handleElem_gradedBaseChange_mem {R S A : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [NonAssocSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A]
    (𝒮 : ℤ → Submodule R S) [GradedAlgebra 𝒮]
    (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜] {d : ℤ}
    (hh : Coalgebra.handleElem R A ∈ 𝒜 d) :
    Coalgebra.handleElem S (S ⊗[R] A) ∈
      ((InternalGrading.ofDecomposition 𝒮).tensorProduct
        (InternalGrading.ofDecomposition 𝒜)).piece d := by
  rw [Coalgebra.handleElem_baseChange]
  simpa using (InternalGrading.ofDecomposition 𝒮).tmul_mem_tensorProduct
    (InternalGrading.ofDecomposition 𝒜) (p := 0) (q := d)
    (by simpa using SetLike.one_mem_graded 𝒮) (by simpa using hh)

end Compatibility
