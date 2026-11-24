/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
-- Non-public: `forall_conj_eq_iff_exists_scalar_mul_eq` is used only in a proof.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Inner automorphisms of a matrix algebra

An invertible matrix `g ∈ GL n R` over a commutative semiring acts on the matrix algebra
`Matrix n n R` by the algebra automorphism `x ↦ g x g⁻¹`. This file packages that action as a
group homomorphism `GL n R →* (Matrix n n R ≃ₐ[R] Matrix n n R)` and proves:

* over a commutative ring, its kernel is the center of `GL n R`, the invertible scalar matrices, so
  the conjugating matrix is unique up to an invertible scalar;
* every algebra endomorphism `σ` of `Matrix n n R` is Zariski-locally inner: there are finitely
  many elements of the commutative semiring `R` generating the unit ideal such that, after mapping
  to a commutative semiring in which one of them is invertible, `σ` becomes inner;
* hence over a local semiring, in particular over a field, every algebra endomorphism of a matrix
  algebra is inner, hence an automorphism (Skolem–Noether);
* hence it induces an injective homomorphism from Mathlib's projective general linear group
  `PGL(n, R) = GL n R / Z(GL n R)`, which is bijective over a local ring.

These are the pointwise facts behind the identification of the projective general linear group
scheme with the automorphism group scheme of the matrix algebra, and of that group scheme with the
fppf quotient of `GLₙ` by its center.

## Main declarations

* `Matrix.GeneralLinearGroup.innerAut`: conjugation as algebra automorphisms.
* `Matrix.GeneralLinearGroup.ker_innerAut`: its kernel is the center.
* `Matrix.GeneralLinearGroup.innerAut_eq_innerAut_iff`: the conjugating matrix is unique up to an
  invertible scalar.
* `AlgHom.exists_span_eq_top_forall_map_eq_innerAut`: endomorphisms are Zariski-locally inner.
* `AlgHom.exists_innerAut_eq_of_isLocalRing`: every algebra endomorphism of a matrix algebra over
  a local semiring is inner, and in particular bijective
  (`AlgHom.bijective_of_isLocalRing_of_matrix`).
* `Matrix.GeneralLinearGroup.innerAut_surjective`: surjectivity over a local ring.
* `Matrix.ProjGenLinGroup.innerAut`: the induced homomorphism on `PGL(n, R)`, with
  `Matrix.ProjGenLinGroup.innerAut_injective` and `Matrix.ProjGenLinGroup.innerAut_bijective`.

## Implementation notes

Write `Eᵢⱼ` for the matrix units and fix an index `b`. For each `a`, the matrices
`Gₐ = ∑ⱼ σ(Eⱼₐ) Eᵦⱼ` and `Hₐ = ∑ⱼ Eⱼᵦ σ(Eₐⱼ)` satisfy `σ(x) Gₐ = Gₐ x` and `Hₐ Gₐ = σ(Eₐₐ)ᵦᵦ`, a
scalar. Since the `Eₐₐ` sum to `1`, these scalars sum to `1` over `a`, so they generate the unit
ideal. Wherever `σ(Eₐₐ)ᵦᵦ` is invertible, `Gₐ` is invertible and conjugates `x` to `σ(x)`. Over a
local semiring one of these scalars is already a unit.

## References

* M.-A. Knus, M. Ojanguren, *Théorie de la descente et algèbres d'Azumaya*, Lecture Notes in
  Mathematics 389, Chapter IV, for the Skolem–Noether theorem over local rings and the local
  innerness of automorphisms of Azumaya algebras.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation by an invertible matrix, `x ↦ g x g⁻¹`, as an algebra automorphism of the matrix
algebra. -/
noncomputable def innerAut [CommSemiring R] : GL n R →* (Matrix n n R ≃ₐ[R] Matrix n n R) :=
  (MulSemiringAction.toAlgAut (ConjAct (GL n R)) R (Matrix n n R)).comp
    ConjAct.toConjAct.toMonoidHom

/-- The inner automorphism by `g` sends `x` to `g x g⁻¹`. -/
@[simp]
theorem innerAut_apply [CommSemiring R] (g : GL n R) (x : Matrix n n R) :
    innerAut g x = (g : Matrix n n R) * x * (g⁻¹ : GL n R) := by
  simp [innerAut, ConjAct.units_smul_def]

/-- Conjugation by an invertible scalar matrix is the identity algebra automorphism. -/
@[simp]
theorem innerAut_scalar [CommSemiring R] (a : Rˣ) : innerAut (scalar n a) = 1 := by
  ext X i j
  rw [innerAut_apply, ← map_inv (scalar n) a, coe_scalar, coe_scalar]
  simp only [scalar_apply, mul_diagonal, diagonal_mul, AlgEquiv.one_apply]
  rw [mul_right_comm, Units.mul_inv, one_mul]

variable [CommRing R]

/-- **An inner automorphism of a matrix algebra is trivial exactly when the conjugating matrix is
central**, that is, an invertible scalar matrix. -/
theorem innerAut_eq_one_iff (g : GL n R) :
    innerAut g = 1 ↔ g ∈ Subgroup.center (GL n R) := by
  -- Both sides say that `g` commutes with every matrix.
  rw [mem_center_iff_val_mem_range_scalar, ← center_eq_range, Semigroup.mem_center_iff,
    AlgEquiv.ext_iff]
  refine forall_congr' fun x => ?_
  rw [innerAut_apply, AlgEquiv.one_apply, Units.mul_inv_eq_iff_eq_mul, eq_comm]

/-- The kernel of conjugation is the center of the general linear group. -/
@[simp]
theorem ker_innerAut : (innerAut (n := n) (R := R)).ker = Subgroup.center (GL n R) :=
  Subgroup.ext fun g => MonoidHom.mem_ker.trans (innerAut_eq_one_iff g)

/-- **The conjugating matrix is unique up to a unit**: two invertible matrices induce the same
inner automorphism exactly when they differ by an invertible scalar. -/
theorem innerAut_eq_innerAut_iff {g g' : GL n R} :
    innerAut g = innerAut g' ↔ ∃ u : Rˣ, g' = g * scalar n u := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- Equal inner automorphisms conjugate every element of `GL n R` in the same way.
    obtain ⟨u, hu⟩ := (forall_conj_eq_iff_exists_scalar_mul_eq (g := g') (h := g)).1
      fun x ↦ Units.ext (by simpa using (DFunLike.congr_fun h (x : Matrix n n R)).symm)
    exact ⟨u, by rw [← hu, scalar_commute]⟩
  · rintro ⟨u, rfl⟩
    rw [map_mul, innerAut_scalar, mul_one]

section LocallyInner

variable {A : Type*} [CommSemiring A]

/-- The matrix `∑ⱼ σ(Eⱼₐ) Eᵦⱼ`, which intertwines an endomorphism `σ` of `Mₙ(A)` with the
identity: `σ x * G = G * x`. -/
private def intertwiner (σ : Matrix n n A →ₐ[A] Matrix n n A) (a b : n) : Matrix n n A :=
  ∑ j, σ (single j a 1) * single b j 1

/-- The matrix `∑ⱼ Eⱼᵦ σ(Eₐⱼ)`, a left inverse of the intertwiner up to the scalar `σ(Eₐₐ)ᵦᵦ`. -/
private def coIntertwiner (σ : Matrix n n A →ₐ[A] Matrix n n A) (a b : n) : Matrix n n A :=
  ∑ j, single j b 1 * σ (single a j 1)

private theorem apply_mul_intertwiner (σ : Matrix n n A →ₐ[A] Matrix n n A) (a b : n)
    (x : Matrix n n A) : σ x * intertwiner σ a b = intertwiner σ a b * x := by
  induction x using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => rw [map_add, add_mul, mul_add, hp, hq]
  | h_std_basis k l c =>
    rw [← mul_one c, ← smul_eq_mul c 1, ← smul_single, map_smul, smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [intertwiner, Finset.mul_sum, Finset.sum_mul, ← mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single l (fun j _ hj => by simp [Ne.symm hj]) (by simp),
      Finset.sum_eq_single k (fun j _ hj => by simp [mul_assoc, hj]) (by simp)]
    simp [mul_assoc]

/-- `Hₐ Gₐ` is the scalar matrix `σ(Eₐₐ)ᵦᵦ`. -/
private theorem coIntertwiner_mul_intertwiner (σ : Matrix n n A →ₐ[A] Matrix n n A) (a b : n) :
    coIntertwiner σ a b * intertwiner σ a b = Matrix.scalar n (σ (single a a 1) b b) := by
  -- `σ(Eₐⱼ) σ(Eₖₐ) = σ(Eₐⱼ Eₖₐ)` vanishes unless `j = k`, when it is `σ(Eₐₐ)`.
  have h (j k : n) (X : Matrix n n A) : σ (single a j 1) * (σ (single k a 1) * X) =
      if j = k then σ (single a a 1) * X else 0 := by
    rw [← mul_assoc, ← map_mul]
    split_ifs with hjk
    · rw [hjk, single_mul_single_same, mul_one]
    · rw [single_mul_single_of_ne (h := hjk), map_zero, zero_mul]
  simp only [coIntertwiner, intertwiner, Finset.sum_mul, Finset.mul_sum, mul_assoc, h, mul_ite,
    mul_zero]
  simp only [← mul_assoc, single_mul_mul_single, one_mul, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact sum_single_eq_diagonal _

end LocallyInner

end Matrix.GeneralLinearGroup

namespace AlgHom

universe w

variable {n A : Type*} [Fintype n] [DecidableEq n] [CommSemiring A]

open Matrix Matrix.GeneralLinearGroup in
/-- **Endomorphisms of a matrix algebra are Zariski-locally inner.** For an algebra endomorphism
`σ` of `Mₙ(A)` over a commutative semiring `A`, there are finitely many elements of `A` generating
the unit ideal such that, along any homomorphism `φ : A →+* B` to a commutative semiring
inverting one of them, `σ` becomes conjugation by an invertible matrix over `B`:
`(σ x).map φ = g (x.map φ) g⁻¹` for every `x`.

Over a local semiring one of the elements is already a unit, which gives
`AlgHom.exists_innerAut_eq_of_isLocalRing`. -/
theorem exists_span_eq_top_forall_map_eq_innerAut (σ : Matrix n n A →ₐ[A] Matrix n n A) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧ ∀ c ∈ s, ∀ {B : Type w} [CommSemiring B]
      (φ : A →+* B), IsUnit (φ c) →
        ∃ g : GL n B, ∀ x : Matrix n n A, (σ x).map φ = innerAut g (x.map φ) := by
  classical
  cases isEmpty_or_nonempty n
  · exact ⟨{1}, by simp, fun _ _ _ _ _ _ => ⟨1, fun _ => Subsingleton.elim _ _⟩⟩
  obtain ⟨b⟩ := ‹Nonempty n›
  have hsum : ∑ a, σ (single a a 1) b b = 1 := by
    rw [← Matrix.sum_apply, ← map_sum, sum_single_one, map_one, one_apply_eq]
  refine ⟨Finset.univ.image fun a => σ (single a a 1) b b, ?_, ?_⟩
  · have h := Ideal.sum_mem (Ideal.span (Finset.univ.image fun a => σ (single a a 1) b b : Set A))
      (t := Finset.univ) (f := fun a => σ (single a a 1) b b) fun a _ => Ideal.subset_span (by simp)
    rwa [hsum, ← Ideal.eq_top_iff_one] at h
  · intro c hc B _ φ hu
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨u, hu⟩ := hu
    let G := (intertwiner σ a b).map φ
    let K := ((u⁻¹ : Bˣ) : B) • (coIntertwiner σ a b).map φ
    have h₁ : K * G = 1 := by
      rw [smul_mul_assoc, ← Matrix.map_mul, coIntertwiner_mul_intertwiner]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, ← hu, hij]
    have h₂ : G * K = 1 := mul_eq_one_comm.1 h₁
    refine ⟨⟨G, K, h₂, h₁⟩, fun x => ?_⟩
    have hx := congrArg (·.map φ) (apply_mul_intertwiner σ a b x)
    simp only [Matrix.map_mul] at hx
    rw [innerAut_apply]
    calc (σ x).map φ = (σ x).map φ * (G * K) := by rw [h₂, Matrix.mul_one]
      _ = G * x.map φ * K := by rw [← Matrix.mul_assoc, hx]

open Matrix.GeneralLinearGroup in
/-- **Endomorphisms of a matrix algebra over a local semiring are inner**: every unital algebra
endomorphism `σ` of `Mₙ(K)`, for `K` a commutative local semiring, is conjugation by an invertible
matrix. -/
theorem exists_innerAut_eq_of_isLocalRing {K : Type*} [CommSemiring K] [IsLocalRing K]
    (σ : Matrix n n K →ₐ[K] Matrix n n K) :
    ∃ g : GL n K, (innerAut g : Matrix n n K →ₐ[K] Matrix n n K) = σ := by
  obtain ⟨s, hs, h⟩ := σ.exists_span_eq_top_forall_map_eq_innerAut
  obtain ⟨c, hc, hu⟩ : ∃ c ∈ s, IsUnit c := by
    by_contra! hne
    refine (IsLocalRing.maximalIdeal.isMaximal K).ne_top (top_le_iff.1 (hs ▸ ?_))
    exact Ideal.span_le.2 fun c hc => (IsLocalRing.mem_maximalIdeal c).2 (hne c hc)
  obtain ⟨g, hg⟩ := h c hc (RingHom.id K) hu
  exact ⟨g, AlgHom.ext fun x => by simpa using (hg x).symm⟩

/-- An endomorphism of a matrix algebra over a local semiring is bijective. -/
theorem bijective_of_isLocalRing_of_matrix {K : Type*} [CommSemiring K] [IsLocalRing K]
    (σ : Matrix n n K →ₐ[K] Matrix n n K) : Function.Bijective σ := by
  obtain ⟨g, hg⟩ := σ.exists_innerAut_eq_of_isLocalRing
  rw [← hg]
  exact (Matrix.GeneralLinearGroup.innerAut g).bijective

end AlgHom

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Skolem–Noether for matrix algebras over a local semiring**: every algebra automorphism of a
matrix algebra over a commutative local semiring, in particular over a field, is inner. -/
theorem innerAut_surjective (K : Type*) [CommSemiring K] [IsLocalRing K] :
    Function.Surjective (innerAut (n := n) (R := K)) := fun σ =>
  let ⟨g, hg⟩ := σ.toAlgHom.exists_innerAut_eq_of_isLocalRing
  ⟨g, AlgEquiv.ext fun x => DFunLike.congr_fun hg x⟩

end Matrix.GeneralLinearGroup

namespace AlgEquiv

variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix.GeneralLinearGroup in
/-- Two algebra isomorphisms from an algebra onto a matrix algebra over a local semiring, in
particular over a field, differ by conjugation by an invertible matrix (Skolem–Noether). -/
theorem exists_forall_eq_mul_mul_inv {K : Type*} [CommSemiring K] [IsLocalRing K] {A : Type*}
    [Semiring A] [Algebra K A] (e e' : A ≃ₐ[K] Matrix n n K) :
    ∃ g : GL n K, ∀ x : A,
      e' x = (g : Matrix n n K) * e x * (g⁻¹ : GL n K) := by
  obtain ⟨g, hg⟩ := innerAut_surjective K (e.symm.trans e')
  exact ⟨g, fun x => by simpa using (congrArg (fun τ => τ (e x)) hg).symm⟩

end AlgEquiv

namespace Matrix.ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Conjugation induces a homomorphism from the projective general linear group
`PGL(n, R) = GL n R / Z(GL n R)` to the automorphism group of the matrix algebra. -/
noncomputable def innerAut : ProjGenLinGroup n R →* (Matrix n n R ≃ₐ[R] Matrix n n R) :=
  QuotientGroup.lift (Subgroup.center (GL n R)) GeneralLinearGroup.innerAut
    GeneralLinearGroup.ker_innerAut.ge

/-- On the class of `g`, the induced homomorphism is the inner automorphism by `g`. -/
@[simp]
theorem innerAut_mk (g : GL n R) : innerAut (mk g) = GeneralLinearGroup.innerAut g :=
  (rfl)

/-- `PGL(n, R)` acts faithfully on the matrix algebra by conjugation. -/
theorem innerAut_injective : Function.Injective (innerAut (n := n) (R := R)) :=
  (QuotientGroup.injective_lift_iff _ _ _).2 GeneralLinearGroup.ker_innerAut.symm

/-- Over a local ring, in particular over a field, `PGL(n, K)` is the automorphism group of the
matrix algebra. -/
theorem innerAut_bijective (K : Type*) [CommRing K] [IsLocalRing K] :
    Function.Bijective (innerAut (n := n) (R := K)) :=
  ⟨innerAut_injective, QuotientGroup.lift_surjective_of_surjective _ _
    (GeneralLinearGroup.innerAut_surjective K) _⟩

end Matrix.ProjGenLinGroup
