/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Inner automorphisms of a matrix algebra

An invertible matrix `g ∈ GL n R` over a commutative semiring acts on the matrix algebra
`Matrix n n R` by the algebra automorphism `x ↦ g x g⁻¹`. This file packages that action as a
group homomorphism `GL n R →* (Matrix n n R ≃ₐ[R] Matrix n n R)` and proves:

* over a commutative ring, its kernel is the center of `GL n R`, the invertible scalar matrices;
* every algebra automorphism `σ` of `Matrix n n R` is Zariski-locally inner: there are finitely
  many elements of the commutative semiring `R` generating the unit ideal such that, after mapping
  to a commutative semiring in which one of them is invertible, `σ` becomes inner;
* hence over a local semiring, in particular over a field, every automorphism of a matrix algebra is
  inner (Skolem–Noether);
* hence it induces an injective homomorphism from Mathlib's projective general linear group
  `PGL(n, R) = GL n R / Z(GL n R)`, which is bijective over a local ring.

These are the pointwise facts behind the identification of the projective general linear group
scheme with the automorphism group scheme of the matrix algebra, and of that group scheme with the
fppf quotient of `GLₙ` by its center.

## Main declarations

* `Matrix.GeneralLinearGroup.innerAut`: conjugation as algebra automorphisms.
* `Matrix.GeneralLinearGroup.ker_innerAut`: its kernel is the center.
* `AlgEquiv.exists_span_eq_top_forall_map_eq_innerAut`: automorphisms are Zariski-locally inner.
* `Matrix.GeneralLinearGroup.innerAut_surjective`: surjectivity over a local ring.
* `Matrix.ProjGenLinGroup.innerAut`: the induced homomorphism on `PGL(n, R)`, with
  `Matrix.ProjGenLinGroup.innerAut_injective` and `Matrix.ProjGenLinGroup.innerAut_bijective`.

## Implementation notes

Write `Eᵢⱼ` for the matrix units and fix an index `a`. For each `b`, the matrices
`Gᵦ = ∑ⱼ σ(Eⱼₐ) Eᵦⱼ` and `Hᵦ = ∑ⱼ Eⱼᵦ σ(Eₐⱼ)` satisfy `σ(x) Gᵦ = Gᵦ x` and `x Hᵦ = Hᵦ σ(x)`.
Hence `Gᵦ Hᵦ` commutes with every matrix, so it is a scalar `cᵦ`, and `∑ᵦ Gᵦ Hᵦ = 1` gives
`∑ᵦ cᵦ = 1`. Wherever `cᵦ` is invertible, `Gᵦ` is invertible and conjugates `x` to `σ(x)`.

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

variable [CommRing R]

/-- **An inner automorphism of a matrix algebra is trivial exactly when the conjugating matrix is
central**, that is, an invertible scalar matrix. -/
theorem innerAut_eq_one_iff (g : GL n R) :
    innerAut g = 1 ↔ g ∈ Subgroup.center (GL n R) := by
  have key : innerAut g = 1 ↔ ∀ x : Matrix n n R, (g : Matrix n n R) * x = x * g := by
    rw [AlgEquiv.ext_iff]
    refine forall_congr' fun x => ?_
    rw [innerAut_apply, AlgEquiv.one_apply, Units.mul_inv_eq_iff_eq_mul]
  rw [key]
  constructor
  · exact fun h => Subgroup.mem_center_iff.mpr fun h' => Units.ext (h h').symm
  · intro hg x
    obtain ⟨a, ha⟩ := mem_center_iff_val_mem_range_scalar.mp hg
    rw [← ha]
    exact (Matrix.scalar_commute a (fun _ => Commute.all _ _) x).eq

/-- The kernel of conjugation is the center of the general linear group. -/
@[simp]
theorem ker_innerAut : (innerAut (n := n) (R := R)).ker = Subgroup.center (GL n R) := by
  ext g
  exact innerAut_eq_one_iff g

section LocallyInner

variable {A : Type*} [CommSemiring A]

/-- The matrix `∑ⱼ σ(Eⱼₐ) Eᵦⱼ`, which intertwines an automorphism `σ` of `Mₙ(A)` with the
identity: `σ x * G = G * x`. -/
private def intertwiner (σ : Matrix n n A ≃ₐ[A] Matrix n n A) (a b : n) : Matrix n n A :=
  ∑ j, σ (single j a 1) * single b j 1

/-- The matrix `∑ⱼ Eⱼᵦ σ(Eₐⱼ)`, which intertwines the identity with `σ`: `x * H = H * σ x`. -/
private def coIntertwiner (σ : Matrix n n A ≃ₐ[A] Matrix n n A) (a b : n) : Matrix n n A :=
  ∑ j, single j b 1 * σ (single a j 1)

private theorem apply_mul_intertwiner (σ : Matrix n n A ≃ₐ[A] Matrix n n A) (a b : n)
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

private theorem mul_coIntertwiner (σ : Matrix n n A ≃ₐ[A] Matrix n n A) (a b : n)
    (x : Matrix n n A) : x * coIntertwiner σ a b = coIntertwiner σ a b * σ x := by
  induction x using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => rw [map_add, add_mul, mul_add, hp, hq]
  | h_std_basis k l c =>
    rw [← mul_one c, ← smul_eq_mul c 1, ← smul_single, map_smul, smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [coIntertwiner, Finset.mul_sum, Finset.sum_mul, mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single l (fun j _ hj => by simp [← mul_assoc, Ne.symm hj]) (by simp),
      Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp [← mul_assoc]

private theorem sum_intertwiner_mul_coIntertwiner (σ : Matrix n n A ≃ₐ[A] Matrix n n A) (a : n) :
    ∑ b, intertwiner σ a b * coIntertwiner σ a b = 1 := by
  have key (j l : n) : ∑ b, single b j (1 : A) * single l b 1 = if j = l then 1 else 0 := by
    split_ifs with h
    · subst h
      simp [sum_single_one]
    · simp [h]
  calc ∑ b, intertwiner σ a b * coIntertwiner σ a b
      = ∑ l, ∑ j, σ (single j a 1) * (∑ b, single b j 1 * single l b 1) * σ (single a l 1) := by
        simp only [intertwiner, coIntertwiner, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        conv_lhs => rw [Finset.sum_comm]
    _ = σ (∑ j, single j j 1) := by
        simp only [key, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_sum, ← map_mul, single_mul_single_same]
    _ = 1 := by rw [sum_single_one, map_one]

end LocallyInner

end Matrix.GeneralLinearGroup

namespace AlgEquiv

universe w

variable {n A : Type*} [Fintype n] [DecidableEq n] [CommSemiring A]

open Matrix.GeneralLinearGroup in
/-- **Automorphisms of a matrix algebra are Zariski-locally inner.** For an algebra automorphism
`σ` of `Mₙ(A)` over a commutative semiring `A`, there are finitely many elements of `A` generating
the unit ideal such that, along any homomorphism `φ : A →+* B` to a commutative semiring
inverting one of them, `σ` becomes conjugation by an invertible matrix over `B`:
`(σ x).map φ = g (x.map φ) g⁻¹` for every `x`.

Over a local semiring one of the elements is already a unit, which gives
`Matrix.GeneralLinearGroup.innerAut_surjective`. -/
theorem exists_span_eq_top_forall_map_eq_innerAut (σ : Matrix n n A ≃ₐ[A] Matrix n n A) :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧ ∀ c ∈ s, ∀ {B : Type w} [CommSemiring B]
      (φ : A →+* B), IsUnit (φ c) →
        ∃ g : GL n B, ∀ x : Matrix n n A, (σ x).map φ = innerAut g (x.map φ) := by
  classical
  cases isEmpty_or_nonempty n
  · exact ⟨{1}, by simp, fun _ _ _ _ _ _ => ⟨1, fun _ => Subsingleton.elim _ _⟩⟩
  obtain ⟨a⟩ := ‹Nonempty n›
  have hscalar (b : n) : intertwiner σ a b * coIntertwiner σ a b =
      scalar n ((intertwiner σ a b * coIntertwiner σ a b) a a) := by
    obtain ⟨r, hr⟩ := mem_range_scalar_of_commute_single
      (M := intertwiner σ a b * coIntertwiner σ a b) fun i j _ => by
        obtain ⟨x, hx⟩ := σ.surjective (single i j 1)
        rw [← hx, Commute, SemiconjBy, ← mul_assoc, apply_mul_intertwiner, mul_assoc,
          mul_coIntertwiner, mul_assoc]
    rw [← hr]
    simp
  have hsum : ∑ b, (intertwiner σ a b * coIntertwiner σ a b) a a = 1 := by
    rw [← Matrix.sum_apply, sum_intertwiner_mul_coIntertwiner, one_apply_eq]
  refine ⟨Finset.univ.image fun b => (intertwiner σ a b * coIntertwiner σ a b) a a, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun b _ => Ideal.subset_span (by simp)
  · intro c hc B _ φ hu
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨u, hu⟩ := hu
    let G := (intertwiner σ a b).map φ
    let K := ((u⁻¹ : Bˣ) : B) • (coIntertwiner σ a b).map φ
    have h₁ : G * K = 1 := by
      rw [mul_smul_comm, ← Matrix.map_mul, hscalar b]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, ← hu, hij]
    have h₂ : K * G = 1 := mul_eq_one_comm.1 h₁
    refine ⟨⟨G, K, h₁, h₂⟩, fun x => ?_⟩
    have hx := congrArg (·.map φ) (apply_mul_intertwiner σ a b x)
    simp only [Matrix.map_mul] at hx
    rw [innerAut_apply]
    calc (σ x).map φ = (σ x).map φ * (G * K) := by rw [h₁, Matrix.mul_one]
      _ = G * x.map φ * K := by rw [← Matrix.mul_assoc, hx]

end AlgEquiv

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Skolem–Noether for matrix algebras over a local semiring**: every algebra automorphism of a
matrix algebra over a commutative local semiring, in particular over a field, is inner. -/
theorem innerAut_surjective (K : Type*) [CommSemiring K] [IsLocalRing K] :
    Function.Surjective (innerAut (n := n) (R := K)) := by
  intro σ
  obtain ⟨s, hs, h⟩ := σ.exists_span_eq_top_forall_map_eq_innerAut
  obtain ⟨c, hc, hu⟩ : ∃ c ∈ s, IsUnit c := by
    by_contra! hne
    refine (IsLocalRing.maximalIdeal.isMaximal K).ne_top (top_le_iff.1 (hs ▸ ?_))
    exact Ideal.span_le.2 fun c hc => (IsLocalRing.mem_maximalIdeal c).2 (hne c hc)
  obtain ⟨g, hg⟩ := h c hc (RingHom.id K) hu
  exact ⟨g, AlgEquiv.ext fun x => by simpa using (hg x).symm⟩

end Matrix.GeneralLinearGroup

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
