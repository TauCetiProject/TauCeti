/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Basic
import TauCeti.Algebra.CharP.Invertible

/-!
# The parity grading and supercommutativity of the parity signed algebra

For an internal `ZMod 2`-grading `G` of an `R`-module `V`, the parity-`i` piece
`TauCeti.paritySignedSymPiece G i` of `TauCeti.ParitySignedSym G` is spanned by products of
homogeneous generators whose parities sum to `i`. These pieces form an internal `ZMod 2`-grading of
`ParitySignedSym G`, making it a graded `R`-algebra with parity-preserving universal property and
homogeneous supercommutativity `a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)` over any commutative ring
(with odd homogeneous squares vanishing when `2` is invertible).

For an internal integer grading `H` of `V`, the presentation equivalence
`TauCeti.SignedSym.parityEquiv H` identifies `TauCeti.parityGrading (TauCeti.signedSymPiece H)`
piece by piece with `paritySignedSymPiece H.parity`. In particular, the parity reduction of an
element of integer input degree `p` lies in `paritySignedSymPiece H.parity p`. Taking
`H = G.ofParity` and rewriting along `G.parity_ofParity` transports internality and
supercommutativity from the integer-graded theory to an arbitrary parity-graded module `G`, without
choosing an integer lift in the statement.

## Main definitions

* `TauCeti.paritySignedSymPiece`: the parity-`i` piece of `ParitySignedSym G`.
* `TauCeti.ParitySignedSym.gradedLift` and `TauCeti.ParitySignedSym.gradedMap`: the `ZMod 2`-graded
  universal property and functoriality.
* `TauCeti.SignedSym.toParityGraded` and `TauCeti.SignedSym.fromParityGraded`: the mutually inverse
  `ZMod 2`-graded algebra maps underlying `SignedSym.parityEquiv`.

## Main results

* `TauCeti.SignedSym.parityGrading_signedSymPiece_map_parityEquiv` and
  `TauCeti.SignedSym.parityEquiv_mem_paritySignedSymPiece_iff`: `SignedSym.parityEquiv H`
  identifies the coarsened integer grading with `paritySignedSymPiece H.parity`.
* `TauCeti.SignedSym.parityEquiv_mem_of_mem_signedSymPiece`: an element of integer degree `p` maps
  into the piece of parity `p` modulo two.
* `TauCeti.isInternal_paritySignedSymPiece` and `GradedAlgebra (paritySignedSymPiece G)`.
* `TauCeti.ParitySignedSym.mul_eq_uzpow_smul_mul`, `TauCeti.ParitySignedSym.sq_eq_neg`, and
  `TauCeti.ParitySignedSym.sq_eq_zero`: homogeneous supercommutativity and odd-square vanishing.
* `TauCeti.ParitySignedSym.congr_mem_paritySignedSymPiece_iff` and
  `TauCeti.ParitySignedSym.paritySignedSymPiece_map_congr`: parity-piece transport along
  `ParitySignedSym.congr`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
* Homogeneous-word induction, the graded universal property (`gradedLift`, `gradedMap`), and the
  odd-square consequences adapt the integer-graded development in
  `TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Grading` and
  `TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Supercommutativity`.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

/-! ### Homogeneous parity pieces -/

/-- The parity-`i` piece of `ParitySignedSym G`, spanned by products of homogeneous generators
whose parities sum to `i`. The empty word gives `1` in parity `0`. -/
noncomputable def paritySignedSymPiece (G : InternalGrading R V (ZMod 2)) (i : ZMod 2) :
    Submodule R (ParitySignedSym G) :=
  Submodule.span R {a | ∃ (n : ℕ) (d : Fin n → ZMod 2) (x : Fin n → V),
    (∀ k, x k ∈ G.piece (d k)) ∧ ∑ k, d k = i ∧
      a = (List.ofFn fun k ↦ ParitySignedSym.generator G (x k)).prod}

variable (G : InternalGrading R V (ZMod 2))

/-- Explicit span description of `paritySignedSymPiece G i`. -/
theorem paritySignedSymPiece_eq_span (i : ZMod 2) :
    paritySignedSymPiece G i = Submodule.span R
      {a | ∃ (n : ℕ) (d : Fin n → ZMod 2) (x : Fin n → V),
        (∀ k, x k ∈ G.piece (d k)) ∧ ∑ k, d k = i ∧
          a = (List.ofFn fun k ↦ ParitySignedSym.generator G (x k)).prod} := (rfl)

/-- A product of homogeneous generators lies in the piece of the sum of their parities. -/
theorem list_prod_generator_mem_paritySignedSymPiece {n : ℕ} (d : Fin n → ZMod 2)
    (x : Fin n → V) (hx : ∀ k, x k ∈ G.piece (d k)) :
    (List.ofFn fun k ↦ ParitySignedSym.generator G (x k)).prod ∈
      paritySignedSymPiece G (∑ k, d k) :=
  Submodule.subset_span ⟨n, d, x, hx, rfl, rfl⟩

/-- The image of a homogeneous tensor word lies in the piece of the sum of its letter parities. -/
theorem quotient_tprod_mem_paritySignedSymPiece {n : ℕ} (d : Fin n → ZMod 2)
    (x : Fin n → V) (hx : ∀ k, x k ∈ G.piece (d k)) :
    ParitySignedSym.quotient G (TensorAlgebra.tprod R V n x) ∈
      paritySignedSymPiece G (∑ k, d k) := by
  rw [ParitySignedSym.quotient_tprod]
  exact list_prod_generator_mem_paritySignedSymPiece G d x hx

/-- A homogeneous generator retains its parity in `ParitySignedSym G`. -/
theorem generator_mem_paritySignedSymPiece {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    ParitySignedSym.generator G x ∈ paritySignedSymPiece G i := by
  simpa using list_prod_generator_mem_paritySignedSymPiece G (fun _ : Fin 1 ↦ i)
    (fun _ : Fin 1 ↦ x) fun _ ↦ hx

namespace ParitySignedSym

/-- Induction on homogeneous elements of `ParitySignedSym G`, tracking parity. -/
@[elab_as_elim]
theorem homogeneous_induction {P : ZMod 2 → ParitySignedSym G → Prop}
    (one : P 0 1)
    (generator : ∀ (i : ZMod 2) (x : V), x ∈ G.piece i → P i (ParitySignedSym.generator G x))
    (mul : ∀ (i j : ZMod 2) (a b : ParitySignedSym G), P i a → P j b → P (i + j) (a * b))
    (zero : ∀ i, P i 0)
    (add : ∀ (i : ZMod 2) (a b : ParitySignedSym G), P i a → P i b → P i (a + b))
    (smul : ∀ (i : ZMod 2) (r : R) (a : ParitySignedSym G), P i a → P i (r • a))
    {i : ZMod 2} {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G i) : P i a := by
  rw [paritySignedSymPiece_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, d, x, hx, rfl, rfl⟩ := ha
    induction n with
    | zero => simpa using one
    | succ n ih =>
      simpa only [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons] using
        mul (d 0) (∑ k : Fin n, d k.succ) _ _ (generator _ _ (hx 0))
          (ih (fun k ↦ d k.succ) (fun k ↦ x k.succ) fun k ↦ hx k.succ)
  | zero => exact zero i
  | add a b _ _ ha hb => exact add i a b ha hb
  | smul r a _ ha => exact smul i r a ha

private theorem generator_mul_mem_paritySignedSymPiece {i j : ZMod 2} {x : V} (hx : x ∈ G.piece i)
    {b : ParitySignedSym G} (hb : b ∈ paritySignedSymPiece G j) :
    generator G x * b ∈ paritySignedSymPiece G (i + j) := by
  rw [paritySignedSymPiece_eq_span] at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨n, d, y, hy, rfl, rfl⟩ := hb
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, List.prod_cons]
      using list_prod_generator_mem_paritySignedSymPiece G (Fin.cons i d) (Fin.cons x y)
        (Fin.cons hx hy)
  | zero => simp
  | add u v _ _ hu hv =>
    rw [mul_add]
    exact add_mem hu hv
  | smul r u _ hu =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hu

end ParitySignedSym

/-- Multiplication in `ParitySignedSym G` adds parities. -/
instance : SetLike.GradedMonoid (paritySignedSymPiece G) where
  one_mem := by
    simpa using list_prod_generator_mem_paritySignedSymPiece G
      (fun k : Fin 0 ↦ k.elim0) (fun k : Fin 0 ↦ k.elim0) fun k ↦ k.elim0
  mul_mem i j a b ha hb :=
    ParitySignedSym.homogeneous_induction G
      (P := fun k c ↦ ∀ {l : ZMod 2} {w : ParitySignedSym G},
        w ∈ paritySignedSymPiece G l → c * w ∈ paritySignedSymPiece G (k + l))
      (fun hw ↦ by simpa using hw)
      (fun _ _ hx _ _ hw ↦ ParitySignedSym.generator_mul_mem_paritySignedSymPiece G hx hw)
      (fun k m u v hu hv {l w} hw ↦ by
        rw [mul_assoc, add_assoc]
        exact hu (hv hw))
      (fun _ _ _ _ ↦ by simp)
      (fun _ _ _ hu hv _ _ hw ↦ by rw [add_mul]; exact add_mem (hu hw) (hv hw))
      (fun _ r _ hu _ _ hw ↦ by rw [smul_mul_assoc]; exact Submodule.smul_mem _ r (hu hw))
      ha hb

/-! ### Comparison with the coarsened integer grading -/

namespace SignedSym

variable (H : InternalGrading R V ℤ)

/-- `SignedSym.parityEquiv H` maps each parity piece of `signedSymPiece H` onto the corresponding
native parity piece of `ParitySignedSym H.parity`. -/
theorem parityGrading_signedSymPiece_map_parityEquiv (i : ZMod 2) :
    (parityGrading (signedSymPiece H) i).map (parityEquiv H).toLinearMap =
      paritySignedSymPiece H.parity i := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap, parityGrading_le_iff]
    intro p hp
    rw [signedSymPiece_eq_span, Submodule.span_le]
    rintro _ ⟨n, d, x, hx, rfl, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, AlgEquiv.toLinearMap_apply, map_list_prod,
      List.map_ofFn]
    have hmem : ∀ k, x k ∈ H.parity.piece (d k : ZMod 2) := fun k ↦ by
      rw [InternalGrading.parity_piece]
      exact mem_parityGrading_of_mem (hx k)
    have hsum : (∑ k, (d k : ZMod 2)) = i := by
      rw [← Int.cast_sum, hp]
    rw [← hsum]
    simpa only [Function.comp_def, parityEquiv_generator] using
      list_prod_generator_mem_paritySignedSymPiece H.parity (fun k ↦ (d k : ZMod 2)) x hmem
  · rw [paritySignedSymPiece_eq_span, Submodule.span_le]
    rintro _ ⟨n, d, x, hx, rfl, rfl⟩
    refine ⟨(List.ofFn fun k ↦ generator H (x k)).prod, ?_, ?_⟩
    · have hgen := (isHomogeneous_signedSymGenerator H).coarsenGrading (Int.castAddHom (ZMod 2))
      rw [← List.sum_ofFn]
      refine SetLike.list_prod_ofFn_mem_graded d (fun k ↦ generator H (x k)) fun k ↦ ?_
      have hxk : x k ∈ parityGrading H.piece (d k) := by
        simpa only [InternalGrading.parity_piece] using hx k
      simpa only [map_zero, add_zero] using hgen.map_mem hxk
    · simp only [AlgEquiv.toLinearMap_apply, map_list_prod, List.map_ofFn, Function.comp_def,
        parityEquiv_generator]

/-- `SignedSym.parityEquiv H` identifies membership in the native parity piece with membership in
the coarsened integer piece. -/
@[simp]
theorem parityEquiv_mem_paritySignedSymPiece_iff {i : ZMod 2} {a : SignedSym H} :
    parityEquiv H a ∈ paritySignedSymPiece H.parity i ↔
      a ∈ parityGrading (signedSymPiece H) i := by
  rw [← parityGrading_signedSymPiece_map_parityEquiv H i]
  exact ⟨fun ⟨y, hy, hye⟩ ↦ (parityEquiv H).injective hye ▸ hy, fun ha ↦ ⟨a, ha, rfl⟩⟩

/-- The inverse comparison `parityEquiv H` likewise reflects parity-piece membership. -/
@[simp]
theorem parityEquiv_symm_mem_parityGrading_iff {i : ZMod 2} {b : ParitySignedSym H.parity} :
    (parityEquiv H).symm b ∈ parityGrading (signedSymPiece H) i ↔
      b ∈ paritySignedSymPiece H.parity i := by
  rw [← parityEquiv_mem_paritySignedSymPiece_iff H, AlgEquiv.apply_symm_apply]

/-- **The parity reduction of the degree-`p` piece lies in the piece of parity `p` modulo two.** -/
theorem parityEquiv_mem_of_mem_signedSymPiece {p : ℤ} {a : SignedSym H}
    (ha : a ∈ signedSymPiece H p) :
    parityEquiv H a ∈ paritySignedSymPiece H.parity p :=
  (parityEquiv_mem_paritySignedSymPiece_iff H).2 (mem_parityGrading_of_mem ha)

end SignedSym

/-! ### Internality, graded algebra structure, and supercommutativity -/

/-- The parity pieces of `ParitySignedSym G` form an internal direct sum, over any commutative
ring. -/
theorem isInternal_paritySignedSymPiece : DirectSum.IsInternal (paritySignedSymPiece G) := by
  rw [← G.parity_ofParity]
  have hpiece : ((InternalGrading.ofDecomposition (parityGrading (signedSymPiece G.ofParity))).map
      (SignedSym.parityEquiv G.ofParity).toLinearEquiv).piece =
        paritySignedSymPiece G.ofParity.parity := by
    funext i
    simpa only [InternalGrading.map_piece, InternalGrading.ofDecomposition_piece] using
      SignedSym.parityGrading_signedSymPiece_map_parityEquiv G.ofParity i
  rw [← hpiece]
  exact ((InternalGrading.ofDecomposition (parityGrading (signedSymPiece G.ofParity))).map
    (SignedSym.parityEquiv G.ofParity).toLinearEquiv).isInternal

/-- `ParitySignedSym G` is an internally `ZMod 2`-graded algebra. -/
noncomputable instance : GradedAlgebra (paritySignedSymPiece G) :=
  (isInternal_paritySignedSymPiece G).gradedAlgebra

/-- The generator map into `ParitySignedSym G` preserves parity. -/
theorem isHomogeneous_paritySignedSymGenerator :
    LinearMap.IsHomogeneous (ParitySignedSym.generator G) G.piece (paritySignedSymPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using generator_mem_paritySignedSymPiece G hx

/-- Homogeneous parity projection commutes with `ParitySignedSym.generator`. -/
@[simp]
theorem decompose_paritySignedSymGenerator (x : V) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece G) (ParitySignedSym.generator G x) i :
        ParitySignedSym G) =
      ParitySignedSym.generator G (DirectSum.decompose G.piece x i : V) := by
  have h := (isHomogeneous_paritySignedSymGenerator G).map_decompose i x
  rw [add_zero] at h
  exact h.symm

namespace ParitySignedSym

/-- Homogeneous elements of `ParitySignedSym G` supercommute with the parity Koszul sign, over any
commutative ring. -/
theorem mul_eq_uzpow_smul_mul {i j : ZMod 2} {a b : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (hb : b ∈ paritySignedSymPiece G j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) := by
  revert a b
  rw [← G.parity_ofParity]
  intro a b ha hb
  obtain ⟨x, rfl⟩ := (SignedSym.parityEquiv G.ofParity).surjective a
  obtain ⟨y, rfl⟩ := (SignedSym.parityEquiv G.ofParity).surjective b
  have hx := (SignedSym.parityEquiv_mem_paritySignedSymPiece_iff G.ofParity).1 ha
  have hy := (SignedSym.parityEquiv_mem_paritySignedSymPiece_iff G.ofParity).1 hb
  have hxy := mul_eq_uzpow_smul_mul_of_mem_parityGrading (𝒜 := signedSymPiece G.ofParity)
    (fun hu hv ↦ by
      simpa [Units.smul_def] using SignedSym.mul_eq_negOnePow_smul_mul G.ofParity hu hv)
    hx hy
  simpa only [← map_mul, Units.smul_def, ← map_zsmul] using
    congrArg (SignedSym.parityEquiv G.ofParity) hxy

/-- An odd homogeneous element of `ParitySignedSym G` squares to its own negative. -/
theorem sq_eq_neg {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 1) :
    a ^ 2 = -(a ^ 2) := by
  simpa only [pow_two, mul_one, uzpow_one, Units.neg_smul, one_smul] using
    mul_eq_uzpow_smul_mul G ha ha

/-- Every odd homogeneous element of `ParitySignedSym G` has square zero when `2` is invertible. -/
theorem sq_eq_zero [Invertible (2 : R)] {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 1) : a ^ 2 = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R) (sq_eq_neg G ha)

/-! ### Graded universal property and functoriality -/

variable {G} in
/-- `ZMod 2`-graded algebra maps out of `ParitySignedSym G` are determined by generators. -/
@[ext]
theorem gradedHom_ext {A : Type w} [Semiring A] [Algebra R A] {𝒜 : ZMod 2 → Submodule R A}
    [GradedAlgebra 𝒜] {φ ψ : paritySignedSymPiece G →ₐᵍ[R] 𝒜}
    (h : ∀ x, φ (generator G x) = ψ (generator G x)) : φ = ψ := by
  have hφψ : φ.toAlgHom = ψ.toAlgHom := hom_ext G h
  exact GradedAlgHom.ext fun a ↦ DFunLike.congr_fun hφψ a

variable {A : Type w} [Ring A] [Algebra R A] (𝒜 : ZMod 2 → Submodule R A)

/-- The universal extension preserves parity when its generator assignment does. -/
theorem isHomogeneous_lift [SetLike.GradedMonoid 𝒜] (f : V →ₗ[R] A)
    (hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) :
    LinearMap.IsHomogeneous (lift G f hr).toLinearMap (paritySignedSymPiece G) 𝒜 0 := by
  refine LinearMap.isHomogeneous_def.2 fun i a ha ↦ ?_
  rw [add_zero]
  refine homogeneous_induction G (P := fun j b ↦ lift G f hr b ∈ 𝒜 j)
    (by simpa only [map_one] using SetLike.GradedOne.one_mem (A := 𝒜))
    (fun j x hx ↦ by simpa only [lift_generator, add_zero] using hf.map_mem hx)
    (fun j k u v hu hv ↦ by rw [map_mul]; exact SetLike.mul_mem_graded hu hv)
    (fun _ ↦ by simp)
    (fun _ _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun _ r _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ r hu) ha

variable [GradedAlgebra 𝒜]

/-- The `ZMod 2`-graded universal extension of a parity-preserving generator assignment satisfying
the Koszul sign rule. Its underlying algebra map is `ParitySignedSym.lift`. -/
noncomputable def gradedLift (f : V →ₗ[R] A)
    (hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      f x * f y = ((-1 : ℤˣ) ^ (i * j)) • (f y * f x))
    (hf : LinearMap.IsHomogeneous f G.piece 𝒜 0) : paritySignedSymPiece G →ₐᵍ[R] 𝒜 where
  toAlgHom := lift G f hr
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using (isHomogeneous_lift G 𝒜 f hr hf).map_mem hx

@[simp]
theorem gradedLift_toAlgHom (f : V →ₗ[R] A) (hr hf) :
    (gradedLift G 𝒜 f hr hf).toAlgHom = lift G f hr := (rfl)

@[simp]
theorem gradedLift_apply (f : V →ₗ[R] A) (hr hf) (a : ParitySignedSym G) :
    gradedLift G 𝒜 f hr hf a = lift G f hr a := (rfl)

-- Not `@[simp]`: `simp` already reduces the LHS via `gradedLift_apply` and `lift_generator`.
theorem gradedLift_generator (f : V →ₗ[R] A) (hr hf) (x : V) :
    gradedLift G 𝒜 f hr hf (generator G x) = f x :=
  lift_generator G f hr x

/-- Uniqueness of the `ZMod 2`-graded universal extension. -/
theorem gradedLift_unique (f : V →ₗ[R] A) (hr hf) (φ : paritySignedSymPiece G →ₐᵍ[R] 𝒜)
    (hφ : ∀ x, φ (generator G x) = f x) : φ = gradedLift G 𝒜 f hr hf := by
  apply gradedHom_ext
  simpa only [gradedLift_generator] using hφ

section GradedMap

variable {W : Type*} [AddCommGroup W] [Module R W] (H : InternalGrading R W (ZMod 2))

/-- Functorial maps induced by parity-preserving linear maps preserve the quotient parity
grading. -/
theorem isHomogeneous_map (f : V →ₗ[R] W) (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    LinearMap.IsHomogeneous (map G H f hf).toLinearMap
      (paritySignedSymPiece G) (paritySignedSymPiece H) 0 := by
  have hr : ∀ (i j : ZMod 2) (x y : V), x ∈ G.piece i → y ∈ G.piece j →
      (generator H).comp f x * (generator H).comp f y =
        ((-1 : ℤˣ) ^ (i * j)) • ((generator H).comp f y * (generator H).comp f x) :=
    fun _ _ _ _ hx hy ↦ generator_mul_generator H
      (by simpa only [add_zero] using hf.map_mem hx)
      (by simpa only [add_zero] using hf.map_mem hy)
  rw [lift_unique G ((generator H).comp f) hr (map G H f hf) (map_generator G H f hf)]
  exact isHomogeneous_lift G (paritySignedSymPiece H) ((generator H).comp f) hr
    (by simpa only [add_zero] using (isHomogeneous_paritySignedSymGenerator H).comp hf)

/-- `ParitySignedSym.congr` reflects and preserves membership in each parity piece. -/
@[simp]
theorem congr_mem_paritySignedSymPiece_iff (e : V ≃ₗ[R] W)
    (he : LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0)
    {i : ZMod 2} {a : ParitySignedSym G} :
    congr G H e he a ∈ paritySignedSymPiece H i ↔ a ∈ paritySignedSymPiece G i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := (isHomogeneous_map H G e.symm.toLinearMap he.linearEquiv_symm).map_mem h
    rw [add_zero, AlgHom.toLinearMap_apply, ← congr_apply, ← congr_symm G H e he,
      AlgEquiv.symm_apply_apply] at h'
    exact h'
  · simpa only [add_zero, AlgHom.toLinearMap_apply, ← congr_apply] using
      (isHomogeneous_map G H e.toLinearMap he).map_mem h

/-- `ParitySignedSym.congr` maps each parity piece of `ParitySignedSym G` onto the corresponding
parity piece of `ParitySignedSym H`. -/
theorem paritySignedSymPiece_map_congr (e : V ≃ₗ[R] W)
    (he : LinearMap.IsHomogeneous e.toLinearMap G.piece H.piece 0) (i : ZMod 2) :
    (paritySignedSymPiece G i).map (congr G H e he).toLinearMap = paritySignedSymPiece H i := by
  ext b
  simp only [Submodule.mem_map, AlgEquiv.toLinearMap_apply]
  exact ⟨fun ⟨a, ha, hab⟩ ↦ hab ▸ (congr_mem_paritySignedSymPiece_iff G H e he).2 ha,
    fun hb ↦ ⟨(congr G H e he).symm b,
      by simpa [congr_symm] using
        (congr_mem_paritySignedSymPiece_iff H G e.symm he.linearEquiv_symm).2 hb,
      (congr G H e he).apply_symm_apply b⟩⟩

/-- A parity-preserving linear map induces a `ZMod 2`-graded algebra map of parity signed
algebras. -/
noncomputable def gradedMap (f : V →ₗ[R] W) (hf : LinearMap.IsHomogeneous f G.piece H.piece 0) :
    paritySignedSymPiece G →ₐᵍ[R] paritySignedSymPiece H where
  toAlgHom := map G H f hf
  map_mem hx := by
    simpa only [add_zero, AlgHom.toLinearMap_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using (isHomogeneous_map G H f hf).map_mem hx

@[simp]
theorem gradedMap_toAlgHom (f : V →ₗ[R] W) (hf) :
    (gradedMap G H f hf).toAlgHom = map G H f hf := (rfl)

@[simp]
theorem gradedMap_apply (f : V →ₗ[R] W) (hf) (a : ParitySignedSym G) :
    gradedMap G H f hf a = map G H f hf a := (rfl)

@[simp]
theorem gradedMap_id :
    gradedMap G G LinearMap.id (LinearMap.isHomogeneous_id G.piece) =
      GradedAlgHom.id R (paritySignedSymPiece G) := by
  ext x
  simp

variable {U : Type*} [AddCommGroup U] [Module R U]

/-- Graded functorial maps of parity signed algebras respect composition. -/
theorem gradedMap_comp (K : InternalGrading R U (ZMod 2)) (f : V →ₗ[R] W) (g : W →ₗ[R] U)
    (hf : LinearMap.IsHomogeneous f G.piece H.piece 0)
    (hg : LinearMap.IsHomogeneous g H.piece K.piece 0) :
    gradedMap G K (g.comp f) (by simpa using hg.comp hf) =
      (gradedMap H K g hg).comp (gradedMap G H f hf) := by
  ext x
  simp

end GradedMap

end ParitySignedSym

namespace SignedSym

variable (H : InternalGrading R V ℤ)

/-- `SignedSym.parityEquiv H` as a `ZMod 2`-graded algebra map from the coarsened integer grading
to the native parity grading. -/
noncomputable def toParityGraded :
    parityGrading (signedSymPiece H) →ₐᵍ[R] paritySignedSymPiece H.parity where
  toAlgHom := (parityEquiv H).toAlgHom
  map_mem ha := (parityEquiv_mem_paritySignedSymPiece_iff H).2 ha

/-- The inverse of `SignedSym.parityEquiv H` as a `ZMod 2`-graded algebra map. -/
noncomputable def fromParityGraded :
    paritySignedSymPiece H.parity →ₐᵍ[R] parityGrading (signedSymPiece H) where
  toAlgHom := (parityEquiv H).symm.toAlgHom
  map_mem hb := (parityEquiv_symm_mem_parityGrading_iff H).2 hb

@[simp]
theorem toParityGraded_toAlgHom :
    (toParityGraded H).toAlgHom = (parityEquiv H).toAlgHom := (rfl)

@[simp]
theorem fromParityGraded_toAlgHom :
    (fromParityGraded H).toAlgHom = (parityEquiv H).symm.toAlgHom := (rfl)

@[simp]
theorem toParityGraded_apply (a : SignedSym H) : toParityGraded H a = parityEquiv H a := (rfl)

@[simp]
theorem fromParityGraded_apply (b : ParitySignedSym H.parity) :
    fromParityGraded H b = (parityEquiv H).symm b := (rfl)

@[simp]
theorem fromParityGraded_comp_toParityGraded :
    (fromParityGraded H).comp (toParityGraded H) =
      GradedAlgHom.id R (parityGrading (signedSymPiece H)) := by
  ext a
  simp

@[simp]
theorem toParityGraded_comp_fromParityGraded :
    (toParityGraded H).comp (fromParityGraded H) =
      GradedAlgHom.id R (paritySignedSymPiece H.parity) := by
  ext b
  simp

/-- `SignedSym.parityEquiv H` commutes with projection onto each parity component. -/
@[simp]
theorem decompose_parityEquiv (a : SignedSym H) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece H.parity) (parityEquiv H a) i :
        ParitySignedSym H.parity) =
      parityEquiv H (DirectSum.decompose (parityGrading (signedSymPiece H)) a i : SignedSym H) := by
  have hhom : LinearMap.IsHomogeneous (parityEquiv H).toLinearMap
      (parityGrading (signedSymPiece H)) (paritySignedSymPiece H.parity) 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
      simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
        (parityEquiv_mem_paritySignedSymPiece_iff H).2 ha
  have h := hhom.map_decompose i a
  rw [add_zero] at h
  exact h.symm

/-- `(SignedSym.parityEquiv H).symm` commutes with projection onto each parity component. -/
@[simp]
theorem decompose_parityEquiv_symm (b : ParitySignedSym H.parity) (i : ZMod 2) :
    (DirectSum.decompose (parityGrading (signedSymPiece H)) ((parityEquiv H).symm b) i :
        SignedSym H) =
      (parityEquiv H).symm
        (DirectSum.decompose (paritySignedSymPiece H.parity) b i : ParitySignedSym H.parity) := by
  have hhom : LinearMap.IsHomogeneous (parityEquiv H).symm.toLinearMap
      (paritySignedSymPiece H.parity) (parityGrading (signedSymPiece H)) 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hb ↦ by
      simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
        (parityEquiv_symm_mem_parityGrading_iff H).2 hb
  have h := hhom.map_decompose i b
  rw [add_zero] at h
  exact h.symm

end SignedSym

end TauCeti
