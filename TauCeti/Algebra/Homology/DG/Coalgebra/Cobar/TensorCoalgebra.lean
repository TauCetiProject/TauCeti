/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.Basic
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.Augmentation
public import TauCeti.LinearAlgebra.TensorAlgebra.Projection
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coassoc
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Prepend
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation
public import TauCeti.LinearAlgebra.TensorCoalgebra.Grading
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives
public import TauCeti.LinearAlgebra.TensorPower.Basic

/-!
# Contracting the cobar construction of the cofree tensor coalgebra

Let `(A, G)` be a `ℤ`-graded module over a commutative ring `R`, and consider the reduced tensor
coalgebra `Tᶜ(sA)` (`TauCeti.ReducedTensorWords R A`) with its reduced deconcatenation coproduct
and zero internal differential.  Its cobar construction `Ω Tᶜ(sA)` carries the unperturbed cobar
differential `δ₀` (`TauCeti.cobarDeconcatDifferential G`), which is the odd derivation extending
the desuspended deconcatenation on generators.

This file constructs an explicit homogeneous special contraction
(`TauCeti.IsNonCounitalDGCoalgebra.cobarUnperturbedContraction`) of the augmentation ideal
`(Ω⁺ Tᶜ(sA), δ₀)` onto `(A, 0)` over an arbitrary commutative ring `R`.  The contraction is given
by:

* inclusion `i : A →ₗ Ω Tᶜ(sA)` (`TauCeti.cobarTensorIncl G`), sending `a` to `(-1) ^ |sa| s⁻¹ [a]`;
* projection `p : Ω Tᶜ(sA) →ₗ A` (`TauCeti.cobarTensorProj G`), reading the single-letter
  component of tensor length one and undoing the suspension sign;
* contracting homotopy `h : Ω Tᶜ(sA) →ₗ Ω Tᶜ(sA)` (`TauCeti.cobarTensorHomotopy G`), which joins
  the first two tensor factors whenever the first is a single letter,
  `h (s⁻¹ [a] * s⁻¹ w * z) = (-1) ^ |sa| s⁻¹ (a · w) * z`, and kills tensor lengths zero and one as
  well as words whose leading factor has bar length at least two.

The contraction is packaged on the augmentation ideal of any noncounital DG coalgebra structure
`hC` on `Tᶜ(sA)` (whose augmentation ideal depends only on the tensor algebra, not on the internal
differential), so that homological perturbation theory can immediately perturb `δ₀` by an arbitrary
coderivation differential `dC`.

## Main definitions

* `TauCeti.cobarDeconcatDifferential`: the unperturbed cobar differential `δ₀` on `Ω Tᶜ(sA)`.
* `TauCeti.cobarTensorIncl`, `TauCeti.cobarTensorProj`, `TauCeti.cobarTensorHomotopy`: the
  inclusion, projection, and contracting homotopy on `Ω Tᶜ(sA)`.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarDeconcatReducedDifferential`: `δ₀` restricted to the
  cobar augmentation ideal `Ω⁺ Tᶜ(sA)`.
* `TauCeti.IsNonCounitalDGCoalgebra.cobarUnperturbedContraction`: the explicit homogeneous special
  contraction of `(Ω⁺ Tᶜ(sA), δ₀)` onto `(A, 0)`.

## Main results

* `TauCeti.cobarDifferential_mul_koszulTwist`: the graded Leibniz rule of `cobarDifferential`
  expressed globally using the Koszul twist automorphism.
* `TauCeti.isHomogeneous_cobarTensorIncl`, `TauCeti.isHomogeneous_cobarTensorProj`,
  `TauCeti.isHomogeneous_cobarTensorHomotopy`: degrees `0`, `0`, and `-1` of the contraction maps.
* `TauCeti.cobarTensorHomotopy_eq_zero_of_mem_tensorPower_one` and
  `TauCeti.cobarTensorHomotopy_mem_tensorPower`: `h` kills tensor length one and strictly lowers
  higher tensor lengths.
* `TauCeti.IsNonCounitalDGCoalgebra.isHomogeneous_cobarUnperturbedContraction_incl`,
  `TauCeti.IsNonCounitalDGCoalgebra.isHomogeneous_cobarUnperturbedContraction_proj`, and
  `TauCeti.IsNonCounitalDGCoalgebra.isHomogeneous_cobarUnperturbedContraction_homotopy`:
  homogeneity of the restricted contraction.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for the acyclic cobar construction of a cofree coalgebra.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
-/

public section

open scoped TensorProduct
open TensorAlgebra

namespace TauCeti

universe uR uA uC

section GeneralCobar

variable {R : Type uR} {C : Type uC} [CommRing R] [AddCommGroup C] [Module R C]

/-- The graded Leibniz rule for `cobarDifferential`, expressed globally using the Koszul twist
automorphism rather than assuming the left factor is homogeneous. -/
theorem cobarDifferential_mul_koszulTwist (G : InternalGrading R C ℤ)
    (Δ : C →ₗ[R] C ⊗[R] C) (d : C →ₗ[R] C) (x y : TensorAlgebra R C) :
    cobarDifferential G Δ d (x * y) =
      cobarDifferential G Δ d x * y +
        InternalGrading.koszulTwistAlgEquiv (tensorAlgebraPiece (G.shift (-1))) 1 x *
          cobarDifferential G Δ d y := by
  let D := cobarDifferential G Δ d
  let L : TensorAlgebra R C →ₗ[R] TensorAlgebra R C := D ∘ₗ LinearMap.mulRight R y
  let Q : TensorAlgebra R C →ₗ[R] TensorAlgebra R C :=
    LinearMap.mulRight R y ∘ₗ D +
      LinearMap.mulRight R (D y) ∘ₗ
        (InternalGrading.koszulTwistAlgEquiv (tensorAlgebraPiece (G.shift (-1))) 1).toLinearMap
  suffices h : L = Q from LinearMap.congr_fun h x
  refine (InternalGrading.ofDecomposition (tensorAlgebraPiece (G.shift (-1)))).linearMap_ext
    fun p z hz ↦ ?_
  rw [InternalGrading.ofDecomposition_piece] at hz
  simp only [L, Q, D, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.mulRight_apply,
    AlgEquiv.toLinearMap_apply]
  rw [cobarDifferential_mul _ _ _ hz,
    InternalGrading.koszulTwistAlgEquiv_apply_of_mem _ 1 hz, one_mul, smul_mul_assoc]

/-- An odd derivation of `Ω C` whose values on generators lie in the augmentation ideal takes every
element into the augmentation ideal. -/
theorem IsNonCounitalDGCoalgebra.cobarAugmentation_derivation_eq_zero
    {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {d : C →ₗ[R] C}
    (hC : IsNonCounitalDGCoalgebra G Δ d) {f : C →ₗ[R] TensorAlgebra R C}
    (hf : ∀ c, hC.cobarAugmentation (f c) = 0) (x : TensorAlgebra R C) :
    hC.cobarAugmentation (tensorAlgebraDerivation (G.shift (-1)) f x) = 0 := by
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp
  | ι c => simp [hf c]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy =>
    rw [tensorAlgebraDerivation_mul, map_add, map_mul, map_mul, hx, hy, zero_mul, mul_zero,
      add_zero]

end GeneralCobar

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Auxiliary extensionality and Koszul-twist lemmas -/

private theorem koszulTwist_ofLetter (G : InternalGrading R A ℤ) (a : A) :
    (ReducedTensorWords.grading (G.shift 1)).koszulTwist 1 (ReducedTensorWords.ofLetter R A a) =
      ReducedTensorWords.ofLetter R A ((G.shift 1).koszulTwist 1 a) := by
  rw [ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

private theorem koszulTwist_prepend (G : InternalGrading R A ℤ) (a : A)
    (w : ReducedTensorWords R A) :
    (ReducedTensorWords.grading (G.shift 1)).koszulTwist 1 (ReducedTensorWords.prepend R A a w) =
      ReducedTensorWords.prepend R A ((G.shift 1).koszulTwist 1 a)
        ((ReducedTensorWords.grading (G.shift 1)).koszulTwist 1 w) := by
  rw [ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_prepend]

private theorem letter_koszulTwist (G : InternalGrading R A ℤ) (c : ReducedTensorWords R A) :
    ReducedTensorWords.letter R A ((ReducedTensorWords.grading (G.shift 1)).koszulTwist 1 c) =
      (G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A c) := by
  have h := ReducedTensorWords.isHomogeneous_letter (G.shift 1)
  rw [← ReducedTensorWords.grading_piece] at h
  simpa using (h.koszulTwist_apply 1 c).symm

private theorem reducedTensorWords_linearMap_ext_ofLetter_prepend {N : Type*}
    [AddCommGroup N] [Module R N] {f g : ReducedTensorWords R A →ₗ[R] N}
    (h1 : ∀ a : A, f (ReducedTensorWords.ofLetter R A a) = g (ReducedTensorWords.ofLetter R A a))
    (h2 : ∀ (a : A) (w : ReducedTensorWords R A),
      f (ReducedTensorWords.prepend R A a w) = g (ReducedTensorWords.prepend R A a w)) :
    f = g := by
  refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
  obtain ⟨n, hn⟩ := n
  rcases n with _ | _ | k
  · omega
  · have hEq : ReducedTensorWords.of R A ⟨1, hn⟩ (PiTensorProduct.tprod R x) =
        ReducedTensorWords.ofLetter R A (x 0) := by
      rw [ReducedTensorWords.ofLetter_eq_of_tprod]
      exact ReducedTensorWords.of_tprod_congr R A hn rfl fun i ↦ by fin_cases i; rfl
    rw [hEq, h1]
  · have hEq : ReducedTensorWords.of R A ⟨k + 2, hn⟩ (PiTensorProduct.tprod R x) =
        ReducedTensorWords.prepend R A (x 0)
          (ReducedTensorWords.of R A ⟨k + 1, Nat.succ_pos k⟩
            (PiTensorProduct.tprod R fun i ↦ x i.succ)) := by
      rw [ReducedTensorWords.prepend_of_tprod]
      refine ReducedTensorWords.of_tprod_congr R A hn rfl fun i ↦ ?_
      cases i using Fin.cases with
      | zero => simp
      | succ j => simp
    rw [hEq, h2]

private theorem tensorAlgebra_linearMap_ext {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {f g : TensorAlgebra R M →ₗ[R] N}
    (h : ∀ (n : ℕ) (x : Fin n → M),
      f (TensorAlgebra.tprod R M n x) = g (TensorAlgebra.tprod R M n x)) :
    f = g := by
  refine LinearMap.ext fun z ↦ ?_
  rw [← TensorAlgebra.ofDirectSum_toDirectSum z]
  generalize TensorAlgebra.toDirectSum z = y
  induction y using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | of n t =>
    induction t using PiTensorProduct.induction_on with
    | add u v hu hv => simp only [map_add, hu, hv]
    | smul_tprod r x =>
      simp only [DirectSum.of_smul, map_smul, TensorAlgebra.ofDirectSum_of_tprod, h n x]

private theorem tprod_succ {M : Type*} [AddCommMonoid M] [Module R M] (n : ℕ)
    (x : Fin (n + 1) → M) :
    TensorAlgebra.tprod R M (n + 1) x =
      ι R (x 0) * TensorAlgebra.tprod R M n (fun i ↦ x i.succ) := by
  simp [TensorAlgebra.tprod_apply, List.ofFn_succ]

/-! ### The unperturbed cobar differential `δ₀` on `Ω Tᶜ(sA)` -/

/-- The reduced tensor coalgebra `Tᶜ(sA)` with reduced deconcatenation and zero differential is a
noncounital differential graded coalgebra. -/
theorem isNonCounitalDGCoalgebra_reducedTensorWords_zero (G : InternalGrading R A ℤ) :
    IsNonCounitalDGCoalgebra (ReducedTensorWords.grading (G.shift 1))
      (ReducedTensorWords.deconcatenation R A) (0 : Module.End R (ReducedTensorWords R A)) where
  coassoc := ReducedTensorWords.deconcatenation_coassoc R A
  isHomogeneous_comul := ReducedTensorWords.isHomogeneous_deconcatenation _
  map_mem _ := zero_mem _
  sq_zero _ := rfl
  comul_differential := by ext x; simp

/-- The unperturbed cobar differential `δ₀` on `Ω Tᶜ(sA)`, carrying only reduced deconcatenation
with zero internal differential. -/
noncomputable def cobarDeconcatDifferential (G : InternalGrading R A ℤ) :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  cobarDifferential (ReducedTensorWords.grading (G.shift 1))
    (ReducedTensorWords.deconcatenation R A) 0

/-- The unperturbed cobar differential on a generator `s⁻¹ c`. -/
@[simp]
theorem cobarDeconcatDifferential_ι (G : InternalGrading R A ℤ) (c : ReducedTensorWords R A) :
    cobarDeconcatDifferential G (ι R c) =
      LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
        (TensorProduct.map
          (ι R ∘ₗ (ReducedTensorWords.grading (G.shift 1)).koszulTwist 1) (ι R)
          (ReducedTensorWords.deconcatenation R A c)) := by
  simp [cobarDeconcatDifferential]

/-- The unperturbed cobar differential kills scalars. -/
@[simp]
theorem cobarDeconcatDifferential_algebraMap (G : InternalGrading R A ℤ) (r : R) :
    cobarDeconcatDifferential G (algebraMap R (TensorAlgebra R (ReducedTensorWords R A)) r) = 0 :=
  cobarDifferential_algebraMap _ _ _ r

/-- The unperturbed cobar differential satisfies the graded Leibniz rule. -/
theorem cobarDeconcatDifferential_mul (G : InternalGrading R A ℤ)
    (x y : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarDeconcatDifferential G (x * y) =
      cobarDeconcatDifferential G x * y +
        InternalGrading.koszulTwistAlgEquiv
          (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1))) 1 x *
          cobarDeconcatDifferential G y :=
  cobarDifferential_mul_koszulTwist _ _ _ x y

/-- The unperturbed cobar differential squares to zero. -/
@[simp]
theorem cobarDeconcatDifferential_comp_self (G : InternalGrading R A ℤ) :
    cobarDeconcatDifferential G ∘ₗ cobarDeconcatDifferential G = 0 :=
  LinearMap.ext fun x ↦
    (isNonCounitalDGCoalgebra_reducedTensorWords_zero G).cobarDifferential_cobarDifferential x

/-! ### The inclusion, projection, and contracting homotopy on `Ω Tᶜ(sA)` -/

/-- The canonical inclusion `A →ₗ Ω Tᶜ(sA)`, sending `a` to `(-1) ^ |sa| s⁻¹ [a]`. -/
noncomputable def cobarTensorIncl (G : InternalGrading R A ℤ) :
    A →ₗ[R] TensorAlgebra R (ReducedTensorWords R A) :=
  ι R ∘ₗ ReducedTensorWords.ofLetter R A ∘ₗ (G.shift 1).koszulTwist 1

/-- Evaluation of `cobarTensorIncl` on an element `a : A`. -/
theorem cobarTensorIncl_apply (G : InternalGrading R A ℤ) (a : A) :
    cobarTensorIncl G a =
      ι R (ReducedTensorWords.ofLetter R A ((G.shift 1).koszulTwist 1 a)) := (rfl)

/-- The inclusion `A →ₗ Ω Tᶜ(sA)` has degree zero. -/
theorem isHomogeneous_cobarTensorIncl (G : InternalGrading R A ℤ) :
    LinearMap.IsHomogeneous (cobarTensorIncl G) G.piece
      (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1))) 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p a ha ↦ ?_
  rw [add_zero, cobarTensorIncl_apply]
  refine ι_mem_tensorAlgebraPiece _ ?_
  rw [InternalGrading.shift_piece, ReducedTensorWords.grading_piece]
  have ha' : a ∈ (G.shift 1).piece (p + -1) := by
    rw [InternalGrading.shift_piece, neg_add_cancel_right]
    exact ha
  exact ReducedTensorWords.ofLetter_mem_gradedPiece (G.shift 1)
    ((G.shift 1).koszulTwist_mem_piece ha' 1)

/-- The canonical projection `Ω Tᶜ(sA) →ₗ A`, reading the single-letter component of tensor length
one and undoing the suspension sign. -/
noncomputable def cobarTensorProj (G : InternalGrading R A ℤ) :
    TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] A :=
  (G.shift 1).koszulTwist 1 ∘ₗ ReducedTensorWords.letter R A ∘ₗ
    (TensorPower.oneEquiv R (ReducedTensorWords R A)).toLinearMap ∘ₗ
    TensorAlgebra.tensorPowerProjection 1

/-- Evaluation of `cobarTensorProj` on a tensor product of generators. -/
theorem cobarTensorProj_tprod (G : InternalGrading R A ℤ) (n : ℕ)
    (x : Fin n → ReducedTensorWords R A) :
    cobarTensorProj G (TensorAlgebra.tprod R (ReducedTensorWords R A) n x) =
      if h : n = 1 then
        (G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (x ⟨0, by omega⟩))
      else 0 := by
  simp only [cobarTensorProj, LinearMap.comp_apply, TensorAlgebra.tensorPowerProjection_tprod]
  split_ifs with h
  · subst h
    simp only [TensorPower.cast_refl, LinearEquiv.refl_apply, LinearEquiv.coe_coe,
      TensorPower.oneEquiv_tprod]
    rfl
  · simp

/-- Evaluation of `cobarTensorProj` on a single generator `s⁻¹ c`. -/
@[simp]
theorem cobarTensorProj_ι (G : InternalGrading R A ℤ) (c : ReducedTensorWords R A) :
    cobarTensorProj G (ι R c) =
      (G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A c) := by
  have hι : ι R c = TensorAlgebra.tprod R (ReducedTensorWords R A) 1 (fun _ ↦ c) := by
    simp [TensorAlgebra.tprod_apply]
  rw [hι, cobarTensorProj_tprod]
  simp

private theorem cobarTensorProj_mul_ι_mul (G : InternalGrading R A ℤ)
    (c₀ c₁ : ReducedTensorWords R A) (z : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorProj G (ι R c₀ * (ι R c₁ * z)) = 0 := by
  let L : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] A :=
    cobarTensorProj G ∘ₗ LinearMap.mulLeft R (ι R c₀) ∘ₗ LinearMap.mulLeft R (ι R c₁)
  suffices h : L = 0 from LinearMap.congr_fun h z
  refine tensorAlgebra_linearMap_ext fun n y ↦ ?_
  have hmul : ι R c₀ * (ι R c₁ * TensorAlgebra.tprod R (ReducedTensorWords R A) n y) =
      TensorAlgebra.tprod R (ReducedTensorWords R A) (n + 2) (Fin.cons c₀ (Fin.cons c₁ y)) := by
    rw [tprod_succ, tprod_succ]; simp
  have hne : n + 2 ≠ 1 := by omega
  simp only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply, hmul,
    cobarTensorProj_tprod, hne, ↓reduceDIte]

/-- The projection `Ω Tᶜ(sA) →ₗ A` has degree zero. -/
theorem isHomogeneous_cobarTensorProj (G : InternalGrading R A ℤ) :
    LinearMap.IsHomogeneous (cobarTensorProj G)
      (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1))) G.piece 0 := by
  refine LinearMap.isHomogeneous_def.2 fun p z hz ↦ ?_
  rw [add_zero]
  refine tensorAlgebraPiece_le (C := (G.piece p).comap (cobarTensorProj G))
    (fun n d x hx hd ↦ ?_) hz
  rw [Submodule.mem_comap, cobarTensorProj_tprod]
  split_ifs with hn
  · subst hn
    have h0 : x 0 ∈ (ReducedTensorWords.grading (G.shift 1)).piece (p - 1) := by
      have hd0 : d 0 = p := by simpa using hd
      have hx0 := hx 0
      rw [hd0, InternalGrading.shift_piece] at hx0
      simpa [sub_eq_add_neg] using hx0
    have hl : ReducedTensorWords.letter R A (x 0) ∈ (G.shift 1).piece (p - 1) := by
      have h := ReducedTensorWords.isHomogeneous_letter (G.shift 1)
      rw [← ReducedTensorWords.grading_piece] at h
      simpa only [add_zero] using h.map_mem h0
    have htw := (G.shift 1).koszulTwist_mem_piece hl 1
    rw [InternalGrading.shift_piece, sub_add_cancel] at htw
    exact htw
  · exact zero_mem _

private theorem fin_zero_ne_one (k : ℕ) : (0 : Fin (k + 2)) ≠ 1 := by
  rw [← Fin.succ_zero_eq_one]
  exact (Fin.succ_ne_zero 0).symm

private theorem fin_one_ne_succ_succ {k : ℕ} (j : Fin k) : (1 : Fin (k + 2)) ≠ j.succ.succ := by
  rw [← Fin.succ_zero_eq_one]
  exact Fin.succ_inj.ne.2 (Fin.succ_ne_zero j).symm

private theorem update_tail_of_one {α : Type*} {k : ℕ} [DecidableEq (Fin (k + 2))]
    (x : Fin (k + 2) → α) (v : α) :
    (fun l : Fin k ↦ Function.update x (1 : Fin (k + 2)) v l.succ.succ) = fun l ↦ x l.succ.succ :=
  funext fun l ↦ Function.update_of_ne (fin_one_ne_succ_succ l).symm _ _

private theorem update_tail_of_succ_succ {α : Type*} {k : ℕ} [DecidableEq (Fin (k + 2))]
    (x : Fin (k + 2) → α) (j : Fin k) (v : α) :
    (fun l : Fin k ↦ Function.update x j.succ.succ v l.succ.succ) =
      Function.update (fun l : Fin k ↦ x l.succ.succ) j v := by
  funext l
  by_cases hlj : l = j
  · subst hlj; simp
  · simp [hlj, Fin.succ_inj]

/-- The multilinear formula defining the unperturbed contracting homotopy on tensor length `k + 2`:
`x ↦ ι (prepend (twist (letter (x 0))) (x 1)) * tprod k (x ∘ succ ∘ succ)`. -/
private noncomputable def cobarTensorHomotopyMulti (G : InternalGrading R A ℤ) (k : ℕ) :
    MultilinearMap (RingHom.id R) (fun _ : Fin (k + 2) ↦ ReducedTensorWords R A)
      (TensorAlgebra R (ReducedTensorWords R A)) where
  toFun x :=
    ι R (ReducedTensorWords.prepend R A
        ((G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (x 0))) (x 1)) *
      TensorAlgebra.tprod R (ReducedTensorWords R A) k (fun j ↦ x j.succ.succ)
  map_update_add' x i a b := by
    cases i using Fin.cases with
    | zero => simp [add_mul]
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.succ_zero_eq_one, Function.update_of_ne (fin_zero_ne_one k),
          Function.update_self, update_tail_of_one, map_add, add_mul]
      | succ j =>
        simp only [Function.update_of_ne (Fin.succ_ne_zero _).symm,
          Function.update_of_ne (fin_one_ne_succ_succ j), update_tail_of_succ_succ,
          (TensorAlgebra.tprod R (ReducedTensorWords R A) k).map_update_add, mul_add]
  map_update_smul' x i r a := by
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.succ_zero_eq_one, Function.update_of_ne (fin_zero_ne_one k),
          Function.update_self, update_tail_of_one, map_smul, smul_mul_assoc, RingHom.id_apply]
      | succ j =>
        simp only [Function.update_of_ne (Fin.succ_ne_zero _).symm,
          Function.update_of_ne (fin_one_ne_succ_succ j), update_tail_of_succ_succ,
          (TensorAlgebra.tprod R (ReducedTensorWords R A) k).map_update_smul, mul_smul_comm]

private noncomputable def cobarTensorHomotopyComp (G : InternalGrading R A ℤ) :
    ∀ n : ℕ, TensorPower R n (ReducedTensorWords R A) →ₗ[R]
      TensorAlgebra R (ReducedTensorWords R A)
  | 0 => 0
  | 1 => 0
  | k + 2 => PiTensorProduct.lift (cobarTensorHomotopyMulti G k)

/-- The unperturbed contracting homotopy on `Ω Tᶜ(sA)`: it joins the first two factors when the
first is a single letter, and vanishes on tensor lengths `0` and `1`. -/
noncomputable def cobarTensorHomotopy (G : InternalGrading R A ℤ) :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  DirectSum.toModule R ℕ (TensorAlgebra R (ReducedTensorWords R A)) (cobarTensorHomotopyComp G) ∘ₗ
    TensorAlgebra.toDirectSum.toLinearMap

theorem cobarTensorHomotopy_tprod_zero (G : InternalGrading R A ℤ)
    (x : Fin 0 → ReducedTensorWords R A) :
    cobarTensorHomotopy G (TensorAlgebra.tprod R (ReducedTensorWords R A) 0 x) = 0 := by
  simp only [cobarTensorHomotopy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof,
    cobarTensorHomotopyComp, LinearMap.zero_apply]

/-- The unperturbed contracting homotopy kills the unit `1`. -/
@[simp]
theorem cobarTensorHomotopy_one (G : InternalGrading R A ℤ) :
    cobarTensorHomotopy G 1 = 0 := by
  have h1 : (1 : TensorAlgebra R (ReducedTensorWords R A)) =
      TensorAlgebra.tprod R (ReducedTensorWords R A) 0 Fin.elim0 := by
    simp [TensorAlgebra.tprod_apply]
  rw [h1, cobarTensorHomotopy_tprod_zero]

/-- The unperturbed contracting homotopy kills tensor products of length one. -/
theorem cobarTensorHomotopy_tprod_one (G : InternalGrading R A ℤ)
    (x : Fin 1 → ReducedTensorWords R A) :
    cobarTensorHomotopy G (TensorAlgebra.tprod R (ReducedTensorWords R A) 1 x) = 0 := by
  simp only [cobarTensorHomotopy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof,
    cobarTensorHomotopyComp, LinearMap.zero_apply]

/-- The unperturbed contracting homotopy kills every single generator `s⁻¹ c`. -/
@[simp]
theorem cobarTensorHomotopy_ι (G : InternalGrading R A ℤ) (c : ReducedTensorWords R A) :
    cobarTensorHomotopy G (ι R c) = 0 := by
  have hι : ι R c = TensorAlgebra.tprod R (ReducedTensorWords R A) 1 (fun _ ↦ c) := by
    simp [TensorAlgebra.tprod_apply]
  rw [hι, cobarTensorHomotopy_tprod_one]

/-- Evaluation of `cobarTensorHomotopy` on a tensor product of length `k + 2`. -/
theorem cobarTensorHomotopy_tprod_add_two (G : InternalGrading R A ℤ) (k : ℕ)
    (x : Fin (k + 2) → ReducedTensorWords R A) :
    cobarTensorHomotopy G (TensorAlgebra.tprod R (ReducedTensorWords R A) (k + 2) x) =
      ι R (ReducedTensorWords.prepend R A
          ((G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (x 0))) (x 1)) *
        TensorAlgebra.tprod R (ReducedTensorWords R A) k (fun j ↦ x j.succ.succ) := by
  simp only [cobarTensorHomotopy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof,
    cobarTensorHomotopyComp, PiTensorProduct.lift.tprod, cobarTensorHomotopyMulti,
    MultilinearMap.coe_mk]

/-- The fundamental formula for `cobarTensorHomotopy` on a product beginning with two generators. -/
theorem cobarTensorHomotopy_ι_mul_ι_mul (G : InternalGrading R A ℤ)
    (c₀ c₁ : ReducedTensorWords R A) (z : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorHomotopy G (ι R c₀ * (ι R c₁ * z)) =
      ι R (ReducedTensorWords.prepend R A
        ((G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A c₀)) c₁) * z := by
  let L : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R]
      TensorAlgebra R (ReducedTensorWords R A) :=
    cobarTensorHomotopy G ∘ₗ LinearMap.mulLeft R (ι R c₀) ∘ₗ LinearMap.mulLeft R (ι R c₁)
  let Q : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R]
      TensorAlgebra R (ReducedTensorWords R A) :=
    LinearMap.mulLeft R (ι R (ReducedTensorWords.prepend R A
      ((G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A c₀)) c₁))
  suffices h : L = Q from LinearMap.congr_fun h z
  refine tensorAlgebra_linearMap_ext fun k y ↦ ?_
  have hmul : ι R c₀ * (ι R c₁ * TensorAlgebra.tprod R (ReducedTensorWords R A) k y) =
      TensorAlgebra.tprod R (ReducedTensorWords R A) (k + 2) (Fin.cons c₀ (Fin.cons c₁ y)) := by
    rw [tprod_succ, tprod_succ]; simp
  simp only [L, Q, LinearMap.comp_apply, LinearMap.mulLeft_apply, hmul,
    cobarTensorHomotopy_tprod_add_two]
  simp

private theorem cobarTensorHomotopy_ι_mul_of_letter_eq_zero (G : InternalGrading R A ℤ)
    {c : ReducedTensorWords R A} (hc : ReducedTensorWords.letter R A c = 0)
    (y : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorHomotopy G (ι R c * y) = 0 := by
  let L : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R]
      TensorAlgebra R (ReducedTensorWords R A) :=
    cobarTensorHomotopy G ∘ₗ LinearMap.mulLeft R (ι R c)
  suffices h : L = 0 from LinearMap.congr_fun h y
  refine tensorAlgebra_linearMap_ext fun n u ↦ ?_
  cases n with
  | zero => simp [L, TensorAlgebra.tprod_apply, cobarTensorHomotopy_ι]
  | succ k =>
    simp only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply, tprod_succ,
      cobarTensorHomotopy_ι_mul_ι_mul, hc, map_zero, LinearMap.zero_apply, zero_mul]

/-- The unperturbed contracting homotopy has degree `-1`. -/
theorem isHomogeneous_cobarTensorHomotopy (G : InternalGrading R A ℤ) :
    LinearMap.IsHomogeneous (cobarTensorHomotopy G)
      (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1)))
      (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1))) (-1) := by
  refine LinearMap.isHomogeneous_def.2 fun q z hz ↦ ?_
  refine tensorAlgebraPiece_le
    (C := (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1))
      (q + -1)).comap (cobarTensorHomotopy G)) (fun n d x hx hd ↦ ?_) hz
  rw [Submodule.mem_comap]
  rcases n with _ | _ | k
  · rw [cobarTensorHomotopy_tprod_zero]; exact zero_mem _
  · rw [cobarTensorHomotopy_tprod_one]; exact zero_mem _
  · rw [cobarTensorHomotopy_tprod_add_two]
    have h0 : x 0 ∈ (ReducedTensorWords.grading (G.shift 1)).piece (d 0 + -1) := by
      simpa only [InternalGrading.shift_piece] using hx 0
    have h1 : x 1 ∈ (ReducedTensorWords.grading (G.shift 1)).piece (d 1 + -1) := by
      simpa only [InternalGrading.shift_piece] using hx 1
    have hl0 : ReducedTensorWords.letter R A (x 0) ∈ (G.shift 1).piece (d 0 + -1) := by
      have h := ReducedTensorWords.isHomogeneous_letter (G.shift 1)
      rw [← ReducedTensorWords.grading_piece] at h
      simpa only [add_zero] using h.map_mem h0
    have htw0 := (G.shift 1).koszulTwist_mem_piece hl0 1
    have hpre : ReducedTensorWords.prepend R A
        ((G.shift 1).koszulTwist 1 (ReducedTensorWords.letter R A (x 0))) (x 1) ∈
        ((ReducedTensorWords.grading (G.shift 1)).shift (-1)).piece (d 0 + d 1 + -1) := by
      rw [InternalGrading.shift_piece, ReducedTensorWords.grading_piece]
      rw [ReducedTensorWords.grading_piece] at h1
      have hdeg : (d 0 + -1) + (d 1 + -1) = d 0 + d 1 + -1 + -1 := by ring
      exact hdeg ▸ ReducedTensorWords.prepend_mem_gradedPiece htw0 h1
    have htail := tprod_mem_tensorAlgebraPiece
      ((ReducedTensorWords.grading (G.shift 1)).shift (-1))
      (fun j : Fin k ↦ d j.succ.succ) (fun j ↦ x j.succ.succ) fun j ↦ hx j.succ.succ
    have hsum : d 0 + d 1 + -1 + ∑ j : Fin k, d j.succ.succ = q + -1 := by
      rw [← hd, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]
      ring
    exact hsum ▸ SetLike.GradedMul.mul_mem (ι_mem_tensorAlgebraPiece _ hpre) htail

/-! ### Tensor-length filtration properties of `cobarTensorHomotopy` -/

/-- Left multiplication by a generator increases tensor length by one. -/
theorem ι_mul_mem_range_toTensorAlgebra {M : Type*} [AddCommMonoid M] [Module R M]
    (c : M) {n : ℕ} {y : TensorAlgebra R M}
    (hy : y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n))) :
    ι R c * y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n + 1)) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | add u v hu hv => simpa only [map_add, mul_add] using Submodule.add_mem _ hu hv
  | smul_tprod r x =>
    rw [map_smul, mul_smul_comm, TensorPower.toTensorAlgebra_tprod]
    refine Submodule.smul_mem _ r ?_
    have h : ι R c * TensorAlgebra.tprod R M n x =
        TensorAlgebra.tprod R M (n + 1) (Fin.cons c x) := by
      rw [tprod_succ]; simp
    exact ⟨PiTensorProduct.tprod R (Fin.cons c x),
      (TensorPower.toTensorAlgebra_tprod _).trans h.symm⟩

/-- The unperturbed contracting homotopy kills tensor length one. -/
theorem cobarTensorHomotopy_eq_zero_of_mem_tensorPower_one (G : InternalGrading R A ℤ)
    {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ LinearMap.range
      (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := 1))) :
    cobarTensorHomotopy G z = 0 := by
  obtain ⟨t, rfl⟩ := hz
  induction t using PiTensorProduct.induction_on with
  | add u v hu hv => simp [hu, hv]
  | smul_tprod r x =>
    simp only [map_smul, TensorPower.toTensorAlgebra_tprod, cobarTensorHomotopy_tprod_one,
      smul_zero]

/-- The unperturbed contracting homotopy lowers tensor length from `n + 2` to `n + 1`. -/
theorem cobarTensorHomotopy_mem_tensorPower (G : InternalGrading R A ℤ) (n : ℕ)
    {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ LinearMap.range
      (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n + 2))) :
    cobarTensorHomotopy G z ∈ LinearMap.range
      (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n + 1)) := by
  obtain ⟨t, rfl⟩ := hz
  induction t using PiTensorProduct.induction_on with
  | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
  | smul_tprod r x =>
    rw [map_smul, map_smul, TensorPower.toTensorAlgebra_tprod, cobarTensorHomotopy_tprod_add_two]
    exact Submodule.smul_mem _ r
      (ι_mul_mem_range_toTensorAlgebra _ ⟨PiTensorProduct.tprod R _,
        TensorPower.toTensorAlgebra_tprod _⟩)

/-! ### Contraction identities on `Ω⁺ Tᶜ(sA)` -/

private theorem cobarDeconcatDifferential_comp_cobarTensorIncl (G : InternalGrading R A ℤ) :
    cobarDeconcatDifferential G ∘ₗ cobarTensorIncl G = 0 := by
  ext a
  simp [cobarTensorIncl_apply]

private theorem cobarTensorProj_comp_cobarTensorIncl (G : InternalGrading R A ℤ) :
    cobarTensorProj G ∘ₗ cobarTensorIncl G = LinearMap.id := by
  ext a
  simp [cobarTensorIncl_apply]

private theorem cobarTensorHomotopy_comp_cobarTensorIncl (G : InternalGrading R A ℤ) :
    cobarTensorHomotopy G ∘ₗ cobarTensorIncl G = 0 := by
  ext a
  simp [cobarTensorIncl_apply]

private theorem cobarTensorProj_comp_cobarTensorHomotopy (G : InternalGrading R A ℤ) :
    cobarTensorProj G ∘ₗ cobarTensorHomotopy G = 0 := by
  refine tensorAlgebra_linearMap_ext fun n x ↦ ?_
  rcases n with _ | _ | k
  · simp
  · simp
  · rw [LinearMap.comp_apply, LinearMap.zero_apply, cobarTensorHomotopy_tprod_add_two]
    cases k with
    | zero => simp [TensorAlgebra.tprod_apply]
    | succ m =>
      rw [tprod_succ]
      exact cobarTensorProj_mul_ι_mul G _ _ _

private theorem cobarTensorHomotopy_comp_self (G : InternalGrading R A ℤ) :
    cobarTensorHomotopy G ∘ₗ cobarTensorHomotopy G = 0 := by
  refine tensorAlgebra_linearMap_ext fun n x ↦ ?_
  rcases n with _ | _ | k
  · simp
  · simp
  · rw [LinearMap.comp_apply, LinearMap.zero_apply, cobarTensorHomotopy_tprod_add_two]
    exact cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (ReducedTensorWords.letter_prepend _ _) _

/-- Case B of the contracting homotopy identity: when the leading generator is a prepended word
`a · w`, `h` kills `ι (a · w) * y` and `h (δ₀ (ι (a · w) * y)) = ι (a · w) * y`. -/
private theorem cobarDeconcatDifferential_homotopy_prepend (G : InternalGrading R A ℤ) (a : A)
    (w : ReducedTensorWords R A) (y : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarDeconcatDifferential G
          (cobarTensorHomotopy G (ι R (ReducedTensorWords.prepend R A a w) * y)) +
        cobarTensorHomotopy G
          (cobarDeconcatDifferential G (ι R (ReducedTensorWords.prepend R A a w) * y)) =
      ι R (ReducedTensorWords.prepend R A a w) * y -
        cobarTensorIncl G (cobarTensorProj G (ι R (ReducedTensorWords.prepend R A a w) * y)) := by
  have hproj : cobarTensorProj G (ι R (ReducedTensorWords.prepend R A a w) * y) = 0 := by
    let L : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] A :=
      cobarTensorProj G ∘ₗ LinearMap.mulLeft R (ι R (ReducedTensorWords.prepend R A a w))
    suffices h : L = 0 from LinearMap.congr_fun h y
    refine tensorAlgebra_linearMap_ext fun n u ↦ ?_
    cases n with
    | zero => simp [L, TensorAlgebra.tprod_apply]
    | succ k =>
      simp only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply, tprod_succ]
      exact cobarTensorProj_mul_ι_mul G _ _ _
  have hh1 : cobarTensorHomotopy G (ι R (ReducedTensorWords.prepend R A a w) * y) = 0 :=
    cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (ReducedTensorWords.letter_prepend a w) y
  have hh2 : cobarTensorHomotopy G (InternalGrading.koszulTwistAlgEquiv
      (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1))) 1
        (ι R (ReducedTensorWords.prepend R A a w)) * cobarDeconcatDifferential G y) = 0 := by
    rw [InternalGrading.koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι]
    refine cobarTensorHomotopy_ι_mul_of_letter_eq_zero G ?_ _
    rw [InternalGrading.koszulTwist_shift]
    simp [letter_koszulTwist]
  have hh3 : cobarTensorHomotopy G (LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
      (TensorProduct.map
        (ι R ∘ₗ (ReducedTensorWords.grading (G.shift 1)).koszulTwist 1) (ι R)
        (LinearMap.rTensor (ReducedTensorWords R A) (ReducedTensorWords.prepend R A a)
          (ReducedTensorWords.deconcatenation R A w))) * y) = 0 := by
    induction ReducedTensorWords.deconcatenation R A w using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
        LinearMap.mul'_apply, mul_assoc]
      exact cobarTensorHomotopy_ι_mul_of_letter_eq_zero G
        (by rw [letter_koszulTwist, ReducedTensorWords.letter_prepend, map_zero]) _
    | add u v hu hv => simp only [map_add, add_mul, hu, hv, add_zero]
  rw [hh1, map_zero, zero_add, hproj, map_zero, sub_zero, cobarDeconcatDifferential_mul, map_add,
    hh2, add_zero, cobarDeconcatDifferential_ι, ReducedTensorWords.deconcatenation_prepend,
    map_add, map_add, add_mul, map_add, hh3, add_zero]
  simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply, mul_assoc,
    koszulTwist_ofLetter, cobarTensorHomotopy_ι_mul_ι_mul, ReducedTensorWords.letter_ofLetter,
    InternalGrading.koszulTwist_koszulTwist]

/-- Case A1 of the contracting homotopy identity: when the leading generator is a single letter
and the tail is nonempty (`ι w * u`), the cuts of `w` and the differential of `u` cancel between
`δ₀ h` and `h δ₀`. -/
private theorem cobarDeconcatDifferential_homotopy_ofLetter_mul_ι (G : InternalGrading R A ℤ)
    (a : A) (w : ReducedTensorWords R A) (u : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarDeconcatDifferential G
          (cobarTensorHomotopy G (ι R (ReducedTensorWords.ofLetter R A a) * (ι R w * u))) +
        cobarTensorHomotopy G
          (cobarDeconcatDifferential G (ι R (ReducedTensorWords.ofLetter R A a) * (ι R w * u))) =
      ι R (ReducedTensorWords.ofLetter R A a) * (ι R w * u) -
        cobarTensorIncl G
          (cobarTensorProj G (ι R (ReducedTensorWords.ofLetter R A a) * (ι R w * u))) := by
  set a' := (G.shift 1).koszulTwist 1 a
  set H := ReducedTensorWords.grading (G.shift 1)
  have hσ_a : InternalGrading.koszulTwistAlgEquiv (tensorAlgebraPiece (H.shift (-1))) 1
      (ι R (ReducedTensorWords.ofLetter R A a)) = -ι R (ReducedTensorWords.ofLetter R A a') := by
    rw [InternalGrading.koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι,
      InternalGrading.koszulTwist_shift]
    simp [H, koszulTwist_ofLetter, a']
  have hσ_w : InternalGrading.koszulTwistAlgEquiv (tensorAlgebraPiece (H.shift (-1))) 1 (ι R w) =
      -ι R (H.koszulTwist 1 w) := by
    rw [InternalGrading.koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι,
      InternalGrading.koszulTwist_shift]
    simp [H]
  have hσ_pre : InternalGrading.koszulTwistAlgEquiv (tensorAlgebraPiece (H.shift (-1))) 1
      (ι R (ReducedTensorWords.prepend R A a' w)) =
      -ι R (ReducedTensorWords.prepend R A a (H.koszulTwist 1 w)) := by
    rw [InternalGrading.koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι,
      InternalGrading.koszulTwist_shift]
    simp [H, koszulTwist_prepend, a']
  have hcut : cobarTensorHomotopy G (ι R (ReducedTensorWords.ofLetter R A a') *
        (cobarDeconcatDifferential G (ι R w) * u)) =
      LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
        (TensorProduct.map (ι R ∘ₗ H.koszulTwist 1) (ι R)
          (LinearMap.rTensor (ReducedTensorWords R A) (ReducedTensorWords.prepend R A a')
            (ReducedTensorWords.deconcatenation R A w))) * u := by
    rw [cobarDeconcatDifferential_ι]
    induction ReducedTensorWords.deconcatenation R A w using TensorProduct.inductionOn with
    | tmul x₁ x₂ =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
        LinearMap.mul'_apply, mul_assoc, cobarTensorHomotopy_ι_mul_ι_mul,
        ReducedTensorWords.letter_ofLetter, H, koszulTwist_prepend, a',
        InternalGrading.koszulTwist_koszulTwist]
    | add x₁ x₂ hx₁ hx₂ => simp only [map_add, add_mul, mul_add, hx₁, hx₂]
  rw [cobarTensorProj_mul_ι_mul, map_zero, sub_zero, cobarTensorHomotopy_ι_mul_ι_mul,
    ReducedTensorWords.letter_ofLetter, cobarDeconcatDifferential_mul, cobarDeconcatDifferential_ι,
    ReducedTensorWords.deconcatenation_prepend, map_add, map_add, add_mul, hσ_pre,
    cobarDeconcatDifferential_mul, cobarDeconcatDifferential_ι,
    ReducedTensorWords.deconcatenation_ofLetter, map_zero, map_zero, zero_mul, zero_add, hσ_a,
    cobarDeconcatDifferential_mul, hσ_w]
  simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply,
    koszulTwist_ofLetter, mul_add, neg_mul, mul_neg, map_add, map_neg, hcut,
    cobarTensorHomotopy_ι_mul_ι_mul, ReducedTensorWords.letter_ofLetter, a',
    InternalGrading.koszulTwist_koszulTwist, mul_assoc]
  abel

/-! ### The unperturbed contraction on the cobar augmentation ideal -/

namespace IsNonCounitalDGCoalgebra

variable {G : InternalGrading R A ℤ} {dC : Module.End R (ReducedTensorWords R A)}
  (hC : IsNonCounitalDGCoalgebra (ReducedTensorWords.grading (G.shift 1))
    (ReducedTensorWords.deconcatenation R A) dC)

private theorem cobarDeconcatDifferential_mem_augmentationIdeal
    (x : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarDeconcatDifferential G x ∈ hC.cobarAugmentation.augmentationIdeal := by
  rw [DGAlgAugmentation.mem_augmentationIdeal]
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp [cobarDeconcatDifferential]
  | ι c =>
    rw [cobarDeconcatDifferential_ι]
    induction ReducedTensorWords.deconcatenation R A c using TensorProduct.inductionOn with
    | tmul u v => simp
    | add u v hu hv => simp [hu, hv]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy =>
    rw [cobarDeconcatDifferential_mul, map_add, map_mul, map_mul, hx, hy, zero_mul, mul_zero,
      add_zero]

private theorem cobarTensorIncl_mem_augmentationIdeal (a : A) :
    cobarTensorIncl G a ∈ hC.cobarAugmentation.augmentationIdeal :=
  hC.ι_mem_cobarAugmentation_augmentationIdeal _

private theorem cobarTensorHomotopy_mem_augmentationIdeal
    (z : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorHomotopy G z ∈ hC.cobarAugmentation.augmentationIdeal := by
  let L : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] R :=
    hC.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap ∘ₗ cobarTensorHomotopy G
  have hL : L = 0 := by
    refine tensorAlgebra_linearMap_ext fun n x ↦ ?_
    rcases n with _ | _ | k
    · simp [L]
    · simp [L]
    · simp only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom,
        DGAlgHom.coe_toGradedAlgHom, cobarTensorHomotopy_tprod_add_two, map_mul,
        hC.cobarAugmentation_ι, zero_mul, LinearMap.zero_apply]
  rw [DGAlgAugmentation.mem_augmentationIdeal]
  simpa only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, GradedAlgHom.coe_toAlgHom,
    DGAlgHom.coe_toGradedAlgHom, LinearMap.zero_apply] using LinearMap.congr_fun hL z

private theorem cobarTensorProj_comp_cobarDeconcatDifferential (G : InternalGrading R A ℤ) :
    cobarTensorProj G ∘ₗ cobarDeconcatDifferential G = 0 := by
  let h0 := isNonCounitalDGCoalgebra_reducedTensorWords_zero G
  refine tensorAlgebra_linearMap_ext fun n x ↦ ?_
  cases n with
  | zero => simp [TensorAlgebra.tprod_apply, cobarDeconcatDifferential]
  | succ k =>
    rw [LinearMap.comp_apply, LinearMap.zero_apply, tprod_succ, cobarDeconcatDifferential_mul,
      map_add]
    have h1 : cobarTensorProj G (cobarDeconcatDifferential G (ι R (x 0)) *
        TensorAlgebra.tprod R (ReducedTensorWords R A) k (fun i ↦ x i.succ)) = 0 := by
      rw [cobarDeconcatDifferential_ι]
      induction ReducedTensorWords.deconcatenation R A (x 0) using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply, mul_assoc]
        exact cobarTensorProj_mul_ι_mul G _ _ _
      | add u v hu hv => simp only [map_add, add_mul, hu, hv, add_zero]
    have h2 : cobarTensorProj G (InternalGrading.koszulTwistAlgEquiv
        (tensorAlgebraPiece ((ReducedTensorWords.grading (G.shift 1)).shift (-1))) 1 (ι R (x 0)) *
        cobarDeconcatDifferential G
          (TensorAlgebra.tprod R (ReducedTensorWords R A) k (fun i ↦ x i.succ))) = 0 := by
      cases k with
      | zero => simp [TensorAlgebra.tprod_apply, cobarDeconcatDifferential]
      | succ m =>
        rw [InternalGrading.koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι]
        let S : Submodule R (TensorAlgebra R (ReducedTensorWords R A)) :=
          LinearMap.ker (cobarTensorProj G ∘ₗ LinearMap.mulLeft R
            (ι R (((ReducedTensorWords.grading (G.shift 1)).shift (-1)).koszulTwist 1 (x 0))))
        have hle : h0.cobarAugmentation.augmentationIdeal.toSubmodule ≤ S := by
          rw [h0.cobarAugmentation_augmentationIdeal_le_iff]
          intro r y
          rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply, tprod_succ]
          exact cobarTensorProj_mul_ι_mul G _ _ _
        exact hle (h0.cobarDeconcatDifferential_mem_augmentationIdeal _)
    rw [h1, h2, add_zero]

private theorem cobarDeconcatDifferential_homotopy_add_homotopy_cobarDeconcatDifferential
    {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    cobarDeconcatDifferential G (cobarTensorHomotopy G z) +
        cobarTensorHomotopy G (cobarDeconcatDifferential G z) =
      z - cobarTensorIncl G (cobarTensorProj G z) := by
  let L : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R]
      TensorAlgebra R (ReducedTensorWords R A) :=
    cobarDeconcatDifferential G ∘ₗ cobarTensorHomotopy G +
      cobarTensorHomotopy G ∘ₗ cobarDeconcatDifferential G -
      (LinearMap.id - cobarTensorIncl G ∘ₗ cobarTensorProj G)
  suffices h : hC.cobarAugmentation.augmentationIdeal.toSubmodule ≤ LinearMap.ker L by
    have hLz : L z = 0 := h hz
    simp only [L, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply, sub_eq_zero] at hLz
    exact hLz
  rw [hC.cobarAugmentation_augmentationIdeal_le_iff]
  intro n x
  rw [LinearMap.mem_ker, tprod_succ]
  suffices hcy : ∀ (c : ReducedTensorWords R A) (y : TensorAlgebra R (ReducedTensorWords R A)),
      L (ι R c * y) = 0 from hcy (x 0) _
  intro c y
  let f : ReducedTensorWords R A →ₗ[R] TensorAlgebra R (ReducedTensorWords R A) :=
    L ∘ₗ LinearMap.mulRight R y ∘ₗ ι R
  suffices hf : f = 0 from LinearMap.congr_fun hf c
  refine reducedTensorWords_linearMap_ext_ofLetter_prepend (fun a ↦ ?_) fun a w ↦ ?_
  · let g : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R]
        TensorAlgebra R (ReducedTensorWords R A) :=
      L ∘ₗ LinearMap.mulLeft R (ι R (ReducedTensorWords.ofLetter R A a))
    suffices hg : g = 0 from LinearMap.congr_fun hg y
    refine tensorAlgebra_linearMap_ext fun m u ↦ ?_
    cases m with
    | zero =>
      simp only [g, L, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply, TensorAlgebra.tprod_apply,
        List.ofFn_zero, List.prod_nil, mul_one, cobarTensorHomotopy_ι, map_zero,
        cobarDeconcatDifferential_ι, ReducedTensorWords.deconcatenation_ofLetter,
        cobarTensorProj_ι, ReducedTensorWords.letter_ofLetter, cobarTensorIncl_apply,
        InternalGrading.koszulTwist_koszulTwist, add_zero, sub_self]
    | succ k =>
      simp only [g, L, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply, tprod_succ,
        cobarDeconcatDifferential_homotopy_ofLetter_mul_ι, sub_self]
  · simp only [f, L, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply,
      cobarDeconcatDifferential_homotopy_prepend, sub_self]

/-- The unperturbed cobar differential `δ₀` restricted to the cobar augmentation ideal `Ω⁺ Tᶜ(sA)`.
-/
noncomputable def cobarDeconcatReducedDifferential :
    Module.End R hC.cobarAugmentation.augmentationIdeal.toSubmodule :=
  (cobarDeconcatDifferential G).restrict fun x _ ↦
    hC.cobarDeconcatDifferential_mem_augmentationIdeal x

@[simp]
theorem coe_cobarDeconcatReducedDifferential
    (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    (hC.cobarDeconcatReducedDifferential x : TensorAlgebra R (ReducedTensorWords R A)) =
      cobarDeconcatDifferential G x := (rfl)

@[simp]
theorem cobarDeconcatReducedDifferential_comp_self :
    hC.cobarDeconcatReducedDifferential ∘ₗ hC.cobarDeconcatReducedDifferential = 0 := by
  ext x
  exact LinearMap.congr_fun (cobarDeconcatDifferential_comp_self G) x

/-- **The unperturbed bar--cobar contraction.**  For any noncounital DG coalgebra structure on
`Tᶜ(sA)`, the augmentation ideal `Ω⁺ Tᶜ(sA)` equipped with the deconcatenation differential `δ₀`
admits an explicit homogeneous special contraction onto `(A, 0)`. -/
noncomputable def cobarUnperturbedContraction :
    LinearSpecialContraction hC.cobarDeconcatReducedDifferential (0 : Module.End R A) where
  incl := (cobarTensorIncl G).codRestrict _ hC.cobarTensorIncl_mem_augmentationIdeal
  proj := cobarTensorProj G ∘ₗ hC.cobarAugmentation.augmentationIdeal.toSubmodule.subtype
  homotopy := (cobarTensorHomotopy G).restrict fun x _ ↦
    hC.cobarTensorHomotopy_mem_augmentationIdeal x
  dM_comp_incl := LinearMap.ext fun a ↦ Subtype.ext <| by
    simpa [cobarDeconcatReducedDifferential] using
      LinearMap.congr_fun (cobarDeconcatDifferential_comp_cobarTensorIncl G) a
  proj_comp_dM := LinearMap.ext fun x ↦ by
    simpa [cobarDeconcatReducedDifferential] using
      LinearMap.congr_fun (cobarTensorProj_comp_cobarDeconcatDifferential G) x
  proj_comp_incl := cobarTensorProj_comp_cobarTensorIncl G
  dM_comp_homotopy_add_homotopy_comp_dM := LinearMap.ext fun x ↦ Subtype.ext <|
    hC.cobarDeconcatDifferential_homotopy_add_homotopy_cobarDeconcatDifferential x.property
  homotopy_comp_incl := LinearMap.ext fun a ↦ Subtype.ext <| by
    simpa using LinearMap.congr_fun (cobarTensorHomotopy_comp_cobarTensorIncl G) a
  proj_comp_homotopy := LinearMap.ext fun x ↦ by
    simpa using LinearMap.congr_fun (cobarTensorProj_comp_cobarTensorHomotopy G) x
  homotopy_comp_homotopy := LinearMap.ext fun x ↦ Subtype.ext <| by
    simpa using LinearMap.congr_fun (cobarTensorHomotopy_comp_self G) x

@[simp]
theorem coe_cobarUnperturbedContraction_incl (a : A) :
    (hC.cobarUnperturbedContraction.incl a : TensorAlgebra R (ReducedTensorWords R A)) =
      cobarTensorIncl G a := (rfl)

@[simp]
theorem cobarUnperturbedContraction_proj_apply
    (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    hC.cobarUnperturbedContraction.proj x = cobarTensorProj G x := (rfl)

@[simp]
theorem coe_cobarUnperturbedContraction_homotopy
    (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    (hC.cobarUnperturbedContraction.homotopy x : TensorAlgebra R (ReducedTensorWords R A)) =
      cobarTensorHomotopy G x := (rfl)

/-- The inclusion of the unperturbed cobar contraction has degree zero. -/
theorem isHomogeneous_cobarUnperturbedContraction_incl :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.incl
      G.piece hC.cobarReducedGrading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦
    hC.mem_cobarReducedGrading_piece.2 ((isHomogeneous_cobarTensorIncl G).map_mem ha)

/-- The projection of the unperturbed cobar contraction has degree zero. -/
theorem isHomogeneous_cobarUnperturbedContraction_proj :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.proj
      hC.cobarReducedGrading.piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    (isHomogeneous_cobarTensorProj G).map_mem (hC.mem_cobarReducedGrading_piece.1 hx)

/-- The homotopy of the unperturbed cobar contraction has degree `-1`. -/
theorem isHomogeneous_cobarUnperturbedContraction_homotopy :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.homotopy
      hC.cobarReducedGrading.piece hC.cobarReducedGrading.piece (-1) :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    hC.mem_cobarReducedGrading_piece.2
      ((isHomogeneous_cobarTensorHomotopy G).map_mem (hC.mem_cobarReducedGrading_piece.1 hx))

end IsNonCounitalDGCoalgebra

end TauCeti
