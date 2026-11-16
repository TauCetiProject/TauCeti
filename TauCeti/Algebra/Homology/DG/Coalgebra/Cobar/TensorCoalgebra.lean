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

For a `ℤ`-graded module `(A, G)` over a commutative ring `R`, the reduced tensor coalgebra `Tᶜ(sA)`
with reduced deconcatenation and zero differential induces `δ₀` on `Ω Tᶜ(sA)`.  We construct an
explicit homogeneous special contraction of `(Ω⁺ Tᶜ(sA), δ₀)` onto `(A, 0)`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Springer (2012), Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemp. Math. 406 (2006), §4.
-/

public section

open scoped TensorProduct
open TensorAlgebra

namespace TauCeti

open ReducedTensorWords (of ofLetter prepend letter deconcatenation grading gradedPiece
  grading_piece isHomogeneous_letter letter_ofLetter letter_prepend deconcatenation_prepend
  deconcatenation_ofLetter koszulTwist_grading map_ofLetter map_prepend)
open InternalGrading (shift_piece koszulTwist_shift koszulTwist_koszulTwist koszulTwistAlgEquiv)

universe uR uA uC

section GeneralCobar

variable {R : Type uR} {C : Type uC} [CommRing R] [AddCommGroup C] [Module R C]

/-- The graded Leibniz rule for `cobarDifferential`, expressed globally via the Koszul twist. -/
theorem cobarDifferential_mul_koszulTwist (G : InternalGrading R C ℤ)
    (Δ : C →ₗ[R] C ⊗[R] C) (d : C →ₗ[R] C) (x y : TensorAlgebra R C) :
    cobarDifferential G Δ d (x * y) =
      cobarDifferential G Δ d x * y +
        koszulTwistAlgEquiv (tensorAlgebraPiece (G.shift (-1))) 1 x *
          cobarDifferential G Δ d y := by
  let D := cobarDifferential G Δ d
  let K := koszulTwistAlgEquiv (tensorAlgebraPiece (G.shift (-1))) 1
  refine LinearMap.congr_fun ((InternalGrading.ofDecomposition (tensorAlgebraPiece (G.shift (-1))))
    |>.linearMap_ext (f := D ∘ₗ LinearMap.mulRight R y)
      (g := LinearMap.mulRight R y ∘ₗ D + LinearMap.mulRight R (D y) ∘ₗ K.toLinearMap)
      fun _ _ hz ↦ ?_) x
  rw [InternalGrading.ofDecomposition_piece] at hz
  simp only [D, K, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.mulRight_apply,
    AlgEquiv.toLinearMap_apply, cobarDifferential_mul _ _ _ hz,
    InternalGrading.koszulTwistAlgEquiv_apply_of_mem _ 1 hz, one_mul, smul_mul_assoc]

/-- An odd derivation of `Ω C` mapping generators into `Ω⁺ C` maps all of `Ω C` into `Ω⁺ C`. -/
theorem IsNonCounitalDGCoalgebra.cobarAugmentation_derivation_eq_zero
    {G : InternalGrading R C ℤ} {Δ : C →ₗ[R] C ⊗[R] C} {d : C →ₗ[R] C}
    (hC : IsNonCounitalDGCoalgebra G Δ d) {f : C →ₗ[R] TensorAlgebra R C}
    (hf : ∀ c, hC.cobarAugmentation (f c) = 0) (x : TensorAlgebra R C) :
    hC.cobarAugmentation (tensorAlgebraDerivation (G.shift (-1)) f x) = 0 := by
  induction x using TensorAlgebra.induction with
  | algebraMap _ => simp
  | ι c => simp [hf c]
  | add _ _ hx hy => simp [hx, hy]
  | mul _ _ hx hy => simp [tensorAlgebraDerivation_mul, hx, hy]

end GeneralCobar

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

private theorem reducedTensorWords_linearMap_ext_ofLetter_prepend {N : Type*}
    [AddCommGroup N] [Module R N] {f g : ReducedTensorWords R A →ₗ[R] N}
    (h1 : ∀ a, f (ofLetter R A a) = g (ofLetter R A a))
    (h2 : ∀ a w, f (prepend R A a w) = g (prepend R A a w)) : f = g :=
  ReducedTensorWords.linearMap_ext R A fun ⟨n, hn⟩ x ↦ by match n with
    | 0 => omega
    | 1 => rw [show of R A ⟨1, hn⟩ (PiTensorProduct.tprod R x) = ofLetter R A (x 0) by
        rw [ReducedTensorWords.ofLetter_eq_of_tprod]
        exact ReducedTensorWords.of_tprod_congr R A hn rfl fun i ↦ by fin_cases i; rfl, h1]
    | k + 2 => rw [show of R A ⟨k + 2, hn⟩ (PiTensorProduct.tprod R x) = prepend R A (x 0)
        (of R A ⟨k + 1, Nat.succ_pos k⟩ (PiTensorProduct.tprod R fun i ↦ x i.succ)) by
        rw [ReducedTensorWords.prepend_of_tprod]
        exact ReducedTensorWords.of_tprod_congr R A hn rfl fun i ↦ by
          cases i using Fin.cases <;> simp, h2]

private theorem tensorAlgebra_linearMap_ext {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {f g : TensorAlgebra R M →ₗ[R] N}
    (h : ∀ (n : ℕ) (x : Fin n → M), f (tprod R M n x) = g (tprod R M n x)) : f = g := by
  refine LinearMap.ext fun z ↦ ?_; rw [← ofDirectSum_toDirectSum z]
  induction toDirectSum z using DirectSum.induction_on with
  | zero => simp
  | add _ _ hu hv => simp only [map_add, hu, hv]
  | of n t => induction t using PiTensorProduct.induction_on with
    | add _ _ hu hv => simp only [map_add, hu, hv]
    | smul_tprod _ x => simp only [DirectSum.of_smul, map_smul, ofDirectSum_of_tprod, h n x]

private theorem tprod_succ {M : Type*} [AddCommMonoid M] [Module R M] (n : ℕ)
    (x : Fin (n + 1) → M) : tprod R M (n + 1) x = ι R (x 0) * tprod R M n (fun i ↦ x i.succ) := by
  simp [tprod_apply, List.ofFn_succ]

private theorem tprod_cons {M : Type*} [AddCommMonoid M] [Module R M] {n : ℕ} (c : M)
    (x : Fin n → M) : tprod R M (n + 1) (Fin.cons c x) = ι R c * tprod R M n x := by simp

theorem ι_mul_mem_range_toTensorAlgebra {M : Type*} [AddCommMonoid M] [Module R M]
    (c : M) {n : ℕ} {y : TensorAlgebra R M}
    (hy : y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n))) :
    ι R c * y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n + 1)) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | add _ _ hu hv => simpa only [map_add, mul_add] using Submodule.add_mem _ hu hv
  | smul_tprod r x =>
    rw [map_smul, mul_smul_comm, TensorPower.toTensorAlgebra_tprod]
    exact Submodule.smul_mem _ r ⟨PiTensorProduct.tprod R (Fin.cons c x), by
      rw [TensorPower.toTensorAlgebra_tprod, tprod_cons]⟩

section UnperturbedCobar

variable (G : InternalGrading R A ℤ)

private theorem letter_koszulTwist (c : ReducedTensorWords R A) :
    letter R A ((grading (G.shift 1)).koszulTwist 1 c) =
      (G.shift 1).koszulTwist 1 (letter R A c) := by
  have h := isHomogeneous_letter (G.shift 1); rw [← grading_piece] at h
  simpa using (h.koszulTwist_apply 1 c).symm

private theorem koszulTwistAlgEquiv_ι (c : ReducedTensorWords R A) :
    koszulTwistAlgEquiv (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) 1 (ι R c) =
      -ι R ((grading (G.shift 1)).koszulTwist 1 c) := by
  rw [InternalGrading.koszulTwistAlgEquiv_apply, koszulTwist_tensorAlgebraPiece_ι,
    koszulTwist_shift]; simp

/-- `Tᶜ(sA)` with reduced deconcatenation and zero differential is a noncounital DG coalgebra. -/
theorem isNonCounitalDGCoalgebra_reducedTensorWords_zero :
    IsNonCounitalDGCoalgebra (grading (G.shift 1)) (deconcatenation R A)
      (0 : Module.End R (ReducedTensorWords R A)) where
  coassoc := ReducedTensorWords.deconcatenation_coassoc R A
  isHomogeneous_comul := ReducedTensorWords.isHomogeneous_deconcatenation _
  map_mem _ := zero_mem _
  sq_zero _ := rfl
  comul_differential := by ext x; simp

/-- The unperturbed cobar differential `δ₀` on `Ω Tᶜ(sA)` (zero internal differential). -/
noncomputable def cobarDeconcatDifferential :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  cobarDifferential (grading (G.shift 1)) (deconcatenation R A) 0

@[simp] theorem cobarDeconcatDifferential_ι (c : ReducedTensorWords R A) :
    cobarDeconcatDifferential G (ι R c) =
      LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
        (TensorProduct.map (ι R ∘ₗ (grading (G.shift 1)).koszulTwist 1) (ι R)
          (deconcatenation R A c)) := by simp [cobarDeconcatDifferential]

@[simp] theorem cobarDeconcatDifferential_algebraMap (r : R) :
    cobarDeconcatDifferential G (algebraMap R (TensorAlgebra R (ReducedTensorWords R A)) r) = 0 :=
  cobarDifferential_algebraMap _ _ _ r

theorem cobarDeconcatDifferential_mul (x y : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarDeconcatDifferential G (x * y) =
      cobarDeconcatDifferential G x * y +
        koszulTwistAlgEquiv (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) 1 x *
          cobarDeconcatDifferential G y :=
  cobarDifferential_mul_koszulTwist _ _ _ x y

@[simp] theorem cobarDeconcatDifferential_comp_self :
    cobarDeconcatDifferential G ∘ₗ cobarDeconcatDifferential G = 0 :=
  LinearMap.ext fun x ↦
    (isNonCounitalDGCoalgebra_reducedTensorWords_zero G).cobarDifferential_cobarDifferential x

/-- The canonical inclusion `A →ₗ Ω Tᶜ(sA)`, sending `a` to `(-1) ^ |sa| s⁻¹ [a]`. -/
noncomputable def cobarTensorIncl : A →ₗ[R] TensorAlgebra R (ReducedTensorWords R A) :=
  ι R ∘ₗ ofLetter R A ∘ₗ (G.shift 1).koszulTwist 1

theorem cobarTensorIncl_apply (a : A) :
    cobarTensorIncl G a = ι R (ofLetter R A ((G.shift 1).koszulTwist 1 a)) := (rfl)

theorem isHomogeneous_cobarTensorIncl :
    LinearMap.IsHomogeneous (cobarTensorIncl G) G.piece
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦ by
    rw [add_zero, cobarTensorIncl_apply]; refine ι_mem_tensorAlgebraPiece _ ?_
    rw [shift_piece, grading_piece]
    exact ReducedTensorWords.ofLetter_mem_gradedPiece (G.shift 1)
      ((G.shift 1).koszulTwist_mem_piece (by simpa [shift_piece] using ha) 1)

/-- The canonical projection `Ω Tᶜ(sA) →ₗ A` onto single-letter words of tensor length one. -/
noncomputable def cobarTensorProj : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] A :=
  (G.shift 1).koszulTwist 1 ∘ₗ letter R A ∘ₗ
    (TensorPower.oneEquiv R (ReducedTensorWords R A)).toLinearMap ∘ₗ tensorPowerProjection 1

theorem cobarTensorProj_tprod (n : ℕ) (x : Fin n → ReducedTensorWords R A) :
    cobarTensorProj G (tprod R (ReducedTensorWords R A) n x) =
      if h : n = 1 then (G.shift 1).koszulTwist 1 (letter R A (x ⟨0, by omega⟩)) else 0 := by
  simp only [cobarTensorProj, LinearMap.comp_apply, tensorPowerProjection_tprod]
  split_ifs with h
  · subst h; simp only [TensorPower.cast_refl, LinearEquiv.refl_apply, LinearEquiv.coe_coe,
      TensorPower.oneEquiv_tprod]; rfl
  · simp

@[simp] theorem cobarTensorProj_ι (c : ReducedTensorWords R A) :
    cobarTensorProj G (ι R c) = (G.shift 1).koszulTwist 1 (letter R A c) := by
  rw [show ι R c = tprod R _ 1 (fun _ ↦ c) by simp [tprod_apply], cobarTensorProj_tprod]; simp

private theorem cobarTensorProj_mul_ι_mul (c₀ c₁ : ReducedTensorWords R A)
    (z : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorProj G (ι R c₀ * (ι R c₁ * z)) = 0 :=
  LinearMap.congr_fun (tensorAlgebra_linearMap_ext
    (f := cobarTensorProj G ∘ₗ LinearMap.mulLeft R (ι R c₀) ∘ₗ LinearMap.mulLeft R (ι R c₁))
    (g := 0) fun n _ ↦ by simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.zero_apply, ← tprod_cons, cobarTensorProj_tprod, show n + 2 ≠ 1 by omega,
      ↓reduceDIte]) z

private theorem cobarTensorProj_ι_prepend_mul (a : A) (w : ReducedTensorWords R A)
    (y : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorProj G (ι R (prepend R A a w) * y) = 0 :=
  LinearMap.congr_fun (tensorAlgebra_linearMap_ext
    (f := cobarTensorProj G ∘ₗ LinearMap.mulLeft R (ι R (prepend R A a w))) (g := 0) fun n _ ↦ by
      cases n with
      | zero => simp [tprod_apply]
      | succ _ => simpa [tprod_succ] using cobarTensorProj_mul_ι_mul G _ _ _) y

theorem isHomogeneous_cobarTensorProj :
    LinearMap.IsHomogeneous (cobarTensorProj G)
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun p _ hz ↦ by
    rw [add_zero]
    refine tensorAlgebraPiece_le (C := (G.piece p).comap (cobarTensorProj G))
      (fun n d x hx hd ↦ ?_) hz
    rw [Submodule.mem_comap, cobarTensorProj_tprod]; split_ifs with hn
    · subst hn
      have hl := isHomogeneous_letter (G.shift 1); rw [← grading_piece] at hl
      have h0 : letter R A (x 0) ∈ (G.shift 1).piece (p - 1) := by
        simpa only [add_zero] using hl.map_mem (show x 0 ∈ (grading (G.shift 1)).piece (p - 1) by
          simpa [show d 0 = p by simpa using hd, shift_piece, sub_eq_add_neg] using hx 0)
      simpa [shift_piece] using (G.shift 1).koszulTwist_mem_piece h0 1
    · exact zero_mem _

private noncomputable def cobarTensorHomotopyComp :
    ∀ n : ℕ, TensorPower R n (ReducedTensorWords R A) →ₗ[R]
      TensorAlgebra R (ReducedTensorWords R A)
  | 0 | 1 => 0
  | k + 2 =>
    LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A)) ∘ₗ
      TensorProduct.map
        (ι R ∘ₗ TensorProduct.lift ((prepend R A).comp ((G.shift 1).koszulTwist 1 ∘ₗ letter R A)) ∘ₗ
          TensorProduct.map (TensorPower.oneEquiv R _).toLinearMap
            (TensorPower.oneEquiv R _).toLinearMap ∘ₗ _root_.TensorPower.splitAt R _ 2 1 (by omega))
        _root_.TensorPower.toTensorAlgebra ∘ₗ _root_.TensorPower.splitAt R _ (k + 2) 2 (by omega)

/-- The unperturbed contracting homotopy on `Ω Tᶜ(sA)`, joining the first two factors when the
first is a single letter. -/
noncomputable def cobarTensorHomotopy :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  DirectSum.toModule R ℕ (TensorAlgebra R (ReducedTensorWords R A)) (cobarTensorHomotopyComp G) ∘ₗ
    toDirectSum.toLinearMap

private theorem cobarTensorHomotopy_tprod (n : ℕ) (x : Fin n → ReducedTensorWords R A) :
    cobarTensorHomotopy G (tprod R (ReducedTensorWords R A) n x) =
      cobarTensorHomotopyComp G n (PiTensorProduct.tprod R x) := by
  simp only [cobarTensorHomotopy, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]

theorem cobarTensorHomotopy_tprod_zero (x : Fin 0 → ReducedTensorWords R A) :
    cobarTensorHomotopy G (tprod R (ReducedTensorWords R A) 0 x) = 0 :=
  cobarTensorHomotopy_tprod G 0 x

@[simp] theorem cobarTensorHomotopy_one : cobarTensorHomotopy G 1 = 0 := by
  rw [show (1 : TensorAlgebra R _) = tprod R _ 0 Fin.elim0 by simp [tprod_apply],
    cobarTensorHomotopy_tprod_zero]

theorem cobarTensorHomotopy_tprod_one (x : Fin 1 → ReducedTensorWords R A) :
    cobarTensorHomotopy G (tprod R (ReducedTensorWords R A) 1 x) = 0 :=
  cobarTensorHomotopy_tprod G 1 x

@[simp] theorem cobarTensorHomotopy_ι (c : ReducedTensorWords R A) :
    cobarTensorHomotopy G (ι R c) = 0 := by
  rw [show ι R c = tprod R _ 1 (fun _ ↦ c) by simp [tprod_apply], cobarTensorHomotopy_tprod_one]

theorem cobarTensorHomotopy_tprod_add_two (k : ℕ) (x : Fin (k + 2) → ReducedTensorWords R A) :
    cobarTensorHomotopy G (tprod R (ReducedTensorWords R A) (k + 2) x) =
      ι R (prepend R A ((G.shift 1).koszulTwist 1 (letter R A (x 0))) (x 1)) *
        tprod R (ReducedTensorWords R A) k (fun j ↦ x j.succ.succ) := by
  rw [cobarTensorHomotopy_tprod]
  simp only [cobarTensorHomotopyComp, LinearMap.comp_apply, _root_.TensorPower.splitAt_tprod,
    TensorProduct.map_tmul, LinearMap.mul'_apply, TensorPower.toTensorAlgebra_tprod]
  congr 1
  · rw [_root_.TensorPower.splitAt_tprod, TensorProduct.map_tmul]
    simp only [LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, TensorProduct.lift.tmul]
    rw [TensorPower.oneEquiv_tprod, TensorPower.oneEquiv_tprod]; congr 1
  · exact congrArg _ (funext fun j ↦ congrArg x (Fin.ext (by simp; omega)))

private theorem comp_cobarTensorHomotopy_eq_zero {N : Type*} [AddCommMonoid N] [Module R N]
    {f : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] N}
    (h : ∀ a w y, f (ι R (prepend R A a w) * y) = 0) :
    f ∘ₗ cobarTensorHomotopy G = 0 :=
  tensorAlgebra_linearMap_ext fun n _ ↦ by match n with
    | 0 => simp
    | 1 => simp
    | _ + 2 => rw [LinearMap.comp_apply, LinearMap.zero_apply, cobarTensorHomotopy_tprod_add_two, h]

theorem cobarTensorHomotopy_ι_mul_ι_mul (c₀ c₁ : ReducedTensorWords R A)
    (z : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorHomotopy G (ι R c₀ * (ι R c₁ * z)) =
      ι R (prepend R A ((G.shift 1).koszulTwist 1 (letter R A c₀)) c₁) * z :=
  LinearMap.congr_fun (tensorAlgebra_linearMap_ext
    (f := cobarTensorHomotopy G ∘ₗ LinearMap.mulLeft R (ι R c₀) ∘ₗ LinearMap.mulLeft R (ι R c₁))
    (g := LinearMap.mulLeft R (ι R (prepend R A ((G.shift 1).koszulTwist 1 (letter R A c₀)) c₁)))
    fun _ _ ↦ by simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← tprod_cons,
      cobarTensorHomotopy_tprod_add_two]; simp) z

private theorem cobarTensorHomotopy_ι_mul_of_letter_eq_zero {c : ReducedTensorWords R A}
    (hc : letter R A c = 0) (y : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorHomotopy G (ι R c * y) = 0 :=
  LinearMap.congr_fun (tensorAlgebra_linearMap_ext
    (f := cobarTensorHomotopy G ∘ₗ LinearMap.mulLeft R (ι R c)) (g := 0) fun n _ ↦ by cases n with
      | zero => simp [tprod_apply]
      | succ _ => simp [cobarTensorHomotopy_ι_mul_ι_mul, hc]) y

theorem isHomogeneous_cobarTensorHomotopy :
    LinearMap.IsHomogeneous (cobarTensorHomotopy G)
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1)))
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) (-1) := by
  let P := (grading (G.shift 1)).shift (-1)
  refine LinearMap.isHomogeneous_def.2 fun q _ hz ↦ tensorAlgebraPiece_le
    (C := (tensorAlgebraPiece P (q + -1)).comap (cobarTensorHomotopy G)) (fun n d x hx hd ↦ ?_) hz
  rw [Submodule.mem_comap]; match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
    rw [cobarTensorHomotopy_tprod_add_two]
    have hl := isHomogeneous_letter (G.shift 1); rw [← grading_piece] at hl
    have h0 : letter R A (x 0) ∈ (G.shift 1).piece (d 0 + -1) := by
      simpa only [add_zero] using hl.map_mem (by simpa [P] using hx 0)
    have hpre : prepend R A ((G.shift 1).koszulTwist 1 (letter R A (x 0))) (x 1) ∈
        P.piece (d 0 + d 1 + -1) := by
      rw [show P.piece (d 0 + d 1 + -1) = gradedPiece (G.shift 1) (d 0 + d 1 + -1 + -1) by
        simp [P, shift_piece, grading_piece]]
      exact (show (d 0 + -1) + (d 1 + -1) = d 0 + d 1 + -1 + -1 by ring) ▸
        ReducedTensorWords.prepend_mem_gradedPiece ((G.shift 1).koszulTwist_mem_piece h0 1)
          (by simpa [P, grading_piece] using hx 1)
    exact (show d 0 + d 1 + -1 + ∑ j : Fin k, d j.succ.succ = q + -1 by
      rw [← hd, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]; ring) ▸
      SetLike.GradedMul.mul_mem (ι_mem_tensorAlgebraPiece _ hpre)
        (tprod_mem_tensorAlgebraPiece _ _ _ fun j ↦ hx j.succ.succ)

theorem cobarTensorHomotopy_eq_zero_of_mem_tensorPower_one
    {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ LinearMap.range
      (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := 1))) :
    cobarTensorHomotopy G z = 0 := by
  obtain ⟨t, rfl⟩ := hz
  induction t using PiTensorProduct.induction_on with
  | add _ _ hu hv => simp [hu, hv]
  | smul_tprod _ _ => simp [TensorPower.toTensorAlgebra_tprod]

theorem cobarTensorHomotopy_mem_tensorPower (n : ℕ)
    {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ LinearMap.range
      (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n + 2))) :
    cobarTensorHomotopy G z ∈ LinearMap.range
      (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n + 1)) := by
  obtain ⟨t, rfl⟩ := hz
  induction t using PiTensorProduct.induction_on with
  | add _ _ hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
  | smul_tprod r _ =>
    rw [map_smul, map_smul, TensorPower.toTensorAlgebra_tprod, cobarTensorHomotopy_tprod_add_two]
    exact Submodule.smul_mem _ r (ι_mul_mem_range_toTensorAlgebra _
      ⟨PiTensorProduct.tprod R _, TensorPower.toTensorAlgebra_tprod _⟩)

end UnperturbedCobar

namespace IsNonCounitalDGCoalgebra

variable {G : InternalGrading R A ℤ} {dC : Module.End R (ReducedTensorWords R A)}
  (hC : IsNonCounitalDGCoalgebra (grading (G.shift 1)) (deconcatenation R A) dC)

private theorem cobarDeconcatDifferential_mem_augmentationIdeal
    (x : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarDeconcatDifferential G x ∈ hC.cobarAugmentation.augmentationIdeal := by
  rw [DGAlgAugmentation.mem_augmentationIdeal]
  induction x using TensorAlgebra.induction with
  | algebraMap _ => simp [cobarDeconcatDifferential]
  | ι c =>
    rw [cobarDeconcatDifferential_ι]
    induction deconcatenation R A c using TensorProduct.inductionOn with
    | tmul _ _ => simp
    | add _ _ hu hv => simp [hu, hv]
  | add _ _ hx hy => simp [hx, hy]
  | mul _ _ hx hy => simp [cobarDeconcatDifferential_mul, hx, hy]

private theorem cobarTensorHomotopy_mem_augmentationIdeal
    (z : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorHomotopy G z ∈ hC.cobarAugmentation.augmentationIdeal :=
  hC.cobarAugmentation.mem_augmentationIdeal.2 <| LinearMap.congr_fun
    (comp_cobarTensorHomotopy_eq_zero G
      (f := hC.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap) fun _ _ _ ↦ by simp) z

private theorem cobarDeconcatDifferential_homotopy_eq
    {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    cobarDeconcatDifferential G (cobarTensorHomotopy G z) +
        cobarTensorHomotopy G (cobarDeconcatDifferential G z) =
      z - cobarTensorIncl G (cobarTensorProj G z) := by
  let D := cobarDeconcatDifferential G; let H := cobarTensorHomotopy G
  let L : Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
    D ∘ₗ H + H ∘ₗ D - (LinearMap.id - cobarTensorIncl G ∘ₗ cobarTensorProj G)
  suffices h : hC.cobarAugmentation.augmentationIdeal.toSubmodule ≤ LinearMap.ker L by
    simpa [L, D, H, sub_eq_zero] using h hz
  refine hC.cobarAugmentation_augmentationIdeal_le_iff.2 fun _ x ↦ ?_
  rw [LinearMap.mem_ker, tprod_succ]
  suffices ∀ c y, L (ι R c * y) = 0 from this (x 0) _
  intro c y
  refine LinearMap.congr_fun (reducedTensorWords_linearMap_ext_ofLetter_prepend
    (f := L ∘ₗ LinearMap.mulRight R y ∘ₗ ι R) (g := 0) (fun a ↦ ?_) (fun a w ↦ ?_)) c
  · refine LinearMap.congr_fun (tensorAlgebra_linearMap_ext
      (f := L ∘ₗ LinearMap.mulLeft R (ι R (ofLetter R A a))) (g := 0) fun m u ↦ ?_) y
    cases m with
    | zero => simp [L, D, H, tprod_apply, cobarTensorIncl_apply]
    | succ k =>
      have hcut : H (ι R (ofLetter R A ((G.shift 1).koszulTwist 1 a)) *
          (D (ι R (u 0)) * tprod R (ReducedTensorWords R A) k (fun i ↦ u i.succ))) =
          LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
            (TensorProduct.map (ι R ∘ₗ ReducedTensorWords.map R ((G.shift 1).koszulTwist 1)) (ι R)
              (LinearMap.rTensor (ReducedTensorWords R A)
                (prepend R A ((G.shift 1).koszulTwist 1 a)) (deconcatenation R A (u 0)))) *
            tprod R (ReducedTensorWords R A) k (fun i ↦ u i.succ) := by
        rw [cobarDeconcatDifferential_ι]
        induction deconcatenation R A (u 0) using TensorProduct.inductionOn with
        | tmul _ _ =>
          simp only [H, LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
            LinearMap.mul'_apply, mul_assoc, cobarTensorHomotopy_ι_mul_ι_mul, letter_ofLetter,
            koszulTwist_grading, map_prepend, koszulTwist_koszulTwist]
        | add _ _ hx₁ hx₂ => simp only [map_add, add_mul, mul_add, hx₁, hx₂]
      simp only [L, D, H, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply, tprod_succ]
      rw [cobarTensorProj_mul_ι_mul, map_zero, sub_zero, cobarTensorHomotopy_ι_mul_ι_mul,
        letter_ofLetter, cobarDeconcatDifferential_mul, cobarDeconcatDifferential_ι,
        deconcatenation_prepend, map_add, map_add, add_mul, koszulTwistAlgEquiv_ι,
        cobarDeconcatDifferential_mul, cobarDeconcatDifferential_ι, deconcatenation_ofLetter,
        map_zero, map_zero, zero_mul, zero_add, koszulTwistAlgEquiv_ι,
        cobarDeconcatDifferential_mul, koszulTwistAlgEquiv_ι]
      simp only [D, H] at hcut
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply,
        koszulTwist_grading, map_ofLetter, map_prepend, mul_add, neg_mul, mul_neg, map_add,
        map_neg, hcut, cobarTensorHomotopy_ι_mul_ι_mul, letter_ofLetter,
        koszulTwist_koszulTwist, mul_assoc]; abel
  · have hh2 : H (koszulTwistAlgEquiv (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) 1
        (ι R (prepend R A a w)) * D y) = 0 := by
      rw [koszulTwistAlgEquiv_ι, neg_mul, map_neg, neg_eq_zero]
      exact cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (by simp [letter_koszulTwist]) _
    have hh3 : H (LinearMap.mul' R (TensorAlgebra R (ReducedTensorWords R A))
        (TensorProduct.map (ι R ∘ₗ (grading (G.shift 1)).koszulTwist 1) (ι R)
          (LinearMap.rTensor (ReducedTensorWords R A) (prepend R A a)
            (deconcatenation R A w))) * y) = 0 := by
      induction deconcatenation R A w using TensorProduct.inductionOn with
      | tmul _ _ =>
        simpa only [H, LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
          LinearMap.mul'_apply, mul_assoc] using cobarTensorHomotopy_ι_mul_of_letter_eq_zero G
          (by rw [letter_koszulTwist, letter_prepend, map_zero]) _
      | add _ _ hu hv => simp only [map_add, add_mul, hu, hv, add_zero]
    simp only [L, D, H, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.id_apply, LinearMap.zero_apply]
    rw [cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (letter_prepend a w) y, map_zero, zero_add,
      cobarTensorProj_ι_prepend_mul, map_zero, sub_zero, cobarDeconcatDifferential_mul, map_add,
      hh2, add_zero, cobarDeconcatDifferential_ι, deconcatenation_prepend, map_add, map_add,
      add_mul, map_add, hh3, add_zero]
    simp only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.mul'_apply, mul_assoc,
      koszulTwist_grading, map_ofLetter, cobarTensorHomotopy_ι_mul_ι_mul, letter_ofLetter,
      koszulTwist_koszulTwist, sub_self]

/-- The unperturbed cobar differential `δ₀` restricted to `Ω⁺ Tᶜ(sA)`. -/
noncomputable def cobarDeconcatReducedDifferential :
    Module.End R hC.cobarAugmentation.augmentationIdeal.toSubmodule :=
  (cobarDeconcatDifferential G).restrict fun x _ ↦
    hC.cobarDeconcatDifferential_mem_augmentationIdeal x

@[simp] theorem coe_cobarDeconcatReducedDifferential
    (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    (hC.cobarDeconcatReducedDifferential x : TensorAlgebra R (ReducedTensorWords R A)) =
      cobarDeconcatDifferential G x := (rfl)

@[simp] theorem cobarDeconcatReducedDifferential_comp_self :
    hC.cobarDeconcatReducedDifferential ∘ₗ hC.cobarDeconcatReducedDifferential = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun (cobarDeconcatDifferential_comp_self G) x)

/-- **The unperturbed bar--cobar contraction** of `(Ω⁺ Tᶜ(sA), δ₀)` onto `(A, 0)`. -/
noncomputable def cobarUnperturbedContraction :
    LinearSpecialContraction hC.cobarDeconcatReducedDifferential (0 : Module.End R A) where
  incl := (cobarTensorIncl G).codRestrict _ fun _ ↦ hC.ι_mem_cobarAugmentation_augmentationIdeal _
  proj := cobarTensorProj G ∘ₗ hC.cobarAugmentation.augmentationIdeal.toSubmodule.subtype
  homotopy := (cobarTensorHomotopy G).restrict fun x _ ↦
    hC.cobarTensorHomotopy_mem_augmentationIdeal x
  dM_comp_incl := LinearMap.ext fun _ ↦ Subtype.ext <| by
    change cobarDeconcatDifferential G (cobarTensorIncl G _) = cobarTensorIncl G 0
    simp [cobarTensorIncl_apply]
  proj_comp_dM := LinearMap.ext fun x ↦ LinearMap.congr_fun (tensorAlgebra_linearMap_ext
    (f := cobarTensorProj G ∘ₗ cobarDeconcatDifferential G) (g := 0) fun n y ↦ by cases n with
    | zero => simp [tprod_apply, cobarDeconcatDifferential]
    | succ k =>
      have h2 : cobarTensorProj G (ι R ((grading (G.shift 1)).koszulTwist 1 (y 0)) *
          cobarDeconcatDifferential G (tprod R _ k (fun i ↦ y i.succ))) = 0 :=
        (hC.cobarAugmentation_augmentationIdeal_le_iff
          (S := LinearMap.ker (cobarTensorProj G ∘ₗ LinearMap.mulLeft R _)).2 fun _ _ ↦ by
            rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply, tprod_succ]
            exact cobarTensorProj_mul_ι_mul G _ _ _)
          (hC.cobarDeconcatDifferential_mem_augmentationIdeal _)
      rw [LinearMap.comp_apply, LinearMap.zero_apply, tprod_succ, cobarDeconcatDifferential_mul,
        map_add, koszulTwistAlgEquiv_ι, neg_mul, map_neg, h2, neg_zero, add_zero,
        cobarDeconcatDifferential_ι]
      induction deconcatenation R A (y 0) using TensorProduct.inductionOn with
      | tmul _ _ => simpa [mul_assoc] using cobarTensorProj_mul_ι_mul G _ _ _
      | add _ _ hu hv => simp only [map_add, add_mul, hu, hv, add_zero]) x
  proj_comp_incl := LinearMap.ext fun _ ↦ by
    change cobarTensorProj G (cobarTensorIncl G _) = _; simp [cobarTensorIncl_apply]
  dM_comp_homotopy_add_homotopy_comp_dM := LinearMap.ext fun x ↦ Subtype.ext <|
    hC.cobarDeconcatDifferential_homotopy_eq x.property
  homotopy_comp_incl := LinearMap.ext fun _ ↦ Subtype.ext <| by
    change cobarTensorHomotopy G (cobarTensorIncl G _) = 0; simp [cobarTensorIncl_apply]
  proj_comp_homotopy := LinearMap.ext fun x ↦ LinearMap.congr_fun
    (comp_cobarTensorHomotopy_eq_zero G (f := cobarTensorProj G)
      (cobarTensorProj_ι_prepend_mul G)) x
  homotopy_comp_homotopy := LinearMap.ext fun x ↦ Subtype.ext <| LinearMap.congr_fun
    (comp_cobarTensorHomotopy_eq_zero G (f := cobarTensorHomotopy G) fun _ _ _ ↦
      cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (letter_prepend _ _) _) x

@[simp] theorem coe_cobarUnperturbedContraction_incl (a : A) :
    (hC.cobarUnperturbedContraction.incl a : TensorAlgebra R (ReducedTensorWords R A)) =
      cobarTensorIncl G a := (rfl)

@[simp] theorem cobarUnperturbedContraction_proj_apply
    (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    hC.cobarUnperturbedContraction.proj x = cobarTensorProj G x := (rfl)

@[simp] theorem coe_cobarUnperturbedContraction_homotopy
    (x : hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    (hC.cobarUnperturbedContraction.homotopy x : TensorAlgebra R (ReducedTensorWords R A)) =
      cobarTensorHomotopy G x := (rfl)

theorem isHomogeneous_cobarUnperturbedContraction_incl :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.incl
      G.piece hC.cobarReducedGrading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ ha ↦
    hC.mem_cobarReducedGrading_piece.2 ((isHomogeneous_cobarTensorIncl G).map_mem ha)

theorem isHomogeneous_cobarUnperturbedContraction_proj :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.proj
      hC.cobarReducedGrading.piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    (isHomogeneous_cobarTensorProj G).map_mem (hC.mem_cobarReducedGrading_piece.1 hx)

theorem isHomogeneous_cobarUnperturbedContraction_homotopy :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.homotopy
      hC.cobarReducedGrading.piece hC.cobarReducedGrading.piece (-1) :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ hC.mem_cobarReducedGrading_piece.2
    ((isHomogeneous_cobarTensorHomotopy G).map_mem (hC.mem_cobarReducedGrading_piece.1 hx))

end IsNonCounitalDGCoalgebra

end TauCeti
