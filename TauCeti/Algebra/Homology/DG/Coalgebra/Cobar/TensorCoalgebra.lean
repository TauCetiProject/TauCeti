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
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation
public import TauCeti.LinearAlgebra.TensorCoalgebra.Grading
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives
public import TauCeti.LinearAlgebra.TensorPower.Basic
import TauCeti.LinearAlgebra.TensorAlgebra.Basic

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
open LinearMap (comp_apply id_apply mulLeft_apply mul'_apply)

namespace TauCeti

open ReducedTensorWords (ofLetter prepend letter deconcatenation grading grading_piece
  isHomogeneous_letter letter_ofLetter letter_prepend deconcatenation_prepend
  deconcatenation_ofLetter koszulTwist_grading map_ofLetter map_prepend)
open InternalGrading (shift_piece koszulTwist_shift koszulTwist_koszulTwist koszulTwistAlgEquiv)

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

section UnperturbedCobar

private abbrev RTW (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] :=
  ReducedTensorWords R A
private abbrev ΩT (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] :=
  TensorAlgebra R (ReducedTensorWords R A)

variable (G : InternalGrading R A ℤ)

private theorem letter_koszulTwist (c : RTW R A) :
    letter R A ((grading (G.shift 1)).koszulTwist 1 c) =
      (G.shift 1).koszulTwist 1 (letter R A c) := by
  have h := isHomogeneous_letter (G.shift 1); rw [← grading_piece] at h
  simpa using (h.koszulTwist_apply 1 c).symm

private theorem koszulTwistAlgEquiv_ι (c : RTW R A) :
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
  map_mem _ := zero_mem _; sq_zero _ := rfl; comul_differential := by ext x; simp

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
          cobarDeconcatDifferential G y := cobarDifferential_mul_koszulTwist _ _ _ x y

@[simp] theorem cobarDeconcatDifferential_comp_self :
    cobarDeconcatDifferential G ∘ₗ cobarDeconcatDifferential G = 0 := LinearMap.ext fun x ↦
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
    rw [shift_piece, grading_piece]; exact ReducedTensorWords.ofLetter_mem_gradedPiece
      (G.shift 1) ((G.shift 1).koszulTwist_mem_piece (by simpa [shift_piece] using ha) 1)

/-- The canonical projection `Ω Tᶜ(sA) →ₗ A` onto single-letter words of tensor length one. -/
noncomputable def cobarTensorProj : TensorAlgebra R (ReducedTensorWords R A) →ₗ[R] A :=
  (G.shift 1).koszulTwist 1 ∘ₗ letter R A ∘ₗ
    (TensorPower.oneEquiv R (ReducedTensorWords R A)).toLinearMap ∘ₗ tensorPowerProjection 1

theorem cobarTensorProj_tprod (n : ℕ) (x : Fin n → ReducedTensorWords R A) :
    cobarTensorProj G (tprod R (ReducedTensorWords R A) n x) =
      if h : n = 1 then (G.shift 1).koszulTwist 1 (letter R A (x ⟨0, by omega⟩)) else 0 := by
  simp only [cobarTensorProj, comp_apply, tensorPowerProjection_tprod]; split_ifs with h
  exacts [by subst h; simp [TensorPower.oneEquiv_tprod], by simp]

@[simp] theorem cobarTensorProj_ι (c : ReducedTensorWords R A) :
    cobarTensorProj G (ι R c) = (G.shift 1).koszulTwist 1 (letter R A c) := by
  simpa [tprod_apply] using cobarTensorProj_tprod G 1 (fun _ ↦ c)

private theorem cobarTensorProj_mul_ι_mul (c₀ c₁ : RTW R A) (z : ΩT R A) :
    cobarTensorProj G (ι R c₀ * (ι R c₁ * z)) = 0 :=
  LinearMap.congr_fun (linearMap_ext_tprod (f := cobarTensorProj G ∘ₗ
      LinearMap.mulLeft R (ι R c₀) ∘ₗ LinearMap.mulLeft R (ι R c₁)) (g := 0) fun _ _ ↦ by
    simp only [comp_apply, mulLeft_apply, LinearMap.zero_apply, ← tprod_cons,
      cobarTensorProj_tprod]; simp) z

private theorem cobarTensorProj_ι_prepend_mul (a : A) (w : RTW R A) (y : ΩT R A) :
    cobarTensorProj G (ι R (prepend R A a w) * y) = 0 :=
  LinearMap.congr_fun (linearMap_ext_tprod (f := cobarTensorProj G ∘ₗ
      LinearMap.mulLeft R (ι R (prepend R A a w))) (g := 0) fun
    | 0, _ => by simp [tprod_apply]
    | _ + 1, _ => by simpa [tprod_succ_eq_ι_mul] using cobarTensorProj_mul_ι_mul G _ _ _) y

theorem isHomogeneous_cobarTensorProj :
    LinearMap.IsHomogeneous (cobarTensorProj G)
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun p _ hz ↦ by
    rw [add_zero]; refine tensorAlgebraPiece_le (C := (G.piece p).comap (cobarTensorProj G))
      (fun n d x hx hd ↦ by
        rw [Submodule.mem_comap, cobarTensorProj_tprod]; split_ifs with hn
        · subst hn; have hl := isHomogeneous_letter (G.shift 1); rw [← grading_piece] at hl
          have hd0 : d 0 = p := by simpa using hd
          have hx0 : x 0 ∈ (grading (G.shift 1)).piece (p - 1) := by
            simpa [hd0, shift_piece, sub_eq_add_neg] using hx 0
          simpa [shift_piece] using (G.shift 1).koszulTwist_mem_piece (hl.map_mem hx0) 1
        · exact zero_mem _) hz

private noncomputable def cobarTensorHomotopyComp :
    ∀ n : ℕ, TensorPower R n (RTW R A) →ₗ[R] ΩT R A
  | 0 | 1 => 0
  | k + 2 =>
    LinearMap.mul' R (ΩT R A) ∘ₗ TensorProduct.map
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

private theorem cobarTensorHomotopy_tprod (n : ℕ) (x : Fin n → RTW R A) :
    cobarTensorHomotopy G (tprod R (RTW R A) n x) =
      cobarTensorHomotopyComp G n (PiTensorProduct.tprod R x) := by
  simp only [cobarTensorHomotopy, comp_apply, AlgHom.toLinearMap_apply,
    toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R, DirectSum.toModule_lof]

theorem cobarTensorHomotopy_tprod_zero (x : Fin 0 → ReducedTensorWords R A) :
    cobarTensorHomotopy G (tprod R (ReducedTensorWords R A) 0 x) = 0 :=
  cobarTensorHomotopy_tprod G 0 x

@[simp] theorem cobarTensorHomotopy_one : cobarTensorHomotopy G 1 = 0 := by
  simpa [tprod_apply] using cobarTensorHomotopy_tprod_zero G Fin.elim0

theorem cobarTensorHomotopy_tprod_one (x : Fin 1 → ReducedTensorWords R A) :
    cobarTensorHomotopy G (tprod R (ReducedTensorWords R A) 1 x) = 0 :=
  cobarTensorHomotopy_tprod G 1 x

@[simp] theorem cobarTensorHomotopy_ι (c : ReducedTensorWords R A) :
    cobarTensorHomotopy G (ι R c) = 0 := by
  simpa [tprod_apply] using cobarTensorHomotopy_tprod_one G fun _ ↦ c

theorem cobarTensorHomotopy_tprod_add_two (k : ℕ) (x : Fin (k + 2) → ReducedTensorWords R A) :
    cobarTensorHomotopy G (tprod R (ReducedTensorWords R A) (k + 2) x) =
      ι R (prepend R A ((G.shift 1).koszulTwist 1 (letter R A (x 0))) (x 1)) *
        tprod R (ReducedTensorWords R A) k (fun j ↦ x j.succ.succ) := by
  simp only [cobarTensorHomotopy_tprod, cobarTensorHomotopyComp, comp_apply, mul'_apply,
    _root_.TensorPower.splitAt_tprod, TensorProduct.map_tmul, TensorPower.toTensorAlgebra_tprod]
  rw [_root_.TensorPower.splitAt_tprod, TensorProduct.map_tmul]
  exact congrArg₂ (· * ·) (by simp [TensorPower.oneEquiv_tprod]; congr 2)
    (congrArg _ (funext fun j ↦ congrArg x (Fin.ext (by simp; omega))))

private theorem comp_cobarTensorHomotopy_eq_zero {N : Type*} [AddCommMonoid N] [Module R N]
    {f : ΩT R A →ₗ[R] N} (h : ∀ a w y, f (ι R (prepend R A a w) * y) = 0) :
    f ∘ₗ cobarTensorHomotopy G = 0 := linearMap_ext_tprod fun
  | 0, _ | 1, _ => by simp
  | _ + 2, _ => by rw [comp_apply, LinearMap.zero_apply, cobarTensorHomotopy_tprod_add_two, h]

theorem cobarTensorHomotopy_ι_mul_ι_mul (c₀ c₁ : ReducedTensorWords R A)
    (z : TensorAlgebra R (ReducedTensorWords R A)) :
    cobarTensorHomotopy G (ι R c₀ * (ι R c₁ * z)) =
      ι R (prepend R A ((G.shift 1).koszulTwist 1 (letter R A c₀)) c₁) * z :=
  LinearMap.congr_fun (linearMap_ext_tprod
    (f := cobarTensorHomotopy G ∘ₗ LinearMap.mulLeft R (ι R c₀) ∘ₗ LinearMap.mulLeft R (ι R c₁))
    (g := LinearMap.mulLeft R (ι R (prepend R A ((G.shift 1).koszulTwist 1 (letter R A c₀)) c₁)))
    fun _ _ ↦ by simp only [comp_apply, mulLeft_apply, ← tprod_cons,
      cobarTensorHomotopy_tprod_add_two]; simp) z

private theorem cobarTensorHomotopy_ι_mul_of_letter_eq_zero {c : RTW R A} (hc : letter R A c = 0)
    (y : ΩT R A) : cobarTensorHomotopy G (ι R c * y) = 0 :=
  LinearMap.congr_fun (linearMap_ext_tprod
    (f := cobarTensorHomotopy G ∘ₗ LinearMap.mulLeft R (ι R c)) (g := 0) fun
      | 0, _ => by simp [tprod_apply]
      | _ + 1, _ => by simp [cobarTensorHomotopy_ι_mul_ι_mul, hc]) y

theorem isHomogeneous_cobarTensorHomotopy :
    LinearMap.IsHomogeneous (cobarTensorHomotopy G)
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1)))
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) (-1) := by
  let P := (grading (G.shift 1)).shift (-1)
  refine LinearMap.isHomogeneous_def.2 fun q _ hz ↦ tensorAlgebraPiece_le
    (C := (tensorAlgebraPiece P (q + -1)).comap (cobarTensorHomotopy G)) (fun n d x hx hd ↦ by
      rw [Submodule.mem_comap]; match n with
      | 0 | 1 => simp
      | k + 2 =>
        rw [cobarTensorHomotopy_tprod_add_two]
        have h0 : letter R A (x 0) ∈ (G.shift 1).piece (d 0 + -1) := by
          simpa only [add_zero] using (isHomogeneous_letter (G.shift 1)).map_mem
            (by simpa [P, grading_piece] using hx 0)
        have hdeg₁ : d 0 + d 1 + -1 + -1 = (d 0 + -1) + (d 1 + -1) := by ring
        have hpre : prepend R A ((G.shift 1).koszulTwist 1 (letter R A (x 0))) (x 1) ∈
            P.piece (d 0 + d 1 + -1) := by
          simpa [P, shift_piece, grading_piece, hdeg₁] using
            ReducedTensorWords.prepend_mem_gradedPiece ((G.shift 1).koszulTwist_mem_piece h0 1)
              (by simpa [P, grading_piece] using hx 1)
        have hdeg₂ : d 0 + d 1 + -1 + ∑ j : Fin k, d j.succ.succ = q + -1 := by
          rw [← hd, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.succ_zero_eq_one]; ring
        rw [← hdeg₂]
        exact SetLike.GradedMul.mul_mem (ι_mem_tensorAlgebraPiece _ hpre)
          (tprod_mem_tensorAlgebraPiece _ _ _ fun j ↦ hx j.succ.succ)) hz

theorem cobarTensorHomotopy_eq_zero_of_mem_tensorPower_one
    {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (n := 1))) :
    cobarTensorHomotopy G z = 0 := by
  obtain ⟨t, rfl⟩ := hz; induction t using PiTensorProduct.induction_on with
  | add _ _ hu hv => simp [hu, hv]
  | smul_tprod _ _ => simp [TensorPower.toTensorAlgebra_tprod]

theorem cobarTensorHomotopy_mem_tensorPower (n : ℕ) {z : TensorAlgebra R (ReducedTensorWords R A)}
    (hz : z ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (n := n + 2))) :
    cobarTensorHomotopy G z ∈
      LinearMap.range (TensorPower.toTensorAlgebra (R := R) (n := n + 1)) := by
  obtain ⟨t, rfl⟩ := hz; induction t using PiTensorProduct.induction_on with
  | add _ _ hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
  | smul_tprod r _ =>
    rw [map_smul, map_smul, TensorPower.toTensorAlgebra_tprod, cobarTensorHomotopy_tprod_add_two]
    exact Submodule.smul_mem _ r (ι_mul_mem_range_toTensorAlgebra _
      ⟨_, TensorPower.toTensorAlgebra_tprod _⟩)

private noncomputable def cobarHomotopyDefect : Module.End R (ΩT R A) :=
  cobarDeconcatDifferential G ∘ₗ cobarTensorHomotopy G +
    cobarTensorHomotopy G ∘ₗ cobarDeconcatDifferential G -
    (LinearMap.id - cobarTensorIncl G ∘ₗ cobarTensorProj G)

private theorem cobarTensorHomotopy_ι_ofLetter_mul_deconcatDifferential_mul (a : A)
    (c : RTW R A) (y : ΩT R A) :
    cobarTensorHomotopy G (ι R (ofLetter R A ((G.shift 1).koszulTwist 1 a)) *
        (cobarDeconcatDifferential G (ι R c) * y)) =
      LinearMap.mul' R (ΩT R A) (TensorProduct.map
        (ι R ∘ₗ ReducedTensorWords.map R ((G.shift 1).koszulTwist 1)) (ι R)
        (LinearMap.rTensor (RTW R A) (prepend R A ((G.shift 1).koszulTwist 1 a))
          (deconcatenation R A c))) * y := by
  rw [cobarDeconcatDifferential_ι]
  induction deconcatenation R A c using TensorProduct.inductionOn with
  | tmul _ _ => simp [mul_assoc, cobarTensorHomotopy_ι_mul_ι_mul, koszulTwist_grading, map_prepend]
  | add _ _ hx₁ hx₂ => simp only [map_add, add_mul, mul_add, hx₁, hx₂]

private theorem cobarTensorHomotopy_rTensor_prepend_mul (a : A) (w : RTW R A) (y : ΩT R A) :
    cobarTensorHomotopy G (LinearMap.mul' R (ΩT R A)
        (TensorProduct.map (ι R ∘ₗ (grading (G.shift 1)).koszulTwist 1) (ι R)
          (LinearMap.rTensor (RTW R A) (prepend R A a) (deconcatenation R A w))) * y) = 0 := by
  induction deconcatenation R A w using TensorProduct.inductionOn with
  | tmul _ _ =>
    simpa only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, comp_apply, mul'_apply, mul_assoc]
      using cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (by simp [letter_koszulTwist]) _
  | add _ _ hu hv => simp only [map_add, add_mul, hu, hv, add_zero]

private theorem cobarHomotopyDefect_ι_ofLetter_mul (a : A) (y : ΩT R A) :
    cobarHomotopyDefect G (ι R (ofLetter R A a) * y) = 0 :=
  LinearMap.congr_fun (linearMap_ext_tprod
    (f := cobarHomotopyDefect G ∘ₗ LinearMap.mulLeft R (ι R (ofLetter R A a))) (g := 0) fun
    | 0, _ => by
      -- Length 1 (`ι [a]`): `H` and `D` vanish, while `i ∘ p` fixes `ι [a]`.
      simp [cobarHomotopyDefect, tprod_apply, cobarTensorIncl_apply]
    | k + 1, u => by
      -- Length ≥ 2 (`ι [a] * ι c * z`): `p` vanishes; internal cuts of `c` and `D z` cancel.
      simp only [comp_apply, mulLeft_apply, LinearMap.zero_apply, tprod_succ_eq_ι_mul,
        cobarHomotopyDefect, LinearMap.sub_apply, LinearMap.add_apply, id_apply,
        cobarTensorProj_mul_ι_mul, map_zero, sub_zero]
      set D := cobarDeconcatDifferential G with hD; set H := cobarTensorHomotopy G with hH
      set c := u 0; set z := tprod R (RTW R A) k (fun i ↦ u i.succ)
      set twa := (G.shift 1).koszulTwist 1 a
      set cut := LinearMap.mul' R (ΩT R A) (TensorProduct.map
        (ι R ∘ₗ ReducedTensorWords.map R ((G.shift 1).koszulTwist 1)) (ι R)
        (LinearMap.rTensor (RTW R A) (prepend R A twa) (deconcatenation R A c))) * z
      set tail := ι R (prepend R A a (ReducedTensorWords.map R ((G.shift 1).koszulTwist 1) c)) * D z
      have hDH : D (H (ι R (ofLetter R A a) * (ι R c * z))) =
          ι R (ofLetter R A a) * (ι R c * z) + cut - tail := by
        rw [hD, hH, cobarTensorHomotopy_ι_mul_ι_mul, letter_ofLetter, cobarDeconcatDifferential_mul,
          koszulTwistAlgEquiv_ι, cobarDeconcatDifferential_ι, deconcatenation_prepend]
        simp only [map_add, add_mul, TensorProduct.map_tmul, comp_apply, mul'_apply,
          koszulTwist_grading, map_ofLetter, map_prepend, koszulTwist_koszulTwist, mul_assoc,
          neg_mul, ← sub_eq_add_neg]; rfl
      have hHD : H (D (ι R (ofLetter R A a) * (ι R c * z))) = -cut + tail := by
        rw [hD, hH, cobarDeconcatDifferential_mul, cobarDeconcatDifferential_ι,
          deconcatenation_ofLetter, map_zero, map_zero, zero_mul, zero_add, koszulTwistAlgEquiv_ι,
          cobarDeconcatDifferential_mul, koszulTwistAlgEquiv_ι, koszulTwist_grading, map_ofLetter]
        simp only [neg_mul, mul_neg, mul_add, map_neg, map_add, neg_neg,
          cobarTensorHomotopy_ι_ofLetter_mul_deconcatDifferential_mul,
          cobarTensorHomotopy_ι_mul_ι_mul, letter_ofLetter, koszulTwist_koszulTwist]; rfl
      rw [hDH, hHD]; abel) y

private theorem cobarHomotopyDefect_ι_prepend_mul (a : A) (w : RTW R A) (y : ΩT R A) :
    cobarHomotopyDefect G (ι R (prepend R A a w) * y) = 0 := by
  -- `H` and `p` vanish on `ι (a · w) * y`; only the leading cut `[a] ⊗ w` survives `H ∘ D`.
  have htw : cobarTensorHomotopy G (koszulTwistAlgEquiv
      (tensorAlgebraPiece ((grading (G.shift 1)).shift (-1))) 1 (ι R (prepend R A a w)) *
      cobarDeconcatDifferential G y) = 0 := by
    rw [koszulTwistAlgEquiv_ι, neg_mul, map_neg, neg_eq_zero]
    exact cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (by simp [letter_koszulTwist]) _
  simp only [cobarHomotopyDefect, LinearMap.sub_apply, LinearMap.add_apply, comp_apply, id_apply,
    cobarTensorHomotopy_ι_mul_of_letter_eq_zero G (letter_prepend a w) y, map_zero, zero_add,
    cobarTensorProj_ι_prepend_mul, sub_zero, cobarDeconcatDifferential_mul, map_add, htw, add_zero,
    cobarDeconcatDifferential_ι, deconcatenation_prepend, add_mul,
    cobarTensorHomotopy_rTensor_prepend_mul]
  simp [mul_assoc, koszulTwist_grading, map_ofLetter, cobarTensorHomotopy_ι_mul_ι_mul]

end UnperturbedCobar

namespace IsNonCounitalDGCoalgebra

variable {G : InternalGrading R A ℤ} {dC : Module.End R (ReducedTensorWords R A)}
  (hC : IsNonCounitalDGCoalgebra (grading (G.shift 1)) (deconcatenation R A) dC)

private theorem cobarDeconcatDifferential_mem_augmentationIdeal (x : ΩT R A) :
    cobarDeconcatDifferential G x ∈ hC.cobarAugmentation.augmentationIdeal := by
  let h0 := isNonCounitalDGCoalgebra_reducedTensorWords_zero G
  have heq : hC.cobarAugmentation.toGradedAlgHom = h0.cobarAugmentation.toGradedAlgHom :=
    tensorAlgebraGradedAlgHom_ext fun _ ↦ by simp
  simpa only [DGAlgAugmentation.mem_augmentationIdeal, ← DGAlgHom.coe_toGradedAlgHom, heq,
    cobarDeconcatDifferential] using h0.cobarAugmentation.map_d x

private theorem cobarTensorHomotopy_mem_augmentationIdeal (z : ΩT R A) :
    cobarTensorHomotopy G z ∈ hC.cobarAugmentation.augmentationIdeal :=
  hC.cobarAugmentation.mem_augmentationIdeal.2 <| LinearMap.congr_fun
    (comp_cobarTensorHomotopy_eq_zero G
      (f := hC.cobarAugmentation.toGradedAlgHom.toAlgHom.toLinearMap) fun _ _ _ ↦ by simp) z

private theorem cobarDeconcatDifferential_homotopy_eq {z : ΩT R A}
    (hz : z ∈ hC.cobarAugmentation.augmentationIdeal.toSubmodule) :
    cobarDeconcatDifferential G (cobarTensorHomotopy G z) +
        cobarTensorHomotopy G (cobarDeconcatDifferential G z) =
      z - cobarTensorIncl G (cobarTensorProj G z) := by
  -- Check `cobarHomotopyDefect G = 0` on spanning generators `ι c * y` via `ofLetter`/`prepend`.
  suffices h : hC.cobarAugmentation.augmentationIdeal.toSubmodule ≤
      LinearMap.ker (cobarHomotopyDefect G) by simpa [cobarHomotopyDefect, sub_eq_zero] using h hz
  refine hC.cobarAugmentation_augmentationIdeal_le_iff.2 fun _ x ↦ ?_
  rw [LinearMap.mem_ker, tprod_succ_eq_ι_mul]
  exact LinearMap.congr_fun (ReducedTensorWords.linearMap_ext_ofLetter_prepend
    (f := cobarHomotopyDefect G ∘ₗ LinearMap.mulRight R _ ∘ₗ ι R) (g := 0)
    (fun a ↦ cobarHomotopyDefect_ι_ofLetter_mul G a _)
    (fun a w ↦ cobarHomotopyDefect_ι_prepend_mul G a w _)) (x 0)

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
  incl := (cobarTensorIncl G).codRestrict _ fun _ ↦ by
    rw [cobarTensorIncl_apply]; exact hC.ι_mem_cobarAugmentation_augmentationIdeal _
  proj := cobarTensorProj G ∘ₗ hC.cobarAugmentation.augmentationIdeal.toSubmodule.subtype
  homotopy := (cobarTensorHomotopy G).restrict fun x _ ↦
    hC.cobarTensorHomotopy_mem_augmentationIdeal x
  dM_comp_incl := LinearMap.ext fun _ ↦ Subtype.ext <| by simp [cobarTensorIncl_apply]
  proj_comp_dM := LinearMap.ext fun x ↦ LinearMap.congr_fun (linearMap_ext_tprod
    (f := cobarTensorProj G ∘ₗ cobarDeconcatDifferential G) (g := 0) fun
    | 0, _ => by simp [tprod_apply, cobarDeconcatDifferential]
    | k + 1, y => by
      have h2 : cobarTensorProj G (ι R ((grading (G.shift 1)).koszulTwist 1 (y 0)) *
          cobarDeconcatDifferential G (tprod R _ k (fun i ↦ y i.succ))) = 0 :=
        (hC.cobarAugmentation_augmentationIdeal_le_iff
          (S := LinearMap.ker (cobarTensorProj G ∘ₗ LinearMap.mulLeft R _)).2 fun _ _ ↦ by
            simpa [tprod_succ_eq_ι_mul] using cobarTensorProj_mul_ι_mul G _ _ _)
          (hC.cobarDeconcatDifferential_mem_augmentationIdeal _)
      simp only [comp_apply, LinearMap.zero_apply, tprod_succ_eq_ι_mul,
        cobarDeconcatDifferential_mul, map_add, koszulTwistAlgEquiv_ι, neg_mul, map_neg, h2,
        neg_zero, add_zero, cobarDeconcatDifferential_ι]
      induction deconcatenation R A (y 0) using TensorProduct.inductionOn with
      | tmul _ _ => simpa [mul_assoc] using cobarTensorProj_mul_ι_mul G _ _ _
      | add _ _ hu hv => simp only [map_add, add_mul, hu, hv, add_zero]) x
  proj_comp_incl := LinearMap.ext fun _ ↦ by simp [cobarTensorIncl_apply]
  dM_comp_homotopy_add_homotopy_comp_dM := LinearMap.ext fun x ↦ Subtype.ext <|
    hC.cobarDeconcatDifferential_homotopy_eq x.property
  homotopy_comp_incl := LinearMap.ext fun _ ↦ Subtype.ext <| by simp [cobarTensorIncl_apply]
  proj_comp_homotopy := LinearMap.ext fun x ↦
    LinearMap.congr_fun (comp_cobarTensorHomotopy_eq_zero G (cobarTensorProj_ι_prepend_mul G)) x
  homotopy_comp_homotopy := LinearMap.ext fun x ↦ Subtype.ext <| LinearMap.congr_fun
    (comp_cobarTensorHomotopy_eq_zero G fun _ _ _ ↦
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
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.incl G.piece
      hC.cobarReducedGrading.piece 0 := LinearMap.isHomogeneous_def.2 fun _ _ ha ↦
  hC.mem_cobarReducedGrading_piece.2 ((isHomogeneous_cobarTensorIncl G).map_mem ha)

theorem isHomogeneous_cobarUnperturbedContraction_proj :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.proj
      hC.cobarReducedGrading.piece G.piece 0 := LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
  (isHomogeneous_cobarTensorProj G).map_mem (hC.mem_cobarReducedGrading_piece.1 hx)

theorem isHomogeneous_cobarUnperturbedContraction_homotopy :
    LinearMap.IsHomogeneous hC.cobarUnperturbedContraction.homotopy
      hC.cobarReducedGrading.piece hC.cobarReducedGrading.piece (-1) :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ hC.mem_cobarReducedGrading_piece.2
    ((isHomogeneous_cobarTensorHomotopy G).map_mem (hC.mem_cobarReducedGrading_piece.1 hx))

end IsNonCounitalDGCoalgebra

end TauCeti
