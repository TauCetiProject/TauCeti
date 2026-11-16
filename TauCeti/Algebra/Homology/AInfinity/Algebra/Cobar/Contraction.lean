/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Homology.Contraction.Perturbation
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TensorCoalgebra

/-!
# Contracting the cobar augmentation ideal of the bar construction

For a nonunital `A∞` algebra `A` over a commutative ring `R`, homological perturbation of
`cobarUnperturbedContraction` by the bar-differential perturbation `δ₁` yields an explicit
homogeneous special contraction (`cobarAugmentationIdealContraction`) of `Ω⁺ Tᶜ(sA)` onto `(A, m₁)`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Springer (2012), Section 2.2.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemp. Math. 406 (2006), §4.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
-/

public section

open scoped TensorProduct
open TensorAlgebra

namespace TauCeti.AInfinityAlgebra

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

private abbrev barCoalg := 𝒜.isNonCounitalDGCoalgebra_bar
private noncomputable abbrev augIdeal := 𝒜.barCoalg.cobarAugmentation.augmentationIdeal.toSubmodule
private noncomputable abbrev redGrad := 𝒜.barCoalg.cobarReducedGrading
private noncomputable abbrev unpert := 𝒜.barCoalg.cobarUnperturbedContraction
private abbrev tensorRange (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] (n : ℕ) :=
  LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n))

private noncomputable def cobarDeltaOne : Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  tensorAlgebraDerivation ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))
    (-(ι R ∘ₗ 𝒜.barDifferential))

private noncomputable def cobarDeltaOneRes : Module.End R 𝒜.augIdeal :=
  𝒜.cobarDeltaOne.restrict fun x _ ↦ 𝒜.barCoalg.cobarAugmentation.mem_augmentationIdeal.2 <|
    𝒜.barCoalg.cobarAugmentation_derivation_eq_zero (fun _ ↦ by simp) x

private theorem cobarDeltaOne_mem_tensorPower :
    ∀ (n : ℕ) {z}, z ∈ tensorRange R A n → 𝒜.cobarDeltaOne z ∈ tensorRange R A n
  | n, _, ⟨t, rfl⟩ => by
    induction t using PiTensorProduct.induction_on with
    | add _ _ hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
    | smul_tprod r x => cases n with
      | zero => simp [TensorPower.toTensorAlgebra_tprod, tprod_apply, cobarDeltaOne]
      | succ n =>
        rw [map_smul, map_smul, TensorPower.toTensorAlgebra_tprod,
          show tprod R (ReducedTensorWords R A) (n + 1) x =
            ι R (x 0) * tprod R (ReducedTensorWords R A) n (fun i ↦ x i.succ) by
            simp [tprod_apply, List.ofFn_succ],
          cobarDeltaOne, tensorAlgebraDerivation_mul, tensorAlgebraDerivation_ι,
          LinearMap.neg_apply, LinearMap.comp_apply, InternalGrading.koszulTwistAlgEquiv_apply,
          koszulTwist_tensorAlgebraPiece_ι, neg_mul]
        have ht : tprod R (ReducedTensorWords R A) n (fun i ↦ x i.succ) ∈ tensorRange R A n :=
          ⟨_, TensorPower.toTensorAlgebra_tprod _⟩
        exact Submodule.smul_mem _ r (add_mem (neg_mem (ι_mul_mem_range_toTensorAlgebra _ ht))
          (ι_mul_mem_range_toTensorAlgebra _ (cobarDeltaOne_mem_tensorPower n ht)))

private theorem pow_cobarDeltaOne_mul_homotopy_eq_zero :
    ∀ (n : ℕ) {z}, z ∈ tensorRange R A (n + 1) →
      ((𝒜.cobarDeltaOne * cobarTensorHomotopy 𝒜.grading) ^ (n + 1)) z = 0
  | 0, _, hz => by
    simp [mul_apply_eq_comp, cobarTensorHomotopy_eq_zero_of_mem_tensorPower_one 𝒜.grading hz]
  | n + 1, _, hz => by
    rw [pow_succ, mul_apply_eq_comp, mul_apply_eq_comp]
    exact pow_cobarDeltaOne_mul_homotopy_eq_zero n
      (𝒜.cobarDeltaOne_mem_tensorPower (n + 1) (cobarTensorHomotopy_mem_tensorPower 𝒜.grading n hz))

private theorem exists_pow_cobarDeltaOneRes_mul_homotopy_eq_zero (z : 𝒜.augIdeal) :
    ∃ k : ℕ, ((𝒜.cobarDeltaOneRes * 𝒜.unpert.homotopy) ^ k) z = 0 := by
  have hcoe (k : ℕ) (w : 𝒜.augIdeal) : ((((𝒜.cobarDeltaOneRes * 𝒜.unpert.homotopy) ^ k) w :
      𝒜.augIdeal) : TensorAlgebra R (ReducedTensorWords R A)) =
      ((𝒜.cobarDeltaOne * cobarTensorHomotopy 𝒜.grading) ^ k) (w : TensorAlgebra R _) := by
    induction k with
    | zero => rfl
    | succ _ ih =>
      simpa only [pow_succ', mul_apply_eq_comp, cobarDeltaOneRes, LinearMap.restrict_apply,
        IsNonCounitalDGCoalgebra.coe_cobarUnperturbedContraction_homotopy] using
        congrArg (fun x ↦ 𝒜.cobarDeltaOne (cobarTensorHomotopy 𝒜.grading x)) ih
  let N : Submodule R (TensorAlgebra R (ReducedTensorWords R A)) :=
    { carrier := {x | ∃ k, ((𝒜.cobarDeltaOne * cobarTensorHomotopy 𝒜.grading) ^ k) x = 0}
      zero_mem' := ⟨0, map_zero _⟩
      add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨max a b, by
        rw [map_add, Module.End.pow_map_zero_of_le (le_max_left _ _) ha,
          Module.End.pow_map_zero_of_le (le_max_right _ _) hb, add_zero]⟩
      smul_mem' := fun _ _ ⟨a, ha⟩ ↦ ⟨a, by rw [map_smul, ha, smul_zero]⟩ }
  obtain ⟨k, hk⟩ := (𝒜.barCoalg.cobarAugmentation_augmentationIdeal_le_iff (S := N).2 fun n x ↦
    ⟨n + 1, 𝒜.pow_cobarDeltaOne_mul_homotopy_eq_zero n
      ⟨_, TensorPower.toTensorAlgebra_tprod x⟩⟩) z.property
  exact ⟨k, Subtype.ext (by rw [hcoe k z, hk]; rfl)⟩

private theorem isUnit_one_add_cobarDeltaOneRes_mul_homotopy :
    IsUnit (1 + 𝒜.cobarDeltaOneRes * 𝒜.unpert.homotopy) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    𝒜.exists_pow_cobarDeltaOneRes_mul_homotopy_eq_zero

private theorem cobarDeconcatReducedDifferential_add_cobarDeltaOneRes :
    𝒜.barCoalg.cobarDeconcatReducedDifferential + 𝒜.cobarDeltaOneRes =
      𝒜.barCoalg.cobarReducedDifferential := by
  have hfull (x : TensorAlgebra R (ReducedTensorWords R A)) :
      (cobarDeconcatDifferential 𝒜.grading + 𝒜.cobarDeltaOne) x =
        cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
          (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential x := by
    induction x using TensorAlgebra.induction with
    | algebraMap _ => simp [cobarDeltaOne]
    | ι _ => simp [cobarDeltaOne, sub_eq_add_neg]
    | add _ _ hx hy => simp only [LinearMap.add_apply, map_add] at hx hy ⊢; rw [← hx, ← hy]
    | mul _ _ hx hy =>
      simp only [LinearMap.add_apply] at hx hy ⊢
      rw [cobarDeconcatDifferential_mul, cobarDeltaOne, tensorAlgebraDerivation_mul,
        cobarDifferential_mul_koszulTwist, ← cobarDeltaOne, ← hx, ← hy, add_mul, mul_add]; abel
  exact LinearMap.ext fun x ↦ Subtype.ext <| by simpa [cobarDeltaOneRes] using hfull x

private theorem homotopy_cobarDeltaOneRes_incl (a : A) :
    𝒜.unpert.homotopy (𝒜.cobarDeltaOneRes (𝒜.unpert.incl a)) = 0 :=
  Subtype.ext <| by simp [cobarDeltaOneRes, cobarTensorIncl_apply, cobarDeltaOne]

private theorem perturbationSeries_incl (a : A) :
    𝒜.unpert.perturbationSeries 𝒜.cobarDeltaOneRes (𝒜.unpert.incl a) =
      𝒜.cobarDeltaOneRes (𝒜.unpert.incl a) := by
  simpa using 𝒜.unpert.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero 𝒜.cobarDeltaOneRes
    𝒜.isUnit_one_add_cobarDeltaOneRes_mul_homotopy (k := 1) (by
      simp [𝒜.homotopy_cobarDeltaOneRes_incl a])

private noncomputable def perturbedCobarContraction :
    LinearSpecialContraction (𝒜.barCoalg.cobarDeconcatReducedDifferential + 𝒜.cobarDeltaOneRes)
      (𝒜.unpert.perturbedDifferential 𝒜.cobarDeltaOneRes) :=
  𝒜.unpert.perturb 𝒜.cobarDeltaOneRes
    (by rw [𝒜.cobarDeconcatReducedDifferential_add_cobarDeltaOneRes,
      𝒜.barCoalg.cobarReducedDifferential_comp_self,
      𝒜.barCoalg.cobarDeconcatReducedDifferential_comp_self])
    𝒜.isUnit_one_add_cobarDeltaOneRes_mul_homotopy

private def transportContraction {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {dM dM' : Module.End R M} {dN dN' : Module.End R N}
    (c : LinearSpecialContraction dM dN) (i : N →ₗ[R] M)
    (hdM : dM = dM') (hdN : dN = dN') (hi : c.incl = i) : LinearSpecialContraction dM' dN' where
  incl := i; proj := c.proj; homotopy := c.homotopy
  dM_comp_incl := by subst hdM hdN hi; exact c.dM_comp_incl
  proj_comp_dM := by subst hdM hdN; exact c.proj_comp_dM
  proj_comp_incl := by subst hi; exact c.proj_comp_incl
  dM_comp_homotopy_add_homotopy_comp_dM := by
    subst hdM hi; exact c.dM_comp_homotopy_add_homotopy_comp_dM
  homotopy_comp_incl := by subst hi; exact c.homotopy_comp_incl
  proj_comp_homotopy := c.proj_comp_homotopy; homotopy_comp_homotopy := c.homotopy_comp_homotopy

/-- Explicit homogeneous special contraction of `Ω⁺ Tᶜ(sA)` onto `(A, m₁)`. -/
noncomputable def cobarAugmentationIdealContraction :
    LinearSpecialContraction 𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedDifferential
      𝒜.differential :=
  transportContraction 𝒜.perturbedCobarContraction 𝒜.unpert.incl
    𝒜.cobarDeconcatReducedDifferential_add_cobarDeltaOneRes
    (LinearMap.ext fun a ↦ by
      have hd : 𝒜.differential ((𝒜.grading.shift 1).koszulTwist 1 a) =
          -(𝒜.grading.shift 1).koszulTwist 1 (𝒜.differential a) := by
        have h := (LinearMap.isHomogeneous_def (f := 𝒜.differential)
          (𝒜 := (𝒜.grading.shift 1).piece) (ℬ := (𝒜.grading.shift 1).piece) (q := 1) |>.2
          fun _ _ hx ↦ by
            rw [InternalGrading.shift_piece] at hx ⊢
            simpa only [add_right_comm] using 𝒜.differential_mem_piece hx).koszulTwist_apply 1 a
        simp only [mul_one, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
          Int.cast_one, neg_one_smul] at h; rw [h, neg_neg]
      rw [LinearSpecialContraction.perturbedDifferential_def, LinearMap.add_apply,
        LinearMap.zero_apply, zero_add, LinearMap.comp_apply, LinearMap.comp_apply,
        𝒜.perturbationSeries_incl]
      simp only [cobarDeltaOneRes, LinearMap.restrict_apply,
        IsNonCounitalDGCoalgebra.cobarUnperturbedContraction_proj_apply,
        IsNonCounitalDGCoalgebra.coe_cobarUnperturbedContraction_incl, cobarTensorIncl_apply,
        cobarDeltaOne, tensorAlgebraDerivation_ι, LinearMap.neg_apply, LinearMap.comp_apply,
        map_neg, cobarTensorProj_ι, 𝒜.barDifferential_ofLetter,
        ReducedTensorWords.letter_ofLetter, ← 𝒜.differential_apply, hd,
        InternalGrading.koszulTwist_koszulTwist, neg_neg])
    (LinearMap.ext fun a ↦ by
      simp [perturbedCobarContraction, LinearSpecialContraction.perturb_incl,
        𝒜.perturbationSeries_incl, 𝒜.homotopy_cobarDeltaOneRes_incl])

@[simp] theorem coe_cobarAugmentationIdealContraction_incl (a : A) :
    (𝒜.cobarAugmentationIdealContraction.incl a :
      TensorAlgebra R (ReducedTensorWords R A)) = 𝒜.toCobarBar.linearPart a := by
  rw [cobarAugmentationIdealContraction, transportContraction,
    IsNonCounitalDGCoalgebra.coe_cobarUnperturbedContraction_incl, cobarTensorIncl_apply,
    AInfinityHom.linearPart_apply, taylor_toCobarBar, LinearMap.comp_apply,
    ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

theorem isHomogeneous_cobarAugmentationIdealContraction_incl :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.incl
      𝒜.grading.piece 𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 0 :=
  𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_incl

private theorem isHomogeneous_pertSeries_comp_h :
    LinearMap.IsHomogeneous (𝒜.unpert.perturbationSeries 𝒜.cobarDeltaOneRes ∘ₗ 𝒜.unpert.homotopy)
      𝒜.redGrad.piece 𝒜.redGrad.piece 0 := by
  have hd : LinearMap.IsHomogeneous 𝒜.cobarDeltaOneRes 𝒜.redGrad.piece 𝒜.redGrad.piece 1 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ 𝒜.barCoalg.mem_cobarReducedGrading_piece.2 <|
      tensorAlgebraDerivation_mem_tensorAlgebraPiece (fun {p c} hc ↦ by
        refine neg_mem (ι_mem_tensorAlgebraPiece _ ?_)
        rw [InternalGrading.shift_piece] at hc ⊢
        simpa only [add_right_comm] using 𝒜.barCoalg.map_mem hc)
        (𝒜.barCoalg.mem_cobarReducedGrading_piece.1 hx)
  have h0 : LinearMap.IsHomogeneous (𝒜.cobarDeltaOneRes * 𝒜.unpert.homotopy)
      𝒜.redGrad.piece 𝒜.redGrad.piece 0 := by
    simpa only [Module.End.mul_eq_comp, neg_add_cancel] using
      hd.comp 𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_homotopy
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  simpa only [← Module.End.mul_eq_comp, add_zero] using
    (h0.ringInverse_one_add 𝒜.exists_pow_cobarDeltaOneRes_mul_homotopy_eq_zero).comp h0

theorem isHomogeneous_cobarAugmentationIdealContraction_proj :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.proj
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 𝒜.grading.piece 0 := by
  have hp := 𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_proj
  change LinearMap.IsHomogeneous 𝒜.perturbedCobarContraction.proj _ _ _
  rw [perturbedCobarContraction, LinearSpecialContraction.perturb_proj]
  exact hp.sub <| by simpa only [add_zero] using hp.comp 𝒜.isHomogeneous_pertSeries_comp_h

theorem isHomogeneous_cobarAugmentationIdealContraction_homotopy :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.homotopy
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece (-1) := by
  have hh := 𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_homotopy
  change LinearMap.IsHomogeneous 𝒜.perturbedCobarContraction.homotopy _ _ _
  rw [perturbedCobarContraction, LinearSpecialContraction.perturb_homotopy]
  exact hh.sub <| by simpa only [zero_add] using hh.comp 𝒜.isHomogeneous_pertSeries_comp_h

end TauCeti.AInfinityAlgebra
