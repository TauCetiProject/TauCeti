/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Cobar.TwistingCochain
public import TauCeti.Algebra.Homology.Contraction.Perturbation
public import TauCeti.Algebra.Homology.DG.Coalgebra.Cobar.TensorCoalgebra
import TauCeti.LinearAlgebra.TensorAlgebra.Basic

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

open TensorAlgebra

namespace TauCeti.AInfinityAlgebra

open IsNonCounitalDGCoalgebra (coe_cobarDeconcatReducedDifferential coe_cobarReducedDifferential)
open LinearSpecialContraction (copy_incl copy_proj copy_homotopy perturb_incl perturb_proj
  perturb_homotopy perturbedDifferential_def perturbationSeries_def)

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

private abbrev ΩT (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] :=
  TensorAlgebra R (ReducedTensorWords R A)
private abbrev barCoalg := 𝒜.isNonCounitalDGCoalgebra_bar
private noncomputable abbrev augIdeal := 𝒜.barCoalg.cobarAugmentation.augmentationIdeal.toSubmodule
private noncomputable abbrev redGrad := 𝒜.barCoalg.cobarReducedGrading
private noncomputable abbrev unpert := 𝒜.barCoalg.cobarUnperturbedContraction
private abbrev tensorRange (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] (n : ℕ) :=
  LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n))

/-- The bar-differential perturbation `δ₁` on `Ω Tᶜ(sA)` induced by `-ι ∘ b`. -/
noncomputable def cobarBarPerturbation :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  tensorAlgebraDerivation ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))
    (-(ι R ∘ₗ 𝒜.barDifferential))

@[simp] theorem cobarBarPerturbation_ι (c : ReducedTensorWords R A) :
    𝒜.cobarBarPerturbation (ι R c) = -ι R (𝒜.barDifferential c) := by simp [cobarBarPerturbation]

/-- The bar-differential perturbation `δ₁` restricted to the augmentation ideal `Ω⁺ Tᶜ(sA)`. -/
noncomputable def cobarBarReducedPerturbation :
    Module.End R 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal.toSubmodule :=
  𝒜.cobarBarPerturbation.restrict fun x _ ↦ 𝒜.barCoalg.cobarAugmentation.mem_augmentationIdeal.2 <|
    𝒜.barCoalg.cobarAugmentation_derivation_eq_zero (fun _ ↦ by simp) x

@[simp] theorem coe_cobarBarReducedPerturbation
    (x : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal.toSubmodule) :
    (𝒜.cobarBarReducedPerturbation x : TensorAlgebra R (ReducedTensorWords R A)) =
      𝒜.cobarBarPerturbation x := (rfl)

private theorem cobarBarPerturbation_mem_tensorPower :
    ∀ (n : ℕ) {z}, z ∈ tensorRange R A n → 𝒜.cobarBarPerturbation z ∈ tensorRange R A n
  | n, _, ⟨t, rfl⟩ => by
    induction t using PiTensorProduct.induction_on with
    | add _ _ hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
    | smul_tprod r x => cases n with
      | zero => simp [TensorPower.toTensorAlgebra_tprod, tprod_apply, cobarBarPerturbation]
      | succ n =>
        rw [map_smul, map_smul, TensorPower.toTensorAlgebra_tprod, tprod_succ_eq_ι_mul,
          cobarBarPerturbation, tensorAlgebraDerivation_mul, tensorAlgebraDerivation_ι,
          LinearMap.neg_apply, LinearMap.comp_apply, InternalGrading.koszulTwistAlgEquiv_apply,
          koszulTwist_tensorAlgebraPiece_ι, neg_mul]
        have ht : tprod R _ n (fun i ↦ x i.succ) ∈ tensorRange R A n :=
          ⟨_, TensorPower.toTensorAlgebra_tprod _⟩
        exact Submodule.smul_mem _ r (add_mem (neg_mem (ι_mul_mem_range_toTensorAlgebra _ ht))
          (ι_mul_mem_range_toTensorAlgebra _ (cobarBarPerturbation_mem_tensorPower n ht)))

private theorem pow_cobarBarPerturbation_mul_homotopy_eq_zero :
    ∀ (n : ℕ) {z}, z ∈ tensorRange R A (n + 1) →
      ((𝒜.cobarBarPerturbation * cobarTensorHomotopy 𝒜.grading) ^ (n + 1)) z = 0
  | 0, _, hz => by
    simp [mul_apply_eq_comp, cobarTensorHomotopy_eq_zero_of_mem_tensorPower_one 𝒜.grading hz]
  | n + 1, _, hz => by
    rw [pow_succ, mul_apply_eq_comp, mul_apply_eq_comp]
    exact pow_cobarBarPerturbation_mul_homotopy_eq_zero n (𝒜.cobarBarPerturbation_mem_tensorPower
      (n + 1) (cobarTensorHomotopy_mem_tensorPower 𝒜.grading n hz))

private theorem exists_pow_cobarBarReducedPerturbation_mul_homotopy_eq_zero (z : 𝒜.augIdeal) :
    ∃ k : ℕ, ((𝒜.cobarBarReducedPerturbation * 𝒜.unpert.homotopy) ^ k) z = 0 := by
  let T := 𝒜.cobarBarPerturbation * cobarTensorHomotopy 𝒜.grading
  have hcoe (k : ℕ) :
      ((((𝒜.cobarBarReducedPerturbation * 𝒜.unpert.homotopy) ^ k) z : 𝒜.augIdeal) : ΩT R A) =
        (T ^ k) (z : ΩT R A) :=
    k.rec rfl fun _ ih ↦ by simpa [T, pow_succ', mul_apply_eq_comp] using congrArg T ih
  let N : Submodule R (ΩT R A) :=
    { carrier := {x | ∃ k, (T ^ k) x = 0}, zero_mem' := ⟨0, map_zero _⟩
      add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨max a b, by
        rw [map_add, Module.End.pow_map_zero_of_le (le_max_left _ _) ha,
          Module.End.pow_map_zero_of_le (le_max_right _ _) hb, add_zero]⟩
      smul_mem' := fun _ _ ⟨a, ha⟩ ↦ ⟨a, by rw [map_smul, ha, smul_zero]⟩ }
  obtain ⟨k, hk⟩ := (𝒜.barCoalg.cobarAugmentation_augmentationIdeal_le_iff (S := N).2 fun n x ↦
    ⟨n + 1, 𝒜.pow_cobarBarPerturbation_mul_homotopy_eq_zero n
      ⟨_, TensorPower.toTensorAlgebra_tprod x⟩⟩) z.property
  exact ⟨k, Subtype.ext (by rw [hcoe k, hk, Submodule.coe_zero])⟩

private theorem isUnit_one_add_cobarBarReducedPerturbation_mul_homotopy :
    IsUnit (1 + 𝒜.cobarBarReducedPerturbation * 𝒜.unpert.homotopy) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    𝒜.exists_pow_cobarBarReducedPerturbation_mul_homotopy_eq_zero

private theorem cobarDeconcatReducedDifferential_add_cobarBarReducedPerturbation :
    𝒜.barCoalg.cobarDeconcatReducedDifferential + 𝒜.cobarBarReducedPerturbation =
      𝒜.barCoalg.cobarReducedDifferential := LinearMap.ext fun x ↦ Subtype.ext <| by
  simp only [LinearMap.add_apply, Submodule.coe_add, coe_cobarDeconcatReducedDifferential,
    coe_cobarBarReducedPerturbation, coe_cobarReducedDifferential]
  induction (x : ΩT R A) using TensorAlgebra.induction with
  | algebraMap _ => simp [cobarBarPerturbation]
  | ι _ => simp [sub_eq_add_neg]
  | add _ _ hx hy => rw [map_add, map_add, map_add, ← hx, ← hy]; abel
  | mul _ _ hx hy =>
    rw [cobarDeconcatDifferential_mul, cobarBarPerturbation, tensorAlgebraDerivation_mul,
      cobarDifferential_mul_koszulTwist, ← cobarBarPerturbation, ← hx, ← hy, add_mul, mul_add]; abel

private theorem homotopy_cobarBarReducedPerturbation_incl (a : A) :
    𝒜.unpert.homotopy (𝒜.cobarBarReducedPerturbation (𝒜.unpert.incl a)) = 0 :=
  Subtype.ext <| by simp [cobarTensorIncl_apply]

private theorem perturbationSeries_incl (a : A) :
    𝒜.unpert.perturbationSeries 𝒜.cobarBarReducedPerturbation (𝒜.unpert.incl a) =
      𝒜.cobarBarReducedPerturbation (𝒜.unpert.incl a) := by
  simpa using 𝒜.unpert.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero
    𝒜.cobarBarReducedPerturbation 𝒜.isUnit_one_add_cobarBarReducedPerturbation_mul_homotopy
    (k := 1) (by simp [𝒜.homotopy_cobarBarReducedPerturbation_incl a])

private noncomputable def perturbedCobarContraction :
    LinearSpecialContraction
      (𝒜.barCoalg.cobarDeconcatReducedDifferential + 𝒜.cobarBarReducedPerturbation)
      (𝒜.unpert.perturbedDifferential 𝒜.cobarBarReducedPerturbation) :=
  𝒜.unpert.perturb 𝒜.cobarBarReducedPerturbation
    (by simp [𝒜.cobarDeconcatReducedDifferential_add_cobarBarReducedPerturbation])
    𝒜.isUnit_one_add_cobarBarReducedPerturbation_mul_homotopy

/-- Explicit homogeneous special contraction of `Ω⁺ Tᶜ(sA)` onto `(A, m₁)`. -/
noncomputable def cobarAugmentationIdealContraction :
    LinearSpecialContraction 𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedDifferential
      𝒜.differential :=
  𝒜.perturbedCobarContraction.copy 𝒜.unpert.incl 𝒜.perturbedCobarContraction.proj
    𝒜.perturbedCobarContraction.homotopy
    𝒜.cobarDeconcatReducedDifferential_add_cobarBarReducedPerturbation
    (LinearMap.ext fun a ↦ by
      have hd : 𝒜.m 1 ![(𝒜.grading.shift 1).koszulTwist 1 a] =
          -(𝒜.grading.shift 1).koszulTwist 1 (𝒜.m 1 ![a]) := by
        simpa [InternalGrading.koszulTwist_one_shift_one, ← differential_apply] using
          congrArg Neg.neg (𝒜.m_one_koszulTwist a)
      simp [perturbedDifferential_def, 𝒜.perturbationSeries_incl, cobarTensorIncl_apply,
        𝒜.barDifferential_ofLetter, hd, differential_apply])
    (LinearMap.ext fun a ↦ by simp [perturbedCobarContraction, perturb_incl,
      𝒜.perturbationSeries_incl, 𝒜.homotopy_cobarBarReducedPerturbation_incl]) rfl rfl

@[simp] theorem coe_cobarAugmentationIdealContraction_incl (a : A) :
    (𝒜.cobarAugmentationIdealContraction.incl a :
      TensorAlgebra R (ReducedTensorWords R A)) = 𝒜.toCobarBar.linearPart a := by
  simp [cobarAugmentationIdealContraction, cobarTensorIncl_apply,
    InternalGrading.koszulTwist_one_shift_one]

/-- The perturbed projection of `cobarAugmentationIdealContraction`. -/
theorem cobarAugmentationIdealContraction_proj :
    𝒜.cobarAugmentationIdealContraction.proj =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.proj -
        𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.proj ∘ₗ
          𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbationSeries
            𝒜.cobarBarReducedPerturbation ∘ₗ
            𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy := by
  rw [cobarAugmentationIdealContraction, copy_proj, perturbedCobarContraction, perturb_proj]

/-- The perturbed homotopy of `cobarAugmentationIdealContraction`. -/
theorem cobarAugmentationIdealContraction_homotopy :
    𝒜.cobarAugmentationIdealContraction.homotopy =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy -
        𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy ∘ₗ
          𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbationSeries
            𝒜.cobarBarReducedPerturbation ∘ₗ
            𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy := by
  rw [cobarAugmentationIdealContraction, copy_homotopy, perturbedCobarContraction, perturb_homotopy]

theorem isHomogeneous_cobarAugmentationIdealContraction_incl :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.incl
      𝒜.grading.piece 𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 0 := by
  rw [cobarAugmentationIdealContraction, copy_incl]
  exact 𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_incl

private theorem isHomogeneous_pertSeries_comp_h :
    LinearMap.IsHomogeneous
      (𝒜.unpert.perturbationSeries 𝒜.cobarBarReducedPerturbation ∘ₗ 𝒜.unpert.homotopy)
      𝒜.redGrad.piece 𝒜.redGrad.piece 0 := by
  have hd : LinearMap.IsHomogeneous 𝒜.cobarBarReducedPerturbation
      𝒜.redGrad.piece 𝒜.redGrad.piece 1 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ 𝒜.barCoalg.mem_cobarReducedGrading_piece.2 <|
      tensorAlgebraDerivation_mem_tensorAlgebraPiece (fun {p _} hc ↦ neg_mem <|
        ι_mem_tensorAlgebraPiece _ <| by
          rw [InternalGrading.shift_piece, add_right_comm]
          exact 𝒜.barCoalg.map_mem (by rwa [InternalGrading.shift_piece] at hc))
        (𝒜.barCoalg.mem_cobarReducedGrading_piece.1 hx)
  have h0 : LinearMap.IsHomogeneous (𝒜.cobarBarReducedPerturbation * 𝒜.unpert.homotopy)
      𝒜.redGrad.piece 𝒜.redGrad.piece 0 := by
    simpa only [Module.End.mul_eq_comp, neg_add_cancel] using
      hd.comp 𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_homotopy
  rw [perturbationSeries_def, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  simpa only [← Module.End.mul_eq_comp, add_zero] using
    (h0.ringInverse_one_add 𝒜.exists_pow_cobarBarReducedPerturbation_mul_homotopy_eq_zero).comp h0

theorem isHomogeneous_cobarAugmentationIdealContraction_proj :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.proj
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 𝒜.grading.piece 0 := by
  have h := 𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_proj
  rw [cobarAugmentationIdealContraction_proj]
  exact h.sub <| by simpa only [add_zero] using h.comp 𝒜.isHomogeneous_pertSeries_comp_h

theorem isHomogeneous_cobarAugmentationIdealContraction_homotopy :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.homotopy
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece (-1) := by
  have h := 𝒜.barCoalg.isHomogeneous_cobarUnperturbedContraction_homotopy
  rw [cobarAugmentationIdealContraction_homotopy]
  exact h.sub <| by simpa only [zero_add] using h.comp 𝒜.isHomogeneous_pertSeries_comp_h

end TauCeti.AInfinityAlgebra
