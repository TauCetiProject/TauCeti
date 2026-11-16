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

Let `A` be a nonunital `A∞` algebra over a commutative ring `R`, and let `Ω Tᶜ(sA)` be the cobar
construction of its reduced bar construction `Tᶜ(sA)`.  This file constructs an explicit homogeneous
special contraction (`TauCeti.AInfinityAlgebra.cobarAugmentationIdealContraction`) of the
augmentation ideal `Ω⁺ Tᶜ(sA)` onto `(A, m₁)`, whose inclusion is the linear part of the canonical
`A∞` morphism `A ⟶ Ω Tᶜ(sA)` (`TauCeti.AInfinityAlgebra.toCobarBar`).

The proof uses homological perturbation theory and requires no field, flatness, or finiteness
hypotheses on `A` or `R`.  The cobar differential `d_Ω` splits as `δ₀ + δ₁`, where `δ₀` is the
unperturbed deconcatenation differential (`TauCeti.cobarDeconcatDifferential`) and `δ₁` is the odd
derivation extending `s⁻¹ z ↦ -s⁻¹ (b z)` (carrying the bar differential).  Starting from the
explicit unperturbed contraction of `(Ω⁺ Tᶜ(sA), δ₀)` onto `(A, 0)`
(`TauCeti.IsNonCounitalDGCoalgebra.cobarUnperturbedContraction`), the homotopy `h` strictly lowers
tensor length in `Ω Tᶜ(sA)` while `δ₁` preserves it, so `δ₁ h` is locally nilpotent on `Ω⁺ Tᶜ(sA)`
and `1 + δ₁ h` is invertible.  Applying the basic perturbation lemma
(`TauCeti.LinearSpecialContraction.perturb`) yields a special contraction of `(Ω⁺ Tᶜ(sA), d_Ω)`
onto `(A, d')`.  Because `δ₁` sends the image of `A` into tensor length one, where `h` vanishes,
the perturbation series collapses on `A`: the perturbed inclusion is unchanged, and the perturbed
differential `d'` is `m₁`.

## Main definitions

* `TauCeti.AInfinityAlgebra.cobarAugmentationIdealContraction`: the homogeneous special contraction
  of the augmentation ideal `Ω⁺ Tᶜ(sA)` onto `(A, m₁)`.

## Main results

* `TauCeti.AInfinityAlgebra.coe_cobarAugmentationIdealContraction_incl`: the inclusion of the
  contraction is the linear part of `TauCeti.AInfinityAlgebra.toCobarBar`.
* `TauCeti.AInfinityAlgebra.isHomogeneous_cobarAugmentationIdealContraction_incl`,
  `TauCeti.AInfinityAlgebra.isHomogeneous_cobarAugmentationIdealContraction_proj`, and
  `TauCeti.AInfinityAlgebra.isHomogeneous_cobarAugmentationIdealContraction_homotopy`: the
  inclusion and projection have degree zero and the homotopy has degree `-1`.

## References

* J.-L. Loday and B. Vallette, *Algebraic Operads*, Grundlehren der mathematischen Wissenschaften
  346, Springer (2012), Section 2.2, for the bar--cobar contracting homotopy.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4, for the enveloping DG algebra `Ω B A` and its quasi-isomorphism from `A`.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
-/

public section

open scoped TensorProduct
open TensorAlgebra

namespace TauCeti.AInfinityAlgebra

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-! ### The internal-differential perturbation `δ₁` -/

private theorem differential_koszulTwist_shift (a : A) :
    𝒜.differential ((𝒜.grading.shift 1).koszulTwist 1 a) =
      -(𝒜.grading.shift 1).koszulTwist 1 (𝒜.differential a) := by
  have hhom : LinearMap.IsHomogeneous 𝒜.differential
      (𝒜.grading.shift 1).piece (𝒜.grading.shift 1).piece 1 :=
    LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [InternalGrading.shift_piece] at hx ⊢
      simpa only [add_right_comm] using 𝒜.differential_mem_piece hx
  have h := hhom.koszulTwist_apply 1 a
  simp only [mul_one, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
    neg_one_smul] at h
  rw [h, neg_neg]

private theorem cobarTensorIncl_eq_toCobarBar_linearPart (a : A) :
    cobarTensorIncl 𝒜.grading a = 𝒜.toCobarBar.linearPart a := by
  rw [cobarTensorIncl_apply, AInfinityHom.linearPart_apply, taylor_toCobarBar,
    LinearMap.comp_apply, ReducedTensorWords.koszulTwist_grading, ReducedTensorWords.map_ofLetter]

/-- The internal-differential perturbation `δ₁` on `Ω Tᶜ(sA)`, the odd derivation extending
`s⁻¹ z ↦ -s⁻¹ (b z)`. -/
private noncomputable def cobarDeltaOne :
    Module.End R (TensorAlgebra R (ReducedTensorWords R A)) :=
  tensorAlgebraDerivation ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))
    (-(ι R ∘ₗ 𝒜.barDifferential))

private theorem cobarDeltaOne_ι (c : ReducedTensorWords R A) :
    𝒜.cobarDeltaOne (ι R c) = -ι R (𝒜.barDifferential c) :=
  tensorAlgebraDerivation_ι _ _ c

private theorem cobarDeltaOne_mul (x y : TensorAlgebra R (ReducedTensorWords R A)) :
    𝒜.cobarDeltaOne (x * y) =
      𝒜.cobarDeltaOne x * y +
        InternalGrading.koszulTwistAlgEquiv
          (tensorAlgebraPiece ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))) 1 x *
          𝒜.cobarDeltaOne y :=
  tensorAlgebraDerivation_mul _ _ x y

private theorem cobarDeconcatDifferential_add_cobarDeltaOne :
    cobarDeconcatDifferential 𝒜.grading + 𝒜.cobarDeltaOne =
      cobarDifferential (ReducedTensorWords.grading (𝒜.grading.shift 1))
        (ReducedTensorWords.deconcatenation R A) 𝒜.barDifferential := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp [cobarDeltaOne]
  | ι c =>
    simp only [LinearMap.add_apply, cobarDeconcatDifferential_ι, 𝒜.cobarDeltaOne_ι,
      cobarDifferential_ι, sub_eq_add_neg]
  | add x y hx hy =>
    simp only [LinearMap.add_apply, map_add] at hx hy ⊢
    rw [← hx, ← hy]
  | mul x y hx hy =>
    simp only [LinearMap.add_apply] at hx hy ⊢
    rw [cobarDeconcatDifferential_mul, 𝒜.cobarDeltaOne_mul, cobarDifferential_mul_koszulTwist,
      ← hx, ← hy, add_mul, mul_add]
    abel

private theorem cobarDeltaOne_mem_augmentationIdeal
    (x : TensorAlgebra R (ReducedTensorWords R A)) :
    𝒜.cobarDeltaOne x ∈ 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal := by
  rw [DGAlgAugmentation.mem_augmentationIdeal]
  exact 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_derivation_eq_zero
    (fun c ↦ by simp) x

private theorem isHomogeneous_cobarDeltaOne :
    LinearMap.IsHomogeneous 𝒜.cobarDeltaOne
      (tensorAlgebraPiece ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1)))
      (tensorAlgebraPiece ((ReducedTensorWords.grading (𝒜.grading.shift 1)).shift (-1))) 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    tensorAlgebraDerivation_mem_tensorAlgebraPiece (fun {p c} hc ↦ by
      rw [LinearMap.neg_apply, LinearMap.comp_apply]
      refine neg_mem (ι_mem_tensorAlgebraPiece _ ?_)
      rw [InternalGrading.shift_piece] at hc ⊢
      have hb := 𝒜.isNonCounitalDGCoalgebra_bar.map_mem hc
      simpa only [add_right_comm] using hb) hx

private noncomputable def cobarDeltaOneRes :
    Module.End R 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal.toSubmodule :=
  𝒜.cobarDeltaOne.restrict fun x _ ↦ 𝒜.cobarDeltaOne_mem_augmentationIdeal x

private theorem isHomogeneous_cobarDeltaOneRes :
    LinearMap.IsHomogeneous 𝒜.cobarDeltaOneRes
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    𝒜.isNonCounitalDGCoalgebra_bar.mem_cobarReducedGrading_piece.2
      (𝒜.isHomogeneous_cobarDeltaOne.map_mem
        (𝒜.isNonCounitalDGCoalgebra_bar.mem_cobarReducedGrading_piece.1 hx))

/-! ### Local nilpotence of `δ₁ h` and homological perturbation -/

/-- `δ₁` preserves each tensor-power subspace of `Ω Tᶜ(sA)`. -/
private theorem cobarDeltaOne_mem_tensorPower :
    ∀ (n : ℕ) {z : TensorAlgebra R (ReducedTensorWords R A)},
      z ∈ LinearMap.range
          (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n)) →
        𝒜.cobarDeltaOne z ∈ LinearMap.range
          (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n))
  | 0, z, hz => by
    obtain ⟨t, rfl⟩ := hz
    induction t using PiTensorProduct.induction_on with
    | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
    | smul_tprod r x =>
      simp [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply, cobarDeltaOne]
  | n + 1, z, hz => by
    obtain ⟨t, rfl⟩ := hz
    induction t using PiTensorProduct.induction_on with
    | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv
    | smul_tprod r x =>
      have hsucc : TensorAlgebra.tprod R (ReducedTensorWords R A) (n + 1) x =
          ι R (x 0) * TensorAlgebra.tprod R (ReducedTensorWords R A) n (fun i ↦ x i.succ) := by
        simp [TensorAlgebra.tprod_apply, List.ofFn_succ]
      rw [map_smul, map_smul, TensorPower.toTensorAlgebra_tprod, hsucc, 𝒜.cobarDeltaOne_mul,
        𝒜.cobarDeltaOne_ι, InternalGrading.koszulTwistAlgEquiv_apply,
        koszulTwist_tensorAlgebraPiece_ι, neg_mul]
      refine Submodule.smul_mem _ r (add_mem (neg_mem ?_) ?_)
      · exact ι_mul_mem_range_toTensorAlgebra _
          ⟨PiTensorProduct.tprod R _, TensorPower.toTensorAlgebra_tprod _⟩
      · exact ι_mul_mem_range_toTensorAlgebra _
          (cobarDeltaOne_mem_tensorPower n
            ⟨PiTensorProduct.tprod R _, TensorPower.toTensorAlgebra_tprod _⟩)

/-- `(δ₁ h)^(n + 1)` vanishes on tensor length `n + 1`. -/
private theorem pow_cobarDeltaOne_mul_homotopy_eq_zero :
    ∀ (n : ℕ) {z : TensorAlgebra R (ReducedTensorWords R A)},
      z ∈ LinearMap.range
          (TensorPower.toTensorAlgebra (R := R) (M := ReducedTensorWords R A) (n := n + 1)) →
        ((𝒜.cobarDeltaOne * cobarTensorHomotopy 𝒜.grading) ^ (n + 1)) z = 0
  | 0, z, hz => by
    simp [mul_apply_eq_comp, cobarTensorHomotopy_eq_zero_of_mem_tensorPower_one 𝒜.grading hz]
  | n + 1, z, hz => by
    rw [pow_succ, mul_apply_eq_comp, mul_apply_eq_comp]
    exact pow_cobarDeltaOne_mul_homotopy_eq_zero n
      (𝒜.cobarDeltaOne_mem_tensorPower (n + 1)
        (cobarTensorHomotopy_mem_tensorPower 𝒜.grading n hz))

private theorem exists_pow_cobarDeltaOneRes_mul_homotopy_eq_zero
    (z : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal.toSubmodule) :
    ∃ k : ℕ,
      ((𝒜.cobarDeltaOneRes *
          𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy) ^ k) z = 0 := by
  have hcoe (k : ℕ)
      (w : 𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal.toSubmodule) :
      ((((𝒜.cobarDeltaOneRes *
            𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy) ^ k) w :
        𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal.toSubmodule) :
        TensorAlgebra R (ReducedTensorWords R A)) =
      ((𝒜.cobarDeltaOne * cobarTensorHomotopy 𝒜.grading) ^ k)
        (w : TensorAlgebra R (ReducedTensorWords R A)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
      simpa only [cobarDeltaOneRes, mul_apply_eq_comp, LinearMap.restrict_apply,
        IsNonCounitalDGCoalgebra.coe_cobarUnperturbedContraction_homotopy] using
        congrArg (fun x ↦ 𝒜.cobarDeltaOne (cobarTensorHomotopy 𝒜.grading x)) ih
  let N : Submodule R (TensorAlgebra R (ReducedTensorWords R A)) :=
    { carrier := {x | ∃ k : ℕ, ((𝒜.cobarDeltaOne * cobarTensorHomotopy 𝒜.grading) ^ k) x = 0}
      zero_mem' := ⟨0, map_zero _⟩
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨max a b, ?_⟩
        rw [map_add, Module.End.pow_map_zero_of_le (le_max_left _ _) ha,
          Module.End.pow_map_zero_of_le (le_max_right _ _) hb, add_zero]
      smul_mem' := by
        rintro r x ⟨a, ha⟩
        exact ⟨a, by rw [map_smul, ha, smul_zero]⟩ }
  have hle :
      𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation.augmentationIdeal.toSubmodule ≤ N := by
    rw [𝒜.isNonCounitalDGCoalgebra_bar.cobarAugmentation_augmentationIdeal_le_iff]
    intro n x
    exact ⟨n + 1, 𝒜.pow_cobarDeltaOne_mul_homotopy_eq_zero n
      ⟨PiTensorProduct.tprod R x, TensorPower.toTensorAlgebra_tprod x⟩⟩
  obtain ⟨k, hk⟩ := hle z.property
  exact ⟨k, Subtype.ext (by rw [hcoe k z, hk]; rfl)⟩

private theorem isUnit_one_add_cobarDeltaOneRes_mul_homotopy :
    IsUnit (1 + 𝒜.cobarDeltaOneRes *
      𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero _
    𝒜.exists_pow_cobarDeltaOneRes_mul_homotopy_eq_zero

private theorem cobarDeconcatReducedDifferential_add_cobarDeltaOneRes :
    𝒜.isNonCounitalDGCoalgebra_bar.cobarDeconcatReducedDifferential + 𝒜.cobarDeltaOneRes =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedDifferential :=
  LinearMap.ext fun x ↦ Subtype.ext <| by
    simpa [cobarDeltaOneRes] using
      LinearMap.congr_fun 𝒜.cobarDeconcatDifferential_add_cobarDeltaOne x

private theorem cobarDeconcatReducedDifferential_add_cobarDeltaOneRes_sq :
    (𝒜.isNonCounitalDGCoalgebra_bar.cobarDeconcatReducedDifferential + 𝒜.cobarDeltaOneRes) ∘ₗ
        (𝒜.isNonCounitalDGCoalgebra_bar.cobarDeconcatReducedDifferential + 𝒜.cobarDeltaOneRes) =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarDeconcatReducedDifferential ∘ₗ
        𝒜.isNonCounitalDGCoalgebra_bar.cobarDeconcatReducedDifferential := by
  rw [𝒜.cobarDeconcatReducedDifferential_add_cobarDeltaOneRes,
    𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedDifferential_comp_self,
    𝒜.isNonCounitalDGCoalgebra_bar.cobarDeconcatReducedDifferential_comp_self]

/-- The perturbation series collapses to `δ₁` on the image of `A`, since `δ₁ (i a)` has tensor
length one and is killed by `h`. -/
private theorem perturbationSeries_incl (a : A) :
    𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbationSeries
        𝒜.cobarDeltaOneRes
        (𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.incl a) =
      𝒜.cobarDeltaOneRes (𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.incl a) := by
  set c := 𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction
  have hh : c.homotopy (𝒜.cobarDeltaOneRes (c.incl a)) = 0 := by
    apply Subtype.ext
    simp [c, cobarDeltaOneRes, cobarTensorIncl_apply, 𝒜.cobarDeltaOne_ι]
  have h1 : ((𝒜.cobarDeltaOneRes * c.homotopy) ^ 1) (𝒜.cobarDeltaOneRes (c.incl a)) = 0 := by
    simp [hh]
  simpa using c.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero
    𝒜.cobarDeltaOneRes 𝒜.isUnit_one_add_cobarDeltaOneRes_mul_homotopy h1

private theorem perturbedDifferential_eq_differential :
    𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbedDifferential
      𝒜.cobarDeltaOneRes = 𝒜.differential := by
  ext a
  rw [LinearSpecialContraction.perturbedDifferential_def, LinearMap.add_apply, LinearMap.zero_apply,
    zero_add, LinearMap.comp_apply, LinearMap.comp_apply, 𝒜.perturbationSeries_incl]
  simp only [cobarDeltaOneRes, LinearMap.restrict_apply,
    IsNonCounitalDGCoalgebra.cobarUnperturbedContraction_proj_apply,
    IsNonCounitalDGCoalgebra.coe_cobarUnperturbedContraction_incl,
    cobarTensorIncl_apply, 𝒜.cobarDeltaOne_ι, map_neg, cobarTensorProj_ι,
    𝒜.barDifferential_ofLetter, ReducedTensorWords.letter_ofLetter, ← 𝒜.differential_apply,
    𝒜.differential_koszulTwist_shift, InternalGrading.koszulTwist_koszulTwist, neg_neg]

private noncomputable def perturbedCobarContraction :
    LinearSpecialContraction
      (𝒜.isNonCounitalDGCoalgebra_bar.cobarDeconcatReducedDifferential + 𝒜.cobarDeltaOneRes)
      (𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbedDifferential
        𝒜.cobarDeltaOneRes) :=
  𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturb 𝒜.cobarDeltaOneRes
    𝒜.cobarDeconcatReducedDifferential_add_cobarDeltaOneRes_sq
    𝒜.isUnit_one_add_cobarDeltaOneRes_mul_homotopy

private theorem perturbedCobarContraction_incl :
    𝒜.perturbedCobarContraction.incl =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.incl := by
  ext a
  rw [perturbedCobarContraction, LinearSpecialContraction.perturb_incl, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, 𝒜.perturbationSeries_incl]
  have hh : 𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy
      (𝒜.cobarDeltaOneRes
        (𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.incl a)) = 0 := by
    apply Subtype.ext
    simp [cobarDeltaOneRes, cobarTensorIncl_apply, 𝒜.cobarDeltaOne_ι]
  rw [hh, sub_zero]

private def transportContraction {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {dM dM' : Module.End R M} {dN dN' : Module.End R N}
    (c : LinearSpecialContraction dM dN) (hdM : dM = dM') (hdN : dN = dN')
    (i : N →ₗ[R] M) (hi : c.incl = i) : LinearSpecialContraction dM' dN' where
  incl := i
  proj := c.proj
  homotopy := c.homotopy
  dM_comp_incl := hdM ▸ hdN ▸ hi ▸ c.dM_comp_incl
  proj_comp_dM := hdM ▸ hdN ▸ c.proj_comp_dM
  proj_comp_incl := hi ▸ c.proj_comp_incl
  dM_comp_homotopy_add_homotopy_comp_dM :=
    hdM ▸ hi ▸ c.dM_comp_homotopy_add_homotopy_comp_dM
  homotopy_comp_incl := hi ▸ c.homotopy_comp_incl
  proj_comp_homotopy := c.proj_comp_homotopy
  homotopy_comp_homotopy := c.homotopy_comp_homotopy

/-! ### The contraction of `Ω⁺ Tᶜ(sA)` onto `(A, m₁)` -/

/-- **The bar--cobar contraction on the augmentation ideal.**  For any nonunital `A∞` algebra `A`
over a commutative ring `R`, the augmentation ideal `Ω⁺ Tᶜ(sA)` of the cobar construction of its
reduced bar construction admits an explicit homogeneous special contraction onto `(A, m₁)`, whose
inclusion is the linear part of the canonical `A∞` morphism `A ⟶ Ω Tᶜ(sA)`. -/
noncomputable def cobarAugmentationIdealContraction :
    LinearSpecialContraction 𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedDifferential
      𝒜.differential :=
  transportContraction 𝒜.perturbedCobarContraction
    𝒜.cobarDeconcatReducedDifferential_add_cobarDeltaOneRes
    𝒜.perturbedDifferential_eq_differential
    𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.incl
    𝒜.perturbedCobarContraction_incl

/-- The inclusion of the cobar contraction is the linear part of the canonical `A∞` morphism
`A ⟶ Ω Tᶜ(sA)`. -/
@[simp]
theorem coe_cobarAugmentationIdealContraction_incl (a : A) :
    (𝒜.cobarAugmentationIdealContraction.incl a :
      TensorAlgebra R (ReducedTensorWords R A)) = 𝒜.toCobarBar.linearPart a :=
  (𝒜.isNonCounitalDGCoalgebra_bar.coe_cobarUnperturbedContraction_incl a).trans
    (𝒜.cobarTensorIncl_eq_toCobarBar_linearPart a)

/-- The inclusion of the cobar contraction has degree zero. -/
theorem isHomogeneous_cobarAugmentationIdealContraction_incl :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.incl
      𝒜.grading.piece 𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 0 :=
  𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_incl

private theorem isHomogeneous_perturbationSeries :
    LinearMap.IsHomogeneous
      (𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbationSeries
        𝒜.cobarDeltaOneRes)
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 1 := by
  have h0 : LinearMap.IsHomogeneous
      (𝒜.cobarDeltaOneRes * 𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy)
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 0 := by
    simpa only [Module.End.mul_eq_comp, neg_add_cancel] using
      𝒜.isHomogeneous_cobarDeltaOneRes.comp
        𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_homotopy
  have hinv := h0.ringInverse_one_add 𝒜.exists_pow_cobarDeltaOneRes_mul_homotopy_eq_zero
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp]
  simpa only [add_zero] using hinv.comp 𝒜.isHomogeneous_cobarDeltaOneRes

/-- The projection of the cobar contraction has degree zero. -/
theorem isHomogeneous_cobarAugmentationIdealContraction_proj :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.proj
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece 𝒜.grading.piece 0 := by
  have hproj : 𝒜.cobarAugmentationIdealContraction.proj =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.proj -
        𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.proj ∘ₗ
          𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbationSeries
            𝒜.cobarDeltaOneRes ∘ₗ
            𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy :=
    LinearSpecialContraction.perturb_proj ..
  rw [hproj]
  exact 𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_proj.sub <| by
    simpa only [neg_add_cancel, add_zero] using
      𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_proj.comp
        (𝒜.isHomogeneous_perturbationSeries.comp
          𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_homotopy)

/-- The homotopy of the cobar contraction has degree `-1`. -/
theorem isHomogeneous_cobarAugmentationIdealContraction_homotopy :
    LinearMap.IsHomogeneous 𝒜.cobarAugmentationIdealContraction.homotopy
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece
      𝒜.isNonCounitalDGCoalgebra_bar.cobarReducedGrading.piece (-1) := by
  have hhom : 𝒜.cobarAugmentationIdealContraction.homotopy =
      𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy -
        𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy ∘ₗ
          𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.perturbationSeries
            𝒜.cobarDeltaOneRes ∘ₗ
            𝒜.isNonCounitalDGCoalgebra_bar.cobarUnperturbedContraction.homotopy :=
    LinearSpecialContraction.perturb_homotopy ..
  rw [hhom]
  exact 𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_homotopy.sub <| by
    simpa only [neg_add_cancel, zero_add] using
      𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_homotopy.comp
        (𝒜.isHomogeneous_perturbationSeries.comp
          𝒜.isNonCounitalDGCoalgebra_bar.isHomogeneous_cobarUnperturbedContraction_homotopy)

end TauCeti.AInfinityAlgebra
