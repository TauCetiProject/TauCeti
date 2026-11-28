/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Basic
public import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism
import Mathlib.Algebra.Lie.Loop
import TauCeti.Algebra.Lie.BaseChange.Basic
import TauCeti.Algebra.Lie.BaseChange.Hom
import TauCeti.Algebra.Lie.Graded.Sign
import TauCeti.Algebra.Lie.KacMoody.Auxiliary
import TauCeti.Algebra.Lie.Presentation.Serre.Triangular
import TauCeti.Algebra.Lie.Subalgebra.Automorphism
import TauCeti.Algebra.Lie.Subalgebra.LieSpan
import TauCeti.LinearAlgebra.Matrix.Cartan.Generalized

/-!
# Triangular decomposition and Chevalley involution of a Kac–Moody presentation

Let `A` be a square matrix of integers and `R` a realization of `A` over a field `K`, with
presented Lie algebra `TauCeti.KacMoody.PresentedLieAlgebra R`. Over an arbitrary field `K` and for
an arbitrary integer matrix `A`, this file defines the Cartan Lie subalgebra
`TauCeti.KacMoody.cartanSubalgebra` (`𝔥`), using the positive and negative Lie subalgebras
`TauCeti.KacMoody.positiveSubalgebra` (`n⁺`) and `TauCeti.KacMoody.negativeSubalgebra` (`n⁻`) from
`TauCeti/Algebra/Lie/KacMoody/Basic.lean`, shows that `TauCeti.KacMoody.chevalleyInvolution`
exchanges `n⁺` and `n⁻` and preserves `𝔥`, proves local nilpotence of `ad eᵢ` and `ad fᵢ`, and
establishes the direct-sum triangular decomposition `𝔤 = n⁻ ⊕ 𝔥 ⊕ n⁺` together with the
intersection formula `⁅𝔤, 𝔤⁆ ∩ 𝔥 = cartanElement '' R.corootSpan` via the principal `ℤ`-grading
into `LieAlgebra.loopAlgebra K ℤ (PresentedLieAlgebra R)`.

When `A` is a generalized Cartan matrix (`Matrix.IsGeneralizedCartan A`), combining
`TauCeti.KacMoody.eq_zero_of_quotientTriangular_sum_eq_zero` from
`TauCeti/Algebra/Lie/KacMoody/Auxiliary.lean` additionally identifies both `n⁺` and `n⁻` with
`FreeLieAlgebra K I ⧸ serreIdeal K A`, proves linear independence of the raising and lowering
generators `eᵢ` and `fᵢ`, and shows that
`TauCeti.KacMoody.serreHom R : Matrix.ToLieAlgebra K A →ₗ⁅K⁆ PresentedLieAlgebra R` is injective.

The Chevalley involution compatibility with `serreHom` closely follows `serreChevalleyInvolution`
in `TauCeti/Algebra/Lie/Presentation/Serre/Automorphism.lean`, while local nilpotence of `ad eᵢ`
and the spanning triangular decomposition transport `engel_serreE_eq_top` from
`TauCeti/Algebra/Lie/Presentation/Serre/Integrable.lean` and
`lieSpan_serreF_sup_span_serreH_sup_lieSpan_serreE_eq_top` from
`TauCeti/Algebra/Lie/Presentation/Serre/Triangular.lean` along `TauCeti.KacMoody.serreHom`.

## Main definitions

* `TauCeti.KacMoody.cartanSubalgebra`: the Lie subalgebra `𝔥` of
  `TauCeti.KacMoody.PresentedLieAlgebra R`, together with the linear equivalence
  `TauCeti.KacMoody.cartanEquiv : H ≃ₗ[K] cartanSubalgebra R` when `cartanElement R` is injective.
* `TauCeti.KacMoody.triangularEquiv`: the direct-sum triangular linear equivalence
  `(negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) ≃ₗ[K] PresentedLieAlgebra R`.
* `TauCeti.KacMoody.negativeProjection`, `TauCeti.KacMoody.cartanProjection`, and
  `TauCeti.KacMoody.positiveProjection`: the bundled linear projections out of
  `TauCeti.KacMoody.PresentedLieAlgebra R`.
* `TauCeti.KacMoody.positiveEquiv` and `TauCeti.KacMoody.negativeEquiv`: the Lie algebra
  isomorphisms `(FreeLieAlgebra K I ⧸ serreIdeal K A) ≃ₗ⁅K⁆ n⁺` and `≃ₗ⁅K⁆ n⁻` for a
  generalized Cartan matrix.

## Main results

* `TauCeti.KacMoody.engel_positiveGenerator_eq_top` and
  `TauCeti.KacMoody.engel_negativeGenerator_eq_top`: `ad eᵢ` and `ad fᵢ` act locally nilpotently.
* `TauCeti.KacMoody.negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top`:
  the spanning triangular decomposition `𝔤 = n⁻ + 𝔥 + n⁺`.
* `TauCeti.KacMoody.disjoint_negativeSubalgebra_cartanSubalgebra_sup_positiveSubalgebra` and
  `TauCeti.KacMoody.disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra`:
  direct-sum disjointness of the triangular factors over any field `K` and integer matrix `A`.
* `TauCeti.KacMoody.derivedSeries_one_inf_cartanSubalgebra`:
  `⁅𝔤, 𝔤⁆ ∩ 𝔥 = R.corootSpan.map (cartanElement R)`.
* `TauCeti.KacMoody.positiveQuotientHom_injective` and
  `TauCeti.KacMoody.negativeQuotientHom_injective`: injectivity of the one-sided Serre quotient
  maps for a generalized Cartan matrix.
* `TauCeti.KacMoody.linearIndependent_positiveGenerator` and
  `TauCeti.KacMoody.linearIndependent_negativeGenerator`: linear independence of `eᵢ` and `fᵢ`.
* `TauCeti.KacMoody.serreHom_injective`: injectivity of `TauCeti.KacMoody.serreHom` for a
  generalized Cartan matrix.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  Theorem 1.2, §1.3, Proposition 1.6, and Lemma 3.5.
-/

public section

open scoped Pointwise TensorProduct
open LieAlgebra LieSubalgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-! ## The triangular subalgebras -/

/-- The Cartan subalgebra `𝔥` of `TauCeti.KacMoody.PresentedLieAlgebra R`, the image of `H` under
`TauCeti.KacMoody.cartanElement`. -/
noncomputable def cartanSubalgebra : LieSubalgebra K (PresentedLieAlgebra R) where
  toSubmodule := LinearMap.range (cartanElement R)
  lie_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; simp

/-- The underlying submodule of `TauCeti.KacMoody.cartanSubalgebra` is the range of
`TauCeti.KacMoody.cartanElement`. -/
@[simp] theorem cartanSubalgebra_toSubmodule :
    (cartanSubalgebra R).toSubmodule = LinearMap.range (cartanElement R) := (rfl)

/-- Membership in `TauCeti.KacMoody.cartanSubalgebra` means coming from `H`. -/
theorem mem_cartanSubalgebra_iff {y : PresentedLieAlgebra R} :
    y ∈ cartanSubalgebra R ↔ ∃ x : H, cartanElement R x = y := by
  rw [← LieSubalgebra.mem_toSubmodule, cartanSubalgebra_toSubmodule, LinearMap.mem_range]

/-- Every Cartan element lies in `TauCeti.KacMoody.cartanSubalgebra`. -/
@[simp] theorem cartanElement_mem_cartanSubalgebra (x : H) :
    cartanElement R x ∈ cartanSubalgebra R :=
  (mem_cartanSubalgebra_iff R).2 ⟨x, rfl⟩

instance : IsLieAbelian (cartanSubalgebra R) where
  trivial := by
    rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
    obtain ⟨x₁, rfl⟩ := (mem_cartanSubalgebra_iff R).1 hy₁
    obtain ⟨x₂, rfl⟩ := (mem_cartanSubalgebra_iff R).1 hy₂
    exact Subtype.ext (by simp)

section CartanEquiv

variable {R} (hinj : Function.Injective (cartanElement R))

/-- The linear equivalence between the realization `H` and `TauCeti.KacMoody.cartanSubalgebra R`
induced by `TauCeti.KacMoody.cartanElement` whenever `cartanElement R` is injective (in particular
for any generalized Cartan matrix via `TauCeti.KacMoody.cartanElement_injective`). -/
noncomputable def cartanEquiv : H ≃ₗ[K] cartanSubalgebra R :=
  (LinearEquiv.ofInjective (cartanElement R) hinj).trans
    (LinearEquiv.ofEq _ _ (cartanSubalgebra_toSubmodule R).symm)

/-- Coercing `TauCeti.KacMoody.cartanEquiv` to the ambient Lie algebra gives
`TauCeti.KacMoody.cartanElement`. -/
@[simp] theorem coe_cartanEquiv_apply (x : H) :
    (cartanEquiv hinj x : PresentedLieAlgebra R) = cartanElement R x := by
  rw [cartanEquiv, LinearEquiv.trans_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans (LinearEquiv.ofInjective_apply (cartanElement R) x)

/-- The inverse of `TauCeti.KacMoody.cartanEquiv` recovers `x` from `cartanElement R x`. -/
@[simp] theorem cartanEquiv_symm_cartanElement (x : H) :
    (cartanEquiv hinj).symm
        ⟨cartanElement R x, cartanElement_mem_cartanSubalgebra R x⟩ = x :=
  (cartanEquiv hinj).injective (Subtype.ext (by simp))

/-- Applying `TauCeti.KacMoody.cartanElement` to `(cartanEquiv hinj).symm y` recovers
`(y : PresentedLieAlgebra R)`. -/
@[simp] theorem cartanElement_cartanEquiv_symm (y : cartanSubalgebra R) :
    cartanElement R ((cartanEquiv hinj).symm y) = y := by
  conv_rhs => rw [← (cartanEquiv hinj).apply_symm_apply y, coe_cartanEquiv_apply]

end CartanEquiv

/-- `TauCeti.KacMoody.serreHom` maps the positive part of Serre's presentation onto
`TauCeti.KacMoody.positiveSubalgebra`. -/
theorem map_serreHom_lieSpan_serreE [DecidableEq I] :
    (lieSpan K (Matrix.ToLieAlgebra K A) (Set.range (serreE K A))).map (serreHom R) =
      positiveSubalgebra R := by
  rw [positiveSubalgebra_def]
  exact map_lieSpan_range_of_surjective (serreHom R) Function.surjective_id (serreHom_serreE R)

/-- `TauCeti.KacMoody.serreHom` maps the negative part of Serre's presentation onto
`TauCeti.KacMoody.negativeSubalgebra`. -/
theorem map_serreHom_lieSpan_serreF [DecidableEq I] :
    (lieSpan K (Matrix.ToLieAlgebra K A) (Set.range (serreF K A))).map (serreHom R) =
      negativeSubalgebra R := by
  rw [negativeSubalgebra_def]
  exact map_lieSpan_range_of_surjective (serreHom R) Function.surjective_id (serreHom_serreF R)

/-! ## The Chevalley involution -/

section Chevalley

/-- `TauCeti.KacMoody.serreHom` intertwines the Chevalley involutions of Serre's presentation and
of the full realization. -/
@[simp] theorem chevalleyInvolution_comp_serreHom [DecidableEq I] :
    (chevalleyInvolution R : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R).comp (serreHom R) =
      (serreHom R).comp
        (serreChevalleyInvolution K A : Matrix.ToLieAlgebra K A →ₗ⁅K⁆ Matrix.ToLieAlgebra K A) :=
  serre_hom_ext (fun _ => by simp) fun _ => by simp

/-- The Chevalley involution carries `n⁺` onto `n⁻`. -/
@[simp] theorem map_chevalleyInvolution_positiveSubalgebra :
    (positiveSubalgebra R).map
        (chevalleyInvolution R : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) =
      negativeSubalgebra R := by
  have hcomp : (chevalleyInvolution R : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) ∘
      positiveGenerator R = -negativeGenerator R := by ext i; simp
  rw [positiveSubalgebra_def, negativeSubalgebra_def, LieSubalgebra.map_lieSpan,
    ← Set.range_comp, hcomp, ← Set.neg_range', LieSubalgebra.lieSpan_neg]

/-- The Chevalley involution carries `n⁻` onto `n⁺`. -/
@[simp] theorem map_chevalleyInvolution_negativeSubalgebra :
    (negativeSubalgebra R).map
        (chevalleyInvolution R : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) =
      positiveSubalgebra R := by
  simpa [chevalleyInvolution_symm] using
    (LieSubalgebra.map_symm_eq_iff (chevalleyInvolution R)).2
      (map_chevalleyInvolution_positiveSubalgebra R)

/-- The Chevalley involution preserves `𝔥`. -/
@[simp] theorem map_chevalleyInvolution_cartanSubalgebra :
    (cartanSubalgebra R).map
        (chevalleyInvolution R : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) =
      cartanSubalgebra R :=
  LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg (chevalleyInvolution R) fun _ hy => by
    obtain ⟨x, rfl⟩ := (mem_cartanSubalgebra_iff R).1 hy; simp

end Chevalley

/-! ## Local nilpotence and spanning triangular decomposition -/

/-- **Local nilpotence of `ad eᵢ`.** Every element of `TauCeti.KacMoody.PresentedLieAlgebra R` is
killed by some power of `ad (positiveGenerator R i)`. -/
theorem engel_positiveGenerator_eq_top (i : I) :
    LieSubalgebra.engel K (positiveGenerator R i) = ⊤ := by
  classical
  rw [eq_top_iff, ← LieSubalgebra.toSubmodule_le_toSubmodule, top_toSubmodule,
    ← range_serreHom_sup_range_cartanElement R, sup_le_iff]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    have hu : u ∈ LieSubalgebra.engel K (serreE K A i) := by rw [engel_serreE_eq_top]; trivial
    obtain ⟨n, hn⟩ := (LieSubalgebra.mem_engel_iff K _ _).1 hu
    refine (LieSubalgebra.mem_engel_iff K _ _).2 ⟨n, ?_⟩
    rw [LieHom.coe_toLinearMap, ← serreHom_serreE R i, ← LieHom.map_ad_pow, hn, map_zero]
  · rintro _ ⟨x, rfl⟩
    refine (LieSubalgebra.mem_engel_iff K _ _).2 ⟨2, ?_⟩
    rw [ad_pow_succ_apply, pow_one, ad_apply,
      ← lie_skew (positiveGenerator R i) (cartanElement R x), lie_cartanElement_positiveGenerator]
    simp

/-- **Local nilpotence of `ad fᵢ`.** Every element of `TauCeti.KacMoody.PresentedLieAlgebra R` is
killed by some power of `ad (negativeGenerator R i)`. -/
theorem engel_negativeGenerator_eq_top (i : I) :
    LieSubalgebra.engel K (negativeGenerator R i) = ⊤ := by
  have h := (chevalleyInvolution R).map_engel (positiveGenerator R i)
  rw [engel_positiveGenerator_eq_top, chevalleyInvolution_positiveGenerator,
    LieSubalgebra.engel_neg] at h
  exact eq_top_iff.2 fun y _ => h ▸ ⟨chevalleyInvolution R y, trivial, by simp⟩

/-- The derived subalgebra `𝔤'` (the image of `TauCeti.KacMoody.serreHom`) is the sum of `n⁻`, the
image of `R.corootSpan`, and `n⁺`. -/
theorem range_serreHom_toSubmodule_eq [DecidableEq I] :
    (serreHom R).range.toSubmodule =
      (negativeSubalgebra R).toSubmodule ⊔ R.corootSpan.map (cartanElement R) ⊔
        (positiveSubalgebra R).toSubmodule := by
  have htop := congrArg (Submodule.map (serreHom R).toLinearMap)
    (lieSpan_serreF_sup_span_serreH_sup_lieSpan_serreE_eq_top K A)
  rw [Submodule.map_top, Submodule.map_sup, Submodule.map_sup, ← LieSubalgebra.map_toSubmodule,
    ← LieSubalgebra.map_toSubmodule, map_serreHom_lieSpan_serreF,
    map_serreHom_lieSpan_serreE] at htop
  have hH : (Submodule.span K (Set.range (serreH K A))).map (serreHom R).toLinearMap =
      R.corootSpan.map (cartanElement R) := by
    rw [R.corootSpan_def, LinearMap.map_span, LinearMap.map_span, ← Set.range_comp,
      ← Set.range_comp]
    congr 2; funext i; exact serreHom_serreH R i
  simpa only [LieHom.range_toSubmodule, LinearMap.range_eq_map, hH] using htop.symm

/-- **The spanning triangular decomposition**: `TauCeti.KacMoody.PresentedLieAlgebra R` is the sum
`n⁻ + 𝔥 + n⁺`. -/
theorem negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top :
    (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ⊔
      (positiveSubalgebra R).toSubmodule = ⊤ := by
  classical
  rw [eq_top_iff, ← range_serreHom_sup_range_cartanElement R, range_serreHom_toSubmodule_eq R,
    cartanSubalgebra_toSubmodule]
  exact sup_le (sup_le (sup_le (le_sup_of_le_left le_sup_left)
    (LinearMap.map_le_range.trans (le_sup_of_le_left le_sup_right))) le_sup_right)
    (le_sup_of_le_left le_sup_right)

/-! ## Principal `ℤ`-grading and direct-sum triangular decomposition -/

section PrincipalGrading

private theorem satisfiesRelations_principalGrading :
    SatisfiesRelations R
      ((TensorProduct.mk K (AddMonoidAlgebra K ℤ) (PresentedLieAlgebra R)
        (AddMonoidAlgebra.single 0 1)).comp (cartanElement R))
      (fun i => AddMonoidAlgebra.single 1 1 ⊗ₜ[K] positiveGenerator R i)
      (fun i => AddMonoidAlgebra.single (-1) 1 ⊗ₜ[K] negativeGenerator R i) where
  lie_cartan_cartan x y := by simp
  lie_cartan_positive x j := by simp
  lie_cartan_negative x j := by simp [TensorProduct.tmul_neg, TensorProduct.tmul_smul]
  lie_positive_negative_self i := by simp [-LaurentPolynomial.single_eq_C_mul_T]
  lie_positive_negative_of_ne i j hij := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, lie_positiveGenerator_negativeGenerator_of_ne R hij,
      TensorProduct.tmul_zero]
  serre_positive i j := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, LieAlgebra.ExtendScalars.ad_pow_tmul,
      ad_pow_lie_positiveGenerator_positiveGenerator, TensorProduct.tmul_zero]
  serre_negative i j := by
    rw [LieAlgebra.ExtendScalars.bracket_tmul, LieAlgebra.ExtendScalars.ad_pow_tmul,
      ad_pow_lie_negativeGenerator_negativeGenerator, TensorProduct.tmul_zero]

private noncomputable def principalGrading :
    PresentedLieAlgebra R →ₗ⁅K⁆ LieAlgebra.loopAlgebra K ℤ (PresentedLieAlgebra R) :=
  lift (satisfiesRelations_principalGrading R)

private noncomputable def principalGradingLeftInv :
    LieAlgebra.loopAlgebra K ℤ (PresentedLieAlgebra R) →ₗ⁅K⁆ PresentedLieAlgebra R :=
  ((LieHom.id : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R).liftBaseChange K).comp
    (LieAlgebra.ExtendScalars.map (AddMonoidAlgebra.lift K K ℤ 1) LieHom.id)

private theorem principalGradingLeftInv_comp :
    (principalGradingLeftInv R).comp (principalGrading R) = LieHom.id := by
  ext <;> simp [principalGradingLeftInv, principalGrading, -LaurentPolynomial.single_eq_C_mul_T]

private theorem principalGrading_injective : Function.Injective (principalGrading R) :=
  Function.LeftInverse.injective (g := principalGradingLeftInv R) fun z => by
    simpa using DFunLike.congr_fun (principalGradingLeftInv_comp R) z

private noncomputable abbrev loopGrade :
    ℤ → Submodule K (LieAlgebra.loopAlgebra K ℤ (PresentedLieAlgebra R)) :=
  fun a => DirectSum.decomposeTensor (AddMonoidAlgebra.grade K) (PresentedLieAlgebra R) a

private theorem single_tmul_mem_loopGrade (d : ℤ) (u : PresentedLieAlgebra R) :
    AddMonoidAlgebra.single d (1 : K) ⊗ₜ[K] u ∈ loopGrade R d := by
  rw [loopGrade, DirectSum.decomposeTensor_apply]
  exact ⟨⟨AddMonoidAlgebra.single d 1, AddMonoidAlgebra.single_mem_grade d 1⟩ ⊗ₜ[K] u, rfl⟩

private theorem negativeSubalgebra_le_comap_signSubalgebra :
    negativeSubalgebra R ≤
      (signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) .neg).comap (principalGrading R) := by
  rw [negativeSubalgebra_def, lieSpan_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, LieSubalgebra.mem_comap, principalGrading, lift_negativeGenerator]
  exact le_signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) (-1 : ℤ)
    (single_tmul_mem_loopGrade R (-1) (negativeGenerator R i))

private theorem cartanSubalgebra_le_comap_signSubalgebra :
    cartanSubalgebra R ≤
      (signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) .zero).comap (principalGrading R) := by
  intro y hy
  obtain ⟨x, rfl⟩ := (mem_cartanSubalgebra_iff R).1 hy
  rw [LieSubalgebra.mem_comap, principalGrading, lift_cartanElement]
  exact le_signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) (0 : ℤ)
    (single_tmul_mem_loopGrade R 0 (cartanElement R x))

private theorem positiveSubalgebra_le_comap_signSubalgebra :
    positiveSubalgebra R ≤
      (signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) .pos).comap (principalGrading R) := by
  rw [positiveSubalgebra_def, lieSpan_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, LieSubalgebra.mem_comap, principalGrading, lift_positiveGenerator]
  exact le_signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) (1 : ℤ)
    (single_tmul_mem_loopGrade R 1 (positiveGenerator R i))

private theorem eq_zero_of_add_add_eq_zero {x y w : PresentedLieAlgebra R}
    (hx : x ∈ negativeSubalgebra R) (hy : y ∈ cartanSubalgebra R) (hw : w ∈ positiveSubalgebra R)
    (hsum : x + y + w = 0) : x = 0 ∧ y = 0 ∧ w = 0 := by
  have hindep :=
    (isInternal_signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ)).submodule_iSupIndep
  have hcomp : ∀ {s t₁ t₂ : SignType}, t₁ ≠ s → t₂ ≠ s →
      ∀ {a b c : LieAlgebra.loopAlgebra K ℤ (PresentedLieAlgebra R)},
        a ∈ signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) s →
        b ∈ signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) t₁ →
        c ∈ signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) t₂ →
        a + b + c = 0 → a = 0 := by
    intro s t₁ t₂ ht₁ ht₂ a b c ha hb hc heq
    have ha' : a ∈ ⨆ (t) (_ : t ≠ s),
        (signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) t).toSubmodule := by
      have hneg : a = -(b + c) := eq_neg_of_add_eq_zero_left (by rwa [← add_assoc])
      rw [hneg]
      exact neg_mem (add_mem (Submodule.mem_iSup_of_mem t₁ (Submodule.mem_iSup_of_mem ht₁ hb))
        (Submodule.mem_iSup_of_mem t₂ (Submodule.mem_iSup_of_mem ht₂ hc)))
    exact Submodule.disjoint_def.1 (hindep s) a ha ha'
  have hx' : principalGrading R x ∈ signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) .neg :=
    negativeSubalgebra_le_comap_signSubalgebra R hx
  have hy' : principalGrading R y ∈ signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) .zero :=
    cartanSubalgebra_le_comap_signSubalgebra R hy
  have hw' : principalGrading R w ∈ signSubalgebra (loopGrade R) (AddMonoidHom.id ℤ) .pos :=
    positiveSubalgebra_le_comap_signSubalgebra R hw
  have hmap : principalGrading R x + principalGrading R y + principalGrading R w = 0 := by
    rw [← map_add, ← map_add, hsum, map_zero]
  refine ⟨principalGrading_injective R <|
      (hcomp (by decide) (by decide) hx' hy' hw' hmap).trans (map_zero _).symm,
    principalGrading_injective R <|
      (hcomp (by decide) (by decide) hy' hx' hw'
        (by rw [add_comm (principalGrading R y), hmap])).trans (map_zero _).symm,
    principalGrading_injective R <|
      (hcomp (by decide) (by decide) hw' hx' hy'
        (by rw [← hmap]; abel)).trans (map_zero _).symm⟩

end PrincipalGrading

/-- Over any field `K` and for any integer matrix `A`, `n⁻` has trivial intersection with
`𝔥 + n⁺`. -/
theorem disjoint_negativeSubalgebra_cartanSubalgebra_sup_positiveSubalgebra :
    Disjoint (negativeSubalgebra R).toSubmodule
      ((cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule) := by
  rw [Submodule.disjoint_def]; intro x hx hyw
  rcases Submodule.mem_sup.1 hyw with ⟨y, hy, w, hw, hsum⟩
  exact neg_eq_zero.1
    (eq_zero_of_add_add_eq_zero R (neg_mem hx) hy hw (by rw [add_assoc, hsum, neg_add_cancel])).1

/-- Over any field `K` and for any integer matrix `A`, `n⁻ + n⁺` has trivial intersection with
`𝔥`. -/
theorem disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra :
    Disjoint ((negativeSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule)
      (cartanSubalgebra R).toSubmodule := by
  rw [Submodule.disjoint_def]; intro z hxw hy
  rcases Submodule.mem_sup.1 hxw with ⟨x, hx, w, hw, hsum⟩
  exact neg_eq_zero.1
    (eq_zero_of_add_add_eq_zero R hx (neg_mem hy) hw (by rw [← hsum]; abel)).2.1

/-- Over any field `K` and for any integer matrix `A`, `n⁻` and `n⁺` have trivial intersection. -/
theorem disjoint_negativeSubalgebra_positiveSubalgebra :
    Disjoint (negativeSubalgebra R).toSubmodule (positiveSubalgebra R).toSubmodule :=
  (disjoint_negativeSubalgebra_cartanSubalgebra_sup_positiveSubalgebra R).mono_right le_sup_right

/-- Over any field `K` and for any integer matrix `A`, `n⁻` and `𝔥` have trivial intersection. -/
theorem disjoint_negativeSubalgebra_cartanSubalgebra :
    Disjoint (negativeSubalgebra R).toSubmodule (cartanSubalgebra R).toSubmodule :=
  (disjoint_negativeSubalgebra_cartanSubalgebra_sup_positiveSubalgebra R).mono_right le_sup_left

/-- Over any field `K` and for any integer matrix `A`, `n⁺` and `𝔥` have trivial intersection. -/
theorem disjoint_positiveSubalgebra_cartanSubalgebra :
    Disjoint (positiveSubalgebra R).toSubmodule (cartanSubalgebra R).toSubmodule :=
  (disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra R).mono_left le_sup_right

private noncomputable def triangularLinearMap :
    (negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) →ₗ[K]
      PresentedLieAlgebra R where
  toFun p := (p.1 : PresentedLieAlgebra R) + p.2.1 + p.2.2
  map_add' p q := by simp; abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, smul_add, RingHom.id_apply]

private theorem triangularLinearMap_bijective : Function.Bijective (triangularLinearMap R) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun ⟨x, y, w⟩ h => ?_, fun z => ?_⟩
  · obtain ⟨hx, hy, hw⟩ := eq_zero_of_add_add_eq_zero R x.property y.property w.property h
    exact Prod.ext (Subtype.ext hx) (Prod.ext (Subtype.ext hy) (Subtype.ext hw))
  · have hz : z ∈ (negativeSubalgebra R).toSubmodule ⊔ (cartanSubalgebra R).toSubmodule ⊔
        (positiveSubalgebra R).toSubmodule := by
      rw [negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra_eq_top]
      exact Submodule.mem_top
    obtain ⟨ab, hab, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hab
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩, ⟨w, hw⟩), rfl⟩

/-- **The direct-sum triangular decomposition**: over any field `K` and for any integer matrix `A`,
addition gives a `K`-linear isomorphism `n⁻ ⊕ 𝔥 ⊕ n⁺ ≃ₗ[K] PresentedLieAlgebra R`. -/
noncomputable def triangularEquiv :
    (negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) ≃ₗ[K]
      PresentedLieAlgebra R :=
  LinearEquiv.ofBijective (triangularLinearMap R) (triangularLinearMap_bijective R)

/-- `TauCeti.KacMoody.triangularEquiv` acts by adding the three components. -/
@[simp] theorem triangularEquiv_apply
    (p : negativeSubalgebra R × cartanSubalgebra R × positiveSubalgebra R) :
    triangularEquiv R p = (p.1 : PresentedLieAlgebra R) + p.2.1 + p.2.2 :=
  (rfl)

/-- `TauCeti.KacMoody.triangularEquiv.symm` sends an element of `n⁻` to `(x, 0, 0)`. -/
@[simp] theorem triangularEquiv_symm_coe_negative (x : negativeSubalgebra R) :
    (triangularEquiv R).symm (x : PresentedLieAlgebra R) = (x, 0, 0) :=
  (triangularEquiv R).injective (by simp)

/-- `TauCeti.KacMoody.triangularEquiv.symm` sends an element of `𝔥` to `(0, y, 0)`. -/
@[simp] theorem triangularEquiv_symm_coe_cartan (y : cartanSubalgebra R) :
    (triangularEquiv R).symm (y : PresentedLieAlgebra R) = (0, y, 0) :=
  (triangularEquiv R).injective (by simp)

/-- `TauCeti.KacMoody.triangularEquiv.symm` sends an element of `n⁺` to `(0, 0, z)`. -/
@[simp] theorem triangularEquiv_symm_coe_positive (z : positiveSubalgebra R) :
    (triangularEquiv R).symm (z : PresentedLieAlgebra R) = (0, 0, z) :=
  (triangularEquiv R).injective (by simp)

/-- `TauCeti.KacMoody.triangularEquiv.symm` sends the lowering generator `fᵢ` to `(fᵢ, 0, 0)`. -/
@[simp] theorem triangularEquiv_symm_negativeGenerator (i : I) :
    (triangularEquiv R).symm (negativeGenerator R i) =
      (⟨negativeGenerator R i, negativeGenerator_mem_negativeSubalgebra R i⟩, 0, 0) :=
  (triangularEquiv R).injective (by simp)

/-- `TauCeti.KacMoody.triangularEquiv.symm` sends `cartanElement R x` to `(0, x, 0)`. -/
@[simp] theorem triangularEquiv_symm_cartanElement (x : H) :
    (triangularEquiv R).symm (cartanElement R x) =
      (0, ⟨cartanElement R x, cartanElement_mem_cartanSubalgebra R x⟩, 0) :=
  (triangularEquiv R).injective (by simp)

/-- `TauCeti.KacMoody.triangularEquiv.symm` sends the raising generator `eᵢ` to `(0, 0, eᵢ)`. -/
@[simp] theorem triangularEquiv_symm_positiveGenerator (i : I) :
    (triangularEquiv R).symm (positiveGenerator R i) =
      (0, 0, ⟨positiveGenerator R i, positiveGenerator_mem_positiveSubalgebra R i⟩) :=
  (triangularEquiv R).injective (by simp)

/-- **Intersection of the derived algebra with the Cartan subalgebra**: the image of Serre's
presentation meets `LinearMap.range (cartanElement R)` in the image of `R.corootSpan`. -/
theorem range_serreHom_inf_range_cartanElement [DecidableEq I] :
    (serreHom R).range.toSubmodule ⊓ LinearMap.range (cartanElement R) =
      R.corootSpan.map (cartanElement R) := by
  rw [range_serreHom_toSubmodule_eq, sup_right_comm, sup_comm,
    sup_inf_assoc_of_le _ LinearMap.map_le_range, ← cartanSubalgebra_toSubmodule,
    (disjoint_negativeSubalgebra_sup_positiveSubalgebra_cartanSubalgebra R).eq_bot, sup_bot_eq]

/-- **Intersection of `⁅𝔤, 𝔤⁆` with `𝔥`**: the derived subalgebra meets `𝔥` in the image of the
coroot span `R.corootSpan`. -/
theorem derivedSeries_one_inf_cartanSubalgebra :
    (derivedSeries K (PresentedLieAlgebra R) 1).toSubmodule ⊓
        (cartanSubalgebra R).toSubmodule =
      R.corootSpan.map (cartanElement R) := by
  classical
  have hd : (derivedSeries K (PresentedLieAlgebra R) 1).toSubmodule =
      (serreHom R).range.toSubmodule := by
    simpa using (congrArg LieSubalgebra.toSubmodule (range_serreHom_eq_derivedSeries R)).symm
  rw [hd, cartanSubalgebra_toSubmodule, range_serreHom_inf_range_cartanElement R]

/-! ## Cartan stability and triangular projections -/

/-- The Cartan subalgebra preserves the positive subalgebra under the adjoint action. -/
theorem lie_mem_positiveSubalgebra_of_mem_cartanSubalgebra
    {x y : PresentedLieAlgebra R} (hx : x ∈ cartanSubalgebra R)
    (hy : y ∈ positiveSubalgebra R) : ⁅x, y⁆ ∈ positiveSubalgebra R := by
  obtain ⟨h, rfl⟩ := (mem_cartanSubalgebra_iff R).1 hx
  rw [positiveSubalgebra_def] at hy ⊢
  exact LieSubalgebra.lie_mem_lieSpan_range_of_lie_eq_smul
    (lie_cartanElement_positiveGenerator R h) hy

/-- The Cartan subalgebra preserves the negative subalgebra under the adjoint action. -/
theorem lie_mem_negativeSubalgebra_of_mem_cartanSubalgebra
    {x y : PresentedLieAlgebra R} (hx : x ∈ cartanSubalgebra R)
    (hy : y ∈ negativeSubalgebra R) : ⁅x, y⁆ ∈ negativeSubalgebra R := by
  obtain ⟨h, rfl⟩ := (mem_cartanSubalgebra_iff R).1 hx
  rw [negativeSubalgebra_def] at hy ⊢
  exact LieSubalgebra.lie_mem_lieSpan_range_of_lie_eq_smul
    (fun j => by rw [lie_cartanElement_negativeGenerator, ← neg_smul]) hy

/-- The projection of `TauCeti.KacMoody.PresentedLieAlgebra R` onto `n⁻` along the triangular
decomposition. -/
noncomputable def negativeProjection :
    PresentedLieAlgebra R →ₗ[K] negativeSubalgebra R :=
  (LinearMap.fst K (negativeSubalgebra R) (cartanSubalgebra R × positiveSubalgebra R)).comp
    (triangularEquiv R).symm.toLinearMap

/-- The projection of `TauCeti.KacMoody.PresentedLieAlgebra R` onto `𝔥` along the triangular
decomposition. -/
noncomputable def cartanProjection :
    PresentedLieAlgebra R →ₗ[K] cartanSubalgebra R :=
  (LinearMap.fst K (cartanSubalgebra R) (positiveSubalgebra R)).comp
    ((LinearMap.snd K (negativeSubalgebra R) (cartanSubalgebra R × positiveSubalgebra R)).comp
      (triangularEquiv R).symm.toLinearMap)

/-- The projection of `TauCeti.KacMoody.PresentedLieAlgebra R` onto `n⁺` along the triangular
decomposition. -/
noncomputable def positiveProjection :
    PresentedLieAlgebra R →ₗ[K] positiveSubalgebra R :=
  (LinearMap.snd K (cartanSubalgebra R) (positiveSubalgebra R)).comp
    ((LinearMap.snd K (negativeSubalgebra R) (cartanSubalgebra R × positiveSubalgebra R)).comp
      (triangularEquiv R).symm.toLinearMap)

@[simp] theorem negativeProjection_coe_negativeSubalgebra (u : negativeSubalgebra R) :
    negativeProjection R (u : PresentedLieAlgebra R) = u := by
  simp [negativeProjection]

@[simp] theorem negativeProjection_coe_cartanSubalgebra (y : cartanSubalgebra R) :
    negativeProjection R (y : PresentedLieAlgebra R) = 0 := by
  simp [negativeProjection]

@[simp] theorem negativeProjection_cartanElement (x : H) :
    negativeProjection R (cartanElement R x) = 0 := by
  simp [negativeProjection]

@[simp] theorem negativeProjection_coe_positiveSubalgebra (w : positiveSubalgebra R) :
    negativeProjection R (w : PresentedLieAlgebra R) = 0 := by
  simp [negativeProjection]

@[simp] theorem cartanProjection_coe_negativeSubalgebra (u : negativeSubalgebra R) :
    cartanProjection R (u : PresentedLieAlgebra R) = 0 := by
  simp [cartanProjection]

@[simp] theorem cartanProjection_coe_cartanSubalgebra (y : cartanSubalgebra R) :
    cartanProjection R (y : PresentedLieAlgebra R) = y := by
  simp [cartanProjection]

@[simp] theorem cartanProjection_cartanElement (x : H) :
    cartanProjection R (cartanElement R x) =
      ⟨cartanElement R x, cartanElement_mem_cartanSubalgebra R x⟩ := by
  simp [cartanProjection]

@[simp] theorem cartanProjection_coe_positiveSubalgebra (w : positiveSubalgebra R) :
    cartanProjection R (w : PresentedLieAlgebra R) = 0 := by
  simp [cartanProjection]

@[simp] theorem positiveProjection_coe_negativeSubalgebra (u : negativeSubalgebra R) :
    positiveProjection R (u : PresentedLieAlgebra R) = 0 := by
  simp [positiveProjection]

@[simp] theorem positiveProjection_coe_cartanSubalgebra (y : cartanSubalgebra R) :
    positiveProjection R (y : PresentedLieAlgebra R) = 0 := by
  simp [positiveProjection]

@[simp] theorem positiveProjection_cartanElement (x : H) :
    positiveProjection R (cartanElement R x) = 0 := by
  simp [positiveProjection]

@[simp] theorem positiveProjection_coe_positiveSubalgebra (w : positiveSubalgebra R) :
    positiveProjection R (w : PresentedLieAlgebra R) = w := by
  simp [positiveProjection]

/-- Every element of `TauCeti.KacMoody.PresentedLieAlgebra R` is the sum of its negative, Cartan,
and positive projections. -/
theorem negativeProjection_add_cartanProjection_add_positiveProjection (z : PresentedLieAlgebra R) :
    (negativeProjection R z : PresentedLieAlgebra R) +
      (cartanProjection R z : PresentedLieAlgebra R) +
      (positiveProjection R z : PresentedLieAlgebra R) = z := by
  have h := (triangularEquiv R).apply_symm_apply z
  rw [triangularEquiv_apply] at h
  simpa only [negativeProjection, cartanProjection, positiveProjection, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_coe] using h

/-! ## One-sided Serre quotient identifications, generator independence, and `serreHom_injective` -/

section SerreQuotient

/-- For a generalized Cartan matrix `A`, `TauCeti.KacMoody.positiveQuotientHom R` is injective. -/
theorem positiveQuotientHom_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (positiveQuotientHom R) :=
  (injective_iff_map_eq_zero _).mpr fun _ hb =>
    (eq_zero_of_quotientTriangular_sum_eq_zero R hA (a := 0) (x := 0) (by simpa using hb)).2.2

/-- For a generalized Cartan matrix `A`, `TauCeti.KacMoody.negativeQuotientHom R` is injective. -/
theorem negativeQuotientHom_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (negativeQuotientHom R) :=
  (injective_iff_map_eq_zero _).mpr fun _ ha =>
    (eq_zero_of_quotientTriangular_sum_eq_zero R hA (x := 0) (b := 0) (by simpa using ha)).1

/-- The Lie algebra isomorphism between `FreeLieAlgebra K I ⧸ serreIdeal K A` and the raising
subalgebra `n⁺` of `PresentedLieAlgebra R`. -/
noncomputable def positiveEquiv (hA : A.IsGeneralizedCartan) :
    (FreeLieAlgebra K I ⧸ serreIdeal K A) ≃ₗ⁅K⁆ positiveSubalgebra R :=
  (LieEquiv.ofInjective (positiveQuotientHom R) (positiveQuotientHom_injective R hA)).trans
    (LieEquiv.ofEq _ _ (congrArg SetLike.coe (range_positiveQuotientHom R)))

@[simp] theorem coe_positiveEquiv_apply (hA : A.IsGeneralizedCartan)
    (b : FreeLieAlgebra K I ⧸ serreIdeal K A) :
    (positiveEquiv R hA b : PresentedLieAlgebra R) = positiveQuotientHom R b := by
  rw [positiveEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply, LieEquiv.ofInjective_apply]

/-- The Lie algebra isomorphism between `FreeLieAlgebra K I ⧸ serreIdeal K A` and the lowering
subalgebra `n⁻` of `PresentedLieAlgebra R`. -/
noncomputable def negativeEquiv (hA : A.IsGeneralizedCartan) :
    (FreeLieAlgebra K I ⧸ serreIdeal K A) ≃ₗ⁅K⁆ negativeSubalgebra R :=
  (LieEquiv.ofInjective (negativeQuotientHom R) (negativeQuotientHom_injective R hA)).trans
    (LieEquiv.ofEq _ _ (congrArg SetLike.coe (range_negativeQuotientHom R)))

@[simp] theorem coe_negativeEquiv_apply (hA : A.IsGeneralizedCartan)
    (a : FreeLieAlgebra K I ⧸ serreIdeal K A) :
    (negativeEquiv R hA a : PresentedLieAlgebra R) = negativeQuotientHom R a := by
  rw [negativeEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply, LieEquiv.ofInjective_apply]

/-- For a generalized Cartan matrix `A`, the raising generators `eᵢ` are linearly independent over
`K`. -/
theorem linearIndependent_positiveGenerator (hA : A.IsGeneralizedCartan) :
    LinearIndependent K (positiveGenerator R) := by
  have h := (linearIndependent_serreIdeal_mk_of K A).map' (positiveQuotientHom R).toLinearMap
    (LinearMap.ker_eq_bot.mpr (positiveQuotientHom_injective R hA))
  simpa [Function.comp_def] using h

/-- For a generalized Cartan matrix `A`, the lowering generators `fᵢ` are linearly independent over
`K`. -/
theorem linearIndependent_negativeGenerator (hA : A.IsGeneralizedCartan) :
    LinearIndependent K (negativeGenerator R) := by
  have h := (linearIndependent_serreIdeal_mk_of K A).map' (negativeQuotientHom R).toLinearMap
    (LinearMap.ker_eq_bot.mpr (negativeQuotientHom_injective R hA))
  simpa [Function.comp_def] using h

/-- For a generalized Cartan matrix `A`, the raising generator map `i ↦ eᵢ` is injective. -/
theorem positiveGenerator_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (positiveGenerator R) :=
  (linearIndependent_positiveGenerator R hA).injective

/-- For a generalized Cartan matrix `A`, the lowering generator map `i ↦ fᵢ` is injective. -/
theorem negativeGenerator_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (negativeGenerator R) :=
  (linearIndependent_negativeGenerator R hA).injective

section SerreInjective

variable [DecidableEq I]

private theorem serreHom_comp_toSerreE :
    (serreHom R).comp (toSerreE K A) = positiveQuotientHom R :=
  TauCeti.FreeLieAlgebra.quotient_hom_ext fun i => by
    rw [LieHom.comp_apply, LieIdeal.mkQ_apply, toSerreE_mk_of,
      positiveQuotientHom_mk_of, serreHom_serreE]

private theorem serreHom_comp_toSerreF :
    (serreHom R).comp (toSerreF K A) = negativeQuotientHom R :=
  TauCeti.FreeLieAlgebra.quotient_hom_ext fun i => by
    rw [LieHom.comp_apply, LieIdeal.mkQ_apply, toSerreF_mk_of,
      negativeQuotientHom_mk_of, serreHom_serreF]

private theorem exists_serreHom_eq_triangular (z : Matrix.ToLieAlgebra K A) :
    ∃ (a b : FreeLieAlgebra K I ⧸ serreIdeal K A) (c : I →₀ K),
      z = toSerreF K A a + c.sum (fun i r => r • serreH K A i) + toSerreE K A b ∧
      serreHom R z = negativeQuotientHom R a +
        cartanElement R (Finsupp.linearCombination K R.coroot c) + positiveQuotientHom R b := by
  have htop : z ∈ (LieSubalgebra.lieSpan K _ (Set.range (serreF K A))).toSubmodule ⊔
      Submodule.span K (Set.range (serreH K A)) ⊔
      (LieSubalgebra.lieSpan K _ (Set.range (serreE K A))).toSubmodule := by
    rw [lieSpan_serreF_sup_span_serreH_sup_lieSpan_serreE_eq_top K A]; trivial
  obtain ⟨uh, huh, v, hv, rfl⟩ := Submodule.mem_sup.mp htop
  obtain ⟨u, hu, h, hh, rfl⟩ := Submodule.mem_sup.mp huh
  have hrF : (toSerreF K A).range =
      LieSubalgebra.lieSpan K _ (Set.range (serreF K A)) :=
    range_toSerreF K A
  have hrE : (toSerreE K A).range =
      LieSubalgebra.lieSpan K _ (Set.range (serreE K A)) :=
    range_toSerreE K A
  rw [LieSubalgebra.mem_toSubmodule, ← hrF] at hu
  rw [LieSubalgebra.mem_toSubmodule, ← hrE] at hv
  rcases hu with ⟨a, rfl⟩
  rcases hv with ⟨b, rfl⟩
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hh
  refine ⟨a, b, c, rfl, ?_⟩
  have hserreH : serreHom R (c.sum fun i r => r • serreH K A i) =
      cartanElement R (Finsupp.linearCombination K R.coroot c) := by
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  have hF : serreHom R (toSerreF K A a) = negativeQuotientHom R a :=
    DFunLike.congr_fun (serreHom_comp_toSerreF R) a
  have hE : serreHom R (toSerreE K A b) = positiveQuotientHom R b :=
    DFunLike.congr_fun (serreHom_comp_toSerreE R) b
  simp only [LieHom.coe_toLinearMap]
  rw [map_add, map_add, hF, hserreH, hE]

/-- **Faithfulness of Serre's presentation on the derived subalgebra.** For a generalized Cartan
matrix `A`, `TauCeti.KacMoody.serreHom R : Matrix.ToLieAlgebra K A →ₗ⁅K⁆ PresentedLieAlgebra R`
is injective. -/
theorem serreHom_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (serreHom R) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨a, b, c, rfl, htri⟩ := exists_serreHom_eq_triangular R z
  rw [htri] at hz
  obtain ⟨rfl, hc, rfl⟩ := eq_zero_of_quotientTriangular_sum_eq_zero R hA hz
  have hc0 : c = 0 := R.coroot_linearIndependent.finsuppLinearCombination_injective
    (hc.trans (map_zero _).symm)
  simp [hc0]

end SerreInjective

end SerreQuotient

/-! ### Example: affine type `A₁⁽¹⁾` -/

example {H : Type*} [AddCommGroup H] [Module ℚ H]
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ))
      H) :
    Function.Injective (positiveQuotientHom R) ∧
      LinearIndependent ℚ (positiveGenerator R) ∧
      Function.Injective (serreHom R) :=
  have hA : (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan := by decide
  ⟨positiveQuotientHom_injective R hA, linearIndependent_positiveGenerator R hA,
    serreHom_injective R hA⟩

end KacMoody

end TauCeti
