/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Basic

import TauCeti.Algebra.Lie.Abelian
import TauCeti.Algebra.Lie.Hom
import TauCeti.Algebra.Lie.KacMoody.Auxiliary
import TauCeti.Algebra.Lie.Presentation.Serre.Triangular
import TauCeti.Algebra.Lie.Subalgebra.Automorphism
import TauCeti.LinearAlgebra.Matrix.Cartan.Generalized

/-!
# Triangular decomposition for Kac–Moody algebras

Let `R` be a realization of an integral matrix `A` over a field `K`. This file establishes the
structure of the presented Kac–Moody algebra `TauCeti.KacMoody.PresentedLieAlgebra R` around its
raising subalgebra `n⁺`, its Cartan space `H`, and its lowering subalgebra `n⁻`.

For an arbitrary integral matrix `A`:

* the Chevalley involution `ω` sends `h ↦ -h`, `eᵢ ↦ -fᵢ`, `fᵢ ↦ -eᵢ` and exchanges `n⁺` and `n⁻`;
* the algebra is the sum `n⁻ + H + n⁺` as a `K`-vector space;
* `ad eᵢ` and `ad fᵢ` act locally nilpotently on the whole algebra.

When `A` is a generalized Cartan matrix (`Matrix.IsGeneralizedCartan A`), combining the spanning
decomposition with `TauCeti.KacMoody.quotientTriangular_eq_zero` (proved via Kac's auxiliary
presentation and word representation in `TauCeti/Algebra/Lie/KacMoody/Auxiliary.lean`) yields:

* **Triangular decomposition**: `n⁻ × H × n⁺ ≃ₗ[K] PresentedLieAlgebra R`, with bundled
  coordinate projections onto the three summands and both `n⁺` and `n⁻` canonically isomorphic to
  `FreeLieAlgebra K I ⧸ serreIdeal K A`;
* **Generator independence**: the families `eᵢ` and `fᵢ` are linearly independent over `K`;
* **Derived subalgebra comparison**: `TauCeti.KacMoody.serreHom R` embeds `Matrix.ToLieAlgebra K A`
  isomorphically onto `⁅𝔤, 𝔤⁆`, with `⁅𝔤, 𝔤⁆ ∩ H` equal to the image of `R.corootSpan`.

All results hold over an arbitrary field `K`, with no characteristic or finiteness assumption.

## Main definitions

* `TauCeti.KacMoody.chevalleyInvolution`: the involutive Lie automorphism `h ↦ -h`, `eᵢ ↦ -fᵢ`,
  `fᵢ ↦ -eᵢ`.
* `TauCeti.KacMoody.positiveEquiv` and `TauCeti.KacMoody.negativeEquiv`: the Lie algebra
  isomorphisms `(FreeLieAlgebra K I ⧸ serreIdeal K A) ≃ₗ⁅K⁆ n⁺` and `≃ₗ⁅K⁆ n⁻`.
* `TauCeti.KacMoody.triangularEquiv`: the `K`-linear equivalence
  `negativeSubalgebra R × H × positiveSubalgebra R ≃ₗ[K] PresentedLieAlgebra R`.
* `TauCeti.KacMoody.negativeProjection`, `TauCeti.KacMoody.cartanProjection`, and
  `TauCeti.KacMoody.positiveProjection`: the bundled linear projections out of
  `PresentedLieAlgebra R`.
* `TauCeti.KacMoody.serreEquivRange`: the Lie algebra isomorphism from `Matrix.ToLieAlgebra K A`
  onto `(serreHom R).range = ⁅𝔤, 𝔤⁆`.

## Main results

* `TauCeti.KacMoody.lie_cartanElement_mem_positiveSubalgebra` and
  `TauCeti.KacMoody.lie_cartanElement_mem_negativeSubalgebra`: Cartan stability of `n⁺` and `n⁻`.
* `TauCeti.KacMoody.negativeProjection_add_cartanProjection_add_positiveProjection`:
  reconstruction of an element of `PresentedLieAlgebra R` from its three triangular projections.
* `TauCeti.KacMoody.cartanElement_injective`: injectivity of `TauCeti.KacMoody.cartanElement`
  for a generalized Cartan matrix.
* `TauCeti.KacMoody.cartanElement_coroot_ne_zero`, `TauCeti.KacMoody.positiveGenerator_ne_zero`,
  and `TauCeti.KacMoody.negativeGenerator_ne_zero`: the simple coroots `hᵢ` and the generators
  `eᵢ`, `fᵢ` are nonzero.
* `TauCeti.KacMoody.engel_positiveGenerator_eq_top` and
  `TauCeti.KacMoody.engel_negativeGenerator_eq_top`: local nilpotence of `ad eᵢ` and `ad fᵢ`.
* `TauCeti.KacMoody.linearIndependent_positiveGenerator` and
  `TauCeti.KacMoody.linearIndependent_negativeGenerator`: linear independence of `eᵢ` and of `fᵢ`.
* `TauCeti.KacMoody.serreHom_injective` and
  `TauCeti.KacMoody.range_serreHom_inf_range_cartanElement`: `Matrix.ToLieAlgebra K A` embeds as
  `⁅𝔤, 𝔤⁆`, and `⁅𝔤, 𝔤⁆ ∩ H` is the image of the coroot span.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§1.2–1.3, Theorem 1.2, §3.3, and §9.11.
-/

public section

open LieAlgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-! ## The Chevalley involution -/

section Chevalley

private noncomputable def chevalleyHom : PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R :=
  lift (satisfiesRelations_generators R).neg_swap

private theorem chevalleyHom_comp_self :
    (chevalleyHom R).comp (chevalleyHom R) = LieHom.id := by
  ext <;> simp [chevalleyHom]

/-- The *Chevalley involution* `ω` of `PresentedLieAlgebra R`, sending `h ↦ -h` for `h ∈ H`,
`eᵢ ↦ -fᵢ`, and `fᵢ ↦ -eᵢ`. -/
noncomputable def chevalleyInvolution : PresentedLieAlgebra R ≃ₗ⁅K⁆ PresentedLieAlgebra R :=
  LieEquiv.ofLieHoms (chevalleyHom R) (chevalleyHom R)
    (chevalleyHom_comp_self R) (chevalleyHom_comp_self R)

@[simp]
theorem chevalleyInvolution_cartanElement (x : H) :
    chevalleyInvolution R (cartanElement R x) = -cartanElement R x := by
  simp [chevalleyInvolution, chevalleyHom]

@[simp]
theorem chevalleyInvolution_positiveGenerator (i : I) :
    chevalleyInvolution R (positiveGenerator R i) = -negativeGenerator R i := by
  simp [chevalleyInvolution, chevalleyHom]

@[simp]
theorem chevalleyInvolution_negativeGenerator (i : I) :
    chevalleyInvolution R (negativeGenerator R i) = -positiveGenerator R i := by
  simp [chevalleyInvolution, chevalleyHom]

theorem chevalleyInvolution_involutive : Function.Involutive (chevalleyInvolution R) :=
  fun x => by
    simpa [chevalleyInvolution] using LieHom.congr_fun (chevalleyHom_comp_self R) x

@[simp]
theorem chevalleyInvolution_apply_apply (x : PresentedLieAlgebra R) :
    chevalleyInvolution R (chevalleyInvolution R x) = x :=
  chevalleyInvolution_involutive R x

@[simp]
theorem chevalleyInvolution_symm : (chevalleyInvolution R).symm = chevalleyInvolution R :=
  LieEquiv.symm_ofLieHoms _ _ _ _

end Chevalley

/-! ## Raising and lowering subalgebras, spanning, and local nilpotence -/

section Subalgebras

/-- Bracketing with a Cartan element preserves the raising subalgebra `n⁺`. -/
theorem lie_cartanElement_mem_positiveSubalgebra (x : H) {y : PresentedLieAlgebra R}
    (hy : y ∈ positiveSubalgebra R) : ⁅cartanElement R x, y⁆ ∈ positiveSubalgebra R := by
  rw [positiveSubalgebra_def] at hy ⊢
  refine LieSubalgebra.lie_mem_of_mem_lieSpan ?_ hy
  rintro _ ⟨i, rfl⟩
  rw [lie_cartanElement_positiveGenerator]
  exact LieSubalgebra.smul_mem _ _ (LieSubalgebra.subset_lieSpan (Set.mem_range_self i))

/-- Bracketing with a Cartan element preserves the lowering subalgebra `n⁻`. -/
theorem lie_cartanElement_mem_negativeSubalgebra (x : H) {y : PresentedLieAlgebra R}
    (hy : y ∈ negativeSubalgebra R) : ⁅cartanElement R x, y⁆ ∈ negativeSubalgebra R := by
  rw [negativeSubalgebra_def] at hy ⊢
  refine LieSubalgebra.lie_mem_of_mem_lieSpan ?_ hy
  rintro _ ⟨i, rfl⟩
  rw [lie_cartanElement_negativeGenerator]
  exact neg_mem (LieSubalgebra.smul_mem _ _
    (LieSubalgebra.subset_lieSpan (Set.mem_range_self i)))

/-- The Chevalley involution carries `n⁺` onto `n⁻`. -/
@[simp]
theorem map_positiveSubalgebra_chevalleyInvolution :
    (positiveSubalgebra R).map (chevalleyInvolution R :
      PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) = negativeSubalgebra R := by
  have hcomp : ((chevalleyInvolution R :
      PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) ∘ positiveGenerator R) =
      -negativeGenerator R :=
    funext (chevalleyInvolution_positiveGenerator R)
  rw [positiveSubalgebra_def, LieSubalgebra.map_lieSpan, ← Set.range_comp, hcomp, ← Set.neg_range',
    LieSubalgebra.lieSpan_neg, negativeSubalgebra_def]

/-- The Chevalley involution carries `n⁻` onto `n⁺`. -/
@[simp]
theorem map_negativeSubalgebra_chevalleyInvolution :
    (negativeSubalgebra R).map (chevalleyInvolution R :
      PresentedLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R) = positiveSubalgebra R := by
  simpa using (LieSubalgebra.map_symm_eq_iff (chevalleyInvolution R)).2
    (map_positiveSubalgebra_chevalleyInvolution R)

/-- **Spanning triangular decomposition.** For any integral matrix `A`, the presented Lie algebra is
the sum `n⁻ + H + n⁺` of its lowering subalgebra, the image of `H`, and its raising subalgebra. -/
theorem negativeSubalgebra_sup_range_cartanElement_sup_positiveSubalgebra :
    (negativeSubalgebra R).toSubmodule ⊔ LinearMap.range (cartanElement R) ⊔
      (positiveSubalgebra R).toSubmodule = ⊤ := by
  classical
  have hserre := congrArg (Submodule.map (serreHom R).toLinearMap)
    (lieSpan_serreF_sup_span_serreH_sup_lieSpan_serreE_eq_top K A)
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_top] at hserre
  have hF_comp : ⇑(serreHom R) ∘ serreF K A = negativeGenerator R := funext (serreHom_serreF R)
  have hE_comp : ⇑(serreHom R) ∘ serreE K A = positiveGenerator R := funext (serreHom_serreE R)
  have hF : ((LieSubalgebra.lieSpan K _ (Set.range (serreF K A))).toSubmodule).map
      (serreHom R).toLinearMap = (negativeSubalgebra R).toSubmodule := by
    rw [← LieSubalgebra.map_toSubmodule, LieSubalgebra.map_lieSpan, ← Set.range_comp,
      hF_comp, negativeSubalgebra_def]
  have hE : ((LieSubalgebra.lieSpan K _ (Set.range (serreE K A))).toSubmodule).map
      (serreHom R).toLinearMap = (positiveSubalgebra R).toSubmodule := by
    rw [← LieSubalgebra.map_toSubmodule, LieSubalgebra.map_lieSpan, ← Set.range_comp,
      hE_comp, positiveSubalgebra_def]
  have hH : (Submodule.span K (Set.range (serreH K A))).map (serreHom R).toLinearMap ≤
      LinearMap.range (cartanElement R) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨R.coroot i, (serreHom_serreH R i).symm⟩
  rw [eq_top_iff, ← range_serreHom_sup_range_cartanElement R, sup_le_iff]
  refine ⟨?_, le_sup_of_le_left le_sup_right⟩
  rw [LieHom.range_toSubmodule, ← hserre, hF, hE]
  exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (hH.trans (le_sup_of_le_left le_sup_right)))
    le_sup_right

/-- **The raising generators act locally nilpotently** on `PresentedLieAlgebra R`. -/
theorem engel_positiveGenerator_eq_top (i : I) :
    LieSubalgebra.engel K (positiveGenerator R i) = ⊤ := by
  classical
  have hs := (satisfiesRelations_generators R).isSerreSystem
  rw [eq_top_iff, ← lieSpan_generators_eq_top R, LieSubalgebra.lieSpan_le]
  rintro _ ((⟨x, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact LieSubalgebra.mem_engel_of_lie_eq_smul (lie_cartanElement_positiveGenerator R x i)
  · exact hs.E_mem_engel_E i j
  · exact hs.F_mem_engel_E i j

/-- **The lowering generators act locally nilpotently** on `PresentedLieAlgebra R`. -/
theorem engel_negativeGenerator_eq_top (i : I) :
    LieSubalgebra.engel K (negativeGenerator R i) = ⊤ := by
  have h := (chevalleyInvolution R).map_engel (positiveGenerator R i)
  rw [engel_positiveGenerator_eq_top, ← LieHom.range_eq_map,
    (LieHom.range_eq_top _).mpr (chevalleyInvolution R).surjective,
    chevalleyInvolution_positiveGenerator, LieSubalgebra.engel_neg] at h
  exact h.symm

end Subalgebras

/-! ## Triangular equivalence, projections, and generator independence -/

section Triangular

/-- For a generalized Cartan matrix `A`, `positiveQuotientHom R` is injective. -/
theorem positiveQuotientHom_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (positiveQuotientHom R) :=
  (injective_iff_map_eq_zero _).mpr fun _ hb =>
    (quotientTriangular_eq_zero R hA (a := 0) (x := 0) (by simpa using hb)).2.2

/-- For a generalized Cartan matrix `A`, `negativeQuotientHom R` is injective. -/
theorem negativeQuotientHom_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (negativeQuotientHom R) :=
  (injective_iff_map_eq_zero _).mpr fun _ ha =>
    (quotientTriangular_eq_zero R hA (x := 0) (b := 0) (by simpa using ha)).1

/-- The Lie algebra isomorphism between `FreeLieAlgebra K I ⧸ serreIdeal K A` and the raising
subalgebra `n⁺` of `PresentedLieAlgebra R`. -/
noncomputable def positiveEquiv (hA : A.IsGeneralizedCartan) :
    (FreeLieAlgebra K I ⧸ serreIdeal K A) ≃ₗ⁅K⁆ positiveSubalgebra R :=
  (LieEquiv.ofInjective (positiveQuotientHom R) (positiveQuotientHom_injective R hA)).trans
    (LieEquiv.ofEq _ _ (congrArg SetLike.coe (range_positiveQuotientHom R)))

@[simp]
theorem coe_positiveEquiv_apply (hA : A.IsGeneralizedCartan)
    (b : FreeLieAlgebra K I ⧸ serreIdeal K A) :
    (positiveEquiv R hA b : PresentedLieAlgebra R) = positiveQuotientHom R b := by
  rw [positiveEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply, LieEquiv.ofInjective_apply]

/-- The Lie algebra isomorphism between `FreeLieAlgebra K I ⧸ serreIdeal K A` and the lowering
subalgebra `n⁻` of `PresentedLieAlgebra R`. -/
noncomputable def negativeEquiv (hA : A.IsGeneralizedCartan) :
    (FreeLieAlgebra K I ⧸ serreIdeal K A) ≃ₗ⁅K⁆ negativeSubalgebra R :=
  (LieEquiv.ofInjective (negativeQuotientHom R) (negativeQuotientHom_injective R hA)).trans
    (LieEquiv.ofEq _ _ (congrArg SetLike.coe (range_negativeQuotientHom R)))

@[simp]
theorem coe_negativeEquiv_apply (hA : A.IsGeneralizedCartan)
    (a : FreeLieAlgebra K I ⧸ serreIdeal K A) :
    (negativeEquiv R hA a : PresentedLieAlgebra R) = negativeQuotientHom R a := by
  rw [negativeEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply, LieEquiv.ofInjective_apply]

/-- The canonical addition map `n⁻ × H × n⁺ →ₗ[K] PresentedLieAlgebra R`. -/
noncomputable def triangularLinearMap :
    (negativeSubalgebra R × H × positiveSubalgebra R) →ₗ[K] PresentedLieAlgebra R :=
  ((negativeSubalgebra R).toSubmodule.subtype).coprod
    ((cartanElement R).coprod (positiveSubalgebra R).toSubmodule.subtype)

@[simp]
theorem triangularLinearMap_apply (p : negativeSubalgebra R × H × positiveSubalgebra R) :
    triangularLinearMap R p =
      (p.1 : PresentedLieAlgebra R) + cartanElement R p.2.1 + (p.2.2 : PresentedLieAlgebra R) := by
  simp only [triangularLinearMap, LinearMap.coprod_apply, add_assoc]
  rfl

theorem triangularLinearMap_surjective : Function.Surjective (triangularLinearMap R) := by
  rw [← LinearMap.range_eq_top, triangularLinearMap, LinearMap.range_coprod, LinearMap.range_coprod,
    Submodule.range_subtype, Submodule.range_subtype, ← sup_assoc]
  exact negativeSubalgebra_sup_range_cartanElement_sup_positiveSubalgebra R

/-- **Triangular decomposition.** For a generalized Cartan matrix `A`, addition gives a `K`-linear
isomorphism `n⁻ × H × n⁺ ≃ₗ[K] PresentedLieAlgebra R`. -/
noncomputable def triangularEquiv (hA : A.IsGeneralizedCartan) :
    (negativeSubalgebra R × H × positiveSubalgebra R) ≃ₗ[K] PresentedLieAlgebra R :=
  LinearEquiv.ofBijective (triangularLinearMap R) ⟨by
    refine (injective_iff_map_eq_zero _).mpr ?_
    rintro ⟨u, x, w⟩ hzero
    obtain ⟨a, rfl⟩ := (negativeEquiv R hA).surjective u
    obtain ⟨b, rfl⟩ := (positiveEquiv R hA).surjective w
    simp only [triangularLinearMap_apply, LieEquiv.coe_toLieHom, coe_negativeEquiv_apply,
      coe_positiveEquiv_apply] at hzero
    obtain ⟨rfl, rfl, rfl⟩ := quotientTriangular_eq_zero R hA hzero
    simp, triangularLinearMap_surjective R⟩

@[simp]
theorem triangularEquiv_apply (hA : A.IsGeneralizedCartan)
    (p : negativeSubalgebra R × H × positiveSubalgebra R) :
    triangularEquiv R hA p =
      (p.1 : PresentedLieAlgebra R) + cartanElement R p.2.1 + (p.2.2 : PresentedLieAlgebra R) :=
  triangularLinearMap_apply R p

@[simp]
theorem triangularEquiv_symm_coe_negativeSubalgebra (hA : A.IsGeneralizedCartan)
    (u : negativeSubalgebra R) :
    (triangularEquiv R hA).symm (u : PresentedLieAlgebra R) = (u, 0, 0) :=
  (triangularEquiv R hA).injective (by simp)

@[simp]
theorem triangularEquiv_symm_cartanElement (hA : A.IsGeneralizedCartan) (x : H) :
    (triangularEquiv R hA).symm (cartanElement R x) = (0, x, 0) :=
  (triangularEquiv R hA).injective (by simp)

@[simp]
theorem triangularEquiv_symm_coe_positiveSubalgebra (hA : A.IsGeneralizedCartan)
    (w : positiveSubalgebra R) :
    (triangularEquiv R hA).symm (w : PresentedLieAlgebra R) = (0, 0, w) :=
  (triangularEquiv R hA).injective (by simp)

/-- The projection of `PresentedLieAlgebra R` onto the lowering subalgebra `n⁻` along the
triangular decomposition. -/
noncomputable def negativeProjection (hA : A.IsGeneralizedCartan) :
    PresentedLieAlgebra R →ₗ[K] negativeSubalgebra R :=
  (LinearMap.fst K (negativeSubalgebra R) (H × positiveSubalgebra R)).comp
    (triangularEquiv R hA).symm.toLinearMap

/-- The projection of `PresentedLieAlgebra R` onto the Cartan space `H` along the triangular
decomposition. -/
noncomputable def cartanProjection (hA : A.IsGeneralizedCartan) :
    PresentedLieAlgebra R →ₗ[K] H :=
  (LinearMap.fst K H (positiveSubalgebra R)).comp
    ((LinearMap.snd K (negativeSubalgebra R) (H × positiveSubalgebra R)).comp
      (triangularEquiv R hA).symm.toLinearMap)

/-- The projection of `PresentedLieAlgebra R` onto the raising subalgebra `n⁺` along the
triangular decomposition. -/
noncomputable def positiveProjection (hA : A.IsGeneralizedCartan) :
    PresentedLieAlgebra R →ₗ[K] positiveSubalgebra R :=
  (LinearMap.snd K H (positiveSubalgebra R)).comp
    ((LinearMap.snd K (negativeSubalgebra R) (H × positiveSubalgebra R)).comp
      (triangularEquiv R hA).symm.toLinearMap)

@[simp]
theorem negativeProjection_coe_negativeSubalgebra (hA : A.IsGeneralizedCartan)
    (u : negativeSubalgebra R) :
    negativeProjection R hA (u : PresentedLieAlgebra R) = u := by
  simp [negativeProjection]

@[simp]
theorem negativeProjection_cartanElement (hA : A.IsGeneralizedCartan) (x : H) :
    negativeProjection R hA (cartanElement R x) = 0 := by
  simp [negativeProjection]

@[simp]
theorem negativeProjection_coe_positiveSubalgebra (hA : A.IsGeneralizedCartan)
    (w : positiveSubalgebra R) :
    negativeProjection R hA (w : PresentedLieAlgebra R) = 0 := by
  simp [negativeProjection]

@[simp]
theorem cartanProjection_coe_negativeSubalgebra (hA : A.IsGeneralizedCartan)
    (u : negativeSubalgebra R) :
    cartanProjection R hA (u : PresentedLieAlgebra R) = 0 := by
  simp [cartanProjection]

@[simp]
theorem cartanProjection_cartanElement (hA : A.IsGeneralizedCartan) (x : H) :
    cartanProjection R hA (cartanElement R x) = x := by
  simp [cartanProjection]

@[simp]
theorem cartanProjection_coe_positiveSubalgebra (hA : A.IsGeneralizedCartan)
    (w : positiveSubalgebra R) :
    cartanProjection R hA (w : PresentedLieAlgebra R) = 0 := by
  simp [cartanProjection]

@[simp]
theorem positiveProjection_coe_negativeSubalgebra (hA : A.IsGeneralizedCartan)
    (u : negativeSubalgebra R) :
    positiveProjection R hA (u : PresentedLieAlgebra R) = 0 := by
  simp [positiveProjection]

@[simp]
theorem positiveProjection_cartanElement (hA : A.IsGeneralizedCartan) (x : H) :
    positiveProjection R hA (cartanElement R x) = 0 := by
  simp [positiveProjection]

@[simp]
theorem positiveProjection_coe_positiveSubalgebra (hA : A.IsGeneralizedCartan)
    (w : positiveSubalgebra R) :
    positiveProjection R hA (w : PresentedLieAlgebra R) = w := by
  simp [positiveProjection]

/-- Every element of `PresentedLieAlgebra R` is the sum of its negative, Cartan, and positive
projections. -/
theorem negativeProjection_add_cartanProjection_add_positiveProjection (hA : A.IsGeneralizedCartan)
    (z : PresentedLieAlgebra R) :
    (negativeProjection R hA z : PresentedLieAlgebra R) +
      cartanElement R (cartanProjection R hA z) +
      (positiveProjection R hA z : PresentedLieAlgebra R) = z := by
  have h := (triangularEquiv R hA).apply_symm_apply z
  rw [triangularEquiv_apply] at h
  simpa only [negativeProjection, cartanProjection, positiveProjection, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_coe] using h

/-- **Cartan injectivity.** For a generalized Cartan matrix `A`, the canonical map
`TauCeti.KacMoody.cartanElement` from the realization `H` into the presented Lie algebra is
injective. -/
theorem cartanElement_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (cartanElement R) :=
  Function.HasLeftInverse.injective ⟨cartanProjection R hA, cartanProjection_cartanElement R hA⟩

/-- For a generalized Cartan matrix `A`, the simple coroot `hᵢ` is nonzero in the presented
Kac–Moody algebra. -/
theorem cartanElement_coroot_ne_zero (hA : A.IsGeneralizedCartan) (i : I) :
    cartanElement R (R.coroot i) ≠ 0 :=
  (map_ne_zero_iff _ (cartanElement_injective R hA)).2 (R.coroot_linearIndependent.ne_zero i)

theorem disjoint_negativeSubalgebra_range_cartanElement_sup_positiveSubalgebra
    (hA : A.IsGeneralizedCartan) :
    Disjoint (negativeSubalgebra R).toSubmodule
      (LinearMap.range (cartanElement R) ⊔ (positiveSubalgebra R).toSubmodule) := by
  rw [Submodule.disjoint_def]
  intro z hz₁ hz₂
  obtain ⟨_, ⟨x, rfl⟩, w, hw, hsum⟩ := Submodule.mem_sup.mp hz₂
  have heq : triangularEquiv R hA (⟨z, hz₁⟩, 0, 0) = triangularEquiv R hA (0, x, ⟨w, hw⟩) := by
    simpa using hsum.symm
  have hinj := (triangularEquiv R hA).injective heq
  simpa using congrArg (fun p => (p.1 : PresentedLieAlgebra R)) hinj

theorem disjoint_range_cartanElement_positiveSubalgebra (hA : A.IsGeneralizedCartan) :
    Disjoint (LinearMap.range (cartanElement R)) (positiveSubalgebra R).toSubmodule := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, rfl⟩ hw
  have heq :
      triangularEquiv R hA (0, x, 0) = triangularEquiv R hA (0, 0, ⟨cartanElement R x, hw⟩) := by
    simp
  have hinj := (triangularEquiv R hA).injective heq
  have hx : x = 0 := congrArg (fun p => p.2.1) hinj
  simp [hx]

/-! ### Linear independence of the raising and lowering generators -/

section GeneratorIndependence

/-- For a generalized Cartan matrix `A`, the raising generators `eᵢ` are linearly independent over
`K`. -/
theorem linearIndependent_positiveGenerator (hA : A.IsGeneralizedCartan) :
    LinearIndependent K (positiveGenerator R) := by
  classical
  let eBasis : I → TauCeti.AbelianLieAlgebra (I →₀ K) :=
    fun i => (TauCeti.AbelianLieAlgebra.equiv K (I →₀ K)).symm (Finsupp.single i 1)
  let abHom : FreeLieAlgebra K I ⧸ serreIdeal K A →ₗ⁅K⁆ TauCeti.AbelianLieAlgebra (I →₀ K) :=
    serreIdealLift (E := eBasis) fun i j => by simp
  let proj : positiveSubalgebra R →ₗ[K] (I →₀ K) :=
    (TauCeti.AbelianLieAlgebra.equiv K (I →₀ K)).toLinearMap.comp
      (abHom.toLinearMap.comp (positiveEquiv R hA).symm.toLinearMap)
  have hproj : ∀ i : I,
      proj ⟨positiveGenerator R i, positiveGenerator_mem_positiveSubalgebra R i⟩ =
        Finsupp.single i 1 := fun i => by
    have hsymm : (positiveEquiv R hA).symm
        ⟨positiveGenerator R i, positiveGenerator_mem_positiveSubalgebra R i⟩ =
        (serreIdeal K A).mkQ (FreeLieAlgebra.of K i) :=
      (positiveEquiv R hA).injective <| Subtype.ext <| by
        rw [LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply]
        simp
    simp only [proj, LinearMap.comp_apply, LieHom.coe_toLinearMap, LieEquiv.coe_toLieHom, hsymm,
      abHom, LieIdeal.mkQ_apply, serreIdealLift_mk_of, eBasis, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  have hcomp : proj ∘ (fun i =>
      (⟨positiveGenerator R i, positiveGenerator_mem_positiveSubalgebra R i⟩ :
        positiveSubalgebra R)) = fun i => Finsupp.single i (1 : K) :=
    funext hproj
  have hind_sub : LinearIndependent K (fun i =>
      (⟨positiveGenerator R i, positiveGenerator_mem_positiveSubalgebra R i⟩ :
        positiveSubalgebra R)) :=
    LinearIndependent.of_comp proj
      (hcomp ▸ (Finsupp.basisSingleOne (ι := I) (R := K)).linearIndependent)
  exact hind_sub.map' (positiveSubalgebra R).toSubmodule.subtype
    (Submodule.ker_subtype (positiveSubalgebra R).toSubmodule)

/-- For a generalized Cartan matrix `A`, the lowering generators `fᵢ` are linearly independent over
`K`. -/
theorem linearIndependent_negativeGenerator (hA : A.IsGeneralizedCartan) :
    LinearIndependent K (negativeGenerator R) := by
  have h := (linearIndependent_positiveGenerator R hA).map'
    (chevalleyInvolution R).toLinearEquiv.toLinearMap (LinearEquiv.ker _)
  have hcomp : (chevalleyInvolution R).toLinearEquiv.toLinearMap ∘ positiveGenerator R =
      -negativeGenerator R := funext (chevalleyInvolution_positiveGenerator R)
  rw [hcomp] at h
  exact linearIndependent_neg_iff.mp h

/-- For a generalized Cartan matrix `A`, the raising generator `eᵢ` is nonzero in the presented
Kac–Moody algebra. -/
theorem positiveGenerator_ne_zero (hA : A.IsGeneralizedCartan) (i : I) :
    positiveGenerator R i ≠ 0 :=
  (linearIndependent_positiveGenerator R hA).ne_zero i

/-- For a generalized Cartan matrix `A`, the lowering generator `fᵢ` is nonzero in the presented
Kac–Moody algebra. -/
theorem negativeGenerator_ne_zero (hA : A.IsGeneralizedCartan) (i : I) :
    negativeGenerator R i ≠ 0 :=
  (linearIndependent_negativeGenerator R hA).ne_zero i

theorem positiveGenerator_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (positiveGenerator R) :=
  (linearIndependent_positiveGenerator R hA).injective

theorem negativeGenerator_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (negativeGenerator R) :=
  (linearIndependent_negativeGenerator R hA).injective

end GeneratorIndependence

end Triangular

/-! ## Comparison with Serre's presentation of the derived subalgebra -/

section SerreComparison

variable [DecidableEq I]

private noncomputable def toSerreE :
    FreeLieAlgebra K I ⧸ serreIdeal K A →ₗ⁅K⁆ Matrix.ToLieAlgebra K A :=
  serreIdealLift (ad_pow_lie_serreE_serreE K A)

private noncomputable def toSerreF :
    FreeLieAlgebra K I ⧸ serreIdeal K A →ₗ⁅K⁆ Matrix.ToLieAlgebra K A :=
  serreIdealLift (ad_pow_lie_serreF_serreF K A)

private theorem serreHom_comp_toSerreE :
    (serreHom R).comp (toSerreE (K := K) (A := A)) = positiveQuotientHom R :=
  TauCeti.FreeLieAlgebra.quotient_hom_ext fun i => by
    rw [LieHom.comp_apply, LieIdeal.mkQ_apply, toSerreE, serreIdealLift_mk_of,
      positiveQuotientHom_mk_of, serreHom_serreE]

private theorem serreHom_comp_toSerreF :
    (serreHom R).comp (toSerreF (K := K) (A := A)) = negativeQuotientHom R :=
  TauCeti.FreeLieAlgebra.quotient_hom_ext fun i => by
    rw [LieHom.comp_apply, LieIdeal.mkQ_apply, toSerreF, serreIdealLift_mk_of,
      negativeQuotientHom_mk_of, serreHom_serreF]

private theorem exists_serreHom_eq_triangular (z : Matrix.ToLieAlgebra K A) :
    ∃ (a b : FreeLieAlgebra K I ⧸ serreIdeal K A) (c : I →₀ K),
      z = toSerreF a + c.sum (fun i r => r • serreH K A i) + toSerreE b ∧
      serreHom R z = negativeQuotientHom R a +
        cartanElement R (Finsupp.linearCombination K R.coroot c) + positiveQuotientHom R b := by
  have htop : z ∈ (LieSubalgebra.lieSpan K _ (Set.range (serreF K A))).toSubmodule ⊔
      Submodule.span K (Set.range (serreH K A)) ⊔
      (LieSubalgebra.lieSpan K _ (Set.range (serreE K A))).toSubmodule := by
    rw [lieSpan_serreF_sup_span_serreH_sup_lieSpan_serreE_eq_top K A]; trivial
  obtain ⟨uh, huh, v, hv, rfl⟩ := Submodule.mem_sup.mp htop
  obtain ⟨u, hu, h, hh, rfl⟩ := Submodule.mem_sup.mp huh
  have hrF : (toSerreF (K := K) (A := A)).range =
      LieSubalgebra.lieSpan K _ (Set.range (serreF K A)) :=
    range_serreIdealLift _
  have hrE : (toSerreE (K := K) (A := A)).range =
      LieSubalgebra.lieSpan K _ (Set.range (serreE K A)) :=
    range_serreIdealLift _
  rw [LieSubalgebra.mem_toSubmodule, ← hrF] at hu
  rw [LieSubalgebra.mem_toSubmodule, ← hrE] at hv
  rcases hu with ⟨a, rfl⟩
  rcases hv with ⟨b, rfl⟩
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hh
  refine ⟨a, b, c, rfl, ?_⟩
  have hserreH : serreHom R (c.sum fun i r => r • serreH K A i) =
      cartanElement R (Finsupp.linearCombination K R.coroot c) := by
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  have hF : serreHom R (toSerreF a) = negativeQuotientHom R a :=
    DFunLike.congr_fun (serreHom_comp_toSerreF R) a
  have hE : serreHom R (toSerreE b) = positiveQuotientHom R b :=
    DFunLike.congr_fun (serreHom_comp_toSerreE R) b
  simp only [LieHom.coe_toLinearMap]
  rw [map_add, map_add, hF, hserreH, hE]

/-- **Faithfulness of Serre's presentation on the derived subalgebra.** For a generalized Cartan
matrix `A`, `serreHom R : Matrix.ToLieAlgebra K A →ₗ⁅K⁆ PresentedLieAlgebra R` is injective. -/
theorem serreHom_injective (hA : A.IsGeneralizedCartan) :
    Function.Injective (serreHom R) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨a, b, c, rfl, htri⟩ := exists_serreHom_eq_triangular R z
  rw [htri] at hz
  obtain ⟨rfl, hc, rfl⟩ := quotientTriangular_eq_zero R hA hz
  have hc0 : c = 0 := R.coroot_linearIndependent.finsuppLinearCombination_injective
    (hc.trans (map_zero _).symm)
  simp [hc0]

/-- The Lie algebra isomorphism between `Matrix.ToLieAlgebra K A` and `(serreHom R).range`, the
derived subalgebra `⁅𝔤, 𝔤⁆` of `PresentedLieAlgebra R`. -/
noncomputable def serreEquivRange (hA : A.IsGeneralizedCartan) :
    Matrix.ToLieAlgebra K A ≃ₗ⁅K⁆ (serreHom R).range :=
  LieEquiv.ofInjective (serreHom R) (serreHom_injective R hA)

/-- Coercing the image of `z` under `TauCeti.KacMoody.serreEquivRange` back to
`PresentedLieAlgebra R` recovers `serreHom R z`. -/
@[simp]
theorem coe_serreEquivRange_apply (hA : A.IsGeneralizedCartan) (z : Matrix.ToLieAlgebra K A) :
    (serreEquivRange R hA z : PresentedLieAlgebra R) = serreHom R z := by
  rw [serreEquivRange, LieEquiv.ofInjective_apply]

/-- **Intersection of the derived subalgebra with the Cartan subalgebra.** For a generalized Cartan
matrix `A`, `⁅𝔤, 𝔤⁆ ∩ H` is the image of `R.corootSpan` under `cartanElement R`. -/
theorem range_serreHom_inf_range_cartanElement (hA : A.IsGeneralizedCartan) :
    (serreHom R).range.toSubmodule ⊓ LinearMap.range (cartanElement R) =
      R.corootSpan.map (cartanElement R) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨z, rfl⟩, ⟨x, hzx⟩⟩
    simp only [LieHom.coe_toLinearMap] at hzx ⊢
    obtain ⟨a, b, c, -, htri⟩ := exists_serreHom_eq_triangular R z
    have hzero : negativeQuotientHom R a +
        cartanElement R (Finsupp.linearCombination K R.coroot c - x) +
        positiveQuotientHom R b = 0 := by
      rw [map_sub, hzx, htri]
      abel
    obtain ⟨-, hcx, -⟩ := quotientTriangular_eq_zero R hA hzero
    rw [← hzx, ← sub_eq_zero.mp hcx]
    refine ⟨Finsupp.linearCombination K R.coroot c, ?_, rfl⟩
    rw [R.corootSpan_def, Finsupp.linearCombination_apply]
    exact Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨c, rfl⟩
  · refine le_inf ?_ fun _ ⟨x, _, hx⟩ => ⟨x, hx⟩
    rw [R.corootSpan_def, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨serreH K A i, serreHom_serreH R i⟩

end SerreComparison

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
