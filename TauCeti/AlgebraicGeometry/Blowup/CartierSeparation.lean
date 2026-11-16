/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Colon
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.CommRing
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.RingTheory.Ideal.AffineBlowup
import TauCeti.RingTheory.Ideal.Colon

/-!
# Cartier separation

Let `X` be an arbitrary scheme and `D₁`, `D₂` be two effective Cartier divisors on `X`, represented
as `Scheme.IdealSheafData` satisfying `IsEffectiveCartier`. Blowing up the sum ideal sheaf
`I = D₁ ⊔ D₂` yields a proper morphism `p : Bl_{D₁ ⊔ D₂} X ⟶ X`, which is an isomorphism away from
`V(D₁) ∩ V(D₂)`, together with its invertible exceptional divisor `F = (D₁ ⊔ D₂).comap p`.

More generally, **every** blowup `Bl_I X ⟶ X` pulls back every effective Cartier divisor `D` on `X`
to an effective Cartier divisor `D.comap I.blowupToBase` (`IsEffectiveCartier.comap_blowupToBase`),
without any flatness, integrality, reducedness, or Noetherian hypothesis: on each affine blowup
chart `Spec R[I/a]`, the algebra `R[I/a]` embeds into the localization `R_a`, so every regular
element of `R` remains regular in `R[I/a]`.

Because `F` is always an effective Cartier divisor on `Bl_{D₁ ⊔ D₂} X`, the residual ideal sheaves
`D'₁ = (D₁.comap p : F)` (`blowupSupResidualLeft`) and `D'₂ = (D₂.comap p : F)`
(`blowupSupResidualRight`) are defined for arbitrary ideal sheaves `D₁` and `D₂` and satisfy:

* `F * D'₁ = D₁.comap p` and `F * D'₂ = D₂.comap p` (`p* Dᵢ = F + D'ᵢ`),
* `D'₁ ⊔ D'₂ = ⊤`, equivalently `Disjoint D'₁.support D'₂.support`,
* `D₁.comap p * D'₂ = D₂.comap p * D'₁` (`p* D₁ + D'₂ = p* D₂ + D'₁`).

When `D₁` and `D₂` are effective Cartier divisors, so are `D'₁` and `D'₂`, and their line-bundle
classes satisfy `[D'₁] * [D'₂]⁻¹ = p* ([D₁] * [D₂]⁻¹)` in the Picard group. Locally on an affine
open `U` where `D₁(U) = (x₁)` and `D₂(U) = (x₂)`, the residual ideals on the chart
`Spec Γ(X, U)[(x₁, x₂)/x₁]` are `(1)` and `(x₂ / x₁)` (and symmetrically on the `x₂`-chart); the
degree-one Rees sections `x'₁, x'₂` of `𝒪(1)` on `Proj R[(x₁, x₂)t]` satisfy `x₂ • x'₁ = x₁ • x'₂`,
have no common zero, and generate `𝒪(1)`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.blowupSupResidualLeft`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowupSupResidualRight`: the residual ideal sheaves
  `D'₁ = (p* D₁ : F)` and `D'₂ = (p* D₂ : F)` on `Bl_{D₁ ⊔ D₂} X`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.comap_blowupToBase`: pulling back an
  effective Cartier divisor along any blowup yields an effective Cartier divisor.
* `TauCeti.AlgebraicGeometry.smul_toTwistingSheaf_monomialDegreeOne_eq`: `b • (a t) = a • (b t)`
  in `Γ(Proj R[It], 𝒪(1))`.
* `TauCeti.AlgebraicGeometry.sup_nonvanishingLocus_toTwistingSheaf_monomialDegreeOne_span_pair`:
  the degree-one Rees sections `x'₁, x'₂` of `𝒪(1)` on `Proj R[(x₁, x₂)t]` have no common zero.
* `TauCeti.AlgebraicGeometry.epi_freeHomEquiv_symm_toTwistingSheaf_reesAlgebra` and
  `TauCeti.AlgebraicGeometry.epi_freeHomEquiv_symm_toTwistingSheaf_span_pair`: the degree-one Rees
  sections generate `𝒪(1)` (giving an epimorphism from the free sheaf onto `𝒪(1)`).
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_blowupToBase_sup_mul_blowupSupResidualLeft`,
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_blowupToBase_sup_mul_blowupSupResidualRight`:
  `F * D'ᵢ = p* Dᵢ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.blowupSupResidualLeft_sup_right`,
  `AlgebraicGeometry.Scheme.IdealSheafData.disjoint_support_blowupSupResidual`: `D'₁ ⊔ D'₂ = ⊤`
  and `D'₁`, `D'₂` have disjoint supports.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul_blowupSupResidualRight_eq`:
  `p* D₁ * D'₂ = p* D₂ * D'₁`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.blowupSupResidualLeft`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.blowupSupResidualRight`:
  the residual ideal sheaves of effective Cartier divisors are effective Cartier.
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_blowupSupResidual_mul_inv`:
  `[D'₁] * [D'₂]⁻¹ = p* ([D₁] * [D₂]⁻¹)`.

## References

* G. Boxer and V. Pilloni, *Higher Hida theory for Siegel modular forms*, §4.1.10,
  Proposition-construction 4.1.11, p. 42.
* [The Stacks Project, Section 31.32 / Tag 01OF](https://stacks.math.columbia.edu/tag/01OF):
  blowing up along a quasi-coherent sheaf of ideals.
-/

public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace reesAlgebra

universe u

/-! ### Pullback of effective Cartier divisors along arbitrary blowups -/

namespace Ideal

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry

/-- On the affine blowup `Proj R[It] ⟶ Spec R` along an arbitrary ideal `I`, the inverse image of
any principal effective Cartier divisor `V(d)` (with `d` regular in `R`) is again an effective
Cartier divisor, with equation `d` on every affine blowup chart `Spec R[I/a]`. -/
theorem isEffectiveCartier_comap_toSpecCoeff_span_singleton {R : Type u} [CommRing R]
    (I : Ideal R) {d : R} (hd : IsSMulRegular R d) :
    ((ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv d})).comap
      (Proj.toSpecCoeff (grade I))).IsEffectiveCartier := by
  have hs : Ideal.span (Set.range ((↑) : I → R)) = I := by
    rw [Subtype.range_coe, Ideal.span_eq]
  rw [isEffectiveCartier_iff_exists_isOpenImmersion]
  intro x
  obtain ⟨⟨a, ha⟩, hx⟩ := Opens.mem_iSup.mp
    ((iSup_opensRange_affineBlowupι hs).ge (Set.mem_univ x))
  let B := I.affineBlowup a (Localization.Away a)
  refine ⟨_, inferInstance, affineBlowupι (Localization.Away a) ha, inferInstance, hx,
    (Scheme.ΓSpecIso (.of B)).inv (algebraMap R B d),
    Scheme.isSMulRegular_ΓSpecIso_inv (Ideal.isSMulRegular_algebraMap_affineBlowup hd), ?_⟩
  rw [← comap_comp, toSpecCoeff_reesAlgebra, affineBlowupι_toSpecZero]
  simpa only [Ideal.map_span, Set.image_singleton, CommRingCat.hom_ofHom] using
    comap_ofIdealTop_map_ΓSpecIso_inv (CommRingCat.ofHom (algebraMap R B)) (Ideal.span {d})

end Ideal

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Pullback of an effective Cartier divisor along an arbitrary blowup.** For any scheme `X`,
any ideal sheaf `I`, and any effective Cartier divisor `D` on `X`, the inverse image
`D.comap I.blowupToBase` on `Bl_I X` is again an effective Cartier divisor. No flatness,
integrality, reducedness, or Noetherian assumption is needed. -/
theorem IsEffectiveCartier.comap_blowupToBase {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (I : X.IdealSheafData) : (D.comap I.blowupToBase).IsEffectiveCartier := by
  refine isEffectiveCartier_of_forall_exists_isOpenImmersion _ fun x ↦ ?_
  obtain ⟨U, hxU, d, hd, hDd⟩ := (isEffectiveCartier_iff D).mp hD (I.blowupToBase x)
  have hU : IsAffineOpen U.1 := U.2
  refine ⟨_, I.blowupChart hU, inferInstance, ?_, ?_⟩
  · rw [← Scheme.Hom.coe_opensRange, opensRange_blowupChart]
    exact hxU
  · rw [← comap_comp, blowupChart_blowupToBase, comap_comp, comap_fromSpec_eq_ofIdealTop, hDd,
      Ideal.map_span, Set.image_singleton]
    exact Ideal.isEffectiveCartier_comap_toSpecCoeff_span_singleton (I.ideal ⟨U.1, hU⟩) hd

end AlgebraicGeometry.Scheme.IdealSheafData

/-! ### Degree-one Rees sections on `Proj R[It]` -/

namespace reesAlgebra

/-- In the Rees algebra `R[It]`, the degree-one elements `a t` and `b t` satisfy the cross-relation
`b · (a t) = a · (b t)`. -/
theorem algebraMap_mul_monomialDegreeOne_eq {R : Type*} [CommRing R] {I : Ideal R} {a b : R}
    (ha : a ∈ I) (hb : b ∈ I) :
    algebraMap R (reesAlgebra I) b * monomialDegreeOne ha =
      algebraMap R (reesAlgebra I) a * monomialDegreeOne hb := by
  ext1
  simp [Polynomial.C_mul_monomial, mul_comm]

end reesAlgebra

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

section ReesTwistingSheaf

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- On `Proj R[It]`, every twisting sheaf `𝒪(n)` is invertible, since the degree-one elements
`a t` (`a ∈ I`) cover `Proj R[It]`. -/
theorem isInvertible_twistingSheaf_reesAlgebra (I : Ideal R) (n : ℤ) :
    TauCeti.SheafOfModules.IsInvertible (R := (Proj (grade I)).ringCatSheaf)
      (Proj.twistingSheaf (grade I) n) := by
  have hs : Ideal.span (Set.range ((↑) : I → R)) = I := by
    rw [Subtype.range_coe, Ideal.span_eq]
  exact Proj.isInvertible_twistingSheaf_of_iSup_eq_top
    (fun a : I ↦ monomialDegreeOne a.2) (fun a ↦ monomialDegreeOne_mem_grade a.2)
    (Proj.iSup_basicOpen_eq_top _ _ (irrelevant_eq_span_monomialDegreeOne hs).le) n

/-- **Cross-relation of degree-one Rees sections.** For any `a, b ∈ I`, the global sections `x'ₐ`
and `x'_b` of `𝒪(1)` on `Proj R[It]` satisfy `b • x'ₐ = a • x'_b` under the pullback action of
`Γ(Spec R, ⊤) → Γ(Proj R[It], ⊤)`. -/
theorem smul_toTwistingSheaf_monomialDegreeOne_eq {a b : R} (ha : a ∈ I) (hb : b ∈ I) :
    ((Proj.toSpecCoeff (grade I)).appTop ((Scheme.ΓSpecIso (.of R)).inv b)) •
        Proj.toTwistingSheaf (grade I) rfl ⊤
          ⟨monomialDegreeOne ha, monomialDegreeOne_mem_grade ha⟩ =
      ((Proj.toSpecCoeff (grade I)).appTop ((Scheme.ΓSpecIso (.of R)).inv a)) •
        Proj.toTwistingSheaf (grade I) rfl ⊤
          ⟨monomialDegreeOne hb, monomialDegreeOne_mem_grade hb⟩ := by
  ext x
  simp only [Proj.twistingSheaf.smul_apply, Proj.toTwistingSheaf_apply_apply,
    Proj.val_toSpecCoeff_appTop_apply (grade I), Localization.mk_mul, mul_one,
    algebraMap_mul_monomialDegreeOne_eq ha hb]

/-- The nonvanishing locus of the degree-one Rees section `a t` of `𝒪(1)` on `Proj R[It]` is the
standard open `D₊(a t)`. -/
theorem nonvanishingLocus_toTwistingSheaf_monomialDegreeOne {a : R} (ha : a ∈ I) :
    haveI := isInvertible_twistingSheaf_reesAlgebra I 1
    (Proj.twistingSheaf (grade I) 1).nonvanishingLocus
        (Proj.toTwistingSheaf (grade I) rfl ⊤
          ⟨monomialDegreeOne ha, monomialDegreeOne_mem_grade ha⟩) =
      Proj.basicOpen (grade I) (monomialDegreeOne ha) := by
  have hs : Ideal.span (Set.range ((↑) : I → R)) = I := by
    rw [Subtype.range_coe, Ideal.span_eq]
  exact Proj.twistingSheaf.nonvanishingLocus_toTwistingSheaf
    (fun c : I ↦ monomialDegreeOne c.2) (fun c ↦ monomialDegreeOne_mem_grade c.2)
    (Proj.iSup_basicOpen_eq_top _ _ (irrelevant_eq_span_monomialDegreeOne hs).le)
    1 ⟨monomialDegreeOne ha, monomialDegreeOne_mem_grade ha⟩

/-- If `g : ι → R` generates `I`, the corresponding degree-one Rees sections `gᵢ t` generate
`𝒪(1)` on `Proj R[It]`: the induced morphism from the free sheaf `𝒪_{Proj R[It]}^{(ι)}` to `𝒪(1)`
is an epimorphism (making them a `SheafOfModules.GeneratingSections` family). -/
theorem epi_freeHomEquiv_symm_toTwistingSheaf_reesAlgebra {ι : Type u} (g : ι → R)
    (hg : Ideal.span (Set.range g) = I) :
    Epi ((Proj.twistingSheaf (grade I) 1).freeHomEquiv.symm fun i : ι ↦
      (Proj.twistingSheaf (grade I) 1).sectionsEquivTop.symm
        (Proj.toTwistingSheaf (grade I) (j := 1) rfl ⊤
          ⟨monomialDegreeOne (hg ▸ Ideal.subset_span (Set.mem_range_self i)),
            monomialDegreeOne_mem_grade _⟩)) := by
  have := isInvertible_twistingSheaf_reesAlgebra I 1
  refine epi_freeHomEquiv_symm_of_iSup_nonvanishingLocus_eq_top _ ?_
  simp_rw [nonvanishingLocus_toTwistingSheaf_monomialDegreeOne]
  exact Proj.iSup_basicOpen_eq_top _ _ (irrelevant_eq_span_monomialDegreeOne hg).le

/-- The two standard opens `D₊(x₁ t)` and `D₊(x₂ t)` cover the blowup `Proj R[(x₁, x₂)t]`. -/
theorem sup_basicOpen_monomialDegreeOne_span_pair (x₁ x₂ : R) :
    Proj.basicOpen (grade (Ideal.span ({x₁, x₂} : Set R)))
        (monomialDegreeOne (Ideal.subset_span (Set.mem_insert x₁ {x₂}))) ⊔
      Proj.basicOpen (grade (Ideal.span ({x₁, x₂} : Set R)))
        (monomialDegreeOne (Ideal.subset_span (Set.mem_insert_of_mem x₁ (Set.mem_singleton x₂)))) =
      ⊤ := by
  have hspan : Ideal.span (Set.range ![x₁, x₂]) = Ideal.span ({x₁, x₂} : Set R) := by
    rw [Matrix.range_cons_cons_empty]
  have htop := Proj.iSup_basicOpen_eq_top (grade (Ideal.span ({x₁, x₂} : Set R)))
    (fun i : Fin 2 ↦ monomialDegreeOne (I := Ideal.span ({x₁, x₂} : Set R))
      (hspan ▸ Ideal.subset_span ⟨i, rfl⟩))
    (irrelevant_eq_span_monomialDegreeOne hspan).le
  rw [← htop]
  refine le_antisymm (sup_le (le_iSup_of_le 0 le_rfl) (le_iSup_of_le 1 le_rfl))
    (iSup_le fun i ↦ ?_)
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- **No common zero of the degree-one Rees sections.** On `Proj R[(x₁, x₂)t]`, the nonvanishing
loci of the two degree-one sections `x'₁` and `x'₂` of `𝒪(1)` cover the entire blowup. -/
theorem sup_nonvanishingLocus_toTwistingSheaf_monomialDegreeOne_span_pair (x₁ x₂ : R) :
    haveI := isInvertible_twistingSheaf_reesAlgebra (Ideal.span ({x₁, x₂} : Set R)) 1
    (Proj.twistingSheaf (grade (Ideal.span ({x₁, x₂} : Set R))) 1).nonvanishingLocus
        (Proj.toTwistingSheaf (grade (Ideal.span ({x₁, x₂} : Set R))) rfl ⊤
          ⟨monomialDegreeOne (Ideal.subset_span (Set.mem_insert x₁ {x₂})),
            monomialDegreeOne_mem_grade _⟩) ⊔
      (Proj.twistingSheaf (grade (Ideal.span ({x₁, x₂} : Set R))) 1).nonvanishingLocus
        (Proj.toTwistingSheaf (grade (Ideal.span ({x₁, x₂} : Set R))) rfl ⊤
          ⟨monomialDegreeOne (Ideal.subset_span (Set.mem_insert_of_mem x₁ (Set.mem_singleton x₂))),
            monomialDegreeOne_mem_grade _⟩) =
      ⊤ := by
  have := isInvertible_twistingSheaf_reesAlgebra (Ideal.span ({x₁, x₂} : Set R)) 1
  rw [nonvanishingLocus_toTwistingSheaf_monomialDegreeOne,
    nonvanishingLocus_toTwistingSheaf_monomialDegreeOne]
  exact sup_basicOpen_monomialDegreeOne_span_pair x₁ x₂

/-- **The two degree-one Rees sections generate `𝒪(1)`.** On `Proj R[(x₁, x₂)t]`, the morphism
`𝒪² ⟶ 𝒪(1)` sending the two basis sections to `x'₁` and `x'₂` is an epimorphism. -/
theorem epi_freeHomEquiv_symm_toTwistingSheaf_span_pair (x₁ x₂ : R) :
    Epi ((Proj.twistingSheaf (grade (Ideal.span ({x₁, x₂} : Set R))) 1).freeHomEquiv.symm
      fun i : ULift.{u} (Fin 2) ↦
        (Proj.twistingSheaf (grade (Ideal.span ({x₁, x₂} : Set R))) 1).sectionsEquivTop.symm
          (Proj.toTwistingSheaf (grade (Ideal.span ({x₁, x₂} : Set R))) (j := 1) rfl ⊤
            (if i.down = 0 then
              ⟨monomialDegreeOne (Ideal.subset_span (Set.mem_insert x₁ {x₂})),
                monomialDegreeOne_mem_grade _⟩
            else
              ⟨monomialDegreeOne
                  (Ideal.subset_span (Set.mem_insert_of_mem x₁ (Set.mem_singleton x₂))),
                monomialDegreeOne_mem_grade _⟩))) := by
  have := isInvertible_twistingSheaf_reesAlgebra (Ideal.span ({x₁, x₂} : Set R)) 1
  refine epi_freeHomEquiv_symm_of_iSup_nonvanishingLocus_eq_top _ ?_
  refine Eq.trans ?_ (sup_nonvanishingLocus_toTwistingSheaf_monomialDegreeOne_span_pair x₁ x₂)
  refine le_antisymm (iSup_le fun ⟨i⟩ ↦ ?_)
    (sup_le (le_iSup_of_le ⟨0⟩ le_rfl) (le_iSup_of_le ⟨1⟩ le_rfl))
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

end ReesTwistingSheaf

end TauCeti.AlgebraicGeometry

/-! ### Global Cartier separation -/

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The **left residual ideal sheaf** `D'₁ = (p* D₁ : F)` on the blowup `Bl_{D₁ ⊔ D₂} X`, where
`p = (D₁ ⊔ D₂).blowupToBase` and `F = (D₁ ⊔ D₂).comap p` is the invertible exceptional divisor.
When `D₁` and `D₂` are effective Cartier divisors, `D'₁` is the effective Cartier divisor
`p* D₁ - F`. -/
def blowupSupResidualLeft (D₁ D₂ : X.IdealSheafData) : (D₁ ⊔ D₂).blowup.IdealSheafData :=
  (D₁.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)
    (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.fg_ideal

/-- The **right residual ideal sheaf** `D'₂ = (p* D₂ : F)` on the blowup `Bl_{D₁ ⊔ D₂} X`, where
`p = (D₁ ⊔ D₂).blowupToBase` and `F = (D₁ ⊔ D₂).comap p` is the invertible exceptional divisor.
When `D₁` and `D₂` are effective Cartier divisors, `D'₂` is the effective Cartier divisor
`p* D₂ - F`. -/
def blowupSupResidualRight (D₁ D₂ : X.IdealSheafData) : (D₁ ⊔ D₂).blowup.IdealSheafData :=
  (D₂.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)
    (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.fg_ideal

/-- Definitional unfolding of `blowupSupResidualLeft`. -/
theorem blowupSupResidualLeft_def (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualLeft D₂ =
      (D₁.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)
        (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.fg_ideal :=
  (rfl)

/-- Definitional unfolding of `blowupSupResidualRight`. -/
theorem blowupSupResidualRight_def (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualRight D₂ =
      (D₂.comap (D₁ ⊔ D₂).blowupToBase).colon ((D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase)
        (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.fg_ideal :=
  (rfl)

/-- **Left factorization `p* D₁ = F + D'₁`.** On `Bl_{D₁ ⊔ D₂} X`, the product of the exceptional
ideal `F` with the left residual ideal `D'₁` is the pulled-back ideal `p* D₁`. -/
theorem comap_blowupToBase_sup_mul_blowupSupResidualLeft (D₁ D₂ : X.IdealSheafData) :
    (D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase * D₁.blowupSupResidualLeft D₂ =
      D₁.comap (D₁ ⊔ D₂).blowupToBase :=
  (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.mul_colon_eq_of_le
    (comap_mono _ le_sup_left)

/-- **Right factorization `p* D₂ = F + D'₂`.** On `Bl_{D₁ ⊔ D₂} X`, the product of the exceptional
ideal `F` with the right residual ideal `D'₂` is the pulled-back ideal `p* D₂`. -/
theorem comap_blowupToBase_sup_mul_blowupSupResidualRight (D₁ D₂ : X.IdealSheafData) :
    (D₁ ⊔ D₂).comap (D₁ ⊔ D₂).blowupToBase * D₁.blowupSupResidualRight D₂ =
      D₂.comap (D₁ ⊔ D₂).blowupToBase :=
  (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.mul_colon_eq_of_le
    (comap_mono _ le_sup_right)

/-- **Coprimality of residual ideals.** On `Bl_{D₁ ⊔ D₂} X`, the sum of the two residual ideals
`D'₁` and `D'₂` is the unit ideal sheaf. -/
@[simp]
theorem blowupSupResidualLeft_sup_right (D₁ D₂ : X.IdealSheafData) :
    D₁.blowupSupResidualLeft D₂ ⊔ D₁.blowupSupResidualRight D₂ = ⊤ := by
  refine (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.mul_left_cancel ?_
  rw [mul_inf, comap_blowupToBase_sup_mul_blowupSupResidualLeft,
    comap_blowupToBase_sup_mul_blowupSupResidualRight, ← comap_sup, mul_top]

/-- **Cartier separation of supports.** On `Bl_{D₁ ⊔ D₂} X`, the two residual subschemes `V(D'₁)`
and `V(D'₂)` have disjoint supports. -/
theorem disjoint_support_blowupSupResidual (D₁ D₂ : X.IdealSheafData) :
    Disjoint (D₁.blowupSupResidualLeft D₂).support (D₁.blowupSupResidualRight D₂).support := by
  rw [disjoint_iff, ← support_sup, blowupSupResidualLeft_sup_right, support_top]

/-- **Cross-sum identity `p* D₁ + D'₂ = p* D₂ + D'₁`.** On `Bl_{D₁ ⊔ D₂} X`, the ideal products
`p* D₁ * D'₂` and `p* D₂ * D'₁` coincide. -/
theorem comap_mul_blowupSupResidualRight_eq (D₁ D₂ : X.IdealSheafData) :
    D₁.comap (D₁ ⊔ D₂).blowupToBase * D₁.blowupSupResidualRight D₂ =
      D₂.comap (D₁ ⊔ D₂).blowupToBase * D₁.blowupSupResidualLeft D₂ := by
  rw [← comap_blowupToBase_sup_mul_blowupSupResidualLeft,
    ← comap_blowupToBase_sup_mul_blowupSupResidualRight, mul_assoc, mul_assoc,
    mul_comm (D₁.blowupSupResidualLeft D₂)]

/-- If `D₁` is an effective Cartier divisor, its residual `D'₁ = p* D₁ - F` on `Bl_{D₁ ⊔ D₂} X`
is an effective Cartier divisor (for any ideal sheaf `D₂`). -/
theorem IsEffectiveCartier.blowupSupResidualLeft {D₁ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (D₂ : X.IdealSheafData) :
    (D₁.blowupSupResidualLeft D₂).IsEffectiveCartier :=
  (hD₁.comap_blowupToBase (D₁ ⊔ D₂)).isEffectiveCartier_colon
    (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase (comap_mono _ le_sup_left)

/-- If `D₂` is an effective Cartier divisor, its residual `D'₂ = p* D₂ - F` on `Bl_{D₁ ⊔ D₂} X`
is an effective Cartier divisor (for any ideal sheaf `D₁`). -/
theorem IsEffectiveCartier.blowupSupResidualRight {D₂ : X.IdealSheafData}
    (hD₂ : D₂.IsEffectiveCartier) (D₁ : X.IdealSheafData) :
    (D₁.blowupSupResidualRight D₂).IsEffectiveCartier :=
  (hD₂.comap_blowupToBase (D₁ ⊔ D₂)).isEffectiveCartier_colon
    (D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase (comap_mono _ le_sup_right)

/-- The blowup of the sum of two effective Cartier divisors is proper over `X`, without any
Noetherian assumption. -/
theorem IsEffectiveCartier.isProper_blowupToBase_sup {D₁ D₂ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (hD₂ : D₂.IsEffectiveCartier) :
    IsProper (D₁ ⊔ D₂).blowupToBase :=
  (D₁ ⊔ D₂).isProper_blowupToBase fun U ↦ Submodule.FG.sup (hD₁.fg_ideal U) (hD₂.fg_ideal U)

/-! ### Explicit affine chart equations of the residual ideals -/

/-- Affine chart pullback of a principal ideal `(b)` along `Spec R[I/a] ⟶ Proj R[It] ⟶ Spec R`. -/
private theorem comap_affineBlowupι_toSpecCoeff_span_singleton {R : Type u} [CommRing R]
    {I : Ideal R} {a b : R} (ha : a ∈ I) :
    ((ofIdealTop ((Ideal.span {b}).map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
        (Proj.toSpecCoeff (grade I))).comap (affineBlowupι (Localization.Away a) ha) =
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso (.of (I.affineBlowup a (Localization.Away a)))).inv
          (algebraMap R (I.affineBlowup a (Localization.Away a)) b)}) := by
  rw [← comap_comp, toSpecCoeff_reesAlgebra, affineBlowupι_toSpecZero,
    comap_ofIdealTop_map_ΓSpecIso_inv, CommRingCat.hom_ofHom,
    Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]

/-- Affine chart pullback of the centre `I` along `Spec R[I/a] ⟶ Proj R[It] ⟶ Spec R`. -/
private theorem comap_affineBlowupι_toSpecCoeff_self {R : Type u} [CommRing R]
    {I : Ideal R} {a : R} (ha : a ∈ I) :
    ((ofIdealTop (I.map (Scheme.ΓSpecIso (.of R)).inv.hom)).comap
        (Proj.toSpecCoeff (grade I))).comap (affineBlowupι (Localization.Away a) ha) =
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso (.of (I.affineBlowup a (Localization.Away a)))).inv
          (algebraMap R (I.affineBlowup a (Localization.Away a)) a)}) := by
  rw [← comap_comp, toSpecCoeff_reesAlgebra]
  exact comap_affineBlowupι_eq_ofIdealTop (Localization.Away a) ha

/-- Helper computing the pullback of a locally principal ideal sheaf `L` on `X` to an affine
blowup chart `Spec Γ(X, U)[I(U)/a]`. -/
private theorem comap_affineBlowupι_blowupChart_of_ideal_eq_span {I L : X.IdealSheafData}
    {U : X.Opens} (hU : IsAffineOpen U) {a b : Γ(X, U)} (ha : a ∈ I.ideal ⟨U, hU⟩)
    (hL : L.ideal ⟨U, hU⟩ = Ideal.span {b}) :
    (L.comap I.blowupToBase).comap (affineBlowupι (Localization.Away a) ha ≫ I.blowupChart hU) =
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso (.of ((I.ideal ⟨U, hU⟩).affineBlowup a (Localization.Away a)))).inv
          (algebraMap Γ(X, U) ((I.ideal ⟨U, hU⟩).affineBlowup a (Localization.Away a)) b)}) := by
  have hchart : (L.comap I.blowupToBase).comap (I.blowupChart hU) =
      (ofIdealTop ((Ideal.span {b}).map (Scheme.ΓSpecIso Γ(X, U)).inv.hom)).comap
        (Proj.toSpecCoeff (grade (I.ideal ⟨U, hU⟩))) := by
    rw [← comap_comp, blowupChart_blowupToBase, comap_comp, comap_fromSpec_eq_ofIdealTop, hL]
  exact (comap_comp _ _ _).trans
    ((congrArg (·.comap (affineBlowupι (Localization.Away a) ha)) hchart).trans
      (comap_affineBlowupι_toSpecCoeff_span_singleton ha))

/-- Helper computing the pullback of the exceptional ideal sheaf `I.comap I.blowupToBase` to an
affine blowup chart `Spec Γ(X, U)[I(U)/a]`. -/
private theorem comap_affineBlowupι_blowupChart_exceptional {I : X.IdealSheafData}
    {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)} (ha : a ∈ I.ideal ⟨U, hU⟩) :
    (I.comap I.blowupToBase).comap (affineBlowupι (Localization.Away a) ha ≫ I.blowupChart hU) =
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso (.of ((I.ideal ⟨U, hU⟩).affineBlowup a (Localization.Away a)))).inv
          (algebraMap Γ(X, U) ((I.ideal ⟨U, hU⟩).affineBlowup a (Localization.Away a)) a)}) :=
  (comap_comp _ _ _).trans
    ((congrArg (·.comap (affineBlowupι (Localization.Away a) ha))
        (I.comap_blowupChart_comap_blowupToBase hU)).trans
      (comap_affineBlowupι_toSpecCoeff_self ha))

/-- Helper: on `Spec R`, a nonzerodivisor `a : R` defines a principal effective Cartier divisor. -/
private theorem isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv {R : Type u} [CommRing R] {a : R}
    (ha : IsSMulRegular R a) :
    (ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv a})).IsEffectiveCartier := by
  have h := Scheme.Hom.isEffectiveCartier_ofIdealTop_span_appTop (𝟙 (Spec (.of R)))
    (Scheme.isSMulRegular_ΓSpecIso_inv ha)
  rwa [Scheme.Hom.id_appTop] at h

/-- On the affine blowup chart `Spec R[I/a]`, the product of the principal ideal `(a)` with the
principal ideal `(b / a)` is the principal ideal `(b)`. -/
private theorem ofIdealTop_span_algebraMap_mul_divBy {R : Type u} [CommRing R]
    {I : Ideal R} {a b : R} (hb : b ∈ I) :
    ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso (.of (I.affineBlowup a (Localization.Away a)))).inv
          (algebraMap R (I.affineBlowup a (Localization.Away a)) a)}) *
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso (.of (I.affineBlowup a (Localization.Away a)))).inv
          (⟨TauCeti.Localization.divBy (S := Localization.Away a) b a,
            Ideal.divBy_mem_affineBlowup hb⟩ : I.affineBlowup a (Localization.Away a))}) =
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso (.of (I.affineBlowup a (Localization.Away a)))).inv
          (algebraMap R (I.affineBlowup a (Localization.Away a)) b)}) := by
  have hmul :
      algebraMap R (I.affineBlowup a (Localization.Away a)) a *
          ⟨TauCeti.Localization.divBy (S := Localization.Away a) b a,
            Ideal.divBy_mem_affineBlowup hb⟩ =
        algebraMap R (I.affineBlowup a (Localization.Away a)) b := by
    ext
    simp
  rw [← ofIdealTop_mul, Ideal.span_singleton_mul_span_singleton, ← map_mul, hmul]

/-- On the affine chart `Spec Γ(X, U)[(D₁ ⊔ D₂)(U)/x₁]` over an affine open `U` where
`D₁(U) = (x₁)`, the left residual ideal sheaf `D'₁` pulls back to the unit ideal sheaf. -/
theorem comap_affineBlowupι_blowupChart_blowupSupResidualLeft_left
    (D₁ D₂ : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U) {x₁ : Γ(X, U)}
    (hD₁ : D₁.ideal ⟨U, hU⟩ = Ideal.span {x₁})
    (hx₁ : x₁ ∈ (D₁ ⊔ D₂).ideal ⟨U, hU⟩ := by
      rw [ideal_sup, Pi.sup_apply, hD₁]
      exact Ideal.mem_sup_left (Ideal.subset_span rfl)) :
    (D₁.blowupSupResidualLeft D₂).comap
        (affineBlowupι (Localization.Away x₁) hx₁ ≫ (D₁ ⊔ D₂).blowupChart hU) = ⊤ := by
  rw [blowupSupResidualLeft, comap_colon_of_isOpenImmersion, colon_eq_top_iff,
    comap_affineBlowupι_blowupChart_of_ideal_eq_span hU hx₁ hD₁,
    comap_affineBlowupι_blowupChart_exceptional hU hx₁]

/-- On the affine chart `Spec Γ(X, U)[(D₁ ⊔ D₂)(U)/x₁]` over an affine open `U` where
`D₂(U) = (x₂)` and `x₁ ∈ (D₁ ⊔ D₂)(U)`, the right residual ideal sheaf `D'₂` pulls back to the
principal ideal generated by `x₂ / x₁`. -/
theorem comap_affineBlowupι_blowupChart_blowupSupResidualRight_left
    (D₁ D₂ : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U) {x₁ x₂ : Γ(X, U)}
    (hx₁ : x₁ ∈ (D₁ ⊔ D₂).ideal ⟨U, hU⟩) (hD₂ : D₂.ideal ⟨U, hU⟩ = Ideal.span {x₂})
    (hx₂ : x₂ ∈ (D₁ ⊔ D₂).ideal ⟨U, hU⟩ := by
      rw [ideal_sup, Pi.sup_apply, hD₂]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)) :
    (D₁.blowupSupResidualRight D₂).comap
        (affineBlowupι (Localization.Away x₁) hx₁ ≫ (D₁ ⊔ D₂).blowupChart hU) =
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso
            (.of (((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₁ (Localization.Away x₁)))).inv
          (⟨TauCeti.Localization.divBy (S := Localization.Away x₁) x₂ x₁,
            Ideal.divBy_mem_affineBlowup hx₂⟩ :
            ((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₁ (Localization.Away x₁))}) := by
  have hreg : (ofIdealTop (Ideal.span
      {(Scheme.ΓSpecIso
          (.of (((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₁ (Localization.Away x₁)))).inv
        (algebraMap Γ(X, U) (((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₁ (Localization.Away x₁))
          x₁)})).IsEffectiveCartier :=
    isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv
      (Ideal.isRegular_algebraMap_affineBlowup (I := (D₁ ⊔ D₂).ideal ⟨U, hU⟩)
        (a := x₁) (S := Localization.Away x₁)).left.isSMulRegular
  have hprod := (comap_mul _ _
      (affineBlowupι (Localization.Away x₁) hx₁ ≫ (D₁ ⊔ D₂).blowupChart hU)).symm.trans
    (congrArg (·.comap (affineBlowupι (Localization.Away x₁) hx₁ ≫ (D₁ ⊔ D₂).blowupChart hU))
      (comap_blowupToBase_sup_mul_blowupSupResidualRight D₁ D₂))
  rw [comap_affineBlowupι_blowupChart_exceptional hU hx₁,
    comap_affineBlowupι_blowupChart_of_ideal_eq_span hU hx₁ hD₂] at hprod
  exact hreg.mul_left_cancel (hprod.trans (ofIdealTop_span_algebraMap_mul_divBy hx₂).symm)

/-- Symmetric chart equation: on the affine chart `Spec Γ(X, U)[(D₁ ⊔ D₂)(U)/x₂]` over an affine
open `U` where `D₂(U) = (x₂)`, the right residual ideal sheaf `D'₂` pulls back to the unit ideal
sheaf. -/
theorem comap_affineBlowupι_blowupChart_blowupSupResidualRight_right
    (D₁ D₂ : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U) {x₂ : Γ(X, U)}
    (hD₂ : D₂.ideal ⟨U, hU⟩ = Ideal.span {x₂})
    (hx₂ : x₂ ∈ (D₁ ⊔ D₂).ideal ⟨U, hU⟩ := by
      rw [ideal_sup, Pi.sup_apply, hD₂]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)) :
    (D₁.blowupSupResidualRight D₂).comap
        (affineBlowupι (Localization.Away x₂) hx₂ ≫ (D₁ ⊔ D₂).blowupChart hU) = ⊤ := by
  rw [blowupSupResidualRight, comap_colon_of_isOpenImmersion, colon_eq_top_iff,
    comap_affineBlowupι_blowupChart_of_ideal_eq_span hU hx₂ hD₂,
    comap_affineBlowupι_blowupChart_exceptional hU hx₂]

/-- Symmetric chart equation: on the affine chart `Spec Γ(X, U)[(D₁ ⊔ D₂)(U)/x₂]` over an affine
open `U` where `D₁(U) = (x₁)` and `x₂ ∈ (D₁ ⊔ D₂)(U)`, the left residual ideal sheaf `D'₁` pulls
back to the principal ideal generated by `x₁ / x₂`. -/
theorem comap_affineBlowupι_blowupChart_blowupSupResidualLeft_right
    (D₁ D₂ : X.IdealSheafData) {U : X.Opens} (hU : IsAffineOpen U) {x₁ x₂ : Γ(X, U)}
    (hx₂ : x₂ ∈ (D₁ ⊔ D₂).ideal ⟨U, hU⟩) (hD₁ : D₁.ideal ⟨U, hU⟩ = Ideal.span {x₁})
    (hx₁ : x₁ ∈ (D₁ ⊔ D₂).ideal ⟨U, hU⟩ := by
      rw [ideal_sup, Pi.sup_apply, hD₁]
      exact Ideal.mem_sup_left (Ideal.subset_span rfl)) :
    (D₁.blowupSupResidualLeft D₂).comap
        (affineBlowupι (Localization.Away x₂) hx₂ ≫ (D₁ ⊔ D₂).blowupChart hU) =
      ofIdealTop (Ideal.span
        {(Scheme.ΓSpecIso
            (.of (((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₂ (Localization.Away x₂)))).inv
          (⟨TauCeti.Localization.divBy (S := Localization.Away x₂) x₁ x₂,
            Ideal.divBy_mem_affineBlowup hx₁⟩ :
            ((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₂ (Localization.Away x₂))}) := by
  have hreg : (ofIdealTop (Ideal.span
      {(Scheme.ΓSpecIso
          (.of (((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₂ (Localization.Away x₂)))).inv
        (algebraMap Γ(X, U) (((D₁ ⊔ D₂).ideal ⟨U, hU⟩).affineBlowup x₂ (Localization.Away x₂))
          x₂)})).IsEffectiveCartier :=
    isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv
      (Ideal.isRegular_algebraMap_affineBlowup (I := (D₁ ⊔ D₂).ideal ⟨U, hU⟩)
        (a := x₂) (S := Localization.Away x₂)).left.isSMulRegular
  have hprod := (comap_mul _ _
      (affineBlowupι (Localization.Away x₂) hx₂ ≫ (D₁ ⊔ D₂).blowupChart hU)).symm.trans
    (congrArg (·.comap (affineBlowupι (Localization.Away x₂) hx₂ ≫ (D₁ ⊔ D₂).blowupChart hU))
      (comap_blowupToBase_sup_mul_blowupSupResidualLeft D₁ D₂))
  rw [comap_affineBlowupι_blowupChart_exceptional hU hx₂,
    comap_affineBlowupι_blowupChart_of_ideal_eq_span hU hx₂ hD₁] at hprod
  exact hreg.mul_left_cancel (hprod.trans (ofIdealTop_span_algebraMap_mul_divBy hx₁).symm)

/-! ### Degenerate and comparable cases -/

/-- If `D₂ ≤ D₁` (geometrically `D₁ ≤ D₂`), the left residual ideal is the unit ideal sheaf. -/
theorem blowupSupResidualLeft_eq_top_of_le {D₁ D₂ : X.IdealSheafData} (h : D₂ ≤ D₁) :
    D₁.blowupSupResidualLeft D₂ = ⊤ := by
  rw [blowupSupResidualLeft, colon_eq_top_iff]
  exact comap_mono _ (sup_le le_rfl h)

/-- If `D₁ ≤ D₂` (geometrically `D₂ ≤ D₁`), the right residual ideal is the unit ideal sheaf. -/
theorem blowupSupResidualRight_eq_top_of_le {D₁ D₂ : X.IdealSheafData} (h : D₁ ≤ D₂) :
    D₁.blowupSupResidualRight D₂ = ⊤ := by
  rw [blowupSupResidualRight, colon_eq_top_iff]
  exact comap_mono _ (sup_le h le_rfl)

/-- If `D₁` is effective Cartier and `D₂ ≤ D₁`, the blowup along `D₁ ⊔ D₂ = D₁` is an
isomorphism. -/
theorem IsEffectiveCartier.isIso_blowupToBase_sup_of_le {D₁ D₂ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (h : D₂ ≤ D₁) : IsIso (D₁ ⊔ D₂).blowupToBase := by
  rw [isIso_blowupToBase_iff, sup_eq_left.mpr h]
  exact hD₁

/-- If `D₁` is effective Cartier and `D₂ ≤ D₁`, the right residual ideal on `Bl_{D₁ ⊔ D₂} X` is
the pullback of the quotient `(D₂ : D₁)`. -/
theorem IsEffectiveCartier.blowupSupResidualRight_of_le {D₁ D₂ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (h : D₂ ≤ D₁) :
    D₁.blowupSupResidualRight D₂ = (D₂.colon D₁ hD₁.fg_ideal).comap (D₁ ⊔ D₂).blowupToBase := by
  refine ((D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.eq_colon_of_mul_eq ?_).symm
  rw [← comap_mul, sup_eq_left.mpr h, hD₁.mul_colon_eq_of_le h]

/-- If `D₂` is effective Cartier and `D₁ ≤ D₂`, the left residual ideal on `Bl_{D₁ ⊔ D₂} X` is
the pullback of the quotient `(D₁ : D₂)`. -/
theorem IsEffectiveCartier.blowupSupResidualLeft_of_le {D₁ D₂ : X.IdealSheafData}
    (hD₂ : D₂.IsEffectiveCartier) (h : D₁ ≤ D₂) :
    D₁.blowupSupResidualLeft D₂ = (D₁.colon D₂ hD₂.fg_ideal).comap (D₁ ⊔ D₂).blowupToBase := by
  refine ((D₁ ⊔ D₂).isEffectiveCartier_comap_blowupToBase.eq_colon_of_mul_eq ?_).symm
  rw [← comap_mul, sup_eq_right.mpr h, hD₂.mul_colon_eq_of_le h]

/-- For identical ideal sheaves `D`, the left residual ideal on `Bl_{D ⊔ D} X` is `⊤`. -/
@[simp]
theorem blowupSupResidualLeft_self (D : X.IdealSheafData) : D.blowupSupResidualLeft D = ⊤ :=
  blowupSupResidualLeft_eq_top_of_le le_rfl

/-- For identical ideal sheaves `D`, the right residual ideal on `Bl_{D ⊔ D} X` is `⊤`. -/
@[simp]
theorem blowupSupResidualRight_self (D : X.IdealSheafData) : D.blowupSupResidualRight D = ⊤ :=
  blowupSupResidualRight_eq_top_of_le le_rfl

/-- When `D₁ = ⊤`, the left residual ideal is `⊤`. -/
@[simp]
theorem blowupSupResidualLeft_top_left (D₂ : X.IdealSheafData) :
    (⊤ : X.IdealSheafData).blowupSupResidualLeft D₂ = ⊤ :=
  blowupSupResidualLeft_eq_top_of_le le_top

/-- When `D₁ = ⊤`, the right residual ideal is the pullback of `D₂`. -/
@[simp]
theorem blowupSupResidualRight_top_left (D₂ : X.IdealSheafData) :
    (⊤ : X.IdealSheafData).blowupSupResidualRight D₂ =
      D₂.comap ((⊤ : X.IdealSheafData) ⊔ D₂).blowupToBase := by
  simpa only [colon_top] using (isEffectiveCartier_top X).blowupSupResidualRight_of_le le_top

/-- When `D₂ = ⊤`, the left residual ideal is the pullback of `D₁`. -/
@[simp]
theorem blowupSupResidualLeft_top_right (D₁ : X.IdealSheafData) :
    D₁.blowupSupResidualLeft ⊤ = D₁.comap (D₁ ⊔ ⊤).blowupToBase := by
  simpa only [colon_top] using (isEffectiveCartier_top X).blowupSupResidualLeft_of_le le_top

/-- When `D₂ = ⊤`, the right residual ideal is `⊤`. -/
@[simp]
theorem blowupSupResidualRight_top_right (D₁ : X.IdealSheafData) :
    D₁.blowupSupResidualRight ⊤ = ⊤ :=
  blowupSupResidualRight_eq_top_of_le le_top

end AlgebraicGeometry.Scheme.IdealSheafData

/-! ### Picard-group identity for Cartier separation -/

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **Picard-group difference identity `D'₁ - D'₂ = p* (D₁ - D₂)`.** In the Picard group of
`Bl_{D₁ ⊔ D₂} X`, the ratio of the line-bundle classes of the residual effective Cartier divisors
equals the pullback of the ratio of the classes of `D₁` and `D₂`. -/
theorem mk_toInvertibleSheaf_blowupSupResidual_mul_inv {D₁ D₂ : X.IdealSheafData}
    (hD₁ : D₁.IsEffectiveCartier) (hD₂ : D₂.IsEffectiveCartier) :
    mk (hD₁.blowupSupResidualLeft D₂).toInvertibleSheaf *
        (mk (hD₂.blowupSupResidualRight D₁).toInvertibleSheaf)⁻¹ =
      pullback (D₁ ⊔ D₂).blowupToBase
        (mk hD₁.toInvertibleSheaf * (mk hD₂.toInvertibleSheaf)⁻¹) := by
  rw [pullback_mul, pullback_inv,
    hD₁.pullback_mk_toInvertibleSheaf (hD₁.comap_blowupToBase (D₁ ⊔ D₂)),
    hD₂.pullback_mk_toInvertibleSheaf (hD₂.comap_blowupToBase (D₁ ⊔ D₂)),
    mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq,
    mul_comm (mk (hD₁.blowupSupResidualLeft D₂).toInvertibleSheaf),
    ← mk_toInvertibleSheaf_mul, ← mk_toInvertibleSheaf_mul]
  exact mk_toInvertibleSheaf_congr _ _ (comap_mul_blowupSupResidualRight_eq D₁ D₂).symm

end TauCeti.AlgebraicGeometry.LineBundleClass

/-! ### Concrete checks -/

section Examples

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry

-- Check 1: On `𝔸²_k = Spec k[X, Y]`, blowing up `(X, Y)` separates the strict transforms of the two
-- coordinate axes `(X)` and `(Y)`, producing disjoint effective Cartier divisors.
example (k : Type u) [CommRing k] :
    let R := MvPolynomial (Fin 2) k
    let D₁ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (MvPolynomial.X 0)})
    let D₂ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (MvPolynomial.X 1)})
    (D₁.blowupSupResidualLeft D₂).IsEffectiveCartier ∧
      (D₁.blowupSupResidualRight D₂).IsEffectiveCartier ∧
      Disjoint (D₁.blowupSupResidualLeft D₂).support (D₁.blowupSupResidualRight D₂).support := by
  intro R D₁ D₂
  have hX (i : Fin 2) : IsSMulRegular R (MvPolynomial.X i) :=
    MvPolynomial.isRegular_X.left.isSMulRegular
  have hD₁ : D₁.IsEffectiveCartier := isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv (hX 0)
  have hD₂ : D₂.IsEffectiveCartier := isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv (hX 1)
  exact ⟨hD₁.blowupSupResidualLeft D₂, hD₂.blowupSupResidualRight D₁,
    disjoint_support_blowupSupResidual D₁ D₂⟩

-- Check 2: On `𝔸¹_k = Spec k[t]`, for `D₁ = 2[0] = (t²)` and `D₂ = 3[0] = (t³)`, the blowup along
-- `(t²) ⊔ (t³) = (t²)` is an isomorphism, with `D'₁ = ⊤` (empty) and `D'₂ = p* (t)`.
example (k : Type u) [CommRing k] :
    let R := Polynomial k
    let D₁ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.X ^ 2)})
    let D₂ : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.X ^ 3)})
    IsIso (D₁ ⊔ D₂).blowupToBase ∧
      D₁.blowupSupResidualLeft D₂ = ⊤ ∧
      D₁.blowupSupResidualRight D₂ =
        (ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv Polynomial.X})).comap
          (D₁ ⊔ D₂).blowupToBase := by
  intro R D₁ D₂
  have hX : IsSMulRegular R Polynomial.X := Polynomial.monic_X.isRegular.left.isSMulRegular
  have hD₁ : D₁.IsEffectiveCartier :=
    isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv (hX.pow 2)
  have hle : D₂ ≤ D₁ := fun U ↦ Ideal.map_mono <| by
    rw [Ideal.span_singleton_le_span_singleton]
    exact map_dvd (Scheme.ΓSpecIso (.of R)).inv.hom ⟨Polynomial.X, by ring⟩
  refine ⟨hD₁.isIso_blowupToBase_sup_of_le hle, blowupSupResidualLeft_eq_top_of_le hle, ?_⟩
  rw [hD₁.blowupSupResidualRight_of_le hle]
  congr 1
  rw [colon_ofIdealTop]
  refine congrArg ofIdealTop ?_
  rw [pow_succ, map_mul, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.colon_span_singleton_mul_of_isLeftRegular
    (Scheme.isSMulRegular_ΓSpecIso_inv (hX.pow 2))

-- Check 3: On the nonreduced scheme `Spec ℚ[e, t]/(e²) = Spec (DualNumber ℚ)[t]`, `(t)` is
-- effective Cartier while `(e)` is not; for `D₁ = (t)` and `D₂ = (t²)`, the blowup along `(t)` is
-- an isomorphism with residual ideals `⊤` and `p* (t)` and cross-sum
-- `p* (t) * D'₂ = p* (t²) * D'₁`.
example :
    let R := Polynomial (DualNumber ℚ)
    let Dt : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv Polynomial.X})
    let Dt2 : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.X ^ 2)})
    let De : (Spec (.of R)).IdealSheafData :=
      ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (.of R)).inv (Polynomial.C DualNumber.eps)})
    Dt.IsEffectiveCartier ∧ ¬ De.IsEffectiveCartier ∧
      IsIso (Dt ⊔ Dt2).blowupToBase ∧
      Dt.blowupSupResidualLeft Dt2 = ⊤ ∧
      Dt.blowupSupResidualRight Dt2 = Dt.comap (Dt ⊔ Dt2).blowupToBase ∧
      Dt.comap (Dt ⊔ Dt2).blowupToBase * Dt.blowupSupResidualRight Dt2 =
        Dt2.comap (Dt ⊔ Dt2).blowupToBase * Dt.blowupSupResidualLeft Dt2 := by
  intro R Dt Dt2 De
  have hX : IsSMulRegular R Polynomial.X := Polynomial.monic_X.isRegular.left.isSMulRegular
  have hDt : Dt.IsEffectiveCartier := isEffectiveCartier_ofIdealTop_span_ΓSpecIso_inv hX
  have hDe : ¬ De.IsEffectiveCartier := by
    intro h
    obtain ⟨x⟩ : Nonempty (Spec (.of R)) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
    obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff De).mp h x
    have hDe2 : De ^ 2 = ⊥ := by
      dsimp only [De]
      rw [← ofIdealTop_pow, Ideal.span_singleton_pow, sq, ← map_mul, ← map_mul,
        DualNumber.eps_mul_eps, map_zero, map_zero, Ideal.span_singleton_zero]
      ext U : 2
      simp
    have ha2 : a * a = 0 := by
      have hmem : a * a ∈ (De ^ 2).ideal U := by
        rw [ideal_pow, Pi.pow_apply, sq, hUa, Ideal.span_singleton_mul_span_singleton]
        exact Ideal.subset_span rfl
      simpa only [hDe2, ideal_bot, Pi.bot_apply, Ideal.mem_bot] using hmem
    have ha0 : a = 0 := ha (ha2.trans (mul_zero a).symm)
    have h10 : (1 : Γ(Spec (.of R), U)) = 0 := ha (by simp [ha0])
    have hg := congrArg ((Spec (.of R)).presheaf.germ U x hxU) h10
    rw [map_one, map_zero] at hg
    exact one_ne_zero hg
  have hle : Dt2 ≤ Dt := fun U ↦ Ideal.map_mono <| by
    rw [Ideal.span_singleton_le_span_singleton]
    exact map_dvd (Scheme.ΓSpecIso (.of R)).inv.hom ⟨Polynomial.X, by ring⟩
  refine ⟨hDt, hDe, hDt.isIso_blowupToBase_sup_of_le hle,
    blowupSupResidualLeft_eq_top_of_le hle, ?_,
    comap_mul_blowupSupResidualRight_eq Dt Dt2⟩
  rw [hDt.blowupSupResidualRight_of_le hle]
  congr 1
  rw [colon_ofIdealTop]
  refine congrArg ofIdealTop ?_
  rw [sq, map_mul, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.colon_span_singleton_mul_of_isLeftRegular (Scheme.isSMulRegular_ΓSpecIso_inv hX)

end Examples
