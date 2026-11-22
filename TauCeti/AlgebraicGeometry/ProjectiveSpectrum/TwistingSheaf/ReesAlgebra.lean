/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ReesAlgebra
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.NonvanishingLocus
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic

/-!
# Twisting sheaves on `Proj` of a Rees algebra

On the projective spectrum `Proj R[It]` of the Rees algebra of an ideal `I` of a commutative ring
`R`, the degree-one monomials `a t` (`a ∈ I`) cover `Proj R[It]` by their standard opens `D₊(a t)`.
Consequently every twisting sheaf `𝒪(n)` is invertible
(`TauCeti.AlgebraicGeometry.isInvertible_twistingSheaf_reesAlgebra`), the sections `a t` of `𝒪(1)`
have nonvanishing locus `D₊(a t)` (`nonvanishingLocus_toTwistingSheaf_monomialDegreeOne`) and
satisfy the cross-relation `b • (a t) = a • (b t)`
(`smul_toTwistingSheaf_monomialDegreeOne_eq`), and any generating family of `I` induces an
epimorphism from the corresponding free sheaf onto `𝒪(1)`
(`epi_freeHomEquiv_symm_toTwistingSheaf_reesAlgebra`). For a two-generator ideal `(x₁, x₂)`, the
two sections `x₁ t` and `x₂ t` have no common zero and generate `𝒪(1)`.
-/

public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace reesAlgebra

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- On `Proj R[It]`, every twisting sheaf `𝒪(n)` is invertible, since the degree-one elements
`a t` (`a ∈ I`) cover `Proj R[It]`. -/
theorem isInvertible_twistingSheaf_reesAlgebra (I : Ideal R) (n : ℤ) :
    TauCeti.SheafOfModules.IsInvertible (R := (Proj (grade I)).ringCatSheaf)
      (Proj.twistingSheaf (grade I) n) :=
  Proj.isInvertible_twistingSheaf_of_iSup_eq_top
    (fun a : I ↦ monomialDegreeOne a.property) (fun a ↦ monomialDegreeOne_mem_grade a.property)
    (iSup_basicOpen_monomialDegreeOne_coe I) n

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
@[simp]
theorem nonvanishingLocus_toTwistingSheaf_monomialDegreeOne {a : R} (ha : a ∈ I) :
    haveI := isInvertible_twistingSheaf_reesAlgebra I 1
    (Proj.twistingSheaf (grade I) 1).nonvanishingLocus
        (Proj.toTwistingSheaf (grade I) (n := 1) (j := 1) Int.cast_one ⊤
          ⟨monomialDegreeOne ha, monomialDegreeOne_mem_grade ha⟩) =
      Proj.basicOpen (grade I) (monomialDegreeOne ha) :=
  Proj.twistingSheaf.nonvanishingLocus_toTwistingSheaf
    (fun c : I ↦ monomialDegreeOne c.property) (fun c ↦ monomialDegreeOne_mem_grade c.property)
    (iSup_basicOpen_monomialDegreeOne_coe I)
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
  simp_rw [Int.cast_ofNat_Int, nonvanishingLocus_toTwistingSheaf_monomialDegreeOne]
  exact iSup_basicOpen_monomialDegreeOne hg

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
  have hspan : Ideal.span (Set.range (![x₁, x₂] ∘ ULift.down)) =
      Ideal.span ({x₁, x₂} : Set R) := by
    rw [Set.range_comp, ULift.down_surjective.range_eq, Set.image_univ,
      Matrix.range_cons_cons_empty]
  convert epi_freeHomEquiv_symm_toTwistingSheaf_reesAlgebra
    (fun i : ULift.{u} (Fin 2) ↦ ![x₁, x₂] i.down) hspan using 2
  funext ⟨i⟩
  fin_cases i <;> rfl

end TauCeti.AlgebraicGeometry
