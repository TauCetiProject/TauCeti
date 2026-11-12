/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear.Homology

/-!
# The minimal A-infinity model on cohomology

Over a field, the unary complex of an `A∞` algebra contracts onto its cohomology.  The
contraction is the general contraction of a graded vector space with a square-zero differential
onto its homology `ker m₁ ⧸ im m₁` (`TauCeti.InternalGrading.homologyContraction`), whose target is
identified with the cohomology by `TauCeti.AInfinityAlgebra.cohomologyEquivHomology`.  It chooses
homogeneous representatives of cohomology classes and a homogeneous degree-minus-one section `s`
of `m₁` onto the boundaries; then `q = 1 - s m₁` projects onto cycles, the projection to
cohomology is the class of `q x`, and the contracting homotopy applies `s` to the boundary
`q x - i [q x]`.

These formulas give a special contraction with homogeneous inclusion, projection, and homotopy.
Applying homological transfer produces the minimal `A∞` structure on cohomology and a
quasi-isomorphism to the original algebra.  Its binary operation is the product already induced
on cohomology, so this is Kadeishvili's existence theorem with the multiplication pinned rather
than merely an abstract minimal structure.

The transferred projection is a quasi-isomorphism in the other direction, from the original
algebra to the minimal model, and it induces the identity on cohomology.  Composing with it gives
the uniqueness clause of Kadeishvili's theorem: a quasi-isomorphism between minimal `A∞` algebras
is an `A∞` isomorphism, so every minimal `A∞` algebra with a quasi-isomorphism to the original
algebra, or from it, is isomorphic to the minimal model through an explicit composite.  The
isomorphism depends on the chosen quasi-isomorphism and is not canonical.

## Main definitions

* `TauCeti.AInfinityAlgebra.cohomologyContraction`: a homogeneous special contraction of the
  unary complex onto cohomology with zero differential.
* `TauCeti.AInfinityAlgebra.minimalModel`: the transferred `A∞` structure on cohomology.
* `TauCeti.AInfinityAlgebra.minimalModelInclusion`: the extending quasi-isomorphism from the
  minimal model to the original algebra.
* `TauCeti.AInfinityAlgebra.minimalModelProjection`: the quasi-isomorphism from the original
  algebra to the minimal model extending the projection of the contraction.

## Main results

* `TauCeti.AInfinityAlgebra.isMinimal_minimalModel`: the transferred structure is minimal.
* `TauCeti.AInfinityAlgebra.minimalModel_m_two`: its binary operation is the cohomology product.
* `TauCeti.AInfinityAlgebra.minimalModel_m_three`: its ternary operation is the
  Kontsevich--Soibelman/Merkulov expression `p m₃ (i ⊗ i ⊗ i) + p m₂ (h m₂ (i ⊗ i) ⊗ i)
  - p m₂ (i ⊗ h m₂ (i ⊗ i))`, with the Koszul sign of the first input on the last term.
* `TauCeti.AInfinityAlgebra.component_two_minimalModelInclusion`: the quadratic component of the
  extending morphism is `-h m₂ (i ⊗ i)`.
* `TauCeti.AInfinityAlgebra.isQuasiIso_minimalModelInclusion`: the extending morphism is a
  quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.cohomologyMap_minimalModelInclusion_cohomologyEquiv`: the extending
  morphism induces the identity on cohomology.
* `TauCeti.AInfinityAlgebra.isQuasiIso_minimalModelProjection`,
  `TauCeti.AInfinityAlgebra.minimalModelProjection_comp_minimalModelInclusion` and
  `TauCeti.AInfinityAlgebra.cohomologyMap_minimalModelProjection`: the projection onto the minimal
  model is a quasi-isomorphism, a left inverse of the inclusion, and the identity on cohomology.
* `TauCeti.AInfinityAlgebra.isIso_minimalModelProjection_comp` and
  `TauCeti.AInfinityAlgebra.isIso_comp_minimalModelInclusion`: **uniqueness of the minimal
  model**; a quasi-isomorphism from or to a minimal `A∞` algebra, composed with the projection onto
  or the inclusion of the minimal model, is an `A∞` isomorphism.

## References

* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

open DirectSum

namespace TauCeti.AInfinityAlgebra

universe uK uA uB

variable {K : Type uK} {A : Type uA} [Field K] [AddCommGroup A] [Module K A]
  (𝒜 : AInfinityAlgebra K A)

private theorem isHomogeneous_differential :
    LinearMap.IsHomogeneous 𝒜.differential 𝒜.grading.piece 𝒜.grading.piece 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ 𝒜.differential_mem_piece hx

/-- The contraction of the unary complex onto the homology `ker m₁ ⧸ im m₁`. -/
private noncomputable def homologyContraction :
    LinearSpecialContraction 𝒜.differential
      (0 : Module.End K (𝒜.differential.homology 𝒜.differential_comp_self_eq_zero)) :=
  𝒜.grading.homologyContraction 𝒜.isHomogeneous_differential 𝒜.differential_comp_self_eq_zero

/-- The comparison of cohomology with homology has degree zero. -/
private theorem isHomogeneous_cohomologyEquivHomology :
    LinearMap.IsHomogeneous (𝒜.cohomologyEquivHomology : 𝒜.Cohomology →ₗ[K] _)
      𝒜.cohomologyGrading.piece
      (𝒜.grading.homology 𝒜.isHomogeneous_differential 𝒜.differential_comp_self_eq_zero).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hc ↦ by
    obtain ⟨x, hx, hp, rfl⟩ := 𝒜.mem_cohomologyGrading_piece_iff.1 hc
    rw [add_zero, LinearEquiv.coe_coe, cohomologyEquivHomology_cohomologyClass]
    exact 𝒜.grading.homologyπ_mem_homology_piece _ _ hp

/-- The inverse comparison of homology with cohomology has degree zero. -/
private theorem isHomogeneous_cohomologyEquivHomology_symm :
    LinearMap.IsHomogeneous (𝒜.cohomologyEquivHomology.symm : _ →ₗ[K] 𝒜.Cohomology)
      (𝒜.grading.homology 𝒜.isHomogeneous_differential 𝒜.differential_comp_self_eq_zero).piece
      𝒜.cohomologyGrading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hy ↦ by
    obtain ⟨z, hz, rfl⟩ := (𝒜.grading.mem_homology_piece_iff _ _).1 hy
    rw [add_zero, LinearEquiv.coe_coe, cohomologyEquivHomology_symm_homologyπ]
    exact 𝒜.cohomologyClass_mem_cohomologyGrading_piece _ hz

/-- Over a field, the unary complex of an `A∞` algebra admits a homogeneous special
contraction onto its cohomology with zero differential: the contraction onto the homology
`ker m₁ ⧸ im m₁` (`InternalGrading.homologyContraction`), with its target identified with the
cohomology by `cohomologyEquivHomology`. -/
noncomputable def cohomologyContraction :
    LinearSpecialContraction 𝒜.differential (0 : Module.End K 𝒜.Cohomology) where
  incl := 𝒜.homologyContraction.incl ∘ₗ 𝒜.cohomologyEquivHomology.toLinearMap
  proj := 𝒜.cohomologyEquivHomology.symm.toLinearMap ∘ₗ 𝒜.homologyContraction.proj
  homotopy := 𝒜.homologyContraction.homotopy
  dM_comp_incl := by
    rw [← LinearMap.comp_assoc, 𝒜.homologyContraction.dM_comp_incl, LinearMap.comp_zero,
      LinearMap.zero_comp, LinearMap.comp_zero]
  proj_comp_dM := by
    rw [LinearMap.comp_assoc, 𝒜.homologyContraction.proj_comp_dM, LinearMap.zero_comp,
      LinearMap.comp_zero, LinearMap.zero_comp]
  proj_comp_incl := LinearMap.ext fun x ↦ by
    simp [𝒜.homologyContraction.proj_incl_apply]
  dM_comp_homotopy_add_homotopy_comp_dM := LinearMap.ext fun x ↦ by
    rw [𝒜.homologyContraction.dM_comp_homotopy_add_homotopy_comp_dM]
    simp
  homotopy_comp_incl := by
    rw [← LinearMap.comp_assoc, 𝒜.homologyContraction.homotopy_comp_incl, LinearMap.zero_comp]
  proj_comp_homotopy := by
    rw [LinearMap.comp_assoc, 𝒜.homologyContraction.proj_comp_homotopy, LinearMap.comp_zero]
  homotopy_comp_homotopy := 𝒜.homologyContraction.homotopy_comp_homotopy

private theorem cohomologyContraction_incl :
    𝒜.cohomologyContraction.incl =
      𝒜.homologyContraction.incl ∘ₗ 𝒜.cohomologyEquivHomology.toLinearMap :=
  rfl

private theorem cohomologyContraction_incl_apply (x : 𝒜.Cohomology) :
    𝒜.cohomologyContraction.incl x =
      𝒜.homologyContraction.incl (𝒜.cohomologyEquivHomology x) :=
  rfl

private theorem cohomologyContraction_proj :
    𝒜.cohomologyContraction.proj =
      𝒜.cohomologyEquivHomology.symm.toLinearMap ∘ₗ 𝒜.homologyContraction.proj :=
  rfl

private theorem cohomologyContraction_homotopy :
    𝒜.cohomologyContraction.homotopy = 𝒜.homologyContraction.homotopy :=
  rfl

/-- The inclusion of the cohomology contraction is a cycle. -/
theorem cohomologyContraction_incl_mem_cycles (x : 𝒜.Cohomology) :
    𝒜.cohomologyContraction.incl x ∈ 𝒜.cycles := by
  have h := 𝒜.grading.homologyContraction_incl_mem_ker 𝒜.isHomogeneous_differential
    𝒜.differential_comp_self_eq_zero (𝒜.cohomologyEquivHomology x)
  rwa [← homologyContraction, ← cohomologyContraction_incl_apply, ← cycles_def] at h

/-- The inclusion of the cohomology contraction chooses a representative of the given class. -/
@[simp]
theorem cohomologyClass_cohomologyContraction_incl (x : 𝒜.Cohomology) :
    𝒜.cohomologyClass (𝒜.cohomologyContraction_incl_mem_cycles x) = x := by
  apply 𝒜.cohomologyEquivHomology.injective
  simp only [cohomologyEquivHomology_cohomologyClass, cohomologyContraction_incl_apply,
    homologyContraction]
  exact 𝒜.grading.homologyπ_homologyContraction_incl _ _ _

/-- The projection of the cohomology contraction sends a cycle to its cohomology class. -/
@[simp]
theorem cohomologyContraction_proj_of_mem_cycles {x : A} (hx : x ∈ 𝒜.cycles) :
    𝒜.cohomologyContraction.proj x = 𝒜.cohomologyClass hx := by
  rw [cohomologyContraction_proj, LinearMap.comp_apply, homologyContraction,
    InternalGrading.homologyContraction_proj_of_mem_ker _ _ _ (by rwa [← cycles_def]),
    LinearEquiv.coe_coe, cohomologyEquivHomology_symm_homologyπ]

/-- The inclusion of the cohomology contraction has degree zero. -/
theorem isHomogeneous_cohomologyContraction_incl :
    LinearMap.IsHomogeneous 𝒜.cohomologyContraction.incl 𝒜.cohomologyGrading.piece
      𝒜.grading.piece 0 := by
  rw [cohomologyContraction_incl, homologyContraction]
  simpa only [add_zero] using
    (𝒜.grading.isHomogeneous_homologyContraction_incl _ _).comp
      𝒜.isHomogeneous_cohomologyEquivHomology

/-- The projection of the cohomology contraction has degree zero. -/
theorem isHomogeneous_cohomologyContraction_proj :
    LinearMap.IsHomogeneous 𝒜.cohomologyContraction.proj 𝒜.grading.piece
      𝒜.cohomologyGrading.piece 0 := by
  rw [cohomologyContraction_proj, homologyContraction]
  simpa only [add_zero] using
    𝒜.isHomogeneous_cohomologyEquivHomology_symm.comp
      (𝒜.grading.isHomogeneous_homologyContraction_proj _ _)

/-- The homotopy of the cohomology contraction has degree minus one. -/
theorem isHomogeneous_cohomologyContraction_homotopy :
    LinearMap.IsHomogeneous 𝒜.cohomologyContraction.homotopy 𝒜.grading.piece
      𝒜.grading.piece (-1) := by
  rw [cohomologyContraction_homotopy, homologyContraction]
  exact 𝒜.grading.isHomogeneous_homologyContraction_homotopy _ _

/-- The inclusion of the cohomology contraction has degree zero, so it commutes with the Koszul
twist. -/
theorem cohomologyContraction_incl_koszulTwist (x : 𝒜.Cohomology) :
    𝒜.cohomologyContraction.incl (𝒜.cohomologyGrading.koszulTwist 1 x) =
      𝒜.grading.koszulTwist 1 (𝒜.cohomologyContraction.incl x) := by
  simpa using
    (𝒜.isHomogeneous_cohomologyContraction_incl.koszulTwist_apply 1 x).symm

/-- The homotopy of the cohomology contraction bounds every cycle with vanishing class. -/
theorem m_one_cohomologyContraction_homotopy {w : A} (hw : w ∈ 𝒜.cycles)
    (h₀ : 𝒜.cohomologyClass hw = 0) :
    𝒜.m 1 ![𝒜.cohomologyContraction.homotopy w] = w := by
  have h := LinearMap.congr_fun 𝒜.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM w
  have hd : 𝒜.differential w = 0 := by rw [differential_apply, ← mem_cycles]; exact hw
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hd, map_zero, add_zero, 𝒜.cohomologyContraction_proj_of_mem_cycles hw, h₀,
    sub_zero] at h
  rwa [differential_apply] at h

/-- The minimal `A∞` model on cohomology obtained by homogeneous transfer. -/
noncomputable def minimalModel : AInfinityAlgebra K 𝒜.Cohomology :=
  𝒜.transfer 𝒜.cohomologyContraction 𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl 𝒜.isHomogeneous_cohomologyContraction_proj

/-- The grading of the minimal model is the quotient grading on cohomology. -/
@[simp]
theorem minimalModel_grading : 𝒜.minimalModel.grading = 𝒜.cohomologyGrading := by
  rw [minimalModel, transfer_grading]

/-- The transferred model on cohomology is minimal. -/
theorem isMinimal_minimalModel : 𝒜.minimalModel.IsMinimal :=
  𝒜.isMinimal_transfer 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj rfl

/-- The differential of the minimal model vanishes. -/
@[simp]
theorem minimalModel_differential : 𝒜.minimalModel.differential = 0 :=
  (𝒜.minimalModel.isMinimal_def).mp 𝒜.isMinimal_minimalModel

/-- The binary operation of the minimal model is the product induced on cohomology. -/
@[simp]
theorem minimalModel_m_two (x y : 𝒜.Cohomology) :
    𝒜.minimalModel.m 2 ![x, y] = x * y := by
  rw [minimalModel, mul_transfer]
  have hz : 𝒜.mul (𝒜.cohomologyContraction.incl x) (𝒜.cohomologyContraction.incl y) ∈
      𝒜.cycles := by
    simpa only [mul_apply] using 𝒜.m_two_mem_cycles
      (𝒜.cohomologyContraction_incl_mem_cycles x) (𝒜.cohomologyContraction_incl_mem_cycles y)
  rw [cohomologyContraction_proj_of_mem_cycles _ hz]
  calc
    𝒜.cohomologyClass hz = 𝒜.cohomologyMul
        (𝒜.cohomologyClass (𝒜.cohomologyContraction_incl_mem_cycles x))
        (𝒜.cohomologyClass (𝒜.cohomologyContraction_incl_mem_cycles y)) := by
      simpa only [mul_apply] using
        (𝒜.cohomologyMul_cohomologyClass (𝒜.cohomologyContraction_incl_mem_cycles x)
          (𝒜.cohomologyContraction_incl_mem_cycles y)).symm
    _ = x * y := by
      rw [cohomologyClass_cohomologyContraction_incl, cohomologyClass_cohomologyContraction_incl,
        𝒜.cohomology_mul_eq_cohomologyMul]

/-- The ternary operation of the minimal model, in the Kontsevich--Soibelman/Merkulov form: the
ternary operation of `𝒜` on the chosen cycle representatives, corrected by the two homotopies of
adjacent products; the second correction carries the Koszul sign of the first input. -/
@[simp]
theorem minimalModel_m_three (x y z : 𝒜.Cohomology) :
    𝒜.minimalModel.m 3 ![x, y, z] =
      𝒜.cohomologyContraction.proj (𝒜.m 3 ![𝒜.cohomologyContraction.incl x,
          𝒜.cohomologyContraction.incl y, 𝒜.cohomologyContraction.incl z]) +
        𝒜.cohomologyContraction.proj (𝒜.m 2 ![𝒜.cohomologyContraction.homotopy
          (𝒜.m 2 ![𝒜.cohomologyContraction.incl x, 𝒜.cohomologyContraction.incl y]),
          𝒜.cohomologyContraction.incl z]) -
        𝒜.cohomologyContraction.proj (𝒜.m 2
          ![𝒜.cohomologyContraction.incl (𝒜.cohomologyGrading.koszulTwist 1 x),
            𝒜.cohomologyContraction.homotopy
              (𝒜.m 2 ![𝒜.cohomologyContraction.incl y, 𝒜.cohomologyContraction.incl z])]) :=
  𝒜.m_three_transfer 𝒜.cohomologyContraction 𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl 𝒜.isHomogeneous_cohomologyContraction_proj x y z

/-- The `A∞` morphism from the minimal model on cohomology to the original algebra, extending
the chosen cycle representatives. -/
noncomputable def minimalModelInclusion : AInfinityHom 𝒜.minimalModel 𝒜 :=
  𝒜.transferInclusion 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj

/-- The linear part of the minimal-model quasi-isomorphism is the chosen inclusion of cohomology
representatives. -/
@[simp]
theorem linearPart_minimalModelInclusion :
    𝒜.minimalModelInclusion.linearPart = 𝒜.cohomologyContraction.incl := by
  unfold minimalModelInclusion minimalModel
  rw [linearPart_transferInclusion]

/-- The quadratic component of the minimal-model quasi-isomorphism is `-h m₂ (i ⊗ i)`: minus the
homotopy of the product of the chosen cycle representatives. -/
@[simp]
theorem component_two_minimalModelInclusion (x y : 𝒜.Cohomology) :
    𝒜.minimalModelInclusion.component 2 ![x, y] =
      -𝒜.cohomologyContraction.homotopy
        (𝒜.m 2 ![𝒜.cohomologyContraction.incl x, 𝒜.cohomologyContraction.incl y]) :=
  𝒜.component_two_transferInclusion 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy 𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj x y

/-- The morphism from the minimal model to the original algebra induces the identity on
cohomology, once the minimal model is identified with its own cohomology. -/
theorem cohomologyMap_minimalModelInclusion_cohomologyEquiv (x : 𝒜.Cohomology) :
    𝒜.minimalModelInclusion.cohomologyMap (𝒜.isMinimal_minimalModel.cohomologyEquiv x) = x := by
  simp

/-- The morphism from the minimal model to the original algebra is a quasi-isomorphism. -/
theorem isQuasiIso_minimalModelInclusion : 𝒜.minimalModelInclusion.IsQuasiIso :=
  𝒜.isQuasiIso_transferInclusion 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj

/-- The `A∞` morphism from the original algebra to its minimal model on cohomology, extending the
projection of the cohomology contraction, which sends a cycle to its class. -/
noncomputable def minimalModelProjection : AInfinityHom 𝒜 𝒜.minimalModel :=
  𝒜.transferProjection 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj

/-- The linear part of the projection onto the minimal model is the projection of the cohomology
contraction. -/
@[simp]
theorem linearPart_minimalModelProjection :
    𝒜.minimalModelProjection.linearPart = 𝒜.cohomologyContraction.proj := by
  unfold minimalModelProjection minimalModel
  rw [linearPart_transferProjection]

/-- The projection onto the minimal model is a left inverse of the inclusion of the minimal
model. -/
@[simp]
theorem minimalModelProjection_comp_minimalModelInclusion :
    𝒜.minimalModelProjection.comp 𝒜.minimalModelInclusion = AInfinityHom.id 𝒜.minimalModel :=
  𝒜.transferProjection_comp_transferInclusion 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj

/-- The projection onto the minimal model induces the identity on cohomology, once the minimal
model is identified with its own cohomology. -/
@[simp]
theorem cohomologyMap_minimalModelProjection (x : 𝒜.Cohomology) :
    𝒜.minimalModelProjection.cohomologyMap x = 𝒜.isMinimal_minimalModel.cohomologyEquiv x := by
  obtain ⟨z, hz, rfl⟩ := 𝒜.exists_cohomologyClass_eq x
  rw [AInfinityHom.cohomologyMap_cohomologyClass, IsMinimal.cohomologyEquiv_apply]
  congr 1
  rw [linearPart_minimalModelProjection, cohomologyContraction_proj_of_mem_cycles]

/-- The projection onto the minimal model is a quasi-isomorphism. -/
theorem isQuasiIso_minimalModelProjection : 𝒜.minimalModelProjection.IsQuasiIso :=
  𝒜.isQuasiIso_transferProjection 𝒜.cohomologyContraction
    𝒜.isHomogeneous_cohomologyContraction_homotopy
    𝒜.isHomogeneous_cohomologyContraction_incl
    𝒜.isHomogeneous_cohomologyContraction_proj

/-! ### Uniqueness of the minimal model -/

section Uniqueness

variable {B : Type uB} [AddCommGroup B] [Module K B] {ℬ : AInfinityAlgebra K B}

/-- **Uniqueness of the minimal model**, for a quasi-isomorphism into `𝒜`: if `f` is a
quasi-isomorphism from a minimal `A∞` algebra to `𝒜`, then `f` followed by the projection onto the
minimal model is an `A∞` isomorphism. -/
theorem isIso_minimalModelProjection_comp (hℬ : ℬ.IsMinimal) {f : AInfinityHom ℬ 𝒜}
    (hf : f.IsQuasiIso) : (𝒜.minimalModelProjection.comp f).IsIso :=
  (𝒜.isQuasiIso_minimalModelProjection.comp hf).isIso hℬ 𝒜.isMinimal_minimalModel

/-- **Uniqueness of the minimal model**, for a quasi-isomorphism out of `𝒜`: if `g` is a
quasi-isomorphism from `𝒜` to a minimal `A∞` algebra, then the inclusion of the minimal model
followed by `g` is an `A∞` isomorphism. -/
theorem isIso_comp_minimalModelInclusion (hℬ : ℬ.IsMinimal) {g : AInfinityHom 𝒜 ℬ}
    (hg : g.IsQuasiIso) : (g.comp 𝒜.minimalModelInclusion).IsIso :=
  (hg.comp 𝒜.isQuasiIso_minimalModelInclusion).isIso 𝒜.isMinimal_minimalModel hℬ

end Uniqueness

end TauCeti.AInfinityAlgebra
