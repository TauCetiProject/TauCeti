/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Inverse
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Homotopy

/-!
# Homotopy equivalences of A-infinity algebras and Whitehead's theorem

An `A∞` morphism `f : A ⟶ B` over a commutative ring `R` is a *homotopy equivalence*
(`TauCeti.AInfinityHom.IsHomotopyEquiv`) when it admits a two-sided inverse up to `A∞` homotopy: an
`A∞` morphism `g : B ⟶ A` together with `A∞` homotopies `g ∘ f ⇒ id_A` and `f ∘ g ⇒ id_B`.

Combining the arity-one extraction and the two-stage obstruction lifting in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Inverse` characterises `A∞` homotopy
equivalences over an arbitrary commutative ring solely in terms of their linear part
(`TauCeti.AInfinityHom.isHomotopyEquiv_iff_nonempty_linearHomotopyInverse`): `f` is an `A∞`
homotopy equivalence if and only if `f.linearPart` admits a graded chain-homotopy inverse.  In
particular, `A∞` homotopy equivalences are closed under composition and invariant under `A∞`
homotopy, and homological perturbation transfer along any graded special contraction produces `A∞`
homotopy equivalences over every commutative ring.

Over a field `K`, the cohomology contractions of `A` and `B` invert the linear part of any
quasi-isomorphism up to chain homotopy (`TauCeti.AInfinityHom.IsQuasiIso.linearHomotopyInverse`),
yielding Whitehead's theorem for `A∞` algebras
(`TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`): an `A∞` morphism over a field is a
homotopy equivalence if and only if it is a quasi-isomorphism.

## Main definitions

* `TauCeti.AInfinityHom.IsHomotopyEquiv`: two-sided invertibility up to `A∞` homotopy.
* `TauCeti.AInfinityHom.IsQuasiIso.linearHomotopyInverse`,
  `TauCeti.AInfinityHom.IsQuasiIso.homotopyInverse`,
  `TauCeti.AInfinityHom.IsQuasiIso.leftHomotopy`, and
  `TauCeti.AInfinityHom.IsQuasiIso.rightHomotopy`: the `A∞` homotopy inverse and witnessing
  homotopies of a quasi-isomorphism over a field.
* `TauCeti.AInfinityAlgebra.transferInclusionLinearHomotopyInverse` and
  `TauCeti.AInfinityAlgebra.transferProjectionLinearHomotopyInverse`: linear chain-homotopy inverses
  of homological perturbation transfer morphisms.

## Main results

* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_nonempty_linearHomotopyInverse`: over any commutative
  ring, an `A∞` morphism is a homotopy equivalence if and only if its linear part admits a graded
  chain-homotopy inverse.
* `TauCeti.AInfinityHom.IsHomotopyEquiv.comp` and
  `TauCeti.AInfinityHom.Homotopy.isHomotopyEquiv_iff`: closure under composition and homotopy
  invariance of `A∞` homotopy equivalences.
* `TauCeti.AInfinityHom.isHomotopyEquiv_iff_isQuasiIso`: Whitehead's theorem for `A∞` algebras over
  a field.
* `TauCeti.AInfinityAlgebra.isHomotopyEquiv_transferInclusion`,
  `TauCeti.AInfinityAlgebra.isHomotopyEquiv_transferProjection`,
  `TauCeti.AInfinityAlgebra.isHomotopyEquiv_minimalModelInclusion`, and
  `TauCeti.AInfinityAlgebra.isHomotopyEquiv_minimalModelProjection`: homological perturbation
  transfer and minimal-model morphisms are `A∞` homotopy equivalences.

## References

* A. Prouté, *`A∞`-structures: Modèle minimal de Baues–Lemaire et homologie des fibrations*,
  Reprints in Theory and Applications of Categories 21 (2011), 1--99 (thèse d'État, 1986), §4.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Theorem 1.3.3.1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Homology, Homotopy and
  Applications 3 (2001), Section 3.7.
-/

public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

section CommRing

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- An `A∞` morphism is a **homotopy equivalence** when it admits a two-sided inverse up to `A∞`
homotopy. -/
def IsHomotopyEquiv (f : AInfinityHom AA BB) : Prop :=
  ∃ g : AInfinityHom BB AA,
    Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
      Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB))

/-- An `A∞` morphism is a homotopy equivalence exactly when it admits an `A∞` morphism `g` with
homotopies `g ∘ f ⇒ id` and `f ∘ g ⇒ id`. -/
theorem isHomotopyEquiv_def (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔
      ∃ g : AInfinityHom BB AA,
        Nonempty (Homotopy (g.comp f) (AInfinityHom.id AA)) ∧
          Nonempty (Homotopy (f.comp g) (AInfinityHom.id BB)) :=
  Iff.rfl

/-- Every graded chain-homotopy inverse to `f.linearPart` lifts to witness `f.IsHomotopyEquiv`. -/
theorem LinearHomotopyInverse.isHomotopyEquiv {f : AInfinityHom AA BB}
    (d : f.LinearHomotopyInverse) : f.IsHomotopyEquiv :=
  ⟨d.homotopyInverse, ⟨d.leftHomotopyLift⟩, ⟨d.rightHomotopyLift⟩⟩

/-- The lifted `A∞` homotopy inverse is itself a homotopy equivalence, with inverse `f`. -/
theorem LinearHomotopyInverse.isHomotopyEquiv_homotopyInverse {f : AInfinityHom AA BB}
    (d : f.LinearHomotopyInverse) : d.homotopyInverse.IsHomotopyEquiv :=
  ⟨f, ⟨d.rightHomotopyLift⟩, ⟨d.leftHomotopyLift⟩⟩

/-- Every `A∞` homotopy equivalence induces a graded chain-homotopy inverse to its linear part. -/
theorem IsHomotopyEquiv.nonempty_linearHomotopyInverse {f : AInfinityHom AA BB}
    (hf : f.IsHomotopyEquiv) : Nonempty f.LinearHomotopyInverse := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf
  exact ⟨Homotopy.toLinearHomotopyInverse hL hR⟩

/-- **Characterisation of `A∞` homotopy equivalences over a commutative ring**: an `A∞` morphism is
a homotopy equivalence if and only if its linear part admits a graded chain-homotopy inverse. -/
theorem isHomotopyEquiv_iff_nonempty_linearHomotopyInverse (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ Nonempty f.LinearHomotopyInverse :=
  ⟨IsHomotopyEquiv.nonempty_linearHomotopyInverse, fun ⟨d⟩ ↦ d.isHomotopyEquiv⟩

/-- The identity `A∞` morphism is a homotopy equivalence. -/
@[simp]
theorem isHomotopyEquiv_id (AA : AInfinityAlgebra R A) : (AInfinityHom.id AA).IsHomotopyEquiv :=
  ⟨AInfinityHom.id AA, ⟨by rw [comp_id]; exact Homotopy.refl _⟩,
    ⟨by rw [comp_id]; exact Homotopy.refl _⟩⟩

/-- Every `A∞` isomorphism is a homotopy equivalence. -/
theorem IsIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsIso) : f.IsHomotopyEquiv := by
  obtain ⟨g, hg₁, hg₂⟩ := (isIso_def f).1 hf
  exact ⟨g, ⟨hg₁ ▸ Homotopy.refl _⟩, ⟨hg₂ ▸ Homotopy.refl _⟩⟩

/-- Every `A∞` homotopy equivalence is a quasi-isomorphism. -/
theorem IsHomotopyEquiv.isQuasiIso {f : AInfinityHom AA BB} (hf : f.IsHomotopyEquiv) :
    f.IsQuasiIso := by
  obtain ⟨g, ⟨hL⟩, ⟨hR⟩⟩ := hf
  have hLMap : g.cohomologyMap.comp f.cohomologyMap = NonUnitalAlgHom.id R AA.Cohomology := by
    rw [← cohomologyMap_comp, hL.cohomologyMap_eq, cohomologyMap_id]
  have hRMap : f.cohomologyMap.comp g.cohomologyMap = NonUnitalAlgHom.id R BB.Cohomology := by
    rw [← cohomologyMap_comp, hR.cohomologyMap_eq, cohomologyMap_id]
  rw [isQuasiIso_def]
  exact Function.bijective_iff_has_inverse.2
    ⟨g.cohomologyMap, DFunLike.congr_fun hLMap, DFunLike.congr_fun hRMap⟩

/-- `A∞` homotopy equivalences are closed under composition. -/
theorem IsHomotopyEquiv.comp {g : AInfinityHom BB CC} {f : AInfinityHom AA BB}
    (hg : g.IsHomotopyEquiv) (hf : f.IsHomotopyEquiv) : (g.comp f).IsHomotopyEquiv := by
  obtain ⟨dg⟩ := hg.nonempty_linearHomotopyInverse
  obtain ⟨df⟩ := hf.nonempty_linearHomotopyInverse
  exact (dg.comp df).isHomotopyEquiv

/-- Homotopic `A∞` morphisms are homotopy equivalences together. -/
theorem Homotopy.isHomotopyEquiv_iff {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    f.IsHomotopyEquiv ↔ g.IsHomotopyEquiv := by
  rw [isHomotopyEquiv_iff_nonempty_linearHomotopyInverse,
    isHomotopyEquiv_iff_nonempty_linearHomotopyInverse]
  exact ⟨fun ⟨d⟩ ↦ ⟨d.ofHomotopy h⟩, fun ⟨d⟩ ↦ ⟨d.ofHomotopySymm h⟩⟩

end CommRing

/-! ### Homotopy inverses of quasi-isomorphisms over a field -/

section Field

universe uK

variable {K : Type uK} {A : Type uA} {B : Type uB} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  {AA : AInfinityAlgebra K A} {BB : AInfinityAlgebra K B}

private noncomputable def IsQuasiIso.linearInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    B →ₗ[K] A :=
  AA.cohomologyContraction.incl ∘ₗ hf.cohomologyLinearEquiv.symm.toLinearMap ∘ₗ
    BB.cohomologyContraction.proj

private theorem IsQuasiIso.isHomogeneous_linearInv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    LinearMap.IsHomogeneous hf.linearInv BB.grading.piece AA.grading.piece 0 := by
  have he : LinearMap.IsHomogeneous hf.cohomologyLinearEquiv.symm.toLinearMap
      BB.cohomologyGrading.piece AA.cohomologyGrading.piece 0 :=
    LinearMap.isHomogeneous_def.2 fun _ _ hc ↦ by
      rw [add_zero, LinearEquiv.coe_coe, ← hf.cohomologyMapInv_apply]
      exact hf.cohomologyMapInv_mem_cohomologyGrading_piece hc
  rw [IsQuasiIso.linearInv]
  simpa only [add_zero] using
    AA.isHomogeneous_cohomologyContraction_incl.comp
      (he.comp BB.isHomogeneous_cohomologyContraction_proj)

private theorem IsQuasiIso.proj_linearPart_incl {f : AInfinityHom AA BB} (hf : f.IsQuasiIso)
    (x : AA.Cohomology) :
    BB.cohomologyContraction.proj (f.linearPart (AA.cohomologyContraction.incl x)) =
      hf.cohomologyLinearEquiv x := by
  have hx : AA.cohomologyContraction.incl x ∈ AA.cycles :=
    AA.cohomologyContraction_incl_mem_cycles x
  rw [BB.cohomologyContraction_proj_of_mem_cycles (f.linearPart_mem_cycles hx),
    ← f.cohomologyMap_cohomologyClass hx, AA.cohomologyClass_cohomologyContraction_incl,
    hf.cohomologyLinearEquiv_apply]

private theorem IsQuasiIso.differential_comp_linearInv {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    AA.differential ∘ₗ hf.linearInv = hf.linearInv ∘ₗ BB.differential :=
  LinearMap.ext fun b ↦ by
    have hA := LinearMap.congr_fun AA.cohomologyContraction.dM_comp_incl
      (hf.cohomologyLinearEquiv.symm (BB.cohomologyContraction.proj b))
    have hB := LinearMap.congr_fun BB.cohomologyContraction.proj_comp_dM b
    simp only [IsQuasiIso.linearInv, LinearMap.comp_apply, LinearMap.zero_apply,
      LinearEquiv.coe_coe] at hA hB ⊢
    rw [hA, hB, map_zero, map_zero, map_zero]

private theorem IsQuasiIso.linearInv_comp_linearPart_sub_id {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    hf.linearInv ∘ₗ f.linearPart - LinearMap.id =
      AA.differential ∘ₗ
          (hf.linearInv ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
            AA.cohomologyContraction.homotopy) +
        (hf.linearInv ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
          AA.cohomologyContraction.homotopy) ∘ₗ AA.differential :=
  LinearMap.ext fun a ↦ by
    have hc := eq_sub_of_add_eq
      (LinearMap.congr_fun AA.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM a)
    have hcomm := LinearMap.congr_fun hf.differential_comp_linearInv
      (f.linearPart (AA.cohomologyContraction.homotopy a))
    have hfcomm := LinearMap.congr_fun f.differential_comp_linearPart
      (AA.cohomologyContraction.homotopy a)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hc hcomm hfcomm ⊢
    rw [map_sub, hcomm, hfcomm, hc]
    simp only [IsQuasiIso.linearInv, LinearMap.comp_apply, map_sub, LinearEquiv.coe_coe,
      hf.proj_linearPart_incl, LinearEquiv.symm_apply_apply]
    abel

private theorem IsQuasiIso.linearPart_comp_linearInv_sub_id {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) :
    f.linearPart ∘ₗ hf.linearInv - LinearMap.id =
      BB.differential ∘ₗ
          (BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.linearInv -
            BB.cohomologyContraction.homotopy) +
        (BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.linearInv -
          BB.cohomologyContraction.homotopy) ∘ₗ BB.differential :=
  LinearMap.ext fun b ↦ by
    have hc := eq_sub_of_add_eq
      (LinearMap.congr_fun BB.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM b)
    have hc' := eq_sub_of_add_eq
      (LinearMap.congr_fun BB.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM
        (f.linearPart (hf.linearInv b)))
    have hcomm := LinearMap.congr_fun hf.differential_comp_linearInv b
    have hfcomm := LinearMap.congr_fun f.differential_comp_linearPart (hf.linearInv b)
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at hc hc' hcomm hfcomm ⊢
    rw [map_sub, hc, hc', ← hcomm, ← hfcomm]
    simp only [IsQuasiIso.linearInv, LinearMap.comp_apply, LinearEquiv.coe_coe,
      hf.proj_linearPart_incl, LinearEquiv.apply_symm_apply]
    abel

/-- Over a field, the cohomology contractions of `AA` and `BB` equip the linear part of any
quasi-isomorphism `f : AA ⟶ BB` with an explicit graded chain-homotopy inverse. -/
noncomputable def IsQuasiIso.linearHomotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.LinearHomotopyInverse where
  inv := hf.linearInv
  isHomogeneous_inv := hf.isHomogeneous_linearInv
  differential_comp_inv := hf.differential_comp_linearInv
  leftHomotopy := hf.linearInv ∘ₗ f.linearPart ∘ₗ AA.cohomologyContraction.homotopy -
    AA.cohomologyContraction.homotopy
  isHomogeneous_leftHomotopy := by
    have hLf : LinearMap.IsHomogeneous (f.linearPart ∘ₗ AA.cohomologyContraction.homotopy)
        AA.grading.piece BB.grading.piece (-1) := by
      simpa only [add_zero] using
        f.isHomogeneous_linearPart.comp AA.isHomogeneous_cohomologyContraction_homotopy
    exact LinearMap.IsHomogeneous.sub
      (by simpa only [add_zero, LinearMap.comp_assoc] using hf.isHomogeneous_linearInv.comp hLf)
      AA.isHomogeneous_cohomologyContraction_homotopy
  inv_comp_linearPart_sub_id := hf.linearInv_comp_linearPart_sub_id
  rightHomotopy := BB.cohomologyContraction.homotopy ∘ₗ f.linearPart ∘ₗ hf.linearInv -
    BB.cohomologyContraction.homotopy
  isHomogeneous_rightHomotopy := by
    have hRf : LinearMap.IsHomogeneous (f.linearPart ∘ₗ hf.linearInv)
        BB.grading.piece BB.grading.piece 0 := by
      simpa only [add_zero] using f.isHomogeneous_linearPart.comp hf.isHomogeneous_linearInv
    exact LinearMap.IsHomogeneous.sub
      (by
        simpa only [zero_add, LinearMap.comp_assoc] using
          BB.isHomogeneous_cohomologyContraction_homotopy.comp hRf)
      BB.isHomogeneous_cohomologyContraction_homotopy
  linearPart_comp_inv_sub_id := hf.linearPart_comp_linearInv_sub_id

/-- Over a field, every `A∞` quasi-isomorphism `f : AA ⟶ BB` admits an `A∞` homotopy inverse
`BB ⟶ AA`. -/
noncomputable def IsQuasiIso.homotopyInverse {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    AInfinityHom BB AA :=
  hf.linearHomotopyInverse.homotopyInverse

/-- The left `A∞` homotopy `hf.homotopyInverse ∘ f ⇒ id AA` of a quasi-isomorphism over a field. -/
noncomputable def IsQuasiIso.leftHomotopy {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (hf.homotopyInverse.comp f) (AInfinityHom.id AA) :=
  hf.linearHomotopyInverse.leftHomotopyLift

/-- The right `A∞` homotopy `f ∘ hf.homotopyInverse ⇒ id BB` of a quasi-isomorphism over a field. -/
noncomputable def IsQuasiIso.rightHomotopy {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    Homotopy (f.comp hf.homotopyInverse) (AInfinityHom.id BB) :=
  hf.linearHomotopyInverse.rightHomotopyLift

/-- **Whitehead's theorem for `A∞` algebras over a field**: every `A∞` quasi-isomorphism is an `A∞`
homotopy equivalence. -/
theorem IsQuasiIso.isHomotopyEquiv {f : AInfinityHom AA BB} (hf : f.IsQuasiIso) :
    f.IsHomotopyEquiv :=
  hf.linearHomotopyInverse.isHomotopyEquiv

/-- The lifted `A∞` homotopy inverse of a quasi-isomorphism over a field is itself a homotopy
equivalence. -/
theorem IsQuasiIso.isHomotopyEquiv_homotopyInverse {f : AInfinityHom AA BB}
    (hf : f.IsQuasiIso) : hf.homotopyInverse.IsHomotopyEquiv :=
  hf.linearHomotopyInverse.isHomotopyEquiv_homotopyInverse

/-- Over a field, an `A∞` morphism is a homotopy equivalence if and only if it is a
quasi-isomorphism. -/
theorem isHomotopyEquiv_iff_isQuasiIso (f : AInfinityHom AA BB) :
    f.IsHomotopyEquiv ↔ f.IsQuasiIso :=
  ⟨IsHomotopyEquiv.isQuasiIso, IsQuasiIso.isHomotopyEquiv⟩

end Field

end AInfinityHom

/-! ### Homotopy equivalence of homological perturbation transfer -/

namespace AInfinityAlgebra

section Transfer

universe uH

variable {R : Type uR} {A : Type uA} {H : Type uH} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H ℤ} {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

/-- A graded special contraction supplies an explicit linear chain-homotopy inverse to the
transferred `A∞` inclusion. -/
noncomputable def transferInclusionLinearHomotopyInverse :
    (𝒜.transferInclusion c hh hincl hproj).LinearHomotopyInverse where
  inv := c.proj
  isHomogeneous_inv := by rwa [transfer_grading]
  differential_comp_inv := by rw [differential_transfer, c.proj_comp_dM]
  leftHomotopy := 0
  isHomogeneous_leftHomotopy := LinearMap.isHomogeneous_zero _ _ _
  inv_comp_linearPart_sub_id := by
    rw [linearPart_transferInclusion, c.proj_comp_incl, sub_self, LinearMap.comp_zero,
      LinearMap.zero_comp, add_zero]
  rightHomotopy := -c.homotopy
  isHomogeneous_rightHomotopy := hh.neg
  linearPart_comp_inv_sub_id := by
    rw [linearPart_transferInclusion, LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add,
      c.dM_comp_homotopy_add_homotopy_comp_dM, neg_sub]

/-- A graded special contraction supplies an explicit linear chain-homotopy inverse to the
transferred `A∞` projection. -/
noncomputable def transferProjectionLinearHomotopyInverse :
    (𝒜.transferProjection c hh hincl hproj).LinearHomotopyInverse where
  inv := c.incl
  isHomogeneous_inv := by rwa [transfer_grading]
  differential_comp_inv := by rw [differential_transfer, c.dM_comp_incl]
  leftHomotopy := -c.homotopy
  isHomogeneous_leftHomotopy := hh.neg
  inv_comp_linearPart_sub_id := by
    rw [linearPart_transferProjection, LinearMap.comp_neg, LinearMap.neg_comp, ← neg_add,
      c.dM_comp_homotopy_add_homotopy_comp_dM, neg_sub]
  rightHomotopy := 0
  isHomogeneous_rightHomotopy := LinearMap.isHomogeneous_zero _ _ _
  linearPart_comp_inv_sub_id := by
    rw [linearPart_transferProjection, c.proj_comp_incl, sub_self, LinearMap.comp_zero,
      LinearMap.zero_comp, add_zero]

/-- Over any commutative ring, the transferred `A∞` inclusion of a graded special contraction is an
`A∞` homotopy equivalence. -/
theorem isHomotopyEquiv_transferInclusion :
    (𝒜.transferInclusion c hh hincl hproj).IsHomotopyEquiv :=
  (𝒜.transferInclusionLinearHomotopyInverse c hh hincl hproj).isHomotopyEquiv

/-- Over any commutative ring, the transferred `A∞` projection of a graded special contraction is
an `A∞` homotopy equivalence. -/
theorem isHomotopyEquiv_transferProjection :
    (𝒜.transferProjection c hh hincl hproj).IsHomotopyEquiv :=
  (𝒜.transferProjectionLinearHomotopyInverse c hh hincl hproj).isHomotopyEquiv

end Transfer

section MinimalModel

universe uK

variable {K : Type uK} {A : Type uA} [Field K] [AddCommGroup A] [Module K A]
  (𝒜 : AInfinityAlgebra K A)

/-- Over a field, the minimal-model inclusion `minimalModel ⟶ 𝒜` is an `A∞` homotopy equivalence. -/
theorem isHomotopyEquiv_minimalModelInclusion : 𝒜.minimalModelInclusion.IsHomotopyEquiv :=
  𝒜.isQuasiIso_minimalModelInclusion.isHomotopyEquiv

/-- Over a field, the minimal-model projection `𝒜 ⟶ minimalModel` is an `A∞` homotopy
equivalence. -/
theorem isHomotopyEquiv_minimalModelProjection : 𝒜.minimalModelProjection.IsHomotopyEquiv :=
  𝒜.isQuasiIso_minimalModelProjection.isHomotopyEquiv

end MinimalModel

end AInfinityAlgebra

end TauCeti
