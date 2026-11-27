/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import TauCeti.CategoryTheory.Sites.Canonical
public import TauCeti.CategoryTheory.Sites.QuotientSheaf

/-!
# Representability of the quotient sheaf

Let `J` be a subcanonical Grothendieck topology on a category `C`, let `s t : R ⟶ U` be a
pre-relation on `U`, and let `q : U ⟶ M` be invariant, `t ≫ q = s ≫ q`. If `h_U ⟶ h_M` is
`J`-locally surjective and `h_R ⟶ h_U ×_{h_M} h_U` is `J`-locally surjective, then the
factorisation `U/R ⟶ h_M` of `q` through the quotient sheaf is an isomorphism (for schemes and the
fppf topology, Stacks, Lemma 39.20.3 (03C5)).

## Main results

* `TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_isLocallySurjective`: under these
  hypotheses, `quotientSheaf.desc (h q) : U/R ⟶ h_M` is an isomorphism.
* `TauCeti.CategoryTheory.quotientSheaf.isoOfIsLocallySurjective`: the resulting isomorphism
  `U/R ≅ h_M`.
* `TauCeti.CategoryTheory.quotientSheaf.isIso_desc_kernelPair`: for `q` whose singleton sieve
  covers `M`, the quotient sheaf of the kernel pair `U ×_M U ⇉ U` is `h_M`.
* `TauCeti.CategoryTheory.quotientSheaf.exists_comp_eq_id_of_isSheaf`: if `U/R ≅ h_M` through
  `q` and the presheaf quotient is already a sheaf, then `q` has a section; so for `q` without a
  section the presheaf quotient is not a sheaf.
* `TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_epi`: if `p : h_U ⟶ F` is an epimorphism to
  a `J`-sheaf and `π : h_U ⟶ U/R` coequalises the kernel pair of `p`, then
  `quotientSheaf.desc p : U/R ⟶ F` is an isomorphism.
* `TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_isKernelPair`: if `p : h_U ⟶ F` is an
  epimorphism to a `J`-sheaf with kernel pair `h_R ⇉ h_U`, then the factorisation `U/R ⟶ F` of `p`
  through the quotient sheaf is an isomorphism.

## Implementation notes

The proof is categorical instead of the local argument of Stacks, Lemma 39.20.3. Since
`Sheaf J (Type _)` is a regular epi category, the epimorphism `h q : h_U ⟶ h_M` is effective, so it
is the coequaliser of its kernel pair `h_U ×_{h_M} h_U ⇉ h_U`. As `h_R ⟶ h_U ×_{h_M} h_U` is an
epimorphism, the projection `π : h_U ⟶ U/R`, which coequalises `h_R ⇉ h_U`, also coequalises the
kernel pair, and so descends along `h q`; the descended map is the inverse of
`quotientSheaf.desc (h q)`.

## References

* [Stacks Project, Lemma 39.20.3](https://stacks.math.columbia.edu/tag/03C5)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [J.Subcanonical] {R U M : C} {s t : R ⟶ U} {q : U ⟶ M}

/-- An invariant map `q : U ⟶ M` induces an invariant map `h_U ⟶ h_M` of representable sheaves. -/
theorem quotientSheaf.uliftYoneda_map_condition (hq : t ≫ q = s ≫ q) :
    J.uliftYoneda.{w}.map t ≫ J.uliftYoneda.{w}.map q =
      J.uliftYoneda.{w}.map s ≫ J.uliftYoneda.{w}.map q := by
  rw [← Functor.map_comp, ← Functor.map_comp, hq]

variable (J) in
/-- The comparison map `h_R ⟶ h_U ×_{h_M} h_U` of a pre-relation `(t, s)` with an invariant map
`q : U ⟶ M`, the pair `(h t, h s)` into the kernel pair of `h q`. -/
noncomputable def quotientSheaf.toKernelPair (hq : t ≫ q = s ≫ q) :
    J.uliftYoneda.{w}.obj R ⟶
      pullback (J.uliftYoneda.{w}.map q) (J.uliftYoneda.{w}.map q) :=
  pullback.lift (J.uliftYoneda.{w}.map t) (J.uliftYoneda.{w}.map s)
    (quotientSheaf.uliftYoneda_map_condition hq)

/-- The first component of `h_R ⟶ h_U ×_{h_M} h_U` is `h t`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.toKernelPair_fst (hq : t ≫ q = s ≫ q) :
    quotientSheaf.toKernelPair.{w} J hq ≫ pullback.fst _ _ = J.uliftYoneda.{w}.map t :=
  pullback.lift_fst _ _ _

/-- The second component of `h_R ⟶ h_U ×_{h_M} h_U` is `h s`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.toKernelPair_snd (hq : t ≫ q = s ≫ q) :
    quotientSheaf.toKernelPair.{w} J hq ≫ pullback.snd _ _ = J.uliftYoneda.{w}.map s :=
  pullback.lift_snd _ _ _

variable [HasSheafify J (Type (max v w))]

/-- If `p : h_U ⟶ F` is an epimorphism to a `J`-sheaf and the projection `π : h_U ⟶ U/R`
coequalises the kernel pair `h_U ×_F h_U ⇉ h_U` of `p`, then the factorisation `U/R ⟶ F` of `p`
through the quotient sheaf is an isomorphism. -/
theorem quotientSheaf.isIso_desc_of_epi {F : Sheaf J (Type (max v w))}
    (p : J.uliftYoneda.{w}.obj U ⟶ F) [Epi p]
    (hp : J.uliftYoneda.{w}.map t ≫ p = J.uliftYoneda.{w}.map s ≫ p)
    (hπ : pullback.fst p p ≫ quotientSheaf.π J s t = pullback.snd p p ≫ quotientSheaf.π J s t) :
    IsIso (quotientSheaf.desc p hp) := by
  have := IsRegularEpiCategory.regularEpiOfEpi p
  have hc := isColimitCoforkOfEffectiveEpi p _ (pullback.isLimit _ _)
  let ψ := Cofork.IsColimit.desc hc (quotientSheaf.π J s t) hπ
  have hψ : p ≫ ψ = quotientSheaf.π J s t := Cofork.IsColimit.π_desc hc
  refine ⟨ψ, quotientSheaf.hom_ext ?_, ?_⟩
  · rw [quotientSheaf.π_desc_assoc, hψ, Category.comp_id]
  · rw [← cancel_epi p, reassoc_of% hψ, quotientSheaf.π_desc, Category.comp_id]

/-- If `p : h_U ⟶ F` is an epimorphism to a `J`-sheaf whose kernel pair is `h_R ⇉ h_U`, then the
factorisation `U/R ⟶ F` of `p` through the quotient sheaf is an isomorphism. -/
theorem quotientSheaf.isIso_desc_of_isKernelPair {F : Sheaf J (Type (max v w))}
    (p : J.uliftYoneda.{w}.obj U ⟶ F) [Epi p]
    (hk : IsKernelPair p (J.uliftYoneda.{w}.map t) (J.uliftYoneda.{w}.map s)) :
    IsIso (quotientSheaf.desc p hk.w) := by
  refine quotientSheaf.isIso_desc_of_epi p hk.w ?_
  rw [← hk.isoPullback_inv_fst, ← hk.isoPullback_inv_snd, Category.assoc, Category.assoc,
    quotientSheaf.condition]

/-- **Stacks, Lemma 39.20.3 (03C5).** Let `q : U ⟶ M` be invariant for the pre-relation `(t, s)`.
If `h_U ⟶ h_M` and `h_R ⟶ h_U ×_{h_M} h_U` are `J`-locally surjective, then the factorisation
`U/R ⟶ h_M` of `q` through the quotient sheaf is an isomorphism. -/
theorem quotientSheaf.isIso_desc_of_isLocallySurjective (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : Sheaf.IsLocallySurjective (quotientSheaf.toKernelPair.{w} J hq)) :
    IsIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
      (quotientSheaf.uliftYoneda_map_condition hq)) := by
  refine quotientSheaf.isIso_desc_of_epi _ _ ?_
  rw [← cancel_epi (quotientSheaf.toKernelPair.{w} J hq), quotientSheaf.toKernelPair_fst_assoc,
    quotientSheaf.toKernelPair_snd_assoc, quotientSheaf.condition]

/-- **Stacks, Lemma 39.20.3 (03C5).** For an invariant map `q : U ⟶ M` such that `h_U ⟶ h_M` and
`h_R ⟶ h_U ×_{h_M} h_U` are `J`-locally surjective, the quotient sheaf `U/R` is the representable
sheaf `h_M`. -/
noncomputable def quotientSheaf.isoOfIsLocallySurjective (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : Sheaf.IsLocallySurjective (quotientSheaf.toKernelPair.{w} J hq)) :
    quotientSheaf.{w} J s t ≅ J.uliftYoneda.{w}.obj M :=
  have := quotientSheaf.isIso_desc_of_isLocallySurjective hq hU hR
  asIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
    (quotientSheaf.uliftYoneda_map_condition hq))

/-- The isomorphism `U/R ≅ h_M` is the factorisation of `q` through the quotient sheaf. -/
@[simp]
theorem quotientSheaf.isoOfIsLocallySurjective_hom (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : Sheaf.IsLocallySurjective (quotientSheaf.toKernelPair.{w} J hq)) :
    (quotientSheaf.isoOfIsLocallySurjective hq hU hR).hom =
      quotientSheaf.desc (J.uliftYoneda.{w}.map q)
        (quotientSheaf.uliftYoneda_map_condition hq) := by
  rfl

/-- The projection onto the quotient sheaf, followed by `U/R ≅ h_M`, is the map `h q`. -/
@[reassoc]
theorem quotientSheaf.π_isoOfIsLocallySurjective_hom (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : Sheaf.IsLocallySurjective (quotientSheaf.toKernelPair.{w} J hq)) :
    quotientSheaf.π J s t ≫ (quotientSheaf.isoOfIsLocallySurjective hq hU hR).hom =
      J.uliftYoneda.{w}.map q :=
  quotientSheaf.π_desc _ _

/-- The map `h q : h_U ⟶ h_M`, followed by the inverse of `U/R ≅ h_M`, is the projection onto the
quotient sheaf. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.uliftYoneda_map_isoOfIsLocallySurjective_inv (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : Sheaf.IsLocallySurjective (quotientSheaf.toKernelPair.{w} J hq)) :
    J.uliftYoneda.{w}.map q ≫ (quotientSheaf.isoOfIsLocallySurjective hq hU hR).inv =
      quotientSheaf.π J s t :=
  (Iso.comp_inv_eq _).2 (quotientSheaf.π_isoOfIsLocallySurjective_hom hq hU hR).symm

/-- **A presheaf quotient that is already a sheaf.** Let `q : U ⟶ M` be invariant for the
pre-relation `(t, s)`, with factorisation `U/R ⟶ h_M` through the quotient sheaf an isomorphism.
If the presheaf quotient `T ↦ U(T)/R(T)` is a `J`-sheaf, then it is its sheafification `U/R`, so
its section over `M` lying over the identity is the class of a section of `q`. Contrapositively,
if `q` has no section, the presheaf quotient is not a `J`-sheaf. -/
theorem quotientSheaf.exists_comp_eq_id_of_isSheaf (hq : t ≫ q = s ≫ q)
    [IsIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
      (quotientSheaf.uliftYoneda_map_condition hq))]
    (hP : Presheaf.IsSheaf J (quotientPresheaf s t ⋙ uliftFunctor.{w})) :
    ∃ a : M ⟶ U, a ≫ q = 𝟙 M := by
  have := isIso_toSheafify J hP
  let D := quotientPresheaf.uliftDesc.{w} (J.uliftYoneda.{w}.map q).hom
    (congrArg (·.hom) (quotientSheaf.uliftYoneda_map_condition.{w} (J := J) hq))
  have hD : D = toSheafify J _ ≫ (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
      (quotientSheaf.uliftYoneda_map_condition hq)).hom := by
    rw [quotientSheaf.desc_def, ObjectProperty.homMk_hom, toSheafify_sheafifyLift]
  have : IsIso D := by rw [hD]; infer_instance
  obtain ⟨⟨z⟩, hz⟩ := ((isIso_iff_bijective _).1
    (inferInstance : IsIso (D.app (op M)))).2 (J.uliftYonedaEquiv (𝟙 (J.uliftYoneda.{w}.obj M)))
  obtain ⟨a, rfl⟩ := quotientPresheaf.π_app_surjective _ _ _ z
  refine ⟨a, (GrothendieckTopology.fullyFaithfulUliftYoneda.{w} J).map_injective ?_⟩
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  apply J.uliftYonedaEquiv.injective
  rw [← hz, GrothendieckTopology.uliftYonedaEquiv_comp,
    GrothendieckTopology.uliftYonedaEquiv_uliftYoneda_map]
  exact (quotientPresheaf.uliftDesc_app_apply _ _ _ a).symm

variable (q) in
/-- The quotient sheaf of the kernel pair `U ×_M U ⇉ U` of a morphism `q : U ⟶ M` whose singleton
sieve is `J`-covering is the representable sheaf `h_M`: the factorisation of `q` through it is an
isomorphism. -/
theorem quotientSheaf.isIso_desc_kernelPair [HasPullback q q]
    (hq : Sieve.generate (Presieve.singleton q) ∈ J M) :
    IsIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
      (quotientSheaf.uliftYoneda_map_condition (pullback.condition (f := q) (g := q)))) := by
  refine quotientSheaf.isIso_desc_of_isLocallySurjective pullback.condition
    (Sheaf.isLocallySurjective_uliftYoneda_map_of_mem hq) ?_
  have : quotientSheaf.toKernelPair.{w} J (pullback.condition (f := q) (g := q)) =
      pullbackComparison J.uliftYoneda.{w} q q := by
    ext1 <;> simp
  rw [this]
  infer_instance

end TauCeti.CategoryTheory
