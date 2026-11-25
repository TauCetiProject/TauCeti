/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.RegularEpi
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

/-- The map of representable sheaves induced by a morphism `q : U ⟶ M` whose singleton sieve is
`J`-covering is `J`-locally surjective: every `T`-point of `M` lifts to `U` on a covering sieve
of `T`. -/
theorem isLocallySurjective_uliftYoneda_map_of_mem [J.Subcanonical] {U M : C} {q : U ⟶ M}
    (hq : Sieve.generate (Presieve.singleton q) ∈ J M) :
    Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q) where
  imageSieve_mem {T} x := by
    refine J.superset_covering ?_ (J.pullback_stable x.down hq)
    rintro T' g ⟨W, a, b, ⟨⟩, hab⟩
    exact ⟨ULift.up a, by
      change ULift.up (a ≫ q) = ULift.up (g ≫ x.down)
      rw [hab]⟩

/-- An invariant map `q : U ⟶ M` induces an invariant map `h_U ⟶ h_M` of representable sheaves. -/
theorem quotientSheaf.uliftYoneda_map_condition [J.Subcanonical] {R U M : C} {s t : R ⟶ U}
    {q : U ⟶ M} (hq : t ≫ q = s ≫ q) :
    J.uliftYoneda.{w}.map t ≫ J.uliftYoneda.{w}.map q =
      J.uliftYoneda.{w}.map s ≫ J.uliftYoneda.{w}.map q := by
  rw [← Functor.map_comp, ← Functor.map_comp, hq]

variable [HasSheafify J (Type (max v w))] [J.Subcanonical] {R U M : C} {s t : R ⟶ U}
  {q : U ⟶ M}

variable (J) in
/-- The comparison map `h_R ⟶ h_U ×_{h_M} h_U` of a pre-relation `(t, s)` with an invariant map
`q : U ⟶ M`, the pair `(h t, h s)` into the kernel pair of `h q`. -/
noncomputable abbrev quotientSheaf.toKernelPair (hq : t ≫ q = s ≫ q) :
    J.uliftYoneda.{w}.obj R ⟶
      pullback (J.uliftYoneda.{w}.map q) (J.uliftYoneda.{w}.map q) :=
  pullback.lift (J.uliftYoneda.{w}.map t) (J.uliftYoneda.{w}.map s)
    (by rw [← Functor.map_comp, ← Functor.map_comp, hq])

/-- **Stacks, Lemma 39.20.3 (03C5).** Let `q : U ⟶ M` be invariant for the pre-relation `(t, s)`.
If `h_U ⟶ h_M` and `h_R ⟶ h_U ×_{h_M} h_U` are `J`-locally surjective, then the factorisation
`U/R ⟶ h_M` of `q` through the quotient sheaf is an isomorphism. -/
theorem quotientSheaf.isIso_desc_of_isLocallySurjective (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : Sheaf.IsLocallySurjective (quotientSheaf.toKernelPair.{w} J hq)) :
    IsIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
      (quotientSheaf.uliftYoneda_map_condition hq)) := by
  have := IsRegularEpiCategory.regularEpiOfEpi (J.uliftYoneda.{w}.map q)
  have hπ : ∀ {Z : Sheaf J (Type (max v w))} (g₁ g₂ : Z ⟶ J.uliftYoneda.{w}.obj U),
      g₁ ≫ J.uliftYoneda.{w}.map q = g₂ ≫ J.uliftYoneda.{w}.map q →
        g₁ ≫ quotientSheaf.π J s t = g₂ ≫ quotientSheaf.π J s t := by
    intro Z g₁ g₂ h
    have key : pullback.fst (J.uliftYoneda.{w}.map q) (J.uliftYoneda.{w}.map q) ≫
        quotientSheaf.π J s t =
          pullback.snd (J.uliftYoneda.{w}.map q) (J.uliftYoneda.{w}.map q) ≫
            quotientSheaf.π J s t := by
      rw [← cancel_epi (quotientSheaf.toKernelPair.{w} J hq), pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, quotientSheaf.condition]
    calc g₁ ≫ quotientSheaf.π J s t
        = pullback.lift g₁ g₂ h ≫ pullback.fst _ _ ≫ quotientSheaf.π J s t := by
          rw [pullback.lift_fst_assoc]
      _ = pullback.lift g₁ g₂ h ≫ pullback.snd _ _ ≫ quotientSheaf.π J s t := by rw [key]
      _ = g₂ ≫ quotientSheaf.π J s t := by rw [pullback.lift_snd_assoc]
  let ψ := EffectiveEpi.desc (J.uliftYoneda.{w}.map q) (quotientSheaf.π J s t) hπ
  have hψ : J.uliftYoneda.{w}.map q ≫ ψ = quotientSheaf.π J s t := EffectiveEpi.fac _ _ _
  refine ⟨ψ, quotientSheaf.hom_ext ?_, ?_⟩
  · rw [quotientSheaf.π_desc_assoc, hψ, Category.comp_id]
  · rw [← cancel_epi (J.uliftYoneda.{w}.map q), reassoc_of% hψ, quotientSheaf.π_desc,
      Category.comp_id]

/-- **Stacks, Lemma 39.20.3 (03C5).** For an invariant map `q : U ⟶ M` such that `h_U ⟶ h_M` and
`h_R ⟶ h_U ×_{h_M} h_U` are `J`-locally surjective, the quotient sheaf `U/R` is the representable
sheaf `h_M`. -/
@[expose] noncomputable def quotientSheaf.isoOfIsLocallySurjective (hq : t ≫ q = s ≫ q)
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
        (quotientSheaf.uliftYoneda_map_condition hq) :=
  rfl

/-- The projection onto the quotient sheaf, followed by `U/R ≅ h_M`, is the map `h q`. -/
@[reassoc]
theorem quotientSheaf.π_isoOfIsLocallySurjective_hom (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : Sheaf.IsLocallySurjective (quotientSheaf.toKernelPair.{w} J hq)) :
    quotientSheaf.π J s t ≫ (quotientSheaf.isoOfIsLocallySurjective hq hU hR).hom =
      J.uliftYoneda.{w}.map q :=
  quotientSheaf.π_desc _ _

variable (q) in
/-- The quotient sheaf of the kernel pair `U ×_M U ⇉ U` of a morphism `q : U ⟶ M` whose singleton
sieve is `J`-covering is the representable sheaf `h_M`: the factorisation of `q` through it is an
isomorphism. -/
theorem quotientSheaf.isIso_desc_kernelPair [HasPullback q q]
    (hq : Sieve.generate (Presieve.singleton q) ∈ J M) :
    IsIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
      (quotientSheaf.uliftYoneda_map_condition (pullback.condition (f := q) (g := q)))) := by
  refine quotientSheaf.isIso_desc_of_isLocallySurjective pullback.condition
    (isLocallySurjective_uliftYoneda_map_of_mem hq) ?_
  have : quotientSheaf.toKernelPair.{w} J (pullback.condition (f := q) (g := q)) =
      pullbackComparison J.uliftYoneda.{w} q q := by
    ext1 <;> simp
  rw [this]
  infer_instance

end TauCeti.CategoryTheory
