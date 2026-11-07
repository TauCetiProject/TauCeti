/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.OrthogonalLimits
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Abelian
public import TauCeti.Algebra.Homology.Curved.Module.Right.Cone.Triangulated
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Basic
public import TauCeti.Algebra.Homology.Curved.Module.Right.SecondKind
public import TauCeti.CategoryTheory.Triangulated.Orthogonal

/-!
# Graded-projective curved modules and contraacyclic objects

A curved right module is **graded-projective** when its underlying graded right module, obtained
by forgetting the differential, is a projective object of the abelian category of graded right
modules. In the curved homotopy category such a module `P` has no nonzero morphisms to a
contraacyclic module: `Hom(P, X) = 0` for every contraacyclic `X`.

The proof follows Positselski. Let `0 ⟶ K ⟶ L ⟶ M ⟶ 0` be a short exact sequence of curved
modules with maps `f` and `g`. Its totalization is the cone of the induced map
`cone(f) ⟶ M`. Composition with this map is a bijection from homotopy classes of maps
`P ⟶ cone(f)` to homotopy classes of maps `P ⟶ M`:

* a closed map `u : P ⟶ M` lifts to a right-linear map `u' : P ⟶ L` of degree zero, since `P` is
  graded-projective; the commutator `d u' - u' d` is killed by `g`, so it is `f ∘ v` for a map `v`
  of degree one, and `(-v, u')` is a closed map to the cone lifting `u`;
* if the composite of a closed map `φ : P ⟶ cone(f)` with `cone(f) ⟶ M` is the boundary of an
  odd homotopy `k`, a lift of `k` to `L` and the factorization through `f` of the resulting
  correction of the second component of `φ` assemble to an odd homotopy contracting `φ`.

Since graded-projective modules are stable under shifts, the long exact sequence of
`Hom(P, -)` on the distinguished cone triangle shows that totalizations are right orthogonal to
graded-projective modules. The right orthogonal of a shift-stable class is a triangulated
subcategory closed under products, so it contains the contraacyclic modules.

Consequently the localization functor to the contraderived category is bijective on morphisms
out of a graded-projective module. This is the full faithfulness in Positselski's graded-projective
model of the contraderived category; its essential surjectivity needs a further hypothesis on
countable products of projective graded modules and is not treated here.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.gradedProjective`: the curved modules whose underlying graded
  right module is projective.

## Main results

* `TauCeti.CurvedDGRightModuleCat.totalizations_le_rightOrthogonal_gradedProjective`:
  totalizations of short exact sequences are right orthogonal to graded-projective modules.
* `TauCeti.CurvedDGRightModuleCat.contraacyclic_le_rightOrthogonal_gradedProjective`:
  contraacyclic modules are right orthogonal to graded-projective modules.
* `TauCeti.CurvedDGRightModuleCat.ContraderivedCategory.map_bijective_of_gradedProjective`:
  morphisms out of a graded-projective module in the curved homotopy category are exactly the
  morphisms in the contraderived category.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.5.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6 and Theorem 7.9(b).
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-! ### Graded-projective curved modules -/

variable (R h) in
/-- The **graded-projective** curved right modules, as objects of the curved homotopy category:
those whose underlying graded right module is a projective object of the category of graded right
modules. -/
def gradedProjective :
    ObjectProperty (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  fun X ↦ Projective (toGradedModuleCat X.underlying)

/-- An object of the curved homotopy category is graded-projective when its underlying graded
right module is projective. -/
@[simp]
theorem gradedProjective_iff (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    gradedProjective R h X ↔ Projective (toGradedModuleCat X.underlying) :=
  Iff.rfl

/-- Shifts of graded-projective curved modules are graded-projective: the underlying graded
module of a cohomological shift is a grading shift. -/
instance : (gradedProjective R h).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun X hX ↦ (gradedProjective_iff _).2 <|
    have := (gradedProjective_iff X).1 hX
    Projective.of_iso ((closedShiftFunctorCompForgetDifferentialIso (h := h) n).app
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) X.underlying)).symm
      (GradedModuleCat.projective_shiftObj (toGradedModuleCat X.underlying) (-n))⟩

/-! ### Lifting and factoring homogeneous maps -/

section Homogeneous

variable {M N : CurvedDGRightModuleCat.{u, u, u} h}

variable {P : CurvedDGRightModuleCat.{u, u, u} h}

/-- Along a surjective closed map, a right-linear map of degree `p` out of a graded-projective
curved module lifts to a map of degree `p`. -/
private theorem exists_comp_eq_of_surjective [Projective (toGradedModuleCat P)]
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)
    (hg : Function.Surjective (closedHom g)) {p : ℤ}
    (u : dgRightModuleCochains (R := R) (A := A) (ℳ := P.grading) (ℳN := N.grading) p) :
    ∃ v : dgRightModuleCochains (R := R) (A := A) (ℳ := P.grading) (ℳN := M.grading) p,
      ∀ x, closedHom g (v.1 x) = u.1 x := by
  have : Epi ((forgetDifferential (h := h)).map g) := (GradedModuleCat.epi_iff_surjective _).2 hg
  obtain ⟨v, hv, hvu⟩ := GradedModuleCat.exists_isHomogeneous_comp_eq_of_epi
    (toGradedModuleCat P) ((forgetDifferential (h := h)).map g) (p := p) u.1
    ((isHomogeneous_toGradedModuleCat_iff _).2 u.2)
  exact ⟨⟨v, (isHomogeneous_toGradedModuleCat_iff _).1 hv⟩,
    fun x ↦ congrArg (fun l : P →ₗ[Aᵐᵒᵖ] N ↦ l x) hvu⟩

/-- A right-linear map of degree `p` whose values lie in the range of an injective closed map `f`
factors through `f` by a map of degree `p`. -/
private theorem exists_comp_eq_of_injective
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)
    (hf : Function.Injective (closedHom f)) {p : ℤ}
    (χ : dgRightModuleCochains (R := R) (A := A) (ℳ := P.grading) (ℳN := N.grading) p)
    (hχ : ∀ x, χ.1 x ∈ LinearMap.range (closedHom f)) :
    ∃ a : dgRightModuleCochains (R := R) (A := A) (ℳ := P.grading) (ℳN := M.grading) p,
      ∀ x, closedHom f (a.1 x) = χ.1 x := by
  obtain ⟨a, ha, hfa⟩ := InternalGrading.exists_isHomogeneous_comp_eq_of_injective
    (toGradedModuleCat M).grading (toGradedModuleCat N).grading (toGradedModuleCat P).grading hf
    ((forgetDifferential (h := h)).map f).isHomogeneous
    ((isHomogeneous_toGradedModuleCat_iff _).2 χ.2)
    (by rintro _ ⟨x, rfl⟩; exact hχ x)
  exact ⟨⟨a, (isHomogeneous_toGradedModuleCat_iff _).1 ha⟩,
    fun x ↦ congrArg (fun l : P →ₗ[Aᵐᵒᵖ] N ↦ l x) hfa⟩

end Homogeneous

/-! ### Maps from graded-projective modules into the cone of the first map -/

section Cone

variable {K L M : CurvedDGRightModuleCat.{u, u, u} h}
  {f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) K ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) L}
  {g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) L ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M}
  (hfg : f ≫ g = 0) (hf : Function.Injective (closedHom f))
  (hg : Function.Surjective (closedHom g)) (hex : Function.Exact (closedHom f) (closedHom g))
  {P : CurvedDGRightModuleCat.{u, u, u} h} [Projective (toGradedModuleCat P)]
include hf hg hex

/-- For a short exact sequence `K ⟶ L ⟶ M` of curved modules, every closed map from a
graded-projective module to `M` lifts to a closed map into the cone of `K ⟶ L`. -/
private theorem exists_comp_coneDesc_eq
    (u : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) :
    ∃ φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f),
      φ ≫ coneDesc f g hfg = u := by
  -- Lift `u` to a right-linear map `u' : P ⟶ L` of degree zero.
  obtain ⟨u', hu'⟩ := exists_comp_eq_of_surjective g hg (p := 0)
    ⟨closedHom u, (isHomogeneous_toGradedModuleCat_iff _).1
      ((forgetDifferential (h := h)).map u).isHomogeneous⟩
  simp only at hu'
  -- Its commutator with the differentials is killed by `g`, so it factors through `f`.
  obtain ⟨δ, hδ⟩ : ∃ δ : dgRightModuleCochains (R := R) (A := A) (ℳ := P.grading)
      (ℳN := L.grading) (0 + 1),
      ∀ x, δ.1 x = L.differential (u'.1 x) - u'.1 (P.differential x) :=
    ⟨dgRightModuleCochains.curvedDifferential (hM := P.isCurvedDGRightModule)
      (hN := L.isCurvedDGRightModule) 0 u', fun x ↦ by
      rw [dgRightModuleCochains.curvedDifferential_apply, Int.negOnePow_zero, one_smul]⟩
  obtain ⟨v, hv⟩ := exists_comp_eq_of_injective f hf δ fun x ↦
    (hex _).1 (by
      rw [hδ, map_sub, ← differential_closedHom, hu', hu', differential_closedHom, sub_self])
  have hdv (x : P) : K.differential (v.1 x) = -v.1 (P.differential x) := by
    apply hf
    rw [← differential_closedHom, map_neg, hv, hv]
    simp only [hδ, map_sub, L.isCurvedDGRightModule.sq_eq, P.isCurvedDGRightModule.sq_eq,
      LinearMap.map_smul]
    abel
  -- The lift `x ↦ (-v x, u' x)`, computed on the cone's product carrier.
  have hφ₀ (x : P) : ((-v.1).prod u'.1 : P →ₗ[Aᵐᵒᵖ] cone f) x = (-v.1 x, u'.1 x) := rfl
  refine ⟨closedHomOf (M := P) (N := cone f) ((-v.1).prod u'.1) (fun p x hx ↦ ?_) (fun x ↦ ?_),
    closedHom_ext fun x ↦ ?_⟩
  · rw [cone_grading, hφ₀]
    exact ⟨(K.grading (p + 1)).neg_mem (by simpa using dgRightModuleCochains.map_mem v hx),
      by simpa using dgRightModuleCochains.map_mem u' hx⟩
  · rw [cone_differential_apply, hφ₀, hφ₀]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [map_neg, hdv, neg_neg]
    · dsimp only
      rw [map_neg, hv, hδ]
      abel
  · rw [closedHom_comp, closedHom_coneDesc, closedHom_closedHomOf, LinearMap.comp_apply,
      LinearMap.comp_apply, hφ₀, LinearMap.snd_apply, hu']

/-- For a short exact sequence `K ⟶ L ⟶ M` of curved modules, a closed map from a
graded-projective module to the cone of `K ⟶ L` is null-homotopic as soon as its composite with
the induced map to `M` is. -/
private theorem quotient_map_eq_zero_of_comp_coneDesc
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone f))
    (hφ : (dgClosedToHomotopy R).map (φ ≫ coneDesc f g hfg) = 0) :
    (dgClosedToHomotopy R).map φ = 0 := by
  rw [← (dgClosedToHomotopy R).map_zero, quotient_map_eq_iff_exists_homotopy] at hφ ⊢
  obtain ⟨k, hk⟩ := hφ
  -- Lift the odd homotopy `k` to `L`.
  obtain ⟨k', hk'⟩ := exists_comp_eq_of_surjective g hg k
  -- Correct the second component of `φ` by the boundary of the lift; the result factors
  -- through `f`.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : dgRightModuleCochains (R := R) (A := A) (ℳ := P.grading)
      (ℳN := L.grading) 0, ∀ x, ψ.1 x = (closedHom φ x).2 -
        (L.differential (k'.1 x) + k'.1 (P.differential x)) := by
    refine ⟨⟨(LinearMap.snd _ _ _).comp (closedHom φ) -
      (dgRightModuleCochains.curvedDifferential (hM := P.isCurvedDGRightModule)
        (hN := L.isCurvedDGRightModule) (-1) k').1, Submodule.sub_mem _ ?_ (by simp)⟩,
      fun x ↦ ?_⟩
    · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
      intro p x hx
      have := closedHom_mem φ hx
      rw [cone_grading] at this
      simpa using this.2
    · rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply,
        dgRightModuleCochains.curvedDifferential_neg_one_apply]
  obtain ⟨a, ha⟩ := exists_comp_eq_of_injective f hf ψ fun x ↦
    (hex _).1 (by
      have := hk x
      simp only [closedHom_comp, closedHom_coneDesc, LinearMap.comp_apply, closedHom_zero,
        LinearMap.zero_apply, sub_zero] at this
      rw [LinearMap.snd_apply] at this
      rw [hψ, map_sub, map_add, ← differential_closedHom, hk', hk', ← this]
      exact sub_self _)
  -- The closedness of `φ`, componentwise.
  have hφd (x : P) : closedHom f (closedHom φ x).1 =
      (closedHom φ (P.differential x)).2 - L.differential (closedHom φ x).2 := by
    have := congrArg Prod.snd (differential_closedHom φ x)
    rw [cone_differential_apply] at this
    dsimp only at this
    rw [← this]
    abel
  -- The contracting homotopy `x ↦ (a x, k' x)`, computed on the cone's product carrier.
  have hH (x : P) : (a.1.prod k'.1 : P →ₗ[Aᵐᵒᵖ] cone f) x = (a.1 x, k'.1 x) := rfl
  -- Addition on the cone's carrier is componentwise.
  have hadd (y z : cone f) : y + z = (y.1 + z.1, y.2 + z.2) := rfl
  refine ⟨⟨a.1.prod k'.1, ?_⟩, fun x ↦ ?_⟩
  · rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p x hx
    rw [LinearMap.restrictScalars_apply, hH, cone_grading, (by ring : p + -1 + 1 = p + 0)]
    exact ⟨dgRightModuleCochains.map_mem a hx, dgRightModuleCochains.map_mem k' hx⟩
  · rw [closedHom_zero, LinearMap.zero_apply, sub_zero, cone_differential_apply, hH, hH, hadd]
    refine Prod.ext (hf ?_) ?_
    · dsimp only
      rw [hφd, map_add, map_neg, ← differential_closedHom f, ha, ha]
      simp only [hψ, map_sub, map_add, L.isCurvedDGRightModule.sq_eq,
        P.isCurvedDGRightModule.sq_eq, LinearMap.map_smul]
      abel
    · dsimp only
      rw [ha, hψ]
      abel

/-- For a short exact sequence `K ⟶ L ⟶ M` of curved modules and a graded-projective module
`P`, composition with the induced map `cone(K ⟶ L) ⟶ M` is a bijection on morphisms out of `P`
in the curved homotopy category. -/
private theorem bijective_comp_coneDesc :
    Function.Bijective fun φ : DGHomotopyCategory.of R P ⟶
        (dgClosedToHomotopy R).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
          (cone f)) ↦
      φ ≫ (dgClosedToHomotopy R).map (coneDesc f g hfg) := by
  refine ⟨fun φ₁ φ₂ hφ ↦ ?_, fun β ↦ ?_⟩
  · dsimp only at hφ
    obtain ⟨φ, hφ'⟩ := (dgClosedToHomotopy R).map_surjective (φ₁ - φ₂)
    rw [← sub_eq_zero, ← hφ']
    refine quotient_map_eq_zero_of_comp_coneDesc hfg hf hg hex φ ?_
    rw [Functor.map_comp, hφ', Preadditive.sub_comp, hφ, sub_self]
  · obtain ⟨u, rfl⟩ := (dgClosedToHomotopy R).map_surjective β
    obtain ⟨φ, hφ⟩ := exists_comp_coneDesc_eq hfg hf hg hex u
    exact ⟨(dgClosedToHomotopy R).map φ, by dsimp only; rw [← Functor.map_comp, hφ]⟩

end Cone

section ShortExact

variable {S : ShortComplex
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
  (hS : S.ShortExact)
include hS

/-- For a graded-projective module `P` and a short exact sequence `K ⟶ L ⟶ M` of curved modules,
composition with the induced map `cone(K ⟶ L) ⟶ M` is a bijection on morphisms out of `P` in the
curved homotopy category. -/
private theorem bijective_comp_coneDesc_of_shortExact (P : CurvedDGRightModuleCat.{u, u, u} h)
    [Projective (toGradedModuleCat P)] :
    Function.Bijective fun φ : DGHomotopyCategory.of R P ⟶
        (dgClosedToHomotopy R).obj (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ)
          (cone S.f)) ↦
      φ ≫ (dgClosedToHomotopy R).map (coneDesc S.f S.g S.zero) :=
  have hS' := hS.map_of_exact (forgetDifferential (h := h))
  bijective_comp_coneDesc S.zero ((GradedModuleCat.mono_iff_injective _).1 hS'.mono_f)
    ((GradedModuleCat.epi_iff_surjective _).1 hS'.epi_g) (GradedModuleCat.exact_iff.1 hS'.exact)

end ShortExact

/-! ### Orthogonality -/

variable (R h) in
/-- **Totalizations are right orthogonal to graded-projective modules.** In the curved homotopy
category, every morphism from a graded-projective module to the totalization of a short exact
sequence of curved modules is zero. -/
theorem totalizations_le_rightOrthogonal_gradedProjective :
    totalizations R h ≤ (gradedProjective R h).rightOrthogonal := by
  refine (totalizations_le_iff _).2 fun S hS ↦ ?_
  rw [totalization_eq]
  exact (gradedProjective R h).rightOrthogonal_obj₃_of_bijective
    (coneTriangle (coneDesc S.f S.g S.zero)) (coneTriangle_distinguished _)
    fun K hK ↦
      have := (gradedProjective_iff K).1 hK
      bijective_comp_coneDesc_of_shortExact hS K.underlying

variable (R h) in
/-- **Contraacyclic modules are right orthogonal to graded-projective modules.** In the curved
homotopy category, every morphism from a graded-projective module to a contraacyclic module is
zero. -/
theorem contraacyclic_le_rightOrthogonal_gradedProjective :
    contraacyclic R h ≤ (gradedProjective R h).rightOrthogonal :=
  contraacyclic_le_iff.2 (totalizations_le_rightOrthogonal_gradedProjective R h)

/-- The localization functor to the contraderived category is bijective on morphisms out of a
graded-projective module. -/
theorem ContraderivedCategory.map_bijective_of_gradedProjective
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)} (hX : gradedProjective R h X)
    (Y : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    Function.Bijective ((ContraderivedCategory.Q R h).map : (X ⟶ Y) → _) :=
  ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated
    ((ObjectProperty.le_leftOrthogonal_iff_le_rightOrthogonal _ _).2
      (contraacyclic_le_rightOrthogonal_gradedProjective R h) X hX) _ Y

end TauCeti.CurvedDGRightModuleCat
