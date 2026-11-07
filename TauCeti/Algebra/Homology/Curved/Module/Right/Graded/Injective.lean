/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.OrthogonalLimits
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import TauCeti.Algebra.Category.GradedModuleCat.Injective
public import TauCeti.Algebra.Homology.Curved.Module.Right.SecondKind

/-!
# Graded-injective curved modules and coacyclic objects

A curved module is graded-injective if its underlying graded right module is injective.
Every map from a coacyclic curved module into a graded-injective curved module is zero in
the homotopy category. Thus localization to the coderived category is fully faithful on maps
into graded-injective modules. No finiteness hypothesis on injective dimensions is needed for
this orthogonality statement; such hypotheses enter the existence of injective replacements.

For a short exact sequence `K → L → M`, a map from its totalization to a graded-injective
module is contracted by extending its `K` component to `L` and descending the remaining
correction to `M`. The Hom differential squares to zero because the curvatures agree.
Closure under triangles and coproducts then gives the result for all coacyclic objects.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.5.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6 and Theorem 7.9(a).
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective`,
  for the dual grading-shift and orthogonal-localization pattern. The totalization contraction
  here is constructed directly.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- These categorical wrappers retain the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

variable (R h) in
/-- Curved modules whose underlying graded right module is injective, viewed as objects of
  the curved homotopy category. -/
def gradedInjective :
    ObjectProperty (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :=
  fun X ↦ Injective (toGradedModuleCat X.underlying)

/-- Graded injectivity means injectivity after forgetting the differential. -/
@[simp] theorem gradedInjective_iff
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) :
    gradedInjective R h X ↔ Injective (toGradedModuleCat X.underlying) := Iff.rfl

/-- Cohomological shifts preserve graded injectivity. -/
instance : (gradedInjective R h).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun X hX ↦ (gradedInjective_iff _).2 <|
    have := (gradedInjective_iff X).1 hX
    Injective.of_iso ((closedShiftFunctorCompForgetDifferentialIso (h := h) n).app
      (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) X.underlying)).symm
      (GradedModuleCat.injective_shiftObj (toGradedModuleCat X.underlying) (-n))⟩

section Totalization

variable {K L M I : CurvedDGRightModuleCat.{u, u, u} h}
  (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) K ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) L)
  (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) L ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)
  (hfg : f ≫ g = 0)

/-- The differential on the three components of a totalization. -/
private theorem totalization_differential (x : K) (y : L) (z : M) :
    (cone (coneDesc f g hfg)).differential ((x, y), z) =
      ((K.differential x, -closedHom f x - L.differential y),
        closedHom g y + M.differential z) := by
  rw [cone_differential_apply, cone_differential_apply, closedHom_coneDesc]
  -- Cone carriers have componentwise product operations; expose their projections here.
  change ((- -K.differential x, -(closedHom f x + L.differential y)),
    closedHom g y + M.differential z) = _
  simp only [neg_neg, neg_add, sub_eq_add_neg]

/-- The three homogeneous components of a closed map out of a totalization. -/
private theorem totalization_map_components
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone (coneDesc f g hfg)) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) I) :
    ∃ a : dgRightModuleCochains (R := R) (A := A) (ℳ := K.grading) (ℳN := I.grading) (-2),
      ∃ b : dgRightModuleCochains (R := R) (A := A) (ℳ := L.grading) (ℳN := I.grading) (-1),
      ∃ c : M →ₗ[Aᵐᵒᵖ] I,
        (∀ x y z, closedHom φ ((x, y), z) = a.1 x + b.1 y + c z) ∧
        (∀ x, I.differential (a.1 x) = a.1 (K.differential x) - b.1 (closedHom f x)) ∧
        (∀ y, I.differential (b.1 y) = -b.1 (L.differential y) + c (closedHom g y)) := by
  let F := closedHom φ
  let a : K →ₗ[Aᵐᵒᵖ] I := F.comp
    ((LinearMap.inl Aᵐᵒᵖ (cone f) M).comp (LinearMap.inl Aᵐᵒᵖ K L))
  let b : L →ₗ[Aᵐᵒᵖ] I := F.comp
    ((LinearMap.inl Aᵐᵒᵖ (cone f) M).comp (LinearMap.inr Aᵐᵒᵖ K L))
  let c : M →ₗ[Aᵐᵒᵖ] I := F.comp (LinearMap.inr Aᵐᵒᵖ (cone f) M)
  have ha_apply (x : K) : a x = F ((x, 0), 0) := rfl
  have hb_apply (y : L) : b y = F ((0, y), 0) := rfl
  have hc_apply (z : M) : c z = F ((0, 0), z) := rfl
  have hsplit (x : K) (y : L) (z : M) : F ((x, y), z) = a x + b y + c z := by
    rw [ha_apply, hb_apply, hc_apply]
    have hx : (((x, y), z) : (K × L) × M) =
        ((x, 0), 0) + ((0, y), 0) + ((0, 0), z) := by simp
    exact (congrArg F hx).trans ((F.map_add _ _).trans
      (congrArg (· + F ((0, 0), z)) (F.map_add _ _)))
  have ha : a ∈ dgRightModuleCochains (R := R) (A := A)
      (ℳ := K.grading) (ℳN := I.grading) (-2) := by
    rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p x hx
    exact closedHom_mem φ (p := p + -2) (x := ((x, 0), 0)) (by
      rw [cone_grading, cone_grading, show p + -2 + 1 + 1 = p by omega]
      exact ⟨⟨hx, Submodule.zero_mem _⟩, Submodule.zero_mem _⟩)
  have hb : b ∈ dgRightModuleCochains (R := R) (A := A)
      (ℳ := L.grading) (ℳN := I.grading) (-1) := by
    rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p x hx
    exact closedHom_mem φ (p := p + -1) (x := ((0, x), 0)) (by
      rw [cone_grading, cone_grading, show p + -1 + 1 = p by omega]
      exact ⟨⟨Submodule.zero_mem _, hx⟩, Submodule.zero_mem _⟩)
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, c, hsplit, fun x ↦ ?_, fun y ↦ ?_⟩
  · have hd := differential_closedHom φ ((x, 0), 0)
    rw [totalization_differential] at hd
    rw [ha_apply]
    exact hd.trans (by
      simp only [map_zero, sub_zero, add_zero]
      rw [hsplit, map_neg, map_zero, add_zero]
      exact (sub_eq_add_neg _ _).symm)
  · have hd := differential_closedHom φ ((0, y), 0)
    rw [totalization_differential] at hd
    rw [hb_apply]
    exact hd.trans (by
      simp only [map_zero, neg_zero, zero_sub, add_zero]
      rw [hsplit, map_zero, zero_add, map_neg])

variable (hS : (ShortComplex.mk f g hfg).ShortExact)
include hS

/-- A cochain killing the first map of a short exact sequence descends through its second
map, with its degree unchanged. -/
private theorem descend_cochain {p : ℤ}
    (b : dgRightModuleCochains (R := R) (A := A) (ℳ := L.grading) (ℳN := I.grading) p)
    (hb : ∀ x, b.1 (closedHom f x) = 0) :
    ∃ c : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := I.grading) p,
      ∀ x, c.1 (closedHom g x) = b.1 x := by
  let T := (ShortComplex.mk f g hfg).map (forgetDifferential (h := h))
  have hT : T.ShortExact := hS.map_of_exact _
  have := hT.epi_g
  let b' : toGradedModuleCat L ⟶ (toGradedModuleCat I).shiftObj (-p) :=
    GradedModuleCat.ofHom b.1
      ((mem_dgRightModuleCochains_iff_isHomogeneous_shiftObj b.1).1 b.2)
  have hz : T.f ≫ b' = 0 := GradedModuleCat.hom_ext (LinearMap.ext hb)
  let c := hT.exact.desc b' hz
  refine ⟨⟨c.hom, ?_⟩, fun x ↦ congrArg (fun a : T.X₂ ⟶ _ ↦ a.hom x)
    (hT.exact.g_desc b' hz)⟩
  exact (mem_dgRightModuleCochains_iff_isHomogeneous_shiftObj c.hom).2 c.isHomogeneous

variable [Injective (toGradedModuleCat I)]

/-- A homogeneous cochain into a graded-injective module extends across a monomorphism. -/
private theorem extend_cochain {p : ℤ}
    (a : dgRightModuleCochains (R := R) (A := A) (ℳ := K.grading) (ℳN := I.grading) p) :
    ∃ b : dgRightModuleCochains (R := R) (A := A) (ℳ := L.grading) (ℳN := I.grading) p,
      ∀ x, b.1 (closedHom f x) = a.1 x := by
  have : Mono ((forgetDifferential (h := h)).map f) :=
    (hS.map_of_exact (forgetDifferential (h := h))).mono_f
  obtain ⟨b, hb, hba⟩ := GradedModuleCat.exists_isHomogeneous_comp_eq_of_mono
    (toGradedModuleCat I) ((forgetDifferential (h := h)).map f) (p := p) a.1
    ((isHomogeneous_toGradedModuleCat_iff a.1).2 a.2)
  refine ⟨⟨b, ?_⟩, fun x ↦ congrArg (fun l ↦ l x) hba⟩
  exact (isHomogeneous_toGradedModuleCat_iff b).1 hb

/-- Maps from a short-exact totalization to a graded-injective module are null-homotopic. -/
private theorem totalization_map_eq_zero
    (φ : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone (coneDesc f g hfg)) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) I) :
    (dgClosedToHomotopy R).map φ = 0 := by
  obtain ⟨a, b, c, hsplit, hda, hdb⟩ := totalization_map_components f g hfg φ
  -- Extend the degree -2 component and correct the degree -1 component by its boundary.
  obtain ⟨e, he⟩ := extend_cochain f g hfg hS a
  let δe : dgRightModuleCochains (R := R) (A := A) (ℳ := L.grading) (ℳN := I.grading) (-1) :=
    dgRightModuleCochains.curvedDifferential
      (hM := L.isCurvedDGRightModule) (hN := I.isCurvedDGRightModule) (-2) e
  have hδe (x : L) : δe.1 x = I.differential (e.1 x) - e.1 (L.differential x) := by
    simpa only [show (-2 : ℤ).negOnePow = 1 from by decide, one_smul] using
      (dgRightModuleCochains.curvedDifferential_apply
        (hM := L.isCurvedDGRightModule) (hN := I.isCurvedDGRightModule) (-2) e x)
  obtain ⟨v, hv⟩ := descend_cochain f g hfg hS (b + δe) (fun x ↦ by
    simp only [Submodule.coe_add, LinearMap.add_apply, hδe]
    rw [he, differential_closedHom f, he, hda]
    abel)
  have hv' (x : L) : v.1 (closedHom g x) =
      b.1 x + I.differential (e.1 x) - e.1 (L.differential x) := by
    simpa only [Submodule.coe_add, LinearMap.add_apply, hδe, add_sub_assoc] using hv x
  -- The last component equation follows after precomposition with the surjection `g`.
  have hdv (x : M) : I.differential (v.1 x) + v.1 (M.differential x) = c x := by
    have hg : Function.Surjective (closedHom g) :=
      (GradedModuleCat.epi_iff_surjective _).1
        (hS.map_of_exact (forgetDifferential (h := h))).epi_g
    obtain ⟨y, rfl⟩ := hg x
    rw [differential_closedHom g, hv', hv']
    simp only [map_sub, map_add, I.isCurvedDGRightModule.sq_eq,
      L.isCurvedDGRightModule.sq_eq, LinearMap.map_smul, hdb]
    abel
  -- On `(K[2] × L[1]) × M` the contracting homotopy is `(x,y,z) ↦ -e(y) + v(z)`.
  let H : cone (coneDesc f g hfg) →ₗ[Aᵐᵒᵖ] I :=
    -(e.1.comp ((LinearMap.snd Aᵐᵒᵖ K L).comp (LinearMap.fst Aᵐᵒᵖ (cone f) M))) +
      v.1.comp (LinearMap.snd Aᵐᵒᵖ (cone f) M)
  have hH (x : cone (coneDesc f g hfg)) : H x = -e.1 x.1.2 + v.1 x.2 := rfl
  have hH_mem : H ∈ dgRightModuleCochains (R := R) (A := A)
      (ℳ := (cone (coneDesc f g hfg)).grading) (ℳN := I.grading) (-1) := by
    rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
    intro p x hx
    simp only [cone_grading] at hx
    rcases hx with ⟨⟨_, hy⟩, hz⟩
    rw [LinearMap.restrictScalars_apply, hH]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (by
      simpa only [add_assoc, Int.reduceAdd] using dgRightModuleCochains.map_mem e hy))
      (dgRightModuleCochains.map_mem v hz)
  rw [← (dgClosedToHomotopy R).map_zero, quotient_map_eq_iff_exists_homotopy]
  refine ⟨⟨H, hH_mem⟩, fun x ↦ ?_⟩
  rcases x with ⟨⟨x, y⟩, z⟩
  rw [closedHom_zero, LinearMap.zero_apply, sub_zero, hH, totalization_differential, hH,
    hsplit]
  simp only [map_neg, map_add, map_sub, neg_sub, he, hv']
  rw [← hdv z]
  abel

end Totalization

variable (R h) in
/-- Every map from the totalization of a short exact sequence into a graded-injective curved
module vanishes in the homotopy category. -/
theorem totalizations_le_leftOrthogonal_gradedInjective :
    totalizations R h ≤ (gradedInjective R h).leftOrthogonal := by
  refine (totalizations_le_iff _).2 fun S hS ↦ ?_
  rw [totalization_eq]
  intro I f hI
  have := (gradedInjective_iff I).1 hI
  obtain ⟨φ, hφ⟩ := (dgClosedToHomotopy R).map_surjective f
  exact hφ.symm.trans (totalization_map_eq_zero (I := I.underlying) S.f S.g S.zero hS φ)

variable (R h) in
/-- Coacyclic curved modules have no nonzero maps to graded-injective curved modules in the
homotopy category. -/
theorem coacyclic_le_leftOrthogonal_gradedInjective :
    coacyclic R h ≤ (gradedInjective R h).leftOrthogonal :=
  coacyclic_le_iff.2 (totalizations_le_leftOrthogonal_gradedInjective R h)

/-- Localization to the coderived category is bijective on morphisms into a graded-injective
curved module. -/
theorem CoderivedCategory.map_bijective_of_gradedInjective
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    {I : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)} (hI : gradedInjective R h I) :
    Function.Bijective ((CoderivedCategory.Q R h).map : (X ⟶ I) → _) :=
  ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated
    ((ObjectProperty.le_leftOrthogonal_iff_le_rightOrthogonal _ _).1
      (coacyclic_le_leftOrthogonal_gradedInjective R h) I hI) _ X

end TauCeti.CurvedDGRightModuleCat
