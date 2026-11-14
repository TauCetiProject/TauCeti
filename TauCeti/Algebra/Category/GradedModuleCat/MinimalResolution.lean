/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution
public import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Ext from minimal graded resolutions

For a minimal graded projective resolution, every differential has image in the positive-degree
algebra action. Against a target annihilated by that action, the Hom complex has zero
differentials. Its terms therefore compute Ext in every degree, including degree zero.

`GradedProjectiveResolution.IsMinimal.extLinearEquiv` identifies graded Hom from the `n`th
resolution term with `Extⁿ`. The vanishing characterization converts diagonal Ext vanishing
into vanishing of graded Hom, without assuming the resolution is linear. The equivalence is
natural in the target. Neither nonnegative grading nor semisimplicity is needed for this
computation; those hypotheses enter when detecting generating degrees or constructing minimal
resolutions.

`GradedProjectiveResolution.exists_isMinimal_of_forall_cover` assembles a minimal resolution from
any supply of minimal projective surjections that is stable under passing to kernels.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for the minimal-resolution computation underlying the diagonal Ext criterion.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.4, for computing Ext
  from projective resolutions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {M N N' : GradedModuleCat.{v} 𝒜}

namespace GradedProjectiveResolution

variable {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}

/-- Every differential of a minimal resolution dies after mapping to a target annihilated by
positive-degree scalars. -/
@[reassoc (attr := simp)]
theorem IsMinimal.differential_comp_eq_zero (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥)
    (n : ℕ) (f : r.termObj n ⟶ N) : r.differential n ≫ f = 0 := by
  have hker : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) ≤
      LinearMap.ker (f.hom.restrictScalars k) := by
    refine Submodule.smul_le.mpr fun a ha x _ ↦ ?_
    have hz := Submodule.smul_mem_smul ha (Submodule.mem_top : f.hom x ∈ (⊤ : Submodule k N))
    rw [hN] at hz
    simpa only [LinearMap.mem_ker, LinearMap.restrictScalars_apply, map_smul,
      Submodule.mem_bot] using hz
  apply GradedModuleCat.hom_ext
  ext x
  exact hker (isMinimal_iff.mp hr n x)

/-- Precomposition with the augmentation of a minimal resolution is an equivalence for a
positive-action-annihilated target. This also explains the degree-zero Ext computation. -/
noncomputable def IsMinimal.augmentationLinearEquiv (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥) :
    (M ⟶ N) ≃ₗ[k] (r.termObj 0 ⟶ N) := by
  have : Epi r.augmentation := (GradedModuleCat.epi_iff_surjective _).mpr r.surjective_π
  refine LinearEquiv.ofBijective (Linear.leftComp k N r.augmentation) ⟨?_, ?_⟩
  · intro f g hfg
    exact (cancel_epi r.augmentation).mp hfg
  · intro f
    let S := ShortComplex.mk (r.differential 0) r.augmentation
      r.differential_zero_comp_augmentation
    have hS : S.Exact := (GradedModuleCat.exact_iff).mpr r.exact_d_π
    exact hS.desc' f (hr.differential_comp_eq_zero hN 0 f)

/-- The augmentation equivalence is precomposition with the original augmentation. -/
@[simp]
theorem IsMinimal.augmentationLinearEquiv_apply (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥) (f : M ⟶ N) :
    hr.augmentationLinearEquiv hN f = r.augmentation ≫ f :=
  (rfl)

open GradedModuleCat in
/-- Iterating minimal projective surjections along successive kernels gives a minimal resolution.
Suppose every graded module satisfying `S` is the target of a projective surjection whose kernel
lies in the positive-degree action on the source, whose source satisfies `T`, and whose kernel
again satisfies `S`. Then every graded module satisfying `S` has a minimal graded projective
resolution all of whose terms satisfy `T`. -/
theorem exists_isMinimal_of_forall_cover (S T : GradedModuleCat.{v} 𝒜 → Prop)
    (hcover : ∀ N, S N → ∃ (P : GradedModuleCat.{v} 𝒜) (π : P ⟶ N), Module.Projective A P ∧
      Function.Surjective π.hom ∧
      (∀ x, π.hom x = 0 → x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) ∧
      T P ∧ S (kernelObj π))
    (M : GradedModuleCat.{v} 𝒜) (hM : S M) :
    ∃ r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading,
      r.IsMinimal ∧ ∀ n, T (r.termObj n) := by
  choose P π hP hπ hmin hT hS using fun N : {N // S N} => hcover N.1 N.2
  -- The successive kernels, starting from `M`.
  let K : ℕ → {N // S N} := fun n => Nat.rec ⟨M, hM⟩ (fun _ N => ⟨kernelObj (π N), hS N⟩) n
  refine ⟨{
    X := fun n => P (K n)
    grading := fun n => (P (K n)).grading
    projective := fun n => hP (K n)
    d := fun n => (π (K (n + 1)) ≫ kernelι (π (K n))).hom
    π := (π (K 0)).hom
    isHomogeneous_d := fun n => (π (K (n + 1)) ≫ kernelι (π (K n))).isHomogeneous
    isHomogeneous_π := (π (K 0)).isHomogeneous
    surjective_π := hπ (K 0)
    exact_d_π := by
      rw [GradedModuleCat.hom_comp, hom_kernelι]
      exact (hπ (K (0 + 1))).comp_exact_iff_exact.mpr (LinearMap.exact_subtype_ker_map _)
    exact_d_d := fun n => by
      rw [GradedModuleCat.hom_comp, hom_kernelι, GradedModuleCat.hom_comp, hom_kernelι,
        (Submodule.injective_subtype _).comp_exact_iff_exact]
      exact (hπ (K (n + 2))).comp_exact_iff_exact.mpr (LinearMap.exact_subtype_ker_map _) },
    isMinimal_iff.mpr fun n x => hmin (K n) _ (π (K (n + 1)) |>.hom x).2, fun n => hT (K n)⟩

variable [DirectSum.Decomposition 𝒜]

private theorem IsMinimal.complex_d_comp_eq_zero (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥)
    (n : ℕ) (f : r.toProjectiveResolution.complex.X n ⟶ N) :
    r.toProjectiveResolution.complex.d (n + 1) n ≫ f = 0 := by
  rw [r.toProjectiveResolution_complex_d]
  simp only [Category.assoc, hr.differential_comp_eq_zero hN, comp_zero]

variable [HasExt.{w} (GradedModuleCat.{v} 𝒜)]

/-- A minimal resolution computes Ext as graded Hom from its terms whenever positive-degree
scalars annihilate the target. The statement includes degree zero. -/
noncomputable def IsMinimal.extLinearEquiv (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥)
    (n : ℕ) : (r.termObj n ⟶ N) ≃ₗ[k] Ext.{w} M N n :=
  match n with
  | 0 => (hr.augmentationLinearEquiv hN).symm.trans (Ext.linearEquiv₀ (R := k)).symm
  | n + 1 =>
      (Linear.homCongr k (r.toProjectiveResolutionXIso (n + 1)).symm (Iso.refl N)).trans
        (r.toProjectiveResolution.extLinearEquiv n
          (hr.complex_d_comp_eq_zero hN (n + 1)) (hr.complex_d_comp_eq_zero hN n))

/-- In degree zero, a map pulled back along the augmentation represents the ordinary Hom class. -/
@[simp]
theorem IsMinimal.extLinearEquiv_zero_augmentation_comp (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥) (f : M ⟶ N) :
    hr.extLinearEquiv hN 0 (r.augmentation ≫ f) = Ext.mk₀ f := by
  dsimp only [IsMinimal.extLinearEquiv, LinearEquiv.trans_apply]
  rw [← hr.augmentationLinearEquiv_apply hN f, LinearEquiv.symm_apply_apply]
  simp

/-- The degree-zero equivalence descends a map through the augmentation. -/
@[reassoc (attr := simp)]
theorem IsMinimal.augmentation_comp_linearEquiv₀_extLinearEquiv (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥)
    (f : r.termObj 0 ⟶ N) :
    r.augmentation ≫ Ext.linearEquiv₀ (R := k) (hr.extLinearEquiv hN 0 f) = f := by
  obtain ⟨g, rfl⟩ := (hr.augmentationLinearEquiv hN).surjective f
  simp only [IsMinimal.augmentationLinearEquiv_apply,
    IsMinimal.extLinearEquiv_zero_augmentation_comp]
  simpa only [Ext.linearEquiv₀_symm_apply] using
    congrArg (r.augmentation ≫ ·) ((Ext.linearEquiv₀ (R := k)).apply_symm_apply g)

/-- In positive degree the equivalence sends a graded map to its projective-resolution class. -/
@[simp]
theorem IsMinimal.extLinearEquiv_succ_apply (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥)
    (n : ℕ) (f : r.termObj (n + 1) ⟶ N) :
    hr.extLinearEquiv hN (n + 1) f =
      r.toProjectiveResolution.extMk ((r.toProjectiveResolutionXIso (n + 1)).hom ≫ f)
        (n + 2) rfl
        (by
          rw [r.toProjectiveResolution_complex_d]
          simp only [Category.assoc, Iso.inv_hom_id_assoc,
            hr.differential_comp_eq_zero hN, comp_zero]) := by
  simp [IsMinimal.extLinearEquiv, Linear.homCongr_apply]

/-- Ext against an annihilated target vanishes exactly when graded Hom from the corresponding
term of the minimal resolution vanishes. -/
theorem IsMinimal.subsingleton_ext_iff (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥) (n : ℕ) :
    Subsingleton (Ext.{w} M N n) ↔ Subsingleton (r.termObj n ⟶ N) :=
  (hr.extLinearEquiv hN n).toEquiv.subsingleton_congr.symm

/-- The minimal-resolution Ext computation is natural under maps between targets annihilated
by positive-degree scalars. -/
theorem IsMinimal.extLinearEquiv_comp (hr : r.IsMinimal)
    (hN : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) = ⊥)
    (hN' : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N') = ⊥)
    (n : ℕ) (f : r.termObj n ⟶ N) (g : N ⟶ N') :
    hr.extLinearEquiv hN' n (f ≫ g) =
      (hr.extLinearEquiv hN n f).comp (Ext.mk₀ g) (add_zero _) := by
  cases n with
  | zero =>
      obtain ⟨f, rfl⟩ := (hr.augmentationLinearEquiv hN).surjective f
      simp only [IsMinimal.augmentationLinearEquiv_apply, Category.assoc,
        IsMinimal.extLinearEquiv_zero_augmentation_comp, Ext.mk₀_comp_mk₀]
  | succ n =>
      simp only [IsMinimal.extLinearEquiv_succ_apply,
        ProjectiveResolution.extMk_comp_mk₀, Category.assoc]

/-! ### Uniqueness of minimal resolutions -/

section Uniqueness

omit [HasExt.{w} (GradedModuleCat.{v} 𝒜)] in
private theorem IsMinimal.sub_id_mem_positive_smul_top_of_homotopy_id (hr : r.IsMinimal)
    {u : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (h : Homotopy u (𝟙 r.toProjectiveResolution.complex)) (n : ℕ) (x : r.X n) :
    (((r.toProjectiveResolutionXIso n).inv ≫ u.f n ≫
        (r.toProjectiveResolutionXIso n).hom).hom x) - x ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) := by
  have hcomm :
      (r.toProjectiveResolutionXIso n).inv ≫ u.f n ≫ (r.toProjectiveResolutionXIso n).hom -
        𝟙 (r.termObj n) =
      (r.toProjectiveResolutionXIso n).inv ≫ dNext n h.hom ≫
        (r.toProjectiveResolutionXIso n).hom +
      (r.toProjectiveResolutionXIso n).inv ≫ prevD n h.hom ≫
        (r.toProjectiveResolutionXIso n).hom := by
    rw [h.comm n]
    simp only [Preadditive.comp_add, Preadditive.add_comp, HomologicalComplex.id_f,
      Category.id_comp, Iso.inv_hom_id, add_sub_cancel_right]
  have hsub :
      (((r.toProjectiveResolutionXIso n).inv ≫ u.f n ≫
          (r.toProjectiveResolutionXIso n).hom).hom x) - x =
        (((r.toProjectiveResolutionXIso n).inv ≫ dNext n h.hom ≫
            (r.toProjectiveResolutionXIso n).hom +
          (r.toProjectiveResolutionXIso n).inv ≫ prevD n h.hom ≫
            (r.toProjectiveResolutionXIso n).hom).hom x) := by
    simpa [GradedModuleCat.hom_sub] using
      congrArg (fun φ : r.termObj n ⟶ r.termObj n => φ.hom x) hcomm
  rw [hsub, GradedModuleCat.hom_add, LinearMap.add_apply]
  refine add_mem ?_ ?_
  · cases n with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex]
        simp
    | succ m =>
        rw [Homotopy.dNext_succ_chainComplex, r.toProjectiveResolution_complex_d m]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        exact InternalGrading.map_mem_positive_smul_top 𝒜
          ((r.toProjectiveResolutionXIso m).inv ≫ h.hom m (m + 1) ≫
            (r.toProjectiveResolutionXIso (m + 1)).hom).hom
          (isMinimal_iff.mp hr m x)
  · rw [Homotopy.prevD_chainComplex, r.toProjectiveResolution_complex_d n]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, GradedModuleCat.hom_comp,
      LinearMap.comp_apply]
    exact isMinimal_iff.mp hr n _

omit [HasExt.{w} (GradedModuleCat.{v} 𝒜)] in
/-- **A chain endomorphism of a bounded-below minimal resolution homotopic to the identity is an
isomorphism.** Each component differs from the identity by an endomorphism valued in `A₊ Pₙ`, so
Graded Nakayama makes every component invertible. -/
theorem IsMinimal.isIso_of_homotopy_id (hr : r.IsMinimal)
    (hbelow : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    {u : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (h : Homotopy u (𝟙 r.toProjectiveResolution.complex)) : IsIso u := by
  have : ∀ n, IsIso (u.f n) := fun n => by
    obtain ⟨b, hb⟩ := hbelow n
    let v : r.termObj n ⟶ r.termObj n :=
      (r.toProjectiveResolutionXIso n).inv ≫ u.f n ≫ (r.toProjectiveResolutionXIso n).hom
    have hv : IsIso v := (GradedModuleCat.isIso_iff_bijective v).mpr
      (InternalGrading.bijective_of_sub_mem_positive_smul_top 𝒜 b hb v.hom v.isHomogeneous
        (hr.sub_id_mem_positive_smul_top_of_homotopy_id h n))
    have heq : u.f n =
        (r.toProjectiveResolutionXIso n).hom ≫ v ≫ (r.toProjectiveResolutionXIso n).inv := by
      simp [v]
    rw [heq]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components u

omit [HasExt.{w} (GradedModuleCat.{v} 𝒜)] in
/-- **Uniqueness of minimal graded projective resolutions up to complex isomorphism.** Any
graded isomorphism `φ : M ≅ M'` lifts to an isomorphism between the chain complexes of any two
bounded-below minimal graded projective resolutions of `M` and `M'`. -/
noncomputable def IsMinimal.complexIsoOfIso {M' : GradedModuleCat.{v} 𝒜}
    {r' : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M'.grading}
    (φ : M ≅ M') (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (hbelow : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hbelow' : ∀ n, ∃ b : ℤ, ∀ p < b, (r'.grading n).piece p = ⊥) :
    r.toProjectiveResolution.complex ≅ r'.toProjectiveResolution.complex := by
  let P := r.toProjectiveResolution
  let Q := r'.toProjectiveResolution
  let f : P.complex ⟶ Q.complex := ProjectiveResolution.lift φ.hom P Q
  let g : Q.complex ⟶ P.complex := ProjectiveResolution.lift φ.inv Q P
  have hfg : IsIso (f ≫ g) := hr.isIso_of_homotopy_id hbelow
    (ProjectiveResolution.liftHomotopy (𝟙 M) (f ≫ g) (𝟙 P.complex) (by simp [f, g]) (by simp))
  have hgf : IsIso (g ≫ f) := hr'.isIso_of_homotopy_id hbelow'
    (ProjectiveResolution.liftHomotopy (𝟙 M') (g ≫ f) (𝟙 Q.complex) (by simp [f, g]) (by simp))
  have hf : IsIso f := by
    let rInv : Q.complex ⟶ P.complex := g ≫ inv (f ≫ g)
    let lInv : Q.complex ⟶ P.complex := inv (g ≫ f) ≫ g
    have hrInv : f ≫ rInv = 𝟙 P.complex := by simp [rInv, ← Category.assoc]
    have hlInv : lInv ≫ f = 𝟙 Q.complex := by simp [lInv]
    have hlr : lInv = rInv := by
      calc
        lInv = lInv ≫ (f ≫ rInv) := by rw [hrInv, Category.comp_id]
        _ = (lInv ≫ f) ≫ rInv := (Category.assoc _ _ _).symm
        _ = rInv := by rw [hlInv, Category.id_comp]
    exact ⟨⟨rInv, hrInv, hlr ▸ hlInv⟩⟩
  exact asIso f

omit [HasExt.{w} (GradedModuleCat.{v} 𝒜)] in
/-- Two bounded-below minimal graded projective resolutions of isomorphic graded modules have
isomorphic `n`th terms in `GradedModuleCat 𝒜`. -/
noncomputable def IsMinimal.termObjIsoOfIso {M' : GradedModuleCat.{v} 𝒜}
    {r' : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M'.grading}
    (φ : M ≅ M') (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (hbelow : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hbelow' : ∀ n, ∃ b : ℤ, ∀ p < b, (r'.grading n).piece p = ⊥) (n : ℕ) :
    r.termObj n ≅ r'.termObj n :=
  (r.toProjectiveResolutionXIso n).symm ≪≫
    (HomologicalComplex.eval _ _ n).mapIso (hr.complexIsoOfIso φ hr' hbelow hbelow') ≪≫
    r'.toProjectiveResolutionXIso n

omit [HasExt.{w} (GradedModuleCat.{v} 𝒜)] in
/-- Any two bounded-below minimal graded projective resolutions of the same graded module have
isomorphic `n`th terms in `GradedModuleCat 𝒜`. -/
noncomputable def IsMinimal.termObjIso
    {r' : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (hbelow : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hbelow' : ∀ n, ∃ b : ℤ, ∀ p < b, (r'.grading n).piece p = ⊥) (n : ℕ) :
    r.termObj n ≅ r'.termObj n :=
  hr.termObjIsoOfIso (Iso.refl M) hr' hbelow hbelow' n

end Uniqueness

end GradedProjectiveResolution

/-! ### Shifts and finitely generated minimal resolutions -/

namespace GradedProjectiveResolution

variable [GradedAlgebra 𝒜] {r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}

/-- Shifting a graded projective resolution of `M` by `d` produces a graded projective resolution
of `M{d}` whose `n`th term is `(r.termObj n){d}`. -/
abbrev shiftObj (r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading) (d : ℤ) :
    GradedProjectiveResolution.{uk, uA, v, v} 𝒜 (M.shiftObj d).grading :=
  r.shift (-d)

omit [GradedAlgebra 𝒜] in
/-- The `n`th term of `r.shiftObj d` is the shifted object `(r.termObj n){d}`. -/
@[simp]
theorem shiftObj_termObj (r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading)
    (d : ℤ) (n : ℕ) :
    (r.shiftObj d).termObj n = (r.termObj n).shiftObj d :=
  (rfl)

omit [GradedAlgebra 𝒜] in
/-- Shifting a resolution of `M` to `M{d}` preserves minimality. -/
theorem isMinimal_shiftObj_iff (r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading)
    (d : ℤ) :
    (r.shiftObj d).IsMinimal ↔ r.IsMinimal :=
  r.isMinimal_shift_iff (-d)

/-- Over a nonnegatively graded algebra, two minimal graded projective resolutions with finitely
generated terms of isomorphic graded modules have isomorphic `n`th terms in `GradedModuleCat 𝒜`. -/
noncomputable def IsMinimal.termObjIsoOfIsoOfFinite (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {M' : GradedModuleCat.{v} 𝒜}
    {r' : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M'.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (φ : M ≅ M') (hr : r.IsMinimal) (hr' : r'.IsMinimal) (n : ℕ) :
    r.termObj n ≅ r'.termObj n :=
  hr.termObjIsoOfIso φ hr'
    (fun m => (r.grading m).exists_piece_eq_bot_of_lt 𝒜 hneg)
    (fun m => (r'.grading m).exists_piece_eq_bot_of_lt 𝒜 hneg) n

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions with
finitely generated terms of the same graded module have isomorphic `n`th terms. -/
noncomputable def IsMinimal.termObjIsoOfFinite (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {r' : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (n : ℕ) :
    r.termObj n ≅ r'.termObj n :=
  hr.termObjIsoOfIsoOfFinite hneg (Iso.refl M) hr' n

end GradedProjectiveResolution

end TauCeti
