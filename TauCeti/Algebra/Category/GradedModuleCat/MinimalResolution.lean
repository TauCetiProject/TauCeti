/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution
import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Ext and uniqueness for minimal graded resolutions

For a minimal graded projective resolution, every differential has image in the positive-degree
algebra action. Against a target annihilated by that action, the Hom complex has zero
differentials. Its terms therefore compute Ext in every degree, including degree zero. Moreover,
any chain endomorphism of a minimal resolution homotopic to the identity is congruent to the
identity modulo `A₊` in every degree, so graded Nakayama makes minimal resolutions unique up to
termwise graded isomorphism whenever their terms are bounded below (in particular, whenever their
terms are finitely generated over a nonnegatively decomposed algebra).

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
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded Nakayama
  and minimal graded resolutions.
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

/-- Any chain endomorphism of a minimal resolution homotopic to the identity is an isomorphism in
every homological degree whose term is bounded below. -/
theorem IsMinimal.isIso_f_of_homotopy_id (hr : r.IsMinimal)
    {g : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (h : Homotopy g (𝟙 r.toProjectiveResolution.complex)) {n : ℕ} (b : ℤ)
    (hbelow : ∀ p < b, (r.grading n).piece p = ⊥) :
    IsIso (g.f n) := by
  -- `g.f n - 𝟙` is a sum of composites factoring through `r.differential`, so it lands in `A₊`
  -- and `g.f n` is bijective by graded Nakayama.
  let e := r.toProjectiveResolutionXIso n
  let g' : r.termObj n ⟶ r.termObj n := e.inv ≫ g.f n ≫ e.hom
  have hg' : IsIso g' := (GradedModuleCat.isIso_iff_bijective g').mpr <|
    InternalGrading.bijective_of_sub_mem_positive_smul_top 𝒜 b hbelow g'.isHomogeneous fun x ↦ by
      have hcomm := congrArg (fun φ : _ ⟶ _ ↦ (e.inv ≫ φ ≫ e.hom).hom x) (h.comm n)
      simp only [Preadditive.add_comp, Preadditive.comp_add, HomologicalComplex.id_f,
        Category.id_comp, Iso.inv_hom_id, GradedModuleCat.hom_add, LinearMap.add_apply,
        GradedModuleCat.hom_id, LinearMap.id_apply] at hcomm
      have hsub : g'.hom x - x =
          (e.inv ≫ dNext n h.hom ≫ e.hom).hom x + (e.inv ≫ prevD n h.hom ≫ e.hom).hom x := by
        dsimp only [g']
        rw [hcomm, add_sub_cancel_right]
      rw [hsub]
      refine add_mem ?_ ?_
      · cases n with
        | zero =>
          rw [dNext_eq_zero h.hom 0 (by simp [ComplexShape.down_Rel])]
          simp
        | succ m =>
          rw [dNext_eq h.hom (rfl : (ComplexShape.down ℕ).Rel (m + 1) m),
            r.toProjectiveResolution_complex_d]
          simp only [e, Category.assoc, Iso.inv_hom_id_assoc, GradedModuleCat.hom_comp,
            LinearMap.comp_apply]
          exact InternalGrading.map_mem_positive_smul_top _ <|
            InternalGrading.map_mem_positive_smul_top _ <|
              InternalGrading.map_mem_positive_smul_top _ (isMinimal_iff.mp hr m x)
      · rw [prevD_eq h.hom (rfl : (ComplexShape.down ℕ).Rel (n + 1) n),
          r.toProjectiveResolution_complex_d]
        simp only [e, Category.assoc, Iso.inv_hom_id, Category.comp_id, GradedModuleCat.hom_comp,
          LinearMap.comp_apply]
        exact isMinimal_iff.mp hr n _
  have hge : g.f n = e.hom ≫ g' ≫ e.inv := by simp [g', e]
  rw [hge]
  infer_instance

/-- **Comparison morphisms between minimal resolutions are termwise isomorphisms.** Any chain map
between minimal graded projective resolutions of `M` compatible with the augmentations is an
isomorphism in every homological degree where both resolution terms are bounded below. -/
theorem IsMinimal.isIso_f_of_comm
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (f : r₁.toProjectiveResolution.complex ⟶ r₂.toProjectiveResolution.complex)
    (hf : f ≫ r₂.toProjectiveResolution.π = r₁.toProjectiveResolution.π)
    {n : ℕ} (b₁ b₂ : ℤ)
    (hbelow₁ : ∀ p < b₁, (r₁.grading n).piece p = ⊥)
    (hbelow₂ : ∀ p < b₂, (r₂.grading n).piece p = ⊥) :
    IsIso (f.f n) := by
  let heq := ProjectiveResolution.homotopyEquivOfComm r₁.toProjectiveResolution
    r₂.toProjectiveResolution f hf
  have h₁ : IsIso ((heq.hom ≫ heq.inv).f n) :=
    hr₁.isIso_f_of_homotopy_id heq.homotopyHomInvId b₁ hbelow₁
  have h₂ : IsIso ((heq.inv ≫ heq.hom).f n) :=
    hr₂.isIso_f_of_homotopy_id heq.homotopyInvHomId b₂ hbelow₂
  rw [ProjectiveResolution.homotopyEquivOfComm_hom] at h₁ h₂
  have hb₁ : Function.Bijective (f.f n ≫ heq.inv.f n).hom :=
    (GradedModuleCat.isIso_iff_bijective _).mp h₁
  have hb₂ : Function.Bijective (heq.inv.f n ≫ f.f n).hom :=
    (GradedModuleCat.isIso_iff_bijective _).mp h₂
  rw [GradedModuleCat.isIso_iff_bijective]
  exact ⟨Function.Injective.of_comp (f := (heq.inv.f n).hom) (by simpa using hb₁.1),
    Function.Surjective.of_comp (g := (heq.inv.f n).hom) (by simpa using hb₂.2)⟩

/-- **Uniqueness of minimal graded projective resolutions (bounded-below form).** Two minimal
graded projective resolutions of `M` have isomorphic `n`th graded terms whenever both `n`th terms
are bounded below. -/
noncomputable def IsMinimal.termObjIso
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) {n : ℕ} (b₁ b₂ : ℤ)
    (hbelow₁ : ∀ p < b₁, (r₁.grading n).piece p = ⊥)
    (hbelow₂ : ∀ p < b₂, (r₂.grading n).piece p = ⊥) :
    r₁.termObj n ≅ r₂.termObj n := by
  let f := (ProjectiveResolution.homotopyEquiv r₁.toProjectiveResolution
    r₂.toProjectiveResolution).hom
  have : IsIso (f.f n) := hr₁.isIso_f_of_comm hr₂ f (by simp [f]) b₁ b₂ hbelow₁ hbelow₂
  exact (r₁.toProjectiveResolutionXIso n).symm ≪≫ asIso (f.f n) ≪≫ r₂.toProjectiveResolutionXIso n

/-- **Uniqueness of minimal graded projective resolutions (finitely generated form).** Over a
nonnegatively decomposed algebra, two minimal graded projective resolutions of `M` have isomorphic
`n`th graded terms whenever both `n`th terms are finitely generated `A`-modules. -/
noncomputable def IsMinimal.termObjIsoOfFinite
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    r₁.termObj n ≅ r₂.termObj n :=
  let hb₁ := (r₁.grading n).bddBelow_setOf_piece_ne_bot 𝒜 h𝒜
  let hb₂ := (r₂.grading n).bddBelow_setOf_piece_ne_bot 𝒜 h𝒜
  hr₁.termObjIso hr₂ hb₁.choose hb₂.choose
    (fun _ hp ↦ Classical.not_not.mp fun hne ↦ (hb₁.choose_spec hne).not_gt hp)
    (fun _ hp ↦ Classical.not_not.mp fun hne ↦ (hb₂.choose_spec hne).not_gt hp)

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

end GradedProjectiveResolution

end TauCeti
