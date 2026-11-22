/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Nakayama
public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution

/-!
# Ext from minimal graded resolutions and uniqueness

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

Minimality also forces termwise uniqueness: any degree-zero endomorphism of a bounded-below graded
module taking values in `A₊ P` is locally nilpotent, so `𝟙 P - h` is an isomorphism
(`GradedModuleCat.isIso_id_sub_of_mem_positive_smul_top`). Applying this to the homotopy
equivalence between two bounded-below minimal graded projective resolutions shows that the
comparison map is an isomorphism of chain complexes
(`GradedProjectiveResolution.IsMinimal.isIso_hom_of_homotopyEquiv`), so the terms of a minimal
resolution are unique up to graded isomorphism (`IsMinimal.nonempty_iso_termObj`). In particular,
linearity is independent of the choice of minimal resolution (`IsMinimal.isLinear_iff_isLinear`).

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for the minimal-resolution computation underlying the diagonal Ext criterion.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.4, for computing Ext
  from projective resolutions.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projective modules and minimal resolutions.
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

/-! ### Uniqueness of minimal resolutions -/

private theorem IsMinimal.dNext_add_prevD_mem_positive_smul_top (hr : r.IsMinimal)
    {φ : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (H : Homotopy φ (𝟙 r.toProjectiveResolution.complex)) (n : ℕ) (x : r.termObj n) :
    ((r.toProjectiveResolutionXIso n).inv ≫ (dNext n H.hom + prevD n H.hom) ≫
        (r.toProjectiveResolutionXIso n).hom).hom x ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.termObj n)) := by
  let e := r.toProjectiveResolutionXIso n
  have hdNext : (e.inv ≫ dNext n H.hom ≫ e.hom).hom x ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.termObj n)) := by
    cases n with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp)]
      simp
    | succ m =>
      rw [dNext_eq H.hom (by simp : (ComplexShape.down ℕ).Rel (m + 1) m),
        r.toProjectiveResolution_complex_d m]
      have hd :
          (r.differential m).hom ((e.inv ≫ (r.toProjectiveResolutionXIso (m + 1)).hom).hom x) ∈
            (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X m)) :=
        isMinimal_iff.mp hr m _
      simpa only [Category.assoc, GradedModuleCat.hom_comp, LinearMap.comp_apply] using
        ((r.toProjectiveResolutionXIso m).inv ≫ H.hom m (m + 1) ≫
          e.hom).hom.map_mem_positive_smul_top hd
  have hprevD : (e.inv ≫ prevD n H.hom ≫ e.hom).hom x ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.termObj n)) := by
    rw [prevD_eq H.hom (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
      r.toProjectiveResolution_complex_d n]
    have hd : (r.differential n).hom
        ((e.inv ≫ H.hom n (n + 1) ≫ (r.toProjectiveResolutionXIso (n + 1)).hom).hom x) ∈
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) :=
      isMinimal_iff.mp hr n _
    dsimp only [e]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      GradedModuleCat.hom_comp, LinearMap.comp_apply] using hd
  simpa only [Preadditive.add_comp, Preadditive.comp_add, GradedModuleCat.hom_add,
    LinearMap.add_apply] using Submodule.add_mem _ hdNext hprevD

/-- Any chain endomorphism homotopic to the identity on a bounded-below minimal graded projective
resolution is an isomorphism in every degree. -/
private theorem IsMinimal.isIso_f_of_homotopy_id (hr : r.IsMinimal)
    (hb : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    {φ : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (H : Homotopy φ (𝟙 r.toProjectiveResolution.complex)) (n : ℕ) :
    IsIso (φ.f n) := by
  obtain ⟨b, hbelow⟩ := hb n
  let e := r.toProjectiveResolutionXIso n
  -- Conjugate `φ.f n` across `e : complex.X n ≅ termObj n`, then apply local nilpotence.
  have hcomm := H.comm n
  rw [HomologicalComplex.id_f] at hcomm
  let ψ : r.termObj n ⟶ r.termObj n := e.inv ≫ φ.f n ≫ e.hom
  let h : r.termObj n ⟶ r.termObj n := -(e.inv ≫ (dNext n H.hom + prevD n H.hom) ≫ e.hom)
  have hψ : ψ = 𝟙 (r.termObj n) - h := by
    rw [sub_neg_eq_add]
    simp only [ψ, hcomm, Preadditive.add_comp, Preadditive.comp_add, Category.id_comp,
      Iso.inv_hom_id, add_comm]
  have hh : ∀ x : r.termObj n,
      h.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.termObj n)) := fun x => by
    simpa only [h, GradedModuleCat.hom_neg, LinearMap.neg_apply] using
      Submodule.neg_mem _ (hr.dNext_add_prevD_mem_positive_smul_top H n x)
  have hψiso : IsIso ψ := hψ ▸ GradedModuleCat.isIso_id_sub_of_mem_positive_smul_top h b hbelow hh
  have hφ : φ.f n = e.hom ≫ ψ ≫ e.inv := by simp [ψ]
  rw [hφ]
  infer_instance

/-- **Uniqueness of minimal graded projective resolutions.** The canonical homotopy equivalence
between two bounded-below minimal graded projective resolutions of `M` is an isomorphism of chain
complexes in `GradedModuleCat 𝒜`. -/
theorem IsMinimal.isIso_hom_of_homotopyEquiv
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) :
    IsIso (ProjectiveResolution.homotopyEquiv
      r₁.toProjectiveResolution r₂.toProjectiveResolution).hom := by
  let e := ProjectiveResolution.homotopyEquiv r₁.toProjectiveResolution r₂.toProjectiveResolution
  have hcomp (n : ℕ) : IsIso (e.hom.f n) := by
    have h₁ : IsIso ((e.hom ≫ e.inv).f n) :=
      hr₁.isIso_f_of_homotopy_id hb₁ e.homotopyHomInvId n
    have h₂ : IsIso ((e.inv ≫ e.hom).f n) :=
      hr₂.isIso_f_of_homotopy_id hb₂ e.homotopyInvHomId n
    rw [HomologicalComplex.comp_f, GradedModuleCat.isIso_iff_bijective,
      GradedModuleCat.hom_comp] at h₁ h₂
    rw [GradedModuleCat.isIso_iff_bijective]
    exact ⟨Function.Injective.of_comp h₁.1, Function.Surjective.of_comp h₂.2⟩
  exact HomologicalComplex.Hom.isIso_of_components e.hom

/-- **Termwise uniqueness of minimal resolutions.** Any two bounded-below minimal graded projective
resolutions of `M` have isomorphic terms in every homological degree. -/
theorem IsMinimal.nonempty_iso_termObj
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) (n : ℕ) :
    Nonempty (r₁.termObj n ≅ r₂.termObj n) := by
  have := hr₁.isIso_hom_of_homotopyEquiv hr₂ hb₁ hb₂
  exact ⟨(r₁.toProjectiveResolutionXIso n).symm ≪≫
    (HomologicalComplex.eval (GradedModuleCat.{v} 𝒜) (ComplexShape.down ℕ) n).mapIso
      (asIso (ProjectiveResolution.homotopyEquiv
        r₁.toProjectiveResolution r₂.toProjectiveResolution).hom) ≪≫
    r₂.toProjectiveResolutionXIso n⟩

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions of `M` with
finitely generated terms have isomorphic terms in every homological degree. -/
theorem IsMinimal.nonempty_iso_termObj_of_finite
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    [∀ n, Module.Finite A (r₁.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (n : ℕ) :
    Nonempty (r₁.termObj n ≅ r₂.termObj n) :=
  hr₁.nonempty_iso_termObj hr₂
    (fun m => (r₁.grading m).exists_piece_eq_bot_of_lt 𝒜 hneg)
    (fun m => (r₂.grading m).exists_piece_eq_bot_of_lt 𝒜 hneg) n

/-- **Linearity is independent of the minimal resolution.** If two bounded-below minimal graded
projective resolutions resolve the same graded module, one is linear if and only if the other is. -/
theorem IsMinimal.isLinear_iff_isLinear
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) :
    r₁.IsLinear ↔ r₂.IsLinear := by
  have hgen (n : ℕ) :
      (r₁.grading n).IsGeneratedInDegree A n ↔ (r₂.grading n).IsGeneratedInDegree A n := by
    obtain ⟨e⟩ := hr₁.nonempty_iso_termObj hr₂ hb₁ hb₂ n
    have he₁ : e.hom.hom ∘ₗ e.inv.hom = LinearMap.id := by
      rw [← GradedModuleCat.hom_comp, e.inv_hom_id, GradedModuleCat.hom_id]
    have he₂ : e.inv.hom ∘ₗ e.hom.hom = LinearMap.id := by
      rw [← GradedModuleCat.hom_comp, e.hom_inv_id, GradedModuleCat.hom_id]
    let le : r₁.X n ≃ₗ[A] r₂.X n := LinearEquiv.ofLinearMap e.hom.hom e.inv.hom he₁ he₂
    have hpiece : ((r₁.grading n).map (le.restrictScalars k)).piece n = (r₂.grading n).piece n := by
      ext y
      rw [InternalGrading.mem_map_piece_iff]
      constructor
      · intro hy
        have hmap := e.hom.isHomogeneous.map_mem hy
        simpa only [le, LinearEquiv.restrictScalars_symm_apply, LinearEquiv.symm_ofLinearMap,
          LinearEquiv.coe_ofLinearMap, add_zero, ← LinearMap.comp_apply, he₁,
          LinearMap.id_apply] using hmap
      · intro hy
        simpa only [le, LinearEquiv.restrictScalars_symm_apply, LinearEquiv.symm_ofLinearMap,
          LinearEquiv.coe_ofLinearMap, add_zero] using e.inv.isHomogeneous.map_mem hy
    rw [← InternalGrading.isGeneratedInDegree_map_iff (r₁.grading n) le n,
      InternalGrading.isGeneratedInDegree_iff, InternalGrading.isGeneratedInDegree_iff, hpiece]
  rw [GradedProjectiveResolution.isLinear_iff, GradedProjectiveResolution.isLinear_iff]
  exact forall_congr' hgen

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
