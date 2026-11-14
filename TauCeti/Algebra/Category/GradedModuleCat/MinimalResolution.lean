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
# Ext and uniqueness for minimal graded resolutions

For a minimal graded projective resolution, every differential has image in the positive-degree
algebra action. Against a target annihilated by that action, the Hom complex has zero
differentials. Its terms therefore compute Ext in every degree, including degree zero.

`GradedProjectiveResolution.IsMinimal.extLinearEquiv` identifies graded Hom from the `n`th
resolution term with `Extⁿ`. The vanishing characterization converts diagonal Ext vanishing
into vanishing of graded Hom, without assuming the resolution is linear. The equivalence is
natural in the target. Neither nonnegative grading nor semisimplicity is needed for this
computation; those hypotheses enter when detecting generating degrees or constructing minimal
resolutions.

Any two bounded-below minimal graded projective resolutions of the same graded module are
canonically chain-isomorphic (`GradedProjectiveResolution.IsMinimal.complexIso`), and in fact any
augmentation-compatible chain map between them is already an isomorphism: homotopic chain maps
between minimal resolutions agree modulo `A₊`, so graded Nakayama makes any homotopy equivalence an
isomorphism in every homological degree. Over a nonnegatively decomposed ring, finite generation of
the resolution terms supplies the lower bounds automatically
(`GradedProjectiveResolution.IsMinimal.termObjIsoOfModuleFinite`).

`GradedProjectiveResolution.exists_isMinimal_of_forall_cover` assembles a minimal resolution from
any supply of minimal projective surjections that is stable under passing to kernels.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for the minimal-resolution computation underlying the diagonal Ext criterion.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded Nakayama
  and minimal graded projective resolutions.
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

end GradedProjectiveResolution

/-! ### Uniqueness up to chain isomorphism -/

namespace GradedModuleCat

/-- On a bounded-below graded module, any graded endomorphism congruent to the identity modulo
`A₊ M` is an isomorphism in `GradedModuleCat`. -/
theorem isIso_of_sub_id_mem_positive_smul_top {M : GradedModuleCat.{v} 𝒜} (b : ℤ)
    (hbelow : ∀ p < b, M.grading.piece p = ⊥) (f : M ⟶ M)
    (hsub : ∀ x, f.hom x - x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    IsIso f :=
  (isIso_iff_bijective f).mpr <|
    InternalGrading.bijective_of_sub_id_mem_positive_smul_top (H := M.grading) 𝒜 b hbelow
      f.isHomogeneous hsub

end GradedModuleCat

namespace GradedProjectiveResolution

variable [DirectSum.Decomposition 𝒜]
  {r r' : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}

omit [DirectSum.Decomposition 𝒜] in
private theorem map_mem_positive_smul_top {X Y : GradedModuleCat.{v} 𝒜} (g : X ⟶ Y) {x : X}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k X)) :
    g.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k Y) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_)
    (fun y z hy hz ↦ by simpa only [map_add] using Submodule.add_mem _ hy hz)
  rw [map_smul]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

private theorem IsMinimal.complex_d_apply_mem (hr : r.IsMinimal) (i j : ℕ)
    (x : r.toProjectiveResolution.complex.X i) :
    (r.toProjectiveResolution.complex.d i j).hom x ∈
      (⨆ (d : ℤ) (_ : 0 < d), 𝒜 d) •
        (⊤ : Submodule k (r.toProjectiveResolution.complex.X j)) := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := hij
    rw [r.toProjectiveResolution_complex_d, GradedModuleCat.hom_comp, GradedModuleCat.hom_comp]
    exact map_mem_positive_smul_top (r.toProjectiveResolutionXIso j).inv
      (isMinimal_iff.mp hr j _)
  · simp [r.toProjectiveResolution.complex.shape i j hij]

/-- Homotopic chain maps between minimal graded projective resolutions agree modulo `A₊` in every
homological degree. -/
theorem IsMinimal.sub_mem_of_homotopy (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    {f g : r.toProjectiveResolution.complex ⟶ r'.toProjectiveResolution.complex}
    (h : Homotopy f g) (n : ℕ) (x : r.toProjectiveResolution.complex.X n) :
    (f.f n).hom x - (g.f n).hom x ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) •
        (⊤ : Submodule k (r'.toProjectiveResolution.complex.X n)) := by
  have hd := hr.complex_d_apply_mem n ((ComplexShape.down ℕ).next n) x
  have hm := map_mem_positive_smul_top (h.hom ((ComplexShape.down ℕ).next n) n) hd
  have hp := hr'.complex_d_apply_mem ((ComplexShape.down ℕ).prev n) n
    ((h.hom n ((ComplexShape.down ℕ).prev n)).hom x)
  have he := congrArg
    (fun a : r.toProjectiveResolution.complex.X n ⟶ r'.toProjectiveResolution.complex.X n ↦
      a.hom x) (h.comm n)
  simp only [dNext, prevD, AddMonoidHom.mk'_apply, GradedModuleCat.hom_add,
    GradedModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply] at he
  rw [he, add_sub_cancel_right]
  exact Submodule.add_mem _ hm hp

/-- A chain endomorphism of a bounded-below minimal graded projective resolution that is homotopic
to the identity is an isomorphism of chain complexes. -/
theorem IsMinimal.isIso_of_homotopy_id (hr : r.IsMinimal) (b : ℕ → ℤ)
    (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥)
    {f : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (h : Homotopy f (𝟙 r.toProjectiveResolution.complex)) : IsIso f := by
  have (n : ℕ) : IsIso (f.f n) := by
    let e := r.toProjectiveResolutionXIso n
    let φ : r.termObj n ⟶ r.termObj n := e.inv ≫ f.f n ≫ e.hom
    have : IsIso φ :=
      GradedModuleCat.isIso_of_sub_id_mem_positive_smul_top (b n) (hbelow n) φ fun x ↦ by
        have hsub : (f.f n).hom (e.inv.hom x) - e.inv.hom x ∈
            (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) •
              (⊤ : Submodule k (r.toProjectiveResolution.complex.X n)) := by
          simpa using hr.sub_mem_of_homotopy hr h n (e.inv.hom x)
        have hmap := map_mem_positive_smul_top e.hom hsub
        have hid := congrArg (fun u : r.termObj n ⟶ r.termObj n ↦ u.hom x) e.inv_hom_id
        simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply, GradedModuleCat.hom_id,
          LinearMap.id_apply] at hid
        simpa [φ, map_sub, hid] using hmap
    have hfeq : f.f n = e.hom ≫ φ ≫ e.inv := by simp [φ]
    rw [hfeq]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components f

/-- Any homotopy equivalence between bounded-below minimal graded projective resolutions is an
isomorphism on its forward chain map. -/
theorem IsMinimal.isIso_hom_of_homotopyEquiv (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (b : ℕ → ℤ) (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥)
    (b' : ℕ → ℤ) (hbelow' : ∀ n p, p < b' n → (r'.grading n).piece p = ⊥)
    (e : HomotopyEquiv r.toProjectiveResolution.complex r'.toProjectiveResolution.complex) :
    IsIso e.hom := by
  have := hr.isIso_of_homotopy_id b hbelow e.homotopyHomInvId
  have := hr'.isIso_of_homotopy_id b' hbelow' e.homotopyInvHomId
  have : Mono e.hom := mono_of_mono e.hom e.inv
  have : IsSplitEpi e.hom := IsSplitEpi.mk'
    { section_ := inv (e.inv ≫ e.hom) ≫ e.inv
      id := by simp }
  exact isIso_of_mono_of_isSplitEpi e.hom

/-- **Rigidity of minimal graded projective resolutions.** Any chain map compatible with the
augmentations between two bounded-below minimal graded projective resolutions of `M` is an
isomorphism of chain complexes. -/
theorem IsMinimal.isIso_of_comm (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (b : ℕ → ℤ) (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥)
    (b' : ℕ → ℤ) (hbelow' : ∀ n p, p < b' n → (r'.grading n).piece p = ⊥)
    (f : r.toProjectiveResolution.complex ⟶ r'.toProjectiveResolution.complex)
    (hf : f ≫ r'.toProjectiveResolution.π = r.toProjectiveResolution.π) : IsIso f := by
  simpa only [ProjectiveResolution.homotopyEquivOfComm_hom] using
    hr.isIso_hom_of_homotopyEquiv hr' b hbelow b' hbelow'
      (ProjectiveResolution.homotopyEquivOfComm r.toProjectiveResolution
        r'.toProjectiveResolution f hf)

/-- **Uniqueness of minimal graded projective resolutions up to chain isomorphism.** Two
bounded-below minimal graded projective resolutions of `M` have isomorphic underlying chain
complexes via the comparison lift of `𝟙 M`. -/
noncomputable def IsMinimal.complexIso (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (b : ℕ → ℤ) (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥)
    (b' : ℕ → ℤ) (hbelow' : ∀ n p, p < b' n → (r'.grading n).piece p = ⊥) :
    r.toProjectiveResolution.complex ≅ r'.toProjectiveResolution.complex := by
  have := hr.isIso_hom_of_homotopyEquiv hr' b hbelow b' hbelow'
    (ProjectiveResolution.homotopyEquiv r.toProjectiveResolution r'.toProjectiveResolution)
  exact asIso
    (ProjectiveResolution.homotopyEquiv r.toProjectiveResolution r'.toProjectiveResolution).hom

/-- The chain isomorphism between minimal resolutions commutes with the augmentations. -/
@[reassoc (attr := simp)]
theorem IsMinimal.complexIso_hom_comp_π (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (b : ℕ → ℤ) (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥)
    (b' : ℕ → ℤ) (hbelow' : ∀ n p, p < b' n → (r'.grading n).piece p = ⊥) :
    (hr.complexIso hr' b hbelow b' hbelow').hom ≫ r'.toProjectiveResolution.π =
      r.toProjectiveResolution.π := by
  simp [IsMinimal.complexIso, ProjectiveResolution.homotopyEquiv]

/-- Corresponding terms of two bounded-below minimal graded projective resolutions of `M` are
isomorphic as graded modules. -/
noncomputable def IsMinimal.termObjIso (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (b : ℕ → ℤ) (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥)
    (b' : ℕ → ℤ) (hbelow' : ∀ n p, p < b' n → (r'.grading n).piece p = ⊥) (n : ℕ) :
    r.termObj n ≅ r'.termObj n :=
  (r.toProjectiveResolutionXIso n).symm ≪≫
    (HomologicalComplex.eval _ _ n).mapIso (hr.complexIso hr' b hbelow b' hbelow') ≪≫
    r'.toProjectiveResolutionXIso n

/-- Over a nonnegatively decomposed ring, two minimal graded projective resolutions of `M` with
finitely generated terms have isomorphic underlying chain complexes. -/
noncomputable def IsMinimal.complexIsoOfModuleFinite
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hr : r.IsMinimal) (hr' : r'.IsMinimal) :
    r.toProjectiveResolution.complex ≅ r'.toProjectiveResolution.complex := by
  classical
  choose b hb using fun n ↦
    InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite (G := r.grading n) 𝒜 hneg
  choose b' hb' using fun n ↦
    InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite (G := r'.grading n) 𝒜 hneg
  exact hr.complexIso hr' b hb b' hb'

/-- Over a nonnegatively decomposed ring, corresponding terms of two minimal graded projective
resolutions of `M` with finitely generated terms are isomorphic as graded modules. -/
noncomputable def IsMinimal.termObjIsoOfModuleFinite
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hr : r.IsMinimal) (hr' : r'.IsMinimal) (n : ℕ) :
    r.termObj n ≅ r'.termObj n :=
  (r.toProjectiveResolutionXIso n).symm ≪≫
    (HomologicalComplex.eval _ _ n).mapIso (hr.complexIsoOfModuleFinite hneg hr') ≪≫
    r'.toProjectiveResolutionXIso n

end GradedProjectiveResolution

end TauCeti
