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
# Ext and uniqueness of minimal graded resolutions

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

When the terms of a minimal resolution have gradings bounded below, any chain endomorphism
homotopic to the identity is an isomorphism: graded Nakayama shows each component is surjective,
projectivity splits it, and graded Nakayama on the kernel shows it is injective. Consequently, any
two minimal graded projective resolutions with bounded-below terms — in particular, with finitely
generated terms over a nonnegatively graded algebra — are isomorphic as chain complexes and
term-by-term in `GradedModuleCat` (`GradedProjectiveResolution.IsMinimal.isoOfMinimal`,
`GradedProjectiveResolution.IsMinimal.termObjIso`).

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for the minimal-resolution computation underlying the diagonal Ext criterion.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded
  projectives and graded Nakayama.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 2.4, for computing Ext
  from projective resolutions and homotopy uniqueness of projective resolutions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {M N N' : GradedModuleCat.{v} 𝒜}

namespace GradedModuleCat

/-- On a projective graded module with grading bounded below, any homogeneous endomorphism that
agrees with the identity modulo `A₊ P` is an isomorphism in `GradedModuleCat 𝒜`. -/
theorem isIso_of_sub_id_mem_positive_smul_top
    {P : GradedModuleCat.{v} 𝒜} [Projective P] {b : ℤ} (hb : ∀ p < b, P.grading.piece p = ⊥)
    {f : P ⟶ P}
    (hf : ∀ x : P, f.hom x - x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) :
    IsIso f := by
  have hrange : LinearMap.range f.hom = ⊤ :=
    InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜 (LinearMap.range f.hom)
      f.isHomogeneous.isHomogeneous_range b hb fun p x _ ↦
        Submodule.mem_sup.2 ⟨f.hom x, LinearMap.mem_range_self f.hom x, -(f.hom x - x),
          neg_mem (hf x), by abel⟩
  have hsurj : Function.Surjective f.hom := LinearMap.range_eq_top.1 hrange
  have : Epi f := (epi_iff_surjective f).2 hsurj
  let σ : P ⟶ P := Projective.factorThru (𝟙 P) f
  have hσ : σ ≫ f = 𝟙 P := Projective.factorThru_comp (𝟙 P) f
  let π : P →ₗ[A] kernelObj f :=
    LinearMap.codRestrict (LinearMap.ker f.hom) (LinearMap.id - σ.hom.comp f.hom) fun y ↦ by
      have hy : (σ ≫ f).hom (f.hom y) = f.hom y := by simp [hσ]
      simpa [LinearMap.mem_ker, sub_eq_zero] using hy.symm
  have hker_top :
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (kernelObj f)) = ⊤ := by
    refine top_unique fun z _ ↦ ?_
    have hz : z.1 ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P) := by
      have hz0 : f.hom z.1 = 0 := z.2
      simpa [hz0] using neg_mem (hf z.1)
    have hπz : π z.1 = z := Subtype.ext (by simp [π])
    exact hπz ▸ InternalGrading.map_mem_positive_smul_top 𝒜 π hz
  have hker_below : ∀ p < b, (kernelObj f).grading.piece p = ⊥ := fun p hp ↦
    (Submodule.eq_bot_iff _).2 fun z hz ↦ Subtype.ext <|
      (Submodule.eq_bot_iff _).1 (hb p hp) z.1 ((InternalGrading.mem_ker_piece _ _).1 hz)
  let _ := (kernelObj f).gradedSMul
  have : Subsingleton (kernelObj f) :=
    InternalGrading.subsingleton_of_positive_smul_top_eq_top 𝒜 b hker_below hker_top
  have hinj : Function.Injective f.hom :=
    LinearMap.ker_eq_bot.1 Submodule.eq_bot_of_subsingleton
  exact (isIso_iff_bijective f).2 ⟨hinj, hsurj⟩

end GradedModuleCat

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

private theorem IsMinimal.complex_d_apply_mem (hr : r.IsMinimal) (i j : ℕ)
    (x : r.toProjectiveResolution.complex.X i) :
    (r.toProjectiveResolution.complex.d i j).hom x ∈
      (⨆ (m : ℤ) (_ : 0 < m), 𝒜 m) •
        (⊤ : Submodule k (r.toProjectiveResolution.complex.X j)) := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · obtain rfl : j + 1 = i := hij
    rw [r.toProjectiveResolution_complex_d, GradedModuleCat.hom_comp, GradedModuleCat.hom_comp,
      LinearMap.comp_apply, LinearMap.comp_apply]
    exact InternalGrading.map_mem_positive_smul_top 𝒜 (r.toProjectiveResolutionXIso j).inv.hom
      (isMinimal_iff.mp hr j _)
  · rw [r.toProjectiveResolution.complex.shape i j hij, GradedModuleCat.hom_zero,
      LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- Homotopic chain maps between minimal graded projective resolutions agree modulo `A₊` in every
homological degree. -/
theorem IsMinimal.sub_mem_of_homotopy {r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 N.grading}
    (hr₁ : r.IsMinimal) (hr₂ : r₂.IsMinimal)
    {f g : r.toProjectiveResolution.complex ⟶ r₂.toProjectiveResolution.complex}
    (h : Homotopy f g) (n : ℕ) (x : r.toProjectiveResolution.complex.X n) :
    (f.f n).hom x - (g.f n).hom x ∈
      (⨆ (m : ℤ) (_ : 0 < m), 𝒜 m) •
        (⊤ : Submodule k (r₂.toProjectiveResolution.complex.X n)) := by
  have hd := hr₁.complex_d_apply_mem n ((ComplexShape.down ℕ).next n) x
  have hm := InternalGrading.map_mem_positive_smul_top 𝒜
    (h.hom ((ComplexShape.down ℕ).next n) n).hom hd
  have hp := hr₂.complex_d_apply_mem ((ComplexShape.down ℕ).prev n) n
    ((h.hom n ((ComplexShape.down ℕ).prev n)).hom x)
  have he := congrArg (fun a : r.toProjectiveResolution.complex.X n ⟶
      r₂.toProjectiveResolution.complex.X n ↦ a.hom x) (h.comm n)
  simp only [dNext, prevD, AddMonoidHom.mk'_apply,
    GradedModuleCat.hom_add, GradedModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply] at he
  rw [he, add_sub_cancel_right]
  exact add_mem hm hp

/-- A chain endomorphism homotopic to the identity on a minimal graded projective resolution with
bounded-below terms is an isomorphism. -/
theorem IsMinimal.isIso_of_homotopy_id (hr : r.IsMinimal)
    (hb : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    {f : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (h : Homotopy f (𝟙 _)) : IsIso f := by
  have (n : ℕ) : IsIso (f.f n) := by
    obtain ⟨b, hbn⟩ := hb n
    have hbn' : ∀ p < b, (r.toProjectiveResolution.complex.X n).grading.piece p = ⊥ := fun p hp ↦
      (Submodule.eq_bot_iff _).2 fun x hx ↦ by
        have hx' := (r.toProjectiveResolutionXIso n).hom.isHomogeneous.map_mem hx
        rw [add_zero] at hx'
        exact (GradedModuleCat.mono_iff_injective (r.toProjectiveResolutionXIso n).hom).1
          inferInstance ((Submodule.eq_bot_iff _).1 (hbn p hp) _ hx' |>.trans (map_zero _).symm)
    exact GradedModuleCat.isIso_of_sub_id_mem_positive_smul_top hbn' fun x ↦ by
      simpa using hr.sub_mem_of_homotopy hr h n x
  exact HomologicalComplex.Hom.isIso_of_components f

/-- Any chain homotopy equivalence between minimal graded projective resolutions with
bounded-below terms is an isomorphism on its forward chain map. -/
theorem IsMinimal.isIso_hom_of_homotopyEquiv
    {r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 N.grading}
    (hr₁ : r.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥)
    (e : HomotopyEquiv r.toProjectiveResolution.complex r₂.toProjectiveResolution.complex) :
    IsIso e.hom := by
  have := hr₁.isIso_of_homotopy_id hb₁ e.homotopyHomInvId
  have := hr₂.isIso_of_homotopy_id hb₂ e.homotopyInvHomId
  have : Mono e.hom := mono_of_mono e.hom e.inv
  have : IsSplitEpi e.hom := IsSplitEpi.mk'
    { section_ := inv (e.inv ≫ e.hom) ≫ e.inv
      id := by simp }
  exact isIso_of_mono_of_isSplitEpi e.hom

/-- **Uniqueness of minimal graded projective resolutions.** Any two minimal graded projective
resolutions of `M` whose terms have bounded-below gradings are isomorphic as chain complexes in
`GradedModuleCat 𝒜`. -/
noncomputable def IsMinimal.isoOfMinimal
    {r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) :
    r.toProjectiveResolution.complex ≅ r₂.toProjectiveResolution.complex :=
  have := hr₁.isIso_hom_of_homotopyEquiv hr₂ hb₁ hb₂
    (r.toProjectiveResolution.homotopyEquiv r₂.toProjectiveResolution)
  asIso (r.toProjectiveResolution.homotopyEquiv r₂.toProjectiveResolution).hom

/-- **Termwise uniqueness of minimal graded projective resolutions.** Any two minimal graded
projective resolutions of `M` whose terms have bounded-below gradings have isomorphic terms in
every homological degree. -/
noncomputable def IsMinimal.termObjIso
    {r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hr₁ : r.IsMinimal) (hr₂ : r₂.IsMinimal)
    (hb₁ : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hb₂ : ∀ n, ∃ b : ℤ, ∀ p < b, (r₂.grading n).piece p = ⊥) (n : ℕ) :
    r.termObj n ≅ r₂.termObj n :=
  (r.toProjectiveResolutionXIso n).symm ≪≫
    (HomologicalComplex.eval _ _ n).mapIso (hr₁.isoOfMinimal hr₂ hb₁ hb₂) ≪≫
    r₂.toProjectiveResolutionXIso n

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions of `M` with
finitely generated terms are isomorphic as chain complexes. -/
noncomputable def IsMinimal.isoOfMinimalOfModuleFinite
    {r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r.IsMinimal) (hr₂ : r₂.IsMinimal) :
    r.toProjectiveResolution.complex ≅ r₂.toProjectiveResolution.complex :=
  hr₁.isoOfMinimal hr₂
    (fun n ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg (G := r.grading n))
    (fun n ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg (G := r₂.grading n))

/-- Over a nonnegatively graded algebra, any two minimal graded projective resolutions of `M` with
finitely generated terms have isomorphic terms in every homological degree. -/
noncomputable def IsMinimal.termObjIsoOfModuleFinite
    {r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r₂.X n)]
    (hr₁ : r.IsMinimal) (hr₂ : r₂.IsMinimal) (n : ℕ) :
    r.termObj n ≅ r₂.termObj n :=
  hr₁.termObjIso hr₂
    (fun n ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg (G := r.grading n))
    (fun n ↦ InternalGrading.exists_piece_eq_bot_of_lt_of_moduleFinite 𝒜 hneg (G := r₂.grading n))
    n

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
