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

`GradedProjectiveResolution.exists_isMinimal_of_forall_cover` assembles a minimal resolution from
any supply of minimal projective surjections that is stable under passing to kernels.

Any two minimal graded projective resolutions with bounded-below terms are canonically isomorphic
as chain complexes (`GradedProjectiveResolution.IsMinimal.isIso_homotopyEquiv_hom`), yielding
termwise graded isomorphisms (`GradedProjectiveResolution.IsMinimal.termObjIso` and
`GradedProjectiveResolution.IsMinimal.termObjIsoOfModuleFinite`). The key input is the
local-nilpotency Nakayama criterion `GradedModuleCat.isIso_of_sub_mem_positive_smul_top`: any
graded endomorphism of a bounded-below graded module congruent to the identity modulo `A₊ P` is an
isomorphism.

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

end GradedProjectiveResolution

/-! ### Uniqueness of minimal graded projective resolutions -/

namespace GradedModuleCat

/-- Any `A`-linear map sends the positive-degree scalar action `A₊ M₁` into `A₊ M₂`. -/
theorem map_mem_positive_smul_top (𝒜 : ℤ → Submodule k A)
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module k M₁] [Module A M₁] [IsScalarTower k A M₁]
    [AddCommMonoid M₂] [Module k M₂] [Module A M₂] [IsScalarTower k A M₂]
    (f : M₁ →ₗ[A] M₂) {x : M₁}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M₁)) :
    f x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M₂) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact add_mem hy hz

/-- **Local-nilpotency isomorphism criterion.** For a bounded-below graded module `P`, any
graded endomorphism `φ : P ⟶ P` congruent to the identity modulo `A₊ P` is an isomorphism:
`id - φ` raises the lower bound of homogeneous components at each iterate, so its powers
eventually annihilate every element of `P`. -/
theorem isIso_of_sub_mem_positive_smul_top {P : GradedModuleCat.{v} 𝒜}
    (b : ℤ) (hbelow : ∀ p < b, P.grading.piece p = ⊥) (φ : P ⟶ P)
    (hφ : ∀ x : P, x - φ.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P)) :
    IsIso φ := by
  let ψ : Module.End A P := LinearMap.id - φ.hom
  have hψ_hom : TauCeti.LinearMap.IsHomogeneous ψ P.grading.piece P.grading.piece 0 :=
    (TauCeti.LinearMap.isHomogeneous_id _).sub φ.isHomogeneous
  have hpow : ∀ (m : ℕ) {p : ℤ}, p < b + m → ∀ x ∈ P.grading.piece p, (ψ ^ m) x = 0 := by
    intro m
    induction m with
    | zero =>
      intro p hp x hx
      rw [Nat.cast_zero, add_zero] at hp
      rw [hbelow p hp, Submodule.mem_bot] at hx
      simp [hx]
    | succ m ih =>
      intro p hp x hx
      have hψx : ψ x ∈ P.grading.piece p := by simpa using hψ_hom.map_mem hx
      have hmem := InternalGrading.decompose_mem_of_mem_positive_smul_top 𝒜
        (LinearMap.ker (ψ ^ m)) (p := p)
        (fun q hq y hy ↦ LinearMap.mem_ker.mpr (ih (by omega) y hy))
        (show ψ x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P) from hφ x)
      rw [_root_.DirectSum.decompose_of_mem_same P.grading.piece hψx, LinearMap.mem_ker] at hmem
      simpa only [pow_succ, mul_apply_eq_comp] using hmem
  have hnil : ∀ x : P, ∃ m : ℕ, (ψ ^ m) x = 0 := fun x ↦ by
    classical
    by_cases hs : (_root_.DirectSum.decompose P.grading.piece x).support.Nonempty
    · refine ⟨((_root_.DirectSum.decompose P.grading.piece x).support.sup' hs id - b).toNat + 1,
        ?_⟩
      calc
        (ψ ^ (((_root_.DirectSum.decompose P.grading.piece x).support.sup' hs id - b).toNat + 1)) x
            = (ψ ^ (((_root_.DirectSum.decompose P.grading.piece x).support.sup' hs id -
                b).toNat + 1))
                (∑ p ∈ (_root_.DirectSum.decompose P.grading.piece x).support,
                  (_root_.DirectSum.decompose P.grading.piece x p : P)) :=
          congrArg _ (_root_.DirectSum.sum_support_decompose P.grading.piece x).symm
        _ = 0 := by
          rw [map_sum]
          refine Finset.sum_eq_zero fun p hp ↦ ?_
          have hle : p ≤ (_root_.DirectSum.decompose P.grading.piece x).support.sup' hs id :=
            Finset.le_sup' id hp
          exact hpow _ (by omega) _ (_root_.DirectSum.decompose P.grading.piece x p).2
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      refine ⟨0, ?_⟩
      rw [← _root_.DirectSum.sum_support_decompose P.grading.piece x, hs, Finset.sum_empty,
        map_zero]
  have hgeom : ∀ m : ℕ,
      φ.hom * (∑ j ∈ Finset.range m, ψ ^ j) = 1 - ψ ^ m ∧
        (∑ j ∈ Finset.range m, ψ ^ j) * φ.hom = 1 - ψ ^ m := by
    intro m
    have hφeq : (φ.hom : Module.End A P) = 1 - ψ := by
      ext x
      simp [ψ]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      refine ⟨?_, ?_⟩
      · calc
          φ.hom * (∑ j ∈ Finset.range m, ψ ^ j + ψ ^ m)
              = (1 - ψ ^ m) + (1 - ψ) * ψ ^ m := by rw [mul_add, ih.1, hφeq]
          _ = 1 - ψ ^ (m + 1) := by rw [sub_mul, one_mul, ← pow_succ']; abel
      · calc
          (∑ j ∈ Finset.range m, ψ ^ j + ψ ^ m) * φ.hom
              = (1 - ψ ^ m) + ψ ^ m * (1 - ψ) := by rw [add_mul, ih.2, hφeq]
          _ = 1 - ψ ^ (m + 1) := by rw [mul_sub, mul_one, ← pow_succ]; abel
  have hinj : Function.Injective φ.hom := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨m, hm⟩ := hnil x
    have h := LinearMap.congr_fun (hgeom m).2 x
    simpa only [mul_apply_eq_comp, LinearMap.mem_ker.mp hx, map_zero,
      LinearMap.sub_apply, one_apply_eq_self, hm, sub_zero] using h.symm
  have hsurj : Function.Surjective φ.hom := fun y ↦ by
    obtain ⟨m, hm⟩ := hnil y
    refine ⟨(∑ j ∈ Finset.range m, ψ ^ j) y, ?_⟩
    have h := LinearMap.congr_fun (hgeom m).1 y
    simpa only [mul_apply_eq_comp, LinearMap.sub_apply, one_apply_eq_self,
      hm, sub_zero] using h
  have : Mono φ := (GradedModuleCat.mono_iff_injective φ).2 hinj
  have : Epi φ := (GradedModuleCat.epi_iff_surjective φ).2 hsurj
  exact isIso_of_mono_of_epi φ

end GradedModuleCat

namespace GradedProjectiveResolution

section Decomposition

variable [DirectSum.Decomposition 𝒜]
  {r r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}

/-- Any chain endomorphism of a minimal resolution homotopic to the identity is an isomorphism
in every bounded-below homological degree. -/
private theorem IsMinimal.isIso_f_of_homotopy_id (hr : r.IsMinimal)
    {f : r.toProjectiveResolution.complex ⟶ r.toProjectiveResolution.complex}
    (h : Homotopy f (𝟙 r.toProjectiveResolution.complex)) {n : ℕ}
    (b : ℤ) (hb : ∀ p < b, (r.grading n).piece p = ⊥) :
    IsIso (f.f n) := by
  let e := r.toProjectiveResolutionXIso n
  let φ : r.termObj n ⟶ r.termObj n := e.inv ≫ f.f n ≫ e.hom
  have hφ_iso : IsIso φ := by
    refine GradedModuleCat.isIso_of_sub_mem_positive_smul_top b hb φ fun x ↦ ?_
    have hcomm : φ = e.inv ≫ dNext n h.hom ≫ e.hom +
        e.inv ≫ prevD n h.hom ≫ e.hom + 𝟙 (r.termObj n) := by
      simp [φ, h.comm n]
    have hprev : ((e.inv ≫ prevD n h.hom ≫ e.hom).hom x) ∈
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) := by
      rw [Homotopy.prevD_chainComplex, r.toProjectiveResolution_complex_d n]
      simp only [e, Category.assoc, Iso.inv_hom_id, Category.comp_id, GradedModuleCat.hom_comp,
        LinearMap.comp_apply]
      exact isMinimal_iff.mp hr n _
    have hdnext : ((e.inv ≫ dNext n h.hom ≫ e.hom).hom x) ∈
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) := by
      cases n with
      | zero =>
        rw [Homotopy.dNext_zero_chainComplex]
        simp
      | succ m =>
        rw [Homotopy.dNext_succ_chainComplex, r.toProjectiveResolution_complex_d m]
        simp only [e, Category.assoc, Iso.inv_hom_id_assoc, GradedModuleCat.hom_comp,
          LinearMap.comp_apply]
        exact GradedModuleCat.map_mem_positive_smul_top 𝒜 _ <|
          GradedModuleCat.map_mem_positive_smul_top 𝒜 _ <|
          GradedModuleCat.map_mem_positive_smul_top 𝒜 _ (isMinimal_iff.mp hr m x)
    have hsub : x - φ.hom x = -((e.inv ≫ dNext n h.hom ≫ e.hom).hom x +
        (e.inv ≫ prevD n h.hom ≫ e.hom).hom x) := by
      rw [hcomm]
      simp [sub_eq_add_neg, add_comm]
    rw [hsub]
    exact neg_mem (add_mem hdnext hprev)
  have hfac : f.f n = e.hom ≫ φ ≫ e.inv := by simp [φ]
  rw [hfac]
  infer_instance

/-- **Minimal resolutions with bounded-below terms are uniquely isomorphic in each degree.**
Every component of the chain-homotopy comparison between two minimal resolutions of `M` is an
isomorphism whenever both terms in that homological degree are bounded below. -/
theorem IsMinimal.isIso_homotopyEquiv_hom_f (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    {n : ℕ} (b₁ b₂ : ℤ) (hb₁ : ∀ p < b₁, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ p < b₂, (r₂.grading n).piece p = ⊥) :
    IsIso ((ProjectiveResolution.homotopyEquiv r₁.toProjectiveResolution
      r₂.toProjectiveResolution).hom.f n) := by
  let e := ProjectiveResolution.homotopyEquiv r₁.toProjectiveResolution r₂.toProjectiveResolution
  have h₁ : IsIso ((e.hom ≫ e.inv).f n) :=
    hr₁.isIso_f_of_homotopy_id e.homotopyHomInvId b₁ hb₁
  have h₂ : IsIso ((e.inv ≫ e.hom).f n) :=
    hr₂.isIso_f_of_homotopy_id e.homotopyInvHomId b₂ hb₂
  rw [HomologicalComplex.comp_f] at h₁ h₂
  let r_inv := e.inv.f n ≫ inv (e.hom.f n ≫ e.inv.f n)
  let l_inv := inv (e.inv.f n ≫ e.hom.f n) ≫ e.inv.f n
  have hr_id : e.hom.f n ≫ r_inv = 𝟙 _ := by
    simp [r_inv, ← Category.assoc]
  have hl_id : l_inv ≫ e.hom.f n = 𝟙 _ := by
    simp [l_inv]
  have hlr : l_inv = r_inv := by
    calc
      l_inv = l_inv ≫ (e.hom.f n ≫ r_inv) := by rw [hr_id, Category.comp_id]
      _ = (l_inv ≫ e.hom.f n) ≫ r_inv := (Category.assoc _ _ _).symm
      _ = r_inv := by rw [hl_id, Category.id_comp]
  exact ⟨⟨r_inv, hr_id, hlr ▸ hl_id⟩⟩

/-- **Uniqueness of minimal graded projective resolutions up to isomorphism of complexes.**
When all terms of two minimal resolutions of `M` are bounded below, the canonical comparison
chain map between them is an isomorphism of chain complexes. -/
theorem IsMinimal.isIso_homotopyEquiv_hom (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    (b₁ b₂ : ℕ → ℤ) (hb₁ : ∀ n p, p < b₁ n → (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ n p, p < b₂ n → (r₂.grading n).piece p = ⊥) :
    IsIso (ProjectiveResolution.homotopyEquiv r₁.toProjectiveResolution
      r₂.toProjectiveResolution).hom := by
  have (n : ℕ) : IsIso ((ProjectiveResolution.homotopyEquiv r₁.toProjectiveResolution
      r₂.toProjectiveResolution).hom.f n) :=
    hr₁.isIso_homotopyEquiv_hom_f hr₂ (b₁ n) (b₂ n) (hb₁ n) (hb₂ n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Termwise graded isomorphism between bounded-below minimal resolutions.** -/
noncomputable def IsMinimal.termObjIso (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal)
    {n : ℕ} (b₁ b₂ : ℤ) (hb₁ : ∀ p < b₁, (r₁.grading n).piece p = ⊥)
    (hb₂ : ∀ p < b₂, (r₂.grading n).piece p = ⊥) :
    r₁.termObj n ≅ r₂.termObj n := by
  have := hr₁.isIso_homotopyEquiv_hom_f hr₂ b₁ b₂ hb₁ hb₂
  exact (r₁.toProjectiveResolutionXIso n).symm ≪≫
    asIso ((ProjectiveResolution.homotopyEquiv r₁.toProjectiveResolution
      r₂.toProjectiveResolution).hom.f n) ≪≫
    r₂.toProjectiveResolutionXIso n

end Decomposition

/-- **Termwise graded isomorphism of minimal resolutions with finitely generated terms.** Over a
nonnegatively graded algebra, finitely generated terms are automatically bounded below, so any two
minimal resolutions of `M` with finitely generated `n`th terms have isomorphic `n`th graded
objects. Neither a base field nor finite dimensionality over the base ring is required. -/
noncomputable def IsMinimal.termObjIsoOfModuleFinite [GradedAlgebra 𝒜]
    {r₁ r₂ : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading}
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (hr₁ : r₁.IsMinimal) (hr₂ : r₂.IsMinimal) (n : ℕ)
    [Module.Finite A (r₁.X n)] [Module.Finite A (r₂.X n)] :
    r₁.termObj n ≅ r₂.termObj n := by
  have hb₁ := (r₁.grading n).exists_piece_eq_bot_of_lt 𝒜 hneg
  have hb₂ := (r₂.grading n).exists_piece_eq_bot_of_lt 𝒜 hneg
  exact hr₁.termObjIso hr₂ hb₁.choose hb₂.choose hb₁.choose_spec hb₂.choose_spec

end GradedProjectiveResolution

end TauCeti
