/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Biprod
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Images
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finite-type quasi-coherent submodules

Finitely many global sections of a quasi-coherent `𝒪_X`-module `N` lie in a quasi-coherent
submodule of `N` of finite type, the image of the corresponding morphism `𝒪_X^n ⟶ N`, and any
two finite-type quasi-coherent submodules of `N` lie in a third. On an affine scheme these
submodules exhaust `N`: a quasi-coherent submodule through which every finite-type
quasi-coherent submodule factors is everything.

More precisely, on an affine scheme `X`, let `V ⊆ X` be a quasi-compact open over which `N` is of
finite type. Then some finite-type quasi-coherent submodule of `N` is all of `N` over `V`. Over a
basic open `D(f)` this holds because each section over `D(f)` times a power of `f` is the
restriction of a global section, and `f` is invertible on `D(f)`; a quasi-compact `V` is a finite
union of basic opens, and the submodules found for each of them lie in a common one. This is the
affine input of the extension of finite-type quasi-coherent submodules along quasi-compact open
immersions into quasi-compact quasi-separated schemes.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_sections`: finitely many global
  sections of a quasi-coherent module lie in a quasi-coherent submodule of finite type.
* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_factors`: the finite-type
  quasi-coherent submodules of a quasi-coherent module form a directed family.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_mono_of_forall_isFiniteType_factors`: on an affine
  scheme, a quasi-coherent submodule containing every finite-type quasi-coherent submodule is
  everything.
* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_basicOpen`: on an affine scheme,
  finitely many sections over a basic open lie in a finite-type quasi-coherent submodule.
* `AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_mono_isIso_restrict`: on an affine
  scheme, a quasi-coherent module of finite type over a quasi-compact open has a finite-type
  quasi-coherent submodule that is everything over that open.

## References

* The Stacks Project, Lemma 28.22.3 (Tag 01PG), the affine case, and the proof of
  Lemma 28.23.2 (Tag 01PF).
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Every finite family of global sections of a quasi-coherent module `N` lies in a quasi-coherent
submodule of `N` of finite type, namely the image of the corresponding morphism `𝒪_X^I ⟶ N`. -/
theorem exists_isFiniteType_mono_sections {I : Type u} [Finite I] {N : X.Modules}
    [N.IsQuasicoherent] (s : I → N.sections) :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i)
      (t : I → N'.sections), ∀ k, SheafOfModules.sectionsMap i (t k) = s k := by
  let F : X.Modules := SheafOfModules.free I
  have : F.IsFinitePresentation :=
    inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) I).IsFinitePresentation
  let φ : F ⟶ N := N.freeHomEquiv.symm s
  refine ⟨image φ, inferInstance, inferInstance, image.ι φ, inferInstance,
    fun k ↦ SheafOfModules.sectionsMap (factorThruImage φ) (SheafOfModules.freeSection k),
    fun k ↦ ?_⟩
  calc _ = N.freeHomEquiv (factorThruImage φ ≫ image.ι φ) k := rfl
    _ = N.freeHomEquiv φ k := congrArg (N.freeHomEquiv · k) (image.fac φ)
    _ = s k := congrFun (N.freeHomEquiv.apply_symm_apply s) k

/-- The finite-type quasi-coherent submodules of a quasi-coherent module form a directed family:
any two of them lie in a third, namely the image of their direct sum. -/
theorem exists_isFiniteType_mono_factors {N N₁ N₂ : X.Modules} [N.IsQuasicoherent]
    [N₁.IsQuasicoherent] [N₁.IsFiniteType] [N₂.IsQuasicoherent] [N₂.IsFiniteType]
    (i₁ : N₁ ⟶ N) (i₂ : N₂ ⟶ N) :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i)
      (g₁ : N₁ ⟶ N') (g₂ : N₂ ⟶ N'), g₁ ≫ i = i₁ ∧ g₂ ≫ i = i₂ :=
  ⟨image (biprod.desc i₁ i₂), inferInstance, inferInstance, image.ι _, inferInstance,
    biprod.inl ≫ factorThruImage _, biprod.inr ≫ factorThruImage _, by simp, by simp⟩

/-- On an affine scheme, a quasi-coherent module is the union of its finite-type quasi-coherent
submodules: a quasi-coherent submodule `M` of a quasi-coherent `N` through which every finite-type
quasi-coherent submodule of `N` factors is all of `N`. -/
theorem isIso_of_mono_of_forall_isFiniteType_factors [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (i : M ⟶ N) [Mono i]
    (h : ∀ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i' : N' ⟶ N),
      Mono i' → ∃ g : N' ⟶ M, g ≫ i = i') : IsIso i := by
  -- Every global section `x` of `N` lies in a finite-type quasi-coherent submodule, hence in `M`.
  refine isIso_of_mono_of_surjective_sectionsFunctor_map_top i fun x ↦ ?_
  obtain ⟨N', _, _, i', _, t, ht⟩ :=
    exists_isFiniteType_mono_sections (I := PUnit.{u + 1}) fun _ ↦ N.sectionsEquivTop.symm x
  obtain ⟨g, rfl⟩ := h N' ‹_› ‹_› i' ‹_›
  refine ⟨M.sectionsEquivTop (SheafOfModules.sectionsMap g (t ⟨⟩)), ?_⟩
  have := (congrArg N.sectionsEquivTop (ht ⟨⟩)).trans (N.sectionsEquivTop.apply_symm_apply x)
  -- `sectionsFunctor ⊤` applies `Hom.app ⊤`, and `(g ≫ i).app ⊤` is `g.app ⊤ ≫ i.app ⊤`.
  rw [sectionsEquivTop_sectionsMap] at this
  rwa [sectionsEquivTop_sectionsMap]

/-- On an affine scheme `X`, finitely many sections of a quasi-coherent module `N` over a basic
open `V = D(f)` lie in a finite-type quasi-coherent submodule of `N`. -/
theorem exists_isFiniteType_mono_basicOpen [IsAffine X] {I : Type u} [Finite I] {N : X.Modules}
    [N.IsQuasicoherent] (f : Γ(X, ⊤)) {V : X.Opens} (hV : X.basicOpen f = V) (s : I → Γ(N, V)) :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i),
      ∀ k, ∃ x : Γ(N', V), i.app V x = s k := by
  subst hV
  -- Each `f ^ n • s k` is the restriction of a global section `y k`.
  choose n y hy using fun k ↦
    N.exists_pow_smul_eq_map (isAffineOpen_top X) f rfl (X.basicOpen_le f) (s k)
  obtain ⟨N', _, _, i, _, t, ht⟩ :=
    exists_isFiniteType_mono_sections fun k ↦ N.sectionsEquivTop.symm (y k)
  refine ⟨N', inferInstance, inferInstance, i, inferInstance, fun k ↦ ?_⟩
  -- `f ^ n` is invertible on `D(f)`.
  obtain ⟨g, hg⟩ : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n k) :=
    (X.toRingedSpace.isUnit_res_basicOpen f).pow (n k)
  let x : Γ(N', X.basicOpen f) := (t k).val (Opposite.op (X.basicOpen f))
  refine ⟨(g⁻¹ : (Γ(X, X.basicOpen f))ˣ).1 • x, ?_⟩
  have h : i.app _ x = N.presheaf.map (homOfLE (X.basicOpen_le f)).op (y k) := by
    have := congrArg (fun σ : N.sections ↦ σ.val (Opposite.op (X.basicOpen f))) (ht k)
    rwa [sectionsEquivTop_symm_val] at this
  rw [Hom.app_smul, h, ← hy k, ← hg, smul_smul, Units.inv_mul, one_smul]

/-- On an affine scheme `X`, a quasi-coherent module `N` of finite type over a basic open `D(f)`
has a finite-type quasi-coherent submodule that is all of `N` over `D(f)`. Here `D(f)` is the
image of an open immersion `j : U ⟶ X`, so the statement is about the restriction along `j`. -/
theorem exists_isFiniteType_mono_isIso_restrict_basicOpen [IsAffine X] {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (f : Γ(X, ⊤)) (hf : X.basicOpen f = j ''ᵁ ⊤)
    {N : X.Modules} [N.IsQuasicoherent] [(N.restrict j).IsFiniteType] :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i),
      IsIso ((restrictFunctor j).map i) := by
  -- `U` is isomorphic to the affine open `D(f)`.
  have : IsAffine U := by
    have h := (isAffineOpen_top X).basicOpen f
    rw [hf, j.isAffineOpen_iff_of_isOpenImmersion] at h
    have : IsAffine (⊤ : U.Opens) := h
    exact IsAffine.of_isIso U.topIso.inv
  -- Finitely many generators of the sections of `N` over `D(f)` lie in a submodule `N'`.
  have := finite_sections_of_isAffineOpen (N.restrict j) ⊤ (isAffineOpen_top _)
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Γ(U, ⊤)) (M := Γ(N.restrict j, ⊤))
  obtain ⟨N', _, _, i, _, hi⟩ :=
    exists_isFiniteType_mono_basicOpen f hf fun k : S ↦ (k.1 : Γ(N, j ''ᵁ ⊤))
  refine ⟨N', inferInstance, inferInstance, i, inferInstance, ?_⟩
  let φ := (restrictFunctor j).map i
  -- `restrictFunctor` is a right adjoint, so it preserves monomorphisms.
  have : Mono φ := (restrictFunctor j).map_mono i
  refine isIso_of_mono_of_surjective_sectionsFunctor_map_top φ ?_
  have h : Submodule.span Γ(U, ⊤) (S : Set Γ(N.restrict j, ⊤)) ≤
      LinearMap.range ((sectionsFunctor ⊤).map φ).hom :=
    Submodule.span_le.mpr fun k hk ↦ hi ⟨k, hk⟩
  exact fun y ↦ h (hS ▸ Submodule.mem_top)

/-- **Finite-type submodules over a quasi-compact open of an affine scheme.** Let `X` be affine,
`N` a quasi-coherent `𝒪_X`-module and `V ⊆ X` a quasi-compact open such that `N|_V` is of finite
type. Then there is a finite-type quasi-coherent submodule `i : N' ⟶ N` that is an isomorphism
over `V`. -/
theorem exists_isFiniteType_mono_isIso_restrict [IsAffine X] {N : X.Modules} [N.IsQuasicoherent]
    (V : X.Opens) (hV : IsCompact (V : Set X)) [(N.restrict V.ι).IsFiniteType] :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i),
      IsIso ((restrictFunctor V.ι).map i) := by
  classical
  -- `V` is a finite union of basic opens `D(f) ⊆ V`, seen as the opens `W f` of `V`.
  obtain ⟨s, hs, hsV⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen.mp ⟨hV, V.isOpen⟩
  have hle (f : Γ(X, ⊤)) (hf : f ∈ s) : X.basicOpen f ≤ V := fun x hx ↦ by
    rw [← SetLike.mem_coe, hsV]
    exact Set.mem_biUnion hf hx
  let W (f : Γ(X, ⊤)) : V.toScheme.Opens := V.ι ⁻¹ᵁ X.basicOpen f
  -- Over each `W f` there is a finite-type submodule that is everything there.
  have key (f : Γ(X, ⊤)) (hf : f ∈ s) :
      ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N)
        (_ : Mono i), IsIso ((restrictFunctor ((W f).ι ≫ V.ι)).map i) := by
    have : ((restrictFunctor V.ι ⋙ restrictFunctor (W f).ι).obj N).IsFiniteType :=
      inferInstanceAs ((N.restrict V.ι).restrict (W f).ι).IsFiniteType
    have : (N.restrict ((W f).ι ≫ V.ι)).IsFiniteType :=
      SheafOfModules.IsFiniteType.of_iso (R := (W f).toScheme.ringCatSheaf)
        ((restrictFunctorComp (W f).ι V.ι).app N).symm
    refine exists_isFiniteType_mono_isIso_restrict_basicOpen _ f ?_
    rw [Scheme.Hom.comp_image, Scheme.Opens.ι_image_top,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hle f hf)]
  -- Finitely many of them lie in a common one, by directedness.
  have comb (t : Finset Γ(X, ⊤)) (ht : ∀ f ∈ t, f ∈ s) :
      ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N)
        (_ : Mono i), ∀ f ∈ t, IsIso ((restrictFunctor ((W f).ι ≫ V.ι)).map i) := by
    induction t using Finset.induction_on with
    | empty =>
      obtain ⟨N', h₁, h₂, i, h₃, -⟩ :=
        exists_isFiniteType_mono_sections (N := N) (I := PEmpty.{u + 1}) PEmpty.elim
      exact ⟨N', h₁, h₂, i, h₃, by simp⟩
    | insert a t ha ih =>
      obtain ⟨N₁, _, _, i₁, _, h₁⟩ := key a (ht a (Finset.mem_insert_self a t))
      obtain ⟨N₂, _, _, i₂, _, h₂⟩ := ih fun f hf ↦ ht f (Finset.mem_insert_of_mem hf)
      obtain ⟨N', _, _, i, _, g₁, g₂, hg₁, hg₂⟩ := exists_isFiniteType_mono_factors i₁ i₂
      refine ⟨N', inferInstance, inferInstance, i, inferInstance, fun f hf ↦ ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact isIso_restrictFunctor_map_of_fac _ g₁ hg₁
      · have := h₂ f hf
        exact isIso_restrictFunctor_map_of_fac _ g₂ hg₂
  obtain ⟨N', _, _, i, _, hi⟩ := comb hs.toFinset fun f hf ↦ hs.mem_toFinset.mp hf
  refine ⟨N', inferInstance, inferInstance, i, inferInstance, ?_⟩
  -- The opens `W f` cover `V`, and `i` is an isomorphism over each of them.
  let U : hs.toFinset → V.toScheme.Opens := fun f ↦ W f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : V.ι x ∈ V.ι.opensRange := ⟨x, rfl⟩
    rw [Scheme.Opens.opensRange_ι, ← SetLike.mem_coe, hsV] at hx
    obtain ⟨f, hf, hfx⟩ := Set.mem_iUnion₂.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hs.mem_toFinset.mpr hf⟩, hfx⟩
  refine (isIso_iff_of_isOpenCover hU _).mpr fun f ↦ ?_
  have := hi f.1 f.2
  have : IsIso ((restrictFunctor (W f.1).ι).map ((restrictFunctor V.ι).map i)) :=
    (NatIso.isIso_map_iff (restrictFunctorComp (W f.1).ι V.ι) i).mp this
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (W f.1).ι) _).mp this

end AlgebraicGeometry.Scheme.Modules
