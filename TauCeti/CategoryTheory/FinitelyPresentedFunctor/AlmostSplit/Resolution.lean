/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.AlmostSplit.Basic
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.ProjectiveDimension
public import TauCeti.CategoryTheory.AlmostSplit.Uniqueness
public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
import TauCeti.Algebra.Homology.ChainComplex.Exact

/-!
# The projective resolution of a simple functor from an almost-split sequence

For a kernel sequence `X ⟶ Y ⟶ Z` whose last map is right almost split, the simple functor
`S_Z = (-, Z) / rad(-, Z)` has the projective resolution
`0 ⟶ (-, X) ⟶ (-, Y) ⟶ (-, Z) ⟶ S_Z ⟶ 0`.
The differentials are induced by the two original maps, and the augmentation is the radical
quotient. Representables are projective in `mod C`, which is the ambient category used here.

We assume `C` is a nonempty preadditive category with weak kernels and binary biproducts, so
that `mod C` is abelian. In particular the construction applies to any abelian category,
including finitely generated modules over an Artin algebra. The resolution is bounded above by
degree two. When `C` is moreover balanced and the sequence is almost split, every chain
endomorphism of this resolution lifting the identity of `S_Z` is invertible; this is the
minimality property of the resolution.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Cambridge University Press (2006), Theorem IV.6.11.
* H. Enomoto, *Classifications of exact structures and Cohen-Macaulay-finite algebras*,
  Adv. Math. 335 (2018), Proposition A.2.
-/

public section

open CategoryTheory Limits TauCeti ZeroObject

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [HasWeakKernels C] [Nonempty C]

private noncomputable abbrev resolutionTerm (S : ShortComplex C) : ℕ →
    (isFinitelyPresentedFunctor C).FullSubcategory
  | 0 => modYoneda.obj S.X₃
  | 1 => modYoneda.obj S.X₂
  | 2 => modYoneda.obj S.X₁
  | _ + 3 => 0

private noncomputable abbrev resolutionDifferential (S : ShortComplex C) :
    ∀ n, resolutionTerm S (n + 1) ⟶ resolutionTerm S n
  | 0 => modYoneda.map S.g
  | 1 => modYoneda.map S.f
  | _ + 2 => 0

omit [HasBinaryBiproducts C] [HasWeakKernels C] in
private theorem resolutionDifferential_comp (S : ShortComplex C) (n : ℕ) :
    resolutionDifferential S (n + 1) ≫ resolutionDifferential S n = 0 := by
  cases n with
  | zero =>
    dsimp only [resolutionDifferential]
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  | succ n => cases n <;> dsimp only [resolutionDifferential] <;> simp

private noncomputable abbrev resolutionComplex (S : ShortComplex C) :
    ChainComplex (isFinitelyPresentedFunctor C).FullSubcategory ℕ :=
  ChainComplex.of (resolutionTerm S) (resolutionDifferential S) (resolutionDifferential_comp S)

private theorem resolutionComplex_exactAt (S : ShortComplex C)
    (hf : IsLimit (KernelFork.ofι S.f S.zero)) (n : ℕ) :
    (resolutionComplex S).ExactAt (n + 1) := by
  apply ChainComplex.of_exactAt_succ
  cases n with
  | zero =>
    dsimp only [resolutionDifferential, resolutionTerm]
    simpa only [ShortComplex.map] using ShortComplex.exact_of_f_is_kernel (S.map modYoneda)
      ((KernelFork.isLimitMapConeEquiv _ _).1 (isLimitOfPreserves modYoneda hf))
  | succ n =>
    cases n with
    | zero =>
      have : Mono (modYoneda.map S.f) := by
        have : Mono S.f := Fork.IsLimit.mono hf
        infer_instance
      dsimp only [resolutionDifferential, resolutionTerm]
      exact (ShortComplex.exact_iff_mono _ rfl).2 inferInstance
    | succ n =>
      dsimp only [resolutionTerm]
      exact ShortComplex.exact_of_isZero_X₂ _ (isZero_zero _)

/-- The canonical projective resolution of `S_Z`, bounded by degree two, from a kernel sequence
`X ⟶ Y ⟶ Z` with right almost split last map. Its terms in degrees `0, 1, 2` are respectively
`(-, Z), (-, Y), (-, X)`, and its augmentation is `(-, Z) ⟶ S_Z`. -/
noncomputable def simpleFunctorProjectiveResolution (S : ShortComplex C)
    (hg : IsRightAlmostSplit S.g) (hf : IsLimit (KernelFork.ofι S.f S.zero)) :
    ProjectiveResolution (⟨simpleFunctor S.X₃,
      have := hg.isLocalRing_end
      (isFinitelyPresentedFunctor_simpleFunctor_iff S.X₃).2 ⟨S.X₂, S.g, hg⟩⟩ :
        (isFinitelyPresentedFunctor C).FullSubcategory) := by
  have := hg.isLocalRing_end
  let ε : resolutionTerm S 0 ⟶ (⟨simpleFunctor S.X₃,
      (isFinitelyPresentedFunctor_simpleFunctor_iff S.X₃).2 ⟨S.X₂, S.g, hg⟩⟩ :
        (isFinitelyPresentedFunctor C).FullSubcategory) :=
    ObjectProperty.homMk (simpleFunctorπ S.X₃)
  have hε : resolutionDifferential S 0 ≫ ε = 0 := ObjectProperty.hom_ext _
    ((preadditiveYoneda_map_comp_simpleFunctorπ_eq_zero_iff S.g).2 hg.mem_jacobsonRadical)
  have : Epi ε := (isFinitelyPresentedFunctor C).ι.epi_of_epi_map
    (inferInstanceAs (Epi (simpleFunctorπ S.X₃)))
  refine (resolutionComplex S).toProjectiveResolution ε
    ((congrArg (fun d ↦ d ≫ ε)
      (ChainComplex.of_d (resolutionTerm S) (resolutionDifferential S) 0)).trans hε)
    (fun n ↦ ?_) ?_ (resolutionComplex_exactAt S hf)
  · rcases n with _ | _ | _ | n <;>
      dsimp [resolutionComplex, resolutionTerm]
    all_goals infer_instance
  · apply ChainComplex.of_exact_d_one_zero _ _ _ ε hε
    apply ShortComplex.exact_of_g_is_cokernel
    apply isColimitOfReflects (isFinitelyPresentedFunctor C).ι
    exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
      (isRightAlmostSplit_iff_exists_exact_simpleFunctorπ.1 hg).choose_spec.gIsCokernel

variable (S : ShortComplex C) (hg : IsRightAlmostSplit S.g)
  (hf : IsLimit (KernelFork.ofι S.f S.zero))

/-- Degree zero of the simple-functor resolution is `(-, Z)`. -/
noncomputable def simpleFunctorProjectiveResolutionZeroIso :
    (S.simpleFunctorProjectiveResolution hg hf).complex.X 0 ≅ modYoneda.obj S.X₃ :=
  Iso.refl _

/-- Degree one of the simple-functor resolution is `(-, Y)`. -/
noncomputable def simpleFunctorProjectiveResolutionOneIso :
    (S.simpleFunctorProjectiveResolution hg hf).complex.X 1 ≅ modYoneda.obj S.X₂ :=
  Iso.refl _

/-- Degree two of the simple-functor resolution is `(-, X)`. -/
noncomputable def simpleFunctorProjectiveResolutionTwoIso :
    (S.simpleFunctorProjectiveResolution hg hf).complex.X 2 ≅ modYoneda.obj S.X₁ :=
  Iso.refl _

/-- The simple-functor resolution vanishes in degrees above two. -/
theorem isZero_simpleFunctorProjectiveResolution_X (n : ℕ) :
    IsZero ((S.simpleFunctorProjectiveResolution hg hf).complex.X (n + 3)) :=
  isZero_zero _

/-- The first differential is induced by `Y ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem simpleFunctorProjectiveResolution_d_one_zero :
    (S.simpleFunctorProjectiveResolution hg hf).complex.d 1 0 ≫
        (S.simpleFunctorProjectiveResolutionZeroIso hg hf).hom =
      (S.simpleFunctorProjectiveResolutionOneIso hg hf).hom ≫ modYoneda.map S.g := by
  dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
    simpleFunctorProjectiveResolutionZeroIso, simpleFunctorProjectiveResolutionOneIso]
  simpa only [Nat.reduceAdd, resolutionTerm, resolutionDifferential, Iso.refl_hom,
    Category.comp_id, Category.id_comp] using
    ChainComplex.of_d (resolutionTerm S) (resolutionDifferential S) 0

/-- The second differential is induced by `X ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem simpleFunctorProjectiveResolution_d_two_one :
    (S.simpleFunctorProjectiveResolution hg hf).complex.d 2 1 ≫
        (S.simpleFunctorProjectiveResolutionOneIso hg hf).hom =
      (S.simpleFunctorProjectiveResolutionTwoIso hg hf).hom ≫ modYoneda.map S.f := by
  dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
    simpleFunctorProjectiveResolutionOneIso, simpleFunctorProjectiveResolutionTwoIso]
  simpa only [Nat.reduceAdd, resolutionTerm, resolutionDifferential, Iso.refl_hom,
    Category.comp_id, Category.id_comp] using
    ChainComplex.of_d (resolutionTerm S) (resolutionDifferential S) 1

/-- The augmentation is the quotient by the radical functor. -/
@[simp]
theorem simpleFunctorProjectiveResolution_π_f_zero :
    (S.simpleFunctorProjectiveResolution hg hf).π.f 0 =
      (S.simpleFunctorProjectiveResolutionZeroIso hg hf).hom ≫
        (ObjectProperty.homMk (simpleFunctorπ S.X₃) : modYoneda.obj S.X₃ ⟶
          ⟨simpleFunctor S.X₃, have := hg.isLocalRing_end
            (isFinitelyPresentedFunctor_simpleFunctor_iff S.X₃).2 ⟨S.X₂, S.g, hg⟩⟩) := by
  dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
    simpleFunctorProjectiveResolutionZeroIso, Iso.refl_hom, Category.id_comp]
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero ..

/-- **Minimality of the resolution associated to an almost-split sequence.** In a balanced
category, every chain endomorphism lifting the identity of the simple functor is an
isomorphism. Thus no nonzero contractible direct summand can be removed from this resolution. -/
theorem IsAlmostSplit.isIso_simpleFunctorProjectiveResolution_of_comp_π_eq [Balanced C]
    {S : ShortComplex C} (hS : S.IsAlmostSplit)
    (α : (S.simpleFunctorProjectiveResolution hS.isRightAlmostSplit_g
        hS.shortExact.fIsKernel).complex ⟶
      (S.simpleFunctorProjectiveResolution hS.isRightAlmostSplit_g
        hS.shortExact.fIsKernel).complex)
    (hα : α ≫ (S.simpleFunctorProjectiveResolution hS.isRightAlmostSplit_g
        hS.shortExact.fIsKernel).π =
      (S.simpleFunctorProjectiveResolution hS.isRightAlmostSplit_g hS.shortExact.fIsKernel).π) :
    IsIso α := by
  -- In this construction the three term isomorphisms are identities. Reduce those endpoints
  -- when reading the chain map through the fully faithful Yoneda embedding.
  let a₀ : S.X₃ ⟶ S.X₃ := modYoneda.preimage (α.f 0)
  let a₁ : S.X₂ ⟶ S.X₂ := modYoneda.preimage (α.f 1)
  let a₂ : S.X₁ ⟶ S.X₁ := modYoneda.preimage (α.f 2)
  have ha₀ : modYoneda.map a₀ = α.f 0 := Functor.map_preimage _ _
  have ha₁ : modYoneda.map a₁ = α.f 1 := Functor.map_preimage _ _
  have ha₂ : modYoneda.map a₂ = α.f 2 := Functor.map_preimage _ _
  have hd₀ : (S.simpleFunctorProjectiveResolution hS.isRightAlmostSplit_g
      hS.shortExact.fIsKernel).complex.d 1 0 = modYoneda.map S.g :=
    ChainComplex.of_d (resolutionTerm S) (resolutionDifferential S) 0
  have hd₁ : (S.simpleFunctorProjectiveResolution hS.isRightAlmostSplit_g
      hS.shortExact.fIsKernel).complex.d 2 1 = modYoneda.map S.f :=
    ChainComplex.of_d (resolutionTerm S) (resolutionDifferential S) 1
  have hg : a₁ ≫ S.g = S.g ≫ a₀ := by
    apply (modYoneda : C ⥤ _).map_injective
    rw [Functor.map_comp, Functor.map_comp, ha₀, ha₁]
    have h := α.comm 1 0
    rw [hd₀] at h
    dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
      resolutionComplex, resolutionTerm] at h
    exact h
  have hf : a₂ ≫ S.f = S.f ≫ a₁ := by
    apply (modYoneda : C ⥤ _).map_injective
    rw [Functor.map_comp, Functor.map_comp, ha₁, ha₂]
    have h := α.comm 2 1
    rw [hd₁] at h
    dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
      resolutionComplex, resolutionTerm] at h
    exact h
  -- The augmentation is the projective cover of `S_Z`, so its degree-zero comparison is invertible.
  have hπ : preadditiveYoneda.map a₀ ≫ simpleFunctorπ S.X₃ = simpleFunctorπ S.X₃ := by
    have h := congrArg (fun β ↦ β.f 0) hα
    simp only [HomologicalComplex.comp_f, simpleFunctorProjectiveResolution_π_f_zero] at h
    dsimp only [simpleFunctorProjectiveResolutionZeroIso, Iso.refl_hom,
      simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
      resolutionComplex, resolutionTerm] at h
    simp only [Category.id_comp, ← ha₀] at h
    exact congrArg (fun f ↦ f.hom) h
  have : IsIso a₀ :=
    (isRepresentableProjectiveCover_preadditiveYonedaMap_jacobsonRadicalIdeal
      S.X₃).isIso_of_preadditiveYoneda_map_comp_eq _ hπ
  -- The remaining comparisons come from the corresponding morphism of almost-split sequences.
  let φ : S ⟶ S := ⟨a₂, a₁, a₀, hf, hg⟩
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso a₀)
  have : IsIso φ := hS.isIso_of_isIso_τ₃ hS φ
  have h₁ : IsIso a₁ := inferInstanceAs (IsIso (π₂.map φ))
  have h₂ : IsIso a₂ := inferInstanceAs (IsIso (π₁.map φ))
  have (n : ℕ) : IsIso (α.f n) := by
    rcases n with _ | _ | _ | n
    · exact ha₀ ▸ (inferInstanceAs (IsIso ((modYoneda : C ⥤ _).map a₀)))
    · exact ha₁ ▸ (inferInstanceAs (IsIso ((modYoneda : C ⥤ _).map a₁)))
    · exact ha₂ ▸ (inferInstanceAs (IsIso ((modYoneda : C ⥤ _).map a₂)))
    · exact (S.isZero_simpleFunctorProjectiveResolution_X _ _ n).isIso
        (S.isZero_simpleFunctorProjectiveResolution_X _ _ n) (α.f (n + 3))
  exact HomologicalComplex.Hom.isIso_of_components α

end CategoryTheory.ShortComplex
