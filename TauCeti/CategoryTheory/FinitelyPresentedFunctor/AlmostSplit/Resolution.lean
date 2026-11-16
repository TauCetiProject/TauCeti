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
degree two. When the last map is moreover right minimal, every chain endomorphism of this
resolution lifting the identity of `S_Z` is invertible; this is the minimality property of the
resolution. It holds in particular when the first map is left almost split, as for an
almost-split sequence, without any balancedness assumption on `C`.

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
noncomputable def simpleFunctorProjectiveResolutionXZeroIso :
    (S.simpleFunctorProjectiveResolution hg hf).complex.X 0 ≅ modYoneda.obj S.X₃ :=
  Iso.refl _

/-- Degree one of the simple-functor resolution is `(-, Y)`. -/
noncomputable def simpleFunctorProjectiveResolutionXOneIso :
    (S.simpleFunctorProjectiveResolution hg hf).complex.X 1 ≅ modYoneda.obj S.X₂ :=
  Iso.refl _

/-- Degree two of the simple-functor resolution is `(-, X)`. -/
noncomputable def simpleFunctorProjectiveResolutionXTwoIso :
    (S.simpleFunctorProjectiveResolution hg hf).complex.X 2 ≅ modYoneda.obj S.X₁ :=
  Iso.refl _

/-- The simple-functor resolution vanishes in degrees above two. -/
theorem isZero_simpleFunctorProjectiveResolution_X_add_three (n : ℕ) :
    IsZero ((S.simpleFunctorProjectiveResolution hg hf).complex.X (n + 3)) :=
  isZero_zero _

/-- The first differential is induced by `Y ⟶ Z`. -/
@[simp]
theorem simpleFunctorProjectiveResolution_d_one_zero :
    (S.simpleFunctorProjectiveResolution hg hf).complex.d 1 0 =
      (S.simpleFunctorProjectiveResolutionXOneIso hg hf).hom ≫ modYoneda.map S.g ≫
        (S.simpleFunctorProjectiveResolutionXZeroIso hg hf).inv := by
  dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
    simpleFunctorProjectiveResolutionXZeroIso, simpleFunctorProjectiveResolutionXOneIso]
  simpa only [Nat.reduceAdd, resolutionTerm, resolutionDifferential, Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Category.id_comp] using
    ChainComplex.of_d (resolutionTerm S) (resolutionDifferential S) 0

/-- The second differential is induced by `X ⟶ Y`. -/
@[simp]
theorem simpleFunctorProjectiveResolution_d_two_one :
    (S.simpleFunctorProjectiveResolution hg hf).complex.d 2 1 =
      (S.simpleFunctorProjectiveResolutionXTwoIso hg hf).hom ≫ modYoneda.map S.f ≫
        (S.simpleFunctorProjectiveResolutionXOneIso hg hf).inv := by
  dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
    simpleFunctorProjectiveResolutionXOneIso, simpleFunctorProjectiveResolutionXTwoIso]
  simpa only [Nat.reduceAdd, resolutionTerm, resolutionDifferential, Iso.refl_hom, Iso.refl_inv,
    Category.comp_id, Category.id_comp] using
    ChainComplex.of_d (resolutionTerm S) (resolutionDifferential S) 1

/-- The differentials out of the degrees above two vanish. -/
@[simp]
theorem simpleFunctorProjectiveResolution_d_add_three (n j : ℕ) :
    (S.simpleFunctorProjectiveResolution hg hf).complex.d (n + 3) j = 0 :=
  (S.isZero_simpleFunctorProjectiveResolution_X_add_three hg hf n).eq_of_src _ _

/-- The augmentation is the quotient by the radical functor. -/
@[simp]
theorem simpleFunctorProjectiveResolution_π_f_zero :
    (S.simpleFunctorProjectiveResolution hg hf).π.f 0 =
      (S.simpleFunctorProjectiveResolutionXZeroIso hg hf).hom ≫
        (ObjectProperty.homMk (simpleFunctorπ S.X₃) : modYoneda.obj S.X₃ ⟶
          ⟨simpleFunctor S.X₃, have := hg.isLocalRing_end
            (isFinitelyPresentedFunctor_simpleFunctor_iff S.X₃).2 ⟨S.X₂, S.g, hg⟩⟩) := by
  dsimp only [simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
    simpleFunctorProjectiveResolutionXZeroIso, Iso.refl_hom, Category.id_comp]
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero ..

omit [HasBinaryBiproducts C] [HasWeakKernels C] [Nonempty C] in
/-- An endomorphism of a kernel sequence whose last map is right almost split and right minimal
is invertible as soon as it is invertible at the right-hand end. -/
private theorem isIso_of_isIso_τ₃_of_rightMinimal {S : ShortComplex C}
    (hg : IsRightAlmostSplit S.g) (hf : IsLimit (KernelFork.ofι S.f S.zero))
    (hmin : ∀ b : S.X₂ ⟶ S.X₂, b ≫ S.g = S.g → IsIso b) (φ : S ⟶ S) [IsIso φ.τ₃] :
    IsIso φ := by
  -- Factoring `S.g ≫ φ.τ₃⁻¹` through `S.g` gives a two-sided inverse of `φ.τ₂` up to right
  -- minimality of `S.g`.
  obtain ⟨c, hc⟩ := hg.factors S.X₂ (S.g ≫ inv φ.τ₃) (hg.comp_iso (inv φ.τ₃)).not_isSplitEpi
  have : IsIso (φ.τ₂ ≫ c) := hmin _ (by
    rw [Category.assoc, hc, reassoc_of% φ.comm₂₃, IsIso.hom_inv_id, Category.comp_id])
  have : IsIso (c ≫ φ.τ₂) := hmin _ (by
    rw [Category.assoc, φ.comm₂₃, reassoc_of% hc, IsIso.inv_hom_id, Category.comp_id])
  have : IsSplitMono φ.τ₂ :=
    IsSplitMono.mk' ⟨c ≫ inv (φ.τ₂ ≫ c), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have : IsSplitEpi φ.τ₂ :=
    IsSplitEpi.mk' ⟨inv (c ≫ φ.τ₂) ≫ c, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  have : IsIso φ.τ₂ := isIso_of_mono_of_isSplitEpi φ.τ₂
  -- The kernel property of `S.f` then inverts the left-hand comparison.
  have : Mono S.f := Fork.IsLimit.mono hf
  have hinv : inv φ.τ₂ ≫ S.g = S.g ≫ inv φ.τ₃ := by
    rw [IsIso.inv_comp_eq, reassoc_of% φ.comm₂₃, IsIso.hom_inv_id, Category.comp_id]
  obtain ⟨(e : S.X₁ ⟶ S.X₁), (he : e ≫ S.f = S.f ≫ inv φ.τ₂)⟩ :=
    KernelFork.IsLimit.lift' hf (S.f ≫ inv φ.τ₂) (by
    rw [Category.assoc, hinv, S.zero_assoc, zero_comp])
  have : IsIso φ.τ₁ := ⟨e, (cancel_mono S.f).1 (by
      rw [Category.assoc, he, reassoc_of% φ.comm₁₂, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]),
    (cancel_mono S.f).1 (by
      rw [Category.assoc, φ.comm₁₂, reassoc_of% he, IsIso.inv_hom_id, Category.comp_id,
        Category.id_comp])⟩
  exact isIso_of_isIso φ

variable {hg hf} in
/-- **Minimality of the resolution of a right minimal kernel sequence.** When the last map
`Y ⟶ Z` is right minimal, every chain endomorphism of the resolution lifting the identity of the
simple functor is an isomorphism. Thus no nonzero contractible direct summand can be removed from
this resolution. -/
theorem isIso_of_comp_simpleFunctorProjectiveResolution_π_eq
    (hmin : ∀ b : S.X₂ ⟶ S.X₂, b ≫ S.g = S.g → IsIso b)
    (α : (S.simpleFunctorProjectiveResolution hg hf).complex ⟶
      (S.simpleFunctorProjectiveResolution hg hf).complex)
    (hα : α ≫ (S.simpleFunctorProjectiveResolution hg hf).π =
      (S.simpleFunctorProjectiveResolution hg hf).π) :
    IsIso α := by
  -- In this construction the three term isomorphisms are identities. Reduce those endpoints
  -- when reading the chain map through the fully faithful Yoneda embedding.
  let a₀ : S.X₃ ⟶ S.X₃ := modYoneda.preimage (α.f 0)
  let a₁ : S.X₂ ⟶ S.X₂ := modYoneda.preimage (α.f 1)
  let a₂ : S.X₁ ⟶ S.X₁ := modYoneda.preimage (α.f 2)
  have ha₀ : modYoneda.map a₀ = α.f 0 := Functor.map_preimage _ _
  have ha₁ : modYoneda.map a₁ = α.f 1 := Functor.map_preimage _ _
  have ha₂ : modYoneda.map a₂ = α.f 2 := Functor.map_preimage _ _
  have hcomm₀ : a₁ ≫ S.g = S.g ≫ a₀ := (modYoneda : C ⥤ _).map_injective <| by
    rw [Functor.map_comp, Functor.map_comp, ha₀, ha₁]
    exact α.comm 1 0
  have hcomm₁ : a₂ ≫ S.f = S.f ≫ a₁ := (modYoneda : C ⥤ _).map_injective <| by
    rw [Functor.map_comp, Functor.map_comp, ha₁, ha₂]
    exact α.comm 2 1
  -- The augmentation is the projective cover of `S_Z`, so its degree-zero comparison is invertible.
  have hπ : preadditiveYoneda.map a₀ ≫ simpleFunctorπ S.X₃ = simpleFunctorπ S.X₃ := by
    have h := congrArg (fun β ↦ β.f 0) hα
    simp only [HomologicalComplex.comp_f, simpleFunctorProjectiveResolution_π_f_zero] at h
    dsimp only [simpleFunctorProjectiveResolutionXZeroIso, Iso.refl_hom,
      simpleFunctorProjectiveResolution, ChainComplex.toProjectiveResolution,
      resolutionComplex, resolutionTerm] at h
    simp only [Category.id_comp, ← ha₀] at h
    exact congrArg (fun f ↦ f.hom) h
  have : IsIso a₀ :=
    (isRepresentableProjectiveCover_preadditiveYonedaMap_jacobsonRadicalIdeal
      S.X₃).isIso_of_preadditiveYoneda_map_comp_eq _ hπ
  -- The remaining comparisons come from the corresponding endomorphism of the kernel sequence.
  let φ : S ⟶ S := ⟨a₂, a₁, a₀, hcomm₁, hcomm₀⟩
  have : IsIso φ.τ₃ := inferInstanceAs (IsIso a₀)
  have : IsIso φ := isIso_of_isIso_τ₃_of_rightMinimal hg hf hmin φ
  have (n : ℕ) : IsIso (α.f n) := by
    rcases n with _ | _ | _ | n
    · exact ha₀ ▸ (inferInstanceAs (IsIso ((modYoneda : C ⥤ _).map a₀)))
    · exact ha₁ ▸ (inferInstanceAs (IsIso ((modYoneda : C ⥤ _).map (π₂.map φ))))
    · exact ha₂ ▸ (inferInstanceAs (IsIso ((modYoneda : C ⥤ _).map (π₁.map φ))))
    · exact (S.isZero_simpleFunctorProjectiveResolution_X_add_three _ _ n).isIso
        (S.isZero_simpleFunctorProjectiveResolution_X_add_three _ _ n) (α.f (n + 3))
  exact HomologicalComplex.Hom.isIso_of_components α

omit [HasBinaryBiproducts C] [HasWeakKernels C] [Nonempty C] in
/-- In a kernel sequence whose first map is left almost split, the last map is right minimal.
Unlike `CategoryTheory.ShortComplex.IsAlmostSplit.isIso_of_comp_g_eq`, this needs no
balancedness: the inverse is written down from the kernel lift of `𝟙 - b`. -/
private theorem isIso_of_comp_g_eq_of_isLeftAlmostSplit {S : ShortComplex C}
    (hf : IsLimit (KernelFork.ofι S.f S.zero)) (hl : IsLeftAlmostSplit S.f) (b : S.X₂ ⟶ S.X₂)
    (hb : b ≫ S.g = S.g) : IsIso b := by
  have := hl.isLocalRing_end
  obtain ⟨(h : S.X₂ ⟶ S.X₁), (hh : h ≫ S.f = 𝟙 S.X₂ - b)⟩ :=
    KernelFork.IsLimit.lift' hf (𝟙 S.X₂ - b) (by
    rw [Preadditive.sub_comp, hb, Category.id_comp, sub_self])
  -- `b` fixes the right-hand end, so its restriction `𝟙 - S.f ≫ h` to `X` is invertible.
  let φ : S ⟶ S := ⟨𝟙 _ - S.f ≫ h, b, 𝟙 _, by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hh, Preadditive.comp_sub,
      Category.comp_id, sub_sub_cancel], by rw [hb, Category.comp_id]⟩
  have : IsIso (𝟙 S.X₁ - S.f ≫ h) := isIso_τ₁_of_τ₃_eq_id hf hl.not_isSplitMono φ rfl
  have hb' : b = 𝟙 S.X₂ - h ≫ S.f := by rw [hh, sub_sub_cancel]
  have hu : ∀ {W : C} (k : S.X₁ ⟶ W),
      S.f ≫ h ≫ inv (𝟙 S.X₁ - S.f ≫ h) ≫ k = inv (𝟙 S.X₁ - S.f ≫ h) ≫ k - k := by
    have := IsIso.hom_inv_id (𝟙 S.X₁ - S.f ≫ h)
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc] at this
    have h₀ := (sub_sub_cancel _ _).symm.trans (congrArg (inv (𝟙 S.X₁ - S.f ≫ h) - ·) this)
    intro W k
    simpa only [Category.assoc, Preadditive.sub_comp, Category.id_comp] using h₀ =≫ k
  have hu' : ∀ {W : C} (k : S.X₁ ⟶ W),
      inv (𝟙 S.X₁ - S.f ≫ h) ≫ S.f ≫ h ≫ k = inv (𝟙 S.X₁ - S.f ≫ h) ≫ k - k := by
    have := IsIso.inv_hom_id (𝟙 S.X₁ - S.f ≫ h)
    rw [Preadditive.comp_sub, Category.comp_id] at this
    have h₀ := (sub_sub_cancel _ _).symm.trans (congrArg (inv (𝟙 S.X₁ - S.f ≫ h) - ·) this)
    intro W k
    simpa only [Category.assoc, Preadditive.sub_comp, Category.id_comp] using h₀ =≫ k
  refine ⟨𝟙 _ + h ≫ inv (𝟙 S.X₁ - S.f ≫ h) ≫ S.f, ?_, ?_⟩ <;> rw [hb']
  · simp only [Preadditive.sub_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
      Category.assoc, hu, Preadditive.comp_sub]
    abel
  · simp only [Preadditive.comp_sub, Preadditive.add_comp, Category.id_comp, Category.comp_id,
      Category.assoc, hu']
    abel

end CategoryTheory.ShortComplex

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [HasWeakKernels C] [Nonempty C]

/-- **Minimality of the resolution associated to an almost-split sequence.** When the first map
`X ⟶ Y` of the kernel sequence is left almost split, as for an almost-split sequence, every chain
endomorphism of the resolution lifting the identity of the simple functor is an isomorphism. No
balancedness of `C` is needed. -/
theorem IsLeftAlmostSplit.isIso_of_comp_simpleFunctorProjectiveResolution_π_eq
    {S : ShortComplex C} {hg : IsRightAlmostSplit S.g} {hf : IsLimit (KernelFork.ofι S.f S.zero)}
    (hl : IsLeftAlmostSplit S.f)
    (α : (S.simpleFunctorProjectiveResolution hg hf).complex ⟶
      (S.simpleFunctorProjectiveResolution hg hf).complex)
    (hα : α ≫ (S.simpleFunctorProjectiveResolution hg hf).π =
      (S.simpleFunctorProjectiveResolution hg hf).π) :
    IsIso α :=
  S.isIso_of_comp_simpleFunctorProjectiveResolution_π_eq
    (ShortComplex.isIso_of_comp_g_eq_of_isLeftAlmostSplit hf hl) α hα

end TauCeti
