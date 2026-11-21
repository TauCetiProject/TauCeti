/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import TauCeti.CategoryTheory.Triangulated.ExtensionClosed
public import TauCeti.CategoryTheory.Triangulated.TriangleIso

/-!
# The heart of a `t`-structure is abelian

Let `t` be a `t`-structure on a pretriangulated category `C` satisfying the octahedral axiom, and
let `H` be a heart of `t` (`t.Heart H`), i.e. an additive category identified by a fully faithful
functor `t.ιHeart : H ⥤ C` with the full subcategory of objects which are both `≤ 0` and `≥ 0`.
We show that `H` is an abelian category, by checking the two hypotheses of Mathlib's criterion
`Triangulated.AbelianSubcategory.abelian` for `t.ιHeart`:

* there is no nonzero morphism `ιA ⟶ (ιB)⟦n⟧` when `n < 0`, by the orthogonality axiom;
* every morphism `f : A ⟶ B` of `H` is admissible: a cone `S` of `ι f` lies in `t.le 0 ⊓ t.ge (-1)`,
  and the truncation triangle `τ_{<0} S ⟶ S ⟶ τ_{≥0} S ⟶ …` has the form `(ιK)⟦1⟧ ⟶ S ⟶ ιQ ⟶ …`
  with `K` and `Q` in the heart.

No boundedness or nondegeneracy of `t` is needed. Along the way, the aisles `t.le n`, the
coaisles `t.ge n` and the heart are shown to be closed under extensions, which makes the heart
closed under finite products.

We also describe the abelian structure through `C`: a short complex `0 ⟶ A ⟶ B ⟶ D ⟶ 0` of `H` is
short exact if and only if `ιA ⟶ ιB ⟶ ιD` extends to a distinguished triangle, whose connecting
morphism is then unique; and for a distinguished triangle `ιA ⟶ ιB ⟶ S ⟶ (ιA)⟦1⟧` on
`f : A ⟶ B`, the image of the cokernel of `f` is `τ_{≥0} S` and the shifted image
`(ι (ker f))⟦1⟧` of the kernel is `τ_{<0} S`, up to isomorphism.

## Main results

* `CategoryTheory.Triangulated.TStructure.heartAbelian`: the abelian structure on a heart, with an
  instance on the full subcategory `t.heart.FullSubcategory`.
* `CategoryTheory.Triangulated.TStructure.admissibleMorphism_ιHeart`: every morphism of the heart
  is admissible.
* `CategoryTheory.Triangulated.TStructure.shortExact_iff_exists_distTriang`: short exact sequences
  of the heart are the distinguished triangles with vertices in the heart.
* `CategoryTheory.Triangulated.TStructure.mor₃_eq_of_distTriang`: the connecting morphism of such
  a triangle is unique.
* `CategoryTheory.Triangulated.TStructure.nonempty_ιHeart_obj_cokernel_iso` and
  `CategoryTheory.Triangulated.TStructure.nonempty_shift_ιHeart_obj_kernel_iso`: kernels and
  cokernels through truncations of a cone.

## References

* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982], 1.3.4–1.3.6
-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated ZeroObject

universe v' u' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

section Extensions

/-- The aisle `t.le n` is closed under extensions. -/
instance (n : ℤ) : (t.le n).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ ↦ (t.le_iff_isLE _ _).2 <|
    t.isLE₂ T hT n ((t.le_iff_isLE _ _).1 h₁) ((t.le_iff_isLE _ _).1 h₃)

/-- The coaisle `t.ge n` is closed under extensions. -/
instance (n : ℤ) : (t.ge n).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ ↦ (t.ge_iff_isGE _ _).2 <|
    t.isGE₂ T hT n ((t.ge_iff_isGE _ _).1 h₁) ((t.ge_iff_isGE _ _).1 h₃)

instance (n : ℤ) : (t.le n).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, (t.le_iff_isLE _ _).2 inferInstance⟩

instance (n : ℤ) : (t.ge n).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, (t.ge_iff_isGE _ _).2 inferInstance⟩

/-- The heart of a `t`-structure is closed under extensions: if `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` is
distinguished with `X₁` and `X₃` in the heart, then so is `X₂`. -/
instance : t.heart.IsTriangulatedClosed₂ :=
  inferInstanceAs (t.le 0 ⊓ t.ge 0).IsTriangulatedClosed₂

instance : t.heart.ContainsZero :=
  inferInstanceAs (t.le 0 ⊓ t.ge 0).ContainsZero

end Extensions

variable (H : Type u') [Category.{v'} H] [Preadditive H] [t.Heart H]

include t in
/-- A heart of a `t`-structure has finite products. -/
theorem hasFiniteProducts_heart : HasFiniteProducts H :=
  ⟨fun _ ↦ ⟨fun K ↦ by
    obtain ⟨X, ⟨e⟩⟩ : (t.ιHeart (H := H)).essImage (limit (K ⋙ t.ιHeart)) := by
      rw [essImage_ιHeart]
      exact t.heart.prop_limit _ fun _ ↦ t.ιHeart_obj_mem _
    have := createsLimitOfFullyFaithfulOfIso X e
    exact hasLimit_of_created K t.ιHeart⟩⟩

variable {H}

/-- There is no nonzero morphism from an object of the heart to a negative shift of an object of
the heart. -/
theorem eq_zero_of_hom_ιHeart_obj_shift_neg ⦃X Y : H⦄ ⦃n : ℤ⦄
    (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧) (hn : n < 0) : f = 0 :=
  have := t.isGE_shift (t.ιHeart.obj Y) 0 n (-n)
  t.zero f 0 (-n)

/-- A cone of a morphism of the heart is `≤ 0` and `≥ -1`. -/
theorem isLE_isGE_of_distTriang {X₁ X₂ : H} {f₁ : X₁ ⟶ X₂} {S : C}
    {f₂ : t.ιHeart.obj X₂ ⟶ S} {f₃ : S ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (t.ιHeart.map f₁) f₂ f₃ ∈ distTriang C) :
    t.IsLE S 0 ∧ t.IsGE S (-1) := by
  have hT' := rot_of_distTriang _ hT
  have := t.isLE_shift (t.ιHeart.obj X₁) 0 1 (-1)
  have := t.isGE_shift (t.ιHeart.obj X₁) 0 1 (-1)
  have := t.isLE_of_le ((t.ιHeart.obj X₁)⟦(1 : ℤ)⟧) (-1) 0
  have := t.isGE_of_ge (t.ιHeart.obj X₂) (-1) 0
  exact ⟨t.isLE₂ _ hT' 0 (by dsimp; infer_instance) (by dsimp; infer_instance),
    t.isGE₂ _ hT' (-1) (by dsimp; infer_instance) (by dsimp; infer_instance)⟩

/-- The connecting morphism of a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` with `X ≤ n` and
`Z ≥ n` is determined by the other two morphisms. This applies in particular when the three
vertices lie in the heart. -/
theorem mor₃_eq_of_distTriang {X Y Z : C} (n : ℤ) [t.IsLE X n] [t.IsGE Z n] {f : X ⟶ Y}
    {g : Y ⟶ Z} {δ δ' : Z ⟶ X⟦(1 : ℤ)⟧} (h : Triangle.mk f g δ ∈ distTriang C)
    (h' : Triangle.mk f g δ' ∈ distTriang C) : δ = δ' := by
  obtain ⟨c, hc₂, hc₃⟩ : ∃ c : Z ⟶ Z, g ≫ c = g ∧ δ = c ≫ δ' := by
    simpa using complete_distinguished_triangle_morphism _ _ h h' (𝟙 X) (𝟙 Y) (by simp)
  obtain ⟨w, hw⟩ : ∃ w : X⟦(1 : ℤ)⟧ ⟶ Z, c - 𝟙 Z = δ ≫ w :=
    Triangle.yoneda_exact₃ _ h _ (by simp [Preadditive.comp_sub, hc₂])
  have := t.isLE_shift X n 1 (n - 1)
  rw [t.zero w (n - 1) n, comp_zero, sub_eq_zero] at hw
  simpa [hw] using hc₃

variable [IsTriangulated C]

/-- An object which is `≤ 0` and `≥ -1` is an extension of an object of the heart by the shift
`(ιK)⟦1⟧` of an object of the heart, through its truncation triangle
`τ_{<0} S ⟶ S ⟶ τ_{≥0} S ⟶ (τ_{<0} S)⟦1⟧`. -/
theorem exists_distTriang_truncLT_truncGE (S : C) [t.IsLE S 0] [t.IsGE S (-1)] :
    ∃ (K Q : H) (e₁ : (t.truncLT 0).obj S ≅ (t.ιHeart.obj K)⟦(1 : ℤ)⟧)
      (e₃ : (t.truncGE 0).obj S ≅ t.ιHeart.obj Q),
      Triangle.mk (e₁.inv ≫ (t.truncLTι 0).app S) ((t.truncGEπ 0).app S ≫ e₃.hom)
        (e₃.inv ≫ (t.truncGEδLT 0).app S ≫ e₁.hom⟦(1 : ℤ)⟧') ∈ distTriang C := by
  have := t.isLE_truncLT_obj S 0 (-1)
  have := t.isLE_shift ((t.truncLT 0).obj S) (-1) (-1) 0
  have := t.isGE_shift ((t.truncLT 0).obj S) (-1) (-1) 0
  obtain ⟨K, ⟨eK⟩⟩ : (t.ιHeart (H := H)).essImage (((t.truncLT 0).obj S)⟦(-1 : ℤ)⟧) := by
    rw [essImage_ιHeart]
    exact ⟨t.le_of_isLE _ _, t.ge_of_isGE _ _⟩
  obtain ⟨Q, ⟨eQ⟩⟩ : (t.ιHeart (H := H)).essImage ((t.truncGE 0).obj S) := by
    rw [essImage_ιHeart]
    exact ⟨t.le_of_isLE _ _, t.ge_of_isGE _ _⟩
  let e₁ : (t.truncLT 0).obj S ≅ (t.ιHeart.obj K)⟦(1 : ℤ)⟧ :=
    ((shiftFunctorCompIsoId C (-1 : ℤ) 1 (by lia)).app _).symm ≪≫
      (shiftFunctor C (1 : ℤ)).mapIso eK.symm
  refine ⟨K, Q, e₁, eQ.symm, ?_⟩
  simpa using distinguished_mk_of_iso (t.triangleLTGE_distinguished 0 S) e₁ (Iso.refl S) eQ.symm

variable (H)

/-- Every morphism of the heart of a `t`-structure is admissible in the sense of
`Triangulated.AbelianSubcategory.admissibleMorphism`. -/
theorem admissibleMorphism_ιHeart :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) = ⊤ := by
  ext X₁ X₂ f₁
  simp only [MorphismProperty.top_apply, iff_true]
  intro S f₂ f₃ hT
  obtain ⟨_, _⟩ := t.isLE_isGE_of_distTriang hT
  obtain ⟨K, Q, e₁, e₃, h⟩ := t.exists_distTriang_truncLT_truncGE (H := H) S
  exact ⟨K, Q, _, _, _, h⟩

/-- **The heart of a `t`-structure is an abelian category** (BBD, Théorème 1.3.6). The abelian
structure is the one given by `Triangulated.AbelianSubcategory.abelian`. -/
@[instance_reducible]
noncomputable def heartAbelian : Abelian H :=
  have := t.hasFiniteProducts_heart H
  AbelianSubcategory.abelian t.ιHeart t.eq_zero_of_hom_ιHeart_obj_shift_neg
    (t.admissibleMorphism_ιHeart H)

noncomputable instance instAbelianHeartFullSubcategory : Abelian t.heart.FullSubcategory :=
  letI := t.hasHeartFullSubcategory
  t.heartAbelian t.heart.FullSubcategory

variable {H}

/-- A short complex `0 ⟶ A ⟶ B ⟶ D ⟶ 0` of the heart is short exact if and only if
`ιA ⟶ ιB ⟶ ιD` extends to a distinguished triangle of `C` (BBD 1.3.6). By
`mor₃_eq_of_distTriang`, the connecting morphism `ιD ⟶ (ιA)⟦1⟧` is then unique. -/
theorem shortExact_iff_exists_distTriang (S : ShortComplex H) :
    S.ShortExact ↔
      ∃ δ, Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) δ ∈ distTriang C := by
  let := t.heartAbelian H
  have := t.hasFiniteProducts_heart H
  refine ⟨fun hS ↦ ?_, fun ⟨δ, hT⟩ ↦ ?_⟩
  · have := hS.mono_f
    have := hS.epi_g
    obtain ⟨X₁, i, δ, hT⟩ := AbelianSubcategory.exists_distinguished_triangle_of_epi
      t.eq_zero_of_hom_ιHeart_obj_shift_neg (t.admissibleMorphism_ιHeart H) S.g
    let e := IsLimit.conePointUniqueUpToIso hS.exact.fIsKernel
      (AbelianSubcategory.isLimitKernelForkOfDistTriang t.eq_zero_of_hom_ιHeart_obj_shift_neg i S.g
        δ hT)
    have he : e.hom ≫ i = S.f :=
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
    refine ⟨δ ≫ (t.ιHeart.map e.inv)⟦(1 : ℤ)⟧', ?_⟩
    simpa [← Functor.map_comp, he] using distinguished_mk_of_iso₁ hT (t.ιHeart.mapIso e.symm)
  · have hf := AbelianSubcategory.isLimitKernelForkOfDistTriang
      t.eq_zero_of_hom_ιHeart_obj_shift_neg S.f S.g δ hT
    have hg := AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      t.eq_zero_of_hom_ιHeart_obj_shift_neg S.f S.g δ hT
    have : Mono S.f := mono_of_isLimit_fork hf
    have : Epi S.g := epi_of_isColimit_cofork hg
    exact ⟨S.exact_of_f_is_kernel hf⟩

/-- For a distinguished triangle `ιA ⟶ ιB ⟶ S ⟶ (ιA)⟦1⟧` on a morphism `f : A ⟶ B` of the heart,
the image of the cokernel of `f` is isomorphic to the truncation `τ_{≥0} S`. -/
theorem nonempty_ιHeart_obj_cokernel_iso {X₁ X₂ : H} {f₁ : X₁ ⟶ X₂} [HasCokernel f₁] {S : C}
    {f₂ : t.ιHeart.obj X₂ ⟶ S} {f₃ : S ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (t.ιHeart.map f₁) f₂ f₃ ∈ distTriang C) :
    Nonempty (t.ιHeart.obj (cokernel f₁) ≅ (t.truncGE 0).obj S) := by
  obtain ⟨_, _⟩ := t.isLE_isGE_of_distTriang hT
  obtain ⟨K, Q, e₁, e₃, h⟩ := t.exists_distTriang_truncLT_truncGE (H := H) S
  exact ⟨t.ιHeart.mapIso ((colimit.isColimit _).coconePointUniqueUpToIso
    (AbelianSubcategory.isColimitCokernelCofork t.eq_zero_of_hom_ιHeart_obj_shift_neg hT h)) ≪≫
      e₃.symm⟩

/-- For a distinguished triangle `ιA ⟶ ιB ⟶ S ⟶ (ιA)⟦1⟧` on a morphism `f : A ⟶ B` of the heart,
the shifted image `(ι (ker f))⟦1⟧` of the kernel of `f` is isomorphic to the truncation
`τ_{<0} S`. -/
theorem nonempty_shift_ιHeart_obj_kernel_iso {X₁ X₂ : H} {f₁ : X₁ ⟶ X₂} [HasKernel f₁] {S : C}
    {f₂ : t.ιHeart.obj X₂ ⟶ S} {f₃ : S ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (t.ιHeart.map f₁) f₂ f₃ ∈ distTriang C) :
    Nonempty ((t.ιHeart.obj (kernel f₁))⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj S) := by
  obtain ⟨_, _⟩ := t.isLE_isGE_of_distTriang hT
  obtain ⟨K, Q, e₁, e₃, h⟩ := t.exists_distTriang_truncLT_truncGE (H := H) S
  exact ⟨(shiftFunctor C (1 : ℤ)).mapIso (t.ιHeart.mapIso ((limit.isLimit _).conePointUniqueUpToIso
    (AbelianSubcategory.isLimitKernelFork t.eq_zero_of_hom_ιHeart_obj_shift_neg hT h))) ≪≫ e₁.symm⟩

end CategoryTheory.Triangulated.TStructure
