/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The resolution of a natural monomorphism into an endofunctor

Let `C` be a category with cokernels, `G : C ⥤ C` a functor and `ι : 𝟭 C ⟶ G` a natural
transformation. Iterating `ι` on cokernels gives a cochain complex, functorial in `X : C`,
`G X ⟶ G (Z¹ X) ⟶ G (Z² X) ⟶ ⋯`, augmented by `ι_X : X ⟶ G X`. Here `Z⁰ X = X`,
`Zⁿ⁺¹ X = coker (ι : Zⁿ X ⟶ G (Zⁿ X))` (`CategoryTheory.NatTrans.cosyzygyFunctor`), and the
differential `G (Zⁿ X) ⟶ G (Zⁿ⁺¹ X)` is the cokernel projection followed by `ι`.

When `C` is abelian and every component of `ι` is a monomorphism, this complex is a resolution of
`X`: the augmentation from `X` placed in degree `0` is a quasi-isomorphism
(`CategoryTheory.NatTrans.quasiIso_toResolution_app`). This is the construction of a canonical
resolution from a functorial embedding: for `ι` the embedding of a sheaf into its sheaf of
discontinuous sections it is the Godement resolution, whose terms are flasque. Unlike the injective
resolutions of `CategoryTheory.InjectiveResolution.of`, which choose an injective object under each
cokernel, it is a functor `C ⥤ CochainComplex C ℕ` on the nose.

## Main definitions

* `CategoryTheory.NatTrans.cokernelFunctor ι`: the functor `X ↦ coker (ι_X)`.
* `CategoryTheory.NatTrans.cosyzygyFunctor ι n`: its `n`-th iterate `X ↦ Zⁿ X`, the cosyzygies.
* `CategoryTheory.NatTrans.resolution ι`: the complex `G X ⟶ G (Z¹ X) ⟶ G (Z² X) ⟶ ⋯`.
* `CategoryTheory.NatTrans.toResolution ι`: its augmentation, from `X` placed in degree `0`.

## Main results

* `CategoryTheory.NatTrans.resolution_obj_exactAt_succ`: the complex is exact in positive degrees.
* `CategoryTheory.NatTrans.quasiIso_toResolution_app`: the augmentation is a quasi-isomorphism.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Chapitre II, §4.3.
* The Stacks Project, Cohomology of Sheaves, Section 20.30 (Godement resolution), tag 0FKR.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.NatTrans

variable {C : Type*} [Category* C]

section Construction

variable [HasZeroMorphisms C] [HasCokernels C] {G : C ⥤ C} (ι : 𝟭 C ⟶ G)

/-- The functor `X ↦ coker (ι_X : X ⟶ G X)` for a natural transformation `ι : 𝟭 C ⟶ G`. -/
@[expose, simps, implicit_reducible]
noncomputable def cokernelFunctor : C ⥤ C where
  obj X := cokernel (ι.app X)
  map f := cokernel.map (ι.app _) (ι.app _) f (G.map f) (ι.naturality f).symm

/-- The cokernel projections `G X ⟶ coker (ι_X)`, as a natural transformation. -/
noncomputable def toCokernelFunctor : G ⟶ ι.cokernelFunctor where
  app X := cokernel.π (ι.app X)
  naturality _ _ _ := (cokernel.π_desc _ _ _).symm

@[simp]
theorem toCokernelFunctor_app (X : C) : ι.toCokernelFunctor.app X = cokernel.π (ι.app X) := by
  simp [toCokernelFunctor]

/-- The `n`-th iterate `X ↦ Zⁿ X` of `cokernelFunctor ι`, with `Z⁰ X = X` and
`Zⁿ⁺¹ X = coker (ι : Zⁿ X ⟶ G (Zⁿ X))`: the cosyzygies of the resolution `ι.resolution`. -/
@[expose, implicit_reducible]
noncomputable def cosyzygyFunctor : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => cosyzygyFunctor n ⋙ ι.cokernelFunctor

theorem cosyzygyFunctor_zero : ι.cosyzygyFunctor 0 = 𝟭 C :=
  (rfl)

@[simp]
theorem cosyzygyFunctor_zero_obj (X : C) : (ι.cosyzygyFunctor 0).obj X = X :=
  (rfl)

@[simp]
theorem cosyzygyFunctor_zero_map {X Y : C} (f : X ⟶ Y) : (ι.cosyzygyFunctor 0).map f = f :=
  (rfl)

theorem cosyzygyFunctor_succ (n : ℕ) :
    ι.cosyzygyFunctor (n + 1) = ι.cosyzygyFunctor n ⋙ ι.cokernelFunctor :=
  (rfl)

theorem cosyzygyFunctor_succ_obj (n : ℕ) (X : C) :
    (ι.cosyzygyFunctor (n + 1)).obj X = cokernel (ι.app ((ι.cosyzygyFunctor n).obj X)) :=
  (rfl)

theorem cosyzygyFunctor_succ_map (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (ι.cosyzygyFunctor (n + 1)).map f = ι.cokernelFunctor.map ((ι.cosyzygyFunctor n).map f) :=
  (rfl)

/-- The differential `G (Zⁿ X) ⟶ G (Zⁿ⁺¹ X)` of `resolution ι`, natural in `X`: the cokernel
projection `G (Zⁿ X) ⟶ Zⁿ⁺¹ X` followed by `ι`. -/
noncomputable def resolutionD (n : ℕ) :
    ι.cosyzygyFunctor n ⋙ G ⟶ ι.cosyzygyFunctor (n + 1) ⋙ G :=
  Functor.whiskerLeft (ι.cosyzygyFunctor n)
    (ι.toCokernelFunctor ≫ Functor.whiskerLeft ι.cokernelFunctor ι)

@[simp]
theorem resolutionD_app (n : ℕ) (X : C) :
    (ι.resolutionD n).app X =
      cokernel.π (ι.app ((ι.cosyzygyFunctor n).obj X)) ≫
        ι.app ((ι.cosyzygyFunctor (n + 1)).obj X) := by
  unfold resolutionD
  rfl

@[reassoc]
theorem resolutionD_app_comp_resolutionD_app (n : ℕ) (X : C) :
    (ι.resolutionD n).app X ≫ (ι.resolutionD (n + 1)).app X = 0 := by
  simp [resolutionD_app]

/-- The complex `G X ⟶ G (Z¹ X) ⟶ G (Z² X) ⟶ ⋯` obtained by iterating `ι : 𝟭 C ⟶ G` on
cokernels, as a functor of `X`. Its degree `n` term is `G (Zⁿ X)` (`resolution_obj_X`) and its
differentials are the cokernel projections followed by `ι` (`resolution_obj_d`). -/
@[expose, implicit_reducible]
noncomputable def resolution : C ⥤ CochainComplex C ℕ where
  obj X := CochainComplex.of (fun n ↦ G.obj ((ι.cosyzygyFunctor n).obj X))
    (fun n ↦ (ι.resolutionD n).app X) (fun n ↦ ι.resolutionD_app_comp_resolutionD_app n X)
  map f := CochainComplex.ofHom (fun n ↦ G.map ((ι.cosyzygyFunctor n).map f))
    (fun n ↦ by simpa using (ι.resolutionD n).naturality f)

@[simp]
theorem resolution_obj_X (X : C) (n : ℕ) :
    (ι.resolution.obj X).X n = G.obj ((ι.cosyzygyFunctor n).obj X) :=
  (rfl)

@[simp]
theorem resolution_obj_d (X : C) (n : ℕ) :
    (ι.resolution.obj X).d n (n + 1) = (ι.resolutionD n).app X :=
  CochainComplex.of_d _ (fun n ↦ (ι.resolutionD n).app X) n

@[simp]
theorem resolution_map_f {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (ι.resolution.map f).f n = G.map ((ι.cosyzygyFunctor n).map f) :=
  (rfl)

/-- The augmentation `ι_X : X ⟶ G X` composes to zero with the first differential of
`resolution ι`. -/
@[reassoc]
theorem app_comp_resolution_obj_d_zero_one (X : C) :
    ι.app X ≫ (ι.resolution.obj X).d 0 1 = 0 := by
  rw [resolution_obj_d, resolutionD_app]
  exact (cokernel.condition_assoc (ι.app X) _).trans zero_comp

variable [HasZeroObject C]

/-- The augmentation of `resolution ι`: the morphism `ι_X : X ⟶ G X` from `X` placed in
degree `0`. -/
noncomputable def toResolution : CochainComplex.single₀ C ⟶ ι.resolution where
  app X := (CochainComplex.fromSingle₀Equiv _ X).symm
    ⟨ι.app X, ι.app_comp_resolution_obj_d_zero_one X⟩
  naturality X Y f := HomologicalComplex.from_single_hom_ext (by simpa using ι.naturality f)

@[simp]
theorem toResolution_app_f_zero (X : C) : (ι.toResolution.app X).f 0 = ι.app X :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end Construction

section Abelian

variable [Abelian C] {G : C ⥤ C} (ι : 𝟭 C ⟶ G) [∀ X, Mono (ι.app X)]

/-- The complex `resolution ι` is exact in positive degrees. -/
theorem resolution_obj_exactAt_succ (X : C) (n : ℕ) :
    (ι.resolution.obj X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
  -- The complex `G (Zⁿ X) ⟶ G (Zⁿ⁺¹ X) ⟶ G (Zⁿ⁺² X)` has the same kernel at the middle as
  -- `G (Zⁿ X) ⟶ G (Zⁿ⁺¹ X) ⟶ Zⁿ⁺² X`, because `ι` is a monomorphism, and the second map of the
  -- latter is a cokernel of the first, because `G (Zⁿ X) ⟶ Zⁿ⁺¹ X` is an epimorphism.
  let Y := (ι.cosyzygyFunctor (n + 1)).obj X
  let α : ShortComplex.mk ((ι.resolutionD n).app X) (cokernel.π (ι.app Y))
        (by simp [Y, resolutionD_app]) ⟶ (ι.resolution.obj X).sc' n (n + 1) (n + 1 + 1) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := ι.app (cokernel (ι.app Y))
      comm₁₂ := (Category.id_comp _).trans
        ((ι.resolution_obj_d X n).trans (Category.comp_id _).symm)
      comm₂₃ := (Category.id_comp _).trans
        ((ι.resolution_obj_d X (n + 1)).trans (ι.resolutionD_app (n + 1) X)) }
  have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono α.τ₃ := ‹∀ X, Mono (ι.app X)› _
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  exact ShortComplex.exact_of_g_is_cokernel _
    (isCokernelEpiComp (cokernelIsCokernel (ι.app Y)) _ (resolutionD_app ι n X))

/-- The augmentation `X ⟶ resolution ι X` is a quasi-isomorphism: `resolution ι X` is a
resolution of `X`. -/
instance quasiIso_toResolution_app (X : C) : QuasiIso (ι.toResolution.app X) where
  quasiIsoAt n := by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      refine (ShortComplex.quasiIso_iff_of_zeros _
        (((CochainComplex.single₀ C).obj X).shape 0 0 (by simp))
        ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 X 1
          (by simp)).eq_of_tgt _ _)
        ((ι.resolution.obj X).shape 0 0 (by simp))).2 ⟨?_, ?_⟩
      · -- The kernel of `G X ⟶ G (Z¹ X)` is the image of `ι_X`, because `ι` is a monomorphism.
        let α : ShortComplex.mk (ι.app X) (cokernel.π (ι.app X)) (cokernel.condition _) ⟶
            ShortComplex.mk ((ι.toResolution.app X).f 0) ((ι.resolution.obj X).d 0 1)
              (CochainComplex.fromSingle₀Equiv _ _ (ι.toResolution.app X)).2 :=
          { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := ι.app (cokernel (ι.app X))
            comm₁₂ := (Category.id_comp _).trans
              ((ι.toResolution_app_f_zero X).trans (Category.comp_id _).symm)
            comm₂₃ := (Category.id_comp _).trans
              ((ι.resolution_obj_d X 0).trans (ι.resolutionD_app 0 X)) }
        have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 _))
        have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
        have : Mono α.τ₃ := ‹∀ X, Mono (ι.app X)› _
        exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).1
          (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      · exact (ι.toResolution_app_f_zero X ▸ ‹∀ X, Mono (ι.app X)› X :
          Mono ((ι.toResolution.app X).f 0))
    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · exact ι.resolution_obj_exactAt_succ X n
      · exact CochainComplex.exactAt_succ_single_obj _ _

end Abelian

end CategoryTheory.NatTrans
