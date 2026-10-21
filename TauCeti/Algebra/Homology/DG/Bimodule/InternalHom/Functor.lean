/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import TauCeti.Algebra.Homology.DG.Bimodule.InternalHom.Basic
public import TauCeti.Algebra.Homology.DG.Bimodule.Category

/-!
# Functoriality of the internal Hom of DG modules

For a DG `(A, B)`-bimodule `M` and a right DG `B`-module `N`, the internal Hom
`Hom_B(M, N)` is a right DG `A`-module. Precomposition with a bimodule morphism and
postcomposition with a right-module morphism give the map `f ↦ v ∘ f ∘ u`.
These maps preserve degrees, the right `A`-action, and the graded-commutator differential.

`DGRightModule.InternalHom.map` supplies this map, with evaluation, identity, and composition
lemmas. `DGBimoduleCat.internalHomFunctor` packages it as a bifunctor, contravariant in the
bimodule and covariant in the right module. Both variables act linearly. This is the internal-Hom
functor used in the tensor–Hom adjunction; no claim of derived functoriality is made here.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- The internal Hom from a DG `(A, B)`-bimodule to a right DG `B`-module, bundled as a
right DG `A`-module. The abbreviation keeps its carrier available for evaluation. -/
noncomputable abbrev DGBimoduleCat.internalHomObj
    (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (N : DGRightModuleCat.{uR, uB, uN} hB) :
    DGRightModuleCat.{uR, uA, max uM uN} hA :=
  DGRightModuleCat.of (M.isDGBimodule.internalHom N.isDGRightModule)

namespace DGRightModule.InternalHom

variable {M M' M'' : DGBimoduleCat.{uR, uA, uB, uM} hA hB}
  {N N' N'' : DGRightModuleCat.{uR, uB, uN} hB}

private theorem comp_mem_cochains (u : M' ⟶ M) (v : N ⟶ N') {p : ℤ}
    {f : M →ₗ[Bᵐᵒᵖ] N}
    (hf : f ∈ dgRightModuleCochains (R := R) (ℳ := M.grading) (ℳN := N.grading) p) :
    v.toLinearMap ∘ₗ f ∘ₗ u.val.toLinearMap ∈
      dgRightModuleCochains (R := R) (ℳ := M'.grading) (ℳN := N'.grading) p := by
  let u₀ := (dgRightModuleHomEquivZeroCocycles M'.isDGRightModule M.isDGRightModule u.val).1
  let v₀ := (dgRightModuleHomEquivZeroCocycles N.isDGRightModule N'.isDGRightModule v).1
  let c := dgRightModuleCochains.comp v₀
    (dgRightModuleCochains.comp ⟨f, hf⟩ u₀ (add_zero p)) (zero_add p)
  convert c.2 using 1
  ext x
  simp only [c, dgRightModuleCochains.comp_apply, LinearMap.comp_apply,
    u₀, v₀, dgRightModuleHomEquivZeroCocycles_apply, DGRightModuleHom.coe_toLinearMap]

private def mapLinearMap (u : M' ⟶ M) (v : N ⟶ N') :
    InternalHom 𝒜 B M.grading N.grading →ₗ[Aᵐᵒᵖ] InternalHom 𝒜 B M'.grading N'.grading where
  toFun f := ⟨⟨v.toLinearMap ∘ₗ coeLM f ∘ₗ u.val.toLinearMap, by
    induction f using DirectSum.Decomposition.inductionOn (grading 𝒜 B M.grading N.grading) with
    | zero => simp
    | @homogeneous p f =>
      exact Submodule.mem_iSup_of_mem p (comp_mem_cochains u v (mem_grading_iff.1 f.2))
    | add f g hf hg =>
      simpa only [map_add, LinearMap.add_comp, LinearMap.comp_add] using add_mem hf hg⟩⟩
  map_add' f g := ext fun x ↦ by simp
  map_smul' a f := ext fun x ↦ by simp

private theorem mapLinearMap_apply (u : M' ⟶ M) (v : N ⟶ N')
    (f : InternalHom 𝒜 B M.grading N.grading) (x : M') :
    mapLinearMap u v f x = v (f (u x)) := by
  simp [mapLinearMap]

private theorem mapLinearMap_mem (u : M' ⟶ M) (v : N ⟶ N') {p : ℤ}
    {f : InternalHom 𝒜 B M.grading N.grading} (hf : f ∈ grading 𝒜 B M.grading N.grading p) :
    mapLinearMap u v f ∈ grading 𝒜 B M'.grading N'.grading p := by
  rw [mem_grading_iff]
  convert comp_mem_cochains u v (mem_grading_iff.1 hf) using 1
  ext x
  simp [mapLinearMap_apply]

/-- Precompose with a DG bimodule morphism and postcompose with a DG right-module morphism.
The resulting map of internal Homs is a morphism of DG right `A`-modules. -/
noncomputable def map (u : M' ⟶ M) (v : N ⟶ N') :
    M.internalHomObj N ⟶ M'.internalHomObj N' where
  toLinearMap := mapLinearMap u v
  map_mem' := mapLinearMap_mem u v
  map_d' f := by
    induction f using DirectSum.Decomposition.inductionOn (grading 𝒜 B M.grading N.grading) with
    | zero => simp
    | @homogeneous p f =>
      apply ext
      intro x
      simp only [differential_apply_of_mem _ _ (mapLinearMap_mem u v f.2),
        mapLinearMap_apply, differential_apply_of_mem _ _ f.2, map_sub, map_zsmul_unit,
        DGBimoduleCat.map_d, DGRightModuleCat.map_d]
    | add f g hf hg => simp only [map_add, hf, hg]

/-- The induced map sends `f` to `v ∘ f ∘ u`, with no extra sign since `u` and `v` have
 degree zero. -/
@[simp↓]
theorem map_apply (u : M' ⟶ M) (v : N ⟶ N')
    (f : M.internalHomObj N) (x : M') :
    map u v f x = v (f (u x)) := mapLinearMap_apply u v f x

/-- Identity morphisms induce the identity on the internal Hom. -/
@[simp]
theorem map_id_id (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    (N : DGRightModuleCat.{uR, uB, uN} hB) :
    map (𝟙 M) (𝟙 N) = 𝟙 (M.internalHomObj N) := by
  ext f x
  rw [DGRightModuleCat.id_apply (M.internalHomObj N) f, map_apply]
  simp

/-- Internal Hom is contravariant in the bimodule and covariant in the right module. -/
@[simp]
theorem map_comp (u : M' ⟶ M) (u' : M'' ⟶ M') (v : N ⟶ N') (v' : N' ⟶ N'') :
    map u v ≫ map u' v' = map (u' ≫ u) (v ≫ v') := by
  ext f x
  rw [DGRightModuleCat.comp_apply, map_apply, map_apply, map_apply]
  simp

/-- The induced map is additive in its contravariant argument. -/
@[simp]
theorem map_add_left (u u' : M' ⟶ M) (v : N ⟶ N') :
    map (u + u') v = map u v + map u' v := by
  ext f x
  rw [map_apply, DGRightModuleCat.add_apply, add_apply, map_apply, map_apply]
  simp

/-- The induced map is additive in its covariant argument. -/
@[simp]
theorem map_add_right (u : M' ⟶ M) (v v' : N ⟶ N') :
    map u (v + v') = map u v + map u v' := by
  ext f x
  rw [DGRightModuleCat.add_apply (map u v) (map u v') f, add_apply, map_apply, map_apply,
    map_apply]
  simp

/-- The induced map is linear in its contravariant argument over the ground ring. -/
@[simp]
theorem map_smul_left (r : R) (u : M' ⟶ M) (v : N ⟶ N') :
    map (r • u) v = r • map u v := by
  ext f x
  rw [map_apply, DGRightModuleCat.smul_apply, smul_apply, map_apply, DGBimoduleCat.smul_apply]
  exact congrArg v ((coeLM f).map_smul_of_tower r (u x)) |>.trans
    (v.toLinearMap.map_smul_of_tower r (f (u x)))

/-- The induced map is linear in its covariant argument over the ground ring. -/
@[simp]
theorem map_smul_right (r : R) (u : M' ⟶ M) (v : N ⟶ N') :
    map u (r • v) = r • map u v := by
  ext f x
  rw [DGRightModuleCat.smul_apply r (map u v) f, smul_apply, map_apply, map_apply]
  simp

@[simp]
theorem map_zero_left (v : N ⟶ N') : map (0 : M' ⟶ M) v = 0 := by
  ext f x
  rw [map_apply, DGRightModuleCat.zero_apply, zero_apply]
  simp

@[simp]
theorem map_zero_right (u : M' ⟶ M) : map u (0 : N ⟶ N') = 0 := by
  ext f x
  rw [DGRightModuleCat.zero_apply (M := M.internalHomObj N) (N := M'.internalHomObj N') f,
    zero_apply, map_apply]
  simp

end DGRightModule.InternalHom

namespace DGBimoduleCat

open DGRightModule

/-- The internal Hom out of a fixed DG bimodule, as a linear functor on DG right modules.
The carrier lives in the maximum of the bimodule and right-module universes. -/
-- Keep the object carrier reducible for evaluation of morphisms.
noncomputable abbrev internalHom (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    DGRightModuleCat.{uR, uB, uN} hB ⥤ DGRightModuleCat.{uR, uA, max uM uN} hA where
  obj N := M.internalHomObj N
  map v := InternalHom.map (𝟙 M) v
  map_id N := InternalHom.map_id_id M N
  map_comp v v' := by
    simpa only [Category.id_comp] using (InternalHom.map_comp (𝟙 M) (𝟙 M) v v').symm

@[simp]
theorem internalHom_obj (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    (N : DGRightModuleCat.{uR, uB, uN} hB) :
    M.internalHom.obj N = M.internalHomObj N :=
  (rfl)

@[simp]
theorem internalHom_map (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    {N N' : DGRightModuleCat.{uR, uB, uN} hB} (v : N ⟶ N') :
    M.internalHom.map v = InternalHom.map (𝟙 M) v := (rfl)

/-- The internal-Hom functor acts by postcomposition on elements. -/
@[simp↓]
theorem internalHom_map_apply (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    {N N' : DGRightModuleCat.{uR, uB, uN} hB} (v : N ⟶ N')
    (f : M.internalHomObj N) (x : M) :
    M.internalHom.map v f x = v (f x) := by
  rw [internalHom_map, InternalHom.map_apply]
  simp

instance (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    (internalHom.{uR, uA, uB, uM, uN} M).Additive where
  map_add := by intros; exact InternalHom.map_add_right _ _ _

instance (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    (internalHom.{uR, uA, uB, uM, uN} M).Linear R where
  map_smul := fun v r ↦ InternalHom.map_smul_right r (𝟙 M) v

/-- Internal Hom as a bifunctor on DG bimodules and DG right modules, contravariant in the
bimodule. A bimodule morphism acts by precomposition, naturally in the right module. -/
-- Keep the object and component formulas reducible for evaluation.
noncomputable abbrev internalHomFunctor :
    (DGBimoduleCat.{uR, uA, uB, uM} hA hB)ᵒᵖ ⥤
      DGRightModuleCat.{uR, uB, uN} hB ⥤ DGRightModuleCat.{uR, uA, max uM uN} hA where
  obj M := M.unop.internalHom
  map u :=
    { app N := InternalHom.map u.unop (𝟙 N)
      naturality := fun _ _ v ↦ by
        simp only [InternalHom.map_comp, Category.comp_id, Category.id_comp] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact InternalHom.map_id_id M.unop N
  map_comp u u' := by
    apply NatTrans.ext
    funext N
    simp only [NatTrans.comp_app, InternalHom.map_comp, CategoryTheory.unop_comp,
      Category.id_comp]

@[simp]
theorem internalHomFunctor_obj (M : (DGBimoduleCat.{uR, uA, uB, uM} hA hB)ᵒᵖ) :
    internalHomFunctor.obj M = internalHom.{uR, uA, uB, uM, uN} M.unop := (rfl)

@[simp]
theorem internalHomFunctor_map_app {M M' : DGBimoduleCat.{uR, uA, uB, uM} hA hB}
    (u : Opposite.op M ⟶ Opposite.op M') (N : DGRightModuleCat.{uR, uB, uN} hB) :
    (internalHomFunctor.map u).app N = InternalHom.map u.unop (𝟙 N) := (rfl)

/-- The contravariant internal-Hom component acts by precomposition on elements. -/
@[simp↓]
theorem internalHomFunctor_map_app_apply {M M' : DGBimoduleCat.{uR, uA, uB, uM} hA hB}
    (u : Opposite.op M ⟶ Opposite.op M') (N : DGRightModuleCat.{uR, uB, uN} hB)
    (f : M.internalHomObj N) (x : M') :
    (internalHomFunctor.map u).app N f x = f (u.unop x) := by
  rw [internalHomFunctor_map_app, InternalHom.map_apply]
  simp

instance : (internalHomFunctor.{uR, uA, uB, uM, uN} (hA := hA) (hB := hB)).Additive where
  map_add := by
    intros
    apply NatTrans.ext
    funext N
    exact InternalHom.map_add_left _ _ (𝟙 N)

instance : (internalHomFunctor.{uR, uA, uB, uM, uN} (hA := hA) (hB := hB)).Linear R where
  map_smul := by
    intros
    apply NatTrans.ext
    funext N
    exact InternalHom.map_smul_left _ _ (𝟙 N)

end DGBimoduleCat

end TauCeti
