/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.RingTheory.LocalProperties.Fiber.Splitting

/-!
# Splitting degree-zero cohomology off a nonnegative complex

Let `C` be a nonnegative cochain complex of finite projective modules and let `u : M[0] ⟶ C`
be a map from a finite module in degree zero. If `u` induces an isomorphism on
zeroth cohomology over the residue fields at all maximal ideals, then `C` deformation retracts
onto the sum of `M[0]` and a complex of finite projective modules supported in strictly positive
degrees. The inclusion of `M[0]` is the given map `u`, and the complement inherits any upper
degree bound from `C`. Arbitrary scalar extension preserves the deformation retract, since
it is given by cochain maps and a homotopy.

This is the constants-splitting argument for a finite projective model of the cohomology of the
structure sheaf. The certificate in degrees zero and one comes from
`LinearMap.exists_leftInverse_and_comp_add_comp_eq_id_of_residueField`.
For the cohomological application, see the Stacks Project, Tag
[0E62](https://stacks.math.columbia.edu/tag/0E62).
-/

public section

open CategoryTheory Limits HomologicalComplex
open CochainComplex.HomComplex

attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w w'

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Take the kernel of the idempotent cutting out the degree-zero summand and the
contractible summand in degrees zero and one. -/
private lemma exists_positive_complement
    (C : CochainComplex (ModuleCat.{v} R) ℤ) [C.IsStrictlyGE 0]
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Projective R (C.X i)]
    {M : ModuleCat.{v} R} {u : (single _ (.up ℤ) 0).obj M ⟶ C}
    {ρ : C ⟶ (single _ (.up ℤ) 0).obj M} (hρ : u ≫ ρ = 𝟙 _)
    {n : C ⟶ C} (hn : Homotopy n 0)
    (hp₀ : (ρ ≫ u + n).f 0 = 𝟙 _) (hpp : (ρ ≫ u + n) ≫ (ρ ≫ u + n) = ρ ≫ u + n) :
    ∃ (Q : CochainComplex (ModuleCat.{v} R) ℤ)
      (e : HomotopyEquiv ((single _ (.up ℤ) 0).obj M ⊞ Q) C),
      Q.IsStrictlyGE 1 ∧ (∀ i, Module.Finite R (Q.X i) ∧ Module.Projective R (Q.X i)) ∧
      (∀ b, C.IsStrictlyLE b → Q.IsStrictlyLE b) ∧
      biprod.inl ≫ e.hom = u ∧ e.hom ≫ e.inv = 𝟙 _ := by
  let p := ρ ≫ u + n
  have hp₀' : p.f 0 = 𝟙 _ := hp₀
  have hup : u ≫ p = u := from_single_hom_ext (by simp [hp₀'])
  have hpρ : p ≫ ρ = ρ := to_single_hom_ext (by simp [hp₀'])
  let j := kernel.ι p
  have hpp' : p ≫ p = p := hpp
  let q := kernel.lift p (𝟙 C - p) (by simp [Preadditive.sub_comp, hpp'])
  have hqj : q ≫ j = 𝟙 C - p := kernel.lift_ι _ _ _
  have hjq : j ≫ q = 𝟙 _ := (cancel_mono j).mp (by simp [Category.assoc, hqj, j])
  have huq : u ≫ q = 0 := (cancel_mono j).mp (by simp [Category.assoc, hqj, hup])
  have hjρ : j ≫ ρ = 0 := by rw [← hpρ, ← Category.assoc, kernel.condition, zero_comp]
  have hde : biprod.desc u j ≫ biprod.lift ρ q = 𝟙 _ := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [hρ, huq, hjρ, hjq]
  let e : HomotopyEquiv ((single _ (.up ℤ) 0).obj M ⊞ kernel p) C := {
    hom := biprod.desc u j
    inv := biprod.lift ρ q
    homotopyHomInvId := Homotopy.ofEq hde
    homotopyInvHomId := Homotopy.equivSubZero.symm <|
      (Homotopy.ofEq (by rw [biprod.lift_desc, hqj]; dsimp [p]; abel)).trans
        (Homotopy.equivSubZero hn.symm) }
  have hterm (i : ℤ) (hz : j.f i = 0) : IsZero ((kernel p).X i) := by
    rw [IsZero.iff_id_eq_zero]
    simpa [hz] using (congrArg (fun a ↦ HomologicalComplex.Hom.f a i) hjq).symm
  refine ⟨kernel p, e, (isStrictlyGE_iff _ _).2 (fun i hi ↦ ?_), fun i ↦ ?_, ?_, by simp [e], hde⟩
  · have hj₀ : j.f i = 0 := by
      have hi₀ : i ≤ 0 := by omega
      rcases eq_or_lt_of_le hi₀ with rfl | hlt
      · have hz := congrArg (fun a : kernel p ⟶ C ↦ a.f 0) (kernel.condition p)
        rw [comp_f, zero_f_apply, hp₀', Category.comp_id] at hz
        exact hz
      exact (C.isZero_of_isStrictlyGE 0 i hlt).eq_of_tgt _ _
    exact hterm i hj₀
  · have hh : (q.f i).hom ∘ₗ (j.f i).hom = LinearMap.id :=
      congrArg (fun a : kernel p ⟶ kernel p ↦ (a.f i).hom) hjq
    exact ⟨Module.Finite.of_surjective _ (LinearMap.surjective_of_comp_eq_id _ _ hh),
      Module.Projective.of_split _ _ hh⟩
  · intro b hb
    exact (isStrictlyLE_iff _ b).2 fun i hi ↦
      hterm i ((C.isZero_of_isStrictlyLE b i hi).eq_of_tgt _ _)

/-- The fibrewise tests give a cochain retraction of `u` and a splitting identity in degree zero. -/
private lemma exists_single_retraction_of_residueField
    (C : CochainComplex (ModuleCat.{v} R) ℤ) [C.IsStrictlyGE 0]
    [Module.Finite R (C.X 0)] [Module.Projective R (C.X 0)]
    [Module.Projective R (C.X 1)]
    (M : ModuleCat.{v} R) [Module.Finite R M]
    (u : (single _ (.up ℤ) 0).obj M ⟶ C)
    (hu : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor I.ResidueField))
    (he : ∀ (I : Ideal R) [I.IsMaximal], Function.Exact
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor I.ResidueField)
      ((C.d 0 1).hom.lTensor I.ResidueField)) :
    ∃ (ρ : C ⟶ (single _ (.up ℤ) 0).obj M) (s : C.X 1 ⟶ C.X 0),
      u ≫ ρ = 𝟙 _ ∧ ρ.f 0 ≫ u.f 0 + C.d 0 1 ≫ s = 𝟙 _ := by
  let f := (singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0
  have hf : f ≫ C.d 0 1 = 0 := by simp [f, u.comm]
  obtain ⟨r, s, hr, hsplit⟩ :=
    f.hom.exists_leftInverse_and_comp_add_comp_eq_id_of_residueField (C.d 0 1).hom
      (by simpa using congrArg ModuleCat.Hom.hom hf) hu he
  let ρ : C ⟶ (single _ (.up ℤ) 0).obj M := mkHomToSingle (ModuleCat.ofHom r) (by
    intro i hi
    rw [ComplexShape.up_Rel] at hi
    exact (C.isZero_of_isStrictlyGE 0 i (by omega)).eq_of_src _ _)
  have hρ₀ : ρ.f 0 = ModuleCat.ofHom r ≫ (singleObjXSelf (.up ℤ) 0 M).inv := by
    simp only [ρ, mkHomToSingle_f]
  have hρ : u ≫ ρ = 𝟙 _ := by
    apply from_single_hom_ext
    have h : f ≫ ModuleCat.ofHom r = 𝟙 M := ModuleCat.hom_ext hr
    simpa [comp_f, id_f, hρ₀, f, Category.assoc] using
      congrArg (fun a ↦ (singleObjXSelf (.up ℤ) 0 M).hom ≫ a ≫
        (singleObjXSelf (.up ℤ) 0 M).inv) h
  have hh : ModuleCat.ofHom r ≫ f + C.d 0 1 ≫ ModuleCat.ofHom s = 𝟙 _ :=
    ModuleCat.hom_ext hsplit
  exact ⟨ρ, ModuleCat.ofHom s, hρ, by simpa only [hρ₀, f, Category.assoc] using hh⟩

/-- Splitting off a summand in the lowest cohomological degree. The condition is exactness of
`0 → M ⊗ κ(I) → C⁰ ⊗ κ(I) → C¹ ⊗ κ(I)` at every maximal ideal `I`. The resulting homotopy
equivalence includes the specified copy of `M[0]`. -/
theorem exists_homotopyEquiv_biprod_single_of_residueField
    (C : CochainComplex (ModuleCat.{v} R) ℤ) [C.IsStrictlyGE 0]
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Projective R (C.X i)]
    (M : ModuleCat.{v} R) [Module.Finite R M]
    (u : (single _ (.up ℤ) 0).obj M ⟶ C)
    (hu : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor I.ResidueField))
    (he : ∀ (I : Ideal R) [I.IsMaximal], Function.Exact
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor I.ResidueField)
      ((C.d 0 1).hom.lTensor I.ResidueField)) :
    ∃ (Q : CochainComplex (ModuleCat.{v} R) ℤ)
      (e : HomotopyEquiv ((single _ (.up ℤ) 0).obj M ⊞ Q) C),
      Q.IsStrictlyGE 1 ∧ (∀ i, Module.Finite R (Q.X i) ∧ Module.Projective R (Q.X i)) ∧
      (∀ b, C.IsStrictlyLE b → Q.IsStrictlyLE b) ∧
      biprod.inl ≫ e.hom = u ∧ e.hom ≫ e.inv = 𝟙 _ := by
  obtain ⟨ρ, s, hρ, hsplit⟩ := exists_single_retraction_of_residueField C M u hu he
  -- The boundary of the cochain supported in bidegree `(1, 0)` contracts the first image.
  let h : Cochain C C (-1) := Cochain.single s (-1)
  let n := Cocycle.homOf (Cocycle.mk (δ (-1) 0 h) 1 rfl (δ_δ _ _ _ _))
  have hn : Homotopy n 0 := (Cochain.equivHomotopy n 0).symm ⟨h, by simp [n]⟩
  have hn' (i : ℤ) : n.f i =
      (Cochain.single (s ≫ C.d 0 1) 0 +
        Cochain.single (C.d 0 1 ≫ s) 0).v i i (add_zero i) := by
    simp [n, h, Cochain.δ_single (K := C) (L := C) (p := 1) (q := 0) _ (-1) 0 rfl 0 1 rfl rfl]
  have hn₀ : n.f 0 = C.d 0 1 ≫ s := by
    simpa [Cochain.single_v_eq_zero _ _ _ _ _ (by decide : (0 : ℤ) ≠ 1)] using hn' 0
  let p := ρ ≫ u + n
  have hp₀ : p.f 0 = 𝟙 _ := by
    simpa only [p, add_f_apply, comp_f, hn₀] using hsplit
  have hp₁ : p.f 1 = s ≫ C.d 0 1 := by
    have hz : ρ.f 1 = 0 := (isZero_single_obj_X (.up ℤ) 0 M 1 (by decide)).eq_of_tgt _ _
    simp [p, hz, hn', Cochain.single_v_eq_zero _ _ _ _ _ (by decide : (1 : ℤ) ≠ 0)]
  have hp' (i : ℤ) (hi₀ : i ≠ 0) (hi₁ : i ≠ 1) : p.f i = 0 := by
    have hz : ρ.f i = 0 := (isZero_single_obj_X (.up ℤ) 0 M i hi₀).eq_of_tgt _ _
    simp [p, hz, hn', Cochain.single_v_eq_zero _ _ _ _ _ hi₀,
      Cochain.single_v_eq_zero _ _ _ _ _ hi₁]
  have hpp : p ≫ p = p := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
    by_cases hi₀ : i = 0
    · subst i
      simp [hp₀]
    by_cases hi₁ : i = 1
    · subst i
      -- Since the degree-zero component is the identity, the differential is fixed by `p`.
      have hd : C.d 0 1 ≫ p.f 1 = C.d 0 1 := by simpa [hp₀] using (p.comm 0 1).symm
      simpa only [comp_f, hp₁, Category.assoc] using
        congrArg (fun a ↦ s ≫ a) hd
    simp [hp' _ hi₀ hi₁]
  exact exists_positive_complement C hρ hn hp₀ hpp

/-- A map from `M[0]` to a nonnegative complex which induces an isomorphism on degree-zero
cohomology over the residue field at every maximal ideal still induces one after applying any
additive functor into a category with homology, in particular after arbitrary extension of
scalars. The source `M` is finite, `C⁰` is finite projective, and `C¹` is projective. -/
theorem isIso_homologyMap_zero_of_residueField
    {C : CochainComplex (ModuleCat.{v} R) ℤ} [C.IsStrictlyGE 0]
    [Module.Finite R (C.X 0)] [Module.Projective R (C.X 0)]
    [Module.Projective R (C.X 1)]
    {M : ModuleCat.{v} R} [Module.Finite R M]
    (u : (single _ (.up ℤ) 0).obj M ⟶ C)
    (hu : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor I.ResidueField))
    (he : ∀ (I : Ideal R) [I.IsMaximal], Function.Exact
      (((singleObjXSelf (.up ℤ) 0 M).inv ≫ u.f 0).hom.lTensor I.ResidueField)
      ((C.d 0 1).hom.lTensor I.ResidueField))
    {D : Type w} [Category.{w'} D] [Preadditive D] [CategoryWithHomology D]
    (F : ModuleCat.{v} R ⥤ D) [F.Additive] :
    IsIso (homologyMap ((F.mapHomologicalComplex (.up ℤ)).map u) 0) := by
  obtain ⟨ρ, s, hρ, hsplit⟩ := exists_single_retraction_of_residueField C M u hu he
  let G := F.mapHomologicalComplex (.up ℤ)
  let H := G ⋙ homologyFunctor D (.up ℤ) 0
  have hF : F.map (ρ.f 0) ≫ F.map (u.f 0) + F.map (C.d 0 1) ≫ F.map s = 𝟙 _ := by
    simpa only [F.map_add, F.map_comp, F.map_id] using congrArg F.map hsplit
  -- The differential term of the mapped splitting identity vanishes on cycles.
  have hright : H.map (ρ ≫ u) = H.map (𝟙 C) := by
    apply homologyMap_eq_of_iCycles_comp
    simp only [G, Functor.mapHomologicalComplex_map_f, comp_f, F.map_comp, id_f, F.map_id]
    rw [← hF, Preadditive.comp_add, ← Functor.mapHomologicalComplex_obj_d]
    simp only [iCycles_d_assoc, zero_comp, add_zero]
  have : IsIso (H.map u) := ⟨⟨H.map ρ, by rw [← H.map_comp, hρ, H.map_id], by
    rw [← H.map_comp, hright, H.map_id]⟩⟩
  exact this

end CochainComplex
