/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic
public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The additive category of Gorenstein-projective modules

The direct sum of two complete resolutions is again a complete resolution. Consequently,
Gorenstein-projective modules contain the zero module and are closed under binary biproducts.
Their full subcategory of modules is therefore additive; this is the ambient category on which
the inherited exact structure and the Frobenius structure will be constructed.

## Main declarations

* `CochainComplex.IsTotallyAcyclic.biprod`: binary biproducts preserve total acyclicity.
* `TauCeti.IsGorensteinProjective.biprod`: binary biproducts preserve
  Gorenstein-projectivity.
* `TauCeti.GorensteinProjectiveModuleCat`: the additive full subcategory of
  Gorenstein-projective modules.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
-/

public section

open CategoryTheory Limits

universe v u

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A]
variable {P Q : CochainComplex (ModuleCat.{v} A) ℤ}

/-- The product of exact pairs of linear maps is exact. -/
private lemma exact_prodMap
    {M₁ N₁ P₁ M₂ N₂ P₂ : Type*}
    [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup P₁]
    [AddCommGroup M₂] [AddCommGroup N₂] [AddCommGroup P₂]
    [Module A M₁] [Module A N₁] [Module A P₁]
    [Module A M₂] [Module A N₂] [Module A P₂]
    {f₁ : M₁ →ₗ[A] N₁} {g₁ : N₁ →ₗ[A] P₁}
    {f₂ : M₂ →ₗ[A] N₂} {g₂ : N₂ →ₗ[A] P₂}
    (h₁ : Function.Exact f₁ g₁) (h₂ : Function.Exact f₂ g₂) :
    Function.Exact (f₁.prodMap f₂) (g₁.prodMap g₂) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y₁, hy₁⟩ := (h₁ x.1).1 (congrArg Prod.fst hx)
    obtain ⟨y₂, hy₂⟩ := (h₂ x.2).1 (congrArg Prod.snd hx)
    exact ⟨(y₁, y₂), by ext <;> assumption⟩
  · rintro ⟨y, rfl⟩
    exact Prod.ext ((h₁ _).2 ⟨y.1, rfl⟩) ((h₂ _).2 ⟨y.2, rfl⟩)

/-- The canonical identification of the sum of the duals with the dual of a biproduct term. -/
private noncomputable def dualBiprodEquiv (n : ℤ) :
    ((P.X n →ₗ[A] A) × (Q.X n →ₗ[A] A)) ≃ₗ[Aᵐᵒᵖ]
      ((P ⊞ Q).X n →ₗ[A] A) where
  toFun φ := φ.1.comp ((biprod.fst : P ⊞ Q ⟶ P).f n).hom +
    φ.2.comp ((biprod.snd : P ⊞ Q ⟶ Q).f n).hom
  invFun φ :=
    (φ.comp ((biprod.inl : P ⟶ P ⊞ Q).f n).hom,
      φ.comp ((biprod.inr : Q ⟶ P ⊞ Q).f n).hom)
  left_inv φ := by
    apply Prod.ext <;> apply LinearMap.ext <;> intro x <;>
      simp [← ModuleCat.comp_apply]
  right_inv φ := by
    apply LinearMap.ext
    intro x
    change φ (((biprod.inl : P ⟶ P ⊞ Q).f n).hom
      (((biprod.fst : P ⊞ Q ⟶ P).f n).hom x)) +
        φ (((biprod.inr : Q ⟶ P ⊞ Q).f n).hom
          (((biprod.snd : P ⊞ Q ⟶ Q).f n).hom x)) = φ x
    rw [← map_add]
    congr 1
    simpa only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_id,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] using
      congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.biprod_total_f P Q n))
  map_add' φ ψ := by
    apply LinearMap.ext
    intro x
    simp
    abel
  map_smul' r φ := by
    apply LinearMap.ext
    intro x
    simp [smul_add]

/-- A binary biproduct of totally acyclic complexes is totally acyclic. -/
theorem biprod (hP : P.IsTotallyAcyclic) (hQ : Q.IsTotallyAcyclic) :
    (P ⊞ Q).IsTotallyAcyclic where
  finite n := by
    have := hP.finite n
    have := hQ.finite n
    exact Module.Finite.equiv
      (HomologicalComplex.biprodXIso P Q n ≪≫ ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv
  projective n := by
    have := hP.projective n
    have := hQ.projective n
    exact Projective.of_iso (HomologicalComplex.biprodXIso P Q n).symm inferInstance
  acyclic n := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    let F := HomologicalComplex.homologyFunctor
      (ModuleCat.{v} A) (ComplexShape.up ℤ) n
    let _ : F.Additive := inferInstance
    let _ : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
    let _ : PreservesBiproductsOfShape WalkingPair F := inferInstance
    let _ : PreservesBinaryBiproducts F :=
      preservesBinaryBiproducts_of_preservesBiproducts F
    refine IsZero.of_iso ?_ (F.mapBiprod P Q)
    rw [biprod_isZero_iff]
    exact ⟨(hP.acyclic n).isZero_homology, (hQ.acyclic n).isZero_homology⟩
  exact_dual i j k hij hjk := by
    let δP (p q : ℤ) := LinearMap.lcomp Aᵐᵒᵖ A (P.d p q).hom
    let δQ (p q : ℤ) := LinearMap.lcomp Aᵐᵒᵖ A (Q.d p q).hom
    let δ (p q : ℤ) := LinearMap.lcomp Aᵐᵒᵖ A ((P ⊞ Q).d p q).hom
    have comm (p q : ℤ) :
        δ p q ∘ₗ (dualBiprodEquiv (P := P) (Q := Q) q).toLinearMap =
          (dualBiprodEquiv (P := P) (Q := Q) p).toLinearMap ∘ₗ
            ((δP p q).prodMap (δQ p q)) := by
      apply LinearMap.ext
      rintro ⟨φ, ψ⟩
      apply LinearMap.ext
      intro x
      change
        φ (((biprod.fst : P ⊞ Q ⟶ P).f q).hom (((P ⊞ Q).d p q).hom x)) +
          ψ (((biprod.snd : P ⊞ Q ⟶ Q).f q).hom (((P ⊞ Q).d p q).hom x)) =
        φ ((P.d p q).hom (((biprod.fst : P ⊞ Q ⟶ P).f p).hom x)) +
          ψ ((Q.d p q).hom (((biprod.snd : P ⊞ Q ⟶ Q).f p).hom x))
      have hfst : ((biprod.fst : P ⊞ Q ⟶ P).f q).hom (((P ⊞ Q).d p q).hom x) =
          (P.d p q).hom (((biprod.fst : P ⊞ Q ⟶ P).f p).hom x) := by
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
          congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom
            ((biprod.fst : P ⊞ Q ⟶ P).comm p q).symm)
      have hsnd : ((biprod.snd : P ⊞ Q ⟶ Q).f q).hom (((P ⊞ Q).d p q).hom x) =
          (Q.d p q).hom (((biprod.snd : P ⊞ Q ⟶ Q).f p).hom x) := by
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
          congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom
            ((biprod.snd : P ⊞ Q ⟶ Q).comm p q).symm)
      rw [hfst, hsnd]
    exact Function.Exact.of_ladder_linearEquiv_of_exact (comm j k) (comm i j)
      (exact_prodMap (hP.exact_dual i j k hij hjk) (hQ.exact_dual i j k hij hjk))

end CochainComplex.IsTotallyAcyclic

namespace TauCeti

variable {A : Type u} [Ring A]

/-- Taking cycles is additive on morphisms of complexes. -/
private lemma cyclesMap_add {X Y : CochainComplex (ModuleCat.{v} A) ℤ} (f g : X ⟶ Y) (n : ℤ) :
    HomologicalComplex.cyclesMap (f + g) n =
      HomologicalComplex.cyclesMap f n + HomologicalComplex.cyclesMap g n := by
  apply (cancel_mono (Y.iCycles n)).1
  simp only [Preadditive.add_comp, HomologicalComplex.cyclesMap_i]
  rfl

/-- Every zero module is Gorenstein-projective. -/
theorem isGorensteinProjective_of_isZero {M : ModuleCat.{v} A} (hM : IsZero M) :
    IsGorensteinProjective A M := by
  have := ModuleCat.subsingleton_of_isZero hM
  have : Module.Finite A M := inferInstance
  have := hM.projective
  exact isGorensteinProjective_of_projective M

/-- A binary biproduct of Gorenstein-projective modules is Gorenstein-projective. -/
theorem IsGorensteinProjective.biprod {M N : ModuleCat.{v} A}
    (hM : IsGorensteinProjective A M) (hN : IsGorensteinProjective A N) :
    IsGorensteinProjective A (M ⊞ N) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := (isGorensteinProjective_iff M).mp hM
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := (isGorensteinProjective_iff N).mp hN
  let F := HomologicalComplex.cyclesFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) 0
  let _ : F.Additive := by
    constructor
    intro X Y f g
    change HomologicalComplex.cyclesMap (f + g) 0 =
      HomologicalComplex.cyclesMap f 0 + HomologicalComplex.cyclesMap g 0
    exact cyclesMap_add f g 0
  let _ : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  let _ : PreservesBiproductsOfShape WalkingPair F := inferInstance
  let _ : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  apply (isGorensteinProjective_iff (M ⊞ N)).mpr
  exact ⟨P ⊞ Q, hP.biprod hQ,
    ⟨F.mapBiprod P Q ≪≫ biprod.mapIso eP eQ⟩⟩

instance : (IsGorensteinProjective.{v} A).ContainsZero where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _,
    isGorensteinProjective_of_isZero (ModuleCat.isZero_of_subsingleton _)⟩

instance : (IsGorensteinProjective.{v} A).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ ↦
    IsGorensteinProjective.biprod

/-- The additive category of finitely generated Gorenstein-projective `A`-modules. -/
abbrev GorensteinProjectiveModuleCat (A : Type u) [Ring A] :=
  (IsGorensteinProjective.{v} A).FullSubcategory

end TauCeti
