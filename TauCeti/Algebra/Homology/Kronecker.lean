/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.Algebra.Homology.ModuleCat

/-!
# The Kronecker map from cohomology to morphisms out of homology

Let `X` be a chain complex in a `k`-linear abelian category `C` and let `Y : C`. A cocycle of the
cochain complex `Hom(X, Y)` (`ChainComplex.linearYonedaObj`) of degree `i` is a morphism
`φ : Xᵢ ⟶ Y` vanishing on boundaries, so its restriction to the cycles of `X` descends to a
morphism `Hᵢ(X) ⟶ Y`; the restriction of a coboundary to the cycles is zero. This gives the
`k`-linear **Kronecker map** `Hⁱ(Hom(X, Y)) →ₗ[k] (Hᵢ(X) ⟶ Y)`, which evaluates cohomology classes
on homology classes. It is natural in both `X` and `Y`.

When `Y` is an injective object the Kronecker map is a `k`-linear equivalence
`Hⁱ(Hom(X, Y)) ≃ₗ[k] (Hᵢ(X) ⟶ Y)`. This is the universal coefficient theorem in the case where
its `Ext¹`-term vanishes, as it does for an injective coefficient object, such as a vector space
over a field.

## Main definitions and results

* `TauCeti.ChainComplex.kronecker`: the Kronecker map, with
  `TauCeti.ChainComplex.kronecker_homologyπ` computing it on classes of cycles and cocycles and
  `TauCeti.ChainComplex.kronecker_naturality` its naturality.
* `TauCeti.ChainComplex.homologyClassOfComp`: the class of the cocycle `f ≫ g` for a cochain
  `f : Xᵢ ⟶ A` vanishing on boundaries, with
  `TauCeti.ChainComplex.homologyπ_kronecker_homologyClassOfComp` computing its Kronecker image.
* `TauCeti.ChainComplex.kroneckerSection`: a `k`-linear right inverse of the Kronecker map, built
  from a retraction of the inclusion of the cycles, with
  `TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono`.
* `TauCeti.ChainComplex.kronecker_bijective` and `TauCeti.ChainComplex.kroneckerEquiv`: for an
  injective object `Y`, the Kronecker map is a `k`-linear equivalence.
* `TauCeti.ChainComplex.kronecker_bijective_of_isIso`: the Kronecker map is bijective in a degree
  without outgoing differential, such as degree zero of a chain complex indexed by `ℕ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, the map `h : Hⁿ(C; G) → Hom(Hₙ(C), G)` and the universal coefficient theorem.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C] {α : Type*} [AddRightCancelSemigroup α] [One α]
  {k : Type*} [Ring k] [Linear k C] {X : ChainComplex C α} {Y : C}

/-- The morphism `Hᵢ(X) ⟶ Y` induced by a cocycle of `Hom(X, Y)`: the cocycle vanishes on
boundaries, so it factors through the opcycles of `X`. -/
private def kroneckerOfCycles (i : α) (φ : (X.linearYonedaObj k Y).cycles i) :
    X.homology i ⟶ Y :=
  X.homologyι i ≫ X.descOpcycles ((X.linearYonedaObj k Y).iCycles i φ)
    ((ComplexShape.down α).prev i) rfl (d_comp_linearYonedaObj_iCycles i _ φ)

@[reassoc]
private lemma homologyπ_kroneckerOfCycles (i : α) (φ : (X.linearYonedaObj k Y).cycles i) :
    X.homologyπ i ≫ kroneckerOfCycles i φ =
      X.iCycles i ≫ (X.linearYonedaObj k Y).iCycles i φ := by
  rw [kroneckerOfCycles, homology_π_ι_assoc]
  exact congrArg (X.iCycles i ≫ ·) (X.p_descOpcycles _ _ _ _)

variable (k X Y) in
/-- The Kronecker map on cocycles, as a morphism of `k`-modules. -/
private def kroneckerCyclesHom (i : α) :
    (X.linearYonedaObj k Y).cycles i ⟶ ModuleCat.of k (X.homology i ⟶ Y) :=
  ModuleCat.ofHom (X := (X.linearYonedaObj k Y).cycles i)
    { toFun φ := kroneckerOfCycles i φ
      map_add' φ φ' := by
        rw [← cancel_epi (X.homologyπ i), Preadditive.comp_add, homologyπ_kroneckerOfCycles,
          homologyπ_kroneckerOfCycles, homologyπ_kroneckerOfCycles]
        exact (congrArg (X.iCycles i ≫ ·) (map_add _ φ φ')).trans (Preadditive.comp_add ..)
      map_smul' r φ := by
        rw [← cancel_epi (X.homologyπ i), RingHom.id_apply, Linear.comp_smul,
          homologyπ_kroneckerOfCycles, homologyπ_kroneckerOfCycles]
        exact (congrArg (X.iCycles i ≫ ·) (map_smul _ r φ)).trans (Linear.comp_smul ..) }

/-- The Kronecker map vanishes on coboundaries: a coboundary restricts to zero on the cycles. -/
private lemma kroneckerOfCycles_toCycles (i j : α) (x : (X.linearYonedaObj k Y).X j) :
    kroneckerOfCycles i ((X.linearYonedaObj k Y).toCycles j i x) = 0 := by
  rw [← cancel_epi (X.homologyπ i), homologyπ_kroneckerOfCycles,
    linearYonedaObj_iCycles_toCycles_apply, comp_zero]
  exact (X.iCycles_d_assoc i j x).trans zero_comp

/-- The Kronecker map on cocycles, as a morphism of `k`-modules, vanishes on coboundaries. -/
private lemma toCycles_comp_kroneckerCyclesHom (i : α) :
    (X.linearYonedaObj k Y).toCycles ((ComplexShape.up α).prev i) i ≫
      kroneckerCyclesHom k X Y i = 0 := by
  ext x : 2
  exact kroneckerOfCycles_toCycles i _ x

variable (k X Y) in
/-- **The Kronecker map** `Hⁱ(Hom(X, Y)) →ₗ[k] (Hᵢ(X) ⟶ Y)`: the class of a cocycle `φ` is sent to
the morphism which on the class of a cycle is `φ` evaluated on that cycle
(`TauCeti.ChainComplex.kronecker_homologyπ`). -/
def kronecker (i : α) : (X.linearYonedaObj k Y).homology i →ₗ[k] (X.homology i ⟶ Y) :=
  (CokernelCofork.IsColimit.desc' ((X.linearYonedaObj k Y).homologyIsCokernel _ i rfl)
    (kroneckerCyclesHom k X Y i) (toCycles_comp_kroneckerCyclesHom i)).1.hom

/-- **The Kronecker map on classes**: evaluating the class of a cocycle `φ` on the class of a
cycle is evaluating `φ` on the cycle. -/
@[reassoc (attr := simp)]
lemma kronecker_homologyπ (i : α) (φ : (X.linearYonedaObj k Y).cycles i) :
    X.homologyπ i ≫ kronecker k X Y i ((X.linearYonedaObj k Y).homologyπ i φ) =
      X.iCycles i ≫ (X.linearYonedaObj k Y).iCycles i φ := by
  have hfac := ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    ((X.linearYonedaObj k Y).homologyIsCokernel _ i rfl) (kroneckerCyclesHom k X Y i)
    (toCycles_comp_kroneckerCyclesHom i)).2 φ
  rw [kronecker]
  exact (congrArg (X.homologyπ i ≫ ·) hfac).trans (homologyπ_kroneckerOfCycles i φ)

/-- **Naturality of the Kronecker map**: evaluating the pull-back of a class along a chain map
`f : X' ⟶ X` is evaluating the class after pushing forward along `f`. -/
lemma kronecker_naturality {X' : ChainComplex C α} (f : X' ⟶ X) (i : α)
    (x : (X.linearYonedaObj k Y).homology i) :
    kronecker k X' Y i
        (homologyMap (K := X.linearYonedaObj k Y) (L := X'.linearYonedaObj k Y)
          ((linearYonedaFunctor k Y).map f.op) i x) =
      homologyMap f i ≫ kronecker k X Y i x := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ i x
  rw [homologyMap_linearYonedaFunctor_map_homologyπ_apply, ← cancel_epi (X'.homologyπ i),
    kronecker_homologyπ, homologyπ_naturality_assoc, kronecker_homologyπ]
  exact (congrArg (X'.iCycles i ≫ ·) (iCycles_cyclesMap_linearYonedaFunctor_map_apply f i φ)).trans
    (cyclesMap_i_assoc f i _).symm

/-- Evaluation of cohomology on homology commutes with changing the coefficient object. -/
lemma kronecker_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : α)
    (x : (X.linearYonedaObj k Y).homology i) :
    kronecker k X Z i (homologyMap (X.linearYonedaObjMap k g) i x) =
      kronecker k X Y i x ≫ g := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ i x
  have hπ := ConcreteCategory.congr_hom (homologyπ_naturality (X.linearYonedaObjMap k g) i) φ
  simp only [ModuleCat.comp_apply] at hπ
  rw [hπ, ← cancel_epi (X.homologyπ i), kronecker_homologyπ, kronecker_homologyπ_assoc]
  have hcyc := ConcreteCategory.congr_hom (cyclesMap_i (X.linearYonedaObjMap k g) i) φ
  simp only [ModuleCat.comp_apply] at hcyc
  exact (congrArg (X.iCycles i ≫ ·)
    (hcyc.trans (X.linearYonedaObjMap_f_hom_apply k g i _))).trans (Category.assoc _ _ _).symm

variable (k Y) in
/-- For a morphism `f : Xᵢ ⟶ A` vanishing on the boundaries coming from `Xᵢ₊₁`, the `k`-linear map
sending `g : A ⟶ Y` to the cocycle `f ≫ g` of `Hom(X, Y)`. -/
def cocycleOfComp {i : α} {A : C} (f : X.X i ⟶ A)
    (hf : X.d ((ComplexShape.up α).next i) i ≫ f = 0) :
    (A ⟶ Y) →ₗ[k] (X.linearYonedaObj k Y).cycles i :=
  ((X.linearYonedaObj k Y).liftCycles (ModuleCat.ofHom (Linear.leftComp k Y f)) _ rfl (by
    ext g
    refine (linearYonedaObj_d_apply _ _ (f ≫ g)).trans ?_
    rw [reassoc_of% hf, zero_comp]
    -- the zero morphism is the zero of the cochain module `Hom(Xᵢ₊₁, Y)`
    rfl)).hom

/-- The cocycle `cocycleOfComp k Y f hf g` has underlying cochain `f ≫ g`. -/
@[simp]
lemma iCycles_cocycleOfComp {i : α} {A : C} (f : X.X i ⟶ A)
    (hf : X.d ((ComplexShape.up α).next i) i ≫ f = 0) (g : A ⟶ Y) :
    (X.linearYonedaObj k Y).iCycles i (cocycleOfComp k Y f hf g) = f ≫ g := by
  rw [cocycleOfComp]
  exact ConcreteCategory.congr_hom ((X.linearYonedaObj k Y).liftCycles_i
    (ModuleCat.ofHom (Linear.leftComp k Y f)) _ rfl _) g

variable (k Y) in
/-- For a morphism `f : Xᵢ ⟶ A` vanishing on the boundaries coming from `Xᵢ₊₁`, the `k`-linear map
sending `g : A ⟶ Y` to the cohomology class of the cocycle `f ≫ g` of `Hom(X, Y)`. -/
def homologyClassOfComp {i : α} {A : C} (f : X.X i ⟶ A)
    (hf : X.d ((ComplexShape.up α).next i) i ≫ f = 0) :
    (A ⟶ Y) →ₗ[k] (X.linearYonedaObj k Y).homology i :=
  ((X.linearYonedaObj k Y).homologyπ i).hom ∘ₗ cocycleOfComp k Y f hf

/-- `homologyClassOfComp k Y f hf g` is the class of any cocycle with underlying cochain
`f ≫ g`. -/
lemma homologyClassOfComp_eq {i : α} {A : C} (f : X.X i ⟶ A)
    (hf : X.d ((ComplexShape.up α).next i) i ≫ f = 0) (g : A ⟶ Y)
    (φ : (X.linearYonedaObj k Y).cycles i) (hφ : (X.linearYonedaObj k Y).iCycles i φ = f ≫ g) :
    homologyClassOfComp k Y f hf g = (X.linearYonedaObj k Y).homologyπ i φ :=
  congrArg ((X.linearYonedaObj k Y).homologyπ i) (HomologicalComplex.moduleCat_iCycles_injective
    _ _ ((iCycles_cocycleOfComp f hf g).trans hφ.symm))

/-- The Kronecker map sends `homologyClassOfComp k Y f hf g` to the morphism `Hᵢ(X) ⟶ Y` which on
cycles is `f ≫ g`. -/
@[reassoc (attr := simp)]
lemma homologyπ_kronecker_homologyClassOfComp {i : α} {A : C} (f : X.X i ⟶ A)
    (hf : X.d ((ComplexShape.up α).next i) i ≫ f = 0) (g : A ⟶ Y) :
    X.homologyπ i ≫ kronecker k X Y i (homologyClassOfComp k Y f hf g) = X.iCycles i ≫ f ≫ g := by
  rw [homologyClassOfComp_eq f hf g _ (iCycles_cocycleOfComp f hf g), kronecker_homologyπ,
    iCycles_cocycleOfComp]

/-- For an injective object `Y`, every morphism `Hᵢ(X) ⟶ Y` is the evaluation of a cohomology
class: it extends from the cycles of `X` to a cochain, which is a cocycle. -/
private lemma kronecker_surjective [Injective Y] (i : α) :
    Function.Surjective (kronecker k X Y i) := fun g ↦
  -- extend `g`, viewed on the cycles, along the monomorphism from the cycles into `Xᵢ`
  ⟨homologyClassOfComp k Y (Injective.factorThru (X.homologyπ i ≫ g) (X.iCycles i)) (by
    rw [← X.toCycles_i, Category.assoc, Injective.comp_factorThru, toCycles_comp_homologyπ_assoc,
      zero_comp]) (𝟙 Y), by
    rw [← cancel_epi (X.homologyπ i), homologyπ_kronecker_homologyClassOfComp, Category.comp_id,
      Injective.comp_factorThru]⟩

/-- For an injective object `Y`, a cohomology class evaluating to zero is zero: a cocycle
vanishing on the cycles is the coboundary of an extension of its factorization through the
coimage of the differential. -/
private lemma kronecker_injective [Injective Y] (i : α) :
    Function.Injective (kronecker k X Y i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ i x
  -- name the underlying cochain with its morphism type `Xᵢ ⟶ Y`, so that composites with it can
  -- be rewritten; as an element of the cochain module its type is not syntactically a hom-type
  obtain ⟨a, ha⟩ : ∃ a : X.X i ⟶ Y, (X.linearYonedaObj k Y).iCycles i φ = a := ⟨_, rfl⟩
  let j := (ComplexShape.down α).next i
  -- the cocycle vanishes on the cycles, so on the kernel of the differential `Xᵢ ⟶ Xⱼ`
  have hcyc : X.iCycles i ≫ a = 0 := by
    rw [← ha, ← kronecker_homologyπ, hx, comp_zero]
  have hker : kernel.ι (X.d i j) ≫ a = 0 := by
    rw [← X.liftCycles_i (kernel.ι (X.d i j)) j rfl (kernel.condition _), Category.assoc, hcyc,
      comp_zero]
  -- extend its factorization through the coimage along the monomorphism into `Xⱼ`
  let b : X.X j ⟶ Y :=
    Injective.factorThru (cokernel.desc _ a hker) (Abelian.factorThruCoimage (X.d i j))
  have hb : X.d i j ≫ b = a := by
    rw [← Abelian.coimage.fac (X.d i j), Category.assoc, Injective.comp_factorThru]
    exact cokernel.π_desc _ _ _
  have hφ : (X.linearYonedaObj k Y).toCycles j i b = φ :=
    HomologicalComplex.moduleCat_iCycles_injective _ _
      ((linearYonedaObj_iCycles_toCycles_apply j i b).trans (hb.trans ha.symm))
  rw [← hφ]
  exact linearYonedaObj_homologyπ_toCycles_apply j i b

/-- **The universal coefficient theorem for injective coefficients**: for an injective object `Y`,
the Kronecker map `Hⁱ(Hom(X, Y)) →ₗ[k] (Hᵢ(X) ⟶ Y)` is bijective. -/
theorem kronecker_bijective [Injective Y] (i : α) : Function.Bijective (kronecker k X Y i) :=
  ⟨kronecker_injective i, kronecker_surjective i⟩

variable (k X Y) in
/-- The Kronecker map as a `k`-linear equivalence `Hⁱ(Hom(X, Y)) ≃ₗ[k] (Hᵢ(X) ⟶ Y)`, for an
injective object `Y`. -/
def kroneckerEquiv [Injective Y] (i : α) :
    (X.linearYonedaObj k Y).homology i ≃ₗ[k] (X.homology i ⟶ Y) :=
  LinearEquiv.ofBijective (kronecker k X Y i) (kronecker_bijective i)

/-- The equivalence `TauCeti.ChainComplex.kroneckerEquiv` is the Kronecker map. -/
@[simp]
lemma kroneckerEquiv_apply [Injective Y] (i : α) (x : (X.linearYonedaObj k Y).homology i) :
    kroneckerEquiv k X Y i x = kronecker k X Y i x :=
  (rfl)

variable (k X Y) in
/-- **The splitting of the universal coefficient sequence**: given a retraction of the inclusion
of the cycles `Zᵢ ⟶ Xᵢ`, the `k`-linear right inverse of the Kronecker map sending `g : Hᵢ(X) ⟶ Y`
to the class of the cocycle `Xᵢ ⟶ Zᵢ ⟶ Hᵢ(X) ⟶ Y`. It depends on the chosen retraction. -/
def kroneckerSection (i : α) [IsSplitMono (X.iCycles i)] :
    (X.homology i ⟶ Y) →ₗ[k] (X.linearYonedaObj k Y).homology i :=
  homologyClassOfComp k Y (retraction (X.iCycles i) ≫ X.homologyπ i) (by
    rw [← X.toCycles_i, Category.assoc, IsSplitMono.id_assoc, toCycles_comp_homologyπ])

/-- `kroneckerSection k X Y i g` is the class of the cocycle `Xᵢ ⟶ Zᵢ ⟶ Hᵢ(X) ⟶ Y` built from the
chosen retraction of the cycles. -/
lemma kroneckerSection_apply (i : α) [IsSplitMono (X.iCycles i)] (g : X.homology i ⟶ Y)
    (φ : (X.linearYonedaObj k Y).cycles i)
    (hφ : (X.linearYonedaObj k Y).iCycles i φ = retraction (X.iCycles i) ≫ X.homologyπ i ≫ g) :
    kroneckerSection k X Y i g = (X.linearYonedaObj k Y).homologyπ i φ :=
  homologyClassOfComp_eq _ _ g φ (hφ.trans (Category.assoc ..).symm)

/-- `TauCeti.ChainComplex.kroneckerSection` is a right inverse of the Kronecker map. -/
@[simp]
lemma kronecker_kroneckerSection (i : α) [IsSplitMono (X.iCycles i)] (g : X.homology i ⟶ Y) :
    kronecker k X Y i (kroneckerSection k X Y i g) = g := by
  rw [← cancel_epi (X.homologyπ i), kroneckerSection, homologyπ_kronecker_homologyClassOfComp,
    Category.assoc, IsSplitMono.id_assoc]

/-- If the inclusion of the cycles `Zᵢ ⟶ Xᵢ` is a split monomorphism, then every morphism
`Hᵢ(X) ⟶ Y` is the evaluation of a cohomology class of `Hom(X, Y)`. -/
theorem kronecker_surjective_of_isSplitMono (i : α) [IsSplitMono (X.iCycles i)] :
    Function.Surjective (kronecker k X Y i) :=
  fun g ↦ ⟨kroneckerSection k X Y i g, kronecker_kroneckerSection i g⟩

/-- If the inclusion of the cycles `Zᵢ ⟶ Xᵢ` is an isomorphism, as in degree zero of a chain
complex indexed by `ℕ`, the Kronecker map is injective: a cocycle vanishing on the cycles is
zero. -/
theorem kronecker_injective_of_isIso (i : α) [IsIso (X.iCycles i)] :
    Function.Injective (kronecker k X Y i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ i x
  -- name the underlying cochain with its morphism type `Xᵢ ⟶ Y`, so that it can be cancelled
  obtain ⟨a, ha⟩ : ∃ a : X.X i ⟶ Y, (X.linearYonedaObj k Y).iCycles i φ = a := ⟨_, rfl⟩
  have ha0 : a = 0 := by
    rw [← cancel_epi (X.iCycles i), ← ha, ← kronecker_homologyπ, hx, comp_zero, comp_zero]
  rw [HomologicalComplex.moduleCat_iCycles_injective _ _ ((ha.trans ha0).trans (map_zero _).symm),
    map_zero]

/-- **The Kronecker map in the absence of outgoing differentials**: if the inclusion of the cycles
`Zᵢ ⟶ Xᵢ` is an isomorphism, as in degree zero of a chain complex indexed by `ℕ`, the Kronecker
map `Hⁱ(Hom(X, Y)) →ₗ[k] (Hᵢ(X) ⟶ Y)` is bijective, for every object `Y`. -/
theorem kronecker_bijective_of_isIso (i : α) [IsIso (X.iCycles i)] :
    Function.Bijective (kronecker k X Y i) :=
  ⟨kronecker_injective_of_isIso i, kronecker_surjective_of_isSplitMono i⟩

end TauCeti.ChainComplex
