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
on homology classes. It is natural in `X`.

When `Y` is an injective object the Kronecker map is a `k`-linear equivalence
`Hⁱ(Hom(X, Y)) ≃ₗ[k] (Hᵢ(X) ⟶ Y)`. This is the universal coefficient theorem in the case where
its `Ext¹`-term vanishes, as it does for an injective coefficient object, such as a vector space
over a field.

## Main definitions and results

* `TauCeti.ChainComplex.kronecker`: the Kronecker map, with
  `TauCeti.ChainComplex.kronecker_homologyπ` computing it on classes of cycles and cocycles and
  `TauCeti.ChainComplex.kronecker_naturality` its naturality.
* `TauCeti.ChainComplex.kronecker_bijective` and `TauCeti.ChainComplex.kroneckerEquiv`: for an
  injective object `Y`, the Kronecker map is a `k`-linear equivalence.

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

/-- For an injective object `Y`, every morphism `Hᵢ(X) ⟶ Y` is the evaluation of a cohomology
class: it extends from the cycles of `X` to a cochain, which is a cocycle. -/
private lemma kronecker_surjective [Injective Y] (i : α) :
    Function.Surjective (kronecker k X Y i) := by
  intro g
  -- extend `g`, viewed on the cycles, along the monomorphism from the cycles into `Xᵢ`
  let φ : X.X i ⟶ Y := Injective.factorThru (X.homologyπ i ≫ g) (X.iCycles i)
  have hφ : X.iCycles i ≫ φ = X.homologyπ i ≫ g := Injective.comp_factorThru _ _
  refine ⟨(X.linearYonedaObj k Y).homologyπ i
    ((X.linearYonedaObj k Y).moduleCatCyclesMk φ _ rfl ?_), ?_⟩
  · refine (linearYonedaObj_d_apply i _ φ).trans ?_
    rw [← X.toCycles_i, Category.assoc, hφ, toCycles_comp_homologyπ_assoc, zero_comp]
    -- the zero morphism is the zero of the cochain module `Hom(Xᵢ₊₁, Y)`
    rfl
  · rw [← cancel_epi (X.homologyπ i), kronecker_homologyπ]
    exact (congrArg (X.iCycles i ≫ ·) (iCycles_moduleCatCyclesMk ..)).trans hφ

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

end TauCeti.ChainComplex
