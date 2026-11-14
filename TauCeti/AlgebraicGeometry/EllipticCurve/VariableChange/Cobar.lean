/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.HopfAlgebroid
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Nerve

/-!
# The cobar construction of the Weierstrass Hopf algebroid

Let `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and `Γ = A[u, u⁻¹, r, s, t]` be the rings of objects and arrows
of the Weierstrass Hopf algebroid. Its cobar construction is the cosimplicial commutative ring
`[n] ↦ Γ^{⊗_A n}`, whose alternating coface complex is the cobar complex computing
`Ext_Γ(A, A)`. This file constructs it and compares it with the groupoid of Weierstrass curves.

The `n`-fold tensor power `Γ ⊗_A ⋯ ⊗_A Γ` is the ring `cobarRing n`, obtained from `A` by
adjoining `n` times the coordinates `u, u⁻¹, r, s, t` of a change of variables
(`TauCeti.WeierstrassChange.ChangeRing`). A homomorphism `cobarRing n →+* R` is therefore a
Weierstrass curve `W` over `R` together with `n` changes of variables `C₀, …, Cₙ₋₁` over `R`
(`cobarRingEquiv`), that is, a string `W → C₀ • W → C₁ • C₀ • W → ⋯` of `n` composable arrows
of the action groupoid of `VariableChange R` on `WeierstrassCurve R` (`cobarChainEquiv`). These
are the `n`-simplices of the nerve of that groupoid. The structure maps `cobarMap` of the
cosimplicial ring `cobarObject` are defined so that this identification is natural in `[n]`
(`cobarChainEquiv_comp_cobarMap`) and in `R` (`cobarChainEquiv_comp`): the cobar construction
corepresents the nerve of the Weierstrass groupoid, as a functor of the coefficient ring. Every
coefficient ring is allowed, including rings with nilpotents and the zero ring.

In low degrees the structure maps are those of the Hopf algebroid: the two cofaces `A → Γ` are
the right unit `η_R` and the left unit `η_L`, the codegeneracy `Γ → A` is the counit `ε`, and the
three cofaces `Γ → Γ ⊗_A Γ` are the inclusion `ChangeRing.map η_R` of the second factor, the
coproduct `Δ` and the inclusion `algebraMap` of the first factor. These are the cofaces of the
unnormalised cobar complex of `(A, Γ)` with coefficients in `A`, whose `n`-cochains are
`Γ^{⊗_A n}`; here every coface is the one dual to the corresponding face of the nerve. The
alternating coface complex is `cobarComplex`. Its differential in degree `0` is `η_R - η_L`, and
its degree `0` cocycles are the integral modular forms of weight `0`.

## Main definitions

* `TauCeti.WeierstrassHopfAlgebroid.cobarRing`: the ring `Γ^{⊗_A n}`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarChainEquiv`: homomorphisms `Γ^{⊗_A n} →+* R` classify
  strings of `n` composable arrows of Weierstrass curves over `R`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarObject`: the cosimplicial commutative ring
  `[n] ↦ Γ^{⊗_A n}`, with structure maps `cobarMap`.
* `TauCeti.WeierstrassHopfAlgebroid.cobarComplex`: its alternating coface complex.

## Main results

* `cobarChainEquiv_comp_cobarMap`: precomposition with the structure map of `f : [m] ⟶ [n]` is
  the simplicial operator of `f` on the nerve of the Weierstrass groupoid;
  `cobarRingEquiv_comp_cobarMap` is the same statement in coordinates.
* `cobarMap_δ_zero_eq_rightUnit`, `cobarMap_δ_one_eq_algebraMap`, `cobarMap_σ_zero_eq_counit`:
  the cofaces `A → Γ` are `η_R` and `η_L`, and the codegeneracy `Γ → A` is `ε`.
* `cobarMap_δ_zero_eq_map_rightUnit`, `cobarMap_δ_one_eq_coproduct`,
  `cobarMap_δ_two_eq_algebraMap`: the cofaces `Γ → Γ ⊗_A Γ` are the inclusion of the second
  factor, the coproduct `Δ` and the inclusion of the first factor.
* `cobarComplex_d_zero_one`: the differential of the cobar complex in degree `0` is `η_R - η_L`.
* `WeierstrassCurve.isIntegralModularForm_zero_iff_cobarComplex_d_eq_zero`: the degree `0`
  cocycles of the cobar complex are the integral modular forms of weight `0`.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A1.2
  (the cobar complex of a Hopf algebroid, Definition A1.2.11).
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3 (the Weierstrass Hopf algebroid and
  its cobar complex).
-/

public section

noncomputable section

universe u

open CategoryTheory MvPolynomial

namespace TauCeti.WeierstrassHopfAlgebroid

open _root_.WeierstrassCurve TauCeti.WeierstrassChange TauCeti.WeierstrassChange.ChangeRing
  TauCeti.ActionGroupoid

/-! ### The rings `Γ^{⊗_A n}` -/

/-- The ring `Γ^{⊗_A n} = Γ ⊗_A ⋯ ⊗_A Γ` of strings of `n` composable arrows of the Weierstrass
Hopf algebroid: `A = ℤ[a₁, ⋯, a₆]` for `n = 0`, and `cobarRing n` with the coordinates
`u, u⁻¹, r, s, t` of one more change of variables adjoined for `n + 1`. The adjoined coordinates
are those of the last arrow. So `cobarRing 1` is `ArrowRing` and `cobarRing 2` is
`ChangeRing ArrowRing`, the ring `Γ ⊗_A Γ` of the coproduct. -/
abbrev cobarRing : ℕ → CommRingCat.{0}
  | 0 => CommRingCat.of (MvPolynomial Coeff ℤ)
  | n + 1 => CommRingCat.of (ChangeRing (cobarRing n))

variable (R : Type u) [CommRing R]

/-- Homomorphisms `Γ^{⊗_A n} →+* R` classify a Weierstrass curve `W` over `R` with `n` changes of
variables `C₀, …, Cₙ₋₁` over `R`: the string of composable arrows
`W → C₀ • W → C₁ • C₀ • W → ⋯`. -/
def cobarRingEquiv : (n : ℕ) → (cobarRing n →+* R) ≃ WeierstrassCurve R × (Fin n → VariableChange R)
  | 0 =>
    { toFun k := (WeierstrassCurve.map Universal.curve k, Fin.elim0)
      invFun p := p.1.specialize
      left_inv k := by
        -- Beta-reduce the goal produced by `Function.LeftInverse`.
        beta_reduce
        rw [specialize_map, Universal.specialize_curve, RingHom.comp_id]
      right_inv p := Prod.ext (map_specialize p.1) (funext fun i ↦ i.elim0) }
  | n + 1 => lift.symm.trans <| ((cobarRingEquiv n).prodCongr (Equiv.refl _)).trans <|
      (Equiv.prodAssoc _ _ _).trans <| Equiv.prodCongr (Equiv.refl _) <|
        (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ ↦ VariableChange R)

/-- A homomorphism `k : A →+* R` classifies the specialization of the universal curve along `k`,
with no arrows. -/
theorem cobarRingEquiv_zero_apply (k : cobarRing 0 →+* R) :
    cobarRingEquiv R 0 k = (WeierstrassCurve.map Universal.curve k, Fin.elim0) :=
  (rfl)

/-- The homomorphism `A →+* R` classifying a curve `W` is the specialization `W.specialize`. -/
theorem cobarRingEquiv_zero_symm_apply (p : WeierstrassCurve R × (Fin 0 → VariableChange R)) :
    (cobarRingEquiv R 0).symm p = p.1.specialize :=
  (rfl)

/-- The string classified by `k : Γ^{⊗_A (n + 1)} →+* R` consists of the string classified by the
restriction of `k` to the first `n` factors, followed by the change of variables classified by `k`
on the last factor. -/
theorem cobarRingEquiv_succ_apply (n : ℕ) (k : cobarRing (n + 1) →+* R) :
    cobarRingEquiv R (n + 1) k =
      ((cobarRingEquiv R n (k.comp (algebraMap (cobarRing n) (cobarRing (n + 1))))).1,
        Fin.snoc (cobarRingEquiv R n (k.comp (algebraMap (cobarRing n) (cobarRing (n + 1))))).2
          ((universalChange (cobarRing n)).map k)) := by
  simp [cobarRingEquiv]

/-- The homomorphism `Γ^{⊗_A (n + 1)} →+* R` classifying a string of `n + 1` arrows restricts on the
first `n` factors to the homomorphism classifying its first `n` arrows, and classifies its last
change of variables on the last factor. -/
theorem cobarRingEquiv_succ_symm_apply (n : ℕ)
    (p : WeierstrassCurve R × (Fin (n + 1) → VariableChange R)) :
    (cobarRingEquiv R (n + 1)).symm p =
      lift ((cobarRingEquiv R n).symm (p.1, Fin.init p.2), p.2 (Fin.last n)) :=
  (rfl)

variable {R} in
/-- The classification of `cobarRingEquiv` is natural in the coefficient ring: composing with
`φ : R →+* S` base changes the curve and every change of variables along `φ`. -/
theorem cobarRingEquiv_comp {S : Type*} [CommRing S] (φ : R →+* S) :
    ∀ (n : ℕ) (k : cobarRing n →+* R), cobarRingEquiv S n (φ.comp k) =
      ((cobarRingEquiv R n k).1.map φ, fun i ↦ ((cobarRingEquiv R n k).2 i).map φ)
  | 0, k => Prod.ext (WeierstrassCurve.map_map Universal.curve k φ).symm (funext fun i ↦ i.elim0)
  | n + 1, k => by
    rw [cobarRingEquiv_succ_apply, cobarRingEquiv_succ_apply, RingHom.comp_assoc,
      cobarRingEquiv_comp φ n, ← VariableChange.map_map]
    exact Prod.ext rfl (Fin.comp_snoc (fun C : VariableChange R ↦ C.map φ) _ _).symm

/-! ### Strings of composable arrows -/

/-- **The cobar rings corepresent the nerve of the Weierstrass groupoid**: homomorphisms
`Γ^{⊗_A n} →+* R` classify strings of `n` composable arrows of the action groupoid of the changes
of variables over `R` on the Weierstrass curves over `R`, the `n`-simplices of its nerve. -/
def cobarChainEquiv (n : ℕ) : (cobarRing n →+* R) ≃
    ComposableArrows (ActionCategory (VariableChange R) (WeierstrassCurve R)) n :=
  (cobarRingEquiv R n).trans (nerveEquiv _ _ n).symm

/-- In the coordinates of `TauCeti.ActionGroupoid.nerveEquiv`, the string classified by `k` has
the curve and the changes of variables classified by `k` under `cobarRingEquiv`. -/
theorem nerveEquiv_cobarChainEquiv (n : ℕ) (k : cobarRing n →+* R) :
    nerveEquiv _ _ n (cobarChainEquiv R n k) = cobarRingEquiv R n k :=
  (nerveEquiv _ _ n).apply_symm_apply _

variable {R} in
/-- The classification of `cobarChainEquiv` is natural in the coefficient ring: composing with
`φ : R →+* S` applies the functor induced by base change along `φ`. -/
theorem cobarChainEquiv_comp {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ)
    (k : cobarRing n →+* R) :
    cobarChainEquiv S n (φ.comp k) =
      ((ActionCategory.map (VariableChange.mapHom φ) (mapMulActionHom φ)).mapComposableArrows
        n).obj (cobarChainEquiv R n k) := by
  apply (nerveEquiv _ _ n).injective
  rw [nerveEquiv_cobarChainEquiv, nerveEquiv_mapComposableArrows_obj, nerveEquiv_cobarChainEquiv,
    cobarRingEquiv_comp, mapMulActionHom_apply]
  -- `VariableChange.mapHom φ` applies `VariableChange.map φ`.
  rfl

/-! ### The cosimplicial ring -/

/-- The structure map `Γ^{⊗_A m} →+* Γ^{⊗_A n}` of `f : [m] ⟶ [n]` of the cobar construction. It
classifies the image of the universal string of `n` composable arrows under the simplicial
operator of `f` on the nerve (`cobarChainEquiv_comp_cobarMap`). -/
def cobarMap {m n : SimplexCategory} (f : m ⟶ n) : cobarRing m.len →+* cobarRing n.len :=
  (cobarChainEquiv _ m.len).symm
    ((cobarChainEquiv _ n.len (RingHom.id (cobarRing n.len))).whiskerLeft
      (SimplexCategory.toCat.map f).toFunctor)

/-- Precomposing with `cobarMap f` acts on strings of composable arrows by the simplicial operator
of `f : [m] ⟶ [n]` on the nerve of the Weierstrass groupoid. -/
theorem cobarChainEquiv_comp_cobarMap {m n : SimplexCategory} (f : m ⟶ n)
    (k : cobarRing n.len →+* R) :
    cobarChainEquiv R m.len (k.comp (cobarMap f)) =
      (nerve _).map f.op (cobarChainEquiv R n.len k) := by
  have hk : cobarChainEquiv R n.len k =
      ((ActionCategory.map (VariableChange.mapHom k) (mapMulActionHom k)).mapComposableArrows
        n.len).obj (cobarChainEquiv _ n.len (RingHom.id (cobarRing n.len))) := by
    rw [← cobarChainEquiv_comp, RingHom.comp_id]
  rw [cobarMap, cobarChainEquiv_comp, Equiv.apply_symm_apply, hk]
  -- The simplicial operator precomposes with a functor out of `Fin (m.len + 1)`, while the
  -- functor induced by `k` postcomposes, so the two commute definitionally.
  rfl

/-- **The cobar construction of the Weierstrass Hopf algebroid**: the cosimplicial commutative
ring `[n] ↦ Γ^{⊗_A n}`, with structure maps `cobarMap`. -/
@[expose]
def cobarObject : CosimplicialObject CommRingCat.{0} where
  obj n := cobarRing n.len
  map f := CommRingCat.ofHom (cobarMap f)
  map_id n := by
    ext1
    apply (cobarChainEquiv _ n.len).injective
    rw [CommRingCat.hom_ofHom, ← RingHom.id_comp (cobarMap (𝟙 n)), cobarChainEquiv_comp_cobarMap,
      op_id, CategoryTheory.Functor.map_id]
    -- The identity simplicial operator acts as the identity function.
    rfl
  map_comp f g := by
    ext1
    apply (cobarChainEquiv _ _).injective
    have h₁ := cobarChainEquiv_comp_cobarMap _ (f ≫ g) (RingHom.id _)
    have h₂ := cobarChainEquiv_comp_cobarMap _ f (cobarMap g)
    have h₃ := cobarChainEquiv_comp_cobarMap _ g (RingHom.id _)
    rw [RingHom.id_comp] at h₁ h₃
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, h₁, h₂, h₃, op_comp,
      CategoryTheory.Functor.map_comp]
    -- Composition of simplicial operators is composition of functions.
    rfl

/-- The structure maps of `cobarObject` are the homomorphisms `cobarMap`. -/
@[simp]
theorem cobarObject_map_hom {m n : SimplexCategory} (f : m ⟶ n) :
    (cobarObject.map f).hom = cobarMap f :=
  (rfl)

/-- **The structure maps in coordinates.** Let `k : Γ^{⊗_A n} →+* R` classify the string
`W → C₀ • W → C₁ • C₀ • W → ⋯` and write `Dⱼ = Cⱼ₋₁ ⋯ C₀` for the composite change of variables
from the first to the `j`-th curve. Then `k ∘ cobarMap f` classifies the string with first curve
`D_{f 0} • W` and changes of variables `D_{f (i + 1)} D_{f i}⁻¹`. -/
theorem cobarRingEquiv_comp_cobarMap {m n : SimplexCategory} (f : m ⟶ n)
    (k : cobarRing n.len →+* R) :
    cobarRingEquiv R m.len (k.comp (cobarMap f)) =
      ((Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv R n.len k).2 i))
          (f.toOrderHom 0)).unop • (cobarRingEquiv R n.len k).1,
        fun i ↦ (Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv R n.len k).2 i))
            (f.toOrderHom i.succ)).unop *
          (Fin.partialProd (fun i ↦ MulOpposite.op ((cobarRingEquiv R n.len k).2 i))
            (f.toOrderHom i.castSucc)).unop⁻¹) := by
  rw [← nerveEquiv_cobarChainEquiv, cobarChainEquiv_comp_cobarMap, nerveEquiv_nerve_map]
  exact Prod.ext (back_obj_nerveEquiv_symm _ _)
    (funext fun i ↦ label_nerveEquiv_symm_homOfLE _ _)

/-! ### Comparison with the Hopf algebroid structure maps -/

/-- A homomorphism `k : Γ →+* R` classifies the string consisting of the single arrow
`arrowEquiv R k`. -/
theorem cobarRingEquiv_one_apply (k : ArrowRing →+* R) :
    cobarRingEquiv R 1 k = ((arrowEquiv R k).1, fun _ ↦ (arrowEquiv R k).2) := by
  rw [cobarRingEquiv_succ_apply, cobarRingEquiv_zero_apply, arrowEquiv_apply]
  exact Prod.ext rfl (funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl)

/-- A homomorphism `k : Γ ⊗_A Γ →+* R` classifies the composable pair whose first arrow is
classified by the left factor `algebraMap` and whose second change of variables is classified
by `k`. -/
theorem cobarRingEquiv_two_apply (k : ChangeRing ArrowRing →+* R) :
    cobarRingEquiv R 2 k =
      ((arrowEquiv R (k.comp (algebraMap ArrowRing _))).1,
        ![(arrowEquiv R (k.comp (algebraMap ArrowRing _))).2,
          (universalChange ArrowRing).map k]) := by
  rw [cobarRingEquiv_succ_apply, cobarRingEquiv_one_apply]
  refine Prod.ext rfl (funext fun i ↦ ?_)
  fin_cases i <;> rfl

/-- The coface `δ⁰ : A → Γ` of the cobar construction is the right unit `η_R`, classifying the
target of an arrow. -/
theorem cobarMap_δ_zero_eq_rightUnit : cobarMap (SimplexCategory.δ (n := 0) 0) = rightUnit := by
  apply (cobarRingEquiv _ 0).injective
  rw [← RingHom.id_comp (cobarMap _), cobarRingEquiv_comp_cobarMap, cobarRingEquiv_one_apply,
    cobarRingEquiv_zero_apply]
  refine Prod.ext ?_ (funext fun i ↦ i.elim0)
  simp [SimplexCategory.δ, Fin.partialProd, List.ofFn_succ, map_rightUnit]

/-- The coface `δ¹ : A → Γ` of the cobar construction is the left unit `η_L = algebraMap`,
classifying the source of an arrow. -/
theorem cobarMap_δ_one_eq_algebraMap :
    cobarMap (SimplexCategory.δ (n := 0) 1) = algebraMap (MvPolynomial Coeff ℤ) ArrowRing := by
  apply (cobarRingEquiv _ 0).injective
  rw [← RingHom.id_comp (cobarMap _), cobarRingEquiv_comp_cobarMap, cobarRingEquiv_one_apply,
    cobarRingEquiv_zero_apply]
  refine Prod.ext ?_ (funext fun i ↦ i.elim0)
  simp [SimplexCategory.δ]

/-- The codegeneracy `σ⁰ : Γ → A` of the cobar construction is the counit `ε`, classifying the
identity arrows. -/
theorem cobarMap_σ_zero_eq_counit : cobarMap (SimplexCategory.σ (n := 0) 0) = counit := by
  apply (cobarRingEquiv _ 1).injective
  rw [← RingHom.id_comp (cobarMap _), cobarRingEquiv_comp_cobarMap, cobarRingEquiv_one_apply,
    cobarRingEquiv_zero_apply]
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · simp [Fin.partialProd]
  · simp [SimplexCategory.σ, Fin.fin_one_eq_zero i]

/-- The coface `δ⁰ : Γ → Γ ⊗_A Γ` of the cobar construction is the inclusion `ChangeRing.map η_R`
of the second factor, classifying the second arrow of a composable pair. -/
theorem cobarMap_δ_zero_eq_map_rightUnit :
    cobarMap (SimplexCategory.δ (n := 1) 0) = ChangeRing.map rightUnit := by
  apply (cobarRingEquiv _ 1).injective
  rw [← RingHom.id_comp (cobarMap _), cobarRingEquiv_comp_cobarMap, cobarRingEquiv_two_apply,
    cobarRingEquiv_one_apply]
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · -- The source of the second arrow is the target `η_R` of the first.
    have h : WeierstrassCurve.map Universal.curve
        ((algebraMap ArrowRing (ChangeRing ArrowRing)).comp rightUnit) =
          (universalChange _).map (algebraMap ArrowRing (ChangeRing ArrowRing)) •
            WeierstrassCurve.map Universal.curve
              ((algebraMap ArrowRing (ChangeRing ArrowRing)).comp (algebraMap _ ArrowRing)) := by
      rw [← WeierstrassCurve.map_map, map_rightUnit, ← map_variableChange,
        WeierstrassCurve.map_map]
    simp [SimplexCategory.δ, Fin.partialProd, List.ofFn_succ, h]
  · simp [SimplexCategory.δ, Fin.fin_one_eq_zero i, Fin.partialProd, List.ofFn_succ, Fin.succAbove]

/-- The coface `δ¹ : Γ → Γ ⊗_A Γ` of the cobar construction is the coproduct `Δ`, classifying the
composite of a composable pair. -/
theorem cobarMap_δ_one_eq_coproduct : cobarMap (SimplexCategory.δ (n := 1) 1) = coproduct := by
  apply (cobarRingEquiv _ 1).injective
  rw [← RingHom.id_comp (cobarMap _), cobarRingEquiv_comp_cobarMap, cobarRingEquiv_two_apply,
    cobarRingEquiv_one_apply]
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · simp [SimplexCategory.δ]
  · simp [SimplexCategory.δ, Fin.fin_one_eq_zero i, Fin.partialProd, List.ofFn_succ, Fin.succAbove]

/-- The coface `δ² : Γ → Γ ⊗_A Γ` of the cobar construction is the inclusion `algebraMap` of the
first factor, classifying the first arrow of a composable pair. -/
theorem cobarMap_δ_two_eq_algebraMap :
    cobarMap (SimplexCategory.δ (n := 1) 2) = algebraMap ArrowRing (ChangeRing ArrowRing) := by
  apply (cobarRingEquiv _ 1).injective
  rw [← RingHom.id_comp (cobarMap _), cobarRingEquiv_comp_cobarMap, cobarRingEquiv_two_apply,
    cobarRingEquiv_one_apply]
  refine Prod.ext ?_ (funext fun i ↦ ?_)
  · simp [SimplexCategory.δ, Fin.partialProd]
  · simp [SimplexCategory.δ, Fin.fin_one_eq_zero i, Fin.partialProd, List.ofFn_succ, Fin.succAbove]

/-! ### The cobar complex -/

/-- **The cobar complex** of the Weierstrass Hopf algebroid with coefficients in
`A = ℤ[a₁, ⋯, a₆]`: the alternating coface complex of `cobarObject`, with `n`-cochains
`Γ^{⊗_A n}` and differential `∑ᵢ (-1)ⁱ δⁱ`. -/
@[expose]
def cobarComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).obj
    (cobarObject ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

/-- The differential `A → Γ` of the cobar complex in degree `0` is `η_R - η_L`. -/
theorem cobarComplex_d_zero_one (x : MvPolynomial Coeff ℤ) :
    (cobarComplex.d 0 1).hom x = rightUnit x - algebraMap (MvPolynomial Coeff ℤ) ArrowRing x := by
  have h : cobarComplex.d 0 1 = AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (cobarObject ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) 0 :=
    CochainComplex.of_d (fun n ↦ (cobarObject ⋙ forget₂ CommRingCat RingCat ⋙
      forget₂ RingCat AddCommGrpCat).obj (SimplexCategory.mk n)) _ 0
  rw [h, sub_eq_add_neg, ← cobarMap_δ_zero_eq_rightUnit, ← cobarMap_δ_one_eq_algebraMap]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, pow_zero, pow_one, one_smul, neg_smul,
    zero_add, add_zero]
  -- Both forgetful functors keep the underlying function, and addition and negation of
  -- morphisms of additive groups are pointwise.
  rfl

end TauCeti.WeierstrassHopfAlgebroid

namespace WeierstrassCurve

open TauCeti.WeierstrassHopfAlgebroid

/-- The degree `0` cocycles of the cobar complex of the Weierstrass Hopf algebroid are the
integral modular forms of weight `0`. -/
theorem isIntegralModularForm_zero_iff_cobarComplex_d_eq_zero (f : MvPolynomial Coeff ℤ) :
    IsIntegralModularForm 0 f ↔ (cobarComplex.d 0 1).hom f = 0 := by
  rw [cobarComplex_d_zero_one, isIntegralModularForm_iff_rightUnit, pow_zero, one_mul]
  exact sub_eq_zero.symm

end WeierstrassCurve
