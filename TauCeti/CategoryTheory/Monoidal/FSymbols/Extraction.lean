/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.CategoryTheory.Linear.SplitSimpleFamily
public import TauCeti.CategoryTheory.Monoidal.FSymbols.Defs

/-!
# Extraction of F-symbols

Let `C` be a monoidal `R`-linear category over a commutative semiring `R`, and let `S : ι → C` be a
split simple family (`TauCeti.IsSplitSimpleFamily R S`) indexed by a finite type: each `S a` has
endomorphisms `R`, there are no nonzero morphisms between distinct members, and every object is a
finite biproduct of members. A **fusion basis** for fusion rules `N` (`TauCeti.FusionBasis`) is a
choice of bases `φ^{ab→c}_i`, `i : Fin N_{ab}^c`, of the fusion spaces `S a ⊗ S b ⟶ S c`, normalized
through an isomorphism `𝟙_ C ≅ S u` so that `φ^{ua→a}_0` and `φ^{au→a}_0` are the unitors.

This file reads off the F-symbols of `C` in such a basis. The morphisms
`(S a ⊗ S b) ⊗ S c ⟶ S d` have the basis `(φ^{ab→e}_i ▷ S c) ≫ φ^{ec→d}_j` (the *left family*), and
the morphisms `S a ⊗ (S b ⊗ S c) ⟶ S d` have the basis `(S a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l` (the
*right family*). The F-matrix `F^{abc}_d` expresses the left family in the right family, transported
across the associator. The pentagon axiom of `C` gives the pentagon equation, the triangle axiom and
the normalization give the triangle equation, and the two families being bases gives the inverse
F-matrix. So `C` determines exactly one `TauCeti.FSymbols R N` in a given fusion basis.

The bases come from a decomposition of morphisms out of a tensor product with a member of the
family: every morphism `Y ⊗ S c ⟶ S d` is uniquely a sum `∑ e, ∑ j, (g e j ▷ S c) ≫ φ^{ec→d}_j`
with `g e j : Y ⟶ S e`, and symmetrically for `S a ⊗ Y`. No field and no abelian structure is
needed: coordinates are read off from the scalar endomorphisms of the members.

## Main definitions

* `TauCeti.FusionBasis S N`: a normalized fusion basis of `S` for the fusion rules `N`.
* `TauCeti.FusionBasis.sumWhiskerRight` and `TauCeti.FusionBasis.sumWhiskerLeft`: the linear maps
  assembling morphisms out of `Y ⊗ S c` and `S a ⊗ Y` from morphisms out of `Y`.
* `TauCeti.FusionBasis.left`, `TauCeti.FusionBasis.right`: the left and right families, and
  `TauCeti.FusionBasis.leftBasis`, `TauCeti.FusionBasis.rightBasis`: the bases they form.
* `TauCeti.FusionBasis.fSymbols`: the F-symbols of a split simple family in a fusion basis.

## Main results

* `TauCeti.FusionBasis.finrank_hom`: over a nontrivial commutative ring, `N_{ab}^c` is the rank of
  `S a ⊗ S b ⟶ S c`.
* `TauCeti.FusionBasis.sumWhiskerRight_bijective`, `TauCeti.FusionBasis.sumWhiskerLeft_bijective`:
  the decompositions of morphisms out of `Y ⊗ S c` and `S a ⊗ Y`.
* `TauCeti.FusionBasis.left_eq_fSymbols`: the left family in terms of the right family.
* `TauCeti.FusionBasis.existsUnique_fSymbols`: the F-symbols with this property are unique.

## References

* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics 321 (2006),
  Appendix E, §E.1, eq. (177) and Fig. 17a: the F-symbols of a fusion category over `ℂ` and the
  pentagon equation they satisfy.
* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*, Mathematical Surveys and
  Monographs 205, AMS (2015), §4.9.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Module

universe w v u u'

namespace TauCeti

/-- A **fusion basis** of a family `S : ι → C` of objects of a monoidal `R`-linear category, for
fusion rules `N`: an isomorphism `𝟙_ C ≅ S u` with the unit index `u`, and bases
`φ^{ab→c}_i`, `i : Fin N_{ab}^c`, of the modules `S a ⊗ S b ⟶ S c`, normalized so that
`φ^{ua→a}_0` and `φ^{au→a}_0` are the left and right unitors, through the chosen isomorphism. -/
structure FusionBasis (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear R C] [MonoidalCategory C] {ι : Type u'} (S : ι → C) (N : FusionRules ι) where
  /-- The identification of the tensor unit with the simple object of the unit index. -/
  unitIso : 𝟙_ C ≅ S N.unit
  /-- The basis `φ^{ab→c}` of the fusion space `S a ⊗ S b ⟶ S c`. -/
  basis (a b c : ι) : Basis (Fin (N.N a b c)) R (S a ⊗ S b ⟶ S c)
  /-- The basis vector of `S u ⊗ S a ⟶ S a` is the left unitor. -/
  basis_unitLeft (a : ι) :
    basis N.unit a a (N.unitLeft a) = (unitIso.inv ▷ S a) ≫ (λ_ (S a)).hom
  /-- The basis vector of `S a ⊗ S u ⟶ S a` is the right unitor. -/
  basis_unitRight (a : ι) :
    basis a N.unit a (N.unitRight a) = (S a ◁ unitIso.inv) ≫ (ρ_ (S a)).hom

namespace FusionBasis

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [MonoidalCategory C]
variable {ι : Type u'} {S : ι → C} {N : FusionRules ι} (φ : FusionBasis R S N)

include φ in
/-- Over a commutative semiring with the strong rank condition, for instance a nontrivial
commutative ring, the fusion multiplicities of a fusion basis are the ranks of the fusion
spaces. -/
theorem finrank_hom [StrongRankCondition R] (a b c : ι) :
    finrank R (S a ⊗ S b ⟶ S c) = N.N a b c := by
  rw [finrank_eq_card_basis (φ.basis a b c), Fintype.card_fin]

section Decomposition

variable [MonoidalPreadditive C] [MonoidalLinear R C] [Fintype ι]

/-- The morphism `Y ⊗ S c ⟶ S d` assembled from morphisms `g e j : Y ⟶ S e` and the fusion basis:
`∑ e, ∑ j, (g e j ▷ S c) ≫ φ^{ec→d}_j`. For a split simple family it is a linear isomorphism
(`TauCeti.FusionBasis.sumWhiskerRight_bijective`). -/
def sumWhiskerRight (Y : C) (c d : ι) :
    (∀ e, Fin (N.N e c d) → (Y ⟶ S e)) →ₗ[R] (Y ⊗ S c ⟶ S d) where
  toFun g := ∑ e, ∑ j, (g e j ▷ S c) ≫ φ.basis e c d j
  map_add' g g' := by simp [Finset.sum_add_distrib]
  map_smul' r g := by simp [Finset.smul_sum]

@[simp]
theorem sumWhiskerRight_apply (Y : C) (c d : ι) (g : ∀ e, Fin (N.N e c d) → (Y ⟶ S e)) :
    φ.sumWhiskerRight Y c d g = ∑ e, ∑ j, (g e j ▷ S c) ≫ φ.basis e c d j := (rfl)

/-- The morphism `S a ⊗ Y ⟶ S d` assembled from morphisms `g f l : Y ⟶ S f` and the fusion basis:
`∑ f, ∑ l, (S a ◁ g f l) ≫ φ^{af→d}_l`. For a split simple family it is a linear isomorphism
(`TauCeti.FusionBasis.sumWhiskerLeft_bijective`). -/
def sumWhiskerLeft (a : ι) (Y : C) (d : ι) :
    (∀ f, Fin (N.N a f d) → (Y ⟶ S f)) →ₗ[R] (S a ⊗ Y ⟶ S d) where
  toFun g := ∑ f, ∑ l, (S a ◁ g f l) ≫ φ.basis a f d l
  map_add' g g' := by simp [Finset.sum_add_distrib]
  map_smul' r g := by simp [Finset.smul_sum]

@[simp]
theorem sumWhiskerLeft_apply (a : ι) (Y : C) (d : ι) (g : ∀ f, Fin (N.N a f d) → (Y ⟶ S f)) :
    φ.sumWhiskerLeft a Y d g = ∑ f, ∑ l, (S a ◁ g f l) ≫ φ.basis a f d l := (rfl)

/-- `TauCeti.FusionBasis.sumWhiskerRight` is natural in `Y`. -/
theorem whiskerRight_comp_sumWhiskerRight {Y Y' : C} (h : Y' ⟶ Y) (c d : ι)
    (g : ∀ e, Fin (N.N e c d) → (Y ⟶ S e)) :
    (h ▷ S c) ≫ φ.sumWhiskerRight Y c d g = φ.sumWhiskerRight Y' c d fun e j ↦ h ≫ g e j := by
  simp [sumWhiskerRight_apply, Preadditive.comp_sum]

/-- `TauCeti.FusionBasis.sumWhiskerLeft` is natural in `Y`. -/
theorem whiskerLeft_comp_sumWhiskerLeft (a : ι) {Y Y' : C} (h : Y' ⟶ Y) (d : ι)
    (g : ∀ f, Fin (N.N a f d) → (Y ⟶ S f)) :
    (S a ◁ h) ≫ φ.sumWhiskerLeft a Y d g = φ.sumWhiskerLeft a Y' d fun f l ↦ h ≫ g f l := by
  simp [sumWhiskerLeft_apply, Preadditive.comp_sum]

variable [HasFiniteBiproducts C] (hS : IsSplitSimpleFamily R S)
include hS

/-- Precomposing `TauCeti.FusionBasis.sumWhiskerRight` with `u ▷ S c`, for `u : S e ⟶ Y`, picks out
the summands indexed by `e`, with coefficients the pairings of `u` with `g e j`. -/
private theorem whiskerRight_comp_sumWhiskerRight_eq {Y : C} {e : ι} (u : S e ⟶ Y) (c d : ι)
    (g : ∀ e, Fin (N.N e c d) → (Y ⟶ S e)) :
    (u ▷ S c) ≫ φ.sumWhiskerRight Y c d g =
      ∑ j, homPairingOfBijective (hS.bijective_algebraMap e) Y u (g e j) • φ.basis e c d j := by
  classical
  rw [whiskerRight_comp_sumWhiskerRight, sumWhiskerRight_apply, Finset.sum_eq_single e]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap e),
      MonoidalLinear.smul_whiskerRight, id_whiskerRight, Linear.smul_comp, Category.id_comp]
  · intro e' _ he'
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hS.homOrthogonal.eq_zero (Ne.symm he') (u ≫ g e' j),
      MonoidalPreadditive.zero_whiskerRight, zero_comp]
  · simp

/-- Precomposing `TauCeti.FusionBasis.sumWhiskerLeft` with `S a ◁ u`, for `u : S f ⟶ Y`, picks out
the summands indexed by `f`, with coefficients the pairings of `u` with `g f l`. -/
private theorem whiskerLeft_comp_sumWhiskerLeft_eq (a : ι) {Y : C} {f : ι} (u : S f ⟶ Y) (d : ι)
    (g : ∀ f, Fin (N.N a f d) → (Y ⟶ S f)) :
    (S a ◁ u) ≫ φ.sumWhiskerLeft a Y d g =
      ∑ l, homPairingOfBijective (hS.bijective_algebraMap f) Y u (g f l) • φ.basis a f d l := by
  classical
  rw [whiskerLeft_comp_sumWhiskerLeft, sumWhiskerLeft_apply, Finset.sum_eq_single f]
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap f),
      MonoidalLinear.whiskerLeft_smul, whiskerLeft_id, Linear.smul_comp, Category.id_comp]
  · intro f' _ hf'
    refine Finset.sum_eq_zero fun l _ ↦ ?_
    rw [hS.homOrthogonal.eq_zero (Ne.symm hf') (u ≫ g f' l),
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]
  · simp

/-- A morphism out of `Y ⊗ S c` determines its decomposition along the fusion basis. -/
theorem sumWhiskerRight_injective (Y : C) (c d : ι) :
    Function.Injective (φ.sumWhiskerRight Y c d) := by
  intro g g' h
  funext e j
  refine hS.homTo_ext e fun u ↦ ?_
  have h' := congrArg ((u ▷ S c) ≫ ·) h
  simp only [φ.whiskerRight_comp_sumWhiskerRight_eq hS] at h'
  have hj := congrArg (fun x ↦ (φ.basis e c d).repr x j) h'
  simp only [Basis.repr_sum_self] at hj
  rw [← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap e), hj,
    homPairingOfBijective_smul_id]

/-- A morphism out of `S a ⊗ Y` determines its decomposition along the fusion basis. -/
theorem sumWhiskerLeft_injective (a : ι) (Y : C) (d : ι) :
    Function.Injective (φ.sumWhiskerLeft a Y d) := by
  intro g g' h
  funext f l
  refine hS.homTo_ext f fun u ↦ ?_
  have h' := congrArg ((S a ◁ u) ≫ ·) h
  simp only [φ.whiskerLeft_comp_sumWhiskerLeft_eq hS] at h'
  have hl := congrArg (fun x ↦ (φ.basis a f d).repr x l) h'
  simp only [Basis.repr_sum_self] at hl
  rw [← homPairingOfBijective_smul_id (hS := hS.bijective_algebraMap f), hl,
    homPairingOfBijective_smul_id]

/-- Every morphism out of `Y ⊗ S c` decomposes along the fusion basis. -/
theorem sumWhiskerRight_surjective (Y : C) (c d : ι) :
    Function.Surjective (φ.sumWhiskerRight Y c d) := by
  classical
  intro h
  choose K _ _ u v huv using fun e ↦ hS.exists_dual_bases e Y
  have hid := hS.sum_sum_comp_eq_id Y Finset.univ (by simp) (fun e ↦ u e) (fun e k ↦ v e k) huv
  refine ⟨fun e j ↦ ∑ k, (φ.basis e c d).repr ((u e k ▷ S c) ≫ h) j • v e k, ?_⟩
  conv_rhs => rw [← Category.id_comp h, ← id_whiskerRight, ← hid]
  simp only [sumWhiskerRight_apply, sum_whiskerRight, Preadditive.sum_comp,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp, comp_whiskerRight, Category.assoc]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  conv_rhs => rw [← (φ.basis e c d).sum_repr ((u e k ▷ S c) ≫ h), Preadditive.comp_sum]
  simp only [Linear.comp_smul]

/-- Every morphism out of `S a ⊗ Y` decomposes along the fusion basis. -/
theorem sumWhiskerLeft_surjective (a : ι) (Y : C) (d : ι) :
    Function.Surjective (φ.sumWhiskerLeft a Y d) := by
  classical
  intro h
  choose K _ _ u v huv using fun f ↦ hS.exists_dual_bases f Y
  have hid := hS.sum_sum_comp_eq_id Y Finset.univ (by simp) (fun f ↦ u f) (fun f k ↦ v f k) huv
  refine ⟨fun f l ↦ ∑ k, (φ.basis a f d).repr ((S a ◁ u f k) ≫ h) l • v f k, ?_⟩
  conv_rhs => rw [← Category.id_comp h, ← whiskerLeft_id, ← hid]
  simp only [sumWhiskerLeft_apply, whiskerLeft_sum, Preadditive.sum_comp,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, whiskerLeft_comp, Category.assoc]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  conv_rhs => rw [← (φ.basis a f d).sum_repr ((S a ◁ u f k) ≫ h), Preadditive.comp_sum]
  simp only [Linear.comp_smul]

/-- **Decomposition of morphisms out of `Y ⊗ S c`.** For a split simple family with a fusion
basis, every morphism `Y ⊗ S c ⟶ S d` is uniquely `∑ e, ∑ j, (g e j ▷ S c) ≫ φ^{ec→d}_j`. -/
theorem sumWhiskerRight_bijective (Y : C) (c d : ι) :
    Function.Bijective (φ.sumWhiskerRight Y c d) :=
  ⟨φ.sumWhiskerRight_injective hS Y c d, φ.sumWhiskerRight_surjective hS Y c d⟩

/-- **Decomposition of morphisms out of `S a ⊗ Y`.** For a split simple family with a fusion
basis, every morphism `S a ⊗ Y ⟶ S d` is uniquely `∑ f, ∑ l, (S a ◁ g f l) ≫ φ^{af→d}_l`. -/
theorem sumWhiskerLeft_bijective (a : ι) (Y : C) (d : ι) :
    Function.Bijective (φ.sumWhiskerLeft a Y d) :=
  ⟨φ.sumWhiskerLeft_injective hS a Y d, φ.sumWhiskerLeft_surjective hS a Y d⟩

end Decomposition

section Families

/-- The **left family** `(φ^{ab→e}_i ▷ S c) ≫ φ^{ec→d}_j` of morphisms `(S a ⊗ S b) ⊗ S c ⟶ S d`,
indexed by the row indices `(e, i, j)` of the F-matrix. -/
def left (a b c d : ι) (x : N.Left a b c d) : (S a ⊗ S b) ⊗ S c ⟶ S d :=
  (φ.basis a b x.1 x.2.1 ▷ S c) ≫ φ.basis x.1 c d x.2.2

@[simp]
theorem left_mk (a b c d e : ι) (i : Fin (N.N a b e)) (j : Fin (N.N e c d)) :
    φ.left a b c d ⟨e, i, j⟩ = (φ.basis a b e i ▷ S c) ≫ φ.basis e c d j := (rfl)

/-- The **right family** `(S a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l` of morphisms `S a ⊗ (S b ⊗ S c) ⟶ S d`,
indexed by the column indices `(f, k, l)` of the F-matrix. -/
def right (a b c d : ι) (y : N.Right a b c d) : S a ⊗ (S b ⊗ S c) ⟶ S d :=
  (S a ◁ φ.basis b c y.1 y.2.1) ≫ φ.basis a y.1 d y.2.2

@[simp]
theorem right_mk (a b c d f : ι) (k : Fin (N.N b c f)) (l : Fin (N.N a f d)) :
    φ.right a b c d ⟨f, k, l⟩ = (S a ◁ φ.basis b c f k) ≫ φ.basis a f d l := (rfl)

/-- The left basis vector through `S a ⊗ S u` is the right basis vector through `S u ⊗ S c`,
transported across the associator: this is the triangle axiom. -/
private theorem left_unitRight (a c d : ι) (j : Fin (N.N a c d)) :
    φ.left a N.unit c d ⟨a, N.unitRight a, j⟩ =
      (α_ (S a) (S N.unit) (S c)).hom ≫ φ.right a N.unit c d ⟨c, N.unitLeft c, j⟩ := by
  simp only [left_mk, right_mk, φ.basis_unitLeft, φ.basis_unitRight, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_middle_assoc, triangle_assoc]

variable [MonoidalPreadditive C] [MonoidalLinear R C] [Fintype ι]

/-- A linear combination of the left family, decomposed along `S a ⊗ S b`. -/
theorem sum_smul_left (a b c d : ι) (w : N.Left a b c d → R) :
    ∑ x, w x • φ.left a b c d x =
      φ.sumWhiskerRight (S a ⊗ S b) c d fun e j ↦ ∑ i, w ⟨e, i, j⟩ • φ.basis a b e i := by
  simp only [sumWhiskerRight_apply, Fintype.sum_sigma, Fintype.sum_prod_type, left_mk,
    sum_whiskerRight, MonoidalLinear.smul_whiskerRight, Preadditive.sum_comp, Linear.smul_comp]
  exact Finset.sum_congr rfl fun e _ ↦ Finset.sum_comm

/-- A linear combination of the right family, decomposed along `S b ⊗ S c`. -/
theorem sum_smul_right (a b c d : ι) (w : N.Right a b c d → R) :
    ∑ y, w y • φ.right a b c d y =
      φ.sumWhiskerLeft a (S b ⊗ S c) d fun f l ↦ ∑ k, w ⟨f, k, l⟩ • φ.basis b c f k := by
  simp only [sumWhiskerLeft_apply, Fintype.sum_sigma, Fintype.sum_prod_type, right_mk,
    whiskerLeft_sum, MonoidalLinear.whiskerLeft_smul, Preadditive.sum_comp, Linear.smul_comp]
  exact Finset.sum_congr rfl fun f _ ↦ Finset.sum_comm

variable [HasFiniteBiproducts C] (hS : IsSplitSimpleFamily R S)

/-- For a split simple family, the left family is a basis of `(S a ⊗ S b) ⊗ S c ⟶ S d`. -/
def leftBasis (a b c d : ι) : Basis (N.Left a b c d) R ((S a ⊗ S b) ⊗ S c ⟶ S d) :=
  Basis.mk (v := φ.left a b c d)
    (by
      refine Fintype.linearIndependent_iffₛ.2 fun w w' hw ⟨e, i, j⟩ ↦ ?_
      rw [sum_smul_left, sum_smul_left] at hw
      have := congrArg (fun g ↦ (φ.basis a b e).repr (g e j) i)
        (φ.sumWhiskerRight_injective hS _ c d hw)
      simpa only [Basis.repr_sum_self] using this)
    (by
      rintro h -
      obtain ⟨g, rfl⟩ := φ.sumWhiskerRight_surjective hS (S a ⊗ S b) c d h
      refine (Submodule.mem_span_range_iff_exists_fun R).2
        ⟨fun x ↦ (φ.basis a b x.1).repr (g x.1 x.2.2) x.2.1, ?_⟩
      simp [sum_smul_left])

@[simp]
theorem coe_leftBasis (a b c d : ι) : ⇑(φ.leftBasis hS a b c d) = φ.left a b c d :=
  Basis.coe_mk _ _

/-- For a split simple family, the right family is a basis of `S a ⊗ (S b ⊗ S c) ⟶ S d`. -/
def rightBasis (a b c d : ι) : Basis (N.Right a b c d) R (S a ⊗ (S b ⊗ S c) ⟶ S d) :=
  Basis.mk (v := φ.right a b c d)
    (by
      refine Fintype.linearIndependent_iffₛ.2 fun w w' hw ⟨f, k, l⟩ ↦ ?_
      rw [sum_smul_right, sum_smul_right] at hw
      have := congrArg (fun g ↦ (φ.basis b c f).repr (g f l) k)
        (φ.sumWhiskerLeft_injective hS a _ d hw)
      simpa only [Basis.repr_sum_self] using this)
    (by
      rintro h -
      obtain ⟨g, rfl⟩ := φ.sumWhiskerLeft_surjective hS a (S b ⊗ S c) d h
      refine (Submodule.mem_span_range_iff_exists_fun R).2
        ⟨fun y ↦ (φ.basis b c y.1).repr (g y.1 y.2.2) y.2.1, ?_⟩
      simp [sum_smul_right])

@[simp]
theorem coe_rightBasis (a b c d : ι) : ⇑(φ.rightBasis hS a b c d) = φ.right a b c d :=
  Basis.coe_mk _ _

/-- The right family transported across the associator, `(α_ _ _ _).hom ≫ right`: a second basis
of `(S a ⊗ S b) ⊗ S c ⟶ S d`. -/
private def associatorBasis (a b c d : ι) : Basis (N.Right a b c d) R ((S a ⊗ S b) ⊗ S c ⟶ S d) :=
  (φ.rightBasis hS a b c d).map (Linear.homCongr R (α_ (S a) (S b) (S c)).symm (Iso.refl _))

private theorem associatorBasis_apply (a b c d : ι) (y : N.Right a b c d) :
    φ.associatorBasis hS a b c d y = (α_ (S a) (S b) (S c)).hom ≫ φ.right a b c d y := by
  simp [associatorBasis, Linear.homCongr_apply]

/-- The F-matrix: the coordinates of the left family in the basis
`TauCeti.FusionBasis.associatorBasis`. -/
private def fMatrix (a b c d : ι) : Matrix (N.Left a b c d) (N.Right a b c d) R :=
  ((φ.associatorBasis hS a b c d).toMatrix (φ.left a b c d)).transpose

/-- The inverse F-matrix: the coordinates of `TauCeti.FusionBasis.associatorBasis` in the left
family. -/
private def fInvMatrix (a b c d : ι) : Matrix (N.Right a b c d) (N.Left a b c d) R :=
  ((φ.leftBasis hS a b c d).toMatrix (φ.associatorBasis hS a b c d)).transpose

private theorem left_eq_fMatrix (a b c d : ι) (x : N.Left a b c d) :
    φ.left a b c d x =
      (α_ (S a) (S b) (S c)).hom ≫ ∑ y, φ.fMatrix hS a b c d x y • φ.right a b c d y := by
  conv_lhs => rw [← (φ.associatorBasis hS a b c d).sum_repr (φ.left a b c d x)]
  simp [fMatrix, Basis.toMatrix_apply, associatorBasis_apply, Preadditive.comp_sum]

/-- A linear combination of the left family, expanded in the right family. -/
private theorem sum_smul_left_eq (a b c d : ι) (w : N.Left a b c d → R) :
    ∑ x, w x • φ.left a b c d x = (α_ (S a) (S b) (S c)).hom ≫
      ∑ y, (∑ x, w x * φ.fMatrix hS a b c d x y) • φ.right a b c d y := by
  simp only [φ.left_eq_fMatrix hS, Preadditive.comp_sum, Linear.comp_smul, Finset.smul_sum,
    Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/-- The first expansion in the pentagon: across `α_{AB,C,D}` and then `α_{A,B,CD}`. -/
private theorem comp_left_eq_pentagon_left (A B C D E p q : ι) (i₁ : Fin (N.N A B p))
    (i₂ : Fin (N.N p C q)) (i₃ : Fin (N.N q D E)) :
    ((φ.basis A B p i₁ ▷ S C) ▷ S D) ≫ φ.left p C D E ⟨q, i₂, i₃⟩ =
      (α_ (S A ⊗ S B) (S C) (S D)).hom ≫ (α_ (S A) (S B) (S C ⊗ S D)).hom ≫
        φ.sumWhiskerLeft A (S B ⊗ (S C ⊗ S D)) E fun s n ↦ ∑ y : N.Right B C D s,
          (∑ l, φ.fMatrix hS p C D E ⟨q, i₂, i₃⟩ ⟨y.1, y.2.1, l⟩ *
            φ.fMatrix hS A B y.1 E ⟨p, i₁, l⟩ ⟨s, y.2.2, n⟩) • φ.right B C D s y := by
  have step : ∀ r (l : Fin (N.N p r E)) (g : S C ⊗ S D ⟶ S r),
      (φ.basis A B p i₁ ▷ (S C ⊗ S D)) ≫ (S p ◁ g) ≫ φ.basis p r E l =
        (α_ (S A) (S B) (S C ⊗ S D)).hom ≫ φ.sumWhiskerLeft A _ E fun s n ↦
          (S B ◁ g) ≫ ∑ m, φ.fMatrix hS A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ • φ.basis B r s m := by
    intro r l g
    rw [← whisker_exchange_assoc, ← left_mk, φ.left_eq_fMatrix hS, sum_smul_right,
      associator_naturality_right_assoc, whiskerLeft_comp_sumWhiskerLeft]
  rw [φ.left_eq_fMatrix hS, sum_smul_right, associator_naturality_left_assoc]
  congr 1
  rw [sumWhiskerLeft_apply]
  simp only [Preadditive.comp_sum, step]
  simp only [← Preadditive.comp_sum, ← map_sum]
  congr 2
  funext s n
  simp only [Finset.sum_apply, Fintype.sum_sigma, Fintype.sum_prod_type, right_mk,
    whiskerLeft_sum, MonoidalLinear.whiskerLeft_smul, Preadditive.sum_comp, Preadditive.comp_sum,
    Linear.smul_comp, Linear.comp_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  -- reorder the sums over `l`, `m`, `k` into the order `k`, `m`, `l`
  refine (Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm)).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ by rw [mul_comm])

/-- The second expansion in the pentagon: across `α_{A,B,C} ▷ D`, `α_{A,BC,D}` and then
`A ◁ α_{B,C,D}`. -/
private theorem comp_left_eq_pentagon_right (A B C D E p q : ι) (i₁ : Fin (N.N A B p))
    (i₂ : Fin (N.N p C q)) (i₃ : Fin (N.N q D E)) :
    ((φ.basis A B p i₁ ▷ S C) ▷ S D) ≫ φ.left p C D E ⟨q, i₂, i₃⟩ =
      ((α_ (S A) (S B) (S C)).hom ▷ S D) ≫ (α_ (S A) (S B ⊗ S C) (S D)).hom ≫
        (S A ◁ (α_ (S B) (S C) (S D)).hom) ≫
          φ.sumWhiskerLeft A (S B ⊗ (S C ⊗ S D)) E fun s n ↦ ∑ y : N.Right B C D s,
            (∑ w : N.Left B C D s,
              (∑ y', φ.fMatrix hS A B C q ⟨p, i₁, i₂⟩ ⟨w.1, w.2.1, y'⟩ *
                φ.fMatrix hS A w.1 D E ⟨q, y', i₃⟩ ⟨s, w.2.2, n⟩) *
                  φ.fMatrix hS B C D s w y) • φ.right B C D s y := by
  have step : ∀ t (x : Fin (N.N B C t)) (y' : Fin (N.N A t q)),
      ((S A ◁ φ.basis B C t x) ▷ S D) ≫ (φ.basis A t q y' ▷ S D) ≫ φ.basis q D E i₃ =
        (α_ (S A) (S B ⊗ S C) (S D)).hom ≫ φ.sumWhiskerLeft A _ E fun s n ↦
          (φ.basis B C t x ▷ S D) ≫
            ∑ z, φ.fMatrix hS A t D E ⟨q, y', i₃⟩ ⟨s, z, n⟩ • φ.basis t D s z := by
    intro t x y'
    rw [← left_mk, φ.left_eq_fMatrix hS, sum_smul_right, associator_naturality_middle_assoc,
      whiskerLeft_comp_sumWhiskerLeft]
  rw [left_mk, ← comp_whiskerRight_assoc, ← φ.left_mk A B C q p i₁ i₂, φ.left_eq_fMatrix hS,
    comp_whiskerRight_assoc, whiskerLeft_comp_sumWhiskerLeft]
  congr 1
  conv_lhs =>
    simp only [sum_whiskerRight, MonoidalLinear.smul_whiskerRight, Preadditive.sum_comp,
      Linear.smul_comp, Fintype.sum_sigma, Fintype.sum_prod_type, right_mk, comp_whiskerRight,
      Category.assoc, step]
    simp only [← Linear.comp_smul, ← Preadditive.comp_sum, ← map_smul, ← map_sum]
  congr 2
  funext s n
  rw [← φ.sum_smul_left_eq hS]
  simp only [Finset.sum_apply, Pi.smul_apply, Fintype.sum_sigma, Fintype.sum_prod_type, left_mk,
    Preadditive.comp_sum, Linear.comp_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  exact Finset.sum_comm

private theorem fMatrix_pentagon (A B C D E p q r s : ι) (i₁ : Fin (N.N A B p))
    (i₂ : Fin (N.N p C q)) (i₃ : Fin (N.N q D E)) (k : Fin (N.N C D r)) (m : Fin (N.N B r s))
    (n : Fin (N.N A s E)) :
    ∑ l : Fin (N.N p r E),
        φ.fMatrix hS p C D E ⟨q, i₂, i₃⟩ ⟨r, k, l⟩ * φ.fMatrix hS A B r E ⟨p, i₁, l⟩ ⟨s, m, n⟩ =
      ∑ t : ι, ∑ x : Fin (N.N B C t), ∑ y : Fin (N.N A t q), ∑ z : Fin (N.N t D s),
        φ.fMatrix hS A B C q ⟨p, i₁, i₂⟩ ⟨t, x, y⟩ * φ.fMatrix hS A t D E ⟨q, y, i₃⟩ ⟨s, z, n⟩ *
          φ.fMatrix hS B C D s ⟨t, x, z⟩ ⟨r, k, m⟩ := by
  have h := (φ.comp_left_eq_pentagon_left hS A B C D E p q i₁ i₂ i₃).symm.trans
    (φ.comp_left_eq_pentagon_right hS A B C D E p q i₁ i₂ i₃)
  rw [pentagon_assoc, cancel_epi, cancel_epi] at h
  have h' := congrArg (fun G ↦ (φ.rightBasis hS B C D s).repr (G s n) ⟨r, k, m⟩)
    (φ.sumWhiskerLeft_injective hS A _ E h)
  simp only [← coe_rightBasis φ hS, Basis.repr_sum_self] at h'
  rw [h', Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

private theorem fMatrix_triangle (a c d : ι) (j l : Fin (N.N a c d)) :
    φ.fMatrix hS a N.unit c d ⟨a, N.unitRight a, j⟩ ⟨c, N.unitLeft c, l⟩ =
      if j = l then 1 else 0 := by
  classical
  rw [fMatrix, Matrix.transpose_apply, Basis.toMatrix_apply, φ.left_unitRight,
    ← φ.associatorBasis_apply hS, Basis.repr_self, Finsupp.single_apply]
  simp

variable [DecidableEq ι]

private theorem fMatrix_mul_fInvMatrix (a b c d : ι) :
    φ.fMatrix hS a b c d * φ.fInvMatrix hS a b c d = 1 := by
  rw [fMatrix, fInvMatrix, ← Matrix.transpose_mul, ← coe_leftBasis φ hS,
    Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

private theorem fInvMatrix_mul_fMatrix (a b c d : ι) :
    φ.fInvMatrix hS a b c d * φ.fMatrix hS a b c d = 1 := by
  rw [fMatrix, fInvMatrix, ← Matrix.transpose_mul, ← coe_leftBasis φ hS,
    Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

/-- **The F-symbols of a fusion basis.** For a split simple family with a fusion basis,
`F^{abc}_d` is the matrix of coordinates of the left family of `(S a ⊗ S b) ⊗ S c ⟶ S d` in the
right family of `S a ⊗ (S b ⊗ S c) ⟶ S d`, transported across the associator
(`TauCeti.FusionBasis.left_eq_fSymbols`). -/
def fSymbols : FSymbols R N where
  F := φ.fMatrix hS
  Finv := φ.fInvMatrix hS
  F_mul_Finv := φ.fMatrix_mul_fInvMatrix hS
  Finv_mul_F := φ.fInvMatrix_mul_fMatrix hS
  pentagon := φ.fMatrix_pentagon hS
  triangle := φ.fMatrix_triangle hS

private theorem fSymbols_F : (φ.fSymbols hS).F = φ.fMatrix hS := (rfl)

/-- **The defining property of the extracted F-symbols**: the left family is expressed in the right
family across the associator by the F-matrix. -/
theorem left_eq_fSymbols (a b c d : ι) (x : N.Left a b c d) :
    φ.left a b c d x =
      (α_ (S a) (S b) (S c)).hom ≫ ∑ y, (φ.fSymbols hS).F a b c d x y • φ.right a b c d y :=
  φ.left_eq_fMatrix hS a b c d x

/-- The right family, transported across the associator, is expressed in the left family by the
inverse F-matrix. -/
theorem associator_comp_right_eq_fSymbols (a b c d : ι) (y : N.Right a b c d) :
    (α_ (S a) (S b) (S c)).hom ≫ φ.right a b c d y =
      ∑ x, (φ.fSymbols hS).Finv a b c d y x • φ.left a b c d x := by
  conv_lhs => rw [← φ.associatorBasis_apply hS, ← (φ.leftBasis hS a b c d).sum_repr
    (φ.associatorBasis hS a b c d y)]
  simp [fSymbols, fInvMatrix, Basis.toMatrix_apply]

/-- F-symbols expressing the left family in the right family across the associator are the
extracted F-symbols. -/
theorem eq_fSymbols_of_left_eq {P : FSymbols R N}
    (h : ∀ a b c d (x : N.Left a b c d), φ.left a b c d x =
      (α_ (S a) (S b) (S c)).hom ≫ ∑ y, P.F a b c d x y • φ.right a b c d y) :
    P = φ.fSymbols hS := by
  ext a b c d x y
  have h' : φ.left a b c d x = ∑ y, P.F a b c d x y • φ.associatorBasis hS a b c d y := by
    simp [h a b c d x, associatorBasis_apply, Preadditive.comp_sum]
  rw [fSymbols_F, fMatrix, Matrix.transpose_apply, Basis.toMatrix_apply, h',
    Basis.repr_sum_self]

include hS in
/-- **Extraction of F-symbols.** For a split simple family in a monoidal linear category with a
fusion basis for fusion rules `N`, there is exactly one F-symbols for `N` expressing the left
family `(φ^{ab→e}_i ▷ S c) ≫ φ^{ec→d}_j` in the right family `(S a ◁ φ^{bc→f}_k) ≫ φ^{af→d}_l`
across the associator. -/
theorem existsUnique_fSymbols :
    ∃! P : FSymbols R N, ∀ a b c d (x : N.Left a b c d), φ.left a b c d x =
      (α_ (S a) (S b) (S c)).hom ≫ ∑ y, P.F a b c d x y • φ.right a b c d y :=
  ⟨φ.fSymbols hS, φ.left_eq_fSymbols hS, fun _ ↦ φ.eq_fSymbols_of_left_eq hS⟩

end Families

end FusionBasis

end TauCeti
