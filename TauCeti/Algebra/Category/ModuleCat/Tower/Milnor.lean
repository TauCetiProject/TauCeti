/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact
public import TauCeti.Algebra.Homology.ShortComplex.Limit

/-!
# The Milnor sequence of a tower of complexes of modules

A *tower of complexes* is a functor `C : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat R) c`, a sequence of
complexes `C₀ ← C₁ ← C₂ ← ⋯` of `R`-modules of an arbitrary shape `c`. In each degree `i` its terms
form a tower of modules `C.term i`, and the differentials form morphisms of towers. Applying
`ModuleTower.lim` degreewise gives the *limit complex* `C.limComplex`, which with its projections is
a limit of `C` (`ComplexTower.isLimitLimComplexCone`), and applying `ModuleTower.Product` gives the
*product complex* `C.productComplex`. The shift maps `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)` form a chain map of the
product complex whose kernel is the limit complex. When the shift is surjective in every degree,
equivalently `lim¹` of every tower of terms vanishes (for instance when every transition map
`Cₙ₊₁ → Cₙ` is surjective, `ModuleTower.shift_surjective`, or every tower of terms is
Mittag-Leffler, `ModuleTower.shift_surjective_of_isMittagLeffler`),

`0 → lim C → ∏ₙ Cₙ → ∏ₙ Cₙ → 0`

is a short exact sequence of complexes (`ComplexTower.shortComplex_shortExact`). Products of
modules are exact, so the homology of the product complex is the product of the homologies
(`ComplexTower.productHomologyEquiv`), and the shift acts on it as the shift of the tower of
homology modules `C.homology i`. The long exact homology sequence then splits into the
**Milnor sequences**: for every pair of degrees `i, j` with `c.Rel i j`,

`0 → lim¹ Hᵢ(Cₙ) → Hⱼ(lim C) → lim Hⱼ(Cₙ) → 0`

is exact (`ComplexTower.limOneToHomology_injective`,
`ComplexTower.exact_limOneToHomology_homologyToLim`, `ComplexTower.homologyToLim_surjective`).
The map `Hⱼ(lim C) → lim Hⱼ(Cₙ)` is induced by the projections `lim C → Cₙ`, and the map
`lim¹ Hᵢ(Cₙ) → Hⱼ(lim C)` is induced by the connecting map of the short exact sequence above.

For cochain complexes indexed by `ℤ` and `i = k - 1`, `j = k`, this is the cochain sequence
`0 → lim¹ H^(k-1)(Cₙ) → H^k(lim C) → lim H^k(Cₙ) → 0`; for chain complexes indexed by `ℕ` and
`i = j + 1`, it is the chain sequence `0 → lim¹ H_(j+1)(Cₙ) → H_j(lim C) → lim H_j(Cₙ) → 0`.
When `lim¹ Hᵢ(Cₙ)` vanishes, for instance when the tower of homology modules is Mittag-Leffler
(`ModuleTower.subsingleton_limOne_of_isMittagLeffler`), the map `Hⱼ(lim C) → lim Hⱼ(Cₙ)` is
therefore bijective (`ComplexTower.homologyToLim_bijective`).

## Main declarations

* `TauCeti.ComplexTower`: towers of complexes of `R`-modules of shape `c`.
* `TauCeti.ComplexTower.limComplex`, `TauCeti.ComplexTower.isLimitLimComplexCone`: the limit
  complex, a limit of the tower.
* `TauCeti.ComplexTower.productComplex`, `TauCeti.ComplexTower.productComplexShift`: the product
  complex and the shift chain map.
* `TauCeti.ComplexTower.shortComplex_shortExact`: `0 → lim C → ∏ₙ Cₙ → ∏ₙ Cₙ → 0` is short
  exact for towers whose shift is surjective in every degree.
* `TauCeti.ComplexTower.productHomologyEquiv`: the homology of the product complex is the product
  of the homologies, compatibly with the shifts.
* `TauCeti.ComplexTower.homologyToLim`, `TauCeti.ComplexTower.limOneToHomology`: the two maps of
  the Milnor sequence.
* `TauCeti.ComplexTower.limOneToHomology_injective`,
  `TauCeti.ComplexTower.exact_limOneToHomology_homologyToLim`,
  `TauCeti.ComplexTower.homologyToLim_surjective`: exactness of the Milnor sequence.
* `TauCeti.ComplexTower.homologyToLim_bijective`: `Hⱼ(lim C) ≅ lim Hⱼ(Cₙ)` when `lim¹ Hᵢ(Cₙ)`
  vanishes.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* C. A. Weibel, *An introduction to homological algebra*, Theorem 3.5.8.
* [Stacks: More on Algebra, Lemma 15.87.1, Tag 0919](https://stacks.math.columbia.edu/tag/0919)
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory Limits Opposite

universe v u w

/-- A tower of complexes of `R`-modules of shape `c`: a functor `ℕᵒᵖ ⥤ HomologicalComplex`, given by
complexes `Cₙ` and chain maps `Cₙ₊₁ → Cₙ`. -/
abbrev ComplexTower (R : Type u) [Ring R] {ι : Type w} (c : ComplexShape ι) :=
  ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{v} R) c

namespace ComplexTower

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι} (C : ComplexTower.{v} R c)

section Complexes

/-- The tower of degree-`i` terms of a tower of complexes. -/
abbrev term (i : ι) : ModuleTower.{v} R :=
  C ⋙ HomologicalComplex.eval _ c i

/-- The tower of degree-`i` homology modules of a tower of complexes. -/
abbrev homology (i : ι) : ModuleTower.{v} R :=
  C ⋙ HomologicalComplex.homologyFunctor _ c i

/-- The differentials `Cₙ^i → Cₙ^j` of a tower of complexes, as a morphism of towers. -/
def dTower (i j : ι) : C.term i ⟶ C.term j :=
  Functor.whiskerLeft C (HomologicalComplex.dNatTrans _ c i j)

@[simp]
theorem dTower_app (i j : ι) (n : ℕᵒᵖ) : (C.dTower i j).app n = (C.obj n).d i j :=
  (rfl)

/-- Consecutive differentials of a tower of complexes compose to zero. -/
theorem dTower_comp_dTower (i j k : ι) : C.dTower i j ≫ C.dTower j k = 0 := by
  ext n : 2
  simp

/-- The differential between degrees not related by the complex shape vanishes. -/
theorem dTower_eq_zero {i j : ι} (h : ¬c.Rel i j) : C.dTower i j = 0 := by
  ext n : 2
  simp [(C.obj n).shape i j h]

/-- The transition maps of the tower of homology modules are the maps induced on homology by the
transition chain maps of the tower. -/
theorem homology_transition (i : ι) (n : ℕ) :
    (C.homology i).transition n =
      (HomologicalComplex.homologyMap (C.map (homOfLE (Nat.le_succ n)).op) i).hom := by
  rw [ModuleTower.transition_def]
  -- The homology functor sends `C.map` to `homologyMap`, by definition of the composite functor.
  rfl

/-- The limit complex of a tower of complexes: in degree `i`, the limit of the tower of degree-`i`
terms, with the differential induced by the differentials of the tower. -/
@[expose]
def limComplex : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (C.term i).lim
  d i j := ModuleCat.ofHom (ModuleTower.limMap (C.dTower i j))
  shape i j h := by
    rw [C.dTower_eq_zero h, ModuleTower.limMap_zero, ModuleCat.ofHom_zero]
  d_comp_d' i j k _ _ := by
    rw [← ModuleCat.ofHom_comp, ← ModuleTower.limMap_comp, dTower_comp_dTower,
      ModuleTower.limMap_zero, ModuleCat.ofHom_zero]

@[simp]
theorem limComplex_X (i : ι) : C.limComplex.X i = ModuleCat.of R (C.term i).lim :=
  (rfl)

@[simp]
theorem limComplex_d_hom (i j : ι) :
    (C.limComplex.d i j).hom = ModuleTower.limMap (C.dTower i j) :=
  (rfl)

/-- The product complex of a tower of complexes: in degree `i`, the product of the degree-`i`
terms, with the product of the differentials. -/
@[expose]
def productComplex : HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (C.term i).Product
  d i j := ModuleCat.ofHom (ModuleTower.productMap (C.dTower i j))
  shape i j h := by
    rw [C.dTower_eq_zero h, ModuleTower.productMap_zero, ModuleCat.ofHom_zero]
  d_comp_d' i j k _ _ := by
    rw [← ModuleCat.ofHom_comp, ← ModuleTower.productMap_comp, dTower_comp_dTower,
      ModuleTower.productMap_zero, ModuleCat.ofHom_zero]

@[simp]
theorem productComplex_X (i : ι) : C.productComplex.X i = ModuleCat.of R (C.term i).Product :=
  (rfl)

@[simp]
theorem productComplex_d_hom (i j : ι) :
    (C.productComplex.d i j).hom = ModuleTower.productMap (C.dTower i j) :=
  (rfl)

/-- The inclusion of the limit complex into the product complex. -/
def limComplexι : C.limComplex ⟶ C.productComplex where
  f i := ModuleCat.ofHom (C.term i).lim.subtype
  comm' i j _ := by
    ext x : 2
    exact (ModuleTower.coe_limMap_apply (C.dTower i j) x).symm

@[simp]
theorem limComplexι_f_hom (i : ι) : (C.limComplexι.f i).hom = (C.term i).lim.subtype :=
  (rfl)

/-- The shift maps `δ(x)ₙ = xₙ - φₙ(xₙ₊₁)` of the towers of terms, as a chain map of the product
complex. -/
def productComplexShift : C.productComplex ⟶ C.productComplex where
  f i := ModuleCat.ofHom (C.term i).shift
  comm' i j _ := by
    ext x : 2
    exact (ModuleTower.shift_natural_apply (C.dTower i j) x).symm

@[simp]
theorem productComplexShift_f_hom (i : ι) : (C.productComplexShift.f i).hom = (C.term i).shift :=
  (rfl)

/-- The projection of the product complex onto the complex `Cₙ`. -/
def productComplexπ (n : ℕ) : C.productComplex ⟶ C.obj (op n) where
  f i := ModuleCat.ofHom (LinearMap.proj n)
  comm' i j _ := by
    ext x : 2
    exact (ModuleTower.productMap_apply (C.dTower i j) x n).symm

@[simp]
theorem productComplexπ_f_hom (n : ℕ) (i : ι) :
    ((C.productComplexπ n).f i).hom = LinearMap.proj n :=
  (rfl)

/-- The projection of the limit complex onto the complex `Cₙ`. -/
def limComplexπ (n : ℕ) : C.limComplex ⟶ C.obj (op n) where
  f i := ModuleCat.ofHom ((C.term i).limπ n)
  comm' i j _ := ModuleCat.hom_ext (ModuleTower.limπ_comp_limMap (C.dTower i j) n).symm

@[simp]
theorem limComplexπ_f_hom (n : ℕ) (i : ι) :
    ((C.limComplexπ n).f i).hom = (C.term i).limπ n :=
  (rfl)

@[reassoc (attr := simp)]
theorem limComplexι_comp_productComplexπ (n : ℕ) :
    C.limComplexι ≫ C.productComplexπ n = C.limComplexπ n := by
  ext i : 2
  exact LinearMap.ext fun (x : (C.term i).lim) ↦ ((C.term i).limπ_apply n x).symm

/-- The shift followed by the projection to `Cₙ` is the difference of the projections to `Cₙ`
and to `Cₙ₊₁`, the latter followed by the transition `Cₙ₊₁ → Cₙ`. -/
theorem productComplexShift_comp_productComplexπ (n : ℕ) :
    C.productComplexShift ≫ C.productComplexπ n =
      C.productComplexπ n - C.productComplexπ (n + 1) ≫ C.map (homOfLE (Nat.le_succ n)).op := by
  ext i : 2
  refine LinearMap.ext fun (x : (C.term i).Product) ↦ ?_
  refine ((C.term i).shift_apply x n).trans ?_
  rw [ModuleTower.transition_def]
  -- Both sides are `xₙ - φₙ(xₙ₊₁)`; the right side is evaluated through the componentwise
  -- definitions of `productComplexπ`, of differences and of composites of chain maps.
  rfl

/-- The projections of the limit complex are compatible with the maps of the tower. -/
@[reassoc (attr := simp)]
theorem limComplexπ_comp_map {n k : ℕ} (f : op k ⟶ op n) :
    C.limComplexπ k ≫ C.map f = C.limComplexπ n := by
  ext i : 2
  exact (congrArg (· ∘ₗ (C.term i).limπ k) ((C.term i).map_hom_eq_transitionOfLE f)).trans
    ((C.term i).transitionOfLE_comp_limπ _)

/-- The limit complex, with its projections onto the complexes `Cₙ`, as a cone over the tower. -/
@[expose]
def limComplexCone : Cone C where
  pt := C.limComplex
  π := NatTrans.ofOpSequence (fun n ↦ C.limComplexπ n) fun n ↦ by
    simp

@[simp]
theorem limComplexCone_pt : C.limComplexCone.pt = C.limComplex :=
  (rfl)

@[simp]
theorem limComplexCone_π_app (n : ℕ) : C.limComplexCone.π.app (op n) = C.limComplexπ n :=
  (rfl)

/-- The limit complex, with its projections, is a limit of the tower of complexes. -/
def isLimitLimComplexCone : IsLimit C.limComplexCone :=
  HomologicalComplex.isLimitOfEval _ _ fun i ↦
    IsLimit.ofIsoLimit (C.term i).isLimitLimCone <| Cone.ext (Iso.refl _) fun ⟨n⟩ ↦
      ModuleCat.hom_ext ((C.term i).limCone_π_app n)

end Complexes

section ShortExact

/-- The sequence of complexes `lim C → ∏ₙ Cₙ → ∏ₙ Cₙ` formed by the inclusion and the shift. -/
@[expose]
def shortComplex : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c) :=
  ShortComplex.mk C.limComplexι C.productComplexShift <| by
    ext i : 2
    exact (ModuleTower.exact_lim_subtype_shift (C.term i)).linearMap_comp_eq_zero

@[simp]
theorem shortComplex_f : C.shortComplex.f = C.limComplexι :=
  (rfl)

@[simp]
theorem shortComplex_g : C.shortComplex.g = C.productComplexShift :=
  (rfl)

variable {C} (hC : ∀ i, Function.Surjective (C.term i).shift)

include hC in
/-- **The product-complex short exact sequence.** If the shift of a tower of complexes is
surjective in every degree, for instance if every transition map is surjective in every degree,
then `0 → lim C → ∏ₙ Cₙ → ∏ₙ Cₙ → 0`, formed by the inclusion and the shift, is a short exact
sequence of complexes. -/
theorem shortComplex_shortExact : C.shortComplex.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
        (ModuleTower.exact_lim_subtype_shift (C.term i))
      mono_f := (ModuleCat.mono_iff_injective _).2 (C.term i).lim.injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).2 (hC i) }

end ShortExact

section ProductHomology

/-- The product complex, with its projections, is a product of the complexes `Cₙ`. -/
def isLimitProductComplexFan :
    IsLimit (Fan.mk C.productComplex C.productComplexπ : Fan fun n ↦ C.obj (op n)) :=
  HomologicalComplex.isLimitOfEval _ _ fun i ↦
    (isLimitMapConeFanMkEquiv _ _ _).symm <|
      IsLimit.ofIsoLimit (ModuleCat.productConeIsLimit fun n ↦ (C.obj (op n)).X i)
        (Cone.ext (Iso.refl _) fun _ ↦
          -- The two legs are the projection `LinearMap.proj n`, in the same carrier.
          (rfl))

/-- **Homology of the product complex.** The degree-`i` homology of the product complex is the
product of the degree-`i` homology modules of the complexes `Cₙ`, through the maps induced by the
projections; see `productHomologyEquiv_apply`. -/
def productHomologyEquiv (i : ι) :
    C.productComplex.homology i ≃ₗ[R] (C.homology i).Product :=
  (IsLimit.conePointUniqueUpToIso
    (isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) c i) _ _
      C.isLimitProductComplexFan)
    (ModuleCat.productConeIsLimit fun n ↦ (C.obj (op n)).homology i)).toLinearEquiv

@[simp]
theorem productHomologyEquiv_apply (i : ι) (x : C.productComplex.homology i) (n : ℕ) :
    C.productHomologyEquiv i x n = HomologicalComplex.homologyMap (C.productComplexπ n) i x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) c i) _ _
      C.isLimitProductComplexFan)
    (ModuleCat.productConeIsLimit fun n ↦ (C.obj (op n)).homology i) ⟨n⟩)) x

/-- On homology, the projections of the product complex intertwine the shift chain map with the
shift of the tower of homology modules. -/
theorem productHomologyEquiv_homologyMap_productComplexShift (i : ι)
    (x : C.productComplex.homology i) :
    C.productHomologyEquiv i (HomologicalComplex.homologyMap C.productComplexShift i x) =
      (C.homology i).shift (C.productHomologyEquiv i x) := by
  funext n
  have h : HomologicalComplex.homologyMap C.productComplexShift i ≫
      HomologicalComplex.homologyMap (C.productComplexπ n) i =
        HomologicalComplex.homologyMap (C.productComplexπ n) i -
          HomologicalComplex.homologyMap (C.productComplexπ (n + 1)) i ≫
            HomologicalComplex.homologyMap (C.map (homOfLE (Nat.le_succ n)).op) i := by
    rw [← HomologicalComplex.homologyMap_comp, productComplexShift_comp_productComplexπ,
      HomologicalComplex.homologyMap_sub, HomologicalComplex.homologyMap_comp]
  rw [productHomologyEquiv_apply, ModuleTower.shift_apply, productHomologyEquiv_apply,
    productHomologyEquiv_apply, homology_transition]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x

/-- On homology, the projections of the product complex restrict to those of the limit
complex. -/
theorem productHomologyEquiv_homologyMap_limComplexι (i : ι) (x : C.limComplex.homology i)
    (n : ℕ) :
    C.productHomologyEquiv i (HomologicalComplex.homologyMap C.limComplexι i x) n =
      HomologicalComplex.homologyMap (C.limComplexπ n) i x := by
  rw [productHomologyEquiv_apply, ← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
    limComplexι_comp_productComplexπ]

end ProductHomology

section Milnor

/-- The map `Hⱼ(lim C) → lim Hⱼ(Cₙ)` of the Milnor sequence, induced by the projections of the
limit complex onto the complexes `Cₙ`. -/
def homologyToLim (j : ι) : C.limComplex.homology j →ₗ[R] (C.homology j).lim :=
  (C.homology j).limLift (fun n ↦ (HomologicalComplex.homologyMap (C.limComplexπ n) j).hom)
    fun n ↦ by
      have h : HomologicalComplex.homologyMap (C.limComplexπ (n + 1)) j ≫
          HomologicalComplex.homologyMap (C.map (homOfLE (Nat.le_succ n)).op) j =
            HomologicalComplex.homologyMap (C.limComplexπ n) j := by
        rw [← HomologicalComplex.homologyMap_comp, limComplexπ_comp_map]
      rw [homology_transition]
      exact congrArg ModuleCat.Hom.hom h

@[simp]
theorem coe_homologyToLim_apply (j : ι) (x : C.limComplex.homology j) (n : ℕ) :
    (C.homologyToLim j x : (C.homology j).Product) n =
      HomologicalComplex.homologyMap (C.limComplexπ n) j x :=
  ModuleTower.coe_limLift_apply (C.homology j) _ _ x n

/-- The map `Hⱼ(lim C) → lim Hⱼ(Cₙ)` is the map induced by the inclusion into the product
complex, read in the product of the homologies. -/
theorem coe_homologyToLim (j : ι) (x : C.limComplex.homology j) :
    (C.homologyToLim j x : (C.homology j).Product) =
      C.productHomologyEquiv j (HomologicalComplex.homologyMap C.limComplexι j x) :=
  funext fun n ↦ (C.coe_homologyToLim_apply j x n).trans
    (C.productHomologyEquiv_homologyMap_limComplexι j x n).symm

variable {C} (hC : ∀ i, Function.Surjective (C.term i).shift)

/-- The connecting map of the product-complex short exact sequence, as a linear map between the
homology of the product complex and of the limit complex. -/
private def connecting {i j : ι} (hij : c.Rel i j) :
    C.productComplex.homology i →ₗ[R] C.limComplex.homology j :=
  ((C.shortComplex_shortExact hC).δ i j hij).hom

private theorem connecting_homologyMap_productComplexShift {i j : ι} (hij : c.Rel i j)
    (y : C.productComplex.homology i) :
    connecting hC hij (HomologicalComplex.homologyMap C.productComplexShift i y) = 0 :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((C.shortComplex_shortExact hC).comp_δ i j hij)) y

/-- Exactness of the homology sequence at the source of the connecting map. -/
private theorem exact_homologyMap_productComplexShift_connecting {i j : ι} (hij : c.Rel i j) :
    Function.Exact (HomologicalComplex.homologyMap C.productComplexShift i).hom
      (connecting hC hij) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((C.shortComplex_shortExact hC).homology_exact₃ i j hij)

/-- Exactness of the homology sequence at the homology of the limit complex. -/
private theorem exact_connecting_homologyMap_limComplexι {i j : ι} (hij : c.Rel i j) :
    Function.Exact (connecting hC hij) (HomologicalComplex.homologyMap C.limComplexι j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((C.shortComplex_shortExact hC).homology_exact₁ i j hij)

include hC in
/-- Exactness of the homology sequence at the homology of the product complex. -/
private theorem exact_homologyMap_limComplexι_productComplexShift (j : ι) :
    Function.Exact (HomologicalComplex.homologyMap C.limComplexι j).hom
      (HomologicalComplex.homologyMap C.productComplexShift j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((C.shortComplex_shortExact hC).homology_exact₂ j)

/-- The image of the shift of the tower of homology modules is killed by the connecting map. -/
private theorem range_shift_le_ker {i j : ι} (hij : c.Rel i j) :
    LinearMap.range (C.homology i).shift ≤
      LinearMap.ker (connecting hC hij ∘ₗ (C.productHomologyEquiv i).symm.toLinearMap) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := (C.productHomologyEquiv i).surjective x
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← productHomologyEquiv_homologyMap_productComplexShift, LinearEquiv.symm_apply_apply]
  exact connecting_homologyMap_productComplexShift hC hij y

/-- The map `lim¹ Hᵢ(Cₙ) → Hⱼ(lim C)` of the Milnor sequence, for `c.Rel i j`: the connecting map
of the product-complex short exact sequence, read on the product of the homologies, descends to
the cokernel `lim¹` of the shift. -/
def limOneToHomology {i j : ι} (hij : c.Rel i j) :
    (C.homology i).limOne →ₗ[R] C.limComplex.homology j :=
  (LinearMap.range (C.homology i).shift).liftQ
    (connecting hC hij ∘ₗ (C.productHomologyEquiv i).symm.toLinearMap)
    (range_shift_le_ker hC hij)

/-- The class of a family of homology classes is sent to the connecting map of the corresponding
homology class of the product complex. -/
@[simp]
theorem limOneToHomology_mk {i j : ι} (hij : c.Rel i j) (x : (C.homology i).Product) :
    C.limOneToHomology hC hij (Submodule.Quotient.mk x) =
      (C.shortComplex_shortExact hC).δ i j hij ((C.productHomologyEquiv i).symm x) := by
  rw [limOneToHomology, Submodule.liftQ_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    connecting]
  -- `ModuleCat.Hom.hom` is an abbreviation for the `ConcreteCategory.hom` coercion on the right.
  rfl

/-- **Exactness of the Milnor sequence at `lim¹`.** The map `lim¹ Hᵢ(Cₙ) → Hⱼ(lim C)` is
injective. -/
theorem limOneToHomology_injective {i j : ι} (hij : c.Rel i j) :
    Function.Injective (C.limOneToHomology hC hij) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker, limOneToHomology, Submodule.liftQ_apply, LinearMap.comp_apply] at hz
  -- The class of `x` in the product complex is killed by the connecting map, hence is the image
  -- of a class under the shift.
  obtain ⟨y, hy⟩ := (exact_homologyMap_productComplexShift_connecting hC hij _).1 hz
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨C.productHomologyEquiv i y, ?_⟩
  rw [← productHomologyEquiv_homologyMap_productComplexShift]
  exact (C.productHomologyEquiv i).eq_symm_apply.1 hy

/-- **Exactness of the Milnor sequence at `Hⱼ(lim C)`.** The image of `lim¹ Hᵢ(Cₙ) → Hⱼ(lim C)`
is the kernel of `Hⱼ(lim C) → lim Hⱼ(Cₙ)`. -/
theorem exact_limOneToHomology_homologyToLim {i j : ι} (hij : c.Rel i j) :
    Function.Exact (C.limOneToHomology hC hij) (C.homologyToLim j) := by
  -- `homologyToLim` is the inclusion into the product complex followed by the isomorphism
  -- `productHomologyEquiv`, and `limOneToHomology` has the same image as the connecting map.
  have hrange : Set.range (C.limOneToHomology hC hij) = Set.range (connecting hC hij) := by
    rw [← LinearMap.coe_range, ← LinearMap.coe_range, limOneToHomology, Submodule.range_liftQ,
      LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  intro x
  simpa [hrange, Subtype.ext_iff, coe_homologyToLim] using
    exact_connecting_homologyMap_limComplexι hC hij x

include hC in
/-- **Exactness of the Milnor sequence at `lim Hⱼ(Cₙ)`.** The map `Hⱼ(lim C) → lim Hⱼ(Cₙ)` is
surjective. -/
theorem homologyToLim_surjective (j : ι) : Function.Surjective (C.homologyToLim j) := by
  intro y
  -- The homology class of the product complex corresponding to `y` is killed by the shift, hence
  -- comes from the limit complex.
  have hy : HomologicalComplex.homologyMap C.productComplexShift j
      ((C.productHomologyEquiv j).symm y) = 0 := by
    apply (C.productHomologyEquiv j).injective
    rw [productHomologyEquiv_homologyMap_productComplexShift, LinearEquiv.apply_symm_apply,
      map_zero]
    exact LinearMap.mem_ker.1 (by rw [← ModuleTower.lim_eq_ker]; exact y.2)
  obtain ⟨x, hx⟩ := (exact_homologyMap_limComplexι_productComplexShift hC j _).1 hy
  refine ⟨x, Subtype.ext ?_⟩
  rw [coe_homologyToLim]
  exact (C.productHomologyEquiv j).eq_symm_apply.1 hx

include hC in
/-- If `lim¹ Hᵢ(Cₙ)` vanishes, for instance when the tower of degree-`i` homology modules is
Mittag-Leffler, then `Hⱼ(lim C) → lim Hⱼ(Cₙ)` is bijective. -/
theorem homologyToLim_bijective {i j : ι} (hij : c.Rel i j)
    [Subsingleton (C.homology i).limOne] : Function.Bijective (C.homologyToLim j) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, homologyToLim_surjective hC j⟩
  obtain ⟨y, rfl⟩ := (exact_limOneToHomology_homologyToLim hC hij x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

end Milnor

end ComplexTower

end TauCeti
