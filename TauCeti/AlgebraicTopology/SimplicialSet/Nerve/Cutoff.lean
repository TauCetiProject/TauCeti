/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.BigOperators
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.CategoryTheory.Category.QuiverTotal

/-!
# The cutoff contraction of the cochains of a groupoid nerve

Let `C` be a groupoid, `k` a commutative ring and `M` a `k`-module. The cochain complex
`TauCeti.nerveCochainComplex C k M` of the nerve of `C` with coefficients in `M` is, in degree
`n`, the module of `M`-valued functions on strings `x₀ ⟶ x₁ ⟶ ⋯ ⟶ xₙ` of `n` composable arrows
(`TauCeti.cochainValuesEquiv`), with the alternating sum of faces as differential.

A function `c : C → k` on the objects is a *cutoff* if for every object `x` its values at the
sources of the arrows with target `x` sum to one, `∑ᶠ b : Quiver.Costar x, c b.1 = 1`. Inverting
arrows, this is the normalization `∑ᶠ a ∈ Quiver.Total.left ⁻¹' {x}, c a.right = 1` of the cutoff
functions `TauCeti.Quiver.IsCutoff` of proper étale groupoids
(`Quiver.Total.finsum_costar_eq_finsum_mem_preimage_left_singleton`). The groupoid need not be
finite, and no topology enters here.

Prepending an arrow weighted by `c` defines operators lowering the degree,
$$(h\varphi)(x_0 \to \cdots \to x_n) = \sum_{b : y \to x_0} c(y)\,
  \varphi(y \xrightarrow{b} x_0 \to \cdots \to x_n)$$
(`TauCeti.nerveCochainComplex.cutoffPrepend`). For each string only finitely many terms are nonzero
(otherwise `k` is the zero ring). With
`P φ (x) = ∑_{b : y ⟶ x} c(y) φ(y)` (`TauCeti.nerveCochainComplex.cutoffAverage`), they satisfy
$$h \circ d + d \circ h = 1 \text{ in positive degrees}, \qquad h \circ d = 1 - P
  \text{ in degree } 0.$$
So the identity of the cochain complex is homotopic to the cochain map that is `P` in degree `0`
and zero in positive degrees (`TauCeti.nerveCochainComplex.cutoffHomotopy`). In particular every
positive-degree cocycle `φ` is the coboundary of `h φ`, the positive-degree cohomology vanishes,
the values of `P` are constant along arrows, and every degree-`0` cocycle, that is every function
constant along arrows, is fixed by `P`.
No sign is needed: prepending an arrow commutes with the faces deleting later vertices, and the
face deleting the second vertex composes the prepended arrow with the first arrow of the string
(`CategoryTheory.nerve.δ_succ_precomp`), which reindexes the sum since `C` is a groupoid. Every
arrow is counted, including every isotropy arrow.

The operators are natural for functors `Φ : D ⥤ C` that are bijective on arrows with a given
target, such as the restriction to a full subgroupoid on a saturated set of objects, with the
cutoff pulled back along `Φ`
(`TauCeti.nerveCochainComplex.cochainComplexMap_f_comp_cutoffPrependHom`).

This is the groupoid form of the contraction of the cochains of an action presentation
`TauCeti.groupCohomology.cutoffHomotopy`, which inserts a last label instead of a first arrow.

## Main declarations

* `TauCeti.nerveCochainComplex`: the cochain complex of the nerve with coefficients in `M`.
* `TauCeti.nerveCochainComplex.cutoffPrependHom`: the operator `h` lowering the degree.
* `TauCeti.nerveCochainComplex.cutoffCochainMap`: the cutoff average `P`, placed in degree `0`.
* `TauCeti.nerveCochainComplex.cutoffHomotopy`: the homotopy from the identity to
  `TauCeti.nerveCochainComplex.cutoffCochainMap`.
* `TauCeti.nerveCochainComplex.isZero_homology_succ`: the positive-degree cohomology vanishes.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for cutoff functions and the vanishing
  of the cohomology of proper groupoids.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public section

noncomputable section

open CategoryTheory Simplicial

universe w

namespace TauCeti

variable (C : Type w) [Category.{w} C] (k : Type w) [CommRing k] (M : ModuleCat.{w} k)

/-- The cochain complex of the nerve of `C` with coefficients in `M`: in degree `n`, the
`k`-linear maps from the `n`-chains of the nerve to `M`. These are the `M`-valued functions on
strings of `n` composable arrows (`TauCeti.cochainValuesEquiv`). -/
abbrev nerveCochainComplex : CochainComplex (ModuleCat.{w} k) ℕ :=
  ((nerve C).chainComplex (ModuleCat.of k k)).linearYonedaObj k M

namespace nerveCochainComplex

variable {C k M}

/-- The value coordinates `TauCeti.cochainValuesLinearEquiv` on the cochains of degree `n` of the
nerve: they identify these cochains `k`-linearly with the functions on strings of `n` composable
arrows. -/
def valuesEquiv (n : ℕ) : (nerveCochainComplex C k M).X n ≃ₗ[k] (ComposableArrows C n → M) :=
  cochainValuesLinearEquiv k M (nerve C) n

/-- The value coordinates of the nerve cochains are those of `TauCeti.cochainValuesEquiv`. -/
theorem valuesEquiv_apply (n : ℕ) (φ : (nerveCochainComplex C k M).X n) :
    valuesEquiv n φ = cochainValuesEquiv k M (nerve C) n φ :=
  congrFun (coe_cochainValuesLinearEquiv k M (nerve C) n) φ

/-- The values of a coboundary are alternating sums of values on faces. -/
theorem valuesEquiv_d (n : ℕ) (φ : (nerveCochainComplex C k M).X n)
    (σ : ComposableArrows C (n + 1)) :
    valuesEquiv (n + 1) ((nerveCochainComplex C k M).d n (n + 1) φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • valuesEquiv n φ ((nerve C).δ i σ) := by
  simp only [valuesEquiv_apply]
  exact cochainValuesEquiv_linearYonedaObj_d k M (nerve C) n φ σ

variable (c : C → k)

/-- Prepending an arrow weighted by `c`: the value at a string `x₀ ⟶ ⋯ ⟶ xₙ` is the sum, over the
arrows `b : y ⟶ x₀`, of `c y` times the value at the string `y ⟶ x₀ ⟶ ⋯ ⟶ xₙ`. -/
def cutoffPrepend (n : ℕ) (φ : ComposableArrows C (n + 1) → M) (σ : ComposableArrows C n) : M :=
  ∑ᶠ b : Quiver.Costar σ.left, c b.1 • φ (σ.precomp b.2)

/-- The cutoff average of a function on objects, viewed as strings of no arrows: the value at `x`
is the sum, over the arrows `b : y ⟶ x`, of `c y` times the value at `y`. -/
def cutoffAverage (φ : ComposableArrows C 0 → M) (σ : ComposableArrows C 0) : M :=
  ∑ᶠ b : Quiver.Costar σ.left, c b.1 • φ (ComposableArrows.mk₀ b.1)

variable {c}

/-- Under the cutoff normalization at `x`, sums weighted by `c` over the arrows with target `x`
are finite sums over one finite set of such arrows, on which `c` sums to one. If the sum of the
values of `c` has infinitely many nonzero terms, the ring is trivial and so is `M`. -/
private theorem exists_finset_finsum_smul_eq_sum {x : C}
    (hc : ∑ᶠ b : Quiver.Costar x, c b.1 = 1) :
    ∃ s : Finset (Quiver.Costar x), ∑ b ∈ s, c b.1 = 1 ∧
      ∀ g : Quiver.Costar x → M, ∑ᶠ b, c b.1 • g b = ∑ b ∈ s, c b.1 • g b := by
  by_cases hfin : (Function.support fun b : Quiver.Costar x ↦ c b.1).Finite
  · refine ⟨hfin.toFinset, ?_, fun g ↦ finsum_eq_sum_of_support_subset _ ?_⟩
    · rwa [← finsum_eq_sum_of_support_subset _ (by simp)]
    · exact (Function.support_smul_subset_left _ _).trans (by simp)
  · -- A sum with infinitely many nonzero terms is zero, so `1 = 0` in `k`.
    have : Subsingleton k := subsingleton_of_zero_eq_one <| by
      rw [← hc, finsum_of_infinite_support hfin]
    have : Subsingleton M := Module.subsingleton k M
    exact ⟨∅, Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩

variable (hc : ∀ x : C, ∑ᶠ b : Quiver.Costar x, c b.1 = 1)
include hc

/-- Prepending arrows weighted by a cutoff is additive. -/
theorem cutoffPrepend_add (n : ℕ) (φ ψ : ComposableArrows C (n + 1) → M) :
    cutoffPrepend c n (φ + ψ) = cutoffPrepend c n φ + cutoffPrepend c n ψ := by
  funext σ
  obtain ⟨s, -, hs⟩ := exists_finset_finsum_smul_eq_sum (M := M) (hc σ.left)
  simp only [cutoffPrepend, Pi.add_apply, hs]
  simp only [smul_add, Finset.sum_add_distrib]

/-- Prepending arrows weighted by a cutoff commutes with scalar multiplication. -/
theorem cutoffPrepend_smul (n : ℕ) (a : k) (φ : ComposableArrows C (n + 1) → M) :
    cutoffPrepend c n (a • φ) = a • cutoffPrepend c n φ := by
  funext σ
  obtain ⟨s, -, hs⟩ := exists_finset_finsum_smul_eq_sum (M := M) (hc σ.left)
  simp only [cutoffPrepend, Pi.smul_apply, hs]
  simp only [Finset.smul_sum, smul_comm a]

/-- The cutoff average is additive. -/
theorem cutoffAverage_add (φ ψ : ComposableArrows C 0 → M) :
    cutoffAverage c (φ + ψ) = cutoffAverage c φ + cutoffAverage c ψ := by
  funext σ
  obtain ⟨s, -, hs⟩ := exists_finset_finsum_smul_eq_sum (M := M) (hc σ.left)
  simp only [cutoffAverage, Pi.add_apply, hs]
  simp only [smul_add, Finset.sum_add_distrib]

/-- The cutoff average commutes with scalar multiplication. -/
theorem cutoffAverage_smul (a : k) (φ : ComposableArrows C 0 → M) :
    cutoffAverage c (a • φ) = a • cutoffAverage c φ := by
  funext σ
  obtain ⟨s, -, hs⟩ := exists_finset_finsum_smul_eq_sum (M := M) (hc σ.left)
  simp only [cutoffAverage, Pi.smul_apply, hs]
  simp only [Finset.smul_sum, smul_comm a]

variable (M) in
/-- The operator `TauCeti.nerveCochainComplex.cutoffPrepend` from cochains of degree `n + 1` to
cochains of degree `n`. -/
def cutoffPrependHom (n : ℕ) :
    (nerveCochainComplex C k M).X (n + 1) ⟶ (nerveCochainComplex C k M).X n :=
  ModuleCat.ofHom <| (valuesEquiv n).symm.toLinearMap ∘ₗ
    { toFun := cutoffPrepend c n
      map_add' := cutoffPrepend_add hc n
      map_smul' := cutoffPrepend_smul hc n } ∘ₗ (valuesEquiv (n + 1)).toLinearMap

/-- In values, `TauCeti.nerveCochainComplex.cutoffPrependHom` is
`TauCeti.nerveCochainComplex.cutoffPrepend`. -/
@[simp]
theorem valuesEquiv_cutoffPrependHom (n : ℕ) (φ : (nerveCochainComplex C k M).X (n + 1)) :
    valuesEquiv n (cutoffPrependHom M hc n φ) = cutoffPrepend c n (valuesEquiv (n + 1) φ) := by
  change valuesEquiv n ((valuesEquiv n).symm (cutoffPrepend c n (valuesEquiv (n + 1) φ))) = _
  rw [LinearEquiv.apply_symm_apply]

variable (M) in
/-- The cutoff average `TauCeti.nerveCochainComplex.cutoffAverage` on cochains of degree `0`. -/
def cutoffAverageHom : (nerveCochainComplex C k M).X 0 ⟶ (nerveCochainComplex C k M).X 0 :=
  ModuleCat.ofHom <| (valuesEquiv 0).symm.toLinearMap ∘ₗ
    { toFun := cutoffAverage c
      map_add' := cutoffAverage_add hc
      map_smul' := cutoffAverage_smul hc } ∘ₗ (valuesEquiv 0).toLinearMap

/-- In values, `TauCeti.nerveCochainComplex.cutoffAverageHom` is
`TauCeti.nerveCochainComplex.cutoffAverage`. -/
@[simp]
theorem valuesEquiv_cutoffAverageHom (φ : (nerveCochainComplex C k M).X 0) :
    valuesEquiv 0 (cutoffAverageHom M hc φ) = cutoffAverage c (valuesEquiv 0 φ) := by
  change valuesEquiv 0 ((valuesEquiv 0).symm (cutoffAverage c (valuesEquiv 0 φ))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- **Contraction in degree `0`.** Prepending to the coboundary of a function on objects
subtracts it from its cutoff average. -/
theorem cutoffPrepend_d_zero (φ : (nerveCochainComplex C k M).X 0) (σ : ComposableArrows C 0) :
    cutoffPrepend c 0 (valuesEquiv 1 ((nerveCochainComplex C k M).d 0 1 φ)) σ =
      valuesEquiv 0 φ σ - cutoffAverage c (valuesEquiv 0 φ) σ := by
  obtain ⟨s, hs₁, hs⟩ := exists_finset_finsum_smul_eq_sum (M := M) (hc σ.left)
  have h₀ (b : Quiver.Costar σ.left) : (nerve C).δ 0 (σ.precomp b.2) = σ := rfl
  have h₁ (b : Quiver.Costar σ.left) :
      (nerve C).δ (Fin.succ 0) (σ.precomp b.2) = ComposableArrows.mk₀ b.1 :=
    ComposableArrows.ext₀ rfl
  unfold cutoffPrepend cutoffAverage
  rw [hs, hs]
  simp only [valuesEquiv_d, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, zero_add, pow_one, one_smul, neg_smul, add_zero, h₀, h₁, smul_add, smul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [← Finset.sum_smul, hs₁, one_smul, sub_eq_add_neg]

variable [IsGroupoid C]

/-- **Contraction in positive degrees.** For a cochain `φ` of degree `n + 1`, prepending to its
coboundary plus the coboundary of the prepended cochain is `φ`. -/
theorem cutoffPrepend_d_add_d_cutoffPrepend (n : ℕ) (φ : (nerveCochainComplex C k M).X (n + 1))
    (σ : ComposableArrows C (n + 1)) :
    cutoffPrepend c (n + 1) (valuesEquiv (n + 2) ((nerveCochainComplex C k M).d (n + 1) (n + 2) φ))
        σ +
      valuesEquiv (n + 1) ((nerveCochainComplex C k M).d n (n + 1) (cutoffPrependHom M hc n φ)) σ =
      valuesEquiv (n + 1) φ σ := by
  obtain ⟨s, hs₁, hs⟩ := exists_finset_finsum_smul_eq_sum (M := M) (hc σ.left)
  -- Reindex the sums over the arrows into the first vertex of each face by the arrows into the
  -- first vertex of `σ`, and identify the strings with the faces of the prepended strings.
  have hface (j : Fin (n + 2)) :
      cutoffPrepend c n (valuesEquiv (n + 1) φ) ((nerve C).δ j σ) =
        ∑ b ∈ s, c b.1 • valuesEquiv (n + 1) φ ((nerve C).δ j.succ (σ.precomp b.2)) := by
    unfold cutoffPrepend
    rw [← hs]
    -- Postcomposing with the arrow from `x₀` to the first vertex of the face identifies the
    -- arrows into `x₀` with the arrows into that vertex.
    let e : σ.left ≅ σ.obj (j.succAbove 0) := asIso (σ.map (homOfLE (Fin.zero_le _)))
    refine (finsum_comp_equiv (Equiv.sigmaCongrRight fun _ ↦ e.homToEquiv)).symm.trans
      (finsum_congr fun b ↦ ?_)
    rw [nerve.δ_succ_precomp]
    rfl
  have h₀ (b : Quiver.Costar σ.left) : (nerve C).δ 0 (σ.precomp b.2) = σ := rfl
  rw [valuesEquiv_d]
  simp only [valuesEquiv_cutoffPrependHom, hface]
  unfold cutoffPrepend
  rw [hs]
  -- Split off the face deleting the prepended vertex; the other faces cancel the second sum.
  simp only [valuesEquiv_d, Fin.sum_univ_succ (n := n + 2), h₀, Fin.val_zero, pow_zero,
    one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, smul_add,
    smul_neg, Finset.smul_sum, Finset.sum_add_distrib, smul_comm (c _) ((-1 : ℤ) ^ _)]
  rw [Finset.sum_comm (s := s), ← Finset.sum_smul, hs₁, one_smul]
  abel

/-- **Contraction in positive degrees**, as an identity of maps of cochains. -/
theorem d_comp_cutoffPrependHom_add (n : ℕ) :
    (nerveCochainComplex C k M).d (n + 1) (n + 2) ≫ cutoffPrependHom M hc (n + 1) +
      cutoffPrependHom M hc n ≫ (nerveCochainComplex C k M).d n (n + 1) = 𝟙 _ := by
  ext φ : 2
  apply (valuesEquiv (n + 1)).injective
  funext σ
  rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply, map_add,
    Pi.add_apply, valuesEquiv_cutoffPrependHom]
  exact cutoffPrepend_d_add_d_cutoffPrepend hc n φ σ

omit [IsGroupoid C] in
/-- **Contraction in degree `0`**, as an identity of maps of cochains. -/
theorem d_comp_cutoffPrependHom_zero :
    (nerveCochainComplex C k M).d 0 1 ≫ cutoffPrependHom M hc 0 = 𝟙 _ - cutoffAverageHom M hc := by
  ext φ : 2
  apply (valuesEquiv 0).injective
  funext σ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, LinearMap.sub_apply,
    ModuleCat.hom_id, LinearMap.id_apply, map_sub, Pi.sub_apply, valuesEquiv_cutoffPrependHom,
    valuesEquiv_cutoffAverageHom]
  exact cutoffPrepend_d_zero hc φ σ

/-- The cutoff average of a function on objects is constant along arrows: its coboundary
vanishes. -/
theorem cutoffAverageHom_comp_d :
    cutoffAverageHom M hc ≫ (nerveCochainComplex C k M).d 0 1 = 0 := by
  have hP : cutoffAverageHom M hc =
      𝟙 _ - (nerveCochainComplex C k M).d 0 1 ≫ cutoffPrependHom M hc 0 := by
    rw [d_comp_cutoffPrependHom_zero, sub_sub_cancel]
  have hd : cutoffPrependHom M hc 0 ≫ (nerveCochainComplex C k M).d 0 1 =
      𝟙 _ - (nerveCochainComplex C k M).d 1 2 ≫ cutoffPrependHom M hc 1 := by
    rw [← d_comp_cutoffPrependHom_add hc 0, add_sub_cancel_left]
  rw [hP, Preadditive.sub_comp, Category.id_comp, Category.assoc, hd, Preadditive.comp_sub,
    Category.comp_id, ← Category.assoc, HomologicalComplex.d_comp_d, Limits.zero_comp, sub_zero,
    sub_self]

/-- The cutoff average, placed in degree `0`, as an endomorphism of the cochain complex: it is
`TauCeti.nerveCochainComplex.cutoffAverageHom` on cochains of degree `0` and zero in positive
degrees. -/
def cutoffCochainMap : nerveCochainComplex C k M ⟶ nerveCochainComplex C k M where
  f
    | 0 => cutoffAverageHom M hc
    | _ + 1 => 0
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rcases i with _ | i
    · exact (cutoffAverageHom_comp_d hc).trans Limits.comp_zero.symm
    · exact Limits.zero_comp.trans Limits.comp_zero.symm

/-- In degree `0`, `TauCeti.nerveCochainComplex.cutoffCochainMap` is the cutoff average. -/
@[simp]
theorem cutoffCochainMap_f_zero : (cutoffCochainMap (M := M) hc).f 0 = cutoffAverageHom M hc :=
  (rfl)

/-- In positive degrees, `TauCeti.nerveCochainComplex.cutoffCochainMap` is zero. -/
@[simp]
theorem cutoffCochainMap_f_succ (n : ℕ) : (cutoffCochainMap (M := M) hc).f (n + 1) = 0 :=
  (rfl)

/-- The components `TauCeti.nerveCochainComplex.cutoffPrependHom` of the cutoff homotopy, from
degree `j + 1` to degree `j`. -/
private def cutoffHomotopyHom (i j : ℕ) (hji : (ComplexShape.up ℕ).Rel j i) :
    (nerveCochainComplex C k M).X i ⟶ (nerveCochainComplex C k M).X j :=
  ((nerveCochainComplex C k M).XIsoOfEq hji.symm).hom ≫ cutoffPrependHom M hc j

private theorem sub_cutoffCochainMap_eq_nullHomotopicMap' :
    𝟙 _ - cutoffCochainMap (M := M) hc = Homotopy.nullHomotopicMap' (cutoffHomotopyHom hc) := by
  ext n : 1
  rcases n with _ | n
  · -- Degree `0` has no incoming differential, so only `d ≫ h` contributes.
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      (fun l ↦ by simp)]
    simp only [cutoffHomotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
      cutoffCochainMap_f_zero]
    exact (d_comp_cutoffPrependHom_zero hc).symm
  · rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl)]
    simp only [cutoffHomotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
      cutoffCochainMap_f_succ, sub_zero]
    exact (d_comp_cutoffPrependHom_add hc n).symm

/-- **The cutoff contraction.** The identity of the cochain complex of the nerve is homotopic to
the cutoff average placed in degree `0`, through the homotopy whose component from degree `n + 1`
to degree `n` prepends an arrow weighted by `c`
(`TauCeti.nerveCochainComplex.cutoffHomotopy_hom_succ`). -/
def cutoffHomotopy : Homotopy (𝟙 (nerveCochainComplex C k M)) (cutoffCochainMap hc) :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (sub_cutoffCochainMap_eq_nullHomotopicMap' hc)).trans (Homotopy.nullHomotopy' _)

/-- The component of `TauCeti.nerveCochainComplex.cutoffHomotopy` from degree `n + 1` to degree
`n` is `TauCeti.nerveCochainComplex.cutoffPrependHom`. -/
@[simp]
theorem cutoffHomotopy_hom_succ (n : ℕ) :
    (cutoffHomotopy (M := M) hc).hom (n + 1) n = cutoffPrependHom M hc n := by
  simp [cutoffHomotopy, Homotopy.equivSubZero, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.nullHomotopy'_hom, cutoffHomotopyHom]

/-- **The explicit primitive of a positive-degree cocycle**: prepending an arrow weighted by `c`
to a cocycle of degree `n + 1` gives a cochain whose coboundary is the cocycle. -/
theorem d_cutoffPrependHom_of_d_eq_zero {n : ℕ} {φ : (nerveCochainComplex C k M).X (n + 1)}
    (hφ : (nerveCochainComplex C k M).d (n + 1) (n + 2) φ = 0) :
    (nerveCochainComplex C k M).d n (n + 1) (cutoffPrependHom M hc n φ) = φ := by
  have h := congr($(d_comp_cutoffPrependHom_add hc n).hom φ)
  rwa [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hφ, map_zero, zero_add, ModuleCat.hom_id,
    LinearMap.id_apply] at h

/-- The cochain complex of the nerve is exact in positive degrees. -/
theorem exactAt_succ (n : ℕ) : (nerveCochainComplex C k M).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  exact fun φ hφ ↦ ⟨_, d_cutoffPrependHom_of_d_eq_zero hc hφ⟩

/-- The positive-degree cohomology of the nerve with coefficients in `M` vanishes. -/
theorem isZero_homology_succ (n : ℕ) :
    Limits.IsZero ((nerveCochainComplex C k M).homology (n + 1)) :=
  (exactAt_succ hc n).isZero_homology

omit [IsGroupoid C] in
/-- A function on objects constant along arrows, that is a cocycle of degree `0`, is its own
cutoff average. -/
theorem cutoffAverageHom_apply_of_d_eq_zero {φ : (nerveCochainComplex C k M).X 0}
    (hφ : (nerveCochainComplex C k M).d 0 1 φ = 0) : cutoffAverageHom M hc φ = φ := by
  have h := congr($(d_comp_cutoffPrependHom_zero hc).hom φ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hφ, map_zero, ModuleCat.hom_sub,
    ModuleCat.hom_id, LinearMap.sub_apply, LinearMap.id_apply] at h
  exact (sub_eq_zero.1 h.symm).symm

section Restriction

/-! ### Naturality for functors bijective on arrows with a given target -/

variable {D : Type w} [Category.{w} D] {Φ : D ⥤ C}
  (hΦ : ∀ y : D, Function.Bijective (Φ.toPrefunctor.costar y))
include hΦ

omit [IsGroupoid C]

/-- A cutoff pulls back to a cutoff along a functor bijective on the arrows with a given
target. -/
theorem finsum_costar_comp_eq_one (y : D) : ∑ᶠ b : Quiver.Costar y, (c ∘ Φ.obj) b.1 = 1 :=
  (finsum_comp (g := fun b : Quiver.Costar (Φ.obj y) ↦ c b.1) _ (hΦ y)).trans (hc _)

omit hc hΦ in
/-- Pulling back cochains along the functor `Φ` evaluates them on the images of strings. -/
theorem valuesEquiv_cochainComplexMap (n : ℕ) (φ : (nerveCochainComplex C k M).X n)
    (σ : ComposableArrows D n) :
    valuesEquiv n ((SSet.cochainComplexMap (R := ModuleCat.of k k) (k := k) (M := M)
        (nerveMap Φ)).f n φ) σ = valuesEquiv n φ ((Φ.mapComposableArrows n).obj σ) :=
  by simp only [valuesEquiv_apply]
     exact cochainValuesEquiv_chainComplexMap k M (nerve D) (nerveMap Φ) n φ σ

omit hc in
/-- Prepending arrows weighted by the pulled-back cutoff commutes with evaluating on images of
strings under `Φ`. -/
theorem cutoffPrepend_comp_mapComposableArrows (n : ℕ) (φ : ComposableArrows C (n + 1) → M)
    (σ : ComposableArrows D n) :
    cutoffPrepend (c ∘ Φ.obj) n (φ ∘ (Φ.mapComposableArrows (n + 1)).obj) σ =
      cutoffPrepend c n φ ((Φ.mapComposableArrows n).obj σ) := by
  unfold cutoffPrepend
  refine Eq.trans (finsum_congr fun b ↦ ?_) (finsum_comp
    (g := fun b : Quiver.Costar (Φ.obj σ.left) ↦
      c b.1 • φ (((Φ.mapComposableArrows n).obj σ).precomp b.2)) _ (hΦ σ.left))
  simp only [Function.comp_apply, Functor.mapComposableArrows_obj_precomp]
  rfl

/-- **Restriction law.** Pulling back cochains along a functor bijective on the arrows with a
given target commutes with prepending arrows, weighted by the cutoff and by its pullback. -/
theorem cochainComplexMap_f_comp_cutoffPrependHom (n : ℕ) :
    (SSet.cochainComplexMap (R := ModuleCat.of k k) (k := k) (M := M) (nerveMap Φ)).f (n + 1) ≫
        cutoffPrependHom M (finsum_costar_comp_eq_one hc hΦ) n =
      cutoffPrependHom M hc n ≫
        (SSet.cochainComplexMap (R := ModuleCat.of k k) (k := k) (M := M) (nerveMap Φ)).f n := by
  ext φ : 2
  apply (valuesEquiv n).injective
  funext σ
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    valuesEquiv_cutoffPrependHom, valuesEquiv_cochainComplexMap, valuesEquiv_cutoffPrependHom,
    ← cutoffPrepend_comp_mapComposableArrows hΦ]
  congr 1
  funext τ
  exact valuesEquiv_cochainComplexMap (n + 1) φ τ

end Restriction

end nerveCochainComplex

end TauCeti
