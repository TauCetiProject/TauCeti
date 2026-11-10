/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.BigOperators
public import TauCeti.Algebra.Homology.CochainComplex.OfDegreeZero
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.CategoryTheory.Category.QuiverTotal
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod

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
constant along arrows, is fixed by `P`. The homotopy and the primitives are assembled from the two
identities by `CochainComplex.homotopyOfDCompEq` and `CochainComplex.d_hom_apply_of_d_comp_eq`.
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
is the sum, over the arrows `b : y ⟶ x`, of `c y` times the value at `y`. It prepends an arrow
weighted by `c` to the function on single arrows given by the value at their source. -/
def cutoffAverage (φ : ComposableArrows C 0 → M) : ComposableArrows C 0 → M :=
  cutoffPrepend c 0 (φ ∘ fun τ ↦ ComposableArrows.mk₀ τ.left)

/-- The value of `TauCeti.nerveCochainComplex.cutoffPrepend` at a string `σ` is the sum, over the
arrows `b` into its first vertex, of `c` at the source of `b` times the value at `σ` with `b`
prepended. -/
theorem cutoffPrepend_apply (n : ℕ) (φ : ComposableArrows C (n + 1) → M)
    (σ : ComposableArrows C n) :
    cutoffPrepend c n φ σ = ∑ᶠ b : Quiver.Costar σ.left, c b.1 • φ (σ.precomp b.2) := by
  rfl

/-- The value of `TauCeti.nerveCochainComplex.cutoffAverage` at an object `σ.left` is the sum,
over the arrows `b` into it, of `c` at the source of `b` times the value at that source. -/
theorem cutoffAverage_apply (φ : ComposableArrows C 0 → M) (σ : ComposableArrows C 0) :
    cutoffAverage c φ σ = ∑ᶠ b : Quiver.Costar σ.left, c b.1 • φ (ComposableArrows.mk₀ b.1) := by
  rfl

variable {c}

variable (hc : ∀ x : C, ∑ᶠ b : Quiver.Costar x, c b.1 = 1)
include hc

/-- Prepending arrows weighted by a cutoff is additive. -/
theorem cutoffPrepend_add (n : ℕ) (φ ψ : ComposableArrows C (n + 1) → M) :
    cutoffPrepend c n (φ + ψ) = cutoffPrepend c n φ + cutoffPrepend c n ψ := by
  funext σ
  have hfin : Function.HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc σ.left)
  simp only [cutoffPrepend, Pi.add_apply, smul_add]
  exact finsum_add_distrib (hfin.fun_smul_left _) (hfin.fun_smul_left _)

/-- Prepending arrows weighted by a cutoff commutes with scalar multiplication. -/
theorem cutoffPrepend_smul (n : ℕ) (a : k) (φ : ComposableArrows C (n + 1) → M) :
    cutoffPrepend c n (a • φ) = a • cutoffPrepend c n φ := by
  funext σ
  have hfin : Function.HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc σ.left)
  simp only [cutoffPrepend, Pi.smul_apply, smul_comm _ a]
  exact (smul_finsum' a (hfin.fun_smul_left _)).symm

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
    valuesEquiv n (cutoffPrependHom M hc n φ) = cutoffPrepend c n (valuesEquiv (n + 1) φ) :=
  -- By definition, `cutoffPrependHom` conjugates `cutoffPrepend` by the value coordinates.
  (valuesEquiv n).apply_symm_apply _

variable (M) in
/-- The cutoff average `TauCeti.nerveCochainComplex.cutoffAverage` on cochains of degree `0`. -/
def cutoffAverageHom : (nerveCochainComplex C k M).X 0 ⟶ (nerveCochainComplex C k M).X 0 :=
  ModuleCat.ofHom <| (valuesEquiv 0).symm.toLinearMap ∘ₗ
    { toFun := cutoffAverage c
      map_add' _ _ := cutoffPrepend_add hc 0 _ _
      map_smul' a _ := cutoffPrepend_smul hc 0 a _ } ∘ₗ (valuesEquiv 0).toLinearMap

/-- In values, `TauCeti.nerveCochainComplex.cutoffAverageHom` is
`TauCeti.nerveCochainComplex.cutoffAverage`. -/
@[simp]
theorem valuesEquiv_cutoffAverageHom (φ : (nerveCochainComplex C k M).X 0) :
    valuesEquiv 0 (cutoffAverageHom M hc φ) = cutoffAverage c (valuesEquiv 0 φ) :=
  -- By definition, `cutoffAverageHom` conjugates `cutoffAverage` by the value coordinates.
  (valuesEquiv 0).apply_symm_apply _

/-- **Contraction in degree `0`.** Prepending to the coboundary of a function on objects
gives the function minus its cutoff average. -/
theorem cutoffPrepend_d_zero (φ : (nerveCochainComplex C k M).X 0) (σ : ComposableArrows C 0) :
    cutoffPrepend c 0 (valuesEquiv 1 ((nerveCochainComplex C k M).d 0 1 φ)) σ =
      valuesEquiv 0 φ σ - cutoffAverage c (valuesEquiv 0 φ) σ := by
  have hfin : Function.HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc σ.left)
  have h₁ (b : Quiver.Costar σ.left) :
      (nerve C).δ (Fin.succ 0) (σ.precomp b.2) =
        ComposableArrows.mk₀ (σ.precomp b.2).left :=
    ComposableArrows.ext₀ rfl
  unfold cutoffAverage cutoffPrepend
  rw [finsum_smul_eq_sum hfin, finsum_smul_eq_sum hfin]
  simp only [valuesEquiv_d, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, zero_add, pow_one, one_smul, neg_smul, add_zero, nerve.δ₀_eq,
    ComposableArrows.precomp_δ₀, h₁, Function.comp_apply, smul_add, smul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [← Finset.sum_smul, ← finsum_eq_sum _ hfin, hc, one_smul, sub_eq_add_neg]

variable [IsGroupoid C]

/-- **Contraction in positive degrees.** For a cochain `φ` of degree `n + 1`, prepending to its
coboundary plus the coboundary of the prepended cochain is `φ`. -/
theorem cutoffPrepend_d_add_d_cutoffPrepend (n : ℕ) (φ : (nerveCochainComplex C k M).X (n + 1))
    (σ : ComposableArrows C (n + 1)) :
    cutoffPrepend c (n + 1) (valuesEquiv (n + 2) ((nerveCochainComplex C k M).d (n + 1) (n + 2) φ))
        σ +
      valuesEquiv (n + 1) ((nerveCochainComplex C k M).d n (n + 1) (cutoffPrependHom M hc n φ)) σ =
      valuesEquiv (n + 1) φ σ := by
  have hfin : Function.HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc σ.left)
  -- Reindex the sums over the arrows into the first vertex of each face by the arrows into the
  -- first vertex of `σ`, and identify the strings with the faces of the prepended strings.
  have hface (j : Fin (n + 2)) :
      cutoffPrepend c n (valuesEquiv (n + 1) φ) ((nerve C).δ j σ) =
        ∑ b ∈ hfin.toFinset,
          c b.1 • valuesEquiv (n + 1) φ ((nerve C).δ j.succ (σ.precomp b.2)) := by
    unfold cutoffPrepend
    rw [← finsum_smul_eq_sum hfin]
    -- Postcomposing with the arrow from `x₀` to the first vertex of the face identifies the
    -- arrows into `x₀` with the arrows into that vertex.
    let e : σ.left ≅ σ.obj (j.succAbove 0) := asIso (σ.map (homOfLE (Fin.zero_le _)))
    refine (finsum_comp_equiv (Equiv.sigmaCongrRight fun _ ↦ e.homToEquiv)).symm.trans
      (finsum_congr fun b ↦ ?_)
    rw [nerve.δ_succ_precomp]
    -- `e.homToEquiv b.2` is `b.2 ≫ e.hom` and `e.hom` is `σ.map _` by definition of `asIso`;
    -- the arrow's type depends on `b.1`, so `simp` cannot rewrite inside `Equiv.sigmaCongrRight`.
    rfl
  rw [valuesEquiv_d]
  simp only [valuesEquiv_cutoffPrependHom, hface]
  unfold cutoffPrepend
  rw [finsum_smul_eq_sum hfin]
  -- Split off the face deleting the prepended vertex; the other faces cancel the second sum.
  simp only [valuesEquiv_d, Fin.sum_univ_succ (n := n + 2), nerve.δ₀_eq,
    ComposableArrows.precomp_δ₀, Fin.val_zero, pow_zero,
    one_smul, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, smul_add,
    smul_neg, Finset.smul_sum, Finset.sum_add_distrib, smul_comm (c _) ((-1 : ℤ) ^ _)]
  rw [Finset.sum_comm (s := hfin.toFinset), ← Finset.sum_smul, ← finsum_eq_sum _ hfin, hc,
    one_smul]
  abel

/-- **Contraction in positive degrees**, as an identity of maps of cochains. -/
theorem d_comp_cutoffPrependHom_add (n : ℕ) :
    (nerveCochainComplex C k M).d (n + 1) (n + 2) ≫ cutoffPrependHom M hc (n + 1) +
      cutoffPrependHom M hc n ≫ (nerveCochainComplex C k M).d n (n + 1) = 𝟙 _ := by
  ext φ : 2
  apply (valuesEquiv (n + 1)).injective
  funext σ
  -- `simp` does not normalize these composites in `ModuleCat` (it leaves `(f ≫ g).hom` unfolded
  -- against `ConcreteCategory.hom`), so the structure lemmas are applied by hand.
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
    cutoffAverageHom M hc ≫ (nerveCochainComplex C k M).d 0 1 = 0 :=
  CochainComplex.comp_d_zero_eq_zero_of_d_comp_eq (d_comp_cutoffPrependHom_add hc)
    (d_comp_cutoffPrependHom_zero hc)

/-- The cutoff average, placed in degree `0`, as an endomorphism of the cochain complex: it is
`TauCeti.nerveCochainComplex.cutoffAverageHom` on cochains of degree `0` and zero in positive
degrees. -/
def cutoffCochainMap : nerveCochainComplex C k M ⟶ nerveCochainComplex C k M :=
  (nerveCochainComplex C k M).ofDegreeZero (cutoffAverageHom M hc) (cutoffAverageHom_comp_d hc)

/-- In degree `0`, `TauCeti.nerveCochainComplex.cutoffCochainMap` is the cutoff average. -/
@[simp]
theorem cutoffCochainMap_f_zero : (cutoffCochainMap (M := M) hc).f 0 = cutoffAverageHom M hc :=
  CochainComplex.ofDegreeZero_f_zero _

/-- In positive degrees, `TauCeti.nerveCochainComplex.cutoffCochainMap` is zero. -/
@[simp]
theorem cutoffCochainMap_f_succ (n : ℕ) : (cutoffCochainMap (M := M) hc).f (n + 1) = 0 :=
  CochainComplex.ofDegreeZero_f_succ _ n

/-- **The cutoff contraction.** The identity of the cochain complex of the nerve is homotopic to
the cutoff average placed in degree `0`, through the homotopy whose component from degree `n + 1`
to degree `n` prepends an arrow weighted by `c`
(`TauCeti.nerveCochainComplex.cutoffHomotopy_hom_succ`). -/
def cutoffHomotopy : Homotopy (𝟙 (nerveCochainComplex C k M)) (cutoffCochainMap hc) :=
  CochainComplex.homotopyOfDCompEq (d_comp_cutoffPrependHom_add hc)
    (d_comp_cutoffPrependHom_zero hc)

/-- The component of `TauCeti.nerveCochainComplex.cutoffHomotopy` from degree `n + 1` to degree
`n` is `TauCeti.nerveCochainComplex.cutoffPrependHom`. -/
@[simp]
theorem cutoffHomotopy_hom_succ (n : ℕ) :
    (cutoffHomotopy (M := M) hc).hom (n + 1) n = cutoffPrependHom M hc n :=
  CochainComplex.homotopyOfDCompEq_hom_succ (d_comp_cutoffPrependHom_add hc)
    (d_comp_cutoffPrependHom_zero hc) n

/-- **The explicit primitive of a positive-degree cocycle**: prepending an arrow weighted by `c`
to a cocycle of degree `n + 1` gives a cochain whose coboundary is the cocycle. -/
theorem d_cutoffPrependHom_of_d_eq_zero {n : ℕ} {φ : (nerveCochainComplex C k M).X (n + 1)}
    (hφ : (nerveCochainComplex C k M).d (n + 1) (n + 2) φ = 0) :
    (nerveCochainComplex C k M).d n (n + 1) (cutoffPrependHom M hc n φ) = φ :=
  CochainComplex.d_hom_apply_of_d_comp_eq (d_comp_cutoffPrependHom_add hc n) hφ

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
  -- `Φ.toPrefunctor.costar` sends `⟨y, b⟩` to `⟨Φ.obj y, Φ.map b⟩` by definition.
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
