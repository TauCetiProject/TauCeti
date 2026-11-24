/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Bilinear
public import TauCeti.Analysis.Normed.Operator.Restrict
public import TauCeti.Analysis.Normed.Operator.Compact.Pi
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.Sobolev.Wkp.Gluing

/-!
# Sobolev spaces as compatible families over a finite open cover

Let `V i` be a family of open sets in `Ω`. A family `w i ∈ W^{k,p}(V i)` is *compatible* if `w i`
and `w j` have the same restriction to `V i ⊓ V j` for all `i` and `j`. The compatible families
form a closed subspace `TauCeti.Wkp.compatibleFamilies` of the product `∏ᵢ W^{k,p}(V i)`, so they
form a Banach space.

When the family is finite and covers `Ω`, restriction to the members of the cover is a continuous
linear equivalence `TauCeti.Wkp.restrictCompatibleEquiv` from `W^{k,p}(Ω)` onto the compatible
families, for every order `k` and every `1 ≤ p ≤ ∞`, with no boundary regularity assumed. With
the sup norm on the product, the equivalence has norm at most one and its inverse has norm at most
the number of sets in the cover. In other words, the finite-cover norm `∑ᵢ ‖u|_{V i}‖` is
equivalent to the Sobolev norm on `Ω` (`TauCeti.Wkp.norm_le_sum_norm_restrictL`), which is the
local form of the equivalence of finite-chart norms on a compact manifold. In particular, a map
into `W^{k,p}(Ω)` is a compact operator as soon as its restrictions to the members of a finite
open cover are (`TauCeti.Wkp.isCompactOperator_of_restrictL`).

Injectivity is `TauCeti.Wkp.ext_of_restrictL_eq`; surjectivity and the bound on the inverse come
from the gluing theorem `TauCeti.Wkp.exists_glue_of_restrictL_eq`.

## Main results

* `TauCeti.Wkp.compatibleFamilies`: the closed subspace of compatible families.
* `TauCeti.Wkp.restrictCompatibleL`: restriction to the members of a cover, as a continuous
  linear map into the compatible families.
* `TauCeti.Wkp.norm_le_sum_norm_restrictL`: `‖u‖ ≤ ∑ᵢ ‖u|_{V i}‖` for a finite open cover, and
  `TauCeti.Wkp.norm_le_norm_restrictL_add_norm_restrictL` for a cover by two open sets.
* `TauCeti.Wkp.restrictCompatibleEquiv`: `W^{k,p}(Ω) ≃L[ℝ]` compatible families over a finite
  open cover.
* `TauCeti.Wkp.isCompactOperator_of_restrictL`: compactness of maps into `W^{k,p}(Ω)` is local on
  a finite open cover.
* `TauCeti.Wkp.exists_continuousLinearMap_value_ae_eq`: continuous linear maps into the members
  of a finite open cover with almost everywhere matching values glue to one into `W^{k,p}(Ω)`.
* `TauCeti.Wkp.exists_continuousBilinearMap_value_ae_eq`: continuous bilinear maps into the members
  of a finite open cover, agreeing almost everywhere with one function, glue to a continuous
  bilinear map into `W^{k,p}(Ω)`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, §9.
* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*}

variable (mu p) in
/-- The families `w i ∈ W^{k,p}(V i)` such that `w i` and `w j` have the same restriction to
`V i ⊓ V j` for all `i` and `j`. -/
def compatibleFamilies (V : ι → Opens E) (k : ℕ) :
    Submodule ℝ (∀ i, Wkp mu (V i) p k) where
  carrier := {w | ∀ i j, restrictL (inf_le_left : V i ⊓ V j ≤ V i) k (w i) =
    restrictL (inf_le_right : V i ⊓ V j ≤ V j) k (w j)}
  add_mem' {w w'} hw hw' i j := by
    simp only [Pi.add_apply, map_add, hw i j, hw' i j]
  zero_mem' i j := by simp only [Pi.zero_apply, map_zero]
  smul_mem' c w hw i j := by
    simp only [Pi.smul_apply, map_smul, hw i j]

@[simp]
theorem mem_compatibleFamilies {V : ι → Opens E} {k : ℕ} {w : ∀ i, Wkp mu (V i) p k} :
    w ∈ compatibleFamilies mu p V k ↔ ∀ i j,
      restrictL (inf_le_left : V i ⊓ V j ≤ V i) k (w i) =
        restrictL (inf_le_right : V i ⊓ V j ≤ V j) k (w j) :=
  Iff.rfl

/-- The compatible families form a closed subspace of the product. -/
theorem isClosed_compatibleFamilies (V : ι → Opens E) (k : ℕ) :
    IsClosed (compatibleFamilies mu p V k : Set (∀ i, Wkp mu (V i) p k)) := by
  have : (compatibleFamilies mu p V k : Set (∀ i, Wkp mu (V i) p k)) =
      ⋂ i, ⋂ j, {w | restrictL (inf_le_left : V i ⊓ V j ≤ V i) k (w i) =
        restrictL (inf_le_right : V i ⊓ V j ≤ V j) k (w j)} := by
    ext w
    simp only [SetLike.mem_coe, mem_compatibleFamilies, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq ((restrictL _ k).continuous.comp (continuous_apply i))
      ((restrictL _ k).continuous.comp (continuous_apply j))

/-- The compatible families form a complete space. -/
instance compatibleFamilies.instCompleteSpace (V : ι → Opens E) (k : ℕ) :
    CompleteSpace (compatibleFamilies mu p V k) :=
  (isClosed_compatibleFamilies V k).completeSpace_coe

/-- The restrictions of one Sobolev function on `Ω` to open subsets of `Ω` form a compatible
family. -/
theorem restrictL_mem_compatibleFamilies {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega) (k : ℕ)
    (u : Wkp mu Omega p k) :
    (fun i => restrictL (hle i) k u) ∈ compatibleFamilies mu p V k := fun i j => by
  simp only [restrictL_restrictL]

/-- Restriction of a Sobolev function on `Ω` to the members of a family of open subsets of `Ω`,
as a continuous linear map into the compatible families. -/
def restrictCompatibleL {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega) (k : ℕ) :
    Wkp mu Omega p k →L[ℝ] compatibleFamilies mu p V k :=
  (ContinuousLinearMap.pi fun i => restrictL (hle i) k).codRestrict _
    (restrictL_mem_compatibleFamilies hle k)

/-- The `i`-th member of the family `restrictCompatibleL u` is the restriction of `u` to `V i`. -/
@[simp]
theorem restrictCompatibleL_apply_coe {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega) (k : ℕ)
    (u : Wkp mu Omega p k) (i : ι) :
    (restrictCompatibleL hle k u : ∀ i, Wkp mu (V i) p k) i = restrictL (hle i) k u :=
  (rfl)

/-- Restriction to the members of an open cover is injective; the cover may be infinite. -/
theorem restrictCompatibleL_injective {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) :
    Function.Injective (restrictCompatibleL (mu := mu) (p := p) hle k) := fun _ _ h =>
  ext_of_restrictL_eq hle hcov k fun i => congrFun (congrArg Subtype.val h) i

/-- Every compatible family over a finite open cover is the family of restrictions of a Sobolev
function on `Ω`. -/
theorem restrictCompatibleL_surjective [Finite ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) :
    Function.Surjective (restrictCompatibleL (mu := mu) (p := p) hle k) := fun ⟨w, hw⟩ => by
  have := Fintype.ofFinite ι
  obtain ⟨v, hv, -⟩ := exists_glue_of_restrictL_eq hle hcov k w hw
  exact ⟨v, Subtype.ext (funext hv)⟩

/-- **The finite-cover norm bounds the Sobolev norm.** If finitely many open sets `V i ⊆ Ω` cover
`Ω`, then `‖u‖ ≤ ∑ᵢ ‖u|_{V i}‖` for every `u ∈ W^{k,p}(Ω)`. Together with `norm_restrictL_le`,
the finite-cover norm is equivalent to the Sobolev norm. -/
theorem norm_le_sum_norm_restrictL [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (u : Wkp mu Omega p k) :
    ‖u‖ ≤ ∑ i, ‖restrictL (hle i) k u‖ := by
  obtain ⟨v, hv, hvn⟩ := exists_glue_of_restrictL_eq hle hcov k (fun i => restrictL (hle i) k u)
    (restrictL_mem_compatibleFamilies hle k u)
  rwa [ext_of_restrictL_eq hle hcov k hv] at hvn

/-- The case of `norm_le_sum_norm_restrictL` for a cover of `Ω` by two open sets `U` and `U'`:
`‖u‖ ≤ ‖u|_U‖ + ‖u|_{U'}‖`. -/
theorem norm_le_norm_restrictL_add_norm_restrictL {U U' : Opens E} (hU : U ≤ Omega)
    (hU' : U' ≤ Omega) (hcov : Omega ≤ U ⊔ U') (k : ℕ) (u : Wkp mu Omega p k) :
    ‖u‖ ≤ ‖restrictL hU k u‖ + ‖restrictL hU' k u‖ := by
  exact (norm_le_sum_norm_restrictL (V := fun b ↦ cond b U U') (Bool.forall_bool.2 ⟨hU', hU⟩)
    (hcov.trans (sup_le (le_iSup_of_le true le_rfl) (le_iSup_of_le false le_rfl))) k u).trans_eq
      (Fintype.sum_bool _)

/-- Restriction to the members of a family of open subsets does not increase the norm, for the
sup norm on the product. -/
theorem norm_restrictCompatibleL_le [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega) (k : ℕ)
    (u : Wkp mu Omega p k) : ‖restrictCompatibleL hle k u‖ ≤ ‖u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg u)).2 fun i => norm_restrictL_le (hle i) k u

/-- Over a cover by `n` open sets, the Sobolev norm is at most `n` times the sup norm of the
restrictions. -/
theorem norm_le_card_mul_norm_restrictCompatibleL [Fintype ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (u : Wkp mu Omega p k) :
    ‖u‖ ≤ Fintype.card ι * ‖restrictCompatibleL hle k u‖ :=
  (norm_le_sum_norm_restrictL hle hcov k u).trans <| by
    rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ =>
      norm_le_pi_norm (restrictCompatibleL hle k u : ∀ i, Wkp mu (V i) p k) i

/-- **Sobolev functions are compatible families over a finite open cover.** If finitely many open
sets `V i ⊆ Ω` cover `Ω`, then restriction to the `V i` is a continuous linear equivalence from
`W^{k,p}(Ω)` onto the compatible families in `∏ᵢ W^{k,p}(V i)`. The bounds are
`norm_restrictCompatibleEquiv_le` and `norm_restrictCompatibleEquiv_symm_le`. -/
def restrictCompatibleEquiv [Fintype ι] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) :
    Wkp mu Omega p k ≃L[ℝ] compatibleFamilies mu p V k :=
  let e := LinearEquiv.ofBijective (restrictCompatibleL hle k).toLinearMap
    ⟨restrictCompatibleL_injective hle hcov k, restrictCompatibleL_surjective hle hcov k⟩
  e.toContinuousLinearEquivOfBounds 1 (Fintype.card ι)
    (fun u => by rw [one_mul]; exact norm_restrictCompatibleL_le hle k u)
    (fun w => by
      have he : ∀ u, e u = restrictCompatibleL hle k u := fun _ => LinearEquiv.ofBijective_apply ..
      have h := norm_le_card_mul_norm_restrictCompatibleL hle hcov k (e.symm w)
      rwa [← he, e.apply_symm_apply] at h)

/-- The equivalence `restrictCompatibleEquiv` is the restriction map `restrictCompatibleL`. -/
theorem restrictCompatibleEquiv_apply [Fintype ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (u : Wkp mu Omega p k) :
    restrictCompatibleEquiv hle hcov k u = restrictCompatibleL hle k u :=
  (rfl)

/-- The `i`-th member of the family `restrictCompatibleEquiv u` is the restriction of `u` to
`V i`. -/
@[simp]
theorem restrictCompatibleEquiv_apply_coe [Fintype ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (u : Wkp mu Omega p k) (i : ι) :
    (restrictCompatibleEquiv hle hcov k u : ∀ i, Wkp mu (V i) p k) i = restrictL (hle i) k u :=
  (rfl)

/-- The inverse of `restrictCompatibleEquiv` glues a compatible family: the glued function
restricts to each member of the family. -/
@[simp]
theorem restrictL_restrictCompatibleEquiv_symm [Fintype ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) (k : ℕ)
    (w : compatibleFamilies mu p V k) (i : ι) :
    restrictL (hle i) k ((restrictCompatibleEquiv hle hcov k).symm w) =
      (w : ∀ i, Wkp mu (V i) p k) i := by
  rw [← restrictCompatibleEquiv_apply_coe hle hcov k, ContinuousLinearEquiv.apply_symm_apply]

/-- Restriction to the members of a cover does not increase the norm, for the sup norm on the
product. -/
theorem norm_restrictCompatibleEquiv_le [Fintype ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) (k : ℕ) (u : Wkp mu Omega p k) :
    ‖restrictCompatibleEquiv hle hcov k u‖ ≤ ‖u‖ :=
  norm_restrictCompatibleL_le hle k u

/-- The function glued from a compatible family has norm at most the sum of the norms of the
members of the family. -/
theorem norm_restrictCompatibleEquiv_symm_le_sum [Fintype ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) (k : ℕ)
    (w : compatibleFamilies mu p V k) :
    ‖(restrictCompatibleEquiv hle hcov k).symm w‖ ≤ ∑ i, ‖(w : ∀ i, Wkp mu (V i) p k) i‖ := by
  simpa only [restrictL_restrictCompatibleEquiv_symm] using
    norm_le_sum_norm_restrictL hle hcov k ((restrictCompatibleEquiv hle hcov k).symm w)

/-- The function glued from a compatible family over a cover by `n` sets has norm at most `n`
times the sup norm of the family. -/
theorem norm_restrictCompatibleEquiv_symm_le [Fintype ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) (k : ℕ)
    (w : compatibleFamilies mu p V k) :
    ‖(restrictCompatibleEquiv hle hcov k).symm w‖ ≤ Fintype.card ι * ‖w‖ := by
  have h := norm_le_card_mul_norm_restrictCompatibleL hle hcov k
    ((restrictCompatibleEquiv hle hcov k).symm w)
  rwa [← restrictCompatibleEquiv_apply hle hcov, ContinuousLinearEquiv.apply_symm_apply] at h

/-- **Compactness is local on a finite open cover.** If finitely many open sets `V i ⊆ Ω` cover
`Ω`, a map into `W^{k,p}(Ω)` is a compact operator as soon as its restrictions to all `V i` are. -/
theorem isCompactOperator_of_restrictL [Finite ι] {X : Type*} [TopologicalSpace X]
    [AddCommMonoid X] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) {k : ℕ} {f : X → Wkp mu Omega p k}
    (hf : ∀ i, IsCompactOperator fun x ↦ restrictL (hle i) k (f x)) : IsCompactOperator f := by
  have := Fintype.ofFinite ι
  have h := ((IsCompactOperator.pi hf).codRestrict
    (fun x ↦ restrictL_mem_compatibleFamilies hle k (f x))
    (isClosed_compatibleFamilies V k)).clm_comp
      (restrictCompatibleEquiv hle hcov k).symm.toContinuousLinearMap
  convert h using 1
  funext x
  rw [Function.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.eq_symm_apply]
  exact Subtype.ext (funext fun i ↦ restrictCompatibleEquiv_apply_coe hle hcov k (f x) i)


private theorem mem_compatibleFamilies_of_value_ae_eq {V : ι → Opens E} {k : ℕ}
    (w : ∀ i, Wkp mu (V i) p k) (g : E → ℝ)
    (hw : ∀ i, (value k (w i) : E → ℝ) =ᵐ[mu.restrict (V i)] g) :
    w ∈ compatibleFamilies mu p V k := fun i j ↦ by
  have hi : (value k (w i) : E → ℝ) =ᵐ[mu.restrict (V i ⊓ V j : Opens E)] g :=
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 inf_le_left) (hw i)
  have hj : (value k (w j) : E → ℝ) =ᵐ[mu.restrict (V i ⊓ V j : Opens E)] g :=
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 inf_le_right) (hw j)
  exact Wkp.ext k (Lp.ext ((value_restrictL_ae inf_le_left k (w i)).trans <|
    hi.trans <| hj.symm.trans (value_restrictL_ae inf_le_right k (w j)).symm))

private theorem value_ae_eq_of_restrictL [Countable ι] {V : ι → Opens E}
    (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) {k : ℕ}
    (w : Wkp mu Omega p k) (g : E → ℝ)
    (hw : ∀ i, (value k (restrictL (hle i) k w) : E → ℝ) =ᵐ[mu.restrict (V i)] g) :
    (value k w : E → ℝ) =ᵐ[mu.restrict Omega] g := by
  have hV (i : ι) : (value k w : E → ℝ) =ᵐ[mu.restrict (V i)] g :=
    (value_restrictL_ae (hle i) k w).symm.trans (hw i)
  have hsub : (Omega : Set E) ⊆ ⋃ i, (V i : Set E) := by
    simpa only [Opens.coe_iSup] using SetLike.coe_subset_coe.2 hcov
  exact ae_restrict_of_ae_restrict_of_subset hsub ((ae_restrict_iUnion_iff _ _).2 hV)

/-- **Continuous linear maps into `W^{k,p}(Ω)` glue over a finite open cover.** Let finitely many
open sets `V i ⊆ Ω` cover `Ω`, and let `f i : X → W^{k,p}(V i)` be continuous linear maps whose
values agree, almost everywhere on `V i`, with a function `g x` independent of `i`. Then there is a
continuous linear map `F : X → W^{k,p}(Ω)` whose values equal `g x` almost everywhere on `Ω`. -/
theorem exists_continuousLinearMap_value_ae_eq [Finite ι] {X : Type*} [TopologicalSpace X]
    [AddCommMonoid X] [Module ℝ X] {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega)
    (hcov : Omega ≤ ⨆ i, V i) {k : ℕ} (f : ∀ i, X →L[ℝ] Wkp mu (V i) p k) (g : X → E → ℝ)
    (hf : ∀ i x, (value k (f i x) : E → ℝ) =ᵐ[mu.restrict (V i)] g x) :
    ∃ F : X →L[ℝ] Wkp mu Omega p k, ∀ x, (value k (F x) : E → ℝ) =ᵐ[mu.restrict Omega] g x := by
  have := Fintype.ofFinite ι
  have hcomp (x : X) : (fun i ↦ f i x) ∈ compatibleFamilies mu p V k :=
    mem_compatibleFamilies_of_value_ae_eq _ (g x) (fun i ↦ hf i x)
  refine ⟨(restrictCompatibleEquiv hle hcov k).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi f).codRestrict _ hcomp), fun x ↦ ?_⟩
  apply value_ae_eq_of_restrictL hle hcov _ (g x)
  intro i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [restrictL_restrictCompatibleEquiv_symm]
  exact hf i x

/-- Continuous bilinear maps into `W^{k,p}` glue over a finite open cover when their values agree
almost everywhere with one function. The resulting map is bounded in both inputs jointly. -/
theorem exists_continuousBilinearMap_value_ae_eq [Finite ι] {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {V : ι → Opens E} (hle : ∀ i, V i ≤ Omega) (hcov : Omega ≤ ⨆ i, V i) {k : ℕ}
    (f : ∀ i, X →L[ℝ] Y →L[ℝ] Wkp mu (V i) p k) (g : X → Y → E → ℝ)
    (hf : ∀ i x y, (value k (f i x y) : E → ℝ) =ᵐ[mu.restrict (V i)] g x y) :
    ∃ F : X →L[ℝ] Y →L[ℝ] Wkp mu Omega p k,
      ∀ x y, (value k (F x y) : E → ℝ) =ᵐ[mu.restrict Omega] g x y := by
  have := Fintype.ofFinite ι
  have hcomp (x : X) (y : Y) : (fun i ↦ f i x y) ∈ compatibleFamilies mu p V k :=
    mem_compatibleFamilies_of_value_ae_eq _ (g x y) (fun i ↦ hf i x y)
  let B := (ContinuousLinearMap.piBilin f).codRestrictBilin
    (compatibleFamilies mu p V k) (fun x y ↦ by
      convert hcomp x y using 1
      exact funext fun i ↦ ContinuousLinearMap.piBilin_apply f x y i)
  have hB (x : X) (y : Y) : B x y = ⟨fun i ↦ f i x y, hcomp x y⟩ := by
    apply Subtype.ext
    funext i
    simp only [B, ContinuousLinearMap.coe_codRestrictBilin_apply,
      ContinuousLinearMap.piBilin_apply]
  let L : compatibleFamilies mu p V k →L[ℝ] Wkp mu Omega p k :=
    (restrictCompatibleEquiv hle hcov k).symm.toContinuousLinearMap
  refine ⟨((ContinuousLinearMap.compL ℝ Y _ _) L).comp B, fun x y ↦ ?_⟩
  apply value_ae_eq_of_restrictL hle hcov _ (g x y)
  intro i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  dsimp only [L]
  simp only [ContinuousLinearEquiv.coe_coe]
  rw [hB, restrictL_restrictCompatibleEquiv_symm]
  exact hf i x y

end TauCeti.Wkp
