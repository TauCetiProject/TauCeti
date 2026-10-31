/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import TauCeti.RepresentationTheory.FunLeft
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The cutoff contraction of the cochains of an action presentation

Let a group `G` act on a type `X` and linearly on a `k`-module `A` through `ρ`, and let
`c : X → k` be a function whose translates sum to one, `∑ᶠ g, c (g • x) = 1` for every `x`. For a
proper action of a discrete group on a space, a cutoff function `TauCeti.MulAction.IsCutoff` is
such a function over `k = ℝ` (its field `finsum_smul_eq_one`). The group need not be finite, and
its action need not be faithful.

The inhomogeneous cochains of `G` with coefficients in the functions `X → A`
(`Representation.funLeft ρ X`) are the functions `Gⁿ × X → A`. A string of `n` composable arrows
of the action groupoid `G ⋉ X` is determined by its `n` labels and one of its points, so under this
identification of the `n`-simplices of the nerve of `G ⋉ X` with `Gⁿ × X`, these are the cochains
on the nerve of `G ⋉ X` with coefficients in the `G`-equivariant family `X × A`. This file
constructs an explicit contracting homotopy of this complex in positive degrees, by inserting a
last arrow weighted by `c`:
$$(hf)(g_1, \dots, g_n)(x) = \sum_{g \in G} c(g \cdot x)\,
  f\bigl(g_1, \dots, g_n, (g\, g_1 \cdots g_n)^{-1}\bigr)(x).$$
For each `x` only finitely many terms are nonzero. With the sign `(-1)^(n+1)` on the component of
degree `n + 1 → n`, the identity of the cochain complex is homotopic to the chain map that is the
cutoff average `Representation.cutoffAverage` in degree `0` and zero in positive degrees, the
projection onto the invariant functions placed in degree `0`. In particular every positive-degree
cocycle has an explicit primitive, and the positive-degree group cohomology with coefficients in
`X → A` vanishes.

For a finite group and the constant function `|G|⁻¹`, `h` averages over the inserted label, as in
`TauCeti.inhomogeneousCochains.averageLast`. The operator is natural for pullback along
equivariant maps `Y → X`, with the cutoff function pulled back to `Y`; restriction to an invariant
subset is the case of an inclusion.

## Main declarations

* `TauCeti.inhomogeneousCochains.cutoffLast`: the insertion of a last arrow weighted by `c`.
* `TauCeti.inhomogeneousCochains.d_comp_cutoffLast`: `h ∘ d = d ∘ h + (-1)^n` on
  `(n + 1)`-cochains.
* `TauCeti.inhomogeneousCochains.d_zero_comp_cutoffLast`: `h ∘ d = Q - 1` on `0`-cochains, where
  `Q` is the cutoff average.
* `TauCeti.inhomogeneousCochains.cutoffLast_hom_comp`: naturality for pullback along equivariant
  maps.
* `TauCeti.groupCohomology.cutoffHomotopy`: the homotopy from the identity of the cochain complex
  to `TauCeti.groupCohomology.cutoffCochainMap`, the cutoff average in degree `0`.
* `TauCeti.groupCohomology.subsingleton_funLeft_of_finsum_smul_eq_one`: positive-degree group
  cohomology with coefficients in `X → A` vanishes.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for the vanishing of the cohomology of
  proper groupoids by cutoff functions.
-/

public section

noncomputable section

universe u

open CategoryTheory Function

namespace TauCeti.inhomogeneousCochains

open _root_.inhomogeneousCochains

variable {k G A X : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A] [MulAction G X]
variable (ρ : Representation k G A) {c : X → k} (hc : ∀ x, ∑ᶠ g : G, c (g • x) = 1)

include hc in
/-- A sum weighted by the translates of `c` is a finite sum over the support of `c (· • x)`. -/
private theorem finsum_smul_eq_sum {V : Type*} [AddCommGroup V] [Module k V] (x : X)
    (v : G → V) :
    ∑ᶠ g : G, c (g • x) • v g =
      ∑ g ∈ (hasFiniteSupport_of_finsum_eq_one (hc x)).toFinset, c (g • x) • v g :=
  finsum_eq_sum_of_support_subset _ fun _ hg ↦
    (Set.Finite.mem_toFinset _).2 (support_smul_subset_left (fun g ↦ c (g • x)) v hg)

include hc in
private theorem sum_eq_one (x : X) :
    ∑ g ∈ (hasFiniteSupport_of_finsum_eq_one (hc x)).toFinset, c (g • x) = 1 :=
  (finsum_eq_sum _ _).symm.trans (hc x)

/-- Translating the point of a weighted sum translates the summation variable. -/
private theorem finsum_smul_inv_smul {V : Type*} [AddCommGroup V] [Module k V] (a : G) (x : X)
    (v : G → V) : ∑ᶠ g : G, c (g • a⁻¹ • x) • v g = ∑ᶠ g : G, c (g • x) • v (g * a) := by
  rw [← finsum_comp_equiv (Equiv.mulRight a)]
  simp [mul_smul]

private theorem partialProd_last_eq_mul_tail {n : ℕ} (y : Fin (n + 1) → G) :
    Fin.partialProd y (Fin.last (n + 1)) = y 0 * Fin.partialProd (fun i ↦ y i.succ) (Fin.last n) :=
  by rw [← Fin.succ_last, Fin.partialProd_succ']; rfl

private theorem partialProd_last_eq_init_mul {n : ℕ} (y : Fin (n + 1) → G) :
    Fin.partialProd y (Fin.last (n + 1)) =
      Fin.partialProd (Fin.init y) (Fin.last n) * y (Fin.last n) := by
  rw [← Fin.succ_last, Fin.partialProd_succ, Fin.partialProd_init]

private theorem apply_last_mul_inv_mul_partialProd_last {n : ℕ} (y : Fin (n + 1) → G) (g : G) :
    y (Fin.last n) * (g * Fin.partialProd y (Fin.last (n + 1)))⁻¹ =
      (g * Fin.partialProd (Fin.init y) (Fin.last n))⁻¹ := by
  rw [partialProd_last_eq_init_mul]
  group

private theorem partialProd_contractNth_castSucc {n : ℕ} (j : Fin n) (y : Fin (n + 1) → G) :
    Fin.partialProd (Fin.contractNth j.castSucc (· * ·) y) (Fin.last n) =
      Fin.partialProd y (Fin.last (n + 1)) := by
  rw [Fin.partialProd_contractNth, comp_apply, Fin.succAbove_of_le_castSucc, Fin.succ_last]
  simp [Fin.le_def]

/-- The insertion `x ↦ ∑ᶠ g, c (g • x) • f (y, (g * y₀ ⋯ yₙ₋₁)⁻¹) x` of a last arrow into an
`(n + 1)`-cochain `f` with coefficients in `X → A`, weighted by `c`, an `n`-cochain. -/
def cutoffLast (n : ℕ) :
    ModuleCat.of k ((Fin (n + 1) → G) → Rep.of (ρ.funLeft X)) ⟶
      ModuleCat.of k ((Fin n → G) → Rep.of (ρ.funLeft X)) :=
  ModuleCat.ofHom
  { toFun f y x := ∑ᶠ g : G, c (g • x) • f (Fin.snoc y (g * Fin.partialProd y (Fin.last n))⁻¹) x
    map_add' f f' := by
      ext y x
      simp only [finsum_smul_eq_sum hc]
      simp [smul_add, Finset.sum_add_distrib]
    map_smul' r f := by
      ext y x
      simp only [finsum_smul_eq_sum hc]
      simp [Finset.smul_sum, smul_comm r] }

/-- The value of the weighted insertion of a last arrow. -/
@[simp]
theorem cutoffLast_hom_apply (n : ℕ) (f : (Fin (n + 1) → G) → X → A) (y : Fin n → G) (x : X) :
    (cutoffLast ρ hc n).hom f y x =
      ∑ᶠ g : G, c (g • x) • f (Fin.snoc y (g * Fin.partialProd y (Fin.last n))⁻¹) x :=
  (rfl)

/-- **The weighted insertion of a last arrow is a homotopy relation with the differential.** On
`(n + 1)`-cochains, `h ∘ d = d ∘ h + (-1)^n`. -/
theorem d_comp_cutoffLast (n : ℕ) :
    d (Rep.of (ρ.funLeft X)) (n + 1) ≫ cutoffLast ρ hc (n + 1) =
      cutoffLast ρ hc n ≫ d (Rep.of (ρ.funLeft X)) n + (-1 : k) ^ n • 𝟙 _ := by
  ext f y x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.add_apply, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply, d_hom_apply,
    Pi.add_apply, Pi.smul_apply, Representation.funLeft_apply, Finset.sum_apply,
    cutoffLast_hom_apply ρ hc]
  have htail (g : G) : (fun i ↦ (Fin.snoc y g : Fin (n + 2) → G) i.succ) =
      Fin.snoc (fun i ↦ y i.succ) g :=
    Fin.tail_snoc y g
  -- Split off the last two faces of `d f`; the other contractions commute with appending the
  -- inserted arrow. Translate the point of the first face of `d (h f)` back to `x`, and rewrite
  -- the products of the strings in terms of the product of `y`.
  simp only [Fin.snoc_apply_zero, htail, Fin.sum_univ_castSucc (n := n + 1),
    Fin.sum_univ_castSucc (n := n), Fin.contractNth_castSucc_castSucc_snoc,
    Fin.contractNth_castSucc_last_snoc, Fin.contractNth_last, Fin.init_snoc,
    partialProd_contractNth_castSucc, apply_last_mul_inv_mul_partialProd_last,
    finsum_smul_inv_smul, mul_assoc, ← partialProd_last_eq_mul_tail, Fin.val_castSucc,
    Fin.val_last]
  -- Every sum is now weighted by `c (· • x)`: write them as finite sums over its support, and
  -- sum the constant last face against the weights.
  have hlast : ∑ g ∈ (hasFiniteSupport_of_finsum_eq_one (hc x)).toFinset,
      (-1 : k) ^ (n + 1 + 1) • c (g • x) • f y x = (-1 : k) ^ n • f y x := by
    rw [← Finset.smul_sum, ← Finset.sum_smul, sum_eq_one hc, one_smul, pow_succ, pow_succ,
      mul_assoc, neg_one_mul, neg_neg, mul_one]
  simp only [finsum_smul_eq_sum hc x]
  simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_comm _ ((-1 : k) ^ _), hlast, Finset.sum_comm (γ := G)]
  abel

/-- **The weighted insertion of a last arrow on a coboundary of degree one.** On `0`-cochains,
`h ∘ d` is the cutoff average minus the identity. -/
theorem d_zero_comp_cutoffLast :
    d (Rep.of (ρ.funLeft X)) 0 ≫ cutoffLast ρ hc 0 =
      ModuleCat.ofHom ((ρ.cutoffAverage hc).compLeft (Fin 0 → G)) - 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun y ↦ funext fun x ↦ ?_)
  have hy (z : Fin 0 → G) : z = y := Subsingleton.elim z y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sub, ModuleCat.hom_ofHom,
    ModuleCat.hom_id, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.compLeft_apply,
    Function.comp_apply, Pi.sub_apply, Representation.cutoffAverage_apply]
  simp only [cutoffLast_hom_apply ρ hc, d_hom_apply, Pi.add_apply, Pi.smul_apply,
    Representation.funLeft_apply, Finset.sum_apply, hy]
  have hsnoc (u : G) : (Fin.snoc y u : Fin 1 → G) 0 = u := Fin.snoc_last (α := fun _ ↦ G) u y
  have hprod : Fin.partialProd y (Fin.last 0) = 1 := Fin.partialProd_zero y
  have hsign : ∑ i : Fin 1, (-1 : k) ^ ((i : ℕ) + 1) = -1 := by simp
  simp only [hsnoc, hprod, mul_one, inv_inv]
  rw [finsum_smul_eq_sum hc, finsum_smul_eq_sum hc]
  simp only [hsign, neg_one_smul, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.sum_smul, sum_eq_one hc, one_smul, sub_eq_add_neg]

/-- **Naturality of the weighted insertion for pullback.** Pulling a cochain back along an
equivariant map `π : Y → X` commutes with the weighted insertion of a last arrow, for the
pulled-back weight `c ∘ π`. For the inclusion of an invariant subset this is restriction. -/
theorem cutoffLast_hom_comp {Y : Type u} [MulAction G Y] (π : Y →[G] X)
    (hc' : ∀ y, ∑ᶠ g : G, (c ∘ π) (g • y) = 1) (n : ℕ)
    (f : ModuleCat.of k ((Fin (n + 1) → G) → Rep.of (ρ.funLeft X))) :
    (cutoffLast ρ hc' n).hom (fun z ↦ f z ∘ π) = fun z ↦ (cutoffLast ρ hc n).hom f z ∘ π := by
  ext z y
  simp [cutoffLast_hom_apply ρ hc, cutoffLast_hom_apply ρ hc', map_smul]

/-- **The explicit primitive of a positive-degree cocycle.** An `(n + 1)`-cocycle `f` is the
coboundary of `(-1)^(n+1)` times its weighted insertion of a last arrow. -/
theorem d_smul_cutoffLast_of_d_eq_zero {n : ℕ}
    {f : ModuleCat.of k ((Fin (n + 1) → G) → Rep.of (ρ.funLeft X))}
    (hf : (d (Rep.of (ρ.funLeft X)) (n + 1)).hom f = 0) :
    (d (Rep.of (ρ.funLeft X)) n).hom ((-1 : k) ^ (n + 1) • (cutoffLast ρ hc n).hom f) = f := by
  have h := congr($(d_comp_cutoffLast ρ hc n).hom f)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hf, map_zero, ModuleCat.hom_add,
    ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.smul_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  have hsign : (-1 : k) ^ (n + 1) * (-1) ^ n = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨n, by ring⟩
  rw [map_smul, eq_neg_of_add_eq_zero_left h.symm, smul_neg, smul_smul, hsign, neg_one_smul,
    neg_neg]

end TauCeti.inhomogeneousCochains

namespace TauCeti.groupCohomology

open _root_.groupCohomology _root_.inhomogeneousCochains TauCeti.inhomogeneousCochains

variable {k G A X : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A] [MulAction G X]
variable (ρ : Representation k G A) {c : X → k} (hc : ∀ x, ∑ᶠ g : G, c (g • x) = 1)

/-- The cutoff average onto the invariant functions placed in degree `0`, as an endomorphism of
the complex of inhomogeneous cochains with coefficients in `X → A`: it is
`Representation.cutoffAverage` on `0`-cochains and zero in positive degrees. -/
def cutoffCochainMap :
    inhomogeneousCochains (Rep.of (ρ.funLeft X)) ⟶ inhomogeneousCochains (Rep.of (ρ.funLeft X))
    where
  f
    | 0 => ModuleCat.ofHom ((ρ.cutoffAverage hc).compLeft (Fin 0 → G))
    | _ + 1 => 0
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rcases i with _ | i
    · rw [inhomogeneousCochains.d_def]
      refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun g ↦ ?_)
      have hf (z : Fin 0 → G) : f z = f (Fin.contractNth 0 (· * ·) g) :=
        congrArg f (by subsingleton)
      have hinv := (ρ.isProj_cutoffAverage hc).map_mem (f (Fin.contractNth 0 (· * ·) g))
      rw [Representation.mem_invariants] at hinv
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, d_hom_apply,
        LinearMap.compLeft_apply, comp_apply, hf, hinv]
      simp [Pi.zero_apply (M := fun _ ↦ X → A)]
    · simp

/-- In degree `0`, `TauCeti.groupCohomology.cutoffCochainMap` is the cutoff average. -/
@[simp]
theorem cutoffCochainMap_f_zero :
    (cutoffCochainMap ρ hc).f 0 = ModuleCat.ofHom ((ρ.cutoffAverage hc).compLeft (Fin 0 → G)) :=
  (rfl)

/-- In positive degrees, `TauCeti.groupCohomology.cutoffCochainMap` is zero. -/
@[simp]
theorem cutoffCochainMap_f_succ (n : ℕ) : (cutoffCochainMap ρ hc).f (n + 1) = 0 :=
  (rfl)

/-- The components `(-1)^(j+1) • cutoffLast ρ hc j` of the cutoff homotopy, from degree `j + 1` to
degree `j`. -/
private def cutoffHomotopyHom (i j : ℕ) (hji : (ComplexShape.up ℕ).Rel j i) :
    (inhomogeneousCochains (Rep.of (ρ.funLeft X))).X i ⟶
      (inhomogeneousCochains (Rep.of (ρ.funLeft X))).X j :=
  ((inhomogeneousCochains (Rep.of (ρ.funLeft X))).XIsoOfEq hji.symm).hom ≫
    ((-1 : k) ^ (j + 1) • cutoffLast ρ hc j)

private theorem sub_cutoffCochainMap_eq_nullHomotopicMap' :
    𝟙 _ - cutoffCochainMap ρ hc = Homotopy.nullHomotopicMap' (cutoffHomotopyHom ρ hc) := by
  ext n : 1
  rcases n with _ | n
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
      (show (ComplexShape.up ℕ).Rel 0 (0 + 1) from rfl) (fun l ↦ by simp),
      inhomogeneousCochains.d_def]
    simp [cutoffHomotopyHom, d_zero_comp_cutoffLast]
  · rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl),
      inhomogeneousCochains.d_def, inhomogeneousCochains.d_def]
    have hsign : (-1 : k) ^ (n + 1 + 1) * (-1) ^ n = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n + 1, by ring⟩
    have hneg : (-1 : k) ^ (n + 1 + 1) = -(-1) ^ (n + 1) := by rw [pow_succ, mul_neg_one]
    simp only [cutoffHomotopyHom, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, Linear.smul_comp, Linear.comp_smul, d_comp_cutoffLast, smul_add,
      smul_smul, hsign, one_smul, HomologicalComplex.id_f, HomologicalComplex.sub_f_apply,
      cutoffCochainMap_f_succ, sub_zero]
    rw [hneg, neg_smul]
    abel

/-- **The cutoff contraction.** The identity of the complex of inhomogeneous cochains with
coefficients in `X → A` is homotopic to the cutoff average onto the invariant functions placed in
degree `0`, through the homotopy whose component from degree `n + 1` to degree `n` is
`(-1)^(n+1)` times the weighted insertion of a last arrow
(`TauCeti.groupCohomology.cutoffHomotopy_hom_succ`). -/
def cutoffHomotopy : Homotopy (𝟙 (inhomogeneousCochains (Rep.of (ρ.funLeft X))))
    (cutoffCochainMap ρ hc) :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (sub_cutoffCochainMap_eq_nullHomotopicMap' ρ hc)).trans
      (Homotopy.nullHomotopy' _)

/-- The component of `TauCeti.groupCohomology.cutoffHomotopy` from degree `n + 1` to degree `n` is
`(-1)^(n+1)` times the weighted insertion of a last arrow. -/
@[simp]
theorem cutoffHomotopy_hom_succ (n : ℕ) :
    (cutoffHomotopy ρ hc).hom (n + 1) n = (-1 : k) ^ (n + 1) • cutoffLast ρ hc n := by
  simp [cutoffHomotopy, Homotopy.equivSubZero, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.nullHomotopy'_hom, cutoffHomotopyHom]

include hc in
/-- **Vanishing of positive-degree cohomology.** If `c : X → k` has translates summing to one,
then the group cohomology of `G` with coefficients in the functions `X → A` vanishes in positive
degrees. -/
theorem subsingleton_funLeft_of_finsum_smul_eq_one (n : ℕ) :
    Subsingleton (groupCohomology (Rep.of (ρ.funLeft X)) (n + 1)) := by
  rw [← ModuleCat.isZero_iff_subsingleton]
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro f hf
  simp only [HomologicalComplex.shortComplexFunctor'_obj_g, CochainComplex.of_d] at hf
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f, CochainComplex.of_d]
  exact ⟨_, d_smul_cutoffLast_of_d_eq_zero ρ hc hf⟩

end TauCeti.groupCohomology
