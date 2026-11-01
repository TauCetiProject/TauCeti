/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import TauCeti.RepresentationTheory.FunLeft
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Contraction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Data.Fin.Basic
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
`X → A` vanishes. As for averaging, the homotopy and the primitives are assembled from the two
identities of `h` with the differential by `TauCeti.groupCohomology.homotopyOfDCompEq` and
`TauCeti.inhomogeneousCochains.d_smul_of_d_comp_eq`.

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

/-- The insertion `x ↦ ∑ᶠ g, c (g • x) • f (y, (g * y₀ ⋯ yₙ₋₁)⁻¹) x` of a last arrow into an
`(n + 1)`-cochain `f` with coefficients in `X → A`, weighted by `c`, an `n`-cochain. -/
def cutoffLast (n : ℕ) :
    ModuleCat.of k ((Fin (n + 1) → G) → Rep.of (ρ.funLeft X)) ⟶
      ModuleCat.of k ((Fin n → G) → Rep.of (ρ.funLeft X)) :=
  ModuleCat.ofHom
  { toFun f y x := ∑ᶠ g : G, c (g • x) • f (Fin.snoc y (g * Fin.partialProd y (Fin.last n))⁻¹) x
    map_add' f f' := by
      ext y x
      have hfin : HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc x)
      simp only [Pi.add_apply, smul_add]
      exact finsum_add_distrib (hfin.fun_smul_left _) (hfin.fun_smul_left _)
    map_smul' r f := by
      ext y x
      have hfin : HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc x)
      simp only [Pi.smul_apply, RingHom.id_apply, smul_comm _ r]
      exact (smul_finsum' r (hfin.fun_smul_left _)).symm }

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
    Fin.partialProd_contractNth_castSucc, Fin.apply_last_mul_inv_mul_partialProd_last,
    finsum_smul_inv_smul, mul_assoc, ← Fin.partialProd_last_eq_mul_tail, Fin.val_castSucc,
    Fin.val_last]
  -- Every sum is now weighted by `c (· • x)`: write them as finite sums over its support, and
  -- sum the constant last face against the weights.
  have hfin : HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc x)
  have hsum : ∑ g ∈ hfin.toFinset, c (g • x) = 1 := (finsum_eq_sum _ hfin).symm.trans (hc x)
  have hlast : ∑ g ∈ (hasFiniteSupport_of_finsum_eq_one (hc x)).toFinset,
      (-1 : k) ^ (n + 1 + 1) • c (g • x) • f y x = (-1 : k) ^ n • f y x := by
    rw [← Finset.smul_sum, ← Finset.sum_smul, hsum, one_smul, pow_succ, pow_succ,
      mul_assoc, neg_one_mul, neg_neg, mul_one]
  simp only [finsum_smul_eq_sum hfin]
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
  have hfin : HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc x)
  have hsum : ∑ g ∈ hfin.toFinset, c (g • x) = 1 := (finsum_eq_sum _ hfin).symm.trans (hc x)
  simp only [hsnoc, hprod, mul_one, inv_inv]
  rw [finsum_smul_eq_sum hfin, finsum_smul_eq_sum hfin]
  simp only [hsign, neg_one_smul, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.sum_smul, hsum, one_smul, sub_eq_add_neg]

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
    (d (Rep.of (ρ.funLeft X)) n).hom ((-1 : k) ^ (n + 1) • (cutoffLast ρ hc n).hom f) = f :=
  d_smul_of_d_comp_eq (d_comp_cutoffLast ρ hc n) hf

end TauCeti.inhomogeneousCochains

namespace TauCeti.groupCohomology

open _root_.groupCohomology _root_.inhomogeneousCochains TauCeti.inhomogeneousCochains

variable {k G A X : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A] [MulAction G X]
variable (ρ : Representation k G A) {c : X → k} (hc : ∀ x, ∑ᶠ g : G, c (g • x) = 1)

/-- The cutoff average onto the invariant functions placed in degree `0`, as an endomorphism of
the complex of inhomogeneous cochains with coefficients in `X → A`: it is
`Representation.cutoffAverage` on `0`-cochains and zero in positive degrees. -/
def cutoffCochainMap :
    inhomogeneousCochains (Rep.of (ρ.funLeft X)) ⟶ inhomogeneousCochains (Rep.of (ρ.funLeft X)) :=
  ofDegreeZero (ModuleCat.ofHom ((ρ.cutoffAverage hc).compLeft (Fin 0 → G)))
    (comp_d_zero_eq_zero (d_comp_cutoffLast ρ hc) (d_zero_comp_cutoffLast ρ hc))

/-- In degree `0`, `TauCeti.groupCohomology.cutoffCochainMap` is the cutoff average. -/
@[simp]
theorem cutoffCochainMap_f_zero :
    (cutoffCochainMap ρ hc).f 0 = ModuleCat.ofHom ((ρ.cutoffAverage hc).compLeft (Fin 0 → G)) :=
  ofDegreeZero_f_zero _

/-- In positive degrees, `TauCeti.groupCohomology.cutoffCochainMap` is zero. -/
@[simp]
theorem cutoffCochainMap_f_succ (n : ℕ) : (cutoffCochainMap ρ hc).f (n + 1) = 0 :=
  ofDegreeZero_f_succ _ n

/-- **The cutoff contraction.** The identity of the complex of inhomogeneous cochains with
coefficients in `X → A` is homotopic to the cutoff average onto the invariant functions placed in
degree `0`, through the homotopy whose component from degree `n + 1` to degree `n` is
`(-1)^(n+1)` times the weighted insertion of a last arrow
(`TauCeti.groupCohomology.cutoffHomotopy_hom_succ`). -/
def cutoffHomotopy : Homotopy (𝟙 (inhomogeneousCochains (Rep.of (ρ.funLeft X))))
    (cutoffCochainMap ρ hc) :=
  homotopyOfDCompEq (d_comp_cutoffLast ρ hc) (d_zero_comp_cutoffLast ρ hc)

/-- The component of `TauCeti.groupCohomology.cutoffHomotopy` from degree `n + 1` to degree `n` is
`(-1)^(n+1)` times the weighted insertion of a last arrow. -/
@[simp]
theorem cutoffHomotopy_hom_succ (n : ℕ) :
    (cutoffHomotopy ρ hc).hom (n + 1) n = (-1 : k) ^ (n + 1) • cutoffLast ρ hc n :=
  homotopyOfDCompEq_hom_succ _ _ n

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
