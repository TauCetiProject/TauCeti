/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Products
public import TauCeti.AlgebraicTopology.Cellular.Lacunary
public import TauCeti.Geometry.Manifold.Morse.CWModel.Proper

/-!
# The lacunary principle for the homology of a Morse function

Let `f` be a Morse function on a boundaryless manifold `M`, either compact or with `f` proper and
bounded below, and write `cⱼ` for the number of its critical points of index `j`
(`TauCeti.criticalCount`). If `cₙ = 0` or `cₙ₊₁ = 0`, and `cₙ₋₁ = 0` or `cₙ = 0` when `n ≥ 1`, then

`Hₙ(M; R) ≅ ∐_{x critical of index n} R`.

On a compact manifold this holds for coefficients `R` in any abelian category with coproducts
(`TauCeti.IsMorse.nonempty_singularHomology_iso_sigma`); for a proper Morse function bounded below,
which may have infinitely many critical points, coproducts must be exact, as they are for modules
over a ring (`TauCeti.IsMorse.nonempty_singularHomology_iso_sigma_of_isProperMap`). In particular,
if no two critical points of `f` have indices differing by one, this holds in every degree
(`TauCeti.IsMorse.nonempty_singularHomology_iso_sigma_of_forall_ne_add_one` and
`TauCeti.IsMorse.nonempty_singularHomology_iso_sigma_of_isProperMap_of_forall_ne_add_one`), and the
homology of `M` with integral coefficients is free abelian, with one generator for each critical
point: `Hₙ(M; ℤ) ≃ₗ[ℤ] (Cₙ →₀ ℤ)` for the set `Cₙ` of critical points of index `n`
(`IsMorse.nonempty_singularHomology_int_linearEquiv_finsupp_of_isProperMap_of_forall_ne_add_one`
and `TauCeti.IsMorse.free_singularHomology_int_of_isProperMap_of_forall_ne_add_one`, with compact
versions `TauCeti.IsMorse.nonempty_singularHomology_int_linearEquiv_finsupp_of_forall_ne_add_one`
and `TauCeti.IsMorse.free_singularHomology_int_of_forall_ne_add_one`). On a compact manifold
`Hₙ(M; ℤ)` is moreover finitely generated, of rank `|Cₙ|`
(`TauCeti.IsMorse.finite_singularHomology_int_of_forall_ne_add_one`,
`TauCeti.IsMorse.finrank_singularHomology_int_eq_ncard_of_forall_ne_add_one`). This applies when
all indices are even (`TauCeti.forall_manifoldMorseIndex_ne_add_one_of_even`), and then the
homology vanishes in odd degrees (`TauCeti.IsMorse.isZero_singularHomology_of_odd`,
`TauCeti.IsMorse.isZero_singularHomology_of_isProperMap_of_odd`); more generally `Hₙ(M; R)`
vanishes whenever no critical point has index `n`
(`TauCeti.IsMorse.isZero_singularHomology_of_criticalCount_eq_zero`,
`TauCeti.IsMorse.isZero_singularHomology_of_isProperMap_of_criticalCount_eq_zero`).

Over a division ring this recovers the equality of Betti numbers and critical counts in the
lacunary case on a compact manifold
(`TauCeti.IsMorse.finrank_singularHomology_eq_of_forall_ne_add_one`), which the Morse inequalities
give; the statement here is integral, which the inequalities cannot give, since they only see
dimensions over fields. The proof goes through Milnor's CW model: `M` is
homotopy equivalent to a finite-dimensional CW complex with one `j`-cell for each critical point of
index `j` (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv` and
`TauCeti.IsMorse.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le`), whose cellular
differentials at degree `n` vanish under the hypotheses, since one end of each is zero
(`ContinuousMap.HomotopyEquiv.singularHomologyIsoSigma`).

For example, the moment function `[z] ↦ (∑ⱼ wⱼ |zⱼ|²) / ∑ⱼ |zⱼ|²` on `ℂℙⁿ` with pairwise distinct
weights has only critical points of even index, one of each index `0, 2, …, 2n`
(`TauCeti.criticalCount_projectiveMomentFunction_complex`), so these results give
`H₂ⱼ(ℂℙⁿ; R) ≅ R` for `j ≤ n` and the vanishing of the other homology groups, for every
coefficient object `R`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 (the CW model) and §4 (the example of `ℂℙⁿ`).
* R. Bott, *Lectures on Morse theory, old and new*, Bull. Amer. Math. Soc. (N.S.) 7 (1982),
  331–358, §1 (the lacunary principle).
-/

public section

open AlgebraicTopology CategoryTheory Limits Module Set Topology Topology.RelCWComplex
open scoped ContDiff ContinuousMap Manifold

universe u v w

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

/-- If no two critical points have indices differing by one, then of any two consecutive indices
one is the index of no critical point. -/
private theorem criticalCount_eq_zero_or_criticalCount_add_one_eq_zero
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (j : ℕ) :
    criticalCount I f j = 0 ∨ criticalCount I f (j + 1) = 0 := by
  simp only [criticalCount_eq_zero_iff]
  by_contra! hne
  obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := hne
  exact hind y hy x hx hxy

/-- The lacunary principle read through a CW model of `M` whose cells in each dimension `m`
correspond to the critical points of index `m`. -/
private theorem nonempty_singularHomology_iso_sigma_of_homotopyEquiv {W : Type u}
    [TopologicalSpace W] [T2Space W] [CWComplex (univ : Set W)] (e : M ≃ₕ W)
    (c : ∀ m, cell (univ : Set W) m ≃ ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = m})
    {n : ℕ} (hsucc : criticalCount I f n = 0 ∨ criticalCount I f (n + 1) = 0)
    (hpred : ∀ m, m + 1 = n → criticalCount I f m = 0 ∨ criticalCount I f n = 0)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A]
    [∀ m, HasExactColimitsOfShape (Discrete (cell (univ : Set W) m)) A] (R : A)
    [IsIso ((skeletonBasePair (univ : Set W) (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex (univ : Set W) (n + 1)) R n)] :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) := by
  -- A dimension of the model carries no cells exactly when no critical point has that index.
  have hcell (j : ℕ) : IsEmpty (cell (univ : Set W) j) ↔ criticalCount I f j = 0 :=
    (c j).isEmpty_congr.trans <| by
      simp [isEmpty_subtype, criticalCount_eq_zero_iff]
  exact ⟨(e.trans (Homeomorph.Set.univ W).symm.toHomotopyEquiv).singularHomologyIsoSigma R n
      (by simpa only [hcell] using hsucc) (fun m hm ↦ by simpa only [hcell] using hpred m hm) ≪≫
    Sigma.whiskerEquiv (c n) fun _ ↦ Iso.refl R⟩

/-- With no critical point of index `n`, the coproduct over the critical points of index `n` is
zero. -/
private theorem isZero_sigma_of_criticalCount_eq_zero {n : ℕ} (hn : criticalCount I f n = 0)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) :
    IsZero (∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) := by
  have : IsEmpty ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} :=
    ⟨fun ⟨x, hx, hxn⟩ ↦ (criticalCount_eq_zero_iff n).1 hn x hx hxn⟩
  exact (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **The lacunary principle for the homology of a compact manifold.** Let `f` be a Morse function
on a compact boundaryless manifold. If `f` has no critical points of index `n` or none of index
`n + 1`, and none of index `m` or none of index `n` whenever `n = m + 1`, then `Hₙ(M; R)` is the
coproduct of one copy of `R` for each critical point of index `n`, for coefficients `R` in any
abelian category with coproducts. -/
theorem IsMorse.nonempty_singularHomology_iso_sigma [CompactSpace M] (hf : IsMorse I f) {n : ℕ}
    (hsucc : criticalCount I f n = 0 ∨ criticalCount I f (n + 1) = 0)
    (hpred : ∀ m, m + 1 = n → criticalCount I f m = 0 ∨ criticalCount I f n = 0)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) := by
  obtain ⟨W, _, _, _, hfin, ⟨e⟩, c⟩ := hf.exists_finite_cwComplex_homotopyEquiv
  -- The model is finite, so its cell coproducts are finite, hence exact.
  have := Abelian.hasFiniteBiproducts (C := A)
  have : ∀ m, HasExactColimitsOfShape (Discrete (cell (univ : Set W) m)) A := fun m ↦
    have := hfin.finite_cell m
    inferInstance
  exact nonempty_singularHomology_iso_sigma_of_homotopyEquiv e.symm (fun m ↦ (c m).some) hsucc
    hpred R

/-- **The lacunary principle for a proper Morse function.** Let `f` be a proper Morse function
bounded below on a boundaryless manifold. If `f` has no critical points of index `n` or none of
index `n + 1`, and none of index `m` or none of index `n` whenever `n = m + 1`, then `Hₙ(M; R)` is
the coproduct of one copy of `R` for each critical point of index `n`, for coefficients `R` in any
abelian category with exact coproducts, such as modules over a ring. -/
theorem IsMorse.nonempty_singularHomology_iso_sigma_of_isProperMap (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {n : ℕ}
    (hsucc : criticalCount I f n = 0 ∨ criticalCount I f (n + 1) = 0)
    (hpred : ∀ m, m + 1 = n → criticalCount I f m = 0 ∨ criticalCount I f n = 0)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [AB4OfSize.{u} A] (R : A) :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) := by
  -- Morse indices are at most the dimension, so the model is finite-dimensional.
  obtain ⟨W, _, _, _, _, ⟨e⟩, c, -⟩ := hf.exists_cwComplex_homotopyEquiv_of_manifoldMorseIndex_le
    hp hbdd fun _ _ ↦ manifoldMorseIndex_le_finrank
  exact nonempty_singularHomology_iso_sigma_of_homotopyEquiv e (fun m ↦ (c m).some) hsucc hpred R

/-- **The lacunary principle for the homology of a compact manifold, in every degree.** If no two
critical points of a Morse function `f` on a compact boundaryless manifold have indices differing
by one, then in every degree `n` the homology `Hₙ(M; R)` is the coproduct of one copy of `R` for
each critical point of index `n`, for coefficients `R` in any abelian category with coproducts. -/
theorem IsMorse.nonempty_singularHomology_iso_sigma_of_forall_ne_add_one [CompactSpace M]
    (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) :=
  hf.nonempty_singularHomology_iso_sigma
    (criticalCount_eq_zero_or_criticalCount_add_one_eq_zero hind n)
    (fun m hm ↦ hm ▸ criticalCount_eq_zero_or_criticalCount_add_one_eq_zero hind m) R

/-- **The lacunary principle for a proper Morse function, in every degree.** If no two critical
points of a proper Morse function `f` bounded below on a boundaryless manifold have indices
differing by one, then in every degree `n` the homology `Hₙ(M; R)` is the coproduct of one copy of
`R` for each critical point of index `n`, for coefficients `R` in any abelian category with exact
coproducts, such as modules over a ring. -/
theorem IsMorse.nonempty_singularHomology_iso_sigma_of_isProperMap_of_forall_ne_add_one
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [AB4OfSize.{u} A] (R : A)
    (n : ℕ) :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) :=
  hf.nonempty_singularHomology_iso_sigma_of_isProperMap hp hbdd
    (criticalCount_eq_zero_or_criticalCount_add_one_eq_zero hind n)
    (fun m hm ↦ hm ▸ criticalCount_eq_zero_or_criticalCount_add_one_eq_zero hind m) R

/-! ### Proper Morse functions bounded below -/

/-- **The lacunary principle for even indices, for a proper Morse function.** If every critical
point of a proper Morse function `f` bounded below on a boundaryless manifold has even index, then
in every degree `n` the homology `Hₙ(M; R)` is the coproduct of one copy of `R` for each critical
point of index `n`, for coefficients `R` in any abelian category with exact coproducts. -/
theorem IsMorse.nonempty_singularHomology_iso_sigma_of_isProperMap_of_even (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x))
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [AB4OfSize.{u} A] (R : A)
    (n : ℕ) :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) :=
  hf.nonempty_singularHomology_iso_sigma_of_isProperMap_of_forall_ne_add_one hp hbdd
    (forall_manifoldMorseIndex_ne_add_one_of_even heven) R n

/-- **Homology vanishes in a degree with no critical points, for a proper Morse function.** If a
proper Morse function bounded below on a boundaryless manifold has no critical point of index `n`,
then `Hₙ(M; R) = 0`, for coefficients in any abelian category with exact coproducts. -/
theorem IsMorse.isZero_singularHomology_of_isProperMap_of_criticalCount_eq_zero (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f)) {n : ℕ} (hn : criticalCount I f n = 0)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [AB4OfSize.{u} A] (R : A) :
    IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of M)) := by
  obtain ⟨e⟩ := hf.nonempty_singularHomology_iso_sigma_of_isProperMap hp hbdd (Or.inl hn)
    (fun _ _ ↦ Or.inr hn) R
  exact (isZero_sigma_of_criticalCount_eq_zero hn R).of_iso e

/-- **Odd homology vanishes for a proper Morse function with only even indices.** On a boundaryless
manifold carrying a proper Morse function bounded below all of whose critical points have even
index, the homology vanishes in odd degrees, for coefficients in any abelian category with exact
coproducts. -/
theorem IsMorse.isZero_singularHomology_of_isProperMap_of_odd (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x))
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] [AB4OfSize.{u} A] (R : A)
    {n : ℕ} (hn : Odd n) : IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of M)) :=
  hf.isZero_singularHomology_of_isProperMap_of_criticalCount_eq_zero hp hbdd
    (criticalCount_eq_zero_of_odd heven hn) R

/-- **Integral homology is free on the critical points, for a proper Morse function.** If no two
critical points of a proper Morse function `f` bounded below on a boundaryless manifold have indices
differing by one, then the integral homology `Hₙ(M; ℤ)` is the free abelian group on the critical
points of index `n`. -/
theorem
    IsMorse.nonempty_singularHomology_int_linearEquiv_finsupp_of_isProperMap_of_forall_ne_add_one
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    Nonempty (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M) ≃ₗ[ℤ]
      (↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} →₀ ℤ)) := by
  obtain ⟨e⟩ := hf.nonempty_singularHomology_iso_sigma_of_isProperMap_of_forall_ne_add_one hp hbdd
    hind (ModuleCat.of ℤ (ULift.{u} ℤ)) n
  exact ⟨e.toLinearEquiv ≪≫ₗ ModuleCat.coprodLinearEquivFinsupp _ _ ≪≫ₗ
    Finsupp.mapRange.linearEquiv ULift.moduleEquiv⟩

/-- **Integral homology is free, for a proper Morse function.** If no two critical points of a
proper Morse function bounded below on a boundaryless manifold have indices differing by one, then
the integral homology of the manifold is a free abelian group in every degree. -/
theorem IsMorse.free_singularHomology_int_of_isProperMap_of_forall_ne_add_one (hf : IsMorse I f)
    (hp : IsProperMap f) (hbdd : BddBelow (range f))
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) := by
  obtain ⟨e⟩ :=
    hf.nonempty_singularHomology_int_linearEquiv_finsupp_of_isProperMap_of_forall_ne_add_one hp
      hbdd hind n
  exact Module.Free.of_equiv e.symm

/-! ### Compact manifolds -/

section Compact

variable [CompactSpace M]

/-- **The lacunary principle for even indices.** If every critical point of a Morse function `f` on
a compact boundaryless manifold has even index, then in every degree `n` the homology `Hₙ(M; R)` is
the coproduct of one copy of `R` for each critical point of index `n`, for coefficients `R` in any
abelian category with coproducts. -/
theorem IsMorse.nonempty_singularHomology_iso_sigma_of_even (hf : IsMorse I f)
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x))
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) (n : ℕ) :
    Nonempty (((singularHomologyFunctor A n).obj R).obj (TopCat.of M) ≅
      ∐ fun _ : ↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} ↦ R) :=
  hf.nonempty_singularHomology_iso_sigma_of_forall_ne_add_one
    (forall_manifoldMorseIndex_ne_add_one_of_even heven) R n

/-- **Homology vanishes in a degree with no critical points.** If a Morse function on a compact
boundaryless manifold has no critical point of index `n`, then `Hₙ(M; R) = 0`, for coefficients in
any abelian category with coproducts. -/
theorem IsMorse.isZero_singularHomology_of_criticalCount_eq_zero (hf : IsMorse I f) {n : ℕ}
    (hn : criticalCount I f n = 0)
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) :
    IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of M)) := by
  obtain ⟨e⟩ := hf.nonempty_singularHomology_iso_sigma (Or.inl hn) (fun _ _ ↦ Or.inr hn) R
  exact (isZero_sigma_of_criticalCount_eq_zero hn R).of_iso e

/-- **Odd homology vanishes for a Morse function with only even indices.** On a compact
boundaryless manifold carrying a Morse function all of whose critical points have even index, the
homology vanishes in odd degrees, for coefficients in any abelian category with coproducts. -/
theorem IsMorse.isZero_singularHomology_of_odd (hf : IsMorse I f)
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x))
    {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A) {n : ℕ}
    (hn : Odd n) : IsZero (((singularHomologyFunctor A n).obj R).obj (TopCat.of M)) :=
  hf.isZero_singularHomology_of_criticalCount_eq_zero (criticalCount_eq_zero_of_odd heven hn) R

/-- **Integral homology is free on the critical points.** If no two critical points of a Morse
function `f` on a compact boundaryless manifold have indices differing by one, then the integral
homology `Hₙ(M; ℤ)` is the free abelian group on the critical points of index `n`. -/
theorem IsMorse.nonempty_singularHomology_int_linearEquiv_finsupp_of_forall_ne_add_one
    (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    Nonempty (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M) ≃ₗ[ℤ]
      (↥{x ∈ criticalPoints I f | manifoldMorseIndex I f x = n} →₀ ℤ)) :=
  -- A continuous function on a compact space is proper and bounded below.
  hf.nonempty_singularHomology_int_linearEquiv_finsupp_of_isProperMap_of_forall_ne_add_one
    hf.contMDiff.continuous.isProperMap (isCompact_range hf.contMDiff.continuous).bddBelow hind n

/-- **Integral homology is free.** If no two critical points of a Morse function on a compact
boundaryless manifold have indices differing by one, then the integral homology of the manifold is
a free abelian group in every degree. -/
theorem IsMorse.free_singularHomology_int_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) :=
  hf.free_singularHomology_int_of_isProperMap_of_forall_ne_add_one
    hf.contMDiff.continuous.isProperMap (isCompact_range hf.contMDiff.continuous).bddBelow hind n

/-- **Integral homology is finitely generated.** If no two critical points of a Morse function on a
compact boundaryless manifold have indices differing by one, then the integral homology of the
manifold is finitely generated in every degree. -/
theorem IsMorse.finite_singularHomology_int_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) := by
  obtain ⟨e⟩ := hf.nonempty_singularHomology_int_linearEquiv_finsupp_of_forall_ne_add_one hind n
  have := (hf.finite_criticalPoints.subset
    (sep_subset _ fun x ↦ manifoldMorseIndex I f x = n)).to_subtype
  exact Module.Finite.equiv e.symm

/-- **The rank of integral homology counts critical points.** If no two critical points of a Morse
function `f` on a compact boundaryless manifold have indices differing by one, then the rank of
`Hₙ(M; ℤ)` is the number of critical points of index `n`. -/
theorem IsMorse.finrank_singularHomology_int_eq_ncard_of_forall_ne_add_one (hf : IsMorse I f)
    (hind : ∀ x ∈ criticalPoints I f, ∀ y ∈ criticalPoints I f,
      manifoldMorseIndex I f x ≠ manifoldMorseIndex I f y + 1) (n : ℕ) :
    finrank ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) =
      {x ∈ criticalPoints I f | manifoldMorseIndex I f x = n}.ncard := by
  obtain ⟨e⟩ := hf.nonempty_singularHomology_int_linearEquiv_finsupp_of_forall_ne_add_one hind n
  have := (hf.finite_criticalPoints.subset
    (sep_subset _ fun x ↦ manifoldMorseIndex I f x = n)).fintype
  rw [e.finrank_eq, finrank_finsupp_self, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

end Compact

end TauCeti
