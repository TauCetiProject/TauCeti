/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CrossProduct
public import TauCeti.AlgebraicTopology.Cohomology.Sphere.Basic
public import TauCeti.AlgebraicTopology.Sphere.Contractible
public import TauCeti.AlgebraicTopology.Sphere.Puncture
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.CupLength

/-!
# The Lusternik–Schnirelmann category of spheres and their products

The unit sphere `S` of a real normed space is covered by the two open sets obtained by removing a
point `p` and its antipode `-p`. Each punctured sphere is contractible, so its inclusion into `S`
is nullhomotopic, and `lsCategoryCount S univ ≤ 2`. When the space is nontrivial and
finite-dimensional, `S` is not contractible, so the count is exactly `2` and the normalized
category of `S` is `1`, including for the two-point zero-sphere.

For spheres of positive dimension the cup-length lower bound is attained: over every nontrivial
commutative ring `R` the top cohomology class of the sphere is nonzero, so the cup length is `1`.
For a product of `k` spheres of positive dimension, the cup product of the pullbacks of the top
classes of the factors evaluates to `1` on a homology class built from homology cross products
(`TopCat.exists_singularKronecker_singularCup_fst_snd_eq_mul`). So this product of `k` classes of
positive degree is nonzero, and the cup length and the normalized category of the product are at
least `k`. This lower bound needs no Künneth isomorphism, so it holds over every nontrivial
commutative ring. No upper bound for the category of a product is proved here.

## Main results

* `TauCeti.lsCategoryCount_univ_sphere_le_two`: the unit sphere of any real normed space has a
  categorical cover by two open sets.
* `TauCeti.lsCategoryCount_univ_sphere` and `TauCeti.normalizedLSCategory_sphere`: the unit
  sphere of a nontrivial finite-dimensional real normed space has count `2` and normalized
  category `1`.
* `TauCeti.lsCupLength_sphere`: a sphere of positive dimension has cup length `1` over every
  nontrivial commutative ring.
* `TauCeti.natCast_le_lsCupLength_pi_sphere` and
  `TauCeti.natCast_le_normalizedLSCategory_pi_sphere`: a product of `k` spheres of positive
  dimension has cup length and normalized category at least `k`.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the cross product and the cohomology ring of a product of spheres.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Metric Module Set TopologicalSpace ContinuousMap
  AlgebraicTopology

universe u

namespace TauCeti

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The unit sphere has a categorical cover by two open sets**: the complements of a point and
of its antipode, whose inclusions are nullhomotopic. This holds for every real normed space,
including the trivial one, whose unit sphere is empty. -/
theorem lsCategoryCount_univ_sphere_le_two : lsCategoryCount (sphere (0 : E) 1) univ ≤ 2 := by
  rcases isEmpty_or_nonempty (sphere (0 : E) 1) with h | ⟨⟨p⟩⟩
  · simp [univ_eq_empty_iff.mpr h]
  let U : Fin 2 → Opens (sphere (0 : E) 1) :=
    ![⟨{p}ᶜ, isOpen_compl_singleton⟩, ⟨{-p}ᶜ, isOpen_compl_singleton⟩]
  have hcover : univ ⊆ ⋃ i, (U i : Set (sphere (0 : E) 1)) := by
    intro x _
    by_cases hx : x = p
    · subst hx
      exact mem_iUnion.2 ⟨1, by simpa [U] using ne_neg_of_mem_unit_sphere ℝ x⟩
    · exact mem_iUnion.2 ⟨0, by simpa [U] using hx⟩
  have hnull (i : Fin 2) : (subtypeVal (U i : Set (sphere (0 : E) 1))).Nullhomotopic := by
    fin_cases i
    · exact nullhomotopic_inclusion_sphere_compl_singleton p
    · exact nullhomotopic_inclusion_sphere_compl_singleton (-p)
  exact_mod_cast (LSCategoricalCover.mk U hcover hnull).lsCategoryCount_le

/-- The unit sphere of a nontrivial finite-dimensional real normed space has
Lusternik–Schnirelmann count `2`: it has a categorical cover by two open sets, and it is not
contractible. -/
@[simp]
theorem lsCategoryCount_univ_sphere [FiniteDimensional ℝ E] [Nontrivial E] :
    lsCategoryCount (sphere (0 : E) 1) univ = 2 := by
  have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  refine le_antisymm lsCategoryCount_univ_sphere_le_two ?_
  have h := not_contractibleSpace_sphere (E := E)
  rw [← lsCategoryCount_univ_le_one_iff, not_le] at h
  exact Order.add_one_le_of_lt h

/-- **The normalized Lusternik–Schnirelmann category of a sphere is `1`**, for the unit sphere of
every nontrivial finite-dimensional real normed space, including the zero-sphere. -/
@[simp]
theorem normalizedLSCategory_sphere [FiniteDimensional ℝ E] [Nontrivial E] :
    normalizedLSCategory (sphere (0 : E) 1) = 1 := by
  rw [normalizedLSCategory_def, lsCategoryCount_univ_sphere]
  rfl

end Sphere

section Detected

-- As in `TauCeti.AlgebraicTopology.Cohomology.Kunneth`, the direct colimit instance of `ModuleCat`
-- supplies the coproducts of singular homology without a long instance search.
attribute [local instance high] ModuleCat.hasColimitsOfShape

variable (X : Type u) [TopologicalSpace X] (R : Type u) [CommRing R]

/-- A nonzero product of `m` classes of positive degree, detected by a homology class on which it
evaluates to `1`. -/
private def HasDetectedCupProduct (m : ℕ) : Prop :=
  ∃ (d : ℕ) (c : (TopCat.of X).singularCohomology (𝟙_ (ModuleCat.{u} R)) R
      (𝟙_ (ModuleCat.{u} R)) d)
    (x : ((singularHomologyFunctor (ModuleCat.{u} R) d).obj (𝟙_ (ModuleCat.{u} R))).obj
      (TopCat.of X)),
    IsPositiveDegreeCupProduct X R m c ∧ (TopCat.of X).singularKronecker R d c x = 1

variable {X R}

private theorem HasDetectedCupProduct.le_lsCupLength [Nontrivial R] {m : ℕ}
    (h : HasDetectedCupProduct X R m) : (m : ℕ∞) ≤ lsCupLength X R := by
  obtain ⟨d, c, x, hc, hx⟩ := h
  refine TauCeti.le_lsCupLength hc fun hc0 ↦ ?_
  rw [hc0, map_zero] at hx
  exact zero_ne_one hx

private theorem HasDetectedCupProduct.of_homeomorph {Y : Type u} [TopologicalSpace Y]
    (e : X ≃ₜ Y) {m : ℕ} (h : HasDetectedCupProduct Y R m) : HasDetectedCupProduct X R m := by
  obtain ⟨d, c, y, hc, hy⟩ := h
  refine ⟨d, TopCat.singularCohomologyMap (TopCat.ofHom (e : C(X, Y))) d c,
    ((singularHomologyFunctor (ModuleCat.{u} R) d).obj (𝟙_ (ModuleCat.{u} R))).map
      (TopCat.ofHom (e.symm : C(Y, X))) y, hc.map (e : C(X, Y)), ?_⟩
  have hid : TopCat.ofHom (e.symm : C(Y, X)) ≫ TopCat.ofHom (e : C(X, Y)) = 𝟙 (TopCat.of Y) := by
    ext; simp
  have key : ((singularHomologyFunctor (ModuleCat.{u} R) d).obj (𝟙_ (ModuleCat.{u} R))).map
      (TopCat.ofHom (e.symm : C(Y, X))) ≫ (TopCat.of X).singularKronecker R d
        (TopCat.singularCohomologyMap (TopCat.ofHom (e : C(X, Y))) d c) =
      (TopCat.of Y).singularKronecker R d c := by
    rw [TopCat.singularKronecker_naturality, ← Category.assoc, ← Functor.map_comp, hid,
      CategoryTheory.Functor.map_id, Category.id_comp]
  exact (ConcreteCategory.comp_apply _ _ y).symm.trans
    ((ConcreteCategory.congr_hom key y).trans hy)

private theorem HasDetectedCupProduct.prod {Y : Type u} [TopologicalSpace Y] {m : ℕ}
    (hY : HasDetectedCupProduct Y R 1) (hX : HasDetectedCupProduct X R m) :
    HasDetectedCupProduct (Y × X) R (m + 1) := by
  obtain ⟨p, b, y, hb, hy⟩ := hY
  obtain ⟨q, c, x, hc, hx⟩ := hX
  obtain ⟨z, hz⟩ := TopCat.exists_singularKronecker_singularCup_fst_snd_eq_mul (k := R)
    (TopCat.of Y) (TopCat.of X) rfl b c y x
  -- The product of `TopCat.of Y` and `TopCat.of X` in `TopCat` is `TopCat.of (Y × X)`, with the
  -- projections as its structure maps.
  refine ⟨p + q, _, z,
    .cup hb.degree_ne_zero rfl (TopCat.singularCohomologyMap (TopCat.ofHom ContinuousMap.fst) p b)
      (hc.map ContinuousMap.snd), ?_⟩
  rw [hy, hx, one_mul] at hz
  exact hz

variable (R) in
private theorem hasDetectedCupProduct_sphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E) :
    HasDetectedCupProduct (sphere (0 : E) 1) R 1 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hE
  refine HasDetectedCupProduct.of_homeomorph ((sphereHomeomorphOfFinrankEq
    (F := EuclideanSpace ℝ (Fin (n + 2))) (by simp [hn])).trans Homeomorph.ulift.symm) ?_
  -- `TopCat.sphere (n + 1)` is the lifted unit sphere of `EuclideanSpace ℝ (Fin (n + 2))`, and the
  -- unit of `ModuleCat R` is `ModuleCat.of R R`.
  exact ⟨n + 1, (singularCohomologyTopCatSphereEquiv R (ModuleCat.of R R) n).symm 1, _,
    .single n.succ_ne_zero _,
    singularKronecker_singularCohomologyTopCatSphereEquiv_symm R (ModuleCat.of R R) n 1⟩

variable (R) in
private theorem hasDetectedCupProduct_pi_sphere (k : ℕ) : ∀ (E : Fin (k + 1) → Type u)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)],
    (∀ i, 2 ≤ finrank ℝ (E i)) →
      HasDetectedCupProduct ((i : Fin (k + 1)) → sphere (0 : E i) 1) R (k + 1) := by
  induction k with
  | zero =>
    intro E _ _ _ hE
    exact .of_homeomorph (Homeomorph.piUnique (α := Fin 1) _)
      (hasDetectedCupProduct_sphere R (hE 0))
  | succ k ih =>
    intro E _ _ _ hE
    -- Split off the first factor, and index the remaining ones by `Fin (k + 1)` through
    -- `Fin.succAbove 0`.
    let e : ((i : Fin (k + 2)) → sphere (0 : E i) 1) ≃ₜ
        sphere (0 : E 0) 1 × ((j : Fin (k + 1)) → sphere (0 : E (finSuccAboveEquiv 0 j)) 1) :=
      (Homeomorph.piSplitAt 0 fun i ↦ sphere (0 : E i) 1).trans ((Homeomorph.refl _).prodCongr
        (Homeomorph.piCongrLeft (Y := fun j : {x : Fin (k + 2) // x ≠ 0} ↦ sphere (0 : E j) 1)
          (finSuccAboveEquiv 0)).symm)
    exact .of_homeomorph e ((hasDetectedCupProduct_sphere R (hE 0)).prod (ih _ fun _ ↦ hE _))

end Detected

/-! ### Cup length of spheres and of their products -/

/-- **The cup length of a positive-dimensional sphere is `1`** over every nontrivial commutative
ring: its top cohomology class is nonzero, and the normalized category `1` bounds the cup length
above. -/
@[simp]
theorem lsCupLength_sphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : 2 ≤ finrank ℝ E) (R : Type u) [CommRing R] [Nontrivial R] :
    lsCupLength (sphere (0 : E) 1) R = 1 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  refine le_antisymm (lsCupLength_le_normalizedLSCategory.trans_eq normalizedLSCategory_sphere) ?_
  exact_mod_cast (hasDetectedCupProduct_sphere R hE).le_lsCupLength

section Products

variable {k : ℕ} (E : Fin k → Type u) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

/-- **The cup length of a product of `k` positive-dimensional spheres is at least `k`**, over every
nontrivial commutative ring `R`: the cup product of the pullbacks of the top classes of the factors
evaluates to `1` on a cross product of generators of the top homology of the factors. -/
theorem natCast_le_lsCupLength_pi_sphere (hE : ∀ i, 2 ≤ finrank ℝ (E i)) (R : Type u)
    [CommRing R] [Nontrivial R] : (k : ℕ∞) ≤ lsCupLength ((i : Fin k) → sphere (0 : E i) 1) R := by
  cases k with
  | zero => simp
  | succ k => exact (hasDetectedCupProduct_pi_sphere R k E hE).le_lsCupLength

/-- **The normalized Lusternik–Schnirelmann category of a product of `k` positive-dimensional
spheres is at least `k`**, by the cup-length lower bound with integer coefficients. -/
theorem natCast_le_normalizedLSCategory_pi_sphere (hE : ∀ i, 2 ≤ finrank ℝ (E i)) :
    (k : ℕ∞) ≤ normalizedLSCategory ((i : Fin k) → sphere (0 : E i) 1) :=
  (natCast_le_lsCupLength_pi_sphere E hE (ULift.{u} ℤ)).trans lsCupLength_le_normalizedLSCategory

end Products

end TauCeti
