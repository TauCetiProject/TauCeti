/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Reduced
public import TauCeti.AlgebraicTopology.Sphere.Equator
public import TauCeti.AlgebraicTopology.Sphere.Puncture
public import TauCeti.AlgebraicTopology.Sphere.Zero
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import TauCeti.AlgebraicTopology.Disk

/-!
# The homology of spheres

For a point `p` of the unit sphere `S` of a real normed space, the complements of `p` and of `-p`
form an open cover of `S` by two contractible sets whose intersection is `S ∖ {p, -p}`. The
reduced Mayer–Vietoris connecting morphism of this cover is therefore an isomorphism
`Hₖ₊₁(S) ≅ H_redₖ(S ∖ {p, -p})` in every degree. In a real inner product space, `S ∖ {p, -p}` is
homotopy equivalent to the unit sphere of the orthogonal complement `(ℝ ∙ p)ᗮ`, and composing
gives the isomorphism `H_redₖ₊₁(S) ≅ H_redₖ(S ∩ (ℝ ∙ p)ᗮ)`, lowering both the sphere's dimension
and the degree.

Iterating this suspension isomorphism down to the zero-sphere, whose reduced homology is one copy
of the coefficient object in degree zero and vanishes above, computes the reduced homology of the
unit sphere of an `(n + 1)`-dimensional real inner product space: it is one copy of the
coefficient object in degree `n` and vanishes in every other degree.  Mathlib's `TopCat.sphere n`
is the universe lift of the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`; through
`TauCeti.diskBoundaryHomeomorph` it is homeomorphic to the unit sphere of a Euclidean space of the
same dimension in the lifted universe, so the same computation applies to it.

For the unit circle `S` of a two-dimensional real inner product space, the explicit form of the
Mayer–Vietoris sequence is recorded directly: the cover is by the two open arcs `S ∖ {p}` and
`S ∖ {-p}`, whose intersection `S ∖ {p, -p}` consists of two open arcs, the path components of any
of its points `x` and of `-x`.  The connecting morphism `H₁(S) ⟶ H₀(S ∖ {p, -p})` identifies
`H₁(S)` with one copy of the coefficient object and sends the resulting generator to `[-x] - [x]`.

Coefficients are an object `R` of an abelian category with coproducts.

## Main definitions and results

* `TauCeti.isIso_reducedMayerVietorisδ_sphere`: the reduced Mayer–Vietoris connecting morphism
  `Hₖ₊₁(S) ⟶ H_redₖ(S ∖ {p, -p})` of the cover of `S` by the complements of `p` and `-p` is an
  isomorphism.
* `TauCeti.reducedSingularHomologySphereSuccIso`: the isomorphism
  `H_redₖ₊₁(S) ≅ H_redₖ(S ∩ (ℝ ∙ p)ᗮ)`, given by that connecting morphism followed by the homotopy
  equivalence of `S ∖ {p, -p}` with the equator.
* `TauCeti.reducedSingularHomologySphereZeroIso`: `H_red₀(S) ≅ R` for the zero-sphere, with
  generator `[-p] - [p]`.
* `TauCeti.singularHomologySphereOneIso` and
  `TauCeti.singularHomologySphereOneIso_inv_mayerVietorisδ`: `H₁(S) ≅ R` for the circle, whose
  generator the Mayer–Vietoris connecting morphism of the cover by `S ∖ {p}` and `S ∖ {-p}` sends
  to `[-x] - [x]` in the zeroth homology of `S ∖ {p, -p}`.
* `TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne` and
  `TauCeti.reducedSingularHomologySphereIso`: for `finrank ℝ E = n + 1`, the reduced homology of
  the unit sphere of `E` vanishes in degrees `k ≠ n` and is isomorphic to `R` in degree `n`.
* `TauCeti.isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne` and
  `TauCeti.reducedSingularHomologyTopCatSphereIso`: the same for Mathlib's `TopCat.sphere n`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, Example 2.46: the reduced Mayer–Vietoris sequence
  of a cover of `Sⁿ` by two contractible open sets meeting in a space homotopy equivalent to
  `Sⁿ⁻¹`, there neighbourhoods of the two hemispheres and here the complements of two antipodal
  points, and the resulting induction on dimension.  The computed groups are those of Section 2.1,
  Corollary 2.14.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

section Normed

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : sphere (0 : E) 1)

/-- **The Mayer–Vietoris isomorphism of a sphere.** The reduced Mayer–Vietoris connecting
morphism `Hₖ₊₁(S) ⟶ H_redₖ(S ∖ {p, -p})` of the cover of the unit sphere `S` by the complements of
`p` and `-p` is an isomorphism in every degree, since both complements are contractible. -/
theorem isIso_reducedMayerVietorisδ_sphere (k : ℕ) :
    IsIso (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
      isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg p) k) :=
  have := contractibleSpace_sphere_compl_singleton p
  have := contractibleSpace_sphere_compl_singleton (-p)
  inferInstance

/-- **Reduced homology of the zero-sphere.**  For a point `p` of the unit sphere of a
one-dimensional real normed space, the reduced homology of the sphere in degree zero is one copy
of the coefficient object, generated by the class `[-p] - [p]`
(`TauCeti.reducedSingularHomologySphereZeroIso_inv_ι`). -/
def reducedSingularHomologySphereZeroIso (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    (reducedSingularHomologyFunctor R 0).obj (TopCat.of (sphere (0 : E) 1)) ≅ R :=
  haveI := zerothHomotopySphereUnique h p
  reducedSingularHomology₀Iso R (X := TopCat.of (sphere (0 : E) 1)) p ≪≫ coproductUniqueIso _

/-- The generator of the reduced homology of the zero-sphere `{p, -p}` is the class
`[-p] - [p]`. -/
-- Not a simp lemma: `reducedSingularHomologyι_zero_app` rewrites the degree-zero inclusion
-- inside the left-hand side first, so this would fail the `simpNF` linter.
@[reassoc]
lemma reducedSingularHomologySphereZeroIso_inv_ι (h : finrank ℝ E = 1) (p : sphere (0 : E) 1) :
    (reducedSingularHomologySphereZeroIso R h p).inv ≫
        (reducedSingularHomologyι R 0).app (TopCat.of (sphere (0 : E) 1)) =
      singularHomology₀Section R (X := TopCat.of (sphere (0 : E) 1)) (-p) -
        singularHomology₀Section R (X := TopCat.of (sphere (0 : E) 1)) p := by
  have := zerothHomotopySphereUnique h p
  simp only [reducedSingularHomologySphereZeroIso, Iso.trans_inv, Category.assoc,
    coproductUniqueIso_inv, zerothHomotopySphereUnique_default]
  exact ι_reducedSingularHomology₀Iso_inv_ι R (X := TopCat.of (sphere (0 : E) 1)) p (-p) _

end Normed

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

-- `reducedSingularHomologySuccIso` targets `singularHomologyFunctor`, while the
-- Mayer–Vietoris connecting morphism starts at `TopCat.toSSet` homology. Ordinary
-- singular homology is defined using `TopCat.toSSet`, so these objects are definitionally equal.
private abbrev singularHomologyFunctor_obj_eq_toSSetHomology (n : ℕ) (X : TopCat.{w}) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj R).obj X =
      (TopCat.toSSet.obj X).homology R n := rfl

private lemma singularHomologyFunctor_obj_eq_toSSetHomology_hom_comp
    (n : ℕ) (X : TopCat.{w}) {Y : C}
    (f : (TopCat.toSSet.obj X).homology R n ⟶ Y) :
    (eqToIso (singularHomologyFunctor_obj_eq_toSSetHomology R n X)).hom ≫ f = f := by
  -- The equality above is `rfl`, so its `eqToIso` is the identity after reduction.
  change 𝟙 _ ≫ f = f
  exact Category.id_comp f

/-- **The suspension isomorphism for the homology of spheres.** For a point `p` of the unit
sphere `S` of a real inner product space `E`, the reduced homology of `S` in degree `k + 1` is
isomorphic to the reduced homology in degree `k` of the equator, the unit sphere of
`(ℝ ∙ p)ᗮ`. It is the Mayer–Vietoris connecting morphism of the cover of `S` by the complements of
`p` and `-p`, followed by the homotopy equivalence `TauCeti.equatorHomotopyEquiv` of
`S ∖ {p, -p}` with the equator. -/
def reducedSingularHomologySphereSuccIso (k : ℕ) :
    (reducedSingularHomologyFunctor R (k + 1)).obj (TopCat.of (sphere (0 : E) 1)) ≅
      (reducedSingularHomologyFunctor R k).obj (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) :=
  -- `TauCeti.isIso_reducedMayerVietorisδ_sphere` is a theorem rather than an instance, so it is
  -- supplied to `asIso` explicitly.
  (reducedSingularHomologySuccIso R k).app _ ≪≫
    eqToIso (singularHomologyFunctor_obj_eq_toSSetHomology R (k + 1) _) ≪≫
    @asIso _ _ _ _ (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
      isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg p) k)
      (isIso_reducedMayerVietorisδ_sphere R p k) ≪≫
    (equatorHomotopyEquiv p).reducedSingularHomologyIso R k

/-- The suspension isomorphism is the identification of reduced with ordinary homology in positive
degrees, followed by the reduced Mayer–Vietoris connecting morphism of the cover by the complements
of `p` and `-p`, and by the map induced by radial projection of the orthogonal projection onto
`(ℝ ∙ p)ᗮ`. -/
@[simp]
lemma reducedSingularHomologySphereSuccIso_hom (k : ℕ) :
    (reducedSingularHomologySphereSuccIso R p k).hom =
      (reducedSingularHomologyι R (k + 1)).app _ ≫
        TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
          isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg p) k ≫
        (reducedSingularHomologyFunctor R k).map (TopCat.ofHom (equatorHomotopyEquiv p).toFun) := by
  simp only [reducedSingularHomologySphereSuccIso, Iso.trans_hom, Iso.app_hom,
    reducedSingularHomologySuccIso_hom, ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom]
  simp only [singularHomologyFunctor_obj_eq_toSSetHomology_hom_comp, asIso_hom]
  -- Both remaining compositions use the same `toSSet` homology object definitionally.
  rfl

section Circle

variable {p} (hE : finrank ℝ E = 2) {x : sphere (0 : E) 1}
  (hx : x ∈ ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))

/-- On the unit circle minus `p` and `-p`, the path component of `-x` is the unique path
component other than that of `x`. -/
@[instance_reducible]
private def zerothHomotopyComplUnique :
    Unique {c : ZerothHomotopy ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) //
      c ≠ ZerothHomotopy.mk ⟨x, hx⟩} where
  default := ⟨_, zerothHomotopy_mk_neg_ne_of_finrank_eq_two hE hx⟩
  uniq := by
    rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective c
    exact Subtype.ext ((zerothHomotopy_mk_eq_or_eq_neg_of_finrank_eq_two hE hx y).resolve_left hc)

/-- **The first homology of a circle through its Mayer–Vietoris sequence.** For a point `p` of
the unit circle `S` of a two-dimensional real inner product space, the Mayer–Vietoris connecting
morphism of the cover of `S` by the two open arcs `S ∖ {p}` and `S ∖ {-p}` identifies `H₁(S)`
with the reduced zeroth homology of their intersection, which consists of two open arcs.  For a
point `x` of that intersection, the arcs are the path components of `x` and of `-x`, so this
reduced homology is one copy of the coefficient object, generated by `[-x] - [x]`.  The
connecting morphism therefore sends the generator of `H₁(S)` determined by this isomorphism to
`[-x] - [x]` (`TauCeti.singularHomologySphereOneIso_inv_mayerVietorisδ`). -/
def singularHomologySphereOneIso :
    (TopCat.toSSet.obj (TopCat.of (sphere (0 : E) 1))).homology R 1 ≅ R :=
  haveI := zerothHomotopyComplUnique hE hx
  -- `TauCeti.isIso_reducedMayerVietorisδ_sphere` is a theorem rather than an instance, so it is
  -- supplied to `asIso` explicitly.
  @asIso _ _ _ _ (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
      isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_union_compl_singleton_neg p) 0)
      (isIso_reducedMayerVietorisδ_sphere R p 0) ≪≫
    reducedSingularHomology₀Iso R (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
      ⟨x, hx⟩ ≪≫ coproductUniqueIso _

/-- **The Mayer–Vietoris sequence of a circle covered by two arcs.**  The generator of `H₁(S)`
given by `TauCeti.singularHomologySphereOneIso` is sent by the Mayer–Vietoris connecting morphism
of the cover of `S` by `S ∖ {p}` and `S ∖ {-p}` to the class `[-x] - [x]` in the zeroth homology
of `S ∖ {p, -p}`, the difference of points on its two arcs. -/
@[reassoc]
lemma singularHomologySphereOneIso_inv_mayerVietorisδ :
    (singularHomologySphereOneIso R hE hx).inv ≫
        TopCat.mayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
          isOpen_compl_singleton isOpen_compl_singleton
          (compl_singleton_union_compl_singleton_neg p) 1 0 =
      singularHomology₀Section R
          (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)))
          ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩ -
        singularHomology₀Section R
          (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1))) ⟨x, hx⟩ := by
  have := isIso_reducedMayerVietorisδ_sphere R p 0
  let := zerothHomotopyComplUnique hE hx
  -- The inverse of the reduced connecting morphism, followed by the connecting morphism, is the
  -- inclusion of reduced homology.
  have key : inv (TopCat.reducedMayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
        isOpen_compl_singleton isOpen_compl_singleton
        (compl_singleton_union_compl_singleton_neg p) 0) ≫
      TopCat.mayerVietorisδ R (X := TopCat.of (sphere (0 : E) 1))
        isOpen_compl_singleton isOpen_compl_singleton
        (compl_singleton_union_compl_singleton_neg p) 1 0 =
      (reducedSingularHomologyι R 0).app _ :=
    (IsIso.inv_comp_eq _).2 (TopCat.reducedMayerVietorisδ_comp_ι R _ _ _ 0).symm
  simp only [singularHomologySphereOneIso, Iso.trans_inv, asIso_inv, coproductUniqueIso_inv,
    Category.assoc, key]
  exact ι_reducedSingularHomology₀Iso_inv_ι R (X := TopCat.of ({p}ᶜ ∩ {-p}ᶜ : Set _)) ⟨x, hx⟩
    ⟨-x, neg_mem_compl_singleton_inter_compl_singleton_neg hx⟩
    (zerothHomotopy_mk_neg_ne_of_finrank_eq_two hE hx)

end Circle

section Dimension

/-- **The reduced homology of a sphere vanishes outside its dimension.**  For a real inner product
space `E` of dimension `n + 1`, the reduced singular homology of its unit sphere vanishes in every
degree `k ≠ n`. -/
theorem isZero_reducedSingularHomologyFunctor_sphere_of_ne {n k : ℕ} (h : finrank ℝ E = n + 1)
    (hk : k ≠ n) :
    IsZero ((reducedSingularHomologyFunctor R k).obj (TopCat.of (sphere (0 : E) 1))) := by
  induction n generalizing E k with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
    obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    have : Fact (finrank ℝ E = 0 + 1) := ⟨h⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 0
    have hE : finrank ℝ (ℝ ∙ (p : E))ᗮ = 0 :=
      Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
    have : Subsingleton (ℝ ∙ (p : E))ᗮ := Module.finrank_zero_iff.mp hE
    have : IsEmpty (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
      Set.isEmpty_coe_sort.mpr (sphere_eq_empty_of_subsingleton one_ne_zero)
    exact (isZero_reducedSingularHomologyFunctor_of_isEmpty R
      (TopCat.of (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)) k).of_iso
      (reducedSingularHomologySphereSuccIso R p k)
  | succ n ih =>
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
    obtain ⟨p⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    have : Fact (finrank ℝ E = (n + 1) + 1) := ⟨h⟩
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (n + 1)
    cases k with
    | zero =>
      have : PathConnectedSpace (sphere (0 : E) 1) :=
        isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere (by
          rw [← Module.finrank_eq_rank, h]
          exact_mod_cast (by omega : 1 < n + 1 + 1)) 0 zero_le_one)
      exact isZero_reducedSingularHomologyFunctor_zero R (TopCat.of (sphere (0 : E) 1))
    | succ k =>
      exact (ih (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p))
        (fun hkn ↦ hk (by omega))).of_iso (reducedSingularHomologySphereSuccIso R p k)

/-- The recursion behind `TauCeti.reducedSingularHomologySphereIso`, with the space as an explicit
argument so that it can vary along the induction on the dimension. -/
private def reducedSingularHomologySphereIsoAux :
    (n : ℕ) → (E : Type w) → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] →
      finrank ℝ E = n + 1 →
      ((reducedSingularHomologyFunctor R n).obj (TopCat.of (sphere (0 : E) 1)) ≅ R)
  | 0, E, _, _, h =>
    haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
    haveI := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    reducedSingularHomologySphereZeroIso R h (Classical.arbitrary _)
  | n + 1, E, _, _, h =>
    haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h
    haveI := (NormedSpace.sphere_nonempty (E := E) (x := 0).mpr zero_le_one).coe_sort
    haveI : Fact (finrank ℝ E = (n + 1) + 1) := ⟨h⟩
    let p : sphere (0 : E) 1 := Classical.arbitrary _
    reducedSingularHomologySphereSuccIso R p n ≪≫ reducedSingularHomologySphereIsoAux n _
      (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p))

/-- **The reduced homology of a sphere in its dimension.**  For a real inner product space `E` of
dimension `n + 1`, the reduced singular homology of its unit sphere in degree `n` is one copy of
the coefficient object.  The isomorphism iterates the suspension isomorphism
`TauCeti.reducedSingularHomologySphereSuccIso` along a chosen point of each sphere down to the
zero-sphere `TauCeti.reducedSingularHomologySphereZeroIso`; it depends on these choices, and is
one choice of generator rather than a canonical identification. -/
def reducedSingularHomologySphereIso {n : ℕ} (h : finrank ℝ E = n + 1) :
    (reducedSingularHomologyFunctor R n).obj (TopCat.of (sphere (0 : E) 1)) ≅ R :=
  reducedSingularHomologySphereIsoAux R n E h

/-- For a one-dimensional space, the chosen generator of `H_red₀(S)` is the zero-sphere
isomorphism `TauCeti.reducedSingularHomologySphereZeroIso` at the point `Classical.arbitrary` of
the sphere. -/
@[simp]
lemma reducedSingularHomologySphereIso_zero (h : finrank ℝ E = 0 + 1)
    [Nonempty (sphere (0 : E) 1)] :
    reducedSingularHomologySphereIso R h =
      reducedSingularHomologySphereZeroIso R h (Classical.arbitrary _) := (rfl)

/-- For a space of dimension `n + 2`, the chosen generator of `H_redₙ₊₁(S)` is the suspension
isomorphism at the point `p = Classical.arbitrary` of the sphere, followed by the chosen generator
of the reduced homology of the equator, the unit sphere of `(ℝ ∙ p)ᗮ`.  The dimension hypothesis
`hp` on the equator may be any proof of it. -/
@[simp]
lemma reducedSingularHomologySphereIso_succ {n : ℕ} (h : finrank ℝ E = n + 1 + 1)
    [Nonempty (sphere (0 : E) 1)]
    (hp : finrank ℝ (ℝ ∙ ((Classical.arbitrary (sphere (0 : E) 1) : sphere (0 : E) 1) : E))ᗮ =
      n + 1) :
    reducedSingularHomologySphereIso R h =
      reducedSingularHomologySphereSuccIso R (Classical.arbitrary _) n ≪≫
        reducedSingularHomologySphereIso R hp := (rfl)

end Dimension

section TopCatSphere

/-- **The reduced homology of `TopCat.sphere n` vanishes outside degree `n`.** -/
theorem isZero_reducedSingularHomologyFunctor_topCatSphere_of_ne {n k : ℕ} (hk : k ≠ n) :
    IsZero ((reducedSingularHomologyFunctor R k).obj (TopCat.sphere.{w} n)) :=
  (isZero_reducedSingularHomologyFunctor_sphere_of_ne R (finrank_euclideanSpace_ulift_fin (n + 1))
    hk).of_iso ((diskBoundaryHomeomorph (n + 1)).toHomotopyEquiv.reducedSingularHomologyIso R k)

/-- **The reduced homology of `TopCat.sphere n` in degree `n` is one copy of the coefficient
object.**  This is one choice of generator, transported from
`TauCeti.reducedSingularHomologySphereIso` along `TauCeti.diskBoundaryHomeomorph`. -/
def reducedSingularHomologyTopCatSphereIso (n : ℕ) :
    (reducedSingularHomologyFunctor R n).obj (TopCat.sphere.{w} n) ≅ R :=
  (diskBoundaryHomeomorph (n + 1)).toHomotopyEquiv.reducedSingularHomologyIso R n ≪≫
    reducedSingularHomologySphereIso R (finrank_euclideanSpace_ulift_fin (n + 1))

/-- The chosen generator of `H_redₙ(TopCat.sphere n)` is the map induced by the homeomorphism
`TauCeti.diskBoundaryHomeomorph` with the unit sphere of `EuclideanSpace ℝ (ULift (Fin (n + 1)))`,
followed by the chosen generator `TauCeti.reducedSingularHomologySphereIso` of that sphere. -/
@[simp]
lemma reducedSingularHomologyTopCatSphereIso_hom (n : ℕ) :
    (reducedSingularHomologyTopCatSphereIso R n).hom =
      (reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom (diskBoundaryHomeomorph (n + 1)).toHomotopyEquiv.toFun) ≫
        (reducedSingularHomologySphereIso R (finrank_euclideanSpace_ulift_fin (n + 1))).hom :=
  -- The source object of the composite is `TopCat.sphere n` only up to unfolding, so `simp` and
  -- `rw` cannot apply `Iso.trans_hom` here; the equations are chained as terms instead.
  (Iso.trans_hom _ _).trans
    (congrArg (· ≫ _) (ContinuousMap.HomotopyEquiv.reducedSingularHomologyIso_hom R _ n))

end TopCatSphere

end TauCeti
