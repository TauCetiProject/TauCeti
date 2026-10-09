/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex
public import Mathlib.Topology.Homotopy.Basic

/-!
# Gluing homotopies on weak realizations

A family on a weak realization, with a locally compact parameter space, is jointly continuous
if and only if its restrictions to all closed simplex cylinders are continuous. The same
criterion holds on the actual polyhedron of a precomplex, with the subspace topology, even
when that precomplex omits vertices.

Compatible homotopies on the closed simplices therefore glue to a homotopy on the entire
realization. The computation rule on each simplex also detects whether the glued homotopy
fixes a subcomplex. These results permit simplex deformations to extend over infinite
complexes without imposing a finite or locally finite triangulation.

The product topology is essential here: continuity separately in time and space would not
suffice. We use Mathlib's quotient-map product lifting theorem, which requires local
compactness only of the parameter space, and the final topology of the closed simplices.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2--3 (weak polyhedra and geometric simplicial collapse).
-/

public section

noncomputable section

open Set Topology TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} {K : AbstractSimplicialComplex ι}
  {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

/-- The closed simplices present the weak realization as a quotient of their disjoint union. -/
theorem isQuotientMap_sigma_faceInclusion (K : AbstractSimplicialComplex ι) :
    IsQuotientMap (fun p : Σ σ : Face K, StandardSimplex σ.1 => faceInclusion K p.1 p.2) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨?_, fun s => ?_⟩
  · intro x
    exact ⟨⟨carrier K x, ⟨x.1, mem_convexHull_carrier K x⟩⟩,
      Subtype.ext (faceInclusion_val _ _ _)⟩
  · rw [isClosed_iff_faceInclusion, isClosed_sigma_iff]
    rfl

/-- Joint continuity with a locally compact parameter can be checked on closed simplex
cylinders. Neither the realization nor the vertex type needs to be locally compact or finite. -/
theorem continuous_prod_iff_faceInclusion [LocallyCompactSpace P]
    {f : P × Realization K → X} :
    Continuous f ↔ ∀ σ : Face K,
      Continuous (fun p : P × StandardSimplex σ.1 => f (p.1, faceInclusion K σ p.2)) := by
  constructor
  · intro hf σ
    exact hf.comp (continuous_id.prodMap (continuous_faceInclusion K σ))
  · intro hf
    apply (isQuotientMap_sigma_faceInclusion K).continuous_lift_prod_right
    -- Swap the factors and distribute the simplex sum to apply the sum continuity criterion.
    let e := Homeomorph.sigmaProdDistrib (X := fun σ : Face K => StandardSimplex σ.1)
      (Y := P)
    have hc : Continuous (fun p : Σ σ : Face K, StandardSimplex σ.1 × P =>
        f (p.2.2, faceInclusion K p.1 p.2.1)) :=
      continuous_sigma fun σ => (hf σ).comp continuous_swap
    exact hc.comp (e.continuous.comp continuous_swap)

/-- The simplices of a precomplex present its actual polyhedron as a quotient, including
when the precomplex has no faces or omits ambient vertices. -/
theorem isQuotientMap_sigma_subtype_faceInclusion {L : PreAbstractSimplicialComplex ι}
    (hL : L ≤ K.toPreAbstractSimplicialComplex) :
    IsQuotientMap (fun p : Σ σ : L.faces, StandardSimplex σ.1 =>
      (⟨faceInclusion K ⟨p.1.1, hL p.1.2⟩ p.2,
        support_faceInclusion_mem hL p.1.2 p.2⟩ : {x : Realization K // x.1.support ∈ L})) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨?_, fun s => ?_⟩
  · intro x
    exact ⟨⟨⟨x.1.1.support, x.2⟩, ⟨x.1.1, by
      simpa only [carrier_val] using mem_convexHull_carrier K x.1⟩⟩,
      Subtype.ext (Subtype.ext (faceInclusion_val _ _ _))⟩
  · constructor
    · intro hs
      apply isClosed_sigma_iff.mpr
      intro σ
      have hcont : Continuous (fun x : StandardSimplex σ.1 =>
          (⟨faceInclusion K ⟨σ.1, hL σ.2⟩ x, support_faceInclusion_mem hL σ.2 x⟩ :
            {x : Realization K // x.1.support ∈ L})) :=
        (continuous_faceInclusion K ⟨σ.1, hL σ.2⟩).subtype_mk _
      exact hs.preimage hcont
    · intro hs
      rw [(isClosed_setOf_support_mem hL).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed]
      apply isClosed_of_faceInclusion hL
      · rintro x ⟨y, hy, rfl⟩
        exact y.2
      · intro σ hσ
        convert (isClosed_sigma_iff.mp hs) ⟨σ, hσ⟩ using 1
        ext x
        constructor
        · rintro ⟨y, hy, hxy⟩
          have he : y = ⟨faceInclusion K ⟨σ, hL hσ⟩ x,
              support_faceInclusion_mem hL hσ x⟩ := Subtype.ext hxy
          simpa only [he, mem_preimage] using hy
        · intro hx
          exact ⟨⟨faceInclusion K ⟨σ, hL hσ⟩ x,
            support_faceInclusion_mem hL hσ x⟩, hx, rfl⟩

/-- Joint continuity on a precomplex polyhedron is detected on its closed simplex cylinders,
with a locally compact parameter space and the ambient weak subspace topology. -/
theorem continuous_prod_subtype_iff_faceInclusion [LocallyCompactSpace P]
    {L : PreAbstractSimplicialComplex ι} (hL : L ≤ K.toPreAbstractSimplicialComplex)
    {f : P × {x : Realization K // x.1.support ∈ L} → X} :
    Continuous f ↔ ∀ (σ : Finset ι) (hσ : σ ∈ L),
      Continuous (fun p : P × StandardSimplex σ =>
        f (p.1, ⟨faceInclusion K ⟨σ, hL hσ⟩ p.2,
          support_faceInclusion_mem hL hσ p.2⟩)) := by
  constructor
  · intro hf σ hσ
    exact hf.comp (continuous_id.prodMap
      ((continuous_faceInclusion K ⟨σ, hL hσ⟩).subtype_mk
        (support_faceInclusion_mem hL hσ)))
  · intro hf
    apply (isQuotientMap_sigma_subtype_faceInclusion hL).continuous_lift_prod_right
    let e := Homeomorph.sigmaProdDistrib (X := fun σ : L.faces => StandardSimplex σ.1)
      (Y := P)
    have hc : Continuous (fun p : Σ σ : L.faces, StandardSimplex σ.1 × P =>
        f (p.2.2, ⟨faceInclusion K ⟨p.1.1, hL p.1.2⟩ p.2.1,
          support_faceInclusion_mem hL p.1.2 p.2.1⟩)) :=
      continuous_sigma fun σ => (hf σ.1 σ.2).comp continuous_swap
    exact hc.comp (e.continuous.comp continuous_swap)

variable (K) {f₀ f₁ : C(Realization K, X)}
  (H : ∀ σ : Face K,
    (f₀.comp ⟨faceInclusion K σ, continuous_faceInclusion K σ⟩).Homotopy
      (f₁.comp ⟨faceInclusion K σ, continuous_faceInclusion K σ⟩))
  (hH : ∀ (σ τ : Face K) (x : StandardSimplex σ.1) (y : StandardSimplex τ.1),
    faceInclusion K σ x = faceInclusion K τ y →
      ∀ t : unitInterval, H σ (t, x) = H τ (t, y))

/-- Glue homotopies on all closed simplices, provided they agree wherever their face maps
have the same image. The endpoint maps are the given global continuous maps. -/
def homotopyOfFaces : f₀.Homotopy f₁ where
  toFun p := H (carrier K p.2) (p.1, ⟨p.2.1, mem_convexHull_carrier K p.2⟩)
  continuous_toFun := by
    apply continuous_prod_iff_faceInclusion.mpr
    intro σ
    exact (H σ).continuous_toFun.congr fun p =>
      hH σ (carrier K (faceInclusion K σ p.2)) p.2
        ⟨_, mem_convexHull_carrier K _⟩
        (Subtype.ext (by simp only [faceInclusion_val])) p.1
  map_zero_left x := by
    simp only [ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply]
    exact congrArg f₀ (Subtype.ext (faceInclusion_val _ _ _))
  map_one_left x := by
    simp only [ContinuousMap.Homotopy.apply_one, ContinuousMap.comp_apply]
    exact congrArg f₁ (Subtype.ext (faceInclusion_val _ _ _))

/-- The glued homotopy agrees with the specified homotopy on every closed simplex. -/
@[simp]
theorem homotopyOfFaces_apply_faceInclusion
    (σ : Face K) (t : unitInterval) (x : StandardSimplex σ.1) :
    homotopyOfFaces K H hH (t, faceInclusion K σ x) = H σ (t, x) := by
  exact hH (carrier K (faceInclusion K σ x)) σ
    ⟨_, mem_convexHull_carrier K _⟩ x
    (Subtype.ext (by simp only [faceInclusion_val])) t

/-- A homotopy with the given restrictions on all closed simplices is the glued homotopy. -/
theorem homotopyOfFaces_unique (G : f₀.Homotopy f₁)
    (hG : ∀ (σ : Face K) (t : unitInterval) (x : StandardSimplex σ.1),
      G (t, faceInclusion K σ x) = H σ (t, x)) : G = homotopyOfFaces K H hH := by
  ext ⟨t, x⟩
  have hx : faceInclusion K (carrier K x) ⟨x.1, mem_convexHull_carrier K x⟩ = x :=
    Subtype.ext (faceInclusion_val _ _ _)
  rw [← hx, homotopyOfFaces_apply_faceInclusion]
  exact hG _ _ _

variable {S : Set (Realization K)}
  (hfix : ∀ (σ : Face K) (t : unitInterval) (x : StandardSimplex σ.1),
    faceInclusion K σ x ∈ S → H σ (t, x) = f₀ (faceInclusion K σ x))

/-- Glue simplex homotopies which fix the traces of `S` to a homotopy relative to `S`.
In particular, `S` may be the retained polyhedron of a simplicial collapse. -/
def homotopyRelOfFaces : f₀.HomotopyRel f₁ S where
  toHomotopy := homotopyOfFaces K H hH
  prop' t x hx := by
    have hfixed : homotopyOfFaces K H hH (t, x) = f₀ x := by
      have he : faceInclusion K (carrier K x) ⟨x.1, mem_convexHull_carrier K x⟩ = x :=
        Subtype.ext (faceInclusion_val _ _ _)
      rw [← he, homotopyOfFaces_apply_faceInclusion]
      exact hfix _ _ _ (he.symm ▸ hx)
    exact hfixed

/-- The relative glued homotopy agrees with the specified homotopy on each closed simplex. -/
@[simp]
theorem homotopyRelOfFaces_apply_faceInclusion
    (σ : Face K) (t : unitInterval) (x : StandardSimplex σ.1) :
    homotopyRelOfFaces K H hH hfix (t, faceInclusion K σ x) = H σ (t, x) :=
  homotopyOfFaces_apply_faceInclusion K H hH σ t x

end AbstractSimplicialComplex
