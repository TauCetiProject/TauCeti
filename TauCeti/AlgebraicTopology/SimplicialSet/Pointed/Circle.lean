module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# The simplicial circle

This file constructs the simplicial circle as the quotient of the standard simplicial interval
by its boundary. Concretely, it is the pushout of the boundary inclusion
`∂Δ[1] ⟶ Δ[1]` along the unique map `∂Δ[1] ⟶ Δ[0]`.

The quotient map and its basepoint satisfy the expected endpoint equations. The type
`SimplicialCircle.MappingData X` packages a simplicial interval in `X` with equal endpoints,
and `SimplicialCircle.homEquiv` gives the universal property in that form. The equivalent
coequalizer formulation is `SimplicialCircle.coforkIsColimit`. These APIs allow the circle to be
used as a pointed simplicial set without unfolding its chosen pushout.
-/

public section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace TauCeti

namespace SimplicialCircle

/-- The map which collapses the boundary of the simplicial interval to `Δ[0]`. -/
def boundaryCollapse : (SSet.boundary 1 : SSet.{u}) ⟶ Δ[0] :=
  SSet.stdSimplex.isTerminalObj₀.from _

end SimplicialCircle

/-- The simplicial circle `Δ[1]/∂Δ[1]`, formed as a pushout in simplicial sets. -/
noncomputable def simplicialCircle : SSet.{u} :=
  pushout (SSet.boundary 1).ι SimplicialCircle.boundaryCollapse

namespace SimplicialCircle

/-- The quotient map from the simplicial interval to the simplicial circle. -/
noncomputable def quotient : Δ[1] ⟶ simplicialCircle.{u} :=
  pushout.inl _ _

/-- The distinguished vertex of the simplicial circle. -/
noncomputable def basepoint : Δ[0] ⟶ simplicialCircle.{u} :=
  pushout.inr _ _

/-- The quotient map agrees with the basepoint after collapsing the boundary. -/
@[reassoc]
lemma boundary_quotient :
    (SSet.boundary 1).ι ≫ quotient.{u} = boundaryCollapse ≫ basepoint :=
  pushout.condition

/-- Both vertices of the simplicial interval map to the basepoint of the circle. -/
@[reassoc]
lemma vertex_quotient (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ quotient.{u} = basepoint := by
  have hi : SSet.boundary.ι i ≫ boundaryCollapse = 𝟙 Δ[0] :=
    SSet.stdSimplex.ext₀
  rw [← SSet.boundary.ι_ι i, Category.assoc, boundary_quotient,
    ← Category.assoc, hi, Category.id_comp]

/-- Descend a simplicial interval whose two vertices are a specified point through the circle. -/
noncomputable def desc {X : SSet.{u}} (f : Δ[1] ⟶ X)
    (x : X.obj (op (SimplexCategory.mk 0)))
    (h : ∀ i : Fin 2, SSet.stdSimplex.δ i ≫ f = SSet.const x) :
    simplicialCircle ⟶ X :=
  pushout.desc f (SSet.const x) (by
    apply SSet.boundary.hom_ext
    intro i
    rw [← Category.assoc, SSet.boundary.ι_ι, h i]
    have hi : SSet.boundary.ι i ≫ boundaryCollapse = 𝟙 Δ[0] :=
      SSet.stdSimplex.ext₀
    rw [← Category.assoc, hi, Category.id_comp])

/-- The descended map restricts to the original map on the simplicial interval. -/
@[reassoc (attr := simp)]
lemma quotient_desc {X : SSet.{u}} (f : Δ[1] ⟶ X)
    (x : X.obj (op (SimplexCategory.mk 0)))
    (h : ∀ i : Fin 2, SSet.stdSimplex.δ i ≫ f = SSet.const x) :
    quotient ≫ desc f x h = f :=
  pushout.inl_desc _ _ _

/-- The descended map sends the circle's basepoint to the specified point. -/
@[reassoc (attr := simp)]
lemma basepoint_desc {X : SSet.{u}} (f : Δ[1] ⟶ X)
    (x : X.obj (op (SimplexCategory.mk 0)))
    (h : ∀ i : Fin 2, SSet.stdSimplex.δ i ≫ f = SSet.const x) :
    basepoint ≫ desc f x h = SSet.const x :=
  pushout.inr_desc _ _ _

/-- Maps from the simplicial circle are determined by their composites with the quotient map. -/
@[ext]
lemma hom_ext {X : SSet.{u}} {f g : simplicialCircle ⟶ X}
    (h : quotient ≫ f = quotient ≫ g) : f = g := by
  apply pushout.hom_ext
  · exact h
  · change basepoint ≫ f = basepoint ≫ g
    rw [← vertex_quotient 0, Category.assoc, Category.assoc, h]

/-- The map obtained by `desc` is the unique extension of its interval map. -/
lemma desc_unique {X : SSet.{u}} (f : Δ[1] ⟶ X)
    (x : X.obj (op (SimplexCategory.mk 0)))
    (h : ∀ i : Fin 2, SSet.stdSimplex.δ i ≫ f = SSet.const x)
    (g : simplicialCircle ⟶ X) (hg : quotient ≫ g = f) :
    g = desc f x h := by
  apply hom_ext
  simpa using hg

private lemma vertex_eq_const_of_eq {X : SSet.{u}} (f : Δ[1] ⟶ X)
    (h : SSet.stdSimplex.δ 0 ≫ f = SSet.stdSimplex.δ 1 ≫ f) (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ f =
      SSet.const (SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ f)) := by
  fin_cases i
  · rw [← SSet.yonedaEquiv_symm_zero]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  · change SSet.stdSimplex.δ (1 : Fin 2) ≫ f = _
    rw [← h, ← SSet.yonedaEquiv_symm_zero]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm

/-- A simplicial interval in `X` whose two endpoints agree. -/
@[ext]
structure MappingData (X : SSet.{u}) where
  /-- The interval in `X`. -/
  interval : Δ[1] ⟶ X
  /-- The two vertices of the interval agree. -/
  vertex_eq : SSet.stdSimplex.δ 0 ≫ interval = SSet.stdSimplex.δ 1 ≫ interval

/-- The common endpoint of circle mapping data. -/
def MappingData.point {X : SSet.{u}} (d : MappingData X) :
    X.obj (op (SimplexCategory.mk 0)) :=
  SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ d.interval)

/-- Either vertex of the interval underlying circle mapping data is its common endpoint. -/
lemma MappingData.vertex_interval {X : SSet.{u}} (d : MappingData X) (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ d.interval = SSet.const d.point :=
  vertex_eq_const_of_eq d.interval d.vertex_eq i

/-- Postcompose mapping data with a morphism of simplicial sets. -/
def MappingData.map {X Y : SSet.{u}} (d : MappingData X) (f : X ⟶ Y) : MappingData Y where
  interval := d.interval ≫ f
  vertex_eq := by rw [← Category.assoc, d.vertex_eq, Category.assoc]

/-- Postcomposition carries the common endpoint to the common endpoint. -/
@[simp]
lemma MappingData.point_map {X Y : SSet.{u}} (d : MappingData X) (f : X ⟶ Y) :
    (d.map f).point = f.app _ d.point :=
  SSet.yonedaEquiv_comp _ _

/-- Postcomposition of circle mapping data by the identity changes nothing. -/
@[simp]
lemma MappingData.map_id {X : SSet.{u}} (d : MappingData X) : d.map (𝟙 X) = d := by
  apply MappingData.ext
  simp [MappingData.map]

/-- Postcomposition of circle mapping data respects composition. -/
@[simp]
lemma MappingData.map_comp {X Y Z : SSet.{u}} (d : MappingData X)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (d.map f).map g = d.map (f ≫ g) := by
  apply MappingData.ext
  simp [MappingData.map]

/-- Maps from the simplicial circle to `X` are equivalent to intervals in `X` with equal
endpoints, together with their common endpoint. -/
noncomputable def homEquiv (X : SSet.{u}) :
    (simplicialCircle ⟶ X) ≃ MappingData X where
  toFun g :=
    { interval := quotient ≫ g
      vertex_eq := by
        calc
          SSet.stdSimplex.δ 0 ≫ quotient ≫ g = basepoint ≫ g := by
            rw [← Category.assoc, vertex_quotient]
          _ = SSet.stdSimplex.δ 1 ≫ quotient ≫ g := by
            rw [← Category.assoc, vertex_quotient] }
  invFun p := desc p.interval p.point p.vertex_interval
  left_inv g := by
    apply hom_ext
    simp
  right_inv p := by
    ext
    simp

/-- The universal equivalence for the circle is natural under postcomposition. -/
lemma homEquiv_naturality {X Y : SSet.{u}} (f : simplicialCircle ⟶ X) (g : X ⟶ Y) :
    homEquiv Y (f ≫ g) = (homEquiv X f).map g := by
  apply MappingData.ext
  simp [homEquiv, MappingData.map, Category.assoc]

/-- The cofork expressing the simplicial circle as the coequalizer of the two interval vertices. -/
noncomputable def cofork :
    Cofork (SSet.stdSimplex.δ (0 : Fin 2)) (SSet.stdSimplex.δ (1 : Fin 2)) :=
  Cofork.ofπ quotient (by rw [vertex_quotient, vertex_quotient])

/-- The simplicial circle is the coequalizer of the two vertex inclusions into `Δ[1]`. -/
noncomputable def coforkIsColimit : IsColimit cofork :=
  Cofork.IsColimit.mk cofork
    (fun s ↦ desc s.π (SSet.yonedaEquiv (SSet.stdSimplex.δ 0 ≫ s.π))
      (vertex_eq_const_of_eq s.π s.condition))
    (fun s ↦ quotient_desc s.π _ (vertex_eq_const_of_eq s.π s.condition))
    (fun s m hm ↦ desc_unique s.π _ (vertex_eq_const_of_eq s.π s.condition) m hm)

noncomputable instance : Epi quotient :=
  Cofork.IsColimit.epi coforkIsColimit

end SimplicialCircle

end TauCeti
