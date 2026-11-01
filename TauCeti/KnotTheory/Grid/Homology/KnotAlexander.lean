/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Alexander
public import TauCeti.KnotTheory.Grid.Homology.Finite
public import TauCeti.Algebra.Module.GradedModule.NonTorsionDegree

/-!
# The Alexander grading on knot grid homology over `R[U]`

For a knot grid the Alexander grading of the concrete cycle quotient transports to the
categorical unblocked homology `GH⁻`. The knot module structure identifies the action of `U`
with that of every grid variable. Since each grid variable lowers Alexander degree by one,
so does `U`. Finite generation then bounds above the Alexander degrees containing a
non-torsion class. These are the grading and boundedness properties used to define the
grid concordance invariant from the top non-torsion degree.

Two knot grids, possibly of different sizes, have isomorphic `GH⁻` as Alexander-graded
`R[U]`-modules when some `R[U]`-linear equivalence between their homologies preserves the
Alexander grading (`GridDiagram.IsKnot.UnblockedHomologyIsomorphic`). This relation is reflexive,
symmetric and transitive. The maps that grid moves induce on `GH⁻` are initially packaged as
semilinear maps over the polynomial rings in the grid variables, along a ring homomorphism such as
a renaming of the variables. When that homomorphism commutes with the evaluation `V_j ↦ U`, the
underlying function is `R[U]`-linear, so such a map that is bijective and preserves the Alexander
grading witnesses the relation
(`GridDiagram.IsKnot.UnblockedHomologyIsomorphic.of_semilinearMap`). This is the form in which the
grid-move invariance theorems for `GH⁻` are stated.

The Alexander grading and the convention that `U` has degree `-1` follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 4 and 6.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (R : Type*)
  [CommRing R] [CharP R 2]

/-- The Alexander grading of the `R[U]`-module `GH⁻` of a knot grid. -/
noncomputable def alexanderUnblockedHomologyGrading : InternalGrading R (G.unblockedHomology R) :=
  (hG.toOddComponentGridDiagram).alexanderUnblockedHomologyGrading R

/-- Membership in a knot grid's Alexander piece is membership in the corresponding piece of
the concrete cycle quotient. -/
@[simp]
theorem mem_alexanderUnblockedHomologyGrading_piece_iff (a : ℤ)
    (y : G.unblockedHomology R) :
    y ∈ (hG.alexanderUnblockedHomologyGrading R).piece a ↔
      (G.unblockedHomologyIso R).hom y ∈
        ((hG.toOddComponentGridDiagram).alexanderHomologyGrading R).piece a :=
  (hG.toOddComponentGridDiagram).mem_alexanderUnblockedHomologyGrading_piece_iff R a y

/-- Multiplication by `U` lowers the Alexander grading of knot grid homology by one. -/
theorem X_smul_mem_alexanderUnblockedHomologyGrading_piece {a : ℤ}
    {y : G.unblockedHomology R}
    (hy : y ∈ (hG.alexanderUnblockedHomologyGrading R).piece a) :
    letI := hG.unblockedHomologyModule R
    (Polynomial.X : Polynomial R) • y ∈
      (hG.alexanderUnblockedHomologyGrading R).piece (a - 1) := by
  let _ := hG.unblockedHomologyModule R
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  rw [hG.X_smul_unblockedHomology i y]
  exact (hG.toOddComponentGridDiagram).X_smul_mem_alexanderUnblockedHomologyGrading_piece R i hy

/-- The Alexander degrees containing a non-torsion class of `GH⁻` are bounded above. -/
theorem bddAbove_nonTorsionDegrees_alexanderUnblockedHomologyGrading
    [IsNoetherianRing R] :
    letI := hG.unblockedHomologyModule R
    BddAbove (hG.alexanderUnblockedHomologyGrading R).nonTorsionDegrees := by
  let _ := hG.unblockedHomologyModule R
  exact @InternalGrading.bddAbove_nonTorsionDegrees R (G.unblockedHomology R)
    _ _ _ _ hG.isScalarTower_unblockedHomology
    (hG.alexanderUnblockedHomologyGrading R) 1
    (hG.finite_unblockedHomology (G := G) R) (fun {p} {y} hy => by
      exact hG.X_smul_mem_alexanderUnblockedHomologyGrading_piece R hy)

end GridDiagram.IsKnot

/-! ### Isomorphism of graded homologies -/

namespace GridDiagram.IsKnot

variable {n m l : ℕ} {G : GridDiagram n} {G' : GridDiagram m} {G'' : GridDiagram l}
  (hG : G.IsKnot) (hG' : G'.IsKnot) (hG'' : G''.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

/-- The unblocked grid homologies of two knot grids are **isomorphic as Alexander-graded
`R[U]`-modules**: some `R[U]`-linear equivalence `GH⁻(G) ≃ GH⁻(G')` maps each Alexander piece into
the piece of the same degree. The two grids may have different sizes. -/
def UnblockedHomologyIsomorphic : Prop :=
  letI := hG.unblockedHomologyModule R
  letI := hG'.unblockedHomologyModule R
  ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
    LinearMap.IsHomogeneous e.toLinearMap (hG.alexanderUnblockedHomologyGrading R).piece
      (hG'.alexanderUnblockedHomologyGrading R).piece 0

/-- Every knot grid has `GH⁻` isomorphic to itself. -/
theorem UnblockedHomologyIsomorphic.refl : hG.UnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  exact ⟨LinearEquiv.refl _ _, LinearMap.isHomogeneous_id _⟩

variable {hG hG' hG'' R}

/-- Unfold `UnblockedHomologyIsomorphic` to the existence of a graded equivalence. -/
theorem unblockedHomologyIsomorphic_def :
    hG.UnblockedHomologyIsomorphic hG' R ↔
      letI := hG.unblockedHomologyModule R
      letI := hG'.unblockedHomologyModule R
      ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
        LinearMap.IsHomogeneous e.toLinearMap (hG.alexanderUnblockedHomologyGrading R).piece
          (hG'.alexanderUnblockedHomologyGrading R).piece 0 :=
  Iff.rfl

/-- Equal knot grids have isomorphic `GH⁻`. This transports the relation along a propositional
equation of diagrams, such as one between two descriptions of a moved diagram. -/
theorem unblockedHomologyIsomorphic_of_eq {G₁ : GridDiagram n} {hG₁ : G₁.IsKnot} (h : G = G₁) :
    hG.UnblockedHomologyIsomorphic hG₁ R := by
  subst h
  exact .refl hG R

/-- Isomorphism of graded homologies is symmetric: the inverse of a graded equivalence is graded. -/
theorem UnblockedHomologyIsomorphic.symm (h : hG.UnblockedHomologyIsomorphic hG' R) :
    hG'.UnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, he.linearEquiv_symm⟩

/-- Isomorphism of graded homologies is transitive: graded equivalences compose. -/
theorem UnblockedHomologyIsomorphic.trans (h : hG.UnblockedHomologyIsomorphic hG' R)
    (h' : hG'.UnblockedHomologyIsomorphic hG'' R) : hG.UnblockedHomologyIsomorphic hG'' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  let _ := hG''.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', by simpa only [LinearEquiv.coe_trans, add_zero] using he'.comp he⟩

/-- Isomorphism of graded homologies holds in one direction exactly when it holds in the other. -/
theorem unblockedHomologyIsomorphic_comm :
    hG.UnblockedHomologyIsomorphic hG' R ↔ hG'.UnblockedHomologyIsomorphic hG R :=
  ⟨.symm, .symm⟩

/-- A bijection between the unblocked homologies of two knot grids makes them isomorphic as
Alexander-graded `R[U]`-modules if it preserves the Alexander grading and is semilinear along a
ring homomorphism `σ` of the polynomial rings that commutes with the evaluation `V_j ↦ U`, such as
a renaming of the variables. -/
theorem UnblockedHomologyIsomorphic.of_semilinearMap
    {σ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin m) R}
    (hσ : ∀ p, MvPolynomial.aeval (fun _ ↦ (Polynomial.X : Polynomial R)) (σ p) =
      MvPolynomial.aeval (fun _ ↦ (Polynomial.X : Polynomial R)) p)
    (f : G.unblockedHomology R →ₛₗ[σ] G'.unblockedHomology R) (hf : Function.Bijective f)
    (hA : ∀ a y, y ∈ (hG.alexanderUnblockedHomologyGrading R).piece a →
      f y ∈ (hG'.alexanderUnblockedHomologyGrading R).piece a) :
    hG.UnblockedHomologyIsomorphic hG' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩⟩
  let f' : G.unblockedHomology R →ₗ[Polynomial R] G'.unblockedHomology R :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun q y ↦ by
        obtain ⟨p, rfl⟩ := MvPolynomial.aeval_const_X_surjective (Fin n) R q
        rw [hG.aeval_smul_unblockedHomology, LinearMap.map_smulₛₗ, RingHom.id_apply, ← hσ,
          hG'.aeval_smul_unblockedHomology] }
  refine ⟨LinearEquiv.ofBijective f' hf, LinearMap.isHomogeneous_def.mpr fun a y hy ↦ ?_⟩
  rw [add_zero]
  exact hA a y hy

end GridDiagram.IsKnot

end TauCeti
