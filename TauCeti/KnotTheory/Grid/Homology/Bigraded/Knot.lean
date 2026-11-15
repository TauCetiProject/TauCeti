/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Coarsen
public import TauCeti.KnotTheory.Grid.Homology.KnotAlexander
public import TauCeti.KnotTheory.Grid.Homology.Tau
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.KnotTheory.Grid.Homology.Bigraded.Finite

/-!
# The Maslov--Alexander bigrading on knot grid homology over `R[U]`

For a knot grid `G`, the `(O-Maslov, Alexander)` bigrading of `GH⁻(G)` equips the `R[U]`-module
`G.unblockedHomology R` with an internal `ℤ × ℤ`-grading over `R`
(`GridDiagram.IsKnot.bigradedUnblockedHomologyGrading`). Under the knot module structure every grid
variable acts as `U`, so multiplication by `U` lowers bidegree by `(2, 1)`
(`GridDiagram.IsKnot.X_smul_mem_bigradedUnblockedHomologyGrading_piece`). Projecting bidegrees onto
their second coordinate recovers `GridDiagram.IsKnot.alexanderUnblockedHomologyGrading`.

On any grid diagram with an odd number of components whose `X`-marking state receives an even
number of counted rectangles from every grid state, each monomial multiple `V^e • λ⁻` witnesses
positive ground-ring `finrank` in bidegree `bidegree X - (2 |e|, |e|)` over a Noetherian ring of
characteristic two (`OddComponentGridDiagram.finrank_bigradedUnblockedHomologyPiece_pos`), giving a
positive-`finrank` `U`-tower on knot grids
(`GridDiagram.IsKnot.finrank_bigradedUnblockedHomologyGrading_piece_pos`).

Two knot grids, possibly of different sizes, have isomorphic `GH⁻` as Maslov--Alexander bigraded
`R[U]`-modules (`GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`) when some `R[U]`-linear
equivalence between their homologies preserves bidegrees. Coarsening along `Prod.snd` shows that
every bigraded `R[U]`-isomorphism is in particular an Alexander-graded `R[U]`-isomorphism
(`BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic`), and restricting to each
bidegree gives `R`-linear equivalences on all homogeneous pieces
(`BigradedUnblockedHomologyIsomorphic.nonempty_piece_linearEquiv`), hence equal piece `finrank`s
(`BigradedUnblockedHomologyIsomorphic.finrank_piece_eq`).

Adapting the Alexander-graded isomorphism API `GridDiagram.IsKnot.UnblockedHomologyIsomorphic` and
`GridDiagram.IsKnot.UnblockedHomologyIsomorphic.of_semilinearMap` in
`TauCeti.KnotTheory.Grid.Homology.KnotAlexander`, grid-move maps that are bijective,
bidegree-preserving, and semilinear along a polynomial ring homomorphism commuting with the
specialization `V_j ↦ U` witness the bigraded isomorphism
(`BigradedUnblockedHomologyIsomorphic.of_semilinearMap`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3, 4.6 and Chapters 5
and 6. The bigraded `R[U]`-isomorphism relation closely adapts
`TauCeti.KnotTheory.Grid.Homology.KnotAlexander` (`GridDiagram.IsKnot.UnblockedHomologyIsomorphic`
and `GridDiagram.IsKnot.UnblockedHomologyIsomorphic.of_semilinearMap`).
-/

public section

open MvPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

/-- On a grid diagram with an odd number of link components, the class of the `X`-marking state is
homogeneous of bidegree `(M_O(G.1.X), A(G.1.X))`. -/
theorem XMarkingClass_mem_bigradedUnblockedHomologyPiece {n : ℕ}
    (G : OddComponentGridDiagram n) (R : Type*) [CommRing R] [CharP R 2] :
    G.1.XMarkingClass R ∈ G.bigradedUnblockedHomologyPiece R (G.bidegree G.1.X) := by
  rw [G.1.XMarkingClass_def]
  refine G.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R ?_
  rw [G.1.coe_XMarkingCycle]
  exact G.single_one_mem_bigradedChainMinusPiece R G.1.X

/-- On an odd-component grid diagram whose `X`-marking state receives an even number of counted
rectangles from every grid state, every monomial multiple `V^e • λ⁻` witnesses positive `finrank`
in bidegree `bidegree X - (2 |e|, |e|)` over any Noetherian commutative ring of characteristic
two. -/
theorem finrank_bigradedUnblockedHomologyPiece_pos {n : ℕ} (G : OddComponentGridDiagram n)
    (K : Type*) [CommRing K] [CharP K 2] [IsNoetherianRing K]
    (hX : ∀ x : GridState n, Even (G.1.unblockedRectangles x G.1.X).card) (e : Fin n →₀ ℕ) :
    0 < Module.finrank K
      (G.bigradedUnblockedHomologyPiece K
        (G.bidegree G.1.X - (2 * (e.degree : ℤ), (e.degree : ℤ)))) := by
  have : Nontrivial K := CharP.nontrivial_of_char_ne_one (v := 2) (by decide)
  have hmem : (monomial e (1 : K)) • G.1.XMarkingClass K ∈
      G.bigradedUnblockedHomologyPiece K
        (G.bidegree G.1.X - (2 * (e.degree : ℤ), (e.degree : ℤ))) :=
    G.monomial_smul_mem_bigradedUnblockedHomologyPiece K e 1
      (G.XMarkingClass_mem_bigradedUnblockedHomologyPiece K)
  have hinj : Function.Injective (LinearMap.toSpanSingleton K
      (G.bigradedUnblockedHomologyPiece K
        (G.bidegree G.1.X - (2 * (e.degree : ℤ), (e.degree : ℤ))))
      ⟨(monomial e (1 : K)) • G.1.XMarkingClass K, hmem⟩) := by
    intro r₁ r₂ hr
    have hr' : (monomial e (r₁ - r₂) : MvPolynomial (Fin n) K) • G.1.XMarkingClass K = 0 := by
      have hval : (r₁ - r₂) • ((monomial e (1 : K)) • G.1.XMarkingClass K) = 0 := by
        have hcoe := congrArg Subtype.val hr
        simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul] at hcoe
        rwa [sub_smul, sub_eq_zero]
      rwa [← algebraMap_smul (MvPolynomial (Fin n) K), smul_smul, algebraMap_eq,
        C_mul_monomial, mul_one] at hval
    exact sub_eq_zero.mp (G.1.eq_zero_of_monomial_smul_XMarkingClass_eq_zero K hX hr')
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hle
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one hle

end OddComponentGridDiagram

namespace GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (R : Type*)
  [CommRing R] [CharP R 2]

/-- The internal `(O-Maslov, Alexander)` bigrading of the `R[U]`-module `GH⁻` of a knot grid. -/
noncomputable def bigradedUnblockedHomologyGrading :
    InternalGrading R (G.unblockedHomology R) (ℤ × ℤ) :=
  hG.toOddComponentGridDiagram.bigradedUnblockedHomologyGrading R

/-- The degree-`g` piece of a knot grid's bigrading is `bigradedUnblockedHomologyPiece`. -/
@[simp]
theorem bigradedUnblockedHomologyGrading_piece (g : ℤ × ℤ) :
    (hG.bigradedUnblockedHomologyGrading R).piece g =
      hG.toOddComponentGridDiagram.bigradedUnblockedHomologyPiece R g := by
  rw [bigradedUnblockedHomologyGrading,
    OddComponentGridDiagram.bigradedUnblockedHomologyGrading_piece]

/-- Over a Noetherian commutative ring of characteristic two, each homogeneous piece of a knot
grid's bundled bigrading on `GH⁻` is finitely generated over the ground ring. -/
instance finite_bigradedUnblockedHomologyGrading_piece [IsNoetherianRing R] (g : ℤ × ℤ) :
    Module.Finite R ((hG.bigradedUnblockedHomologyGrading R).piece g) := by
  rw [bigradedUnblockedHomologyGrading_piece]
  exact hG.toOddComponentGridDiagram.finite_bigradedUnblockedHomologyPiece R g

/-- The degree-`g` piece of a knot grid's bigrading agrees with `bigradedUnblockedHomologyPiece`
computed with any odd-component witness on the same underlying diagram. -/
theorem bigradedUnblockedHomologyGrading_piece_eq_mk
    (hodd : Odd G.componentCount) (g : ℤ × ℤ) :
    (hG.bigradedUnblockedHomologyGrading R).piece g =
      OddComponentGridDiagram.bigradedUnblockedHomologyPiece ⟨G, hodd⟩ R g := by
  rw [bigradedUnblockedHomologyGrading_piece]

/-- Coarsening a knot grid's `(O-Maslov, Alexander)` bigrading along `Prod.snd` recovers its
Alexander grading. -/
@[simp]
theorem coarsen_bigradedUnblockedHomologyGrading_snd :
    (hG.bigradedUnblockedHomologyGrading R).coarsen Prod.snd =
      hG.alexanderUnblockedHomologyGrading R := by
  refine InternalGrading.ext fun a ↦ Submodule.ext fun y ↦ ?_
  rw [bigradedUnblockedHomologyGrading,
    hG.toOddComponentGridDiagram.coarsen_bigradedUnblockedHomologyGrading_snd,
    mem_alexanderUnblockedHomologyGrading_piece_iff,
    OddComponentGridDiagram.mem_alexanderUnblockedHomologyGrading_piece_iff]

/-- Multiplication by `U` lowers the `(O-Maslov, Alexander)` bidegree of knot grid homology by
`(2, 1)`. -/
theorem X_smul_mem_bigradedUnblockedHomologyGrading_piece {g : ℤ × ℤ}
    {y : G.unblockedHomology R}
    (hy : y ∈ (hG.bigradedUnblockedHomologyGrading R).piece g) :
    letI := hG.unblockedHomologyModule R
    (Polynomial.X : Polynomial R) • y ∈
      (hG.bigradedUnblockedHomologyGrading R).piece (g - (2, 1)) := by
  let _ := hG.unblockedHomologyModule R
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  rw [hG.X_smul_unblockedHomology i y]
  exact hG.toOddComponentGridDiagram.X_smul_mem_bigradedUnblockedHomologyPiece R i hy

/-- Multiplication by `U ^ k` lowers the `(O-Maslov, Alexander)` bidegree of knot grid homology by
`(2 * k, k)`. -/
theorem X_pow_smul_mem_bigradedUnblockedHomologyGrading_piece (k : ℕ) {g : ℤ × ℤ}
    {y : G.unblockedHomology R}
    (hy : y ∈ (hG.bigradedUnblockedHomologyGrading R).piece g) :
    letI := hG.unblockedHomologyModule R
    (Polynomial.X ^ k : Polynomial R) • y ∈
      (hG.bigradedUnblockedHomologyGrading R).piece (g - (2 * (k : ℤ), (k : ℤ))) := by
  let _ := hG.unblockedHomologyModule R
  induction k with
  | zero => simpa [Prod.mk_zero_zero] using hy
  | succ k ih =>
    rw [pow_succ', mul_smul]
    have h := hG.X_smul_mem_bigradedUnblockedHomologyGrading_piece R ih
    have heq : g - (2 * (k : ℤ), (k : ℤ)) - (2, 1) =
        g - (2 * ((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ)) := by
      apply Prod.ext <;> simp <;> omega
    rwa [heq] at h

/-- On a knot grid, the class of the `X`-marking state is homogeneous of bidegree
`(M_O(G.X), A(G.X))`. -/
theorem XMarkingClass_mem_bigradedUnblockedHomologyGrading_piece :
    G.XMarkingClass R ∈
      (hG.bigradedUnblockedHomologyGrading R).piece
        (hG.toOddComponentGridDiagram.bidegree G.X) := by
  rw [bigradedUnblockedHomologyGrading_piece]
  exact hG.toOddComponentGridDiagram.XMarkingClass_mem_bigradedUnblockedHomologyPiece R

/-- On a knot grid whose `X`-marking state receives an even number of counted rectangles from every
grid state, each `U ^ k • λ⁻` witnesses positive `finrank` in bidegree `bidegree X - (2k, k)` over
any Noetherian commutative ring of characteristic two. -/
theorem finrank_bigradedUnblockedHomologyGrading_piece_pos [IsNoetherianRing R]
    (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card) (k : ℕ) :
    0 < Module.finrank R ((hG.bigradedUnblockedHomologyGrading R).piece
      (hG.toOddComponentGridDiagram.bidegree G.X - (2 * (k : ℤ), (k : ℤ)))) := by
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  rw [bigradedUnblockedHomologyGrading_piece]
  have h := hG.toOddComponentGridDiagram.finrank_bigradedUnblockedHomologyPiece_pos R hX
    (Finsupp.single i k)
  rwa [Finsupp.degree_single] at h

end GridDiagram.IsKnot

/-! ### Bigraded isomorphism of unblocked grid homologies -/

namespace GridDiagram.IsKnot

variable {n m l : ℕ} {G : GridDiagram n} {G' : GridDiagram m} {G'' : GridDiagram l}
  (hG : G.IsKnot) (hG' : G'.IsKnot) (hG'' : G''.IsKnot) (R : Type*) [CommRing R] [CharP R 2]

/-- The unblocked grid homologies of two knot grids are **isomorphic as Maslov--Alexander bigraded
`R[U]`-modules**: some `R[U]`-linear equivalence `GH⁻(G) ≃ GH⁻(G')` maps each homogeneous piece of
bidegree `g` into the piece of the same bidegree. The two grids may have different sizes. -/
def BigradedUnblockedHomologyIsomorphic : Prop :=
  letI := hG.unblockedHomologyModule R
  letI := hG'.unblockedHomologyModule R
  ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
    LinearMap.IsHomogeneous e.toLinearMap (hG.bigradedUnblockedHomologyGrading R).piece
      (hG'.bigradedUnblockedHomologyGrading R).piece 0

/-- Every knot grid has bigraded `GH⁻` isomorphic to itself. -/
theorem BigradedUnblockedHomologyIsomorphic.refl :
    hG.BigradedUnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  exact ⟨LinearEquiv.refl _ _, LinearMap.isHomogeneous_id _⟩

variable {hG hG' hG'' R}

/-- Unfold `BigradedUnblockedHomologyIsomorphic` to the existence of a bigraded equivalence. -/
theorem bigradedUnblockedHomologyIsomorphic_def :
    hG.BigradedUnblockedHomologyIsomorphic hG' R ↔
      letI := hG.unblockedHomologyModule R
      letI := hG'.unblockedHomologyModule R
      ∃ e : G.unblockedHomology R ≃ₗ[Polynomial R] G'.unblockedHomology R,
        LinearMap.IsHomogeneous e.toLinearMap (hG.bigradedUnblockedHomologyGrading R).piece
          (hG'.bigradedUnblockedHomologyGrading R).piece 0 :=
  Iff.rfl

/-- Equal knot grids have isomorphic bigraded `GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_of_eq {G₁ : GridDiagram n} {hG₁ : G₁.IsKnot}
    (h : G = G₁) : hG.BigradedUnblockedHomologyIsomorphic hG₁ R := by
  subst h
  exact .refl hG R

/-- Isomorphism of bigraded homologies is symmetric: the inverse of a degree-zero bigraded
equivalence is again degree-zero homogeneous. -/
theorem BigradedUnblockedHomologyIsomorphic.symm
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) :
    hG'.BigradedUnblockedHomologyIsomorphic hG R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, he.linearEquiv_symm⟩

/-- Isomorphism of bigraded homologies is transitive: degree-zero equivalences compose. -/
theorem BigradedUnblockedHomologyIsomorphic.trans
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R)
    (h' : hG'.BigradedUnblockedHomologyIsomorphic hG'' R) :
    hG.BigradedUnblockedHomologyIsomorphic hG'' R := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  let _ := hG''.unblockedHomologyModule R
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', by simpa only [LinearEquiv.coe_trans, add_zero] using he'.comp he⟩

/-- Isomorphism of bigraded homologies holds in one direction exactly when it holds in the
other. -/
theorem bigradedUnblockedHomologyIsomorphic_comm :
    hG.BigradedUnblockedHomologyIsomorphic hG' R ↔
      hG'.BigradedUnblockedHomologyIsomorphic hG R :=
  ⟨.symm, .symm⟩

/-- Forgetting the `O`-Maslov grading turns a bigraded `R[U]`-isomorphism of `GH⁻` into an
Alexander-graded `R[U]`-isomorphism. -/
theorem BigradedUnblockedHomologyIsomorphic.unblockedHomologyIsomorphic
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) :
    hG.UnblockedHomologyIsomorphic hG' R := by
  rw [unblockedHomologyIsomorphic_def]
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  have := hG.isScalarTower_unblockedHomology (R := R)
  have := hG'.isScalarTower_unblockedHomology (R := R)
  obtain ⟨e, he⟩ := h
  refine ⟨e, LinearMap.isHomogeneous_def.mpr fun a y hy ↦ ?_⟩
  have hcoarsen := (he.restrictScalars R).coarsenGrading (AddMonoidHom.snd ℤ ℤ)
  rw [← coarsen_bigradedUnblockedHomologyGrading_snd, InternalGrading.coarsen_piece] at hy ⊢
  exact hcoarsen.map_mem hy

/-- Knot grids with isomorphic bigraded `GH⁻` have the same invariant `τ`. -/
theorem BigradedUnblockedHomologyIsomorphic.tau_eq
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) :
    hG.tau R = hG'.tau R :=
  h.unblockedHomologyIsomorphic.tau_eq

/-- A bigraded `R[U]`-isomorphism restricts in every bidegree `g` to an `R`-linear equivalence
between the homogeneous pieces. -/
theorem BigradedUnblockedHomologyIsomorphic.nonempty_piece_linearEquiv
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) (g : ℤ × ℤ) :
    Nonempty (((hG.bigradedUnblockedHomologyGrading R).piece g) ≃ₗ[R]
      ((hG'.bigradedUnblockedHomologyGrading R).piece g)) := by
  let _ := hG.unblockedHomologyModule R
  let _ := hG'.unblockedHomologyModule R
  have := hG.isScalarTower_unblockedHomology (R := R)
  have := hG'.isScalarTower_unblockedHomology (R := R)
  obtain ⟨e, he⟩ := h
  exact ⟨LinearMap.IsHomogeneous.pieceLinearEquiv (e := e.restrictScalars R)
    (he.restrictScalars R) g⟩

/-- Knot grids with isomorphic bigraded `GH⁻` have equal ground-ring `finrank` in every
Maslov--Alexander bidegree. -/
theorem BigradedUnblockedHomologyIsomorphic.finrank_piece_eq
    (h : hG.BigradedUnblockedHomologyIsomorphic hG' R) (g : ℤ × ℤ) :
    Module.finrank R ((hG.bigradedUnblockedHomologyGrading R).piece g) =
      Module.finrank R ((hG'.bigradedUnblockedHomologyGrading R).piece g) :=
  let ⟨e⟩ := h.nonempty_piece_linearEquiv g
  e.finrank_eq

/-- A bijection between the unblocked homologies of two knot grids makes them isomorphic as
Maslov--Alexander bigraded `R[U]`-modules if it preserves every bidegree piece and is semilinear
along a ring homomorphism `σ` of the polynomial rings that commutes with the evaluation
`V_j ↦ U`. -/
theorem BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    {σ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin m) R}
    (hσ : ∀ p, MvPolynomial.aeval (fun _ ↦ (Polynomial.X : Polynomial R)) (σ p) =
      MvPolynomial.aeval (fun _ ↦ (Polynomial.X : Polynomial R)) p)
    (f : G.unblockedHomology R →ₛₗ[σ] G'.unblockedHomology R) (hf : Function.Bijective f)
    (hMA : ∀ g y, y ∈ (hG.bigradedUnblockedHomologyGrading R).piece g →
      f y ∈ (hG'.bigradedUnblockedHomologyGrading R).piece g) :
    hG.BigradedUnblockedHomologyIsomorphic hG' R := by
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
  refine ⟨LinearEquiv.ofBijective f' hf, LinearMap.isHomogeneous_def.mpr fun g y hy ↦ ?_⟩
  rw [add_zero]
  exact hMA g y hy

end GridDiagram.IsKnot

end TauCeti
