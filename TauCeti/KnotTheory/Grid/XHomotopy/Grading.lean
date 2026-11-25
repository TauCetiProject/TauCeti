/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked
public import TauCeti.KnotTheory.Grid.XHomotopy.SimplyBlocked

/-!
# The bigrading of the `X`-marking homotopy

Every rectangle `r` counted by the `X`-marking homotopy `H_k` is empty and covers the single
`X`-marking `X_k`. Thus `H_k` lowers `(O-Maslov, Alexander)` bidegrees by `(1, 1)` on `GC⁻`
(`OddComponentGridDiagram.XHomotopy_mem_bigradedChainMinusPiece`), as do its component-path sums
(`componentPathXHomotopy_mem_bigradedChainMinusPiece`) and specialization `hat H_k` at `V_i = 0`
(`simplyBlockedXHomotopy_mem_bigradedChainHatPiece`), over any commutative semiring. In
characteristic two, summing along a link component gives a bidegree-`(-1, -1)` homotopy between
`V_i` and `V_j` (`exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle`); on a knot grid,
the explicit null-homotopy `GridDiagram.IsKnot.XSmulHomotopy` of `V_c + V_{c'}` has bidegree
`(-1, -1)` (`GridDiagram.IsKnot.XSmulHomotopy_mem_bigradedChainMinusPiece`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Lemma 4.6.9 and Proposition 4.6.15.
-/

public section

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- A rectangle counted by `H_k` lowers the integer Alexander grading by `1` once its weight
`V^{O(r)}` is charged `-1` per variable, because it covers the single `X`-marking `X_k`. -/
theorem alexanderℤ_sub_card_OColumns_of_mem_XHomotopyRectangles {k : Fin n} {x y : GridState n}
    {r : GridRectangleBetween x y} (hr : r ∈ G.val.XHomotopyRectangles k x y) :
    G.alexanderℤ y - ((G.val.OColumns r.toGridRectangle).card : ℤ) = G.alexanderℤ x - 1 := by
  have hX : G.val.XSet ∩ r.toGridRectangle.coveredSquares = {(k, G.val.X k)} :=
    (Finset.inter_comm _ _).trans ((G.val.mem_XHomotopyRectangles k r).mp hr).2
  rw [G.alexanderℤ_sub_card_OColumns_eq_sub_card r, hX, Finset.card_singleton, Nat.cast_one]

/-- Multiplying the basis element `V^e · x` by the weight of a rectangle counted by `H_k` and
passing to the rectangle's target lowers the `(O-Maslov, Alexander)` bidegree by `(1, 1)`. -/
theorem monomialBidegree_add_of_mem_XHomotopyRectangles {k : Fin n} {x y : GridState n}
    {r : GridRectangleBetween x y} (hr : r ∈ G.val.XHomotopyRectangles k x y) (e : Fin n →₀ ℕ) :
    G.monomialBidegree y (e + ∑ c ∈ G.val.OColumns r.toGridRectangle, Finsupp.single c 1) =
      G.monomialBidegree x e - (1, 1) := by
  have hM := G.val.maslovOℤ_sub_two_mul_card_OColumns ((G.val.mem_XHomotopyRectangles k r).mp hr).1
  have hA := G.alexanderℤ_sub_card_OColumns_of_mem_XHomotopyRectangles hr
  simpa [sub_eq_add_neg] using G.monomialBidegree_mapDomain_add_sum_eq_add G (Equiv.refl (Fin n)) e
    (G.val.OColumns r.toGridRectangle) (-1, -1) (by omega) (by omega)

section Semiring

variable {R : Type*} [CommSemiring R]

/-- **The `X`-marking homotopy `H_k` has bidegree `(-1, -1)`**: it lowers both the `O`-Maslov
grading and the Alexander grading of a homogeneous chain of `GC⁻` by `1`. -/
theorem XHomotopy_mem_bigradedChainMinusPiece (k : Fin n) {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.val.XHomotopy R k c ∈ G.bigradedChainMinusPiece R (g - (1, 1)) := by
  simpa only [sub_eq_add_neg] using G.matrixMap_mem_bigradedChainMinusPiece_add R G
    (Equiv.refl (Fin n)) (G.val.XHomotopyCoefficient R k) (G.val.XHomotopy R k)
    (fun d y => by simp [GridDiagram.XHomotopy_apply_apply]) (-(1, 1)) (fun x y w hw d => by
      obtain ⟨r, hr, rfl⟩ :=
        G.val.exists_mem_XHomotopyRectangles_of_mem_support_XHomotopyCoefficient R hw
      simpa [sub_eq_add_neg] using G.monomialBidegree_add_of_mem_XHomotopyRectangles hr d) hc

/-- The `m`-step component-path `X`-homotopy lowers chain bidegrees on `GC⁻` by `(1, 1)`. -/
theorem componentPathXHomotopy_mem_bigradedChainMinusPiece (i : Fin n) (m : ℕ) {g : ℤ × ℤ}
    {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.val.componentPathXHomotopy R i m c ∈ G.bigradedChainMinusPiece R (g - (1, 1)) := by
  rw [GridDiagram.componentPathXHomotopy_apply]
  exact Submodule.sum_mem _ fun _ _ => G.XHomotopy_mem_bigradedChainMinusPiece _ hc

/-- The `X`-marking homotopy `H_k` lowers the Alexander grading of an Alexander-homogeneous chain
of `GC⁻` by `1`. -/
theorem XHomotopy_mem_alexanderChainMinusPiece (k : Fin n) {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.val.XHomotopy R k c ∈ G.alexanderChainMinusPiece R (a - 1) := by
  simpa only [sub_eq_add_neg] using G.matrixMap_mem_alexanderChainMinusPiece_add R G
    (Equiv.refl (Fin n)) (G.val.XHomotopyCoefficient R k) (G.val.XHomotopy R k)
    (fun d y => by simp [GridDiagram.XHomotopy_apply_apply]) (-1) (fun x y w hw d => by
      obtain ⟨r, hr, rfl⟩ :=
        G.val.exists_mem_XHomotopyRectangles_of_mem_support_XHomotopyCoefficient R hw
      simpa [sub_eq_add_neg] using
        congrArg Prod.snd (G.monomialBidegree_add_of_mem_XHomotopyRectangles hr d)) hc

/-- The specialized `X`-marking homotopy `hat H_k` at `V_i = 0` lowers the bidegree of a
homogeneous chain of `GC^_i` by `(1, 1)`. -/
theorem simplyBlockedXHomotopy_mem_bigradedChainHatPiece {i : Fin n} (k : Fin n) {g : ℤ × ℤ}
    {c : GridChainHat R n i} (hc : c ∈ G.bigradedChainHatPiece R i g) :
    G.val.simplyBlockedXHomotopy R i k c ∈ G.bigradedChainHatPiece R i (g - (1, 1)) := by
  obtain ⟨b, hb, rfl⟩ := G.mem_bigradedChainHatPiece_iff_exists.mp hc
  rw [← GridDiagram.simplyBlockedSpecialization_XHomotopy]
  exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i
    (G.XHomotopy_mem_bigradedChainMinusPiece k hb)

end Semiring

section CharTwo

variable (R : Type*) [CommSemiring R] [CharP R 2]

/-- In characteristic two, walking `m` steps along `componentPerm` from column `i` to column `j`
produces a polynomial-linear homotopy `H` of bidegree `(-1, -1)` on `GC⁻` satisfying
`∂⁻ ∘ H + H ∘ ∂⁻ = V_i + V_j`. -/
theorem exists_unblockedDifferential_comp_add_comp_eq_of_pow_componentPerm_apply
    {i j : Fin n} (m : ℕ) (h : (G.val.componentPerm ^ m) i = j) :
    ∃ H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n,
      G.val.unblockedDifferential R ∘ₗ H + H ∘ₗ G.val.unblockedDifferential R =
          (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id ∧
        ∀ ⦃g : ℤ × ℤ⦄ ⦃c : GridChainMinus R n⦄,
          c ∈ G.bigradedChainMinusPiece R g → H c ∈ G.bigradedChainMinusPiece R (g - (1, 1)) := by
  subst h
  exact ⟨G.val.componentPathXHomotopy R i m,
    G.val.unblockedDifferential_comp_componentPathXHomotopy_add_componentPathXHomotopy_comp R i m,
    fun _ _ => G.componentPathXHomotopy_mem_bigradedChainMinusPiece i m⟩

/-- In characteristic two, for any two columns `i` and `j` on the same link component of an
odd-component grid diagram, there is a polynomial-linear homotopy `H` of bidegree `(-1, -1)` on
`GC⁻` satisfying `∂⁻ ∘ H + H ∘ ∂⁻ = V_i + V_j`. -/
theorem exists_unblockedDifferential_comp_add_comp_eq_of_sameCycle
    {i j : Fin n} (h : G.val.componentPerm.SameCycle i j) :
    ∃ H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n,
      G.val.unblockedDifferential R ∘ₗ H + H ∘ₗ G.val.unblockedDifferential R =
          (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) R) • LinearMap.id ∧
        ∀ ⦃g : ℤ × ℤ⦄ ⦃c : GridChainMinus R n⦄,
          c ∈ G.bigradedChainMinusPiece R g → H c ∈ G.bigradedChainMinusPiece R (g - (1, 1)) :=
  let ⟨m, hm⟩ := h.exists_nat_pow_eq
  G.exists_unblockedDifferential_comp_add_comp_eq_of_pow_componentPerm_apply R m hm

end CharTwo

/-- The `X`-marking homotopy `H_k` is homogeneous of bidegree `(-1, -1)` with respect to the
internal bigrading of `GC⁻`. -/
theorem isHomogeneous_XHomotopy_bigradedChainMinusGrading (R : Type*) [CommRing R] (k : Fin n) :
    LinearMap.IsHomogeneous (G.val.XHomotopy R k)
      (G.bigradedChainMinusGrading R).piece (G.bigradedChainMinusGrading R).piece (-(1, 1)) :=
  LinearMap.isHomogeneous_def.mpr fun _ _ hc => by
    simp only [bigradedChainMinusGrading_piece] at hc ⊢
    simpa only [sub_eq_add_neg] using G.XHomotopy_mem_bigradedChainMinusPiece k hc

end TauCeti.OddComponentGridDiagram

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

/-- On a knot grid, the null-homotopy `IsKnot.XSmulHomotopy` of multiplication by
`V_c + V_c'` has bidegree `(-1, -1)`. -/
theorem XSmulHomotopy_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R] (c c' : Fin n)
    {g : ℤ × ℤ} {a : GridChainMinus R n}
    (ha : a ∈ hG.toOddComponentGridDiagram.bigradedChainMinusPiece R g) :
    hG.XSmulHomotopy R c c' a ∈
      hG.toOddComponentGridDiagram.bigradedChainMinusPiece R (g - (1, 1)) := by
  rw [hG.XSmulHomotopy_eq_componentPathXHomotopy R]
  exact hG.toOddComponentGridDiagram.componentPathXHomotopy_mem_bigradedChainMinusPiece c _ ha

end TauCeti.GridDiagram.IsKnot
