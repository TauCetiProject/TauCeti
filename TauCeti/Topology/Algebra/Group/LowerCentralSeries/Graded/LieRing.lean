/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.Basic
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule
import Mathlib.Tactic.LinearCombination

/-!
# The graded Lie ring of the lower `p`-series

For a topological group `G` and `p : ℕ`, the graded pieces `gr_k(G) = λ_k ⧸ λ_{k+1}` of the lower
`p`-series carry the bracket `TauCeti.gradedBracket p G j k : gr_j(G) →+ gr_k(G) →+ gr_{j+k+1}(G)`
induced by the group commutator, alternating and satisfying the Jacobi identity degree by degree.
This file assembles these brackets into a Lie ring structure on the direct sum

  `⨁ k, gr_k(G)`,

on which the bracket of homogeneous elements of degrees `j` and `k` is their graded bracket, of
degree `j + k + 1` (`TauCeti.of_lie_of`); the shift by one is because the series is `0`-based.
Every graded piece is killed by `p`, so the direct sum is a Lie algebra over `ZMod p`. For `p = 0`
this is the graded Lie ring `⨁ n, γ_n(G) ⧸ γ_{n+1}(G)` of the closed lower central series, whose
pieces are `TauCeti.lcsGradedPiece G n = gradedPiece 0 G n`, as a Lie algebra over `ZMod 0 = ℤ`.

A continuous homomorphism `G →* H` induces a Lie algebra homomorphism of the graded Lie rings
(`TauCeti.gradedLieHom`), functorially.

When `G` is a pro-`ℓ` group for a prime `ℓ`, each graded piece is an abelian pro-`ℓ` group, hence a
`ℤ_ℓ`-module (`TauCeti.IsProP.gradedPieceModule`), and the graded bracket is `ℤ_ℓ`-bilinear. The
direct sum of these modules is then a Lie algebra over `ℤ_ℓ` (`TauCeti.IsProP.gradedLieAlgebra`).

## Main definitions

* The `LieRing (⨁ k, gradedPiece p G k)` and `LieAlgebra (ZMod p) (⨁ k, gradedPiece p G k)`
  instances.
* `TauCeti.gradedLieHom`: the Lie algebra homomorphism induced by a continuous homomorphism.
* `TauCeti.IsProP.gradedLieAlgebra`: the `ℤ_ℓ`-Lie algebra structure for a pro-`ℓ` group.

## Main results

* `TauCeti.of_lie_of`: the bracket of homogeneous elements is the graded bracket.
* `TauCeti.gradedLieHom_of`, `TauCeti.gradedLieHom_id`, `TauCeti.gradedLieHom_comp`: the induced
  homomorphism is the graded map in each degree, and is functorial.

## References

* M. Lazard, *Sur les groupes nilpotents et les anneaux de Lie*, Ann. Sci. École Norm. Sup. 71
  (1954).
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

open DirectSum

namespace TauCeti

universe u v w

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Transport along an equality of degrees does not change an element of the direct sum of the
graded pieces. -/
@[simp]
theorem of_gradedCast {j k : ℕ} (h : j = k) (x : gradedPiece p G j) :
    of (gradedPiece p G) k (gradedCast p G h x) = of (gradedPiece p G) j x := by
  subst h
  rw [gradedCast_rfl]

/-! ### The bracket on the direct sum -/

variable (p G) in
/-- **The graded bracket on the direct sum** `⨁ k, gr_k(G)`, as a biadditive map: the biadditive
extension of the graded brackets, which on homogeneous elements of degrees `j` and `k` is
`TauCeti.gradedBracket p G j k`, landing in degree `j + k + 1` (`TauCeti.of_lie_of`). It is the
bracket of the graded Lie ring (`TauCeti.gradedLieBracket_apply`). -/
def gradedLieBracket :
    (⨁ k, gradedPiece p G k) →+ (⨁ k, gradedPiece p G k) →+ ⨁ k, gradedPiece p G k :=
  toAddMonoid fun j => (toAddMonoid fun k =>
    ((gradedBracket p G j k).compr₂ (of (gradedPiece p G) (j + k + 1))).flip).flip

/-- The bracket of the graded Lie ring `⨁ k, gr_k(G)`, given by `TauCeti.gradedLieBracket`. -/
instance : Bracket (⨁ k, gradedPiece p G k) (⨁ k, gradedPiece p G k) where
  bracket x y := gradedLieBracket p G x y

/-- The biadditive map `TauCeti.gradedLieBracket` is the bracket of the graded Lie ring. -/
@[simp]
theorem gradedLieBracket_apply (x y : ⨁ k, gradedPiece p G k) :
    gradedLieBracket p G x y = ⁅x, y⁆ :=
  rfl

/-- **The bracket of homogeneous elements** of degrees `j` and `k` is their graded bracket, of
degree `j + k + 1`. -/
@[simp]
theorem of_lie_of {j k : ℕ} (x : gradedPiece p G j) (y : gradedPiece p G k) :
    ⁅of (gradedPiece p G) j x, of (gradedPiece p G) k y⁆ =
      of (gradedPiece p G) (j + k + 1) (gradedBracket p G j k x y) := by
  simp [← gradedLieBracket_apply, gradedLieBracket]

/-- **Skew-symmetry** of the graded bracket on the direct sum: `[y, x] = -[x, y]`. -/
theorem gradedLieBracket_flip : (gradedLieBracket p G).flip = -gradedLieBracket p G :=
  addHom_ext fun j x => addHom_ext fun k y => by
    rw [AddMonoidHom.flip_apply, AddMonoidHom.neg_apply, AddMonoidHom.neg_apply,
      gradedLieBracket_apply, gradedLieBracket_apply, of_lie_of, of_lie_of,
      ← of_gradedCast (by omega : k + j + 1 = j + k + 1), gradedCast_gradedBracket_swap, map_neg]

/-- The graded Lie ring `⨁ k, gr_k(G)` of the lower `p`-series: the graded brackets are
alternating and satisfy the Jacobi identity degree by degree, hence so does their biadditive
extension to the direct sum. -/
instance : LieRing (⨁ k, gradedPiece p G k) where
  add_lie x y z := by simp only [← gradedLieBracket_apply, map_add, AddMonoidHom.add_apply]
  lie_add x y z := by simp only [← gradedLieBracket_apply, map_add]
  lie_self x := by
    simp only [← gradedLieBracket_apply]
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of k a => rw [gradedLieBracket_apply, of_lie_of, gradedBracket_self, map_zero]
    | add x y hx hy =>
      simp only [map_add, AddMonoidHom.add_apply, hx, hy, zero_add, add_zero]
      rw [← AddMonoidHom.flip_apply (gradedLieBracket p G) x y, gradedLieBracket_flip,
        AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, add_neg_cancel]
  leibniz_lie x y z := by
    simp only [← gradedLieBracket_apply]
    -- By skew-symmetry, the Leibniz rule is the Jacobi identity
    -- `[[x, y], z] + [[y, z], x] + [[z, x], y] = 0`, which is triadditive and so reduces to
    -- homogeneous elements, where it is the graded Jacobi identity `gradedBracket_jacobi`.
    have swap (a b) : gradedLieBracket p G b a = -gradedLieBracket p G a b := by
      rw [← AddMonoidHom.flip_apply, gradedLieBracket_flip, AddMonoidHom.neg_apply,
        AddMonoidHom.neg_apply]
    suffices jacobi : gradedLieBracket p G (gradedLieBracket p G x y) z +
        gradedLieBracket p G (gradedLieBracket p G y z) x +
        gradedLieBracket p G (gradedLieBracket p G z x) y = 0 by
      rw [swap (gradedLieBracket p G y z) x, swap (gradedLieBracket p G x z) y, swap z x, map_neg,
        AddMonoidHom.neg_apply]
      linear_combination (norm := abel) -jacobi
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply, add_zero]
    | add x x' hx hx' =>
      simp only [map_add, AddMonoidHom.add_apply] at *
      linear_combination (norm := abel) hx + hx'
    | of i a =>
      induction y using DirectSum.induction_on with
      | zero => simp only [map_zero, AddMonoidHom.zero_apply, add_zero]
      | add y y' hy hy' =>
        simp only [map_add, AddMonoidHom.add_apply] at *
        linear_combination (norm := abel) hy + hy'
      | of j b =>
        induction z using DirectSum.induction_on with
        | zero => simp only [map_zero, AddMonoidHom.zero_apply, add_zero]
        | add z z' hz hz' =>
          simp only [map_add, AddMonoidHom.add_apply] at *
          linear_combination (norm := abel) hz + hz'
        | of k c =>
          -- Move the three homogeneous terms to the common degree `i + j + k + 2`.
          simp only [gradedLieBracket_apply, of_lie_of]
          rw [← of_gradedCast (by omega : i + j + 1 + k + 1 = i + j + k + 2),
            ← of_gradedCast (by omega : j + k + 1 + i + 1 = i + j + k + 2),
            ← of_gradedCast (by omega : k + i + 1 + j + 1 = i + j + k + 2), ← map_add, ← map_add,
            gradedBracket_jacobi, map_zero]

/-- Every graded piece is a `ZMod p`-module and the graded bracket is biadditive, so the graded
Lie ring is a Lie algebra over `ZMod p`. -/
instance : LieAlgebra (ZMod p) (⨁ k, gradedPiece p G k) where
  lie_smul c x y := ZMod.map_smul (gradedLieBracket p G x) c y

/-! ### Functoriality -/

section Functoriality

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {K : Type w} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

variable (p) in
/-- **The graded Lie homomorphism of a continuous homomorphism** `f : G →* H`: the graded maps
`TauCeti.gradedMap p f hf k` of all degrees, assembled into a homomorphism of graded Lie algebras
`⨁ k, gr_k(G) →ₗ⁅ZMod p⁆ ⨁ k, gr_k(H)`. Its value on homogeneous elements is
`TauCeti.gradedLieHom_of`. -/
def gradedLieHom (f : G →* H) (hf : Continuous f) :
    (⨁ k, gradedPiece p G k) →ₗ⁅ZMod p⁆ ⨁ k, gradedPiece p H k where
  toLinearMap := (DirectSum.map fun k => gradedMap p f hf k).toZModLinearMap p
  map_lie' {x y} := by
    simp only [LinearMap.toFun_eq_coe, AddMonoidHom.coe_toZModLinearMap, ← gradedLieBracket_apply]
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
    | of j a =>
      induction y using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | of k b => simp only [gradedLieBracket_apply, of_lie_of, map_of, gradedMap_gradedBracket]

/-- The graded Lie homomorphism of `f` is the graded map of `f` in each degree. -/
@[simp]
theorem gradedLieHom_of (f : G →* H) (hf : Continuous f) (k : ℕ) (x : gradedPiece p G k) :
    gradedLieHom p f hf (of (gradedPiece p G) k x) =
      of (gradedPiece p H) k (gradedMap p f hf k x) := by
  simp only [← LieHom.coe_toLinearMap, gradedLieHom, AddMonoidHom.coe_toZModLinearMap, map_of]

/-- The identity of `G` induces the identity of the graded Lie ring. -/
@[simp]
theorem gradedLieHom_id :
    gradedLieHom p (MonoidHom.id G) continuous_id = LieHom.id := by
  refine LieHom.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of k a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The graded Lie homomorphism of a composite is the composite of the graded Lie homomorphisms:
the graded Lie ring is a functor. -/
-- Not `@[simp]`: on the left-hand side `hg` and `hf` occur only inside the proof `hg.comp hf`,
-- so `simp` cannot instantiate them.
theorem gradedLieHom_comp (g : H →* K) (hg : Continuous g) (f : G →* H) (hf : Continuous f) :
    gradedLieHom p (g.comp f) (hg.comp hf) = (gradedLieHom p g hg).comp (gradedLieHom p f hf) := by
  refine LieHom.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of k a =>
    rw [gradedLieHom_of, LieHom.comp_apply, gradedLieHom_of, gradedLieHom_of, gradedMap_comp,
      AddMonoidHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Functoriality

/-! ### The `ℤ_ℓ`-Lie algebra of a pro-`ℓ` group -/

section PadicInt

variable {ℓ : ℕ} [Fact ℓ.Prime] [CompactSpace G] [TotallyDisconnectedSpace G]

variable (p) in
/-- **The `ℤ_ℓ`-Lie algebra of a pro-`ℓ` group.** For a pro-`ℓ` group `G`, the graded Lie ring
`⨁ k, gr_k(G)` of the lower `p`-series is a Lie algebra over `ℤ_ℓ`, for the `ℤ_ℓ`-module structure
which in each degree is `TauCeti.IsProP.gradedPieceModule`: the graded bracket is `ℤ_ℓ`-bilinear.
For `p = 0` this is the `ℤ_ℓ`-Lie algebra of the closed lower central series. -/
@[instance_reducible]
noncomputable def IsProP.gradedLieAlgebra (hG : IsProP ℓ G) :
    letI := fun k => hG.gradedPieceModule p k
    LieAlgebra ℤ_[ℓ] (⨁ k, gradedPiece p G k) :=
  letI := fun k => hG.gradedPieceModule p k
  { lie_smul u x y := by
      simp only [← gradedLieBracket_apply]
      induction x using DirectSum.induction_on with
      | zero => simp only [map_zero, AddMonoidHom.zero_apply, smul_zero]
      | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx', smul_add]
      | of j a =>
        induction y using DirectSum.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
        | of k b =>
          rw [← of_smul, gradedLieBracket_apply, gradedLieBracket_apply, of_lie_of, of_lie_of,
            hG.gradedBracket_smul_right, of_smul] }

end PadicInt

end TauCeti
