/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.WeightedTrace

/-!
# Unit-weighted pairings between zero-DG vertex projectives

Homogeneous DG morphisms of degrees `d` and `2 - d` between the actual zero-DG vertex
projectives have a perfect pairing induced by the unit-weighted graded corner trace.
Its value is the source weight times the trace of their actual enriched composition.
Opposite weights at adjacent selected endpoints give the sign `(-1) ^ (d * (2 - d))`
under reversal.

These are generator pairings in the chosen zero-DG model, whose DG degree is path degree.
The ordinary derived category of internally graded modules retains its separate external
cohomological degree. The enriched statements use the common universe of the existing
DG-right-module category.

## References

* B. Keller, *Calabi-Yau triangulated categories*, Proposition 2.2(b), for the graded trace sign.
* The existing zero-DG projective corner dictionary and unit-weighted graded corner pairings.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (k : Type u) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "C" => fun (i j : V) (d : ℤ) ↦
  cornerSubmodule k (e i) (e j) ⊓ zigzagAlgebraIntegerGrade k G d
local notation "L" => zigzagAlgebraProjectiveDGHomEquivCorner k G

-- The landed dictionary is indexed by target shift s and has DG degree -s.
-- Reindex only this concrete dictionary to expose the pairing's complementary DG degrees.
private abbrev projectiveDGHomCornerEquiv (i j : V) (d : ℤ) :
    DGHom k d (D i) (D j) ≃ₗ[k] ↥(C i j d) :=
  (((dgHomComplex k (D i) (D j)).XIsoOfEq (Int.neg_neg d).symm).toLinearEquiv.trans
    (L i j (-d))).trans (LinearEquiv.ofEq _ _ (by dsimp only; rw [Int.neg_neg]))

private theorem coe_projectiveCorner_castDeg (i j : V) (s t : ℤ) (h : s = t)
    (f : DGHom k (-s) (D i) (D j)) :
    (L i j t (castDeg k (congrArg (fun n : ℤ ↦ -n) h) f) : Z) = (L i j s f : Z) := by
  subst t
  simp only [castDeg_self]

private theorem projectiveDGHomCornerEquiv_comp
    (i j l : V) (a b n : ℤ) (hab : a + b = n)
    (f : DGHom k a (D i) (D j)) (g : DGHom k b (D j) (D l)) :
    (projectiveDGHomCornerEquiv k G i l n (dgComp k f g hab) : Z) =
      (projectiveDGHomCornerEquiv k G i j a f : Z) *
        (projectiveDGHomCornerEquiv k G j l b g : Z) := by
  subst n
  -- The term isomorphisms evaluate as castDeg, while ofEq preserves ambient corner vectors.
  simp only [projectiveDGHomCornerEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, Iso.toLinearEquiv_apply, ← castDeg_def]
  have hcast := coe_projectiveCorner_castDeg k G i l (-b + -a) (-(a + b)) (by omega)
    (castDeg k (by omega) (dgComp k f g rfl))
  calc
    _ = (L i l (-b + -a) (castDeg k (by omega) (dgComp k f g rfl)) : Z) := by
      simpa only [castDeg_castDeg] using hcast
    _ = _ := by
      simpa only [castDeg_dgComp_eq_castDeg, dgComp_castDeg_eq_castDeg, castDeg_castDeg] using
        (coe_zigzagAlgebraProjectiveDGHomEquivCorner_comp k G i j l (-a) (-b)
          (castDeg k (Int.neg_neg a).symm f) (castDeg k (Int.neg_neg b).symm g))

/-- The weighted corner trace pulled back to complementary homogeneous DG morphisms. -/
def zigzagAlgebraProjectiveDGHomWeightedTracePairing
    (c : V → kˣ) (i j : V) (d : ℤ) :
    DGHom k d (D i) (D j) →ₗ[k] DGHom k (2 - d) (D j) (D i) →ₗ[k] k :=
  (zigzagAlgebraGradedCornerWeightedTracePairing k G c i j d).compl₁₂
    (projectiveDGHomCornerEquiv k G i j d).toLinearMap
    (projectiveDGHomCornerEquiv k G j i (2 - d)).toLinearMap

/-- The generator pairing is perfect in every pair of complementary DG degrees. -/
instance zigzagAlgebraProjectiveDGHomWeightedTracePairing_isPerfPair
    (c : V → kˣ) (i j : V) (d : ℤ) :
    (zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c i j d).IsPerfPair := by
  dsimp only [zigzagAlgebraProjectiveDGHomWeightedTracePairing]
  infer_instance

/-- The pairing evaluates the genuine enriched composition through its degree-two corner. -/
@[simp]
theorem zigzagAlgebraProjectiveDGHomWeightedTracePairing_apply
    (c : V → kˣ) (i j : V) (d : ℤ)
    (f : DGHom k d (D i) (D j)) (g : DGHom k (2 - d) (D j) (D i)) :
    zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c i j d f g =
      (c i : k) * zigzagAlgebraTrace k G
        (L i i (-2) (dgComp k f g (by omega)) : Z) := by
  -- Unfold the pullback evaluation; the degree-two reindexing reduces to the original dictionary.
  change zigzagAlgebraGradedCornerWeightedTracePairing k G c i j d
      (projectiveDGHomCornerEquiv k G i j d f)
      (projectiveDGHomCornerEquiv k G j i (2 - d) g) =
    (c i : k) * zigzagAlgebraTrace k G
      (projectiveDGHomCornerEquiv k G i i 2 (dgComp k f g (by omega)) : Z)
  rw [zigzagAlgebraGradedCornerWeightedTracePairing_apply,
    projectiveDGHomCornerEquiv_comp]

/-- Reversal has the graded trace sign under the edge condition at the selected endpoints. -/
theorem zigzagAlgebraProjectiveDGHomWeightedTracePairing_flip
    (c : V → kˣ) (i j : V)
    (hc : G.Adj i j → (c j : k) = -(c i : k))
    (d : ℤ) (f : DGHom k d (D i) (D j))
    (g : DGHom k (2 - d) (D j) (D i)) :
    zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c i j d f g =
      (d * (2 - d)).negOnePow • ((c j : k) * zigzagAlgebraTrace k G
        (L j j (-2) (dgComp k g f (by omega)) : Z)) := by
  -- Unfold the pullback evaluation; the degree-two reindexing reduces to the original dictionary.
  change zigzagAlgebraGradedCornerWeightedTracePairing k G c i j d
      (projectiveDGHomCornerEquiv k G i j d f)
      (projectiveDGHomCornerEquiv k G j i (2 - d) g) =
    (d * (2 - d)).negOnePow • ((c j : k) * zigzagAlgebraTrace k G
      (projectiveDGHomCornerEquiv k G j j 2 (dgComp k g f (by omega)) : Z))
  rw [projectiveDGHomCornerEquiv_comp]
  exact zigzagAlgebraGradedCornerWeightedTracePairing_flip k G c i j hc d _ _

end TauCeti
