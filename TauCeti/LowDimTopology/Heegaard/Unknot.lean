/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.Knot.Homology
public import TauCeti.LowDimTopology.Heegaard.Knot.Tau

/-!
# The genus-zero Heegaard diagram and the unknot

The sphere `S²` with no attaching curves is a Heegaard diagram of genus zero of `S³`. It has no
intersection points, a single complementary region, the whole sphere, of Euler characteristic
`2`, and a single generator, the empty tuple. Placing two basepoints `w` and `z` in it gives a
doubly pointed diagram of the unknot. `TauCeti.HeegaardRegionSystem.genusZero B` records this
incidence data, with all the basepoints `B` in the single region.

Every function on the single region is a domain from the generator to itself, the multiples `c`
of the sphere, of Maslov index `μ = 2c` and multiplicity `c` at every basepoint. Hence:

* the Maslov and Alexander gradings `0` form a knot grading
  (`TauCeti.HeegaardRegionSystem.isKnotGrading_genusZero`): `μ - 2 n_w = 0` and `n_z - n_w = 0`
  on every domain;
* no domain has Maslov index one, so the hat differential vanishes
  (`TauCeti.HeegaardRegionSystem.hatDifferential_genusZero`);
* the hat knot Floer homology `HFK̂` of the unknot has rank one
  (`TauCeti.HeegaardRegionSystem.finrank_hatHomology_genusZero`), in bigrading `(0, 0)`, and its
  graded Euler characteristic is `1`
  (`TauCeti.HeegaardRegionSystem.finsum_finrank_hatHomologyGrading_piece_smul_genusZero`), the
  Alexander polynomial of the unknot;
* the minus knot differential vanishes as well
  (`TauCeti.HeegaardRegionSystem.knotMinusDifferential_genusZero`), so `HFK⁻` of the unknot is the
  tower `𝔽₂[U]` on the single generator, in Alexander grading `0`, and `τ = 0`
  (`TauCeti.HeegaardRegionSystem.tau_genusZero`).

The identification of the knot, like that of the incidence data with the sphere, is geometric and
is not formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.genusZero`: the genus-zero diagram, with its basepoints.

## Main results

* `TauCeti.HeegaardRegionSystem.isDomainBetween_genusZero`: every function on the region is a
  domain.
* `TauCeti.HeegaardRegionSystem.isKnotGrading_genusZero`: the zero gradings form a knot grading.
* `TauCeti.HeegaardRegionSystem.hatDifferential_genusZero`: the hat differential vanishes.
* `TauCeti.HeegaardRegionSystem.finrank_hatHomology_genusZero` and
  `TauCeti.HeegaardRegionSystem.finsum_finrank_hatHomologyGrading_piece_smul_genusZero`: `HFK̂` of
  the unknot has rank one and graded Euler characteristic `1`.
* `TauCeti.HeegaardRegionSystem.knotMinusDifferential_genusZero`: the minus knot differential
  vanishes.
* `TauCeti.HeegaardRegionSystem.tau_genusZero`: the unknot has `τ = 0`.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), for doubly pointed diagrams and knot
  Floer homology.
* P. Ozsváth and Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. **7**
  (2003), [arXiv:math/0301149](https://arxiv.org/abs/math/0301149), for the invariant `τ`.
-/

public section

open LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

variable (B : Type*)

/-- The **genus-zero Heegaard diagram**: the sphere with no attaching curves and no intersection
points, whose single complementary region contains all the basepoints `B`. With one basepoint it
is a diagram of `S³`, with two a doubly pointed diagram of the unknot. -/
def genusZero : HeegaardRegionSystem 0 Empty Unit B where
  pointFintype := inferInstance
  alpha := Empty.elim
  beta := Empty.elim
  alphaNext := 1
  alphaNext_isCycleOn i := i.elim0
  betaNext := 1
  betaNext_isCycleOn j := j.elim0
  alphaLeft := Empty.elim
  alphaRight := Empty.elim
  betaLeft := Empty.elim
  betaRight := Empty.elim
  regionNonempty := inferInstance
  crossingCompatible p := p.elim
  regionCovered _ := Or.inr ⟨inferInstance, inferInstance⟩
  basepoint _ := ()

variable {B}

@[simp]
theorem genusZero_basepoint (b : B) : (genusZero B).basepoint b = () :=
  (rfl)

/-- The genus-zero diagram has a single generator, the empty tuple. -/
instance : Unique (genusZero B).Generator where
  default := ⟨1, fun i => i.elim0⟩
  uniq := fun ⟨σ, f⟩ => by
    obtain rfl : σ = 1 := Subsingleton.elim _ _
    exact Sigma.ext rfl (heq_of_eq (funext fun i => i.elim0))

/-- Every function on the single region of the genus-zero diagram is a domain from the generator
to itself: there are no arcs, so the boundary conditions are empty. -/
theorem isDomainBetween_genusZero (x y : (genusZero B).Generator) (D : Unit → ℤ) :
    (genusZero B).IsDomainBetween x y D :=
  isDomainBetween_iff.mpr ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The single region of the genus-zero diagram has no corners. -/
@[simp]
theorem cornerCount_genusZero (r : Unit) : (genusZero B).cornerCount r = 0 := by
  simp [cornerCount_eq_card]

/-- The Maslov index of a domain `D` of the genus-zero diagram, with region Euler characteristic
`2`, is `2 D`. -/
theorem maslovIndex_genusZero (x y : (genusZero B).Generator) (D : Unit → ℤ) :
    (genusZero B).maslovIndex (fun _ => 2) x y D = 2 * D () := by
  simp [maslovIndex_apply, eulerMeasure_apply, mul_comm]

/-- **The zero gradings of the unknot.** In the genus-zero diagram, whose single region is a
sphere, the Maslov and Alexander gradings `0` form a knot grading for any two basepoints. -/
theorem isKnotGrading_genusZero (w z : B) :
    (genusZero B).IsKnotGrading (fun _ => 2) w z 0 0 where
  maslov_sub_maslov {x y D} _ := by
    rw [maslovIndex_genusZero]
    simp
  alexander_sub_alexander {x y D} _ := by
    simp

/-- **The hat differential of the genus-zero diagram vanishes**: every domain has even Maslov
index `2 D`, never one. -/
@[simp]
theorem hatDifferential_genusZero : (genusZero B).hatDifferential (fun _ => 2) = 0 := by
  refine hatDifferential_eq_zero_iff.mpr fun x y => hatCoefficient_eq_zero_of_hatDomains_eq_empty ?_
  refine Set.eq_empty_of_forall_notMem fun D hD => ?_
  have hμ := (mem_hatDomains_iff.mp hD).2.2.2
  rw [maslovIndex_genusZero] at hμ
  have : 2 * D () = 1 := by exact_mod_cast hμ
  omega

/-- The hat differential of the genus-zero diagram squares to zero, since it vanishes. -/
theorem hatDifferential_genusZero_comp_self_eq_zero :
    (genusZero B).hatDifferential (fun _ => 2) ∘ₗ (genusZero B).hatDifferential (fun _ => 2) =
      0 := by
  rw [hatDifferential_genusZero, LinearMap.zero_comp]

/-- **`HFK̂` of the unknot has rank one.** The hat differential of the genus-zero diagram vanishes,
so the homology is the chain group, spanned by the single generator. -/
theorem finrank_hatHomology_genusZero :
    Module.finrank (ZMod 2)
      ((genusZero B).hatHomology (fun _ => 2) hatDifferential_genusZero_comp_self_eq_zero) = 1 := by
  rw [(((genusZero B).hatDifferential fun _ => 2).homologyEquivOfEqZero _
      hatDifferential_genusZero).finrank_eq, Module.finrank_finsupp_self, Fintype.card_unique]

/-- **The graded Euler characteristic of `HFK̂` of the unknot is `1`**, its Alexander polynomial:
the single generator has Maslov and Alexander gradings `0`. -/
theorem finsum_finrank_hatHomologyGrading_piece_smul_genusZero (w z : B) :
    ∑ᶠ p : ℤ × ℤ, Module.finrank (ZMod 2)
        (((isKnotGrading_genusZero w z).hatHomologyGrading
          hatDifferential_genusZero_comp_self_eq_zero).piece p) •
        (p.1.negOnePow • T p.2 : ℤ[T;T⁻¹]) =
      1 := by
  rw [IsKnotGrading.finsum_finrank_hatHomologyGrading_piece_smul, gradedEulerChar_def]
  simp

/-- **The minus knot differential of the genus-zero diagram vanishes**: every domain has even
Maslov index `2 D`, never one, so no domain is counted. -/
@[simp]
theorem knotMinusDifferential_genusZero (w z : B) :
    (genusZero B).knotMinusDifferential (fun _ => 2) w z = 0 := by
  refine knotMinusDifferential_eq_zero_iff.mpr fun x y => ?_
  rw [knotMinusCoefficient_def, knotCoefficient_eq_zero_of_minusDomains_eq_empty, map_zero]
  refine Set.eq_empty_of_forall_notMem fun D hD => ?_
  have hμ := (mem_minusDomains_iff.mp hD).2.2
  rw [maslovIndex_genusZero] at hμ
  have : 2 * D () = 1 := by exact_mod_cast hμ
  omega

/-- The minus knot differential of the genus-zero diagram squares to zero, since it vanishes. -/
theorem knotMinusDifferential_genusZero_comp_self_eq_zero (w z : B) :
    (genusZero B).knotMinusDifferential (fun _ => 2) w z ∘ₗ
        (genusZero B).knotMinusDifferential (fun _ => 2) w z = 0 := by
  rw [knotMinusDifferential_genusZero, LinearMap.zero_comp]

/-- **The unknot has `τ = 0`.** In the genus-zero diagram the minus knot differential vanishes, so
the single generator, of Alexander grading `0`, is a cycle none of whose multiples `U ^ k x` is a
boundary. -/
theorem tau_genusZero (w z : B) :
    (isKnotGrading_genusZero w z).tau (knotMinusDifferential_genusZero_comp_self_eq_zero w z) =
      0 := by
  rw [IsKnotGrading.tau_eq_neg_of_forall_le _ default (by simp)
    (fun k => by simp [Finsupp.single_eq_zero]) fun _ => le_rfl]
  simp

end HeegaardRegionSystem

end TauCeti
