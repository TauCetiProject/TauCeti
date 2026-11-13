/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Pinned
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic

/-!
# The pinned type-B action on the spin lattice

The full type-B spin module is originally a representation of the split odd orthogonal
matrix Lie algebra. Here it is read as a representation of the independently pinned rational
Lie algebra through `TauCeti.typeBPinnedLieEquiv`. The numbered Cartan, raising and lowering
operators are unchanged, including the terminal short root.

The pinned simple-generator Kostant form preserves the existing integral exterior lattice,
and its existing basis has the same integral spin weights. These are the admissibility and
weight-basis inputs to a full-weight Chevalley datum on the spin module. Faithfulness and
comparison of group schemes are not asserted here.

The construction uses the native spin representation and lattice from
`TauCeti.TypeBSpinCarrier`, the numbered orthogonal Lie equivalence
`TauCeti.typeBPinnedLieEquiv`, and `UniversalEnvelopingAlgebra.map_kostantForm`.
In particular, stability concerns all divided powers and Cartan binomial operators, not just
the degree-one Lie generators.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4–6, Plate II.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (ht : (DynkinType.B (n + 1)).Valid)

/-- The enveloping-algebra action of the pinned rational type-`Bₙ₊₁` Lie algebra on the
full spin module, obtained from the native odd orthogonal spin action. -/
def pinnedRep :
    _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.B (n + 1)).lieAlgebra ht) →ₐ[ℚ]
      Module.End ℚ (ExteriorAlgebra ℚ (polarization n).W) :=
  (rep n).comp (map ℚ (typeBPinnedLieEquiv n ht).toLieHom)

/-- The pinned action is the native spin action composed with the induced enveloping map. -/
theorem pinnedRep_def :
    pinnedRep n ht = (rep n).comp (map ℚ (typeBPinnedLieEquiv n ht).toLieHom) := (rfl)

/-- On an enveloping-algebra element, the pinned action is the native action of its image. -/
theorem pinnedRep_apply
    (u : _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.B (n + 1)).lieAlgebra ht)) :
    pinnedRep n ht u = rep n (map ℚ (typeBPinnedLieEquiv n ht).toLieHom u) := (rfl)

/-- On a Lie element, the pinned action is the native spin action after the numbered
orthogonal Lie equivalence. -/
-- Try the numbered-operator equations before this fallback: simplifying the included
-- Lie element first can obscure the dependent Dynkin-rank index of the root family.
@[simp↓ 900]
theorem pinnedRep_ι (x : (DynkinType.B (n + 1)).lieAlgebra ht) :
    pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (typeBPinnedLieEquiv n ht x)) := by
  simp only [pinnedRep, AlgHom.comp_apply, map_ι, LieEquiv.coe_toLieHom]

/-- The generator equation for the pinned action in the simplifier's normal form. -/
@[simp]
theorem pinnedRep_ι' (x : (DynkinType.B (n + 1)).lieAlgebra ht) :
    pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ
        ((DynkinType.B (n + 1)).lieAlgebra ht) (TensorAlgebra.ι ℚ x)) =
      rep n (_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ
        (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) ℚ)
        (TensorAlgebra.ι ℚ (typeBPinnedLieEquiv n ht x))) := by
  simp only [pinnedRep, AlgHom.comp_apply, map_ι', LieEquiv.coe_toLieHom]

/-- The pinned Cartan operator is the original spin simple-coroot operator. -/
@[simp↓]
theorem pinnedRep_ι_h (i : Fin (n + 1)) :
    pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.B (n + 1)).lieBasis ht).h i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (typeBSimpleCorootGenerator i)) := by
  rw [pinnedRep_ι, typeBPinnedLieEquiv_lieBasis_h]

/-- The pinned raising operator is the original positive simple-root spin operator. -/
@[simp↓]
theorem pinnedRep_ι_e (i : Fin (n + 1)) :
    pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.B (n + 1)).lieBasis ht).e i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (typeBSimpleRootGenerator i)) := by
  rw [pinnedRep_ι, typeBPinnedLieEquiv_lieBasis_e]

/-- The pinned lowering operator is the original negative simple-root spin operator. -/
@[simp↓]
theorem pinnedRep_ι_f (i : Fin (n + 1)) :
    pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.B (n + 1)).lieBasis ht).f i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (typeBSimpleNegativeRootGenerator i)) := by
  rw [pinnedRep_ι, typeBPinnedLieEquiv_lieBasis_f]

/-- Both signs of the pinned simple-root family act by the native spin operators. -/
@[simp↓]
theorem pinnedRep_ι_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (((DynkinType.B (n + 1)).lieBasis ht).rootGenerator k)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (typeBSimpleRootGeneratorFamily k)) := by
  rw [pinnedRep_ι]
  exact congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
    (typeBPinnedLieEquiv_lieBasis_rootGenerator n ht k)

/-- The pinned simple-generator Kostant form preserves the integral exterior spin lattice. -/
theorem pinnedRep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.B (n + 1)).lieAlgebra ht))
    (hu : u ∈ kostantForm ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
      ((DynkinType.B (n + 1)).lieBasis ht).h)
    (v : ExteriorAlgebra ℚ (polarization n).W) (hv : v ∈ lattice n) :
    pinnedRep n ht u v ∈ lattice n := by
  apply rep_kostantForm_mem_lattice n _ ?_ v hv
  have hmap := map_kostantForm (typeBPinnedLieEquiv n ht).toLieHom
    ((DynkinType.B (n + 1)).lieBasis ht).rootGenerator
    ((DynkinType.B (n + 1)).lieBasis ht).h
  have he : (fun k => typeBPinnedLieEquiv n ht
      (((DynkinType.B (n + 1)).lieBasis ht).rootGenerator k)) =
      typeBSimpleRootGeneratorFamily (K := ℚ) :=
    funext (typeBPinnedLieEquiv_lieBasis_rootGenerator n ht)
  have hh : (fun i => typeBPinnedLieEquiv n ht
      (((DynkinType.B (n + 1)).lieBasis ht).h i)) =
      typeBSimpleCorootGenerator (K := ℚ) :=
    funext (typeBPinnedLieEquiv_lieBasis_h n ht)
  simp only [LieEquiv.coe_toLieHom, he, hh] at hmap
  -- The mapped families use the Dynkin rank; the native form uses n + 1.
  erw [← hmap]
  exact ⟨u, hu, rfl⟩

/-- Every signed pinned simple-root operator squares to zero on the full spin module. -/
theorem pow_two_pinnedRep_rootGenerator_eq_zero (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.B (n + 1)).lieBasis ht).rootGenerator k)) ^ 2 = 0 := by
  rw [pinnedRep_ι_rootGenerator]
  exact pow_two_rep_rootGenerator_eq_zero n k

/-- The pinned signed simple-root operators are nilpotent. -/
theorem isNilpotent_pinnedRep_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    IsNilpotent (pinnedRep n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.B (n + 1)).lieBasis ht).rootGenerator k))) :=
  ⟨2, pow_two_pinnedRep_rootGenerator_eq_zero n ht k⟩

/-- The exterior lattice basis retains its native integral spin weights for the pinned
Cartan action, in fundamental-weight coordinates. -/
theorem isCartanWeightVector_pinnedRep_latticeBasis (i : Fin (dimension n)) :
    IsCartanWeightVector ((DynkinType.B (n + 1)).lieBasis ht).h (pinnedRep n ht)
      (basisWeight n i)
      ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
  refine (isCartanWeightVector_iff _ _).2 fun j => ?_
  -- The pinned Cartan is indexed by the Dynkin rank, definitionally n + 1;
  -- reduce that rank when matching the native operator equation.
  erw [pinnedRep_ι_h]
  exact (isCartanWeightVector_iff _ _).1 (isCartanWeightVector_latticeBasis n i) j

end

end TauCeti.TypeBSpinCarrier
