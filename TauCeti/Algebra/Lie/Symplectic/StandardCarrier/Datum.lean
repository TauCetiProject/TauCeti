/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Datum
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Pinned

/-!
# The standard symplectic Chevalley datum

The standard representation of the symplectic Lie algebra, its coordinate lattice and its
integral weight basis define a full-weight Chevalley datum of type C. This file transports
that action along `TauCeti.SpStd.pinnedLieEquiv` and packages the result as
`TauCeti.SpStd.chevalleyDatum`. The rational module, integral lattice and ordered basis are
unchanged. Both signs of the pinned simple generators act by the native symplectic matrices,
and the actual character-lattice torus uses fundamental-weight coordinates.

This datum supplies the standard symplectic input to comparisons of Chevalley group schemes.
It does not itself identify its group scheme with the canonical full-weight construction.
Admissibility uses functoriality of the Kostant form and the existing
`SpStd.rep_kostantForm_mem_lattice`; the weight-basis and full-weight calculations are those of
`SpStd.isCartanWeightVector_latticeBasis` and `SpStd.span_range_basisWeight_eq_top`.
The packaging follows `TauCeti.F4ShortRoot.chevalleyDatum`; the character-coordinate equations
use the general `DynkinType.ChevalleyDatum` lemmas for a fundamental-weight basis.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Plate III.
-/

public section

namespace TauCeti.SpStd

noncomputable section

variable (n : ℕ) (ht : (DynkinType.C (n + 1)).Valid)

/-- The standard symplectic action of the pinned rational type-C Lie algebra, extended to its
universal enveloping algebra. -/
def pinnedRepresentation :
    _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.C (n + 1)).lieAlgebra ht) →ₐ[ℚ]
      Module.End ℚ ((Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :=
  (rep n).comp (UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv n ht).toLieHom)

/-- The pinned action is the native standard action after the pinned Lie equivalence. -/
theorem pinnedRepresentation_def :
    pinnedRepresentation n ht =
      (rep n).comp (UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv n ht).toLieHom) :=
  (rfl)

private theorem pinnedRepresentation_ι_eq (x : (DynkinType.C (n + 1)).lieAlgebra ht) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (pinnedLieEquiv n ht x)) := by
  rw [pinnedRepresentation_def, AlgHom.comp_apply, UniversalEnvelopingAlgebra.map_ι,
    LieEquiv.coe_toLieHom]

/-- On Lie elements, the pinned action is multiplication by the corresponding symplectic
matrix. -/
theorem pinnedRepresentation_ι (x : (DynkinType.C (n + 1)).lieAlgebra ht) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Matrix.toLin' (pinnedLieEquiv n ht x).val := by
  apply LinearMap.ext
  intro v
  rw [pinnedRepresentation_ι_eq, rep_ι_apply, Matrix.toLin'_apply]

/-- The pinned standard action is faithful on the Lie algebra. -/
theorem pinnedRepresentation_ι_injective :
    Function.Injective (fun x : (DynkinType.C (n + 1)).lieAlgebra ht =>
      pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) := by
  intro x y hxy
  dsimp only at hxy
  rw [pinnedRepresentation_ι, pinnedRepresentation_ι] at hxy
  exact (pinnedLieEquiv n ht).injective (Subtype.ext (Matrix.toLin'.injective hxy))

-- Type C computes to rank `n + 1`. In the public h/e/f equations below, the cast
-- identifies the pinned index with the native one and is a self-cast by `Fin.cast_eq_self`.

/-- A pinned Cartan generator acts by the native standard Cartan operator. -/
@[simp↓]
theorem pinnedRepresentation_ι_h (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.C (n + 1)).lieBasis ht).h i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (cartanGenerator n (Fin.cast (DynkinType.rank_C _) i))) := by
  rw [pinnedRepresentation_ι_eq]
  exact congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
    (pinnedLieEquiv_lieBasis_h n ht i)

/-- A pinned positive simple generator acts by the native standard root operator. -/
@[simp↓]
theorem pinnedRepresentation_ι_e (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.C (n + 1)).lieBasis ht).e i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator n (.inl (Fin.cast (DynkinType.rank_C _) i)))) := by
  rw [pinnedRepresentation_ι_eq]
  exact congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
    (pinnedLieEquiv_lieBasis_e n ht i)

/-- A pinned negative simple generator acts by the native standard root operator. -/
@[simp↓]
theorem pinnedRepresentation_ι_f (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.C (n + 1)).lieBasis ht).f i)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator n (.inr (Fin.cast (DynkinType.rank_C _) i)))) := by
  rw [pinnedRepresentation_ι_eq]
  exact congrArg (fun x => rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x))
    (pinnedLieEquiv_lieBasis_f n ht i)

/-- A positive pinned root generator acts by the native standard positive root operator. -/
@[simp↓]
theorem pinnedRepresentation_ι_rootGenerator_inl (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.C (n + 1)).lieBasis ht).rootGenerator (.inl i))) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator n (.inl (Fin.cast (DynkinType.rank_C _) i)))) := by
  rw [LieAlgebra.Basis.rootGenerator_inl, pinnedRepresentation_ι_e]

/-- A negative pinned root generator acts by the native standard negative root operator. -/
@[simp↓]
theorem pinnedRepresentation_ι_rootGenerator_inr (i : Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.C (n + 1)).lieBasis ht).rootGenerator (.inr i))) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator n (.inr (Fin.cast (DynkinType.rank_C _) i)))) := by
  rw [LieAlgebra.Basis.rootGenerator_inr, pinnedRepresentation_ι_f]

/-- Each signed pinned simple root acts by the corresponding native standard root operator. -/
@[simp↓ low]
theorem pinnedRepresentation_ι_rootGenerator
    (k : Fin (DynkinType.C (n + 1)).rank ⊕ Fin (DynkinType.C (n + 1)).rank) :
    pinnedRepresentation n ht (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (((DynkinType.C (n + 1)).lieBasis ht).rootGenerator k)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (rootGenerator n (k.map (Fin.cast (DynkinType.rank_C _))
          (Fin.cast (DynkinType.rank_C _))))) := by
  cases k <;> simp only [Sum.map_inl, Sum.map_inr, pinnedRepresentation_ι_rootGenerator_inl,
    pinnedRepresentation_ι_rootGenerator_inr]

-- Use native indices for the Kostant form comparison; type C has definitional rank `n + 1`.
private theorem pinnedLieEquiv_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    pinnedLieEquiv n ht (((DynkinType.C (n + 1)).lieBasis ht).rootGenerator k) =
      rootGenerator n k := by
  cases k with
  | inl i =>
    exact (congrArg (pinnedLieEquiv n ht) (LieAlgebra.Basis.rootGenerator_inl _ i)).trans
      (pinnedLieEquiv_lieBasis_e n ht i)
  | inr i =>
    exact (congrArg (pinnedLieEquiv n ht) (LieAlgebra.Basis.rootGenerator_inr _ i)).trans
      (pinnedLieEquiv_lieBasis_f n ht i)

private theorem pinnedRepresentation_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ ((DynkinType.C (n + 1)).lieAlgebra ht)}
    (hu : u ∈ UniversalEnvelopingAlgebra.kostantForm
      ((DynkinType.C (n + 1)).lieBasis ht).rootGenerator
      ((DynkinType.C (n + 1)).lieBasis ht).h)
    {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} (hv : v ∈ lattice n) :
    pinnedRepresentation n ht u v ∈ lattice n := by
  rw [pinnedRepresentation_def, AlgHom.comp_apply]
  apply rep_kostantForm_mem_lattice n _ _ _ hv
  have hmap : UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv n ht).toLieHom u ∈
      (UniversalEnvelopingAlgebra.kostantForm
        ((DynkinType.C (n + 1)).lieBasis ht).rootGenerator
        ((DynkinType.C (n + 1)).lieBasis ht).h).map
          (UniversalEnvelopingAlgebra.map ℚ (pinnedLieEquiv n ht).toLieHom).toRingHom :=
    ⟨u, hu, rfl⟩
  rw [UniversalEnvelopingAlgebra.map_kostantForm] at hmap
  have he : (fun k => (pinnedLieEquiv n ht)
      (((DynkinType.C (n + 1)).lieBasis ht).rootGenerator k)) = rootGenerator n :=
    funext (pinnedLieEquiv_rootGenerator n ht)
  -- The Cartan comparison already uses the native index type, as does `cartanGenerator`.
  have hh : (fun i => (pinnedLieEquiv n ht)
      (((DynkinType.C (n + 1)).lieBasis ht).h i)) = cartanGenerator n :=
    funext (pinnedLieEquiv_lieBasis_h n ht)
  simp only [LieEquiv.coe_toLieHom, he, hh] at hmap
  exact hmap

private theorem isCartanWeightVector_pinned (a : Fin ((n + 1) + (n + 1))) :
    UniversalEnvelopingAlgebra.IsCartanWeightVector
      ((DynkinType.C (n + 1)).lieBasis ht).h (pinnedRepresentation n ht)
      (basisWeight n a) ((latticeBasis n a : (lattice n).toAddSubgroup) :
        (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) := by
  apply (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mpr
  intro i
  rw [pinnedRepresentation_ι_h n ht i]
  -- The cast in the Cartan equation is a self-cast, so the native weight-vector theorem applies.
  exact (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).mp
    (isCartanWeightVector_latticeBasis n a) i

/-- The full-weight Chevalley datum on the standard symplectic module, with its existing
integral coordinate lattice and ordered coordinate basis. -/
-- Reducibility lets the carrier and module instances compute when applying native coordinate
-- operators to the datum; an opaque definition would obstruct these dependent applications.
abbrev chevalleyDatum : DynkinType.ChevalleyDatum (.C (n + 1)) ht where
  carrier := (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ
  representation := pinnedRepresentation n ht
  injective_representation_ι := pinnedRepresentation_ι_injective n ht
  lattice := (lattice n).toAddSubgroup
  representation_mem_lattice := by
    exact fun _ hu _ hv => pinnedRepresentation_mem_lattice n ht hu hv
  span_lattice_eq_top := by
    apply top_unique
    rw [← (Pi.basisFun ℚ (Fin (n + 1) ⊕ Fin (n + 1))).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    rw [Pi.basisFun_apply]
    exact single_mem_lattice n a
  dim := (n + 1) + (n + 1)
  basis := latticeBasis n
  weight := basisWeight n
  isCartanWeightVector_basis := by exact isCartanWeightVector_pinned n ht
  weightLatticeBasis := (Pi.basisFun ℤ (Fin (n + 1))).map
    (LinearEquiv.ofTop _ (span_range_basisWeight_eq_top n)).symm

/-- The datum basis is the native ordered rational coordinate basis. -/
@[simp↓]
theorem coe_chevalleyDatum_basis (a : Fin ((n + 1) + (n + 1))) :
    (((chevalleyDatum n ht).basis a).val : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) =
      Pi.single (finSumFinEquiv.symm a) 1 :=
  coe_latticeBasis n a

/-- The character-lattice basis of the standard datum consists of the fundamental weights. -/
@[simp↓]
theorem coe_chevalleyDatum_weightLatticeBasis (i : Fin (DynkinType.C (n + 1)).rank) :
    ((chevalleyDatum n ht).weightLatticeBasis i).val = Pi.single i 1 := by
  -- Apply the native mapped-basis equation before identifying its index with the type-C rank.
  have h := congrArg (fun v : Submodule.span ℤ (Set.range (basisWeight n)) =>
      (v : Fin (n + 1) → ℤ))
    (Module.Basis.map_apply (Pi.basisFun ℤ (Fin (n + 1)))
      (LinearEquiv.ofTop _ (span_range_basisWeight_eq_top n)).symm i)
  exact h.trans (Pi.basisFun_apply ℤ (Fin (n + 1)) i)

/-- The standard symplectic datum has the full weight lattice. -/
@[simp]
theorem chevalleyDatum_weightLattice : (chevalleyDatum n ht).weightLattice = ⊤ :=
  (chevalleyDatum n ht).weightLattice_def.trans (span_range_basisWeight_eq_top n)

/-- The actual torus coordinates are the native fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_coordinateWeight :
    (chevalleyDatum n ht).coordinateWeight = basisWeight n :=
  (chevalleyDatum n ht).coordinateWeight_eq_of_coe_weightLatticeBasis
    (coe_chevalleyDatum_weightLatticeBasis n ht)

/-- Root characters use the pinned root datum's fundamental-weight coordinates. -/
@[simp]
theorem chevalleyDatum_coordinateRoot (γ : Fin (DynkinType.C (n + 1)).numRoots) :
    (chevalleyDatum n ht).coordinateRoot γ =
      ((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root γ :=
  (chevalleyDatum n ht).coordinateRoot_eq_of_coe_weightLatticeBasis
    (coe_chevalleyDatum_weightLatticeBasis n ht) γ

end

end TauCeti.SpStd
