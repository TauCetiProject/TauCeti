/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Tangent.SpecialLinear
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Sl2Triple.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.FiniteEtale
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Augmentation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Etale
import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.SpecialLinear
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Center.FiniteFlat
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The central kernel of an integrated `sl₂` triple and `PGL₂` factorization

This file classifies the algebraic image of an integrated `sl₂` triple `SL₂ ⟶ G` (for a finite-type
affine group `G = Spec H` over a characteristic-zero field `k`) up to central isogeny into simply
connected (`SL₂`) versus adjoint (`PGL₂`) type. Its scheme-theoretic kernel is finite étale and
central in `SL₂`, hence either trivial (`HopfIdeal.augmentation`) or `Z(SL₂)`
(`IsSl2Triple.kernelHopfIdeal_sl2CoordinateMap_eq_augmentation_or_eq_centerDefiningIdeal`), and it
factors uniquely through `SL₂ ⟶ PGL₂` iff its kernel equals `Z(SL₂)`
(`IsSl2Triple.existsUnique_comp_conjugationMap_sl2CoordinateMap_iff`). Both types occur via
`SpecialLinear.isSl2Triple_tangentLieEquivSl_symm_single` and
`SpecialLinear.isSl2Triple_derivationCompLieHom_conjugationMap`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7; J. S. Milne, *Algebraic Groups*, Ch. 10, 21.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, §3.3, §3.7.
* J. E. Humphreys, *Conjugacy Classes in Semisimple Algebraic Groups*, AMS, 1995, §8.4.
-/

public section

open CategoryTheory LieAlgebra TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

universe u

variable {k H : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] {h e f : Derivation k H (Bialgebra.CounitAlgebra k H k)}

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` has trivial tangent Lie algebra.** -/
@[simp] theorem lieSubalgebra_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).lieSubalgebra (B := k) = ⊥ := by
  ext d; rw [CommHopfAlgCat.lieSubalgebra_kernelHopfIdeal, LieIdeal.mem_toLieSubalgebra,
    LieHom.mem_ker, LieSubalgebra.mem_bot]
  exact ⟨fun hd ↦ t.derivationCompLieHom_sl2CoordinateMap_injective (hd.trans (map_zero _).symm),
    fun hd ↦ hd ▸ map_zero _⟩

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is étale over `k`.** -/
theorem algebraEtale_quotient_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    Algebra.Etale k (SpecialLinear.coordinateHopfAlgebra k 2 ⧸
      (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).toIdeal) :=
  (CommHopfAlgCat.algebraEtale_quotient_kernelHopfIdeal_iff t.sl2CoordinateMap).mpr
    t.derivationCompLieHom_sl2CoordinateMap_injective

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is finite over `k`.** -/
theorem moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    Module.Finite k (SpecialLinear.coordinateHopfAlgebra k 2 ⧸
      (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).toIdeal) :=
  CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal_of_derivationCompLieHom_injective
    t.derivationCompLieHom_sl2CoordinateMap_injective

/-- **The scheme-theoretic kernel of `t.sl2CoordinateMap` is central in `SL₂`.** -/
theorem isCentral_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    (CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap).IsCentral := by
  let A := SpecialLinear.coordinateHopfAlgebra k 2
  let _ := t.moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap
  let _ := t.algebraEtale_quotient_kernelHopfIdeal_sl2CoordinateMap
  exact HopfIdeal.IsNormal.isCentral_of_finite_of_isGeometricallyReduced
    (H := ⟨A, inferInstanceAs (Algebra.FiniteType k _)⟩)
    (CommHopfAlgCat.isNormal_kernelHopfIdeal t.sl2CoordinateMap)
    (SpecialLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k 2)

/-- **The scheme-theoretic kernel of `SL₂ ⟶ G` is contained in `Z(SL₂) = μ₂`.** -/
theorem centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) ≤
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap :=
  (CommHopfAlgCat.centerDefiningIdeal_le_iff _ _).mpr t.isCentral_kernelHopfIdeal_sl2CoordinateMap

/-- **Kernel dichotomy for integrated `sl₂` triples.** The scheme-theoretic kernel of `SL₂ ⟶ G` is
either trivial (`HopfIdeal.augmentation`) or the full center `Z(SL₂)` (`centerDefiningIdeal`). -/
theorem kernelHopfIdeal_sl2CoordinateMap_eq_augmentation_or_eq_centerDefiningIdeal
    (t : IsSl2Triple h e f) :
    CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap =
        HopfIdeal.augmentation k (SpecialLinear.coordinateHopfAlgebra k 2) ∨
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap =
        CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) := by
  let A := SpecialLinear.coordinateHopfAlgebra k 2; let ε := HopfIdeal.augmentation k A
  let Z := CommHopfAlgCat.centerDefiningIdeal A
  let K := CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap
  have hZK : Z ≤ K := t.centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap
  have hKε : K ≤ ε := HopfIdeal.le_augmentation k A K
  let _ : Module.Finite k (CommHopfAlgCat.quotient A Z) :=
    SpecialLinear.moduleFinite_centerCoordinate 2 zero_lt_two
  let _ : Module.Finite k (CommHopfAlgCat.quotient A K) :=
    t.moduleFinite_quotient_kernelHopfIdeal_sl2CoordinateMap
  let _ := HopfIdeal.moduleFinite_quotient_augmentation (R := k) A
  have hdimZ := SpecialLinear.finrank_centerCoordinate (k := k) 2 zero_lt_two
  have hdimε := HopfIdeal.finrank_quotient_augmentation (R := k) A
  have hle2 := (LinearMap.finrank_le_finrank_of_surjective
    (CommHopfAlgCat.quotientMapOfLe_surjective A hZK)).trans hdimZ.le
  have hge1 := hdimε.symm.le.trans (LinearMap.finrank_le_finrank_of_surjective
    (CommHopfAlgCat.quotientMapOfLe_surjective A hKε))
  rcases (by omega : Module.finrank k (CommHopfAlgCat.quotient A K) = 1 ∨
      Module.finrank k (CommHopfAlgCat.quotient A K) = 2) with h1 | h2
  · exact Or.inl (HopfIdeal.eq_of_le_of_finrank_quotient_le hKε (h1.trans hdimε.symm).le)
  · exact Or.inr (HopfIdeal.eq_of_le_of_finrank_quotient_le hZK (hdimZ.trans h2.symm).le).symm

/-- **`PGL₂` factorization.** `t.sl2CoordinateMap` factors (uniquely) through `SL₂ ⟶ PGL₂`
(`SpecialLinear.conjugationMap 2 k`) if and only if its scheme-theoretic kernel equals `Z(SL₂)`. -/
theorem existsUnique_comp_conjugationMap_sl2CoordinateMap_iff (t : IsSl2Triple h e f) :
    (∃! ψ : CommHopfAlgCat.of k H ⟶ ProjectiveGeneralLinear.coordinateHopfAlgebra 2 k,
        ψ ≫ SpecialLinear.conjugationMap 2 k = t.sl2CoordinateMap) ↔
      CommHopfAlgCat.kernelHopfIdeal t.sl2CoordinateMap =
        CommHopfAlgCat.centerDefiningIdeal (SpecialLinear.coordinateHopfAlgebra k 2) := by
  rw [ProjectiveGeneralLinear.existsUnique_comp_conjugationMap_iff]
  exact ⟨fun hle ↦ le_antisymm hle t.centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap,
    le_of_eq⟩

end IsSl2Triple

namespace TauCeti.SpecialLinear

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The integrated morphism of the standard `sl₂` triple on `SL₂` has trivial kernel. -/
@[simp] theorem kernelHopfIdeal_sl2CoordinateMap_isSl2Triple_tangentLieEquivSl_symm_single :
    CommHopfAlgCat.kernelHopfIdeal (isSl2Triple_tangentLieEquivSl_symm_single k).sl2CoordinateMap =
      HopfIdeal.augmentation k (coordinateHopfAlgebra k 2) := by
  rw [IsSl2Triple.sl2CoordinateMap_tangentLieEquivSl_symm_single]
  exact CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective _ Function.surjective_id

/-- `isSl2Triple_derivationCompLieHom_conjugationMap k` integrates to `SL₂ ⟶ PGL₂`. -/
@[simp] theorem sl2CoordinateMap_isSl2Triple_derivationCompLieHom_conjugationMap :
    (isSl2Triple_derivationCompLieHom_conjugationMap k).sl2CoordinateMap = conjugationMap 2 k := by
  rw [(isSl2Triple_tangentLieEquivSl_symm_single k).sl2CoordinateMap_map (conjugationMap 2 k)
      (derivationCompLieHom_conjugationMap_two_ne_zero k),
    IsSl2Triple.sl2CoordinateMap_tangentLieEquivSl_symm_single, Category.comp_id]

/-- `isSl2Triple_derivationCompLieHom_conjugationMap k` has scheme-theoretic kernel `Z(SL₂)`. -/
@[simp] theorem kernelHopfIdeal_sl2CoordinateMap_isSl2Triple_derivationCompLieHom_conjugationMap :
    CommHopfAlgCat.kernelHopfIdeal
        (isSl2Triple_derivationCompLieHom_conjugationMap k).sl2CoordinateMap =
      CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k 2) := by
  rw [sl2CoordinateMap_isSl2Triple_derivationCompLieHom_conjugationMap,
    kernelHopfIdeal_conjugationMap]

end TauCeti.SpecialLinear
