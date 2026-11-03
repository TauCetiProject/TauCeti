/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.NodeLocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.DiscreteValuationRing
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Normalization of an analytic node

The normalization of the local ring of a node is the product of the holomorphic stalks of its
two branches. Its total ring of fractions is the product of the two branch fraction fields,
not a field. This identifies the local normalization on the native holomorphic-germ carriers,
including a self-node, whose two branches can lie on the same normalized component.

The branch inclusion is finite. A node germ is a nonzerodivisor exactly when neither branch
restriction is zero. Multiplication by a centered coordinate on each branch clears the value
matching condition, so every pair of meromorphic germs is a fraction of node germs. Finally,
the branch stalks are discrete valuation rings, and hence integrally closed; their product is
exactly the integral closure in this total ring of fractions. The node itself is not integrally
closed: the idempotent separating its branches does not descend.

The fraction-ring and integral-closure proofs adapt the corresponding polynomial-node
arguments in `TauCeti.RingTheory.Node.Normalization` to two possibly different holomorphic
stalks. No identification of convergent germs with formal power series is used.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
* Otto Forster, *Lectures on Riemann Surfaces*, §§1, 6, for holomorphic and meromorphic germs.
-/

public noncomputable section

open IsManifold
open scoped Manifold nonZeroDivisors

namespace TauCeti.holomorphicStructureSheaf.nodeLocalRing

section BranchComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'}
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] (p : X) (q : Y)

local notation "A" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf I X)) p
local notation "B" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf J Y)) q
local notation "N" => nodeLocalRing I J p q

variable (K L : Type*) [CommRing K]
  [Algebra ((holomorphicStructureSheaf I X).presheaf.stalk p) K]
  [CommRing L] [Algebra ((holomorphicStructureSheaf J Y).presheaf.stalk q) L]

/-- Restriction to the two branches followed by the algebra maps to `K` and `L`. For branch
fraction fields this is the inclusion into pairs of meromorphic germs. -/
def branchFractionMap : N →+* K × L :=
  ((algebraMap A K).prodMap (algebraMap B L)).comp (nodeLocalRing I J p q).subtype

/-- The fraction comparison is the componentwise algebra map composed with the branch inclusion. -/
theorem branchFractionMap_def :
    branchFractionMap (I := I) (J := J) p q K L =
      ((algebraMap A K).prodMap (algebraMap B L)).comp (nodeLocalRing I J p q).subtype :=
  (rfl)

/-- The fraction comparison takes the componentwise images of the branch restrictions. -/
@[simp]
theorem branchFractionMap_apply (f : N) :
    branchFractionMap p q K L f =
      (algebraMap A K (fst I J p q f), algebraMap B L (snd I J p q f)) := by
  simp [branchFractionMap, fst_apply, snd_apply, Prod.map]

variable [IsFractionRing ((holomorphicStructureSheaf I X).presheaf.stalk p) K]
  [IsFractionRing ((holomorphicStructureSheaf J Y).presheaf.stalk q) L]

/-- The meromorphic branch comparison is injective. -/
theorem branchFractionMap_injective :
    Function.Injective (branchFractionMap (I := I) (J := J) p q K L) := by
  intro f g h
  rw [branchFractionMap_apply, branchFractionMap_apply] at h
  exact ext (IsFractionRing.injective A K (congrArg Prod.fst h))
    (IsFractionRing.injective B L (congrArg Prod.snd h))

end BranchComparison

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] (p : X) (q : Y)

local notation "A" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ) X)) p
local notation "B" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ) Y)) q
local notation "N" => nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) p q

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

variable (K L : Type*) [CommRing K]
  [Algebra ((holomorphicStructureSheaf 𝓘(ℂ) X).presheaf.stalk p) K]
  [CommRing L] [Algebra ((holomorphicStructureSheaf 𝓘(ℂ) Y).presheaf.stalk q) L]

variable [IsFractionRing ((holomorphicStructureSheaf 𝓘(ℂ) X).presheaf.stalk p) K]
  [IsFractionRing ((holomorphicStructureSheaf 𝓘(ℂ) Y).presheaf.stalk q) L]

/-- The product of the branch fraction fields is the total ring of fractions of the node. -/
theorem isFractionRing_branchFractionMap :
    let := (branchFractionMap (I := 𝓘(ℂ)) (J := 𝓘(ℂ)) p q K L).toAlgebra
    IsFractionRing N (K × L) := by
  let := (branchFractionMap (I := 𝓘(ℂ)) (J := 𝓘(ℂ)) p q K L).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · intro f
    have hf := (mem_nonZeroDivisors_iff p q f.val).mp f.property
    rw [RingHom.algebraMap_toAlgebra, branchFractionMap_apply]
    exact Prod.isUnit_iff.mpr
      ⟨IsLocalization.map_units K ⟨_, mem_nonZeroDivisors_iff_ne_zero.mpr hf.1⟩,
        IsLocalization.map_units L ⟨_, mem_nonZeroDivisors_iff_ne_zero.mpr hf.2⟩⟩
  · intro z
    obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj A⁰ z.1
    obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj B⁰ z.2
    let he := chart_mem_maximalAtlas p (I := 𝓘(ℂ)) (n := 1)
    let he' := chart_mem_maximalAtlas q (I := 𝓘(ℂ)) (n := 1)
    let x := (chartAt ℂ p).holomorphicCoordinateGerm he p (mem_chart_source ℂ p)
    let y := (chartAt ℂ q).holomorphicCoordinateGerm he' q (mem_chart_source ℂ q)
    have hx : holomorphicStructureSheaf.eval 𝓘(ℂ) X p x = 0 := by simp [x]
    have hy : holomorphicStructureSheaf.eval 𝓘(ℂ) Y q y = 0 := by simp [y]
    -- Multiplying numerator and denominator by branch coordinates makes both values zero.
    let d : N := mk (s.val * x) (t.val * y) (by simp [hx, hy])
    let n : N := mk (a * x) (b * y) (by simp [hx, hy])
    have hd : d ∈ N⁰ := by
      rw [mem_nonZeroDivisors_iff, fst_mk, snd_mk]
      exact ⟨mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
        ((chartAt ℂ p).holomorphicCoordinateGerm_ne_zero he p (mem_chart_source ℂ p)),
        mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp t.property)
        ((chartAt ℂ q).holomorphicCoordinateGerm_ne_zero he' q (mem_chart_source ℂ q))⟩
    refine ⟨⟨n, ⟨d, hd⟩⟩, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, branchFractionMap_apply, d, n, fst_mk, snd_mk,
      Prod.mul_def, map_mul]
    exact Prod.ext (by dsimp; rw [← mul_assoc, ha]) (by dsimp; rw [← mul_assoc, hb])
  · intro f g h
    exact ⟨1, by simpa using branchFractionMap_injective p q K L h⟩

/-- The product of the holomorphic branch stalks is the integral closure of the node ring in
its total ring of meromorphic fractions. -/
theorem isIntegralClosure_branchFractionMap :
    let := (branchFractionMap (I := 𝓘(ℂ)) (J := 𝓘(ℂ)) p q K L).toAlgebra
    let := ((algebraMap A K).prodMap (algebraMap B L)).toAlgebra
    IsIntegralClosure (A × B) N (K × L) := by
  let := (branchFractionMap (I := 𝓘(ℂ)) (J := 𝓘(ℂ)) p q K L).toAlgebra
  let := ((algebraMap A K).prodMap (algebraMap B L)).toAlgebra
  refine ⟨?_, ?_⟩
  · intro a b h
    exact Prod.ext (IsFractionRing.injective A K (congrArg Prod.fst h))
      (IsFractionRing.injective B L (congrArg Prod.snd h))
  · intro z
    constructor
    · intro hz
      have ha : IsIntegral A z.1 := hz.map_of_comp_eq
        (fst 𝓘(ℂ) 𝓘(ℂ) p q) (RingHom.fst K L) (by
          ext f
          simp [branchFractionMap_apply, RingHom.algebraMap_toAlgebra])
      have hb : IsIntegral B z.2 := hz.map_of_comp_eq
        (snd 𝓘(ℂ) 𝓘(ℂ) p q) (RingHom.snd K L) (by
          ext f
          simp [branchFractionMap_apply, RingHom.algebraMap_toAlgebra])
      obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff K).mp inferInstance ha
      obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff L).mp inferInstance hb
      exact ⟨(a, b), Prod.ext ha hb⟩
    · rintro ⟨z, rfl⟩
      exact ((finite_subtype 𝓘(ℂ) 𝓘(ℂ) p q).to_isIntegral z).map
        ((algebraMap A K).prodMap (algebraMap B L))

/-- A node is not integrally closed: its normalization separates the two branches. -/
theorem not_isIntegrallyClosed : ¬ IsIntegrallyClosed N := by
  let K := FractionRing A
  let L := FractionRing B
  let := (branchFractionMap (I := 𝓘(ℂ)) (J := 𝓘(ℂ)) p q K L).toAlgebra
  have := isFractionRing_branchFractionMap p q K L
  have hint : IsIntegral N ((1, 0) : K × L) := by
    simpa only [IsIntegral, RingHom.algebraMap_toAlgebra, branchFractionMap,
      RingHom.coe_prodMap, Prod.map, map_one, map_zero] using
      ((finite_subtype 𝓘(ℂ) 𝓘(ℂ) p q).to_isIntegral (1, 0)).map
        ((algebraMap A K).prodMap (algebraMap B L))
  intro h
  obtain ⟨f, hf⟩ := (isIntegrallyClosed_iff (K × L)).mp h hint
  have ha : fst 𝓘(ℂ) 𝓘(ℂ) p q f = 1 :=
    IsFractionRing.injective A K (by
      simpa only [RingHom.algebraMap_toAlgebra, branchFractionMap_apply, Prod.fst_one,
        map_one] using congrArg Prod.fst hf)
  have hb : snd 𝓘(ℂ) 𝓘(ℂ) p q f = 0 :=
    IsFractionRing.injective B L (by
      simpa only [RingHom.algebraMap_toAlgebra, branchFractionMap_apply, Prod.snd_zero,
        map_zero] using congrArg Prod.snd hf)
  have he := (eval_fst f).trans (eval_snd f).symm
  simp [ha, hb] at he

end TauCeti.holomorphicStructureSheaf.nodeLocalRing
