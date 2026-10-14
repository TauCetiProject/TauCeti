/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross

/-!
# Associativity of the homology cross product

The cross product of three classes of cycles is independent of parenthesization, after
transport along the tensor associator of the complexes and that of the homology objects.
This is the algebraic associativity identity used when comparing iterated cross products
under the Eilenberg–Zilber maps, and hence when forming products in the homology of a
topological monoid.

The cycle identity needs only the indicated homology objects and tensor products. The
homology identity additionally assumes that left and right tensoring preserve cokernels.
Neither a braiding nor a flatness hypothesis is needed. Intermediate degrees are explicit,
so the statements can be used without transporting homology objects across degree equalities.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6.
* A. Hatcher, *Algebraic Topology*, Section 3.B.

The tensor associator and its homogeneous-summand formula are Mathlib's
`HomologicalComplex.mapBifunctorAssociator` and
`HomologicalComplex.ι_mapBifunctorAssociatorX_hom`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
  (K L M : HomologicalComplex C c)
  [HasTensor K L] [HasTensor L M]
  [HasTensor (tensorObj K L) M] [HasTensor K (tensorObj L M)]
  [HasGoodTensor₁₂ K L M] [HasGoodTensor₂₃ K L M]
  (p q r pq qr n : I) (hpq : p + q = pq) (hqr : q + r = qr)
  (hn : pq + r = n) (hn' : p + qr = n)
  [K.HasHomology p] [L.HasHomology q] [M.HasHomology r]
  [(tensorObj K L).HasHomology pq] [(tensorObj L M).HasHomology qr]
  [(tensorObj (tensorObj K L) M).HasHomology n]
  [(tensorObj K (tensorObj L M)).HasHomology n]

/-- Tensor products of cycles associate through the tensor associator of complexes. -/
@[reassoc]
lemma cyclesCross_assoc :
    (cyclesCross K L p q pq hpq ▷ M.cycles r) ≫
        cyclesCross (tensorObj K L) M pq r n hn ≫
        cyclesMap (associator K L M).hom n =
      (α_ (K.cycles p) (L.cycles q) (M.cycles r)).hom ≫
        (K.cycles p ◁ cyclesCross L M q r qr hqr) ≫
        cyclesCross K (tensorObj L M) p qr n hn' := by
  rw [← cancel_mono ((tensorObj K (tensorObj L M)).iCycles n)]
  simp only [Category.assoc, cyclesMap_i, cyclesCross_iCycles]
  -- Rewrite the iterated cycle inclusions as the triple homogeneous summands to which
  -- Mathlib's associator formula applies.
  have hι := ι_mapBifunctorAssociatorX_hom (curriedAssociatorNatIso C) K L M c c c
    p q r n (by
      -- The total-complex index is definitionally (p + q) + r.
      dsimp [ComplexShape.r]
      simpa only [hpq] using hn)
  rw [mapBifunctor₁₂.ι_eq (curriedTensor C) (curriedTensor C) K L M c c
      p q r pq n hpq hn,
    mapBifunctor₂₃.ι_eq (curriedTensor C) (curriedTensor C) K L M c c c
      p q r qr n hqr hn'] at hι
  simp only [curriedAssociatorNatIso_hom_app_app_app] at hι
  have h := congrArg (((K.iCycles p ⊗ₘ L.iCycles q) ⊗ₘ M.iCycles r) ≫ ·) hι
  rw [Category.assoc, associator_naturality_assoc] at h
  -- The component of the complex associator is exactly mapBifunctorAssociatorX.
  simp only [tensorHom_def, Category.assoc, cyclesCross_iCycles_assoc]
  rw [whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
    cyclesCross_iCycles]
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc, whisker_exchange_assoc, curriedTensor_map_app, curriedTensor_obj_map] at h ⊢
  exact h

section Homology

variable
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (L.homology q))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft ((tensorObj K L).homology pq))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (M.cycles r))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (M.X (c.prev r)))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight ((tensorObj L M).cycles qr))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight ((tensorObj L M).X (c.prev qr)))]

/-- The homology cross product is associative: `(a × b) × d` becomes `a × (b × d)`
under the tensor associator of complexes, with no sign correction. -/
@[reassoc]
lemma homologyCross_assoc :
    (homologyCross K L p q pq hpq ▷ M.homology r) ≫
        homologyCross (tensorObj K L) M pq r n hn ≫
        homologyMap (associator K L M).hom n =
      (α_ (K.homology p) (L.homology q) (M.homology r)).hom ≫
        (K.homology p ◁ homologyCross L M q r qr hqr) ≫
        homologyCross K (tensorObj L M) p qr n hn' := by
  let : PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (K.homology p ⊗ L.homology q)) :=
    preservesColimitsOfShape_of_natIso (tensorLeftTensor (K.homology p) (L.homology q)).symm
  -- Descend one homology quotient at a time. Tensoring preserves each cokernel,
  -- including the two successive right tensorings on the first factor.
  apply Cofork.IsColimit.hom_ext (M.homologyWhiskerLeftIsCokernel r
    (K.homology p ⊗ L.homology q))
  apply Cofork.IsColimit.hom_ext (CokernelCofork.mapIsColimit _
    (L.homologyIsCokernel (c.prev q) q rfl)
    (tensorLeft (K.homology p) ⋙ tensorRight (M.cycles r)))
  apply Cofork.IsColimit.hom_ext (CokernelCofork.mapIsColimit _
    (K.homologyIsCokernel (c.prev p) p rfl)
    (tensorRight (L.cycles q) ⋙ tensorRight (M.cycles r)))
  simp only [CokernelCofork.map_π, Cofork.π_ofπ, Functor.comp_map]
  simp only [tensorRight, tensorLeft, Functor.flip_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map]
  simp only [← comp_whiskerRight_assoc]
  rw [← tensorHom_def (K.homologyπ p) (L.homologyπ q),
    ← tensorHom_def_assoc (K.homologyπ p ⊗ₘ L.homologyπ q) (M.homologyπ r)]
  rw [← tensorHom_def_assoc (K.homologyπ p ⊗ₘ L.homologyπ q) (M.homologyπ r)]
  simp only [← tensorHom_id, ← id_tensorHom, associator_naturality_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id,
    homologyπ_tensorHom_homologyCross]
  rw [← whiskerRight_comp_tensorHom_assoc, ← whiskerLeft_comp_tensorHom_assoc]
  simp only [homologyπ_tensorHom_homologyCross_assoc, homologyπ_naturality]
  rw [cyclesCross_assoc_assoc K L M p q r pq qr n hpq hqr hn hn']
  simp only [homologyπ_tensorHom_homologyCross]

end Homology

end HomologicalComplex
