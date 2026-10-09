/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Tensor
public import TauCeti.Algebra.Homology.Monoidal.Summand

/-!
# The cross product on the homology of a tensor product of complexes

Let `K` and `L` be homological complexes in a preadditive monoidal category `C`, with a shape
`c` carrying tensor signs, such that the tensor product `K ⊗ L` exists.  A cycle of `K` of
degree `p` and a cycle of `L` of degree `q` have a tensor product which is a cycle of `K ⊗ L` of
degree `n = p + q`: the differential `d (x ⊗ y) = d x ⊗ y ± x ⊗ d y` vanishes on it.  If `x` is a
boundary `x = d x'` then `x ⊗ y = d (x' ⊗ y)`, and symmetrically, up to sign, in `y`.  When
tensoring on either side preserves cokernels (for instance for modules over a commutative ring),
the homology objects are cokernels of the boundaries
(`HomologicalComplex.homologyWhiskerRightIsCokernel`), so the construction descends to the
*cross product*

`Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)`,

the map of the algebraic Künneth theorem.  It is natural in both complexes.  The construction
only needs tensoring with `K.homology p` on the left, and with `L.cycles q` and `L.X (c.prev q)` on
the right, to preserve cokernels.

## Main definitions and results

* `HomologicalComplex.cyclesCross`: the tensor product of cycles, a map
  `K.cycles p ⊗ L.cycles q ⟶ (K ⊗ L).cycles n`.
* `HomologicalComplex.homologyCross`: the cross product
  `K.homology p ⊗ L.homology q ⟶ (K ⊗ L).homology n`, characterized by
  `HomologicalComplex.homologyπ_tensorHom_homologyCross` on classes of cycles.
* `HomologicalComplex.cyclesCross_naturality` and `HomologicalComplex.homologyCross_naturality`:
  naturality in both complexes.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

section Cycles

variable (K L : HomologicalComplex C c) [HasTensor K L] (p q n : I) (h : p + q = n)
  [K.HasHomology p] [L.HasHomology q] [(tensorObj K L).HasHomology n]

/-- A cycle of `K` tensored with any chain of `L` is killed by the first part of the
differential of `K ⊗ L`. -/
private lemma iCycles_whiskerRight_d₁ {i : I} (j : I) :
    (K.iCycles p ▷ L.X i) ≫ mapBifunctor.d₁ K L (curriedTensor C) c p i j = 0 := by
  by_cases hp : c.Rel p (c.next p)
  · simp [mapBifunctor.d₁_eq' _ _ _ _ hp, ← comp_whiskerRight_assoc]
  · simp [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hp]

/-- Any chain of `K` tensored with a cycle of `L` is killed by the second part of the
differential of `K ⊗ L`. -/
private lemma whiskerLeft_iCycles_d₂ {i : I} (j : I) :
    (K.X i ◁ L.iCycles q) ≫ mapBifunctor.d₂ K L (curriedTensor C) c i q j = 0 := by
  by_cases hq : c.Rel q (c.next q)
  · simp [mapBifunctor.d₂_eq' _ _ _ _ _ hq, ← whiskerLeft_comp_assoc]
  · simp [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ hq]

omit [(tensorObj K L).HasHomology n] in
/-- The tensor product of cycles of `K` and `L` is killed by the differential of `K ⊗ L`. -/
private lemma tensorHom_iCycles_ιTensorObj_d (j : I) :
    (K.iCycles p ⊗ₘ L.iCycles q) ≫ ιTensorObj K L p q n h ≫ (tensorObj K L).d n j = 0 := by
  simp [mapBifunctor.d_eq, tensorHom_def', whisker_exchange_assoc, iCycles_whiskerRight_d₁,
    whiskerLeft_iCycles_d₂]

/-- The tensor product of cycles: the map `K.cycles p ⊗ L.cycles q ⟶ (K ⊗ L).cycles n` induced
by the inclusion of the summand `K.X p ⊗ L.X q` of `(K ⊗ L).X n`. -/
def cyclesCross : K.cycles p ⊗ L.cycles q ⟶ (tensorObj K L).cycles n :=
  (tensorObj K L).liftCycles ((K.iCycles p ⊗ₘ L.iCycles q) ≫ ιTensorObj K L p q n h) (c.next n)
    rfl (by rw [Category.assoc, tensorHom_iCycles_ιTensorObj_d])

/-- The tensor product of cycles, viewed as a chain of `K ⊗ L`, is the tensor product of the
underlying chains on the summand `K.X p ⊗ L.X q`. -/
@[reassoc (attr := simp)]
lemma cyclesCross_iCycles :
    cyclesCross K L p q n h ≫ (tensorObj K L).iCycles n =
      (K.iCycles p ⊗ₘ L.iCycles q) ≫ ιTensorObj K L p q n h :=
  liftCycles_i _ _ _ _ _

/-- A boundary of `K` tensored with a cycle of `L` is a boundary of `K ⊗ L`:
`d x ⊗ y = d (x ⊗ y)` when `d y = 0`. -/
private lemma whiskerRight_toCycles_cyclesCross {i : I} (hi : c.Rel i p) :
    (K.toCycles i p ▷ L.cycles q) ≫ cyclesCross K L p q n h =
      (tensorObj K L).liftCycles (((K.X i ◁ L.iCycles q) ≫ ιTensorObj K L i q (i + q) rfl) ≫
        (tensorObj K L).d (i + q) n) (c.next n) rfl (by simp) := by
  rw [← cancel_mono ((tensorObj K L).iCycles n)]
  simp only [Category.assoc, cyclesCross_iCycles, liftCycles_i, mapBifunctor.d_eq,
    Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, whiskerLeft_iCycles_d₂, add_zero]
  rw [mapBifunctor.d₁_eq _ _ _ _ hi _ _ (by simpa using h)]
  simp [tensorHom_def, ← comp_whiskerRight_assoc, whisker_exchange_assoc]

/-- A cycle of `K` tensored with a boundary of `L` is a boundary of `K ⊗ L`:
`x ⊗ d y = ε(p) d (x ⊗ y)` when `d x = 0`, where `x` has degree `p`. -/
private lemma whiskerLeft_toCycles_cyclesCross {i : I} (hi : c.Rel i q) :
    (K.cycles p ◁ L.toCycles i q) ≫ cyclesCross K L p q n h =
      (tensorObj K L).liftCycles ((((c.ε p : ℤ) • (K.iCycles p ▷ L.X i)) ≫
        ιTensorObj K L p i (p + i) rfl) ≫ (tensorObj K L).d (p + i) n) (c.next n) rfl
        (by simp) := by
  rw [← cancel_mono ((tensorObj K L).iCycles n)]
  simp only [Category.assoc, cyclesCross_iCycles, liftCycles_i, mapBifunctor.d_eq,
    Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, Preadditive.zsmul_comp,
    iCycles_whiskerRight_d₁, smul_zero, zero_add]
  rw [mapBifunctor.d₂_eq _ _ _ _ _ hi _ (by simpa using h)]
  simp [tensorHom_def', ← whiskerLeft_comp_assoc, whisker_exchange_assoc, Units.smul_def,
    smul_smul, ← Units.val_mul]

end Cycles

section Homology

variable (K L : HomologicalComplex C c) [HasTensor K L] (p q n : I) (h : p + q = n)
  [K.HasHomology p] [L.HasHomology q] [(tensorObj K L).HasHomology n]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]

/-- The cross product on homology restricted to `K.homology p ⊗ L.cycles q`. -/
private def homologyCrossAux : K.homology p ⊗ L.cycles q ⟶ (tensorObj K L).homology n :=
  Cofork.IsColimit.desc (homologyWhiskerRightIsCokernel K p (L.cycles q))
    (cyclesCross K L p q n h ≫ (tensorObj K L).homologyπ n) (by
      by_cases hi : c.Rel (c.prev p) p
      · rw [zero_comp, ← Category.assoc, whiskerRight_toCycles_cyclesCross K L p q n h hi]
        exact (tensorObj K L).liftCycles_homologyπ_eq_zero_of_boundary (i := n) _ _ _ _ rfl
      · rw [toCycles_eq_zero _ hi, MonoidalPreadditive.zero_whiskerRight, zero_comp])

private lemma homologyπ_whiskerRight_homologyCrossAux :
    (K.homologyπ p ▷ L.cycles q) ≫ homologyCrossAux K L p q n h =
      cyclesCross K L p q n h ≫ (tensorObj K L).homologyπ n :=
  Cofork.IsColimit.π_desc' (homologyWhiskerRightIsCokernel K p (L.cycles q)) _ _

variable [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]

/-- **The homology cross product** `Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` for `p + q = n`: the class of
a cycle `x` tensored with the class of a cycle `y` is the class of the cycle `x ⊗ y`
(`HomologicalComplex.homologyπ_tensorHom_homologyCross`). -/
def homologyCross : K.homology p ⊗ L.homology q ⟶ (tensorObj K L).homology n :=
  Cofork.IsColimit.desc (homologyWhiskerLeftIsCokernel L q (K.homology p))
    (homologyCrossAux K L p q n h) (by
      refine Cofork.IsColimit.hom_ext (homologyWhiskerRightIsCokernel K p _) ?_
      dsimp only [Cofork.π_ofπ]
      rw [zero_comp, comp_zero, ← whisker_exchange_assoc, homologyπ_whiskerRight_homologyCrossAux]
      by_cases hi : c.Rel (c.prev q) q
      · rw [← Category.assoc, whiskerLeft_toCycles_cyclesCross K L p q n h hi]
        exact (tensorObj K L).liftCycles_homologyπ_eq_zero_of_boundary (i := n) _ _ _ _ rfl
      · rw [toCycles_eq_zero _ hi, MonoidalPreadditive.whiskerLeft_zero, zero_comp])

private lemma whiskerLeft_homologyπ_homologyCross :
    (K.homology p ◁ L.homologyπ q) ≫ homologyCross K L p q n h = homologyCrossAux K L p q n h :=
  Cofork.IsColimit.π_desc' (homologyWhiskerLeftIsCokernel L q (K.homology p)) _ _

/-- The cross product of the classes of two cycles is the class of their tensor product. -/
@[reassoc (attr := simp)]
lemma homologyπ_tensorHom_homologyCross :
    (K.homologyπ p ⊗ₘ L.homologyπ q) ≫ homologyCross K L p q n h =
      cyclesCross K L p q n h ≫ (tensorObj K L).homologyπ n := by
  rw [tensorHom_def, Category.assoc, whiskerLeft_homologyπ_homologyCross,
    homologyπ_whiskerRight_homologyCrossAux]

end Homology

section Naturality

variable {K L K' L' : HomologicalComplex C c} [HasTensor K L] [HasTensor K' L']
  (φ : K ⟶ K') (ψ : L ⟶ L') (p q n : I) (h : p + q = n)
  [K.HasHomology p] [L.HasHomology q] [(tensorObj K L).HasHomology n]
  [K'.HasHomology p] [L'.HasHomology q] [(tensorObj K' L').HasHomology n]

/-- The tensor product of cycles is natural in both complexes. -/
@[reassoc]
lemma cyclesCross_naturality :
    (cyclesMap φ p ⊗ₘ cyclesMap ψ q) ≫ cyclesCross K' L' p q n h =
      cyclesCross K L p q n h ≫ cyclesMap (tensorHom φ ψ) n := by
  simp [← cancel_mono ((tensorObj K' L').iCycles n), ← tensorHom_def_assoc, ιTensorObj]

/-- **Naturality of the homology cross product** in both complexes. -/
@[reassoc]
lemma homologyCross_naturality
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K.homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L.X (c.prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (K'.homology p))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair (tensorRight (L'.X (c.prev q)))] :
    (homologyMap φ p ⊗ₘ homologyMap ψ q) ≫ homologyCross K' L' p q n h =
      homologyCross K L p q n h ≫ homologyMap (tensorHom φ ψ) n := by
  refine homology_tensor_homology_hom_ext K L p q ?_
  rw [tensorHom_comp_tensorHom_assoc]
  simp [← tensorHom_comp_tensorHom_assoc, cyclesCross_naturality_assoc]

end Naturality

end HomologicalComplex
