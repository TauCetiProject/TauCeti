/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.Algebra.Lie.KacMoody.Basic

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Module
import TauCeti.Algebra.Lie.Free.Basic
import TauCeti.Algebra.Lie.KacMoody.CartanInjective
import TauCeti.Algebra.Lie.Subalgebra.LieSpan
import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding

/-!
# The auxiliary Kac–Moody presentation and Kac's representation

Let `R` be a realization of an integral matrix `A` over a field `K`. To establish the triangular
directness of `TauCeti.KacMoody.PresentedLieAlgebra R` when `A` is a generalized Cartan matrix
(`Matrix.IsGeneralizedCartan A`), we construct Kac's auxiliary presentation without Serre relations
(`TauCeti.KacMoody.IsAuxRelator`), build Kac's Verma-type representation on the tensor algebra
`K[FreeMonoid I]` to prove triangular directness of the auxiliary algebra using
`FreeAlgebra.equivMonoidAlgebraFreeMonoid` and the PBW embedding of `FreeLieAlgebra K I`, and
verify `ad fₖ`-invariance of the Serre ideal in the auxiliary algebra via
`TauCeti.KacMoody.lie_ad_pow_lie_eq_zero`.

Passing to the quotient yields `TauCeti.KacMoody.quotientTriangular_eq_zero`, from which
`TauCeti/Algebra/Lie/KacMoody/Triangular.lean` deduces the triangular equivalence, generator
independence, and the embedding of `Matrix.ToLieAlgebra K A`.

All results hold over an arbitrary field `K`, with no characteristic or finiteness assumption.

## Main results

* `TauCeti.KacMoody.quotientTriangular_eq_zero`: for a generalized Cartan matrix `A`, a sum
  `negativeQuotientHom R a + cartanElement R x + positiveQuotientHom R b` vanishes only when
  `a = 0`, `x = 0`, and `b = 0`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§1.2–1.3, Theorem 1.2, and §3.3.
-/

public section

open LieAlgebra
open scoped MonoidAlgebra

namespace TauCeti

namespace KacMoody

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-! ## Auxiliary presentation and Kac's representation -/

section Auxiliary

private noncomputable def auxIdeal : LieIdeal K (FreeLieAlgebra K (Generator I H)) :=
  LieSubmodule.lieSpan K _ {x | IsAuxRelator R x}

private def AuxLieAlgebra : Type _ :=
  FreeLieAlgebra K (Generator I H) ⧸ auxIdeal R

private noncomputable instance : LieRing (AuxLieAlgebra R) :=
  inferInstanceAs (LieRing (FreeLieAlgebra K (Generator I H) ⧸ auxIdeal R))

private noncomputable instance : LieAlgebra K (AuxLieAlgebra R) :=
  inferInstanceAs (LieAlgebra K (FreeLieAlgebra K (Generator I H) ⧸ auxIdeal R))

private noncomputable def auxMk :
    FreeLieAlgebra K (Generator I H) →ₗ⁅K⁆ AuxLieAlgebra R :=
  LieIdeal.mkQ (auxIdeal R)

private theorem auxMk_eq_zero_of_isAuxRelator {x : FreeLieAlgebra K (Generator I H)}
    (hx : IsAuxRelator R x) : auxMk R x = 0 :=
  (LieIdeal.mkQ_apply _ x).trans
    (LieSubmodule.Quotient.mk_eq_zero'.mpr (LieSubmodule.subset_lieSpan hx))

private noncomputable def auxCartan : H →ₗ[K] AuxLieAlgebra R where
  toFun x := auxMk R (FreeLieAlgebra.of K (Generator.cartan x))
  map_add' x y := by
    have h := auxMk_eq_zero_of_isAuxRelator R (.cartan_add x y)
    rwa [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  map_smul' c x := by
    have h := auxMk_eq_zero_of_isAuxRelator R (.cartan_smul c x)
    rwa [map_sub, map_smul, sub_eq_zero] at h

private noncomputable def auxPos (i : I) : AuxLieAlgebra R :=
  auxMk R (FreeLieAlgebra.of K (Generator.positive i))

private noncomputable def auxNeg (i : I) : AuxLieAlgebra R :=
  auxMk R (FreeLieAlgebra.of K (Generator.negative i))

@[simp]
private theorem auxMk_of_cartan (x : H) :
    auxMk R (FreeLieAlgebra.of K (Generator.cartan x)) = auxCartan R x := rfl

@[simp]
private theorem auxMk_of_pos (i : I) :
    auxMk R (FreeLieAlgebra.of K (Generator.positive i)) = auxPos R i := rfl

@[simp]
private theorem auxMk_of_neg (i : I) :
    auxMk R (FreeLieAlgebra.of K (Generator.negative i)) = auxNeg R i := rfl

@[simp]
private theorem lie_auxCartan_auxCartan (x y : H) :
    ⁅auxCartan R x, auxCartan R y⁆ = 0 := by
  simpa using auxMk_eq_zero_of_isAuxRelator R (.lie_cartan_cartan x y)

@[simp]
private theorem lie_auxCartan_auxPos (x : H) (j : I) :
    ⁅auxCartan R x, auxPos R j⁆ = R.root j x • auxPos R j := by
  simpa [sub_eq_zero] using auxMk_eq_zero_of_isAuxRelator R (.lie_cartan_positive x j)

@[simp]
private theorem lie_auxPos_auxCartan (j : I) (x : H) :
    ⁅auxPos R j, auxCartan R x⁆ = -(R.root j x • auxPos R j) := by
  rw [← lie_skew, lie_auxCartan_auxPos]

@[simp]
private theorem lie_auxCartan_auxNeg (x : H) (j : I) :
    ⁅auxCartan R x, auxNeg R j⁆ = -(R.root j x • auxNeg R j) := by
  simpa [add_eq_zero_iff_eq_neg] using auxMk_eq_zero_of_isAuxRelator R (.lie_cartan_negative x j)

@[simp]
private theorem lie_auxPos_auxNeg_self (i : I) :
    ⁅auxPos R i, auxNeg R i⁆ = auxCartan R (R.coroot i) := by
  simpa [sub_eq_zero] using auxMk_eq_zero_of_isAuxRelator R (.lie_positive_negative_self i)

@[simp]
private theorem lie_auxNeg_auxPos_self (i : I) :
    ⁅auxNeg R i, auxPos R i⁆ = -auxCartan R (R.coroot i) := by
  rw [← lie_skew, lie_auxPos_auxNeg_self]

@[simp]
private theorem lie_auxPos_auxNeg_of_ne {i j : I} (hij : i ≠ j) :
    ⁅auxPos R i, auxNeg R j⁆ = 0 := by
  simpa using auxMk_eq_zero_of_isAuxRelator R (.lie_positive_negative_of_ne i j hij)

@[simp]
private theorem lie_auxNeg_auxPos_of_ne {i j : I} (hij : i ≠ j) :
    ⁅auxNeg R i, auxPos R j⁆ = 0 := by
  rw [← lie_skew, lie_auxPos_auxNeg_of_ne R hij.symm, neg_zero]

private theorem satisfiesAuxRelations_aux :
    SatisfiesAuxRelations R (auxCartan R) (auxPos R) (auxNeg R) where
  lie_cartan_cartan := lie_auxCartan_auxCartan R
  lie_cartan_positive := lie_auxCartan_auxPos R
  lie_cartan_negative := lie_auxCartan_auxNeg R
  lie_positive_negative_self := lie_auxPos_auxNeg_self R
  lie_positive_negative_of_ne _ _ := lie_auxPos_auxNeg_of_ne R

section AuxUniversal

variable {R} {L : Type*} [LieRing L] [LieAlgebra K L]

private noncomputable def auxLift {φ : H →ₗ[K] L} {E F : I → L}
    (h : SatisfiesAuxRelations R φ E F) : AuxLieAlgebra R →ₗ⁅K⁆ L :=
  (auxIdeal R).liftQ (FreeLieAlgebra.lift K (generatorMap φ E F)) (lieSpan_isAuxRelator_le_ker h)

@[simp]
private theorem auxLift_auxCartan {φ : H →ₗ[K] L} {E F : I → L}
    (h : SatisfiesAuxRelations R φ E F) (x : H) : auxLift h (auxCartan R x) = φ x :=
  ((LieIdeal.liftQ_apply _ _ _ _).trans (FreeLieAlgebra.lift_of_apply _ _)).trans
    (generatorMap_cartan x)

@[simp]
private theorem auxLift_auxPos {φ : H →ₗ[K] L} {E F : I → L}
    (h : SatisfiesAuxRelations R φ E F) (i : I) : auxLift h (auxPos R i) = E i :=
  ((LieIdeal.liftQ_apply _ _ _ _).trans (FreeLieAlgebra.lift_of_apply _ _)).trans
    (generatorMap_positive i)

@[simp]
private theorem auxLift_auxNeg {φ : H →ₗ[K] L} {E F : I → L}
    (h : SatisfiesAuxRelations R φ E F) (i : I) : auxLift h (auxNeg R i) = F i :=
  ((LieIdeal.liftQ_apply _ _ _ _).trans (FreeLieAlgebra.lift_of_apply _ _)).trans
    (generatorMap_negative i)

private theorem aux_hom_ext {g₁ g₂ : AuxLieAlgebra R →ₗ⁅K⁆ L}
    (hH : ∀ x, g₁ (auxCartan R x) = g₂ (auxCartan R x))
    (hE : ∀ i, g₁ (auxPos R i) = g₂ (auxPos R i))
    (hF : ∀ i, g₁ (auxNeg R i) = g₂ (auxNeg R i)) : g₁ = g₂ := by
  refine (auxIdeal R).lieHom_qext fun x => ?_
  have hc : g₁.comp (auxMk R) = g₂.comp (auxMk R) := FreeLieAlgebra.hom_ext fun
    | .cartan x => hH x
    | .positive i => hE i
    | .negative i => hF i
  exact DFunLike.congr_fun hc x

end AuxUniversal

private theorem lieSpan_auxGenerators_eq_top :
    LieSubalgebra.lieSpan K (AuxLieAlgebra R)
      (Set.range (auxCartan R) ∪ Set.range (auxPos R) ∪ Set.range (auxNeg R)) = ⊤ := by
  set S := LieSubalgebra.lieSpan K (AuxLieAlgebra R)
    (Set.range (auxCartan R) ∪ Set.range (auxPos R) ∪ Set.range (auxNeg R))
  have hle : LieSubalgebra.lieSpan K (FreeLieAlgebra K (Generator I H))
      (Set.range (FreeLieAlgebra.of K)) ≤ S.comap (auxMk R) := by
    refine LieSubalgebra.lieSpan_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    refine LieSubalgebra.subset_lieSpan ?_
    cases g with
    | cartan x => exact Or.inl (Or.inl ⟨x, rfl⟩)
    | positive i => exact Or.inl (Or.inr ⟨i, rfl⟩)
    | negative i => exact Or.inr ⟨i, rfl⟩
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨x, rfl⟩ := (auxIdeal R).surjective_mkQ y
  exact hle (by rw [FreeLieAlgebra.lieSpan_range_of_eq_top]; trivial)

private noncomputable def auxChevalleyHom : AuxLieAlgebra R →ₗ⁅K⁆ AuxLieAlgebra R :=
  auxLift (satisfiesAuxRelations_aux R).neg_swap

private noncomputable def auxChevalley : AuxLieAlgebra R ≃ₗ⁅K⁆ AuxLieAlgebra R :=
  have hcomp : (auxChevalleyHom R).comp (auxChevalleyHom R) = LieHom.id :=
    aux_hom_ext (by simp [auxChevalleyHom]) (by simp [auxChevalleyHom]) (by simp [auxChevalleyHom])
  { toLieHom := auxChevalleyHom R
    invFun := auxChevalleyHom R
    left_inv := fun x => DFunLike.congr_fun hcomp x
    right_inv := fun x => DFunLike.congr_fun hcomp x }

private noncomputable def auxPosHom : FreeLieAlgebra K I →ₗ⁅K⁆ AuxLieAlgebra R :=
  FreeLieAlgebra.lift K (auxPos R)

private noncomputable def auxNegHom : FreeLieAlgebra K I →ₗ⁅K⁆ AuxLieAlgebra R :=
  FreeLieAlgebra.lift K (auxNeg R)

private theorem auxChevalley_auxPosHom (b : FreeLieAlgebra K I) :
    auxChevalley R (auxPosHom R b) = auxNegHom R (TauCeti.FreeLieAlgebra.freeNeg K I b) :=
  DFunLike.congr_fun (FreeLieAlgebra.hom_ext fun i => by
    simp [auxChevalley, auxChevalleyHom, auxPosHom, auxNegHom] :
    (auxChevalley R).toLieHom.comp (auxPosHom R) =
      (auxNegHom R).comp (TauCeti.FreeLieAlgebra.freeNeg K I).toLieHom) b

private theorem auxChevalley_auxNegHom (b : FreeLieAlgebra K I) :
    auxChevalley R (auxNegHom R b) = auxPosHom R (TauCeti.FreeLieAlgebra.freeNeg K I b) :=
  DFunLike.congr_fun (FreeLieAlgebra.hom_ext fun i => by
    simp [auxChevalley, auxChevalleyHom, auxPosHom, auxNegHom] :
    (auxChevalley R).toLieHom.comp (auxNegHom R) =
      (auxPosHom R).comp (TauCeti.FreeLieAlgebra.freeNeg K I).toLieHom) b

private noncomputable def auxToPresented : AuxLieAlgebra R →ₗ⁅K⁆ PresentedLieAlgebra R :=
  auxLift (satisfiesRelations_generators R).toSatisfiesAuxRelations

/-! ### Kac's Verma-type representation on formal words -/

section AuxRep

open MonoidAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

private def wordWeight (lam : Module.Dual K H) (w : FreeMonoid I) : Module.Dual K H :=
  lam - (w.toList.map R.root).sum

@[simp]
private theorem wordWeight_one (lam : Module.Dual K H) :
    wordWeight R lam (1 : FreeMonoid I) = lam := by
  simp [wordWeight]

@[simp]
private theorem wordWeight_of_mul (lam : Module.Dual K H) (j : I) (w : FreeMonoid I) :
    wordWeight R lam (.of j * w) = wordWeight R lam w - R.root j := by
  simp only [wordWeight, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
    List.map_cons, List.sum_cons]
  abel

private noncomputable def fOp (i : I) : Module.End K K[FreeMonoid I] :=
  LinearMap.mulLeft K (MonoidAlgebra.of K (FreeMonoid I) (FreeMonoid.of i))

@[simp]
private theorem fOp_single (i : I) (w : FreeMonoid I) (c : K) :
    fOp (K := K) i (single w c) = single (.of i * w) c := by
  simp [fOp, LinearMap.mulLeft_apply, MonoidAlgebra.of_apply]

private noncomputable def hOp (lam : Module.Dual K H) : H →ₗ[K] Module.End K K[FreeMonoid I] :=
  ((MonoidAlgebra.basis (FreeMonoid I) K).constr K).toLinearMap ∘ₗ
    LinearMap.pi fun w => (wordWeight R lam w).smulRight (single w (1 : K))

@[simp]
private theorem hOp_single (lam : Module.Dual K H) (x : H) (w : FreeMonoid I) (c : K) :
    hOp R lam x (single w c) = c • wordWeight R lam w x • single w 1 := by
  have hc : single w c = c • MonoidAlgebra.basis (FreeMonoid I) K w := by
    rw [basis_apply, smul_single', mul_one]
  rw [hc, map_smul, hOp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.constr_basis, LinearMap.pi_apply, LinearMap.smulRight_apply]

open scoped Classical in
private noncomputable def eWord (lam : Module.Dual K H) (i : I) (w : FreeMonoid I) :
    K[FreeMonoid I] :=
  w.mulRecOn 0 fun j w r => fOp (K := K) j r +
    if i = j then wordWeight R lam w (R.coroot i) • single w 1 else 0

@[simp]
private theorem eWord_one (lam : Module.Dual K H) (i : I) :
    eWord R lam i 1 = 0 := by
  simp [eWord]

open scoped Classical in
@[simp]
private theorem eWord_of_mul (lam : Module.Dual K H) (i j : I) (w : FreeMonoid I) :
    eWord R lam i (.of j * w) = fOp (K := K) j (eWord R lam i w) +
      if i = j then wordWeight R lam w (R.coroot i) • single w 1 else 0 := by
  simp [eWord]

open scoped Classical in
private noncomputable def eOp (lam : Module.Dual K H) (i : I) : Module.End K K[FreeMonoid I] :=
  (MonoidAlgebra.basis (FreeMonoid I) K).constr K (eWord R lam i)

open scoped Classical in
@[simp]
private theorem eOp_single (lam : Module.Dual K H) (i : I) (w : FreeMonoid I) (c : K) :
    eOp R lam i (single w c) = c • eWord R lam i w := by
  have hc : single w c = c • MonoidAlgebra.basis (FreeMonoid I) K w := by
    rw [basis_apply, smul_single', mul_one]
  rw [hc, map_smul, eOp, Module.Basis.constr_basis]

private theorem hOp_fOp (lam : Module.Dual K H) (x : H) (j : I) (v : K[FreeMonoid I]) :
    hOp R lam x (fOp j v) = fOp j (hOp R lam x v) - R.root j x • fOp j v := by
  have heq : (hOp R lam x).comp (fOp j) = (fOp j).comp (hOp R lam x) - R.root j x • fOp j := by
    refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
    simp only [basis_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      fOp_single, hOp_single, one_smul, map_smul, wordWeight_of_mul]
    rw [sub_smul]
  simpa using LinearMap.congr_fun heq v

open scoped Classical in
private theorem hOp_eWord (lam : Module.Dual K H) (x : H) (i : I) (w : FreeMonoid I) :
    hOp R lam x (eWord R lam i w) = (wordWeight R lam w x + R.root i x) • eWord R lam i w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [eWord_one]
  | of_mul j w ih =>
    have hf : hOp R lam x (fOp j (eWord R lam i w)) =
        (wordWeight R lam (.of j * w) x + R.root i x) • fOp j (eWord R lam i w) := by
      rw [hOp_fOp, ih, map_smul, wordWeight_of_mul, LinearMap.sub_apply]
      module
    simp only [eWord_of_mul, map_add, hf]
    split_ifs with hij
    · subst hij
      simp only [map_smul, hOp_single, one_smul, wordWeight_of_mul, LinearMap.sub_apply]
      module
    · simp

open scoped Classical in
private theorem satisfiesAuxRelations_auxRep (lam : Module.Dual K H) :
    SatisfiesAuxRelations R (hOp R lam) (eOp R lam) (fOp (K := K)) where
  lie_cartan_cartan x y := by
    refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
    rw [LieRing.of_associative_ring_bracket]
    simp [mul_apply_eq_comp, mul_comm]
  lie_cartan_positive x j := by
    refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
    rw [LieRing.of_associative_ring_bracket]
    simp only [basis_apply, LinearMap.sub_apply, mul_apply_eq_comp, eOp_single, hOp_single,
      one_smul, map_smul, hOp_eWord, LinearMap.smul_apply]
    module
  lie_cartan_negative x j := by
    refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
    rw [LieRing.of_associative_ring_bracket]
    simp only [basis_apply, LinearMap.sub_apply, mul_apply_eq_comp, fOp_single, hOp_single,
      one_smul, map_smul, wordWeight_of_mul, LinearMap.neg_apply, LinearMap.smul_apply]
    module
  lie_positive_negative_self i := by
    refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
    rw [LieRing.of_associative_ring_bracket]
    simp [mul_apply_eq_comp]
  lie_positive_negative_of_ne i j hij := by
    refine (MonoidAlgebra.basis (FreeMonoid I) K).ext fun w => ?_
    rw [LieRing.of_associative_ring_bracket]
    simp [mul_apply_eq_comp, hij]

open scoped Classical in
private noncomputable def auxRep (lam : Module.Dual K H) :
    AuxLieAlgebra R →ₗ⁅K⁆ Module.End K K[FreeMonoid I] :=
  auxLift (satisfiesAuxRelations_auxRep R lam)

open scoped Classical in
private theorem auxRep_auxPosHom_one (lam : Module.Dual K H) (b : FreeLieAlgebra K I) :
    auxRep R lam (auxPosHom R b) (1 : K[FreeMonoid I]) = 0 := by
  have hb : b ∈ LieSubalgebra.lieSpan K _ (Set.range (FreeLieAlgebra.of K)) := by
    rw [FreeLieAlgebra.lieSpan_range_of_eq_top]; trivial
  induction hb using LieSubalgebra.lieSpan_induction with
  | mem _ hx => rcases hx with ⟨i, rfl⟩; simp [auxRep, auxPosHom, MonoidAlgebra.one_def]
  | zero => simp
  | add _ _ _ _ hx hy => simp [map_add, hx, hy]
  | smul c _ _ hx => simp [map_smul, hx]
  | lie _ _ _ _ hx hy =>
    rw [LieHom.map_lie, LieHom.map_lie, LieRing.of_associative_ring_bracket]
    simp [mul_apply_eq_comp, hx, hy]

open scoped Classical in
private theorem auxRep_auxNegHom_apply_one (lam : Module.Dual K H) (a : FreeLieAlgebra K I) :
    (auxRep R lam (auxNegHom R a) (1 : K[FreeMonoid I])).coeff 1 = 0 := by
  suffices ∀ v : K[FreeMonoid I], (auxRep R lam (auxNegHom R a) v).coeff 1 = 0 from this _
  have ha : a ∈ LieSubalgebra.lieSpan K _ (Set.range (FreeLieAlgebra.of K)) := by
    rw [FreeLieAlgebra.lieSpan_range_of_eq_top]; trivial
  induction ha using LieSubalgebra.lieSpan_induction with
  | mem _ hx =>
    rcases hx with ⟨i, rfl⟩
    intro v
    simp only [auxNegHom, FreeLieAlgebra.lift_of_apply, auxRep, auxLift_auxNeg]
    induction v using MonoidAlgebra.induction_on with
    | of w =>
      rw [MonoidAlgebra.of_apply, fOp_single]
      have hne : FreeMonoid.of i * w ≠ 1 := fun h => by
        simpa using congrArg FreeMonoid.toList h
      simp [hne]
    | add _ _ hu hw => simp [map_add, hu, hw]
    | smul _ _ hu => simp [map_smul, hu]
  | zero => intro v; simp
  | add _ _ _ _ hx hy => intro v; simp [map_add, hx v, hy v]
  | smul c _ _ hx => intro v; simp [map_smul, hx v]
  | lie _ _ _ _ hx hy =>
    intro v
    rw [LieHom.map_lie, LieHom.map_lie, LieRing.of_associative_ring_bracket]
    simp [mul_apply_eq_comp, hx, hy]

open scoped Classical in
private theorem auxRep_auxNegHom_injective (lam : Module.Dual K H) :
    Function.Injective fun a : FreeLieAlgebra K I =>
      auxRep R lam (auxNegHom R a) (1 : K[FreeMonoid I]) := by
  let ιFA : FreeLieAlgebra K I →ₗ⁅K⁆ FreeAlgebra K I := FreeLieAlgebra.lift K (FreeAlgebra.ι K)
  have hιFA_eq : ∀ a, ιFA a = FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra K I
      (UniversalEnvelopingAlgebra.ι K a) := fun a => by
    simp [ιFA, FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra]
  have hιFA_inj : Function.Injective ιFA := fun a b hab =>
    TauCeti.UniversalEnvelopingAlgebra.ι_injective K (FreeLieAlgebra K I) <|
      (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra K I).injective <| by
        rwa [← hιFA_eq, ← hιFA_eq]
  have hAlg : FreeAlgebra.lift K (fOp (K := K)) =
      (Algebra.lmul K K[FreeMonoid I]).comp FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom := by
    refine FreeAlgebra.hom_ext (funext fun i => ?_)
    simp [fOp, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
    rfl
  have hcomp : (auxRep R lam).comp (auxNegHom R) =
      (FreeAlgebra.lift K (fOp (K := K))).toLieHom.comp ιFA :=
    FreeLieAlgebra.hom_ext fun i => by simp [auxRep, auxNegHom, ιFA]
  intro a b hab
  have ha := LinearMap.congr_fun (DFunLike.congr_fun hcomp a) (1 : K[FreeMonoid I])
  have hb := LinearMap.congr_fun (DFunLike.congr_fun hcomp b) (1 : K[FreeMonoid I])
  have h2 := ha.symm.trans (hab.trans hb)
  simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, hAlg, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one] at h2
  exact hιFA_inj (FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective h2)

private theorem auxTriangular_eq_zero {a b : FreeLieAlgebra K I} {x : H}
    (h : auxNegHom R a + auxCartan R x + auxPosHom R b = 0) :
    a = 0 ∧ x = 0 ∧ b = 0 := by
  classical
  have hx : x = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff K x).mp fun lam => ?_
    have h0 := congrArg (fun z => (auxRep R lam z (1 : K[FreeMonoid I])).coeff 1) h
    simp only [map_add, LinearMap.add_apply, coeff_add, Finsupp.add_apply, map_zero,
      LinearMap.zero_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
      auxRep_auxNegHom_apply_one, auxRep_auxPosHom_one, add_zero, zero_add] at h0
    have hcart : auxRep R lam (auxCartan R x) (1 : K[FreeMonoid I]) =
        lam x • (1 : K[FreeMonoid I]) := by
      simp [auxRep, MonoidAlgebra.one_def]
    rw [hcart] at h0
    simpa [MonoidAlgebra.one_def] using h0
  subst hx
  simp only [map_zero, add_zero] at h
  have ha : a = 0 := auxRep_auxNegHom_injective R 0 <| by
    simpa [map_add, auxRep_auxPosHom_one] using
      congrArg (fun z => auxRep R 0 z (1 : K[FreeMonoid I])) h
  subst ha
  simp only [map_zero, zero_add] at h
  have hb : b = 0 := by
    apply (TauCeti.FreeLieAlgebra.freeNeg K I).injective
    rw [map_zero]
    apply auxRep_auxNegHom_injective R 0
    have hchev := congrArg (auxChevalley R) h
    rw [map_zero, auxChevalley_auxPosHom] at hchev
    simp [hchev]
  exact ⟨rfl, rfl, hb⟩

end AuxRep

/-! ### Invariance of the Serre ideal in the auxiliary algebra -/

section AuxSerre

private theorem lie_auxCartan_mem_range_auxPosHom (x : H) {y : AuxLieAlgebra R}
    (hy : y ∈ (auxPosHom R).range) : ⁅auxCartan R x, y⁆ ∈ (auxPosHom R).range := by
  rw [auxPosHom, TauCeti.FreeLieAlgebra.range_lift_eq_lieSpan] at hy ⊢
  refine LieSubalgebra.lie_mem_of_mem_lieSpan ?_ hy
  rintro _ ⟨j, rfl⟩
  rw [lie_auxCartan_auxPos]
  exact LieSubalgebra.smul_mem _ _ (LieSubalgebra.subset_lieSpan (Set.mem_range_self j))

private theorem lie_auxNeg_mem_range_auxPosHom_sup_range_auxCartan (k : I) {y : AuxLieAlgebra R}
    (hy : y ∈ (auxPosHom R).range) :
    ⁅auxNeg R k, y⁆ ∈ (auxPosHom R).range.toSubmodule ⊔ LinearMap.range (auxCartan R) := by
  have hrange : (auxPosHom R).range = LieSubalgebra.lieSpan K _ (Set.range (auxPos R)) :=
    TauCeti.FreeLieAlgebra.range_lift_eq_lieSpan (auxPos R)
  rw [hrange] at hy ⊢
  refine LieSubalgebra.lie_mem_sup_of_mem_lieSpan ?_ ?_ hy
  · rintro _ ⟨x, rfl⟩ z hz
    rw [← hrange] at hz ⊢
    exact lie_auxCartan_mem_range_auxPosHom R x hz
  · rintro _ ⟨j, rfl⟩
    rcases eq_or_ne k j with rfl | hkj
    · rw [lie_auxNeg_auxPos_self]
      exact Submodule.mem_sup_right ⟨-R.coroot k, map_neg _ _⟩
    · rw [lie_auxNeg_auxPos_of_ne R hkj]
      exact zero_mem _

private theorem lie_auxNeg_serreRelator_eq_zero (hA : A.IsGeneralizedCartan) (k i j : I) :
    ⁅auxNeg R k, (ad K _ (auxPos R i) ^ (-A i j).toNat) ⁅auxPos R i, auxPos R j⁆⁆ = 0 :=
  lie_ad_pow_lie_eq_zero hA.diag hA.offDiag_nonpos (fun a b hab => (hA.zero_comm a b).mp hab)
    (lie_auxCartan_auxPos R) (lie_auxCartan_auxNeg R) (lie_auxPos_auxNeg_self R)
    (fun _ _ => lie_auxPos_auxNeg_of_ne R) i j k

private noncomputable def auxSerrePosSubmodule : Submodule K (AuxLieAlgebra R) :=
  (serreIdeal K A).toSubmodule.map (auxPosHom R).toLinearMap

private theorem auxPosHom_serreRelator (i j : I) :
    auxPosHom R ((ad K _ (FreeLieAlgebra.of K i) ^ (-A i j).toNat)
      ⁅FreeLieAlgebra.of K i, FreeLieAlgebra.of K j⁆) =
      (ad K _ (auxPos R i) ^ (-A i j).toNat) ⁅auxPos R i, auxPos R j⁆ := by
  simp [auxPosHom]

private theorem lie_range_auxPosHom_auxSerrePosSubmodule {u y : AuxLieAlgebra R}
    (hu : u ∈ (auxPosHom R).range) (hy : y ∈ auxSerrePosSubmodule R) :
    ⁅u, y⁆ ∈ auxSerrePosSubmodule R := by
  rcases hu with ⟨a, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  exact ⟨⁅a, b⁆, LieSubmodule.lie_mem (serreIdeal K A) hb, (auxPosHom R).map_lie a b⟩

private theorem lie_auxCartan_auxSerrePosSubmodule (x : H) {y : AuxLieAlgebra R}
    (hy : y ∈ auxSerrePosSubmodule R) : ⁅auxCartan R x, y⁆ ∈ auxSerrePosSubmodule R := by
  rcases hy with ⟨b, hb, rfl⟩
  simp only [LieHom.coe_toLinearMap]
  induction hb using serreIdeal_induction with
  | relator i j =>
    rw [auxPosHom_serreRelator, ← ad_pow_succ_apply,
      lie_ad_pow_of_lie_eq_smul (lie_auxCartan_auxPos R x i) (lie_auxCartan_auxPos R x j)]
    refine Submodule.smul_mem _ _ ⟨_, relator_mem_serreIdeal K A i j, ?_⟩
    simp only [LieHom.coe_toLinearMap, auxPosHom_serreRelator, ad_pow_succ_apply]
  | zero => simp
  | add _ _ _ _ hu hv => simpa [map_add, lie_add] using add_mem hu hv
  | smul c _ _ hu => simpa [map_smul, lie_smul] using Submodule.smul_mem _ c hu
  | lie u v hv ih =>
    rw [LieHom.map_lie, leibniz_lie]
    exact add_mem
      (lie_range_auxPosHom_auxSerrePosSubmodule R
        (lie_auxCartan_mem_range_auxPosHom R x ⟨u, rfl⟩) ⟨v, hv, rfl⟩)
      (lie_range_auxPosHom_auxSerrePosSubmodule R ⟨u, rfl⟩ ih)

private theorem lie_auxNeg_auxSerrePosSubmodule (hA : A.IsGeneralizedCartan) (k : I)
    {y : AuxLieAlgebra R} (hy : y ∈ auxSerrePosSubmodule R) :
    ⁅auxNeg R k, y⁆ ∈ auxSerrePosSubmodule R := by
  rcases hy with ⟨b, hb, rfl⟩
  simp only [LieHom.coe_toLinearMap]
  induction hb using serreIdeal_induction with
  | relator i j =>
    rw [auxPosHom_serreRelator, lie_auxNeg_serreRelator_eq_zero R hA]
    exact zero_mem _
  | zero => simp
  | add _ _ _ _ hu hv => simpa [map_add, lie_add] using add_mem hu hv
  | smul c _ _ hu => simpa [map_smul, lie_smul] using Submodule.smul_mem _ c hu
  | lie u v hv ih =>
    rw [LieHom.map_lie, leibniz_lie]
    refine add_mem ?_ (lie_range_auxPosHom_auxSerrePosSubmodule R ⟨u, rfl⟩ ih)
    obtain ⟨p, hp, _, ⟨x, rfl⟩, hsum⟩ := Submodule.mem_sup.mp
      (lie_auxNeg_mem_range_auxPosHom_sup_range_auxCartan R k ⟨u, rfl⟩)
    simp only [LieHom.coe_toLinearMap] at hsum
    rw [← hsum, add_lie]
    exact add_mem (lie_range_auxPosHom_auxSerrePosSubmodule R hp ⟨v, hv, rfl⟩)
      (lie_auxCartan_auxSerrePosSubmodule R x ⟨v, hv, rfl⟩)

private noncomputable def auxSerrePosIdeal (hA : A.IsGeneralizedCartan) :
    LieIdeal K (AuxLieAlgebra R) :=
  { auxSerrePosSubmodule R with
    lie_mem := fun {z y} hy => by
      suffices ∀ v ∈ auxSerrePosSubmodule R, ⁅z, v⁆ ∈ auxSerrePosSubmodule R from this y hy
      have hz : z ∈ LieSubalgebra.lieSpan K (AuxLieAlgebra R)
          (Set.range (auxCartan R) ∪ Set.range (auxPos R) ∪ Set.range (auxNeg R)) := by
        rw [lieSpan_auxGenerators_eq_top R]; trivial
      induction hz using LieSubalgebra.lieSpan_induction with
      | mem _ hg =>
        rintro v hv
        rcases hg with (⟨x, rfl⟩ | ⟨i, rfl⟩) | ⟨k, rfl⟩
        · exact lie_auxCartan_auxSerrePosSubmodule R x hv
        · exact lie_range_auxPosHom_auxSerrePosSubmodule R
            ⟨FreeLieAlgebra.of K i, FreeLieAlgebra.lift_of_apply _ i⟩ hv
        · exact lie_auxNeg_auxSerrePosSubmodule R hA k hv
      | zero => intro _ _; simp
      | add _ _ _ _ h₁ h₂ => intro v hv; rw [add_lie]; exact add_mem (h₁ v hv) (h₂ v hv)
      | smul c _ _ hw => intro v hv; rw [smul_lie]; exact Submodule.smul_mem _ c (hw v hv)
      | lie _ _ _ _ h₁ h₂ =>
        intro v hv; rw [lie_lie]; exact sub_mem (h₁ _ (h₂ v hv)) (h₂ _ (h₁ v hv)) }

private theorem freeNeg_mem_serreIdeal {b : FreeLieAlgebra K I} (hb : b ∈ serreIdeal K A) :
    TauCeti.FreeLieAlgebra.freeNeg K I b ∈ serreIdeal K A := by
  induction hb using serreIdeal_induction with
  | relator i j =>
    rw [← LieEquiv.coe_toLieHom, LieHom.map_ad_pow, LieHom.map_lie, LieEquiv.coe_toLieHom,
      TauCeti.FreeLieAlgebra.freeNeg_of, TauCeti.FreeLieAlgebra.freeNeg_of, neg_lie, lie_neg,
      neg_neg, ad_neg_pow_apply]
    exact Submodule.smul_mem (serreIdeal K A).toSubmodule _ (relator_mem_serreIdeal K A i j)
  | zero => simp
  | add _ _ _ _ hu hv => simpa [map_add] using add_mem hu hv
  | smul c _ _ hu => simpa [map_smul] using Submodule.smul_mem _ c hu
  | lie _ _ _ ih => simpa [LieEquiv.map_lie] using LieSubmodule.lie_mem (serreIdeal K A) ih

private noncomputable def auxSerreNegIdeal (hA : A.IsGeneralizedCartan) :
    LieIdeal K (AuxLieAlgebra R) :=
  { (serreIdeal K A).toSubmodule.map (auxNegHom R).toLinearMap with
    lie_mem := fun {z y} hy => by
      rcases hy with ⟨b, hb, rfl⟩
      have hb' : auxChevalley R (auxNegHom R b) ∈ auxSerrePosIdeal R hA :=
        ⟨TauCeti.FreeLieAlgebra.freeNeg K I b, freeNeg_mem_serreIdeal hb,
          (auxChevalley_auxNegHom R b).symm⟩
      have hlie : ⁅auxChevalley R z, auxChevalley R (auxNegHom R b)⁆ ∈ auxSerrePosIdeal R hA :=
        LieSubmodule.lie_mem (auxSerrePosIdeal R hA) hb'
      rcases hlie with ⟨a, ha, haEq⟩
      refine ⟨TauCeti.FreeLieAlgebra.freeNeg K I a, freeNeg_mem_serreIdeal ha, ?_⟩
      simp only [LieHom.coe_toLinearMap] at haEq ⊢
      rw [← auxChevalley_auxPosHom, haEq, ← LieEquiv.map_lie]
      exact (auxChevalley R).left_inv _ }

private theorem satisfiesRelations_auxQuotient (hA : A.IsGeneralizedCartan) :
    let J := auxSerreNegIdeal R hA ⊔ auxSerrePosIdeal R hA
    SatisfiesRelations R (J.mkQ.toLinearMap ∘ₗ auxCartan R) (J.mkQ ∘ auxPos R)
      (J.mkQ ∘ auxNeg R) := by
  intro J
  refine { (satisfiesAuxRelations_aux R).map J.mkQ with
    serre_positive := fun i j => ?_
    serre_negative := fun i j => ?_ }
  · simp only [Function.comp_apply, ← LieHom.map_lie, ← LieHom.map_ad_pow, ← LieHom.mem_ker,
      LieIdeal.mkQ_ker]
    exact LieSubmodule.mem_sup_right
      ⟨_, relator_mem_serreIdeal K A i j, auxPosHom_serreRelator R i j⟩
  · simp only [Function.comp_apply, ← LieHom.map_lie, ← LieHom.map_ad_pow, ← LieHom.mem_ker,
      LieIdeal.mkQ_ker]
    refine LieSubmodule.mem_sup_left ⟨_, relator_mem_serreIdeal K A i j, ?_⟩
    simp [auxNegHom]

private theorem auxToPresented_comp_auxPosHom :
    (auxToPresented R).comp (auxPosHom R) = FreeLieAlgebra.lift K (positiveGenerator R) :=
  FreeLieAlgebra.hom_ext fun i => by simp [auxToPresented, auxPosHom]

private theorem auxToPresented_comp_auxNegHom :
    (auxToPresented R).comp (auxNegHom R) = FreeLieAlgebra.lift K (negativeGenerator R) :=
  FreeLieAlgebra.hom_ext fun i => by simp [auxToPresented, auxNegHom]

private theorem ker_auxToPresented_eq (hA : A.IsGeneralizedCartan) :
    (auxToPresented R).ker = auxSerreNegIdeal R hA ⊔ auxSerrePosIdeal R hA := by
  refine le_antisymm ?_ ?_
  · set J := auxSerreNegIdeal R hA ⊔ auxSerrePosIdeal R hA
    have hcomp : (lift (satisfiesRelations_auxQuotient R hA)).comp (auxToPresented R) = J.mkQ :=
      aux_hom_ext (fun _ => by simp [auxToPresented])
        (fun _ => by simp [auxToPresented]) (fun _ => by simp [auxToPresented])
    intro z hz
    rw [LieHom.mem_ker] at hz
    have hz' : J.mkQ z = 0 := by rw [← hcomp, LieHom.comp_apply, hz, map_zero]
    rwa [← LieHom.mem_ker, LieIdeal.mkQ_ker] at hz'
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      have hker := serreIdeal_le_ker_lift (ad_pow_lie_negativeGenerator_negativeGenerator R) ha
      rwa [LieHom.mem_ker, ← auxToPresented_comp_auxNegHom] at hker
    · rintro _ ⟨b, hb, rfl⟩
      have hker := serreIdeal_le_ker_lift (ad_pow_lie_positiveGenerator_positiveGenerator R) hb
      rwa [LieHom.mem_ker, ← auxToPresented_comp_auxPosHom] at hker

/-- **Directness of the triangular sum.** For a generalized Cartan matrix `A`, a sum
`negativeQuotientHom R a + cartanElement R x + positiveQuotientHom R b` vanishes in
`PresentedLieAlgebra R` only when `a = 0`, `x = 0`, and `b = 0`. -/
theorem quotientTriangular_eq_zero (hA : A.IsGeneralizedCartan)
    {a b : FreeLieAlgebra K I ⧸ serreIdeal K A} {x : H}
    (h : negativeQuotientHom R a + cartanElement R x + positiveQuotientHom R b = 0) :
    a = 0 ∧ x = 0 ∧ b = 0 := by
  obtain ⟨a₀, rfl⟩ := (serreIdeal K A).surjective_mkQ a
  obtain ⟨b₀, rfl⟩ := (serreIdeal K A).surjective_mkQ b
  have hneg : negativeQuotientHom R ((serreIdeal K A).mkQ a₀) =
      auxToPresented R (auxNegHom R a₀) := by
    rw [← LieHom.comp_apply, negativeQuotientHom_comp_mkQ, ← auxToPresented_comp_auxNegHom,
      LieHom.comp_apply]
  have hpos : positiveQuotientHom R ((serreIdeal K A).mkQ b₀) =
      auxToPresented R (auxPosHom R b₀) := by
    rw [← LieHom.comp_apply, positiveQuotientHom_comp_mkQ, ← auxToPresented_comp_auxPosHom,
      LieHom.comp_apply]
  have hcart : cartanElement R x = auxToPresented R (auxCartan R x) := (auxLift_auxCartan _ x).symm
  rw [hneg, hcart, hpos, ← map_add, ← map_add, ← LieHom.mem_ker, ker_auxToPresented_eq R hA] at h
  obtain ⟨_, ⟨a', ha', rfl⟩, _, ⟨b', hb', rfl⟩, heq⟩ := (LieSubmodule.mem_sup _ _ _).mp h
  simp only [LieHom.coe_toLinearMap] at heq
  have hsub : auxNegHom R (a₀ - a') + auxCartan R x + auxPosHom R (b₀ - b') = 0 := by
    calc auxNegHom R (a₀ - a') + auxCartan R x + auxPosHom R (b₀ - b')
      _ = (auxNegHom R a₀ + auxCartan R x + auxPosHom R b₀) -
            (auxNegHom R a' + auxPosHom R b') := by simp only [map_sub]; abel
      _ = 0 := sub_eq_zero.mpr heq.symm
  obtain ⟨ha₀, rfl, hb₀⟩ := auxTriangular_eq_zero R hsub
  refine ⟨?_, rfl, ?_⟩
  · rw [← LieHom.mem_ker, LieIdeal.mkQ_ker]; rwa [sub_eq_zero.mp ha₀]
  · rw [← LieHom.mem_ker, LieIdeal.mkQ_ker]; rwa [sub_eq_zero.mp hb₀]

end AuxSerre

end Auxiliary

end KacMoody

end TauCeti
