/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Basis
import TauCeti.Algebra.Lie.Orthogonal.TypeD.Root.Classification
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Simplicity of the split even orthogonal Lie algebra

The split orthogonal Lie algebra on `Fin n ⊕ Fin n` is simple for `4 ≤ n` over a field of
characteristic zero. Consequently its Killing form is nondegenerate.

The Killing certificate makes the generic Borel and highest-weight APIs available for the concrete
type-`D` basis `TypeDStd.lieBasis`. In particular,
`LieAlgebra.Basis.borelSubalgebra_eq_sup_lieSpan_e` describes its compatible Borel using the
diagonal Cartan and raising generators, while
`LieAlgebra.Basis.isHighestWeightVector_iff_forall_e` reduces highest-weight conditions to the
action of those generators.

## Main results

* `TauCeti.TypeDStd.isSimple_typeD`: the split type-`D` Lie algebra is simple.
* `TauCeti.TypeDStd.isKilling_typeD`: its Killing form is nondegenerate.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8, 14.
-/

public section

open _root_.Matrix _root_.LieAlgebra

namespace TauCeti.TypeDStd

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K ι : Type*} [Field K] [DecidableEq ι] [Fintype ι]

private theorem lie_differenceRootGenerator_opposite (i j : ι) :
    ⁅differenceRootGenerator (K := K) i j, differenceRootGenerator (K := K) j i⁆ =
      (typeDDiagonalEquiv (K := K) (Pi.single i 1 - Pi.single j 1) :
        typeDDiagonalCartan K ι) := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, val_differenceRootGenerator,
    val_differenceRootGenerator, coe_typeDDiagonalEquiv_apply]
  -- All terms now lie in the matrix subtype, so expose the underlying block-matrix identity.
  change ⁅differenceRootMatrix (K := K) i j, differenceRootMatrix j i⁆ =
    typeDDiagonalMatrix (Pi.single i 1 - Pi.single j 1)
  rw [LieRing.of_associative_ring_bracket, differenceRootMatrix_def,
    differenceRootMatrix_def, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext (a | a) (b | b) <;>
    simp only [typeDDiagonalMatrix_apply, Matrix.fromBlocks, Matrix.transpose_single,
      typeDDiagonalValue_inl, typeDDiagonalValue_inr, Pi.sub_apply, Pi.single_apply, neg_sub]
  all_goals split_ifs <;> simp_all [eq_comm]

private theorem lie_sumRootGenerator_negSumRootGenerator (i j : ι) (hij : i ≠ j) :
    ⁅sumRootGenerator (K := K) i j, negSumRootGenerator (K := K) i j⁆ =
      (typeDDiagonalEquiv (K := K) (Pi.single i (-1) + Pi.single j (-1)) :
        typeDDiagonalCartan K ι) := by
  have hii : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : K)) i j i hij.symm 1
  have hjj : Matrix.single j i (1 : K) * Matrix.single j i 1 = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : K)) j i j hij 1
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, val_sumRootGenerator,
    val_negSumRootGenerator, coe_typeDDiagonalEquiv_apply]
  -- All terms now lie in the matrix subtype, so expose the underlying block-matrix identity.
  change ⁅sumRootMatrix (K := K) i j, negSumRootMatrix i j⁆ =
    typeDDiagonalMatrix (Pi.single i (-1) + Pi.single j (-1))
  rw [LieRing.of_associative_ring_bracket, sumRootMatrix_def,
    negSumRootMatrix_def, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext (a | a) (b | b) <;>
    simp [Matrix.mul_sub, Matrix.sub_mul, hii, hjj,
      typeDDiagonalMatrix_apply, Matrix.fromBlocks, Matrix.single_apply]
  all_goals split_ifs <;> aesop

private theorem typeDDiagonalEquiv_sub_ne_zero (i j : ι) (hij : i ≠ j) :
    (typeDDiagonalEquiv (K := K) (Pi.single i 1 - Pi.single j 1) :
      typeDDiagonalCartan K ι) ≠ 0 := by
  intro hzero
  apply_fun (typeDDiagonalEquiv (K := K) (ι := ι)).symm at hzero
  have hfun : (Pi.single i (1 : K) : ι → K) - Pi.single j 1 = 0 := by simpa using hzero
  have := congrFun hfun i
  simp [hij] at this

private theorem typeDDiagonalEquiv_add_neg_ne_zero (i j : ι) (hij : i ≠ j) :
    (typeDDiagonalEquiv (K := K) (Pi.single i (-1) + Pi.single j (-1)) :
      typeDDiagonalCartan K ι) ≠ 0 := by
  intro hzero
  apply_fun (typeDDiagonalEquiv (K := K) (ι := ι)).symm at hzero
  have hfun : (Pi.single i (-1 : K) : ι → K) + Pi.single j (-1) = 0 := by
    simpa using hzero
  have := congrFun hfun i
  simp [hij] at this

section Simple

variable [CharZero K]

private theorem exists_lieBasis_e_mem_of_cartan_mem
    (n : ℕ) (hn : 4 ≤ n)
    (I : LieIdeal K (LieAlgebra.Orthogonal.typeD (Fin n) K))
    {x : LieAlgebra.Orthogonal.typeD (Fin n) K}
    (hxI : x ∈ I) (hxH : x ∈ typeDDiagonalCartan K (Fin n)) (hx0 : x ≠ 0) :
    ∃ i, (lieBasis (K := K) n hn).e i ∈ I := by
  let b := lieBasis (K := K) n hn
  let bs : Module.Basis (Fin n) K (Module.Dual K (typeDDiagonalCartan K (Fin n))) :=
    basisOfLinearIndependentOfCardEqFinrank' b.baseSupp b.linearIndependent_baseSupp (by
      simp [finrank_typeDDiagonalCartan])
  let xH : typeDDiagonalCartan K (Fin n) := ⟨x, hxH⟩
  have hxH0 : xH ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_ne_zero K hxH0
  have heval : ∃ i, b.baseSupp i xH ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hphi
    conv_lhs => rw [← bs.sum_repr phi]
    simp [bs, hall]
  obtain ⟨i, hi⟩ := heval
  refine ⟨i, ?_⟩
  apply I.toSubmodule.smul_mem_iff hi |>.mp
  rw [b.baseSupp_apply_smul_e]
  exact lie_mem_left K _ I x (b.e i) hxI

private theorem exists_lieBasis_e_mem_of_root_inf_ne_bot
    (n : ℕ) (hn : 4 ≤ n)
    (I : LieIdeal K (LieAlgebra.Orthogonal.typeD (Fin n) K))
    (chi : Module.Dual K (typeDDiagonalCartan K (Fin n))) (hchi : chi ≠ 0)
    (hcomp : I.restr (typeDDiagonalCartan K (Fin n)) ⊓
      LieAlgebra.rootSpace (typeDDiagonalCartan K (Fin n)) chi ≠ ⊥) :
    ∃ i, (lieBasis (K := K) n hn).e i ∈ I := by
  let H := typeDDiagonalCartan K (Fin n)
  let L := LieAlgebra.Orthogonal.typeD (Fin n) K
  have hcomp' :
      (I.restr H ⊓ LieAlgebra.rootSpace H chi).toSubmodule ≠ ⊥ := by
    intro hbot
    apply hcomp
    exact LieSubmodule.toSubmodule_injective hbot
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomp'
  have hxI : x ∈ I := hx.1
  have hxroot : x ∈ LieAlgebra.rootSpace H chi := hx.2
  obtain ⟨i, j, hij, hsub | hadd | hneg⟩ :=
    (rootSpace_typeDDiagonalCartan_ne_bot_iff (K := K) two_ne_zero chi hchi).mp
      (fun hbot => hcomp (by simp [hbot]))
  · subst chi
    -- The root-space classification is stated for the underlying submodule membership.
    change x ∈ (LieAlgebra.rootSpace H (typeDWeightSub i j)).toSubmodule at hxroot
    rw [rootSpace_typeDWeightSub_eq_span (IsRegular.of_ne_zero two_ne_zero) hij] at hxroot
    have hgenI : differenceRootGenerator (K := K) i j ∈ I :=
      Submodule.mem_of_mem_span_singleton_of_ne_zero I.toSubmodule hxI hx0 hxroot
    let hdiag : H := typeDDiagonalEquiv (Pi.single i 1 - Pi.single j 1)
    have hdiagI : (hdiag : L) ∈ I := by
      rw [← lie_differenceRootGenerator_opposite]
      exact lie_mem_left K L I _ _ hgenI
    exact exists_lieBasis_e_mem_of_cartan_mem n hn I hdiagI hdiag.property
      (fun hzero => typeDDiagonalEquiv_sub_ne_zero (K := K) i j hij (Subtype.ext hzero))
  · subst chi
    -- The root-space classification is stated for the underlying submodule membership.
    change x ∈ (LieAlgebra.rootSpace H (typeDWeightAdd i j)).toSubmodule at hxroot
    rw [rootSpace_typeDWeightAdd_eq_span (IsRegular.of_ne_zero two_ne_zero) hij] at hxroot
    have hgenI : sumRootGenerator (K := K) i j ∈ I :=
      Submodule.mem_of_mem_span_singleton_of_ne_zero I.toSubmodule hxI hx0 hxroot
    let hdiag : H := typeDDiagonalEquiv (Pi.single i (-1) + Pi.single j (-1))
    have hdiagI : (hdiag : L) ∈ I := by
      rw [← lie_sumRootGenerator_negSumRootGenerator _ _ hij]
      exact lie_mem_left K L I _ _ hgenI
    exact exists_lieBasis_e_mem_of_cartan_mem n hn I hdiagI hdiag.property
      (fun hzero => typeDDiagonalEquiv_add_neg_ne_zero (K := K) i j hij (Subtype.ext hzero))
  · subst chi
    have hxroot' : x ∈ LieAlgebra.rootSpace H (-⇑(typeDWeightAdd i j)) := by
      simpa using hxroot
    -- The root-space classification is stated for the underlying submodule membership.
    change x ∈ (LieAlgebra.rootSpace H (-⇑(typeDWeightAdd i j))).toSubmodule at hxroot'
    rw [rootSpace_neg_typeDWeightAdd_eq_span
        (IsRegular.of_ne_zero two_ne_zero) hij] at hxroot'
    have hgenI : negSumRootGenerator (K := K) i j ∈ I :=
      Submodule.mem_of_mem_span_singleton_of_ne_zero I.toSubmodule hxI hx0 hxroot'
    let hdiag : H := typeDDiagonalEquiv (Pi.single i (-1) + Pi.single j (-1))
    have hdiagI : (hdiag : L) ∈ I := by
      rw [← lie_sumRootGenerator_negSumRootGenerator _ _ hij]
      exact lie_mem_right K L I _ _ hgenI
    exact exists_lieBasis_e_mem_of_cartan_mem n hn I hdiagI hdiag.property
      (fun hzero => typeDDiagonalEquiv_add_neg_ne_zero (K := K) i j hij (Subtype.ext hzero))

private theorem exists_lieBasis_e_mem_of_ne_bot
    (n : ℕ) (hn : 4 ≤ n)
    (I : LieIdeal K (LieAlgebra.Orthogonal.typeD (Fin n) K)) (hI : I ≠ ⊥) :
    ∃ i, (lieBasis (K := K) n hn).e i ∈ I := by
  let H := typeDDiagonalCartan K (Fin n)
  let L := LieAlgebra.Orthogonal.typeD (Fin n) K
  let b := lieBasis (K := K) n hn
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  have hrestr : I.restr H ≠ ⊥ := by
    intro hbot
    apply hI
    ext x
    constructor
    · intro hx
      have hx' : x ∈ I.restr H := hx
      rw [hbot] at hx'
      simpa using hx'
    · intro hx
      have : x = 0 := by simpa using hx
      subst x
      exact I.zero_mem
  have hdecomp := LieAlgebra.lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace H I
  by_cases hcart : I.restr H ⊓ H.toLieSubmodule = ⊥
  · have hroots :
        (⨆ alpha : LieModule.Weight K H L, ⨆ (_ : alpha.IsNonZero),
          I.restr H ⊓ LieAlgebra.rootSpace H alpha) ≠ ⊥ := by
      intro hbot
      apply hrestr
      rw [hdecomp, hcart, hbot]
      simp
    have hex : ∃ alpha : LieModule.Weight K H L, ∃ hα : alpha.IsNonZero,
        I.restr H ⊓ LieAlgebra.rootSpace H alpha ≠ ⊥ := by
      by_contra hnone
      simp only [not_exists] at hnone
      apply hroots
      rw [iSup_eq_bot]
      intro alpha
      rw [iSup_eq_bot]
      intro hα
      exact not_ne_iff.mp (hnone alpha hα)
    obtain ⟨alpha, hα, hcomp⟩ := hex
    exact exists_lieBasis_e_mem_of_root_inf_ne_bot n hn I alpha
      (LieModule.Weight.coe_toLinear_ne_zero_iff.mpr hα) hcomp
  · have hcart' : (I.restr H ⊓ H.toLieSubmodule).toSubmodule ≠ ⊥ :=
      fun hbot => hcart (LieSubmodule.toSubmodule_injective hbot)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcart'
    exact exists_lieBasis_e_mem_of_cartan_mem n hn I hx.1 hx.2 hx0

private theorem lieBasis_e_mem_of_diagramGraph_adj
    (n : ℕ) (hn : 4 ≤ n)
    (I : LieIdeal K (LieAlgebra.Orthogonal.typeD (Fin n) K))
    {i j : Fin n} (hi : (lieBasis (K := K) n hn).e i ∈ I)
    (hij : (diagramGraph (CartanMatrix.D n)).Adj i j) :
    (lieBasis (K := K) n hn).e j ∈ I := by
  let b := lieBasis (K := K) n hn
  have hhi : b.h i ∈ I := by
    rw [← (b.sl2 i).lie_e_f]
    exact lie_mem_left K _ I _ _ hi
  have hbracket : ⁅b.h i, b.e j⁆ ∈ I := lie_mem_left K _ I _ _ hhi
  rw [b.lie_h_e j i] at hbracket
  have hentry : (b.A j i : K) ≠ 0 := by
    -- Expose the integer Cartan entry detected by adjacency before casting it to the field.
    change ((lieBasis (K := K) n hn).A j i : K) ≠ 0
    rw [lieBasis_A_eq]
    exact Int.cast_ne_zero.mpr ((diagramGraph_adj.mp hij).2.2)
  have hbracket' : (b.A j i : K) • b.e j ∈ I := by
    simpa only [Int.cast_smul_eq_zsmul] using hbracket
  have : b.e j ∈ I := I.toSubmodule.smul_mem_iff hentry |>.mp hbracket'
  simpa [b] using this

private theorem forall_lieBasis_e_mem_of_exists
    (n : ℕ) (hn : 4 ≤ n)
    (I : LieIdeal K (LieAlgebra.Orthogonal.typeD (Fin n) K))
    (hex : ∃ i, (lieBasis (K := K) n hn).e i ∈ I) :
    ∀ j, (lieBasis (K := K) n hn).e j ∈ I := by
  obtain ⟨i, hi⟩ := hex
  have hconnected : (diagramGraph (CartanMatrix.D n)).Connected := by
    simpa using DynkinType.connected_diagramGraph_cartanMatrix
      (t := DynkinType.D n) (DynkinType.valid_D.mpr hn)
  intro j
  obtain ⟨p⟩ := hconnected i j
  let rec alongWalk {a b : Fin n}
      (ha : (lieBasis (K := K) n hn).e a ∈ I)
      (p : (diagramGraph (CartanMatrix.D n)).Walk a b) :
      (lieBasis (K := K) n hn).e b ∈ I :=
    match p with
    | .nil => ha
    | .cons hadj p => alongWalk (lieBasis_e_mem_of_diagramGraph_adj n hn I ha hadj) p
  exact alongWalk hi p

/-- The split even orthogonal Lie algebra of type `Dₙ` is simple in characteristic zero. -/
theorem isSimple_typeD (n : ℕ) (hn : 4 ≤ n) :
    LieAlgebra.IsSimple K (LieAlgebra.Orthogonal.typeD (Fin n) K) where
  eq_bot_or_eq_top I := by
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      let b := lieBasis (K := K) n hn
      have he : ∀ i, b.e i ∈ I :=
        forall_lieBasis_e_mem_of_exists n hn I (exists_lieBasis_e_mem_of_ne_bot n hn I hI)
      have hh (i : Fin n) : b.h i ∈ I := by
        rw [← (b.sl2 i).lie_e_f]
        exact lie_mem_left K _ I _ _ (he i)
      have hf (i : Fin n) : b.f i ∈ I := by
        have hbracket : ⁅b.h i, b.f i⁆ ∈ I := lie_mem_left K _ I _ _ (hh i)
        rw [(b.sl2 i).lie_lie_smul_f (R := K)] at hbracket
        have hbracket' : (-(2 : K)) • b.f i ∈ I := by
          simpa [neg_smul, two_smul] using hbracket
        have htwo : (2 : K) ≠ 0 := by norm_num
        apply I.toSubmodule.smul_mem_iff (neg_ne_zero.mpr htwo) |>.mp
        exact hbracket'
      apply eq_top_iff.mpr
      intro x _
      have hspan : LieSubalgebra.lieSpan K _ (Set.range b.e ∪ Set.range b.f) ≤
          I.toLieSubalgebra := by
        rw [LieSubalgebra.lieSpan_le]
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact he i
        · exact hf i
      apply hspan
      rw [b.span_ef]
      trivial
  non_abelian := by
    intro habelian
    let _ := habelian
    let b := lieBasis (K := K) n hn
    let i : Fin n := ⟨0, by omega⟩
    apply (b.sl2 i).h_ne_zero
    rw [← (b.sl2 i).lie_e_f]
    exact trivial_lie_zero (LieAlgebra.Orthogonal.typeD (Fin n) K)
      (LieAlgebra.Orthogonal.typeD (Fin n) K) _ _

/-- The Killing form of the split even orthogonal Lie algebra of type `Dₙ` is nondegenerate in
characteristic zero. -/
theorem isKilling_typeD (n : ℕ) (hn : 4 ≤ n) :
    LieAlgebra.IsKilling K (LieAlgebra.Orthogonal.typeD (Fin n) K) := by
  let _ : LieAlgebra.IsSimple K (LieAlgebra.Orthogonal.typeD (Fin n) K) :=
    isSimple_typeD n hn
  infer_instance

end Simple

end TauCeti.TypeDStd
