/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Adjoint weights of dynamic tangent spaces

For a cocharacter, the Lie algebra of its dynamic parabolic is the sum of the
nonnegative adjoint weight spaces, and that of its dynamic unipotent subgroup is the
sum of the strictly positive weight spaces. The coefficient of infinitesimal conjugation
extracts the corresponding weight component.

These statements use the existing adjoint comodule and its internal weight decomposition.
They assume finite projectivity of the augmentation cotangent module, but impose no field,
characteristic, reducedness or smoothness assumption.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct DirectSum

namespace BialgHom

universe u

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

attribute [local instance] Derivation.adjointComodule Classical.decEq

private theorem adDerivation_genericPoint_of_mem_adjointWeightSpace
    (l : H →ₐc[R] LaurentPolynomial R) (m : ℤ)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H))
    (hx : x ∈ Derivation.adjointWeightSpace
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
      (Multiplicative.ofAdd m)) :
    Derivation.adDerivation (LaurentPolynomial R)
        (Derivation.pointInCounitAlgebra (LaurentPolynomial R) (genericPoint R l))
        (Derivation.mapValue (Algebra.ofId R (LaurentPolynomial R))
          (Derivation.cotangentLinearEquiv (B := R) x)) =
      (LaurentPolynomial.T m : LaurentPolynomial R) •
        Derivation.mapValue (Algebra.ofId R (LaurentPolynomial R))
          (Derivation.cotangentLinearEquiv (B := R) x) := by
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ
  let π := e.toBialgHom.comp l
  let f := e.symm.toAlgEquiv.toAlgHom
  have hp : f.comp π.toAlgHom = (genericPoint R l).ofConv := by
    ext a : 1
    simp only [f, π, BialgHom.comp_toAlgHom, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, genericPoint_ofConv]
    ext n
    simp
  have ht : f (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : R)) =
      LaurentPolynomial.T m := by
    apply e.injective
    rw [← AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := R) (A := R) (M := ℤ) m 1]
    exact e.apply_symm_apply _
  have ha := Derivation.endOfPoint_tmul_of_mem_adjointWeightSpace π f 1 hx
  rw [hp, one_mul, ht] at ha
  have hd := congrArg (Derivation.tangentScalarExtensionEquiv
    (R := R) (A := H) (B := LaurentPolynomial R)) ha
  rw [Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
      (CommAlgCat.of R (LaurentPolynomial R)),
    Derivation.tangentScalarExtensionEquiv_tmul,
    Derivation.tangentScalarExtensionEquiv_tmul, one_smul] at hd
  exact hd

/-- On an adjoint weight vector of weight `m`, differentiation of the `n`th universal
conjugation coefficient is zero unless `n = m`, when it recovers the vector. -/
theorem cotangentLinearEquiv_coeff_conjugationAlgHom_of_mem_adjointWeightSpace
    (l : H →ₐc[R] LaurentPolynomial R) {m : ℤ}
    {x : Module.Dual R (Bialgebra.CotangentSpace R H)}
    (hx : x ∈ Derivation.adjointWeightSpace
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
      (Multiplicative.ofAdd m)) (h : H) (n : ℤ) :
    Derivation.cotangentLinearEquiv (B := R) x ((Cocharacter.conjugationAlgHom l h).coeff n) =
      if n = m then Derivation.cotangentLinearEquiv (B := R) x h else 0 := by
  have he := adDerivation_genericPoint_of_mem_adjointWeightSpace l m x hx
  have hc := congrArg (fun D : Derivation R H
      (Bialgebra.CounitAlgebra R H (LaurentPolynomial R)) =>
    (Bialgebra.CounitAlgebra.algEquivSelf R H (LaurentPolynomial R) (D h)).coeff n) he
  have hm : IsScalarTower.toAlgHom R R (LaurentPolynomial R) =
      Algebra.ofId R (LaurentPolynomial R) := by ext
  rw [← hm, Derivation.coeff_adDerivation_genericPoint] at hc
  rw [TauCeti.algEquivSelf_derivation_smul_apply, Derivation.mapValue_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_map] at hc
  simp only [hm, Algebra.ofId_apply, ← LaurentPolynomial.C_eq_algebraMap,
    ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_mul_single_zero,
    LaurentPolynomial.T_apply] at hc
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  simpa only [eq_comm (a := m) (b := n), ite_mul, one_mul, zero_mul,
    apply_ite, map_zero] using hc

private theorem cotangentLinearEquiv_decompose_adjointWeightSpace_apply
    (l : H →ₐc[R] LaurentPolynomial R)
    (y : Module.Dual R (Bialgebra.CotangentSpace R H)) (n : ℤ) (h : H) :
    let : DecidableEq (Multiplicative ℤ) := Classical.decEq _
    let W := Derivation.adjointWeightSpace
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
    let : DirectSum.Decomposition W :=
      (Derivation.isInternal_adjointWeightSpace _).chooseDecomposition
    Derivation.cotangentLinearEquiv (B := R) y
        ((Cocharacter.conjugationAlgHom l h).coeff n) =
      Derivation.cotangentLinearEquiv (B := R)
        (DirectSum.decompose W y (Multiplicative.ofAdd n) :
          Module.Dual R (Bialgebra.CotangentSpace R H)) h := by
  dsimp only
  classical
  let : DecidableEq (Multiplicative ℤ) := Classical.decEq _
  let π := (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l
  let W := Derivation.adjointWeightSpace π
  let : DirectSum.Decomposition W :=
    (Derivation.isInternal_adjointWeightSpace π).chooseDecomposition
  have hy : y ∈ ⨆ α, W α := by
    rw [(Derivation.isInternal_adjointWeightSpace π).submodule_iSup_eq_top]
    trivial
  induction hy using Submodule.iSup_induction' with
  | mem α y hy =>
    rw [cotangentLinearEquiv_coeff_conjugationAlgHom_of_mem_adjointWeightSpace
      l (m := α.toAdd) hy]
    by_cases hα : α = Multiplicative.ofAdd n
    · subst α
      rw [DirectSum.decompose_of_mem_same W hy]
      exact ite_eq_left rfl
    · rw [DirectSum.decompose_of_mem_ne W hy hα]
      simp only [map_zero, Derivation.zero_apply, ite_eq_right_iff]
      intro hn
      exact (hα (congrArg Multiplicative.ofAdd hn.symm)).elim
  | zero =>
    simp only [map_zero, DirectSum.decompose_zero, DirectSum.zero_apply,
      Submodule.coe_zero, Derivation.zero_apply]
  | add y z _ _ hy hz =>
    simpa only [map_add, Derivation.add_apply, DirectSum.decompose_add,
      DirectSum.add_apply, Submodule.coe_add] using congrArg₂ (· + ·) hy hz

/-- The sum of a set of adjoint weight spaces is characterized by vanishing of the
infinitesimal conjugation coefficients at all weights outside that set. -/
theorem mem_iSup_adjointWeightSpace_iff_coeff_conjugationAlgHom
    (l : H →ₐc[R] LaurentPolynomial R) (s : Set ℤ)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    x ∈ (⨆ n ∈ s, Derivation.adjointWeightSpace
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
      (Multiplicative.ofAdd n)) ↔
      ∀ h : H, ∀ n : ℤ, n ∉ s →
        Derivation.cotangentLinearEquiv (B := R) x
          ((Cocharacter.conjugationAlgHom l h).coeff n) = 0 := by
  classical
  let : DecidableEq (Multiplicative ℤ) := Classical.decEq _
  let π := (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l
  let W := Derivation.adjointWeightSpace π
  let : DirectSum.Decomposition W :=
    (Derivation.isInternal_adjointWeightSpace π).chooseDecomposition
  constructor
  · intro hx h n hn
    induction hx using Submodule.iSup_induction' with
    | mem m y hy =>
      induction hy using Submodule.iSup_induction' with
      | mem hm y hy =>
        rw [cotangentLinearEquiv_coeff_conjugationAlgHom_of_mem_adjointWeightSpace l hy]
        simp only [ite_eq_right_iff]
        intro hnm
        subst m
        exact (hn hm).elim
      | zero => simp
      | add y z _ _ hy hz =>
          simpa only [map_add, Derivation.add_apply, add_zero] using congrArg₂ (· + ·) hy hz
    | zero => simp
    | add y z _ _ hy hz =>
        simpa only [map_add, Derivation.add_apply, add_zero] using congrArg₂ (· + ·) hy hz
  · intro hx
    have hzero (n : ℤ) (hn : n ∉ s) :
        (DirectSum.decompose W x (Multiplicative.ofAdd n) :
          Module.Dual R (Bialgebra.CotangentSpace R H)) = 0 := by
      apply (Derivation.cotangentLinearEquiv (B := R)).injective
      ext h
      rw [← cotangentLinearEquiv_decompose_adjointWeightSpace_apply l,
        hx h n hn, map_zero, Derivation.zero_apply]
    rw [← DirectSum.sum_support_decompose W x]
    apply Submodule.sum_mem
    intro α _
    by_cases hα : α.toAdd ∈ s
    · exact Submodule.mem_iSup_of_mem α.toAdd
        (Submodule.mem_iSup_of_mem hα (DirectSum.decompose W x α).property)
    · exact (hzero α.toAdd hα) ▸ Submodule.zero_mem _

/-- The tangent Lie algebra of the dynamic parabolic is the sum of the nonnegative
adjoint weight spaces, transported from the cotangent-dual model of the ambient Lie algebra. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule
    (l : H →ₐc[R] LaurentPolynomial R) :
    ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := R)).toSubmodule =
      (⨆ n : ℤ, ⨆ (_ : 0 ≤ n), Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd n)).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  ext d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).surjective d
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    LieSubalgebra.mem_toSubmodule, mem_lieSubalgebra_parabolicDefiningHopfIdeal_iff]
  simpa only [Set.mem_Ici, not_le] using
    (mem_iSup_adjointWeightSpace_iff_coeff_conjugationAlgHom l (Set.Ici 0) x).symm

/-- The tangent Lie algebra of the dynamic unipotent subgroup is the sum of the strictly
positive adjoint weight spaces, transported from the cotangent-dual model. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule
    (l : H →ₐc[R] LaurentPolynomial R) :
    (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := R)).toSubmodule =
      (⨆ n : ℤ, ⨆ (_ : 0 < n), Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd n)).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  ext d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).surjective d
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    LieSubalgebra.mem_toSubmodule, mem_lieSubalgebra_unipotentDefiningHopfIdeal_iff]
  simpa only [Set.mem_Ioi, not_lt] using
    (mem_iSup_adjointWeightSpace_iff_coeff_conjugationAlgHom l (Set.Ioi 0) x).symm

end BialgHom
