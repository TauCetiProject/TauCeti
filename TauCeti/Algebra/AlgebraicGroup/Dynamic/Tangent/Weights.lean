/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import Mathlib.Algebra.DirectSum.Decomposition
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv

/-!
# Adjoint weights of dynamic tangent spaces

For a cocharacter, the Lie algebra of its dynamic parabolic is the sum of the
nonnegative adjoint weight spaces, and that of its dynamic unipotent subgroup is the
sum of the strictly positive weight spaces. The coefficient of infinitesimal conjugation
extracts the corresponding weight component.

These statements use the existing adjoint comodule and its internal weight decomposition.
They assume finite projectivity of the augmentation cotangent module, but impose no field,
characteristic, reducedness or smoothness assumption. Over a characteristic-zero domain `R`,
characters of `𝔾ₘ` are separated by the unit tangent vector, identifying the `m`-weight space on
any torsion-free comodule and on `Lie(G)` with the `(m : R)`-eigenspace of the cocharacter's unit
tangent differential (`BialgHom.weightSpace_cocharacter_eq_eigenspace`,
`BialgHom.adjointWeightSpace_cocharacter_eq_eigenspace`).

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open LieAlgebra TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct DirectSum LaurentPolynomial

namespace BialgHom

universe u

section Eigenspace

/-- Over a characteristic-zero domain `R`, the `m`-weight space of `l : H →ₐc[R] R[T;T⁻¹]` on any
torsion-free `H`-comodule `V` equals the `(m : R)`-eigenspace of its unit tangent differential. -/
theorem weightSpace_cocharacter_eq_eigenspace {R H : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing H] [Bialgebra R H] (l : H →ₐc[R] LaurentPolynomial R) (V : Type*) [AddCommGroup V]
    [Module R V] [Module.IsTorsionFree R V] [Comodule R H V] (m : ℤ) :
    DiagonalizableGroup.weightSpace V
        (((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l).toCoalgHom)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace (Comodule.differential (R := R) (H := H) (M := V)
        (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) (m : R) := by
  let eMult := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ
  let π : H →ₐc[R] MonoidAlgebra R (Multiplicative ℤ) := eMult.toBialgHom.comp l
  let d₁ := (MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1
  let d₀ := derivationComp (B := R) eMult.symm.toBialgHom d₁
  have hd₀ (x : Multiplicative ℤ) : Bialgebra.CounitAlgebra.algEquivSelf R
      (MonoidAlgebra R (Multiplicative ℤ)) R (d₀ (MonoidAlgebra.single x 1)) = (x.toAdd : R) := by
    rw [algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single,
      ← LaurentPolynomial.T, MultiplicativeGroup.tangentLinearEquiv_symm_apply_T, zsmul_one]
  have hinj : Function.Injective fun x : Multiplicative ℤ ↦ Bialgebra.CounitAlgebra.algEquivSelf R
      (MonoidAlgebra R (Multiplicative ℤ)) R (d₀ (MonoidAlgebra.single x 1)) := fun x y hxy ↦
    Multiplicative.toAdd.injective (Int.cast_inj.mp ((hd₀ x).symm.trans (hxy.trans (hd₀ y))))
  have hπd₀ : derivationComp (B := R) π d₀ = derivationComp (B := R) l d₁ := by
    rw [derivationComp_comp, LinearMap.comp_apply,
      derivationComp_derivationComp_eq_self_of_comp_eq_id _ _ (BialgHom.ext eMult.symm_apply_apply)]
  rw [DiagonalizableGroup.weightSpace_eq_eigenspace_differential_of_injective V π d₀ hinj
      (Multiplicative.ofAdd m), hπd₀, hd₀, toAdd_ofAdd]

end Eigenspace

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
      simp only [map_zero, _root_.zero_apply, ite_eq_right_iff]
      intro hn
      exact (hα (congrArg Multiplicative.ofAdd hn.symm)).elim
  | zero =>
    simp only [map_zero, DirectSum.decompose_zero, DirectSum.zero_apply,
      Submodule.coe_zero, _root_.zero_apply]
  | add y z _ _ hy hz =>
    simpa only [map_add, _root_.add_apply, DirectSum.decompose_add,
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
          simpa only [map_add, _root_.add_apply, add_zero] using congrArg₂ (· + ·) hy hz
    | zero => simp
    | add y z _ _ hy hz =>
        simpa only [map_add, _root_.add_apply, add_zero] using congrArg₂ (· + ·) hy hz
  · intro hx
    have hzero (n : ℤ) (hn : n ∉ s) :
        (DirectSum.decompose W x (Multiplicative.ofAdd n) :
          Module.Dual R (Bialgebra.CotangentSpace R H)) = 0 := by
      apply (Derivation.cotangentLinearEquiv (B := R)).injective
      ext h
      rw [← cotangentLinearEquiv_decompose_adjointWeightSpace_apply l,
        hx h n hn, map_zero, _root_.zero_apply]
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

/-- Over a characteristic-zero domain `R`, the `m`-adjoint weight space of a cocharacter
`l : H →ₐc[R] R[T;T⁻¹]` coincides with the `(m : R)`-eigenspace of `ad` of its unit tangent
differential in the cotangent-dual Lie algebra. -/
theorem adjointWeightSpace_cocharacter_eq_eigenspace [IsDomain R] [CharZero R]
    (l : H →ₐc[R] LaurentPolynomial R) (m : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace (ad R (Module.Dual R (Bialgebra.CotangentSpace R H))
        ((Derivation.cotangentDualLieEquiv (R := R) (H := H)).symm (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1)))) (m : R) := by
  rw [Derivation.adjointWeightSpace_eq_weightSpace,
    l.weightSpace_cocharacter_eq_eigenspace (Module.Dual R (Bialgebra.CotangentSpace R H)) m]
  exact congrArg (Module.End.eigenspace · (m : R))
    (LinearMap.ext fun x ↦ Derivation.differential_adjointComodule _ x)

/-- Transporting the `n`-adjoint weight space of `l : H →ₐc[R] R[T;T⁻¹]` across
`Derivation.cotangentLinearEquiv` yields the `(n : R)`-eigenspace of `ad` of its unit tangent
differential on `Der_R(H, R)`. -/
theorem map_cotangentLinearEquiv_adjointWeightSpace_cocharacter [IsDomain R] [CharZero R]
    (l : H →ₐc[R] LaurentPolynomial R) (n : ℤ) :
    Submodule.map (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R) : _ →ₗ[R] _)
        (Derivation.adjointWeightSpace
          ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
          (Multiplicative.ofAdd n)) =
      Module.End.eigenspace (ad R (Derivation R H (Bialgebra.CounitAlgebra R H R))
        (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) (n : R) := by
  rw [l.adjointWeightSpace_cocharacter_eq_eigenspace]; ext d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).surjective d
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    ← Derivation.cotangentDualLieEquiv_apply, Module.End.mem_eigenspace_iff,
    Module.End.mem_eigenspace_iff, ad_apply, ad_apply]
  simp only [← (Derivation.cotangentDualLieEquiv (R := R) (H := H)).injective.eq_iff,
    LieEquiv.coe_toLieHom, LieEquiv.map_lie, LieEquiv.apply_symm_apply]
  rw [Derivation.cotangentDualLieEquiv_apply, map_smul, ← Derivation.cotangentDualLieEquiv_apply]
  rfl

/-- Over a characteristic-zero domain `R`, the underlying submodule of `Lie(P_G(l))` is the
supremum of the `(n : R)`-eigenspaces of `ad` of its unit tangent differential for `0 ≤ n`. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace [IsDomain R] [CharZero R]
    (l : H →ₐc[R] LaurentPolynomial R) :
    ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := R)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 ≤ n), Module.End.eigenspace
        (ad R (Derivation R H (Bialgebra.CounitAlgebra R H R)) (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) (n : R) := by
  rw [l.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule, Submodule.map_iSup]
  refine iSup_congr fun n ↦ ?_; rw [Submodule.map_iSup]
  exact iSup_congr fun _ ↦ l.map_cotangentLinearEquiv_adjointWeightSpace_cocharacter n

/-- Over a characteristic-zero domain `R`, the underlying submodule of `Lie(U_G(l))` is the
supremum of the `(n : R)`-eigenspaces of `ad` of its unit tangent differential for `0 < n`. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace [IsDomain R] [CharZero R]
    (l : H →ₐc[R] LaurentPolynomial R) :
    (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := R)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 < n), Module.End.eigenspace
        (ad R (Derivation R H (Bialgebra.CounitAlgebra R H R)) (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) (n : R) := by
  rw [l.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule, Submodule.map_iSup]
  refine iSup_congr fun n ↦ ?_; rw [Submodule.map_iSup]
  exact iSup_congr fun _ ↦ l.map_cotangentLinearEquiv_adjointWeightSpace_cocharacter n

end BialgHom
