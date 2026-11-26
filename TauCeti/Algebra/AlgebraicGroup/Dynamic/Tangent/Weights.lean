/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Representability
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
import Mathlib.Algebra.DirectSum.Decomposition
import TauCeti.Algebra.Bialgebra.MonoidAlgebra.Equiv

/-!
# Adjoint weights of dynamic tangent spaces

For a cocharacter, the Lie algebra of its dynamic parabolic is the sum of the
nonnegative adjoint weight spaces, that of its dynamic unipotent subgroup is the
sum of the strictly positive weight spaces, and that of its dynamic Levi subgroup is the
zero adjoint weight space. The coefficient of infinitesimal conjugation extracts the
corresponding weight component.

These statements use the existing adjoint comodule and its internal weight decomposition.
They assume finite projectivity of the augmentation cotangent module, but impose no field,
characteristic, reducedness or smoothness assumption. Over a characteristic-zero domain `R`,
characters of `𝔾ₘ` are separated by the unit tangent vector
(`BialgHom.weightSpace_cocharacter_eq_eigenspace` in `MultiplicativeGroup.Differential`),
identifying each `m`-adjoint weight space on `Lie(G)` with the `(m : R)`-eigenspace of the
cocharacter's unit tangent differential (`BialgHom.adjointWeightSpace_cocharacter_eq_eigenspace`,
`BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace`,
`BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace`,
`BialgHom.lieSubalgebra_leviDefiningHopfIdeal_eq_eigenspace`).
In addition, `BialgHom.basePointsRepresentation_pointsHom_of_mem_weightSpace` evaluates the action
of `Cocharacter.pointsHom` on any `m`-weight vector as multiplication by `s ^ m`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open LieAlgebra TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct DirectSum LaurentPolynomial

namespace BialgHom

/-- A point `l(s)` of a cocharacter `l : H →ₐc[R] R[T;T⁻¹]` acts on the `m`-weight space of `l`
by multiplication by `s ^ m`. -/
theorem basePointsRepresentation_pointsHom_of_mem_weightSpace
    {R H V : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
    [AddCommMonoid V] [Module R V] [Comodule R H V]
    (l : H →ₐc[R] LaurentPolynomial R) (s : Rˣ) {m : ℤ} {v : V}
    (hv : v ∈ DiagonalizableGroup.weightSpace V
      (((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l).toCoalgHom)
      (Multiplicative.ofAdd m)) :
    Comodule.basePointsRepresentation (H := H) V (Cocharacter.pointsHom R l s) v =
      ((s ^ m : Rˣ) : R) • v := by
  let eMult := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ
  let f : MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] R :=
    (laurentEval (R := R) s).comp eMult.symm.toAlgEquiv.toAlgHom
  have hmap : (Cocharacter.pointsHom R l s).ofConv = f.comp (eMult.toBialgHom.comp l).toAlgHom := by
    ext a; simp [Cocharacter.pointsHom_apply, BialgHom.mapDomain_apply, f, eMult]
  have ht : eMult.symm (MonoidAlgebra.single (Multiplicative.ofAdd m) (1 : R)) =
      LaurentPolynomial.T m :=
    eMult.symm_apply_eq.mpr
      (AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := R) (A := R) (M := ℤ) m 1).symm
  rw [Comodule.basePointsRepresentation_apply, hmap,
    DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace V _ f 1 hv]
  simp [f, ht]

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

/-- The tangent Lie algebra of the dynamic Levi subgroup is the zero adjoint weight space,
transported from the cotangent-dual model of the ambient Lie algebra. -/
theorem lieSubalgebra_leviDefiningHopfIdeal_toSubmodule
    (l : H →ₐc[R] LaurentPolynomial R) :
    ((leviDefiningHopfIdeal l).lieSubalgebra (B := R)).toSubmodule =
      (Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd (0 : ℤ))).map
        (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).toLinearMap := by
  have hopp (h : H) (n : ℤ) :
      (Cocharacter.conjugationAlgHom l.oppositeCocharacter h).coeff n =
        (Cocharacter.conjugationAlgHom l h).coeff (-n) := by
    have hc := congrArg (fun p : WithConv (H →ₐ[R] LaurentPolynomial H) ↦ (p.ofConv h).coeff n)
      (Cocharacter.conjugate_oppositeCocharacter l (toConv (AlgHom.id R H)))
    simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom, LaurentPolynomial.invert_apply,
      Cocharacter.coeff_conjugate, AlgHom.id_apply] using hc
  ext d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).surjective d
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, LieSubalgebra.mem_toSubmodule,
    leviDefiningHopfIdeal_def, HopfIdeal.mem_lieSubalgebra_sup_iff,
    mem_lieSubalgebra_parabolicDefiningHopfIdeal_iff,
    mem_lieSubalgebra_parabolicDefiningHopfIdeal_iff]
  have hsing := mem_iSup_adjointWeightSpace_iff_coeff_conjugationAlgHom l {0} x
  rw [iSup_singleton] at hsing
  rw [hsing]
  constructor
  · rintro ⟨h₁, h₂⟩ h n hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact h₁ h n hlt
    · simpa only [hopp, neg_neg] using h₂ h (-n) (neg_neg_of_pos hgt)
  · intro h
    refine ⟨fun a n hn ↦ h a n hn.ne, fun a n hn ↦ ?_⟩
    rw [hopp]
    exact h a (-n) (neg_pos.mpr hn).ne'

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
  rw [Derivation.cotangentDualLieEquiv_apply, map_smul,
    ← Derivation.cotangentDualLieEquiv_apply]; rfl

/-- Over a characteristic-zero domain `R`, the underlying submodule of `Lie(P_G(l))` is the
supremum of the `(n : R)`-eigenspaces of `ad` of its unit tangent differential for `0 ≤ n`. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace [IsDomain R] [CharZero R]
    (l : H →ₐc[R] LaurentPolynomial R) :
    ((parabolicDefiningHopfIdeal l).lieSubalgebra (B := R)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 ≤ n), Module.End.eigenspace
        (ad R (Derivation R H (Bialgebra.CounitAlgebra R H R)) (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) (n : R) := by
  rw [l.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule]
  simp_rw [Submodule.map_iSup, l.map_cotangentLinearEquiv_adjointWeightSpace_cocharacter]

/-- Over a characteristic-zero domain `R`, the underlying submodule of `Lie(U_G(l))` is the
supremum of the `(n : R)`-eigenspaces of `ad` of its unit tangent differential for `0 < n`. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace [IsDomain R] [CharZero R]
    (l : H →ₐc[R] LaurentPolynomial R) :
    (l.unipotentDefiningHopfIdeal.lieSubalgebra (B := R)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 < n), Module.End.eigenspace
        (ad R (Derivation R H (Bialgebra.CounitAlgebra R H R)) (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) (n : R) := by
  rw [l.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule]
  simp_rw [Submodule.map_iSup, l.map_cotangentLinearEquiv_adjointWeightSpace_cocharacter]

/-- Over a characteristic-zero domain `R`, the underlying submodule of `Lie(Z_G(l))` is the
zero eigenspace of `ad` of its unit tangent differential. -/
theorem lieSubalgebra_leviDefiningHopfIdeal_eq_eigenspace [IsDomain R] [CharZero R]
    (l : H →ₐc[R] LaurentPolynomial R) :
    ((leviDefiningHopfIdeal l).lieSubalgebra (B := R)).toSubmodule =
      Module.End.eigenspace
        (ad R (Derivation R H (Bialgebra.CounitAlgebra R H R)) (derivationComp (B := R) l
          ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := R)).symm 1))) 0 := by
  rw [l.lieSubalgebra_leviDefiningHopfIdeal_toSubmodule]
  simpa only [Int.cast_zero] using l.map_cotangentLinearEquiv_adjointWeightSpace_cocharacter 0

end BialgHom
