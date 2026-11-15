/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Weights
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Sl2Triple.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential

/-!
# The cocharacter of an `sl₂` triple and its weight decomposition

Restricting the `i`-th coordinate of the diagonal torus of `SL_{r+1}` defines
`SpecialLinear.simpleCorootCocharacter`, sending `u : Aˣ` to `diag2nUnit _ u` and tangent parameter
`c` to `singleSubSingle i.castSucc i.succ c`. Composing `simpleCorootCocharacter 1 k 0` with
`IsSl2Triple.sl2CoordinateMap` attaches `IsSl2Triple.cocharacter : H →ₐc[k] k[T;T⁻¹]` with unit
differential `h`, equating its `m`-weight space on every `H`-comodule to the `(m : k)`-eigenspace
of `h` (`weightSpace_cocharacter_eq_eigenspace`) and pinning the Lie algebras of
`P_G(t.cocharacter)` and `U_G(t.cocharacter)` to `⨁_{n ≥ 0} 𝔤(n)` and `⨁_{n > 0} 𝔤(n)`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., §7; B. Conrad, O. Gabber, G. Prasad,
  *Pseudo-reductive Groups*, 2nd ed., §2.1; D. H. Collingwood, W. M. McGovern, §3.3, §3.8.
-/

public section

open CategoryTheory LieAlgebra TauCeti TauCeti.Cocharacter WithConv
open scoped LaurentPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SpecialLinear

universe u v

section SimpleCoroot

variable (r : ℕ) (R : Type u) [CommRing R]

/-- **The `i`-th simple-coroot cocharacter of `SL_{r+1}`**, restricting the `i`-th coordinate of
`diagonalTorusCoordinateMap r R`. -/
noncomputable def simpleCorootCocharacter (i : Fin r) :
    coordinateHopfAlgebra R (r + 1) →ₐc[R] LaurentPolynomial R :=
  (diagonalTorusCoordinateMap r R).hom.cocharacter
    (Finsupp.applyAddHom (ULift.up i)).toMultiplicative

variable {r R}

/-- On `A`-points, `simpleCorootCocharacter r R i` sends `u : Aˣ` to `diag2nUnit _ u`. -/
@[simp]
theorem pointsMulEquiv_pointsHom_simpleCorootCocharacter {A : Type v} [CommRing A] [Algebra R A]
    (i : Fin r) (u : Aˣ) :
    pointsMulEquiv (R := R) (A := A) (r + 1)
        (Cocharacter.pointsHom A (simpleCorootCocharacter r R i) u) =
      Matrix.SpecialLinearGroup.diag2nUnit
        ((Fin.castSucc_lt_succ_iff (a := i) (b := i)).mpr le_rfl).ne u := by
  have hne : i.castSucc ≠ i.succ := ((Fin.castSucc_lt_succ_iff (a := i) (b := i)).mpr le_rfl).ne
  let ψ := (Finsupp.applyAddHom (M := ℤ) (ULift.up.{u} i)).toMultiplicative
  let q := DiagonalizableGroup.cocharPoints ψ
    ((DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)).symm (zpowersHom Aˣ u))
  have hmap : BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom q =
      diagonalTorusPoints r R A q := by
    rw [BialgHom.mapDomain_apply, diagonalTorusPoints_apply,
      CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  apply Matrix.SpecialLinearGroup.ext
  have hGL : Matrix.SpecialLinearGroup.toGL
      (pointsMulEquiv (R := R) (A := A) (r + 1)
        (Cocharacter.pointsHom A (simpleCorootCocharacter r R i) u)) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2nUnit hne u) := by
    rw [simpleCorootCocharacter, BialgHom.pointsHom_cocharacter, hmap,
      toGL_pointsMulEquiv_diagonalTorusPoints, Matrix.SpecialLinearGroup.toGL_diag2nUnit]
    congr 1; funext a; rw [torusCharacter_diagonalTorusWeight, torusCharacter_def]
    have hcoord (j : Fin r) :
        SplitTorus.pointsMulEquiv q (ULift.up j) = u ^ (if j = i then (1 : ℤ) else 0) := by
      rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv, freeAbelianCharEquiv_apply,
        DiagonalizableGroup.pointsMulEquiv_cocharPoints, MulEquiv.apply_symm_apply,
        zpowersHom_apply, toAdd_ofAdd, zpow_one]
      congr 1
      simp only [ψ, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
        Finsupp.applyAddHom_apply, Finsupp.single_apply, ULift.up.injEq]
    simp_rw [hcoord, ← zpow_mul]
    rw [Finset.prod_eq_single i (fun j _ hji ↦ by simp [hji])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim)]
    simp only [↓reduceIte, one_mul, SlStd.weight_def]
    by_cases h1 : a = i.castSucc
    · subst h1; simp [hne]
    · by_cases h2 : a = i.succ <;> [subst h2; skip] <;> simp [*]
  exact fun a b ↦ congr_fun (congr_fun
    (congrArg (fun g : GL (Fin (r + 1)) A ↦ (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A)) hGL) a) b

/-- Differential of `simpleCorootCocharacter r R i` on tangent vectors of `𝔾ₘ`. -/
@[simp]
theorem tangentMatrix_derivationComp_simpleCorootCocharacter {B : Type v} [CommRing B]
    [Algebra R B] (i : Fin r)
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    tangentMatrix (r + 1) (derivationComp (B := B) (simpleCorootCocharacter r R i) d) =
      LieAlgebra.SpecialLinear.singleSubSingle i.castSucc i.succ
        (MultiplicativeGroup.tangentLinearEquiv d) := by
  have hne : i.castSucc ≠ i.succ := ((Fin.castSucc_lt_succ_iff (a := i) (b := i)).mpr le_rfl).ne
  have hcomp : (diagonalTorusCoordinateMap r R).hom.comp (coordinateMap R (r + 1)).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) (diagonalTorusWeight.{u} r) := by
    simpa only [CommHopfAlgCat.hom_comp, GeneralLinear.hom_weightTorusCoordinateMap] using
      congrArg CommHopfAlgCat.Hom.hom (coordinateMap_comp_diagonalTorusCoordinateMap r R)
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.val_singleSubSingle, tangentMatrix_apply_coe,
    HopfIdeal.quotientLieHom_apply, ← CommHopfAlgCat.hom_mkQuotient, ← coordinateMap,
    simpleCorootCocharacter,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus
      (coordinateMap R (r + 1)).hom (diagonalTorusCoordinateMap r R).hom
      (diagonalTorusWeight.{u} r) hcomp _ d]
  ext a b
  rw [Matrix.diagonal_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte, and_self, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
      toAdd_ofAdd, Finsupp.applyAddHom_apply, Finsupp.coe_equivFunOnFinite_symm,
      diagonalTorusWeight_apply, SlStd.weight_def]
    by_cases h1 : a = i.castSucc
    · subst h1; simp only [↓reduceIte, hne, hne.symm, sub_zero, one_zsmul]
    · by_cases h2 : a = i.succ
      · subst h2; simp only [↓reduceIte, h1, hne, zero_sub, neg_one_zsmul]
      · simp only [↓reduceIte, h1, h2, Ne.symm h1, Ne.symm h2, sub_zero, zero_zsmul]
  · have hno (x) : ¬(x = a ∧ x = b) := fun ⟨ha, hb⟩ ↦ hab (ha.symm.trans hb)
    simp only [hab, hno i.castSucc, hno i.succ, ↓reduceIte, sub_zero]

end SimpleCoroot

end TauCeti.SpecialLinear

namespace IsSl2Triple

universe u w

variable {k : Type u} [Field k] [CharZero k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
variable {h e f : Derivation k H (Bialgebra.CounitAlgebra k H k)}

/-- **The cocharacter `𝔾ₘ ⟶ G` attached to an `sl₂` triple.** -/
noncomputable def cocharacter (t : IsSl2Triple h e f) : H →ₐc[k] LaurentPolynomial k :=
  (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom

/-- Unfolding `t.cocharacter` via `simpleCorootCocharacter 1 k 0` and `t.sl2CoordinateMap`. -/
theorem cocharacter_def (t : IsSl2Triple h e f) :
    t.cocharacter = (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom :=
  (rfl)

/-- Differential of `t.cocharacter` on tangent vectors of `𝔾ₘ`. -/
@[simp]
theorem derivationComp_cocharacter (t : IsSl2Triple h e f)
    (d : Derivation k (LaurentPolynomial k)
      (Bialgebra.CounitAlgebra k (LaurentPolynomial k) k)) :
    derivationComp (B := k) t.cocharacter d = MultiplicativeGroup.tangentLinearEquiv d • h := by
  rw [cocharacter_def, derivationComp_comp, LinearMap.comp_apply, t.derivationComp_sl2CoordinateMap,
    SpecialLinear.tangentLieEquivSl_apply,
    SpecialLinear.tangentMatrix_derivationComp_simpleCorootCocharacter, Fin.castSucc_zero,
    Fin.succ_zero_eq_one]
  have hsingle : SpecialLinear.singleSubSingle (0 : Fin 2) 1
      (MultiplicativeGroup.tangentLinearEquiv d) =
      MultiplicativeGroup.tangentLinearEquiv d • SpecialLinear.singleSubSingle (0 : Fin 2) 1 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (SpecialLinear.singleSubSingle (0 : Fin 2) 1 (R := k)).map_smul
        (MultiplicativeGroup.tangentLinearEquiv d) 1
  rw [hsingle, map_smul, t.toLieHom_singleSubSingle k]

/-- The unit tangent vector of `𝔾ₘ` maps under `t.cocharacter` to `h`. -/
theorem derivationComp_cocharacter_unit (t : IsSl2Triple h e f) :
    derivationComp (B := k) t.cocharacter
        ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1) = h := by
  rw [t.derivationComp_cocharacter, LinearEquiv.apply_symm_apply, one_smul]

/-- **Naturality of `t.cocharacter`** along a morphism of finite-type affine groups. -/
theorem cocharacter_map {H' : Type u} [CommRing H'] [HopfAlgebra k H'] [Algebra.FiniteType k H']
    (t : IsSl2Triple h e f) (ψ : CommHopfAlgCat.of k H' ⟶ CommHopfAlgCat.of k H)
    (hψ : derivationCompLieHom (B := k) ψ.hom h ≠ 0) :
    (t.map (derivationCompLieHom (B := k) ψ.hom) hψ).cocharacter = t.cocharacter.comp ψ.hom := by
  rw [cocharacter_def, t.sl2CoordinateMap_map ψ hψ, CommHopfAlgCat.hom_comp, ← BialgHom.comp_assoc,
    ← cocharacter_def]

/-- **Weight spaces of `t.cocharacter` are `h`-eigenspaces** on every `H`-comodule `V`. -/
theorem weightSpace_cocharacter_eq_eigenspace (t : IsSl2Triple h e f)
    (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V] (m : ℤ) :
    DiagonalizableGroup.weightSpace V
        (((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp
          t.cocharacter).toCoalgHom)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace (Comodule.differential (R := k) (H := H) (M := V) h) (m : k) := by
  let eMult := AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ
  let π : H →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) := eMult.toBialgHom.comp t.cocharacter
  let d₁ := (MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1
  let d₀ := derivationComp (B := k) eMult.symm.toBialgHom d₁
  have hd₀_eval (x : Multiplicative ℤ) :
      Bialgebra.CounitAlgebra.algEquivSelf k (MonoidAlgebra k (Multiplicative ℤ)) k
        (d₀ (MonoidAlgebra.single x 1)) = (x.toAdd : k) := by
    rw [algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single,
      ← LaurentPolynomial.T, MultiplicativeGroup.tangentLinearEquiv_symm_apply_T, zsmul_one]
  have hd₀_inj : Function.Injective fun x : Multiplicative ℤ ↦
      Bialgebra.CounitAlgebra.algEquivSelf k (MonoidAlgebra k (Multiplicative ℤ)) k
        (d₀ (MonoidAlgebra.single x 1)) := fun x y hxy ↦
    Multiplicative.toAdd.injective <|
      Int.cast_inj.mp ((hd₀_eval x).symm.trans (hxy.trans (hd₀_eval y)))
  have hid : eMult.symm.toBialgHom.comp eMult.toBialgHom = BialgHom.id k (LaurentPolynomial k) :=
    BialgHom.ext eMult.symm_apply_apply
  have hπd₀ : derivationComp (B := k) π d₀ = h := by
    have hd₁ : derivationComp (B := k) (eMult.symm.toBialgHom.comp eMult.toBialgHom) d₁ = d₁ := by
      rw [hid]; apply Derivation.ext; intro p; rw [derivationComp_apply]; rfl
    rw [show derivationComp (B := k) π d₀ = derivationComp (B := k) t.cocharacter
      (derivationComp (B := k) (eMult.symm.toBialgHom.comp eMult.toBialgHom) d₁) by
        rw [← LinearMap.comp_apply, ← derivationComp_comp, ← LinearMap.comp_apply,
          ← derivationComp_comp, BialgHom.comp_assoc], hd₁, t.derivationComp_cocharacter_unit]
  rw [DiagonalizableGroup.weightSpace_eq_eigenspace_differential_of_injective V π d₀ hd₀_inj
      (Multiplicative.ofAdd m), hπd₀, hd₀_eval, toAdd_ofAdd]

/-- **Adjoint weight spaces of `t.cocharacter` are `ad h`-eigenspaces.** -/
theorem adjointWeightSpace_cocharacter_eq_eigenspace (t : IsSl2Triple h e f) (m : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp t.cocharacter)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace
        (ad k (Module.Dual k (Bialgebra.CotangentSpace k H))
          ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm h))
        (m : k) := by
  let _ : Comodule k H (Module.Dual k (Bialgebra.CotangentSpace k H)) :=
    Derivation.adjointComodule (R := k) (H := H)
  rw [Derivation.adjointWeightSpace_eq_weightSpace,
    t.weightSpace_cocharacter_eq_eigenspace (Module.Dual k (Bialgebra.CotangentSpace k H)) m]
  congr 1; exact LinearMap.ext fun x ↦ Derivation.differential_adjointComodule h x

private theorem map_cotangentLinearEquiv_adjointWeightSpace (t : IsSl2Triple h e f) (n : ℤ) :
    Submodule.map
        (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) : _ →ₗ[k] _)
        (Derivation.adjointWeightSpace
          ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp t.cocharacter)
          (Multiplicative.ofAdd n)) =
      Module.End.eigenspace
        (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [t.adjointWeightSpace_cocharacter_eq_eigenspace]
  ext d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).surjective d
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    ← Derivation.cotangentDualLieEquiv_apply, Module.End.mem_eigenspace_iff,
    Module.End.mem_eigenspace_iff, ad_apply, ad_apply]
  simp only [← (Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective.eq_iff,
    LieEquiv.coe_toLieHom, LieEquiv.map_lie, LieEquiv.apply_symm_apply]
  rw [Derivation.cotangentDualLieEquiv_apply, map_smul, ← Derivation.cotangentDualLieEquiv_apply]
  exact Iff.rfl

/-- **The Lie algebra of the parabolic `P_G(t.cocharacter)` is `⨁_{n ≥ 0} 𝔤(n)`.** -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    ((parabolicDefiningHopfIdeal t.cocharacter).lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 ≤ n),
        Module.End.eigenspace
          (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule, Submodule.map_iSup]
  refine iSup_congr fun n ↦ ?_
  rw [Submodule.map_iSup]
  exact iSup_congr fun _ ↦ t.map_cotangentLinearEquiv_adjointWeightSpace n

/-- **The Lie algebra of the Jacobson–Morozov unipotent subgroup `U_G(t.cocharacter)` is
`⨁_{n > 0} 𝔤(n)`.** -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    (t.cocharacter.unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 < n),
        Module.End.eigenspace
          (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule, Submodule.map_iSup]
  refine iSup_congr fun n ↦ ?_
  rw [Submodule.map_iSup]
  exact iSup_congr fun _ ↦ t.map_cotangentLinearEquiv_adjointWeightSpace n

end IsSl2Triple
