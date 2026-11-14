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

For a Bourbaki node `i : Fin r` of `SL_{r+1}` over any commutative ring `R`, restricting the
`i`-th coordinate cocharacter of its diagonal torus defines the simple-coroot cocharacter

```text
TauCeti.SpecialLinear.simpleCorootCocharacter r R i : O(SL_{r+1}) →ₐc[R] R[T;T⁻¹].
```

On `A`-points it sends `u : Aˣ` to `Matrix.SpecialLinearGroup.diag2nUnit _ u` (`diag(u, u⁻¹)` in
positions `(i, i + 1)`), and its differential sends the tangent parameter `c` of `𝔾ₘ` to
`LieAlgebra.SpecialLinear.singleSubSingle i.castSucc i.succ c`.

Specializing to `r = 1, i = 0` gives the standard coroot `u ↦ diag(u, u⁻¹)` of `SL₂`, whose unit
tangent vector maps to `H = E₀₀ - E₁₁`. Composing it with `IsSl2Triple.sl2CoordinateMap` attaches a
cocharacter

```text
IsSl2Triple.cocharacter : H →ₐc[k] k[T;T⁻¹]
```

to any `sl₂` triple `t : IsSl2Triple h e f` in the Lie algebra of a finite-type affine group `G`
over a field `k` of characteristic zero. Its unit tangent differential is `h`. Because `k` has
characteristic zero, the unit tangent vector of `𝔾ₘ` separates characters of `Multiplicative ℤ`, so
for every rational representation `V` of `G` (including infinite-dimensional ones) the `m`-weight
space of `t.cocharacter` equals the `(m : k)`-eigenspace of `h`
(`IsSl2Triple.weightSpace_cocharacter_eq_eigenspace`). In the adjoint representation this identifies
the `m`-th adjoint weight space with `𝔤(m) = ker(ad h - m)`, and pins the Lie algebras of the
dynamic parabolic `P_G(t.cocharacter)` and unipotent subgroup `U_G(t.cocharacter)` to
`⨁_{n ≥ 0} 𝔤(n)` and `⨁_{n > 0} 𝔤(n)`.

## Main declarations

* `TauCeti.SpecialLinear.simpleCorootCocharacter`: the `i`-th simple-coroot cocharacter of
  `SL_{r+1}` over any commutative ring, with point formula
  `TauCeti.SpecialLinear.pointsMulEquiv_pointsHom_simpleCorootCocharacter` and differential
  `TauCeti.SpecialLinear.tangentMatrix_derivationComp_simpleCorootCocharacter`.
* `IsSl2Triple.cocharacter`: the cocharacter `𝔾ₘ ⟶ SL₂ ⟶ G` of an `sl₂` triple.
* `IsSl2Triple.derivationComp_cocharacter` and `IsSl2Triple.derivationComp_cocharacter_unit`: its
  differential sends the unit tangent vector of `𝔾ₘ` to `h`.
* `IsSl2Triple.weightSpace_cocharacter_eq_eigenspace`: on every `H`-comodule, the `m`-weight space
  of `t.cocharacter` equals the `(m : k)`-eigenspace of `h`.
* `IsSl2Triple.adjointWeightSpace_cocharacter_eq_eigenspace`,
  `IsSl2Triple.lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter`, and
  `IsSl2Triple.lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter`: adjoint weight spaces and the
  tangent Lie algebras of the Jacobson–Morozov parabolic and unipotent subgroups.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, Springer, 1991, §7.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed., Cambridge University Press,
  2015, §2.1.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.3 and §3.8.
* J. E. Humphreys, *Conjugacy Classes in Semisimple Algebraic Groups*, AMS, 1995, §8.4.
-/

public section

open CategoryTheory LieAlgebra TauCeti TauCeti.Cocharacter WithConv
open scoped LaurentPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SpecialLinear

universe u v

section SimpleCoroot

variable (r : ℕ) (R : Type u) [CommRing R]

/-- **The `i`-th simple-coroot cocharacter of `SL_{r+1}`**, defined by restricting the `i`-th
coordinate cocharacter of the diagonal torus `diagonalTorusCoordinateMap r R`. For `r = 1, i = 0`
this is the standard coroot `u ↦ diag(u, u⁻¹)` of `SL₂`. -/
noncomputable def simpleCorootCocharacter (i : Fin r) :
    coordinateHopfAlgebra R (r + 1) →ₐc[R] LaurentPolynomial R :=
  (diagonalTorusCoordinateMap r R).hom.cocharacter
    (Finsupp.applyAddHom (ULift.up i)).toMultiplicative

variable {r R}

/-- On `A`-points, the `i`-th simple-coroot cocharacter sends a unit `u` to the two-coordinate
diagonal matrix `diag2nUnit _ u` with `u` at `i.castSucc` and `u⁻¹` at `i.succ`. -/
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
      Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2nUnit hne u) := by
    rw [simpleCorootCocharacter, BialgHom.pointsHom_cocharacter, hmap,
      toGL_pointsMulEquiv_diagonalTorusPoints, Matrix.SpecialLinearGroup.toGL_diag2nUnit]
    congr 1
    funext a
    rw [torusCharacter_diagonalTorusWeight, torusCharacter_def]
    have hcoord (j : Fin r) :
        SplitTorus.pointsMulEquiv q (ULift.up j) = u ^ (if j = i then (1 : ℤ) else 0) := by
      rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv, freeAbelianCharEquiv_apply,
        DiagonalizableGroup.pointsMulEquiv_cocharPoints, MulEquiv.apply_symm_apply,
        zpowersHom_apply, toAdd_ofAdd, zpow_one]
      congr 1
      simp only [ψ, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
        Finsupp.applyAddHom_apply, Finsupp.single_apply, ULift.up.injEq]
    simp_rw [hcoord, ← zpow_mul]
    rw [Finset.prod_eq_single i
      (fun j _ hji ↦ by simp [hji])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim)]
    simp only [↓reduceIte, one_mul, SlStd.weight_def]
    by_cases h1 : a = i.castSucc
    · subst h1
      simp [hne]
    · by_cases h2 : a = i.succ
      · subst h2
        simp [h1]
      · simp [h1, h2]
  have hmat := congrArg (fun g : GL (Fin (r + 1)) A ↦ (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A))
    hGL
  exact fun a b ↦ congr_fun (congr_fun hmat a) b

/-- The differential of `simpleCorootCocharacter r R i` sends a tangent vector `d` of `𝔾ₘ` to
`LieAlgebra.SpecialLinear.singleSubSingle i.castSucc i.succ` scaled by
`MultiplicativeGroup.tangentLinearEquiv d`. -/
@[simp]
theorem tangentMatrix_derivationComp_simpleCorootCocharacter {B : Type v} [CommRing B]
    [Algebra R B] (i : Fin r)
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    tangentMatrix (r + 1)
        (derivationComp (B := B) (simpleCorootCocharacter r R i) d) =
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
    · subst h1
      simp only [↓reduceIte, hne, hne.symm, sub_zero, one_zsmul]
    · by_cases h2 : a = i.succ
      · subst h2
        simp only [↓reduceIte, h1, hne, zero_sub, neg_one_zsmul]
      · simp only [↓reduceIte, h1, h2, Ne.symm h1, Ne.symm h2, sub_zero, zero_zsmul]
  · have h1 : ¬(i.castSucc = a ∧ i.castSucc = b) := fun ⟨ha, hb⟩ ↦ hab (ha.symm.trans hb)
    have h2 : ¬(i.succ = a ∧ i.succ = b) := fun ⟨ha, hb⟩ ↦ hab (ha.symm.trans hb)
    simp only [hab, h1, h2, ↓reduceIte, sub_zero]

end SimpleCoroot

end TauCeti.SpecialLinear

namespace IsSl2Triple

universe u w

variable {k : Type u} [Field k] [CharZero k]
variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
variable {h e f : Derivation k H (Bialgebra.CounitAlgebra k H k)}

/-- **The cocharacter `𝔾ₘ ⟶ G` attached to an `sl₂` triple**, obtained by composing the standard
coroot `u ↦ diag(u, u⁻¹)` of `SL₂` with `t.sl2CoordinateMap`. -/
noncomputable def cocharacter (t : IsSl2Triple h e f) : H →ₐc[k] LaurentPolynomial k :=
  (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom

/-- `t.cocharacter` is the composite of `SpecialLinear.simpleCorootCocharacter 1 k 0` with
`t.sl2CoordinateMap`. -/
theorem cocharacter_def (t : IsSl2Triple h e f) :
    t.cocharacter = (SpecialLinear.simpleCorootCocharacter 1 k 0).comp t.sl2CoordinateMap.hom :=
  (rfl)

/-- The differential of `t.cocharacter` sends a tangent vector `d` of `𝔾ₘ` to
`MultiplicativeGroup.tangentLinearEquiv d • h`. -/
@[simp]
theorem derivationComp_cocharacter (t : IsSl2Triple h e f)
    (d : Derivation k (LaurentPolynomial k)
      (Bialgebra.CounitAlgebra k (LaurentPolynomial k) k)) :
    derivationComp (B := k) t.cocharacter d =
      MultiplicativeGroup.tangentLinearEquiv d • h := by
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

/-- The unit tangent vector of `𝔾ₘ` maps under the differential of `t.cocharacter` to the neutral
element `h` of the triple. -/
theorem derivationComp_cocharacter_unit (t : IsSl2Triple h e f) :
    derivationComp (B := k) t.cocharacter
        ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1) = h := by
  rw [t.derivationComp_cocharacter, LinearEquiv.apply_symm_apply, one_smul]

/-- **Naturality of the cocharacter** along a morphism of finite-type affine groups. -/
theorem cocharacter_map {H' : Type u} [CommRing H'] [HopfAlgebra k H'] [Algebra.FiniteType k H']
    (t : IsSl2Triple h e f) (ψ : CommHopfAlgCat.of k H' ⟶ CommHopfAlgCat.of k H)
    (hψ : derivationCompLieHom (B := k) ψ.hom h ≠ 0) :
    (t.map (derivationCompLieHom (B := k) ψ.hom) hψ).cocharacter =
      t.cocharacter.comp ψ.hom := by
  rw [cocharacter_def, t.sl2CoordinateMap_map ψ hψ, CommHopfAlgCat.hom_comp, ← BialgHom.comp_assoc,
    ← cocharacter_def]

/-- **Weight spaces of `t.cocharacter` are `h`-eigenspaces.** For every `H`-comodule `V` (of any
dimension), the `m`-weight space of `t.cocharacter` equals the `(m : k)`-eigenspace of the
differentiated action of `h`. -/
theorem weightSpace_cocharacter_eq_eigenspace (t : IsSl2Triple h e f)
    (V : Type w) [AddCommGroup V] [Module k V] [Comodule k H V] (m : ℤ) :
    DiagonalizableGroup.weightSpace V
        (((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp
          t.cocharacter).toCoalgHom)
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace (Comodule.differential (R := k) (H := H) (M := V) h) (m : k) := by
  let eMult := AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ
  let π : H →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) := eMult.toBialgHom.comp t.cocharacter
  let d₁ : Derivation k (LaurentPolynomial k)
      (Bialgebra.CounitAlgebra k (LaurentPolynomial k) k) :=
    (MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1
  let d₀ : Derivation k (MonoidAlgebra k (Multiplicative ℤ))
      (Bialgebra.CounitAlgebra k (MonoidAlgebra k (Multiplicative ℤ)) k) :=
    derivationComp (B := k) eMult.symm.toBialgHom d₁
  have hd₀_eval (x : Multiplicative ℤ) :
      Bialgebra.CounitAlgebra.algEquivSelf k (MonoidAlgebra k (Multiplicative ℤ)) k
        (d₀ (MonoidAlgebra.single x 1)) = (x.toAdd : k) := by
    rw [algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, AddMonoidAlgebra.toMultiplicativeBialgEquiv_symm_single,
      ← LaurentPolynomial.T, MultiplicativeGroup.tangentLinearEquiv_symm_apply_T, zsmul_one]
  have hd₀_inj : Function.Injective fun x : Multiplicative ℤ ↦
      Bialgebra.CounitAlgebra.algEquivSelf k (MonoidAlgebra k (Multiplicative ℤ)) k
        (d₀ (MonoidAlgebra.single x 1)) := by
    intro x y hxy
    dsimp only at hxy
    rw [hd₀_eval, hd₀_eval, Int.cast_inj] at hxy
    exact Multiplicative.toAdd.injective hxy
  have hπd₀ : derivationComp (B := k) π d₀ = h := by
    have hid : eMult.symm.toBialgHom.comp eMult.toBialgHom =
        BialgHom.id k (LaurentPolynomial k) := by
      apply BialgHom.ext
      intro p
      exact eMult.symm_apply_apply p
    have hd₁ : derivationComp (B := k) (eMult.symm.toBialgHom.comp eMult.toBialgHom) d₁ = d₁ := by
      rw [hid]
      apply Derivation.ext
      intro p
      rw [derivationComp_apply]
      rfl
    calc
      derivationComp (B := k) π d₀ =
          derivationComp (B := k) t.cocharacter
            (derivationComp (B := k) (eMult.symm.toBialgHom.comp eMult.toBialgHom) d₁) := by
        rw [← LinearMap.comp_apply, ← derivationComp_comp, ← LinearMap.comp_apply,
          ← derivationComp_comp, BialgHom.comp_assoc]
      _ = h := by rw [hd₁, t.derivationComp_cocharacter_unit]
  rw [DiagonalizableGroup.weightSpace_eq_eigenspace_differential_of_injective V π d₀ hd₀_inj
      (Multiplicative.ofAdd m),
    hπd₀, hd₀_eval, toAdd_ofAdd]

/-- **Adjoint weight spaces of `t.cocharacter` are `ad h`-eigenspaces.** In the cotangent-dual
model of `Lie(G)`, the `m`-th adjoint weight space of `t.cocharacter` is the `(m : k)`-eigenspace
of `ad ((cotangentDualLieEquiv).symm h)`. -/
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
  congr 1
  apply LinearMap.ext
  intro x
  rw [ad_apply]
  exact Derivation.differential_adjointComodule h x

/-- **The Lie algebra of the Jacobson–Morozov dynamic parabolic `P_G(t.cocharacter)`** is the sum
`⨁_{n ≥ 0} 𝔤(n)` of the nonnegative integer eigenspaces of `ad h`. -/
theorem lieSubalgebra_parabolicDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    ((parabolicDefiningHopfIdeal t.cocharacter).lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 ≤ n),
        Module.End.eigenspace
          (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_toSubmodule]
  simp_rw [t.adjointWeightSpace_cocharacter_eq_eigenspace]
  rw [Submodule.map_iSup]
  refine iSup_congr fun n ↦ ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ ↦ ?_
  ext d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).surjective d
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    ← Derivation.cotangentDualLieEquiv_apply, Module.End.mem_eigenspace_iff,
    Module.End.mem_eigenspace_iff, ad_apply, ad_apply]
  simp only [← (Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective.eq_iff,
    LieEquiv.coe_toLieHom, LieEquiv.map_lie, LieEquiv.apply_symm_apply]
  rw [Derivation.cotangentDualLieEquiv_apply, map_smul, ← Derivation.cotangentDualLieEquiv_apply]
  exact Iff.rfl

/-- **The Lie algebra of the Jacobson–Morozov dynamic unipotent subgroup `U_G(t.cocharacter)`** is
the sum `⨁_{n > 0} 𝔤(n)` of the strictly positive integer eigenspaces of `ad h`. -/
theorem lieSubalgebra_unipotentDefiningHopfIdeal_cocharacter (t : IsSl2Triple h e f) :
    (t.cocharacter.unipotentDefiningHopfIdeal.lieSubalgebra (B := k)).toSubmodule =
      ⨆ (n : ℤ) (_ : 0 < n),
        Module.End.eigenspace
          (ad k (Derivation k H (Bialgebra.CounitAlgebra k H k)) h) (n : k) := by
  rw [BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_toSubmodule]
  simp_rw [t.adjointWeightSpace_cocharacter_eq_eigenspace]
  rw [Submodule.map_iSup]
  refine iSup_congr fun n ↦ ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ ↦ ?_
  ext d
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).surjective d
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    ← Derivation.cotangentDualLieEquiv_apply, Module.End.mem_eigenspace_iff,
    Module.End.mem_eigenspace_iff, ad_apply, ad_apply]
  simp only [← (Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective.eq_iff,
    LieEquiv.coe_toLieHom, LieEquiv.map_lie, LieEquiv.apply_symm_apply]
  rw [Derivation.cotangentDualLieEquiv_apply, map_smul, ← Derivation.cotangentDualLieEquiv_apply]
  exact Iff.rfl

end IsSl2Triple
