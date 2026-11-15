/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Eigenspace
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Integration
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.BasePoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Eigenspace
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Cocharacter
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Differential
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.GradeTwoOrbit

/-!
# Algebraic `SL₂` homomorphisms, cocharacter gradings, and parabolics of `sl₂`-triples

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` of
characteristic zero, with Lie algebra `𝔤 = Module.Dual k (Bialgebra.CotangentSpace k H)`, and let
`(h, e, f)` be an `sl₂`-triple in `𝔤`.

1. **Integrating `(h, e, f)` to `SL₂ → G`.** An `sl₂`-triple in any Lie algebra determines a
   canonical Lie algebra homomorphism `sl(2, k) →ₗ⁅k⁆ L` sending the standard basis `(E₀₁, E₁₀, H)`
   to `(e, f, h)` (`IsSl2Triple.slFinTwoLieHom`), which is injective over a torsion-free module in
   characteristic zero (`IsSl2Triple.slFinTwoLieHom_injective`). Integrating this homomorphism via
   `TauCeti.SpecialLinear.integrateLieHom` produces a unique coordinate morphism
   `t.sl2CoordinateMap H : H →ₐc[k] O(SL₂)` (`SL₂ → G`) whose differential sends `(E₀₁, E₁₀, H)` to
   `(e, f, h)` and whose scheme-theoretic kernel is central in `SL₂` (hence contained in `{±I}`).
   Composing with the upper and lower root subgroups `𝔾ₐ → SL₂` and with the diagonal coroot
   `c ↦ diag(c, c⁻¹)` gives root subgroups `t.upperRootSubgroup H`, `t.lowerRootSubgroup H` with
   differentials `e` and `f`, and a cocharacter `t.cocharacter H : H →ₐc[k] k[T;T⁻¹]` with unit
   differential `h` whose value at `-1` is the image of `-I ∈ SL₂`.

2. **Adjoint eigenspace grading and the dynamic subgroups `P(h)`, `U(h)`, and `L(h)`.** Combining
   `t.cocharacter H` with the characteristic-zero cocharacter theory in
   `TauCeti.Algebra.AlgebraicGroup.Dynamic.Tangent.Eigenspace` identifies the `m`-weight space of
   `t.cocharacter H` on `𝔤` with `𝔤(m) = ker(ad h - m)`
   (`IsSl2Triple.adjointWeightSpace_cocharacter`).
   Consequently, the dynamic parabolic `P(h)` has Lie algebra `⨁_{n ≥ 0} 𝔤(n)` (containing `h` and
   `e`), its dynamic unipotent subgroup `U(h)` is geometrically connected with Lie algebra
   `⨁_{n > 0} 𝔤(n)` (containing `e`), and its dynamic Levi `L(h)` equals `C_G(h)` (with Lie algebra
   `𝔤(0) = ker(ad h)`, so `L(h)(k)` conjugates any two `sl₂`-triples sharing `h`). All
   constructions are equivariant under conjugation by `G(k)`.

## Main declarations

* `IsSl2Triple.slFinTwoLieHom` and `IsSl2Triple.slFinTwoLieHom_injective`: the canonical
  homomorphism `sl(2, R) →ₗ⁅R⁆ L` of an `sl₂`-triple and its injectivity.
* `IsSl2Triple.sl2CoordinateMap`, `IsSl2Triple.upperRootSubgroup`, `IsSl2Triple.lowerRootSubgroup`,
  and `IsSl2Triple.cocharacter`: the algebraic `SL₂` homomorphism, additive root subgroups, and
  associated cocharacter of an `sl₂`-triple in `Lie(G)`.
* `IsSl2Triple.parabolicHopfIdeal`, `IsSl2Triple.unipotentHopfIdeal`, and
  `IsSl2Triple.leviHopfIdeal`: the dynamic parabolic `P(h)`, geometrically connected unipotent
  subgroup `U(h)`, and Levi `L(h) = C_G(h)`, together with their Lie algebras, shared-`h`
  conjugacy, and `G(k)`-conjugation equivariance.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §3–§4.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §3.2–§3.4 and §3.7.
* J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Progress in Mathematics **228**
  (2004), §5.1–§5.5.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
-/

public section

open CategoryTheory TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct

universe u

namespace IsSl2Triple

section LieHom

variable (R : Type*) [CommRing R] {L : Type*} [LieRing L] [LieAlgebra R L] {h e f : L}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **The canonical Lie algebra homomorphism `sl(2, R) →ₗ⁅R⁆ L` associated to an `sl₂`-triple**,
sending the standard basis `(E₀₁, E₁₀, E₀₀ - E₁₁)` to `(e, f, h)`. -/
noncomputable def slFinTwoLieHom (t : IsSl2Triple h e f) :
    LieAlgebra.SpecialLinear.sl (Fin 2) R →ₗ⁅R⁆ L :=
  lieHomOfSl2Basis (slFinTwoBasis R) (lie_slFinTwoBasis_zero_one R)
    (lie_slFinTwoBasis_two_zero R) (lie_slFinTwoBasis_two_one R) e f h
    t.lie_e_f (t.lie_h_e_smul R) (by rw [t.lie_lie_smul_f R])

variable {R}

@[simp]
theorem slFinTwoLieHom_single_zero_one (t : IsSl2Triple h e f) :
    t.slFinTwoLieHom R (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1) = e := by
  rw [← slFinTwoBasis_zero R, slFinTwoLieHom, lieHomOfSl2Basis_apply]
  rfl

@[simp]
theorem slFinTwoLieHom_single_one_zero (t : IsSl2Triple h e f) :
    t.slFinTwoLieHom R (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1) = f := by
  rw [← slFinTwoBasis_one R, slFinTwoLieHom, lieHomOfSl2Basis_apply]
  rfl

@[simp]
theorem slFinTwoLieHom_singleSubSingle (t : IsSl2Triple h e f) :
    t.slFinTwoLieHom R (LieAlgebra.SpecialLinear.singleSubSingle 0 1 1) = h := by
  rw [← slFinTwoBasis_two R, slFinTwoLieHom, lieHomOfSl2Basis_apply]
  rfl

/-- A Lie homomorphism `φ : sl(2, R) →ₗ⁅R⁆ L` equals `t.slFinTwoLieHom R` if and only if it maps
`E₀₁ ↦ e` and `E₁₀ ↦ f`. -/
theorem eq_slFinTwoLieHom_iff (t : IsSl2Triple h e f)
    (φ : LieAlgebra.SpecialLinear.sl (Fin 2) R →ₗ⁅R⁆ L) :
    φ = t.slFinTwoLieHom R ↔
      φ (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1) = e ∧
        φ (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1) = f := by
  refine ⟨fun hφ ↦ ⟨hφ ▸ t.slFinTwoLieHom_single_zero_one,
    hφ ▸ t.slFinTwoLieHom_single_one_zero⟩, fun ⟨he, hf⟩ ↦ ?_⟩
  exact lieHom_ext_slFinTwo (he.trans t.slFinTwoLieHom_single_zero_one.symm)
    (hf.trans t.slFinTwoLieHom_single_one_zero.symm)

/-- Over an integral domain `R` with `2 ≠ 0` and a torsion-free `R`-Lie algebra `L`,
`t.slFinTwoLieHom R` is injective. -/
theorem slFinTwoLieHom_injective [IsDomain R] [NeZero (2 : R)]
    [Module.IsTorsionFree R L] (t : IsSl2Triple h e f) :
    Function.Injective (t.slFinTwoLieHom R) := by
  rw [← LieHom.coe_toLinearMap, ← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, ← (slFinTwoBasis R).sum_repr x, map_sum] at hx
  have hsum : ∑ i, (slFinTwoBasis R).repr x i • (![e, f, h] i) = 0 := by
    simpa [Fin.sum_univ_three] using hx
  have hzero := Fintype.linearIndependent_iff.mp (linearIndependent_isSl2Triple t)
    ((slFinTwoBasis R).repr x) hsum
  rw [← (slFinTwoBasis R).sum_repr x]
  simp [hzero]

end LieHom

section AlgebraicGroup

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable (H : Type u) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
variable {h e f e' f' : Module.Dual k (Bialgebra.CotangentSpace k H)}

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial
attribute [local instance 100] LieRing.ofAssociativeRing

/-- **The algebraic `SL₂` homomorphism integrating an `sl₂`-triple `(h, e, f)` in `Lie(Spec H)`**,
given contravariantly by its coordinate bialgebra morphism `H →ₐc[k] O(SL₂)`. -/
noncomputable def sl2CoordinateMap (t : IsSl2Triple h e f) :
    H →ₐc[k] SpecialLinear.coordinateHopfAlgebra k 2 :=
  SpecialLinear.integrateLieHom
    ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom.comp (t.slFinTwoLieHom k))

variable {H}

/-- Evaluating the differential of `t.sl2CoordinateMap H` on `(tangentLieEquivSl 2).symm X` gives
the image of `X` under `t.slFinTwoLieHom k` in `Lie(Spec H)`. -/
@[simp]
theorem derivationComp_sl2CoordinateMap_symm (t : IsSl2Triple h e f)
    (X : LieAlgebra.SpecialLinear.sl (Fin 2) k) :
    derivationComp (t.sl2CoordinateMap H)
        ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm X) =
      Derivation.cotangentDualLieEquiv (R := k) (H := H) (t.slFinTwoLieHom k X) := by
  rw [sl2CoordinateMap, SpecialLinear.derivationComp_integrateLieHom_symm, LieHom.comp_apply,
    LieEquiv.coe_toLieHom]

/-- A coordinate morphism `φ : H →ₐc[k] O(SL₂)` equals `t.sl2CoordinateMap H` if and only if its
differential sends `E₀₁ ↦ e` and `E₁₀ ↦ f`. -/
theorem eq_sl2CoordinateMap_iff (t : IsSl2Triple h e f)
    (φ : H →ₐc[k] SpecialLinear.coordinateHopfAlgebra k 2) :
    φ = t.sl2CoordinateMap H ↔
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
          (derivationComp φ ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
            (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1))) = e ∧
        (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
          (derivationComp φ ((SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
            (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1))) = f := by
  rw [sl2CoordinateMap, SpecialLinear.eq_integrateLieHom_iff]
  let ψ : LieAlgebra.SpecialLinear.sl (Fin 2) k →ₗ⁅k⁆
      Module.Dual k (Bialgebra.CotangentSpace k H) :=
    (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm.toLieHom.comp
      ((derivationCompLieHom (B := k) φ).comp
        (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm.toLieHom)
  have hiff :
      (derivationCompLieHom (B := k) φ =
          ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).toLieHom.comp
            (t.slFinTwoLieHom k)).comp
            (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).toLieHom) ↔
        ψ = t.slFinTwoLieHom k := by
    constructor
    · intro hφ
      apply LieHom.ext
      intro X
      simp [ψ, hφ]
    · intro hψ
      apply LieHom.ext
      intro d
      have hd := congrArg (Derivation.cotangentDualLieEquiv (R := k) (H := H))
        (DFunLike.congr_fun hψ (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2 d))
      simp only [ψ, LieHom.comp_apply, LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply,
        LieEquiv.apply_symm_apply, derivationCompLieHom_apply] at hd ⊢
      exact hd
  rw [hiff, t.eq_slFinTwoLieHom_iff]
  simp only [ψ, LieHom.comp_apply, LieEquiv.coe_toLieHom, derivationCompLieHom_apply]

/-- The scheme-theoretic kernel of `t.sl2CoordinateMap H` is central in `SL₂`. -/
theorem isCentral_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    (CommHopfAlgCat.kernelHopfIdeal
      (_root_.CommHopfAlgCat.ofHom (t.sl2CoordinateMap H))).IsCentral :=
  SpecialLinear.isCentral_kernelHopfIdeal_integrateLieHom
    ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective.comp t.slFinTwoLieHom_injective)

/-- The scheme-theoretic kernel of `t.sl2CoordinateMap H` is contained in `Z(SL₂) = μ₂`. -/
theorem centerDefiningIdeal_le_kernelHopfIdeal_sl2CoordinateMap (t : IsSl2Triple h e f) :
    CommHopfAlgCat.centerDefiningIdeal
        (_root_.CommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2)) ≤
      CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom (t.sl2CoordinateMap H)) :=
  SpecialLinear.centerDefiningIdeal_le_kernelHopfIdeal_integrateLieHom
    ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective.comp t.slFinTwoLieHom_injective)

/-- Over any integral domain `A` over `k`, every `A`-point in the kernel of `t.sl2CoordinateMap H`
is `1` or `-1` in `SL(2, A)`. -/
theorem pointsMulEquiv_eq_one_or_neg_one_of_mem_kernel_sl2CoordinateMap
    (t : IsSl2Triple h e f) {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
    (g : WithConv (SpecialLinear.coordinateHopfAlgebra k 2 →ₐ[k] A))
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k (SpecialLinear.coordinateHopfAlgebra k 2))
      (CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom (t.sl2CoordinateMap H)))
      (CommAlgCat.of k A)) :
    SpecialLinear.pointsMulEquiv (R := k) (A := A) 2 g = 1 ∨
      SpecialLinear.pointsMulEquiv (R := k) (A := A) 2 g = -1 :=
  SpecialLinear.pointsMulEquiv_eq_one_or_neg_one_of_mem_kernel_integrateLieHom
    ((Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective.comp t.slFinTwoLieHom_injective)
    g hg

/-! ### Additive root subgroups and associated cocharacter of `(h, e, f)` -/

variable (H) in
/-- The upper root subgroup `𝔾ₐ → SL₂ → G` integrating `e`. -/
noncomputable def upperRootSubgroup (t : IsSl2Triple h e f) :
    H →ₐc[k] AdditiveGroup.coordinateHopfAlgebra k :=
  (SpecialLinear.rootSubgroupCoordinateMap (R := k) (N := 2)
    (zero_ne_one : (0 : Fin 2) ≠ 1)).hom.comp (t.sl2CoordinateMap H)

variable (H) in
/-- The lower root subgroup `𝔾ₐ → SL₂ → G` integrating `f`. -/
noncomputable def lowerRootSubgroup (t : IsSl2Triple h e f) :
    H →ₐc[k] AdditiveGroup.coordinateHopfAlgebra k :=
  (SpecialLinear.rootSubgroupCoordinateMap (R := k) (N := 2)
    (one_ne_zero : (1 : Fin 2) ≠ 0)).hom.comp (t.sl2CoordinateMap H)

/-- The unit tangent vector of `t.upperRootSubgroup H` differentiates to `e`. -/
theorem cotangentDualLieEquiv_symm_derivationComp_upperRootSubgroup (t : IsSl2Triple h e f) :
    (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
        (derivationComp (B := k) (t.upperRootSubgroup H)
          ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1)) = e := by
  have hd :
      derivationComp (B := k)
          (SpecialLinear.rootSubgroupCoordinateMap (R := k) (N := 2)
            (zero_ne_one : (0 : Fin 2) ≠ 1)).hom
          ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1) =
        (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
          (LieAlgebra.SpecialLinear.single 0 1 zero_ne_one 1) := by
    apply (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).injective
    rw [LieEquiv.coe_toLieHom, SpecialLinear.tangentLieEquivSl_apply, LieEquiv.apply_symm_apply,
      SpecialLinear.tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply]
  rw [upperRootSubgroup, derivationComp_comp, LinearMap.comp_apply, hd,
    derivationComp_sl2CoordinateMap_symm, LieEquiv.symm_apply_apply,
    slFinTwoLieHom_single_zero_one]

/-- The unit tangent vector of `t.lowerRootSubgroup H` differentiates to `f`. -/
theorem cotangentDualLieEquiv_symm_derivationComp_lowerRootSubgroup (t : IsSl2Triple h e f) :
    (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
        (derivationComp (B := k) (t.lowerRootSubgroup H)
          ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1)) = f := by
  have hd :
      derivationComp (B := k)
          (SpecialLinear.rootSubgroupCoordinateMap (R := k) (N := 2)
            (one_ne_zero : (1 : Fin 2) ≠ 0)).hom
          ((AdditiveGroup.gaTangentLinearEquiv (R := k) (B := k)).symm 1) =
        (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).symm
          (LieAlgebra.SpecialLinear.single 1 0 one_ne_zero 1) := by
    apply (SpecialLinear.tangentLieEquivSl (R := k) (B := k) 2).injective
    rw [LieEquiv.coe_toLieHom, SpecialLinear.tangentLieEquivSl_apply, LieEquiv.apply_symm_apply,
      SpecialLinear.tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply]
  rw [lowerRootSubgroup, derivationComp_comp, LinearMap.comp_apply, hd,
    derivationComp_sl2CoordinateMap_symm, LieEquiv.symm_apply_apply,
    slFinTwoLieHom_single_one_zero]

variable (H) in
/-- **The cocharacter `𝔾ₘ → SL₂ → G` associated to an `sl₂`-triple `(h, e, f)`**, obtained by
composing `t.sl2CoordinateMap H` with the coroot `c ↦ diag(c, c⁻¹)` of `SL₂`. -/
noncomputable def cocharacter (t : IsSl2Triple h e f) : H →ₐc[k] LaurentPolynomial k :=
  (SpecialLinear.diag2nCocharacter k (zero_ne_one : (0 : Fin 2) ≠ 1)).comp (t.sl2CoordinateMap H)

/-- The unit tangent vector of `t.cocharacter H` differentiates to `h`. -/
@[simp]
theorem derivationComp_cocharacter_unit (t : IsSl2Triple h e f) :
    derivationComp (B := k) (t.cocharacter H)
        ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1) =
      Derivation.cotangentDualLieEquiv (R := k) (H := H) h := by
  rw [cocharacter, derivationComp_comp, LinearMap.comp_apply,
    SpecialLinear.derivationComp_diag2nCocharacter_unit,
    derivationComp_sl2CoordinateMap_symm, slFinTwoLieHom_singleSubSingle]

theorem cotangentDualLieEquiv_symm_derivationComp_cocharacter_unit (t : IsSl2Triple h e f) :
    (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
        (derivationComp (B := k) (t.cocharacter H)
          ((MultiplicativeGroup.tangentLinearEquiv (R := k) (B := k)).symm 1)) = h := by
  rw [derivationComp_cocharacter_unit, LieEquiv.symm_apply_apply]

/-- Evaluating `t.cocharacter H` at `-1` gives the image under `SL₂ → G` of `-I ∈ SL₂(A)`. -/
theorem pointsHom_cocharacter_neg_one (t : IsSl2Triple h e f)
    (A : Type*) [CommRing A] [Algebra k A] :
    Cocharacter.pointsHom A (t.cocharacter H) (-1 : Aˣ) =
      BialgHom.mapDomain (t.sl2CoordinateMap H)
        ((SpecialLinear.pointsMulEquiv (R := k) (A := A) 2).symm (-1)) := by
  rw [cocharacter, Cocharacter.pointsHom_apply, BialgHom.mapDomain_comp, MonoidHom.comp_apply,
    ← Cocharacter.pointsHom_apply]
  congr 1
  apply (SpecialLinear.pointsMulEquiv (R := k) (A := A) 2).injective
  simpa using SpecialLinear.pointsMulEquiv_pointsHom_diag2nCocharacter_neg_one (R := k) (A := A)

/-- The `m`-weight space of `t.cocharacter H` on `Lie(Spec H)` is the `(m : k)`-eigenspace of
`ad h`. -/
theorem adjointWeightSpace_cocharacter (t : IsSl2Triple h e f) (m : ℤ) :
    Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp (t.cocharacter H))
        (Multiplicative.ofAdd m) =
      Module.End.eigenspace
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) h) (m : k) := by
  rw [BialgHom.adjointWeightSpace_eq_eigenspace_ad,
    t.cotangentDualLieEquiv_symm_derivationComp_cocharacter_unit]

/-! ### Dynamic parabolic `P(h)`, unipotent subgroup `U(h)`, and Levi `L(h)` -/

variable (H)

/-- The defining Hopf ideal of the dynamic parabolic subgroup `P(h)` associated to `t`. -/
noncomputable def parabolicHopfIdeal (t : IsSl2Triple h e f) : HopfIdeal k H :=
  parabolicDefiningHopfIdeal (t.cocharacter H)

/-- The defining Hopf ideal of the dynamic unipotent subgroup `U(h)` associated to `t`. -/
noncomputable def unipotentHopfIdeal (t : IsSl2Triple h e f) : HopfIdeal k H :=
  (t.cocharacter H).unipotentDefiningHopfIdeal

/-- The defining Hopf ideal of the dynamic Levi subgroup `L(h)` associated to `t`. -/
noncomputable def leviHopfIdeal (t : IsSl2Triple h e f) : HopfIdeal k H :=
  leviDefiningHopfIdeal (t.cocharacter H)

variable {H}

/-- The Lie algebra of `P(h)` is `⨁_{n ≥ 0} 𝔤(n)`, transported along
`Derivation.cotangentLinearEquiv`. -/
theorem lieSubalgebra_parabolicHopfIdeal_toSubmodule (t : IsSl2Triple h e f) :
    ((t.parabolicHopfIdeal H).lieSubalgebra (B := k)).toSubmodule =
      (⨆ (n : ℤ) (_ : 0 ≤ n), Module.End.eigenspace
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) h) (n : k)).map
        (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).toLinearMap := by
  rw [parabolicHopfIdeal, BialgHom.lieSubalgebra_parabolicDefiningHopfIdeal_eq_iSup_eigenspace,
    t.cotangentDualLieEquiv_symm_derivationComp_cocharacter_unit]

/-- The Lie algebra of `U(h)` is `⨁_{n > 0} 𝔤(n)`, transported along
`Derivation.cotangentLinearEquiv`. -/
theorem lieSubalgebra_unipotentHopfIdeal_toSubmodule (t : IsSl2Triple h e f) :
    ((t.unipotentHopfIdeal H).lieSubalgebra (B := k)).toSubmodule =
      (⨆ (n : ℤ) (_ : 0 < n), Module.End.eigenspace
          (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) h) (n : k)).map
        (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).toLinearMap := by
  rw [unipotentHopfIdeal, BialgHom.lieSubalgebra_unipotentDefiningHopfIdeal_eq_iSup_eigenspace,
    t.cotangentDualLieEquiv_symm_derivationComp_cocharacter_unit]

/-- The nilpositive element `e ∈ 𝔤(2)` belongs to the Lie algebra of `U(h)`. -/
theorem e_mem_lieSubalgebra_unipotentHopfIdeal (t : IsSl2Triple h e f) :
    Derivation.cotangentDualLieEquiv (R := k) (H := H) e ∈
      (t.unipotentHopfIdeal H).lieSubalgebra (B := k) := by
  rw [← LieSubalgebra.mem_toSubmodule, t.lieSubalgebra_unipotentHopfIdeal_toSubmodule]
  refine ⟨e, Submodule.mem_iSup_of_mem (2 : ℤ) (Submodule.mem_iSup_of_mem (by omega) ?_),
    (Derivation.cotangentDualLieEquiv_apply e).symm⟩
  rw [Int.cast_two, Module.End.mem_eigenspace_iff]
  exact t.lie_h_e_smul k

/-- The nilpositive element `e` belongs to the Lie algebra of `P(h)`. -/
theorem e_mem_lieSubalgebra_parabolicHopfIdeal (t : IsSl2Triple h e f) :
    Derivation.cotangentDualLieEquiv (R := k) (H := H) e ∈
      (t.parabolicHopfIdeal H).lieSubalgebra (B := k) := by
  rw [← LieSubalgebra.mem_toSubmodule, t.lieSubalgebra_parabolicHopfIdeal_toSubmodule]
  refine ⟨e, Submodule.mem_iSup_of_mem (2 : ℤ) (Submodule.mem_iSup_of_mem (by omega) ?_),
    (Derivation.cotangentDualLieEquiv_apply e).symm⟩
  rw [Int.cast_two, Module.End.mem_eigenspace_iff]
  exact t.lie_h_e_smul k

/-- The neutral element `h ∈ 𝔤(0)` belongs to the Lie algebra of `P(h)`. -/
theorem h_mem_lieSubalgebra_parabolicHopfIdeal (t : IsSl2Triple h e f) :
    Derivation.cotangentDualLieEquiv (R := k) (H := H) h ∈
      (t.parabolicHopfIdeal H).lieSubalgebra (B := k) := by
  rw [← LieSubalgebra.mem_toSubmodule, t.lieSubalgebra_parabolicHopfIdeal_toSubmodule]
  refine ⟨h, Submodule.mem_iSup_of_mem (0 : ℤ) (Submodule.mem_iSup_of_mem le_rfl ?_),
    (Derivation.cotangentDualLieEquiv_apply h).symm⟩
  rw [Int.cast_zero, Module.End.mem_eigenspace_iff, LieAlgebra.ad_apply, lie_self, zero_smul]

/-- The dynamic unipotent subgroup `U(h)` is geometrically connected. -/
theorem geometricallyConnected_quotient_unipotentHopfIdeal (t : IsSl2Triple h e f) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) (t.unipotentHopfIdeal H)) :=
  Cocharacter.geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal
    (t.cocharacter H)

/-- **The dynamic Levi `L(h)` equals the scheme-theoretic centralizer `C_G(h)`.** -/
@[simp]
theorem leviHopfIdeal_eq_centralizerHopfIdeal (t : IsSl2Triple h e f) :
    t.leviHopfIdeal H = centralizerHopfIdeal H h := by
  rw [leviHopfIdeal, BialgHom.leviDefiningHopfIdeal_eq_centralizerHopfIdeal_unit,
    t.cotangentDualLieEquiv_symm_derivationComp_cocharacter_unit]

/-- The Lie algebra of `L(h)` is `𝔤(0) = ker(ad h)`. -/
theorem lieSubalgebra_leviHopfIdeal (t : IsSl2Triple h e f) :
    ((t.leviHopfIdeal H).lieSubalgebra (B := k)).toSubmodule =
      LinearMap.ker (LieAlgebra.ad k (Derivation k H (Bialgebra.CounitAlgebra k H k))
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) h)) := by
  rw [t.leviHopfIdeal_eq_centralizerHopfIdeal, lieSubalgebra_centralizerHopfIdeal]

/-- **Conjugacy of `sl₂`-triples sharing `h` under `L(h)(k)`.** -/
theorem exists_mem_quotientPointsSubgroup_leviHopfIdeal_basePointsRepresentation_eq
    (t : IsSl2Triple h e f) (t' : IsSl2Triple h e' f') :
    ∃ g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) (t.leviHopfIdeal H)
        (CommAlgCat.of k k),
      Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g h = h ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g e = e' ∧
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g f =
          f' := by
  rw [t.leviHopfIdeal_eq_centralizerHopfIdeal]
  exact t.exists_mem_quotientPointsSubgroup_centralizerHopfIdeal_basePointsRepresentation_eq t'

/-! ### Equivariance under conjugation by `G(k)` -/

/-- Conjugating an `sl₂`-triple `(h, e, f)` by a rational point `g ∈ G(k)` conjugates the
associated `SL₂ → G` homomorphism by `g`. -/
theorem sl2CoordinateMap_basePointsRepresentation (t : IsSl2Triple h e f)
    (g : WithConv (H →ₐ[k] k)) :
    (t.basePointsRepresentation_adjointComodule g).sl2CoordinateMap H =
      (t.sl2CoordinateMap H).comp (HopfAlgebra.pointConjugationBialgEquiv g : H →ₐc[k] H) := by
  have had (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm
          (Derivation.adDerivation k (Derivation.pointInCounitAlgebra k g)
            (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) =
        Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g x := by
    have h1 := Derivation.tangentScalarExtensionEquiv_adjointComodule_endOfPoint
      (R := k) (H := H) (CommAlgCat.of k k) g (1 ⊗ₜ[k] x)
    simp only [Comodule.endOfPoint_tmul, one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation,
      Derivation.tangentScalarExtensionEquiv_tmul, Algebra.ofId_self, Derivation.mapValue_id,
      LinearMap.id_apply] at h1
    have h1' : (1 : k) • Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)
          (Comodule.basePointsRepresentation (Module.Dual k (Bialgebra.CotangentSpace k H)) g x) =
        Derivation.adDerivation k (Derivation.pointInCounitAlgebra k g)
          ((1 : k) • Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k) x) := h1
    rw [one_smul, one_smul] at h1'
    apply (Derivation.cotangentDualLieEquiv (R := k) (H := H)).injective
    simpa only [LieEquiv.coe_toLieHom, LieEquiv.apply_symm_apply,
      Derivation.cotangentDualLieEquiv_apply] using h1'.symm
  symm
  rw [(t.basePointsRepresentation_adjointComodule g).eq_sl2CoordinateMap_iff]
  constructor
  · rw [derivationComp_comp, LinearMap.comp_apply,
      derivationComp_sl2CoordinateMap_symm, t.slFinTwoLieHom_single_zero_one,
      derivationComp_pointConjugationBialgEquiv, had]
  · rw [derivationComp_comp, LinearMap.comp_apply,
      derivationComp_sl2CoordinateMap_symm, t.slFinTwoLieHom_single_one_zero,
      derivationComp_pointConjugationBialgEquiv, had]

/-- Conjugating an `sl₂`-triple `(h, e, f)` by `g ∈ G(k)` conjugates its cocharacter. -/
@[simp]
theorem cocharacter_basePointsRepresentation (t : IsSl2Triple h e f)
    (g : WithConv (H →ₐ[k] k)) :
    (t.basePointsRepresentation_adjointComodule g).cocharacter H =
      (t.cocharacter H).conjCocharacter g := by
  rw [cocharacter, t.sl2CoordinateMap_basePointsRepresentation, ← BialgHom.comp_assoc,
    ← cocharacter, BialgHom.conjCocharacter_eq_comp]

/-- Conjugating `(h, e, f)` by `g ∈ G(k)` conjugates `P(h)`. -/
@[simp]
theorem parabolicHopfIdeal_basePointsRepresentation (t : IsSl2Triple h e f)
    (g : WithConv (H →ₐ[k] k)) :
    (t.basePointsRepresentation_adjointComodule g).parabolicHopfIdeal H =
      (t.parabolicHopfIdeal H).conjugate g := by
  rw [parabolicHopfIdeal, t.cocharacter_basePointsRepresentation,
    BialgHom.parabolicDefiningHopfIdeal_conjCocharacter, parabolicHopfIdeal]

/-- Conjugating `(h, e, f)` by `g ∈ G(k)` conjugates `U(h)`. -/
@[simp]
theorem unipotentHopfIdeal_basePointsRepresentation (t : IsSl2Triple h e f)
    (g : WithConv (H →ₐ[k] k)) :
    (t.basePointsRepresentation_adjointComodule g).unipotentHopfIdeal H =
      (t.unipotentHopfIdeal H).conjugate g := by
  rw [unipotentHopfIdeal, t.cocharacter_basePointsRepresentation,
    BialgHom.unipotentDefiningHopfIdeal_conjCocharacter, unipotentHopfIdeal]

/-- Conjugating `(h, e, f)` by `g ∈ G(k)` conjugates `L(h)`. -/
theorem leviHopfIdeal_basePointsRepresentation (t : IsSl2Triple h e f)
    (g : WithConv (H →ₐ[k] k)) :
    (t.basePointsRepresentation_adjointComodule g).leviHopfIdeal H =
      (t.leviHopfIdeal H).conjugate g := by
  rw [leviHopfIdeal, t.cocharacter_basePointsRepresentation,
    BialgHom.leviDefiningHopfIdeal_conjCocharacter, leviHopfIdeal]

end AlgebraicGroup

end IsSl2Triple
