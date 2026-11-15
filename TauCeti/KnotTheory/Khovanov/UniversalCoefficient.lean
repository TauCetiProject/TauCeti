/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupWithZero.ULift
public import TauCeti.Algebra.Ring.ULift
public import TauCeti.KnotTheory.Khovanov.BaseChange.Complex
public import TauCeti.RingTheory.PrincipalIdealDomain

/-!
# The universal coefficient theorem for Khovanov cohomology

Every term of the normalized Khovanov complex `D.khovanovComplex hD A j` is a finitely generated
free `A`-module (`TauCeti.OrientedPDCode.khovanovComplex`). When `A : Type u` is a principal ideal
domain (`[CommRing A] [NoZeroDivisors A] [IsPrincipalIdealRing A]`) and `f : A →+* B` is a
homomorphism of commutative rings in universe `u`, combining the `B`-linear universal coefficient
sequence of `TauCeti.Algebra.Homology.UniversalCoefficient.Tor` with the complex-level base-change
isomorphism `TauCeti.OrientedPDCode.khovanovComplexBaseChangeIso` produces the split short exact
sequence in `ModuleCat B`:

`0 ⟶ B ⊗[A] Khⁱʲ(D; A) ⟶ Khⁱʲ(D; B) ⟶ Tor₁^A(Khⁱ⁺¹'ʲ(D; A), B) ⟶ 0`.

Specializing `A = ULift.{u} ℤ` along `ULift.intCastRingHom R : ULift.{u} ℤ →+* R` expresses
`Khⁱʲ(D; R)` in `ModuleCat.{u} R` for any commutative ring `R : Type u` in terms of the
universe-lifted integral cohomology groups `Khⁱʲ(D; ULift.{u} ℤ)` and `Khⁱ⁺¹'ʲ(D; ULift.{u} ℤ)`,
which `TauCeti.OrientedPDCode.khovanovHomologyULiftIso` identifies with `Khⁱʲ(D; ℤ)` and
`Khⁱ⁺¹'ʲ(D; ℤ)`.

## Main definitions and results

* `TauCeti.OrientedPDCode.khovanovHomologyToTorOne`: the `B`-linear connecting map
  `Khⁱʲ(D; B) ⟶ Tor₁^A(Khⁱ⁺¹'ʲ(D; A), B)`.
* `TauCeti.OrientedPDCode.khovanovUniversalCoefficientShortComplex`,
  `TauCeti.OrientedPDCode.khovanovUniversalCoefficientSplitting`, and
  `TauCeti.OrientedPDCode.shortExact_khovanovUniversalCoefficientShortComplex`: the `B`-linear
  universal coefficient short exact sequence and splitting over a PID `A`.
* `TauCeti.OrientedPDCode.khovanovHomologyIsoBiprod`: the `B`-linear decomposition
  `Khⁱʲ(D; B) ≅ (B ⊗[A] Khⁱʲ(D; A)) ⊞ Tor₁^A(Khⁱ⁺¹'ʲ(D; A), B)`.
* `TauCeti.OrientedPDCode.isIso_khovanovHomologyBaseChangeMap_of_projective` and
  `TauCeti.OrientedPDCode.isIso_khovanovHomologyBaseChangeMap_of_ge_positiveCrossingCount`:
  invertibility of `B ⊗[A] Khⁱʲ(D; A) ⟶ Khⁱʲ(D; B)` when `Khⁱ⁺¹'ʲ(D; A)` is projective over `A`,
  in particular in cochain degrees `i ≥ n₊`.
* `ULift.intCastRingHom`, `TauCeti.OrientedPDCode.khovanovIntegralUniversalCoefficientShortComplex`,
  `TauCeti.OrientedPDCode.shortExact_khovanovIntegralUniversalCoefficientShortComplex`, and
  `TauCeti.OrientedPDCode.khovanovIntegralHomologyIsoBiprod`: integral universal coefficient
  theorem for arbitrary `R : Type u` `[CommRing R]`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3,
  Proposition 8 and Corollary 1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3A, Theorem 3A.3.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

/-- The canonical ring homomorphism `ULift.{u} ℤ →+* R` into any ring `R`, factoring
`Int.castRingHom` through `ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ`. -/
def ULift.intCastRingHom.{u, v} (R : Type v) [Ring R] : ULift.{u} ℤ →+* R :=
  (Int.castRingHom R).comp (ULift.ringEquiv.{0, u} : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- Evaluation of `ULift.intCastRingHom` on `z : ULift.{u} ℤ` casts `z.down` into `R`. -/
@[simp]
theorem ULift.intCastRingHom_apply.{u, v} (R : Type v) [Ring R] (z : ULift.{u} ℤ) :
    ULift.intCastRingHom R z = (z.down : R) :=
  (rfl)

namespace TauCeti.OrientedPDCode

universe u

section PID

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
  {A B : Type u} [CommRing A] [NoZeroDivisors A] [IsPrincipalIdealRing A] [CommRing B]
  (f : A →+* B)

/-- **The `B`-linear connecting map `Khⁱʲ(D; B) ⟶ Tor₁^A(Khⁱ⁺¹'ʲ(D; A), B)`** in `ModuleCat B`. -/
def khovanovHomologyToTorOne (i j : ℤ) :
    D.khovanovHomology hD B i j ⟶
      (ModuleCat.torExtendScalars f 1).obj (D.khovanovHomology hD A (i + 1) j) :=
  homologyMap (D.khovanovComplexBaseChangeIso hD f j).inv i ≫
    (D.khovanovComplex hD A j).homologyExtendScalarsToTorOne f
      (by simp : (ComplexShape.up ℤ).Rel i (i + 1))

/-- **The `B`-linear universal coefficient short complex for Khovanov cohomology:**
`(B ⊗[A] Khⁱʲ(D; A)) ⟶ Khⁱʲ(D; B) ⟶ Tor₁^A(Khⁱ⁺¹'ʲ(D; A), B)` in `ModuleCat B`. -/
@[expose, simps]
def khovanovUniversalCoefficientShortComplex (i j : ℤ) : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.mk (D.khovanovHomologyBaseChangeMap hD f i j)
    (D.khovanovHomologyToTorOne hD f i j)
    (by
      rw [khovanovHomologyBaseChangeMap_def, khovanovHomologyToTorOne, Category.assoc,
        ← Category.assoc (homologyMap _ i), ← homologyMap_comp, Iso.hom_inv_id, homologyMap_id,
        Category.id_comp]
      exact ((D.khovanovComplex hD A j).extendScalarsUniversalCoefficientShortComplex f
        (by simp : (ComplexShape.up ℤ).Rel i (i + 1))).zero)

/-- Identification of `khovanovUniversalCoefficientShortComplex` with the algebraic universal
coefficient short complex of `D.khovanovComplex hD A j` along `khovanovComplexBaseChangeIso`. -/
def khovanovUniversalCoefficientShortComplexIso (i j : ℤ) :
    (D.khovanovComplex hD A j).extendScalarsUniversalCoefficientShortComplex f
        (by simp : (ComplexShape.up ℤ).Rel i (i + 1)) ≅
      D.khovanovUniversalCoefficientShortComplex hD f i j :=
  ShortComplex.isoMk (Iso.refl _)
    (homologyMapIso (D.khovanovComplexBaseChangeIso hD f j) i)
    (Iso.refl _)
    (by
      dsimp [khovanovUniversalCoefficientShortComplex,
        extendScalarsUniversalCoefficientShortComplex]
      rw [khovanovHomologyBaseChangeMap_def, Category.id_comp, homologyMapIso_hom])
    (by
      dsimp [khovanovUniversalCoefficientShortComplex,
        extendScalarsUniversalCoefficientShortComplex, khovanovHomologyToTorOne]
      rw [Category.comp_id, homologyMapIso_hom, ← Category.assoc, ← homologyMap_comp,
        Iso.hom_inv_id, homologyMap_id, Category.id_comp])

/-- **`B`-linear splitting of the Khovanov universal coefficient sequence** over a PID `A`. -/
def khovanovUniversalCoefficientSplitting (i j : ℤ) :
    (D.khovanovUniversalCoefficientShortComplex hD f i j).Splitting :=
  ShortComplex.Splitting.ofIso
    ((D.khovanovComplex hD A j).extendScalarsUniversalCoefficientSplitting f
      (by simp : (ComplexShape.up ℤ).Rel i (i + 1)))
    (D.khovanovUniversalCoefficientShortComplexIso hD f i j)

/-- **Universal coefficient theorem for Khovanov cohomology over a PID.** For any ring map
`f : A →+* B` out of a principal ideal domain `A`, the sequence
`0 ⟶ B ⊗[A] Khⁱʲ(D; A) ⟶ Khⁱʲ(D; B) ⟶ Tor₁^A(Khⁱ⁺¹'ʲ(D; A), B) ⟶ 0` in `ModuleCat B` is short
exact. -/
theorem shortExact_khovanovUniversalCoefficientShortComplex (i j : ℤ) :
    (D.khovanovUniversalCoefficientShortComplex hD f i j).ShortExact :=
  (D.khovanovUniversalCoefficientSplitting hD f i j).shortExact

/-- **`B`-linear direct-sum decomposition of Khovanov cohomology:**
`Khⁱʲ(D; B) ≅ (B ⊗[A] Khⁱʲ(D; A)) ⊞ Tor₁^A(Khⁱ⁺¹'ʲ(D; A), B)` in `ModuleCat B`. -/
def khovanovHomologyIsoBiprod (i j : ℤ) :
    D.khovanovHomology hD B i j ≅
      (ModuleCat.extendScalars f).obj (D.khovanovHomology hD A i j) ⊞
        (ModuleCat.torExtendScalars f 1).obj (D.khovanovHomology hD A (i + 1) j) :=
  (D.khovanovUniversalCoefficientSplitting hD f i j).isoBinaryBiproduct

/-- When `Khⁱ⁺¹'ʲ(D; A)` is projective over `A` (equivalently free/torsion-free when finitely
generated over a PID), the Tor correction vanishes and `B ⊗[A] Khⁱʲ(D; A) ⟶ Khⁱʲ(D; B)` is an
isomorphism. -/
theorem isIso_khovanovHomologyBaseChangeMap_of_projective (i j : ℤ)
    [Projective (D.khovanovHomology hD A (i + 1) j)] :
    IsIso (D.khovanovHomologyBaseChangeMap hD f i j) := by
  have : IsIso ((D.khovanovComplex hD A j).mapHomologyComparison
      (ModuleCat.extendScalars.{u, u, u} f) i) :=
    (D.khovanovComplex hD A j).isIso_mapHomologyComparison_of_projective_homology
      (ModuleCat.extendScalars.{u, u, u} f) (by simp : (ComplexShape.up ℤ).Rel i (i + 1))
  have : IsIso (homologyMap (D.khovanovComplexBaseChangeIso hD f j).hom i) :=
    ((homologyFunctor _ _ i).mapIso (D.khovanovComplexBaseChangeIso hD f j)).isIso_hom
  rw [khovanovHomologyBaseChangeMap_def]
  exact IsIso.comp_isIso

/-- At or above the top cochain degree `n₊`, `Khⁱ⁺¹'ʲ(D; A)` vanishes and therefore
`B ⊗[A] Khⁱʲ(D; A) ⟶ Khⁱʲ(D; B)` is always an isomorphism. -/
theorem isIso_khovanovHomologyBaseChangeMap_of_ge_positiveCrossingCount {i : ℤ}
    (hi : (D.positiveCrossingCount : ℤ) ≤ i) (j : ℤ) :
    IsIso (D.khovanovHomologyBaseChangeMap hD f i j) := by
  have hmem : i + 1 ∉ Set.Icc (-(D.negativeCrossingCount : ℤ)) D.positiveCrossingCount := by
    simp only [Set.mem_Icc]
    omega
  have hzero : IsZero (D.khovanovHomology hD A (i + 1) j) :=
    D.isZero_khovanovHomology_of_cochain_notMem_Icc hD A hmem j
  have : Projective (D.khovanovHomology hD A (i + 1) j) :=
    Projective.of_iso hzero.isoZero.symm inferInstance
  exact D.isIso_khovanovHomologyBaseChangeMap_of_projective hD f i j

end PID

section Integral

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **The `R`-linear integral universal coefficient short complex for Khovanov cohomology:**
`(R ⊗[ULift ℤ] Khⁱʲ(D; ULift ℤ)) ⟶ Khⁱʲ(D; R) ⟶ Tor₁^{ULift ℤ}(Khⁱ⁺¹'ʲ(D; ULift ℤ), R)` in
`ModuleCat R`. Here `TauCeti.OrientedPDCode.khovanovHomologyULiftIso` identifies
`Khᵏʲ(D; ULift.{u} ℤ)` with the universe lift of `Khᵏʲ(D; ℤ)`. -/
abbrev khovanovIntegralUniversalCoefficientShortComplex (i j : ℤ) :
    ShortComplex (ModuleCat.{u} R) :=
  D.khovanovUniversalCoefficientShortComplex hD (ULift.intCastRingHom R) i j

/-- `R`-linear splitting of `khovanovIntegralUniversalCoefficientShortComplex`. -/
def khovanovIntegralUniversalCoefficientSplitting (i j : ℤ) :
    (D.khovanovIntegralUniversalCoefficientShortComplex hD R i j).Splitting :=
  D.khovanovUniversalCoefficientSplitting hD (ULift.intCastRingHom R) i j

/-- **Integral universal coefficient theorem for Khovanov cohomology.** For every commutative ring
`R : Type u`, `khovanovIntegralUniversalCoefficientShortComplex D hD R i j` is short exact in
`ModuleCat.{u} R`. -/
theorem shortExact_khovanovIntegralUniversalCoefficientShortComplex (i j : ℤ) :
    (D.khovanovIntegralUniversalCoefficientShortComplex hD R i j).ShortExact :=
  D.shortExact_khovanovUniversalCoefficientShortComplex hD (ULift.intCastRingHom R) i j

/-- **`R`-linear decomposition of `Khⁱʲ(D; R)` into extended integral cohomology and Tor:**
`Khⁱʲ(D; R) ≅ (R ⊗[ULift ℤ] Khⁱʲ(D; ULift ℤ)) ⊞ Tor₁^{ULift ℤ}(Khⁱ⁺¹'ʲ(D; ULift ℤ), R)`. -/
def khovanovIntegralHomologyIsoBiprod (i j : ℤ) :
    D.khovanovHomology hD R i j ≅
      (ModuleCat.extendScalars (ULift.intCastRingHom R)).obj
          (D.khovanovHomology hD (ULift.{u} ℤ) i j) ⊞
        (ModuleCat.torExtendScalars (ULift.intCastRingHom R) 1).obj
          (D.khovanovHomology hD (ULift.{u} ℤ) (i + 1) j) :=
  D.khovanovHomologyIsoBiprod hD (ULift.intCastRingHom R) i j

end Integral

end TauCeti.OrientedPDCode
