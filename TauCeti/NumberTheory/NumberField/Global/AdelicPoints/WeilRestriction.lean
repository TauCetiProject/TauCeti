/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.BaseChange
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.Topology.Algebra.PointTopology.WeilRestriction
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Basic

/-!
# Restriction of scalars on adelic points

Let `E / F` be an extension of number fields and `G = Spec H` an affine monoid or group scheme
over `E`, with Weil restriction `Res_{E/F} G = Spec (WeilRestriction F E H)`
over `F`. Combining the topological Weil restriction adjunction with the continuous scalar-extension
isomorphisms `𝔸_F ⊗[F] E ≃A[𝔸_F] 𝔸_E`, `𝔸_F^f ⊗[F] E ≃A[𝔸_F^f] 𝔸_E^f`, and `F_∞ ⊗[F] E ≃A[F_∞] E_∞`
identifies the adelic points of `Res_{E/F} G` over `F` with the adelic points of `G` over `E` as
topological convolution monoids — and hence as topological groups whenever `H` is a Hopf algebra.

At a finite place `v` of `F` or an infinite place `v` of `F`, the semilocal decompositions
`F_v ⊗[F] E ≃A[F_v] ∏_{w ∣ v} E_w` identify `(Res_{E/F} G)(F_v)` with `∏_{w ∣ v} G(E_w)`,
compatibly with the place projections from the finite, infinite, and full adele rings.

## Main definitions

* `TauCeti.Algebra.WeilRestriction.adelicPointsContinuousMulEquiv`: the topological multiplicative
  equivalence `(Res_{E/F} G)(𝔸_F) ≃ₜ* G(𝔸_E)`.
* `TauCeti.Algebra.WeilRestriction.finiteAdelicPointsContinuousMulEquiv` and
  `TauCeti.Algebra.WeilRestriction.infinitePointsContinuousMulEquiv`: the finite-adele and
  infinite-adele counterparts `(Res_{E/F} G)(𝔸_F^f) ≃ₜ* G(𝔸_E^f)` and
  `(Res_{E/F} G)(F_∞) ≃ₜ* G(E_∞)`.
* `TauCeti.Algebra.WeilRestriction.localPointsContinuousMulEquiv` and
  `TauCeti.Algebra.WeilRestriction.infiniteLocalPointsContinuousMulEquiv`: the local place
  decompositions `(Res_{E/F} G)(F_v) ≃ₜ* ∏_{w ∣ v} G(E_w)`.
* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupAdelicPointsContinuousMulEquiv`: for
  `G = 𝔾ₘ`, the topological group isomorphism `(Res_{E/F} 𝔾ₘ)(𝔸_F) ≃ₜ* IdeleGroup (𝓞 E) E`.

## Main results

* `TauCeti.Algebra.WeilRestriction.adelicPointsContinuousMulEquiv_diagonal`: compatibility
  with the rational diagonals `F → 𝔸_F` and `E → 𝔸_E` under `basePointsMulEquiv`.
* `TauCeti.Algebra.WeilRestriction.infinitePointsContinuousMulEquiv_infiniteProjection` and
  `TauCeti.Algebra.WeilRestriction.finiteAdelicPointsContinuousMulEquiv_finiteProjection`:
  compatibility with the projections from `𝔸` to `F_∞` and `𝔸^f`.
* `TauCeti.Algebra.WeilRestriction.adelicPointsContinuousMulEquiv_mapDomain_mapBialgHom`:
  naturality in morphisms `φ : H₁ →ₐc[E] H₂` of coordinate bialgebras.
* `TauCeti.Algebra.WeilRestriction.adelicPointsContinuousMulEquiv_mapDomain_compBialgEquiv`:
  transitivity in a tower `F ⊆ E ⊆ L` of number fields along `WeilRestriction.compBialgEquiv`.
* `TauCeti.Algebra.WeilRestriction.localPointsContinuousMulEquiv_finiteLocalProjection`
  and `infiniteLocalPointsContinuousMulEquiv_infiniteLocalProjection`: compatibility of the
  adelic comparisons with projections to completions at single places.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Examples 2.4 and 4.2, pp. 3, 9–10.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §1.4, p. 8.
* J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4 (2005), §2, p. 11.
-/

public noncomputable section

open IsDedekindDomain NumberField WithConv TauCeti.GlobalNumberFields
open scoped TensorProduct LaurentPolynomial TauCeti.PointTopology
open scoped AdeleExtension InfiniteAdeleExtension FiniteAdeleExtension AdicCompletionExtension
attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

private local instance instTopologicalSpaceBaseChange {F T E : Type*} [Field F]
    [CommRing T] [Algebra F T] [TopologicalSpace T] [AddCommGroup E] [Module F E] :
    TopologicalSpace (T ⊗[F] E) :=
  moduleTopology T (T ⊗[F] E)

private local instance instIsModuleTopologyBaseChange {F T E : Type*} [Field F]
    [CommRing T] [Algebra F T] [TopologicalSpace T] [AddCommGroup E] [Module F E] :
    IsModuleTopology T (T ⊗[F] E) :=
  ⟨rfl⟩

namespace TauCeti.Algebra.WeilRestriction

section Adelic

variable (F E H : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [CommRing H] [Bialgebra E H]

/-- **Restriction of scalars on adelic points.** For an extension `E / F` of number fields and a
commutative `E`-bialgebra `H` (a coordinate Hopf algebra when `G = Spec H` is an
affine algebraic group over `E`), the Weil restriction point isomorphism followed by the adelic
scalar-extension equivalence `E ⊗[F] 𝔸_F ≃ 𝔸_F ⊗[F] E ≃ 𝔸_E` is a topological multiplicative
equivalence `(Res_{E/F} G)(𝔸_F) ≃ₜ* G(𝔸_E)` (an isomorphism of topological groups when `H` is a
Hopf algebra). -/
def adelicPointsContinuousMulEquiv :
    AdelicPoints (𝓞 F) F (WeilRestriction F E H) ≃ₜ* AdelicPoints (𝓞 E) E H :=
  pointsContinuousMulEquivOfBaseChange F E H (adeleBaseChangeEquiv F E)
    (adeleBaseChangeEquiv_one_tmul F E)

/-- **Restriction of scalars on finite adelic points.** The Weil restriction point isomorphism
followed by `E ⊗[F] 𝔸_F^f ≃ 𝔸_F^f ⊗[F] E ≃ 𝔸_E^f` is a topological multiplicative equivalence
`(Res_{E/F} G)(𝔸_F^f) ≃ₜ* G(𝔸_E^f)`. -/
def finiteAdelicPointsContinuousMulEquiv :
    AdelicPoints.FiniteAdelicPoints (𝓞 F) F (WeilRestriction F E H) ≃ₜ*
      AdelicPoints.FiniteAdelicPoints (𝓞 E) E H :=
  pointsContinuousMulEquivOfBaseChange F E H (finiteAdeleBaseChangeEquiv F E)
    (finiteAdeleBaseChangeEquiv_one_tmul F E)

/-- **Restriction of scalars on infinite adelic points.** The Weil restriction point isomorphism
followed by `E ⊗[F] F_∞ ≃ F_∞ ⊗[F] E ≃ E_∞` is a topological multiplicative equivalence
`(Res_{E/F} G)(F_∞) ≃ₜ* G(E_∞)`. -/
def infinitePointsContinuousMulEquiv :
    AdelicPoints.InfinitePoints F (WeilRestriction F E H) ≃ₜ* AdelicPoints.InfinitePoints E H :=
  pointsContinuousMulEquivOfBaseChange F E H (infiniteAdeleBaseChangeEquiv F E)
    (infiniteAdeleBaseChangeEquiv_one_tmul F E)

variable {F E H}

/-- Forgetting continuity from `adelicPointsContinuousMulEquiv` recovers
`pointsMulEquivOfBaseChange`. -/
@[simp]
theorem toMulEquiv_adelicPointsContinuousMulEquiv :
    (adelicPointsContinuousMulEquiv F E H :
        AdelicPoints (𝓞 F) F (WeilRestriction F E H) ≃* AdelicPoints (𝓞 E) E H) =
      pointsMulEquivOfBaseChange F E H (adeleBaseChangeAlgEquiv F E)
        (adeleBaseChangeAlgEquiv_one_tmul F E) := by
  rw [adelicPointsContinuousMulEquiv, toMulEquiv_pointsContinuousMulEquivOfBaseChange]
  simp only [adeleBaseChangeEquiv_toAlgEquiv]

/-- Forgetting continuity from `finiteAdelicPointsContinuousMulEquiv` recovers
`pointsMulEquivOfBaseChange`. -/
@[simp]
theorem toMulEquiv_finiteAdelicPointsContinuousMulEquiv :
    (finiteAdelicPointsContinuousMulEquiv F E H :
        AdelicPoints.FiniteAdelicPoints (𝓞 F) F (WeilRestriction F E H) ≃*
          AdelicPoints.FiniteAdelicPoints (𝓞 E) E H) =
      pointsMulEquivOfBaseChange F E H (finiteAdeleBaseChangeAlgEquiv F E)
        (finiteAdeleBaseChangeAlgEquiv_one_tmul F E) := by
  rw [finiteAdelicPointsContinuousMulEquiv, toMulEquiv_pointsContinuousMulEquivOfBaseChange]
  simp only [finiteAdeleBaseChangeEquiv_toAlgEquiv]

/-- Forgetting continuity from `infinitePointsContinuousMulEquiv` recovers
`pointsMulEquivOfBaseChange`. -/
@[simp]
theorem toMulEquiv_infinitePointsContinuousMulEquiv :
    (infinitePointsContinuousMulEquiv F E H :
        AdelicPoints.InfinitePoints F (WeilRestriction F E H) ≃*
          AdelicPoints.InfinitePoints E H) =
      pointsMulEquivOfBaseChange F E H (infiniteAdeleBaseChangeAlgEquiv F E)
        (infiniteAdeleBaseChangeAlgEquiv_one_tmul F E) := by
  rw [infinitePointsContinuousMulEquiv, toMulEquiv_pointsContinuousMulEquivOfBaseChange]
  simp only [infiniteAdeleBaseChangeEquiv_toAlgEquiv]

/-- `adelicPointsContinuousMulEquiv` acts on coordinate elements by `pointsMulEquiv`, tensor-factor
swap, and `adeleBaseChangeAlgEquiv`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_apply
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F E H)) (h : H) :
    (adelicPointsContinuousMulEquiv F E H x).ofConv h =
      adeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (AdeleRing (𝓞 F) F)
          ((pointsMulEquiv F E H (AdeleRing (𝓞 F) F) x).ofConv h)) := by
  simp [adelicPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- `finiteAdelicPointsContinuousMulEquiv` acts on coordinate elements by `pointsMulEquiv`,
tensor-factor swap, and `finiteAdeleBaseChangeAlgEquiv`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_apply
    (x : AdelicPoints.FiniteAdelicPoints (𝓞 F) F (WeilRestriction F E H)) (h : H) :
    (finiteAdelicPointsContinuousMulEquiv F E H x).ofConv h =
      finiteAdeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (FiniteAdeleRing (𝓞 F) F)
          ((pointsMulEquiv F E H (FiniteAdeleRing (𝓞 F) F) x).ofConv h)) := by
  simp [finiteAdelicPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- `infinitePointsContinuousMulEquiv` acts on coordinate elements by `pointsMulEquiv`,
tensor-factor swap, and `infiniteAdeleBaseChangeAlgEquiv`. -/
@[simp]
theorem infinitePointsContinuousMulEquiv_apply
    (x : AdelicPoints.InfinitePoints F (WeilRestriction F E H)) (h : H) :
    (infinitePointsContinuousMulEquiv F E H x).ofConv h =
      infiniteAdeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (InfiniteAdeleRing F)
          ((pointsMulEquiv F E H (InfiniteAdeleRing F) x).ofConv h)) := by
  simp [infinitePointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- Applying `pointsMulEquiv` to the inverse of `adelicPointsContinuousMulEquiv` post-composes
with the inverse of `adeleBaseChangeAlgEquiv` and the tensor-factor swap. -/
@[simp]
theorem pointsMulEquiv_adelicPointsContinuousMulEquiv_symm
    (y : AdelicPoints (𝓞 E) E H) :
    pointsMulEquiv F E H (AdeleRing (𝓞 F) F)
        ((adelicPointsContinuousMulEquiv F E H).symm y) =
      AlgHom.mapValue ((adeleBaseChangeAlgEquiv F E).ofCommRight
        (adeleBaseChangeAlgEquiv_one_tmul F E)).symm.toAlgHom y := by
  simp [adelicPointsContinuousMulEquiv]

/-- Applying `pointsMulEquiv` to the inverse of `finiteAdelicPointsContinuousMulEquiv`
post-composes with the inverse of `finiteAdeleBaseChangeAlgEquiv` and the tensor-factor swap. -/
@[simp]
theorem pointsMulEquiv_finiteAdelicPointsContinuousMulEquiv_symm
    (y : AdelicPoints.FiniteAdelicPoints (𝓞 E) E H) :
    pointsMulEquiv F E H (FiniteAdeleRing (𝓞 F) F)
        ((finiteAdelicPointsContinuousMulEquiv F E H).symm y) =
      AlgHom.mapValue ((finiteAdeleBaseChangeAlgEquiv F E).ofCommRight
        (finiteAdeleBaseChangeAlgEquiv_one_tmul F E)).symm.toAlgHom y := by
  simp [finiteAdelicPointsContinuousMulEquiv]

/-- Applying `pointsMulEquiv` to the inverse of `infinitePointsContinuousMulEquiv`
post-composes with the inverse of `infiniteAdeleBaseChangeAlgEquiv` and the tensor-factor swap. -/
@[simp]
theorem pointsMulEquiv_infinitePointsContinuousMulEquiv_symm
    (y : AdelicPoints.InfinitePoints E H) :
    pointsMulEquiv F E H (InfiniteAdeleRing F)
        ((infinitePointsContinuousMulEquiv F E H).symm y) =
      AlgHom.mapValue ((infiniteAdeleBaseChangeAlgEquiv F E).ofCommRight
        (infiniteAdeleBaseChangeAlgEquiv_one_tmul F E)).symm.toAlgHom y := by
  simp [infinitePointsContinuousMulEquiv]

/-- **Rational diagonal compatibility on full adeles.** `adelicPointsContinuousMulEquiv` carries
the diagonal image of an `F`-point of `Res_{E/F} G` to the diagonal image of the corresponding
`E`-point of `G`. -/
theorem adelicPointsContinuousMulEquiv_diagonal
    (x : WithConv (WeilRestriction F E H →ₐ[F] F)) :
    adelicPointsContinuousMulEquiv F E H
        (AdelicPoints.diagonal (𝓞 F) F (WeilRestriction F E H) x) =
      AdelicPoints.diagonal (𝓞 E) E H (basePointsMulEquiv F E H x) := by
  rw [AdelicPoints.diagonal_def, AdelicPoints.diagonal_def]
  exact pointsContinuousMulEquivOfBaseChange_mapValue_ofId _ _ x

/-- **Rational diagonal compatibility on finite adeles.** -/
theorem finiteAdelicPointsContinuousMulEquiv_finiteDiagonal
    (x : WithConv (WeilRestriction F E H →ₐ[F] F)) :
    finiteAdelicPointsContinuousMulEquiv F E H
        (AdelicPoints.finiteDiagonal (𝓞 F) F (WeilRestriction F E H) x) =
      AdelicPoints.finiteDiagonal (𝓞 E) E H (basePointsMulEquiv F E H x) := by
  rw [AdelicPoints.finiteDiagonal_def, AdelicPoints.finiteDiagonal_def]
  exact pointsContinuousMulEquivOfBaseChange_mapValue_ofId _ _ x

/-- **Rational diagonal compatibility on infinite adeles.** -/
theorem infinitePointsContinuousMulEquiv_infiniteDiagonal
    (x : WithConv (WeilRestriction F E H →ₐ[F] F)) :
    infinitePointsContinuousMulEquiv F E H
        (AdelicPoints.infiniteDiagonal F (WeilRestriction F E H) x) =
      AdelicPoints.infiniteDiagonal E H (basePointsMulEquiv F E H x) := by
  rw [AdelicPoints.infiniteDiagonal_def, AdelicPoints.infiniteDiagonal_def]
  exact pointsContinuousMulEquivOfBaseChange_mapValue_ofId _ _ x

/-- **Archimedean component projection.** Projecting from full adeles to infinite adeles intertwines
`adelicPointsContinuousMulEquiv` with `infinitePointsContinuousMulEquiv`. -/
theorem infinitePointsContinuousMulEquiv_infiniteProjection
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F E H)) :
    infinitePointsContinuousMulEquiv F E H
        (AdelicPoints.infiniteProjection (𝓞 F) F (WeilRestriction F E H) x) =
      AdelicPoints.infiniteProjection (𝓞 E) E H (adelicPointsContinuousMulEquiv F E H x) := by
  let pT : AdeleRing (𝓞 F) F →ₐ[F] InfiniteAdeleRing F :=
    AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  let pS : AdeleRing (𝓞 E) E →ₐ[E] InfiniteAdeleRing E :=
    AlgHom.fst E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  rw [AdelicPoints.infiniteProjection_def, AdelicPoints.infiniteProjection_def]
  refine pointsContinuousMulEquivOfBaseChange_mapValue (adeleBaseChangeEquiv F E)
    (adeleBaseChangeEquiv_one_tmul F E) _ _ pT pS (fun a b ↦ ?_) x
  simp only [pT, pS, adeleBaseChangeEquiv_tmul, infiniteAdeleBaseChangeEquiv_tmul,
    map_mul, AlgHom.commutes]
  exact congrArg (· * algebraMap E (InfiniteAdeleRing E) b) (adeleExtension_fst a)

/-- **Finite-adele component projection.** Projecting from full adeles to finite adeles intertwines
`adelicPointsContinuousMulEquiv` with `finiteAdelicPointsContinuousMulEquiv`. -/
theorem finiteAdelicPointsContinuousMulEquiv_finiteProjection
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F E H)) :
    finiteAdelicPointsContinuousMulEquiv F E H
        (AdelicPoints.finiteProjection (𝓞 F) F (WeilRestriction F E H) x) =
      AdelicPoints.finiteProjection (𝓞 E) E H (adelicPointsContinuousMulEquiv F E H x) := by
  let pT : AdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 F) F :=
    AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  let pS : AdeleRing (𝓞 E) E →ₐ[E] FiniteAdeleRing (𝓞 E) E :=
    AlgHom.snd E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  rw [AdelicPoints.finiteProjection_def, AdelicPoints.finiteProjection_def]
  refine pointsContinuousMulEquivOfBaseChange_mapValue (adeleBaseChangeEquiv F E)
    (adeleBaseChangeEquiv_one_tmul F E) _ _ pT pS (fun a b ↦ ?_) x
  simp only [pT, pS, adeleBaseChangeEquiv_tmul, finiteAdeleBaseChangeEquiv_tmul,
    map_mul, AlgHom.commutes]
  exact congrArg (· * algebraMap E (FiniteAdeleRing (𝓞 E) E) b) (adeleExtension_snd a)

end Adelic

section NaturalityAndTower

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- **Naturality in morphisms of coordinate bialgebras.** `adelicPointsContinuousMulEquiv` commutes
with homomorphisms `φ : H₁ →ₐc[E] H₂` of affine monoid or group schemes over `E`. -/
theorem adelicPointsContinuousMulEquiv_mapDomain_mapBialgHom
    {H₁ H₂ : Type*} [CommRing H₁] [CommRing H₂] [Bialgebra E H₁] [Bialgebra E H₂]
    (φ : H₁ →ₐc[E] H₂)
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F E H₂)) :
    adelicPointsContinuousMulEquiv F E H₁ (BialgHom.mapDomain (mapBialgHom F E φ) x) =
      BialgHom.mapDomain φ (adelicPointsContinuousMulEquiv F E H₂ x) :=
  pointsContinuousMulEquivOfBaseChange_mapDomain_mapBialgHom _ _ φ x

/-- **Naturality of `finiteAdelicPointsContinuousMulEquiv`** in morphisms `φ : H₁ →ₐc[E] H₂`. -/
theorem finiteAdelicPointsContinuousMulEquiv_mapDomain_mapBialgHom
    {H₁ H₂ : Type*} [CommRing H₁] [CommRing H₂] [Bialgebra E H₁] [Bialgebra E H₂]
    (φ : H₁ →ₐc[E] H₂)
    (x : AdelicPoints.FiniteAdelicPoints (𝓞 F) F (WeilRestriction F E H₂)) :
    finiteAdelicPointsContinuousMulEquiv F E H₁ (BialgHom.mapDomain (mapBialgHom F E φ) x) =
      BialgHom.mapDomain φ (finiteAdelicPointsContinuousMulEquiv F E H₂ x) :=
  pointsContinuousMulEquivOfBaseChange_mapDomain_mapBialgHom _ _ φ x

/-- **Naturality of `infinitePointsContinuousMulEquiv`** in morphisms `φ : H₁ →ₐc[E] H₂`. -/
theorem infinitePointsContinuousMulEquiv_mapDomain_mapBialgHom
    {H₁ H₂ : Type*} [CommRing H₁] [CommRing H₂] [Bialgebra E H₁] [Bialgebra E H₂]
    (φ : H₁ →ₐc[E] H₂)
    (x : AdelicPoints.InfinitePoints F (WeilRestriction F E H₂)) :
    infinitePointsContinuousMulEquiv F E H₁ (BialgHom.mapDomain (mapBialgHom F E φ) x) =
      BialgHom.mapDomain φ (infinitePointsContinuousMulEquiv F E H₂ x) :=
  pointsContinuousMulEquivOfBaseChange_mapDomain_mapBialgHom _ _ φ x

/-- **Tower compatibility on full adeles.** In a tower `F ⊆ E ⊆ L` of number fields, precomposing
an `𝔸_F`-point of `Res_{L/F} G` with `WeilRestriction.compBialgEquiv` and applying
`adelicPointsContinuousMulEquiv` in two steps (`E/F` then `L/E`) recovers the direct `L/F`
comparison. -/
theorem adelicPointsContinuousMulEquiv_mapDomain_compBialgEquiv
    {L H : Type*} [Field L] [NumberField L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [CommRing H] [Bialgebra L H]
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F L H)) :
    adelicPointsContinuousMulEquiv E L H
        (adelicPointsContinuousMulEquiv F E (WeilRestriction E L H)
          (BialgHom.mapDomain (compBialgEquiv F E L H :
            WeilRestriction F E (WeilRestriction E L H) →ₐc[F] WeilRestriction F L H) x)) =
      adelicPointsContinuousMulEquiv F L H x :=
  pointsContinuousMulEquivOfBaseChange_mapDomain_compBialgEquiv
    (adeleBaseChangeEquiv F E) (adeleBaseChangeEquiv_one_tmul F E)
    (adeleBaseChangeEquiv E L) (adeleBaseChangeEquiv_one_tmul E L)
    (adeleBaseChangeEquiv F L) (adeleBaseChangeEquiv_one_tmul F L)
    (adeleBaseChangeEquiv_tower F E L) x

/-- **Tower compatibility on finite adeles.** -/
theorem finiteAdelicPointsContinuousMulEquiv_mapDomain_compBialgEquiv
    {L H : Type*} [Field L] [NumberField L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [CommRing H] [Bialgebra L H]
    (x : AdelicPoints.FiniteAdelicPoints (𝓞 F) F (WeilRestriction F L H)) :
    finiteAdelicPointsContinuousMulEquiv E L H
        (finiteAdelicPointsContinuousMulEquiv F E (WeilRestriction E L H)
          (BialgHom.mapDomain (compBialgEquiv F E L H :
            WeilRestriction F E (WeilRestriction E L H) →ₐc[F] WeilRestriction F L H) x)) =
      finiteAdelicPointsContinuousMulEquiv F L H x :=
  pointsContinuousMulEquivOfBaseChange_mapDomain_compBialgEquiv
    (finiteAdeleBaseChangeEquiv F E) (finiteAdeleBaseChangeEquiv_one_tmul F E)
    (finiteAdeleBaseChangeEquiv E L) (finiteAdeleBaseChangeEquiv_one_tmul E L)
    (finiteAdeleBaseChangeEquiv F L) (finiteAdeleBaseChangeEquiv_one_tmul F L)
    (finiteAdeleBaseChangeEquiv_tower F E L) x

/-- **Tower compatibility on infinite adeles.** -/
theorem infinitePointsContinuousMulEquiv_mapDomain_compBialgEquiv
    {L H : Type*} [Field L] [NumberField L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [CommRing H] [Bialgebra L H]
    (x : AdelicPoints.InfinitePoints F (WeilRestriction F L H)) :
    infinitePointsContinuousMulEquiv E L H
        (infinitePointsContinuousMulEquiv F E (WeilRestriction E L H)
          (BialgHom.mapDomain (compBialgEquiv F E L H :
            WeilRestriction F E (WeilRestriction E L H) →ₐc[F] WeilRestriction F L H) x)) =
      infinitePointsContinuousMulEquiv F L H x :=
  pointsContinuousMulEquivOfBaseChange_mapDomain_compBialgEquiv
    (infiniteAdeleBaseChangeEquiv F E) (infiniteAdeleBaseChangeEquiv_one_tmul F E)
    (infiniteAdeleBaseChangeEquiv E L) (infiniteAdeleBaseChangeEquiv_one_tmul E L)
    (infiniteAdeleBaseChangeEquiv F L) (infiniteAdeleBaseChangeEquiv_one_tmul F L)
    (infiniteAdeleBaseChangeEquiv_tower F E L) x

end NaturalityAndTower

section LocalPlaces

private theorem trans_piContinuousMulEquiv_mapValue {F E H T S Tᵥ : Type*} {ι : Type*}
    {S_w : ι → Type*}
    [Field F] [Field E] [Algebra F E] [Module.Finite F E] [Module.Projective F E]
    [CommRing H] [Bialgebra E H]
    [CommRing T] [CommRing S] [CommRing Tᵥ] [∀ w, CommRing (S_w w)]
    [Algebra F T] [Algebra E S] [Algebra T S] [Algebra F Tᵥ] [∀ w, Algebra E (S_w w)]
    [Algebra Tᵥ (∀ w, S_w w)]
    [TopologicalSpace T] [IsTopologicalRing T] [TopologicalSpace S]
    [TopologicalSpace (T ⊗[F] E)] [IsModuleTopology T (T ⊗[F] E)]
    [TopologicalSpace Tᵥ] [IsTopologicalRing Tᵥ] [∀ w, TopologicalSpace (S_w w)]
    [TopologicalSpace (Tᵥ ⊗[F] E)] [IsModuleTopology Tᵥ (Tᵥ ⊗[F] E)]
    (e : T ⊗[F] E ≃A[T] S) (he : ∀ b : E, e (1 ⊗ₜ[F] b) = algebraMap E S b)
    (eᵥ : Tᵥ ⊗[F] E ≃A[Tᵥ] ∀ w, S_w w) (heᵥ : ∀ b : E, eᵥ (1 ⊗ₜ[F] b) = algebraMap E _ b)
    (pT : T →ₐ[F] Tᵥ) (pS : ∀ w : ι, S →ₐ[E] S_w w)
    (hp : ∀ (a : T) (b : E) (w : ι), pS w (e (a ⊗ₜ[F] b)) = eᵥ (pT a ⊗ₜ[F] b) w)
    (x : WithConv (WeilRestriction F E H →ₐ[F] T)) (w : ι) :
    ((pointsContinuousMulEquivOfBaseChange F E H eᵥ heᵥ).trans
      (TauCeti.PointTopology.piContinuousMulEquiv E H S_w))
      (AlgHom.mapValue pT x) w =
      AlgHom.mapValue (pS w) (pointsContinuousMulEquivOfBaseChange F E H e he x) := by
  have hloc : pointsContinuousMulEquivOfBaseChange F E H eᵥ heᵥ (AlgHom.mapValue pT x) =
      AlgHom.mapValue (AlgHom.pi pS) (pointsContinuousMulEquivOfBaseChange F E H e he x) :=
    pointsContinuousMulEquivOfBaseChange_mapValue e he eᵥ heᵥ pT (AlgHom.pi pS)
      (fun a b ↦ funext fun w' ↦ hp a b w') x
  refine WithConv.ofConv_injective <| AlgHom.ext fun h ↦ ?_
  have h' := DFunLike.congr_fun (congrArg WithConv.ofConv hloc) h
  simpa using congrFun h' w

variable (F E H : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [CommRing H] [Bialgebra E H]

/-- **Local decomposition at a finite place.** At a finite place `v` of `F`, the `F_v`-points of
`Res_{E/F} G` decompose as the topological product over the finite places `w ∣ v` of `E` of the
`E_w`-points of `G`, via `TauCeti.semilocalContinuousEquiv`. -/
def localPointsContinuousMulEquiv (v : HeightOneSpectrum (𝓞 F)) :
    AdelicPoints.LocalPoints (𝓞 F) F (WeilRestriction F E H) v ≃ₜ*
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal},
        AdelicPoints.LocalPoints (𝓞 E) E H w.val :=
  (pointsContinuousMulEquivOfBaseChange F E H (TauCeti.semilocalContinuousEquiv E v)
    TauCeti.semilocalContinuousEquiv_one_tmul).trans
    (TauCeti.PointTopology.piContinuousMulEquiv E H
      fun w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal} ↦
        w.val.adicCompletion E)

/-- **Local decomposition at an infinite place.** At an infinite place `v` of `F`, the
`F_v`-points of `Res_{E/F} G` decompose as the topological product over the infinite places `w ∣ v`
of `E` of the `E_w`-points of `G`, via `infiniteSemilocalContinuousEquiv`. -/
def infiniteLocalPointsContinuousMulEquiv (v : InfinitePlace F) :
    WithConv (WeilRestriction F E H →ₐ[F] v.Completion) ≃ₜ*
      ∀ w : {w : InfinitePlace E // w.LiesOver v}, WithConv (H →ₐ[E] w.val.Completion) :=
  (pointsContinuousMulEquivOfBaseChange F E H (infiniteSemilocalContinuousEquiv E v)
    infiniteSemilocalContinuousEquiv_one_tmul).trans
    (TauCeti.PointTopology.piContinuousMulEquiv E H
      fun w : {w : InfinitePlace E // w.LiesOver v} ↦ w.val.Completion)

variable {F E H}

/-- The `w`-component of `localPointsContinuousMulEquiv` evaluates `pointsMulEquiv`, swaps
the tensor factors, and takes the `w`-coordinate of `v.adicCompletionSemilocalEquiv`. -/
@[simp]
theorem localPointsContinuousMulEquiv_apply (v : HeightOneSpectrum (𝓞 F))
    (x : AdelicPoints.LocalPoints (𝓞 F) F (WeilRestriction F E H) v)
    (w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) (h : H) :
    (localPointsContinuousMulEquiv F E H v x w).ofConv h =
      v.adicCompletionSemilocalEquiv F (𝓞 E) E
        (Algebra.TensorProduct.comm F E (v.adicCompletion F)
          ((pointsMulEquiv F E H (v.adicCompletion F) x).ofConv h)) w := by
  simp [localPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- The `w`-component of `infiniteLocalPointsContinuousMulEquiv` evaluates `pointsMulEquiv`,
swaps the tensor factors, and takes the `w`-coordinate of `infiniteSemilocalEquiv`. -/
@[simp]
theorem infiniteLocalPointsContinuousMulEquiv_apply (v : InfinitePlace F)
    (x : WithConv (WeilRestriction F E H →ₐ[F] v.Completion))
    (w : {w : InfinitePlace E // w.LiesOver v}) (h : H) :
    (infiniteLocalPointsContinuousMulEquiv F E H v x w).ofConv h =
      infiniteSemilocalEquiv E v
        (Algebra.TensorProduct.comm F E v.Completion
          ((pointsMulEquiv F E H v.Completion x).ofConv h)) w := by
  simp [infiniteLocalPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- Applying `pointsMulEquiv` to the inverse of `localPointsContinuousMulEquiv`
assembles the local family with `AlgHom.pi` and post-composes with the inverse of
`v.adicCompletionSemilocalEquiv` and the tensor-factor swap. -/
@[simp]
theorem pointsMulEquiv_localPointsContinuousMulEquiv_symm (v : HeightOneSpectrum (𝓞 F))
    (y : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal},
      AdelicPoints.LocalPoints (𝓞 E) E H w.val) :
    pointsMulEquiv F E H (v.adicCompletion F)
        ((localPointsContinuousMulEquiv F E H v).symm y) =
      AlgHom.mapValue ((v.adicCompletionSemilocalEquiv F (𝓞 E) E).ofCommRight
          fun b ↦ by ext w; simp).symm.toAlgHom
        (toConv (AlgHom.pi fun w ↦ (y w).ofConv)) := by
  have hy : (TauCeti.PointTopology.piContinuousMulEquiv E H
      (fun w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal} ↦
        w.val.adicCompletion E)).symm y = toConv (AlgHom.pi fun w ↦ (y w).ofConv) :=
    WithConv.ofConv_injective <| AlgHom.ext fun h ↦ funext fun w ↦ by simp
  simp [localPointsContinuousMulEquiv, hy]

/-- Applying `pointsMulEquiv` to the inverse of `infiniteLocalPointsContinuousMulEquiv`
assembles the local family with `AlgHom.pi` and post-composes with the inverse of
`infiniteSemilocalEquiv` and the tensor-factor swap. -/
@[simp]
theorem pointsMulEquiv_infiniteLocalPointsContinuousMulEquiv_symm (v : InfinitePlace F)
    (y : ∀ w : {w : InfinitePlace E // w.LiesOver v}, WithConv (H →ₐ[E] w.val.Completion)) :
    pointsMulEquiv F E H v.Completion
        ((infiniteLocalPointsContinuousMulEquiv F E H v).symm y) =
      AlgHom.mapValue ((infiniteSemilocalEquiv E v).ofCommRight
          fun b ↦ by ext w; simp).symm.toAlgHom
        (toConv (AlgHom.pi fun w ↦ (y w).ofConv)) := by
  have hy : (TauCeti.PointTopology.piContinuousMulEquiv E H
      (fun w : {w : InfinitePlace E // w.LiesOver v} ↦ w.val.Completion)).symm y =
      toConv (AlgHom.pi fun w ↦ (y w).ofConv) :=
    WithConv.ofConv_injective <| AlgHom.ext fun h ↦ funext fun w ↦ by simp
  simp [infiniteLocalPointsContinuousMulEquiv, hy]

/-- **Compatibility with projection to a finite place.** Projecting a finite-adelic point of
`Res_{E/F} G` to `F_v` and decomposing via `localPointsContinuousMulEquiv` reads off the
projections to `E_w` (`w ∣ v`) of the corresponding `𝔸_E^f`-point of `G`. -/
theorem localPointsContinuousMulEquiv_finiteLocalProjection (v : HeightOneSpectrum (𝓞 F))
    (x : AdelicPoints.FiniteAdelicPoints (𝓞 F) F (WeilRestriction F E H))
    (w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) :
    localPointsContinuousMulEquiv F E H v
        (AdelicPoints.finiteLocalProjection (𝓞 F) F (WeilRestriction F E H) v x) w =
      AdelicPoints.finiteLocalProjection (𝓞 E) E H w.val
        (finiteAdelicPointsContinuousMulEquiv F E H x) := by
  rw [AdelicPoints.finiteLocalProjection_def, AdelicPoints.finiteLocalProjection_def]
  exact trans_piContinuousMulEquiv_mapValue (finiteAdeleBaseChangeEquiv F E)
    (finiteAdeleBaseChangeEquiv_one_tmul F E) (TauCeti.semilocalContinuousEquiv E v)
    TauCeti.semilocalContinuousEquiv_one_tmul (FiniteAdeleRing.proj F v).toAlgHom
    (fun w' ↦ (FiniteAdeleRing.proj E w'.val).toAlgHom)
    (fun a b w' ↦ finiteAdeleBaseChangeEquiv_proj_tmul F E v a b w') x w

/-- **Compatibility with projection from full adeles to a finite place.** -/
theorem localPointsContinuousMulEquiv_localProjection (v : HeightOneSpectrum (𝓞 F))
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F E H))
    (w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) :
    localPointsContinuousMulEquiv F E H v
        (AdelicPoints.localProjection (𝓞 F) F (WeilRestriction F E H) v x) w =
      AdelicPoints.localProjection (𝓞 E) E H w.val
        (adelicPointsContinuousMulEquiv F E H x) := by
  rw [AdelicPoints.localProjection_apply, AdelicPoints.localProjection_apply,
    localPointsContinuousMulEquiv_finiteLocalProjection,
    finiteAdelicPointsContinuousMulEquiv_finiteProjection]

/-- **Compatibility with projection to an infinite place.** Projecting an infinite-adelic point of
`Res_{E/F} G` to `F_v` and decomposing via `infiniteLocalPointsContinuousMulEquiv` reads off
the projections to `E_w` (`w ∣ v`) of the corresponding `E_∞`-point of `G`. -/
theorem infiniteLocalPointsContinuousMulEquiv_infiniteLocalProjection (v : InfinitePlace F)
    (x : AdelicPoints.InfinitePoints F (WeilRestriction F E H))
    (w : {w : InfinitePlace E // w.LiesOver v}) :
    infiniteLocalPointsContinuousMulEquiv F E H v
        (AdelicPoints.infiniteLocalProjection F (WeilRestriction F E H) v x) w =
      AdelicPoints.infiniteLocalProjection E H w.val
        (infinitePointsContinuousMulEquiv F E H x) := by
  rw [AdelicPoints.infiniteLocalProjection_def, AdelicPoints.infiniteLocalProjection_def]
  exact trans_piContinuousMulEquiv_mapValue (infiniteAdeleBaseChangeEquiv F E)
    (infiniteAdeleBaseChangeEquiv_one_tmul F E) (infiniteSemilocalContinuousEquiv E v)
    infiniteSemilocalContinuousEquiv_one_tmul
    (Pi.evalAlgHom F (fun v' : InfinitePlace F ↦ v'.Completion) v)
    (fun w' ↦ Pi.evalAlgHom E (fun u : InfinitePlace E ↦ u.Completion) w'.val)
    (fun a b w' ↦ infiniteAdeleBaseChangeEquiv_tmul_apply_of_liesOver F E v a b w') x w

/-- **Compatibility with projection from full adeles to an infinite place.** -/
theorem infiniteLocalPointsContinuousMulEquiv_infinitePlaceProjection (v : InfinitePlace F)
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F E H))
    (w : {w : InfinitePlace E // w.LiesOver v}) :
    infiniteLocalPointsContinuousMulEquiv F E H v
        (AdelicPoints.infinitePlaceProjection (𝓞 F) F (WeilRestriction F E H) v x) w =
      AdelicPoints.infinitePlaceProjection (𝓞 E) E H w.val
        (adelicPointsContinuousMulEquiv F E H x) := by
  rw [AdelicPoints.infinitePlaceProjection_apply, AdelicPoints.infinitePlaceProjection_apply,
    infiniteLocalPointsContinuousMulEquiv_infiniteLocalProjection,
    infinitePointsContinuousMulEquiv_infiniteProjection]

end LocalPlaces

section MultiplicativeGroup

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- **Adelic points of the Weil restriction of `𝔾ₘ` form the idele group.** Composing
`adelicPointsContinuousMulEquiv` for `H = E[T;T⁻¹]` with
`MultiplicativeGroup.pointsContinuousMulEquiv` identifies `(Res_{E/F} 𝔾ₘ)(𝔸_F)` as a topological
group with the idele group `IdeleGroup (𝓞 E) E = (AdeleRing (𝓞 E) E)ˣ`. -/
def multiplicativeGroupAdelicPointsContinuousMulEquiv :
    AdelicPoints (𝓞 F) F (WeilRestriction F E E[T;T⁻¹]) ≃ₜ* IdeleGroup (𝓞 E) E :=
  (adelicPointsContinuousMulEquiv F E E[T;T⁻¹]).trans
    (MultiplicativeGroup.pointsContinuousMulEquiv E (AdeleRing (𝓞 E) E))

variable {F E} in
/-- The idele attached to an `𝔸_F`-point of `Res_{E/F} 𝔾ₘ` has underlying adele obtained by
applying `multiplicativeGroupPoints`, swapping tensor factors, and applying
`adeleBaseChangeAlgEquiv`. -/
@[simp]
theorem val_multiplicativeGroupAdelicPointsContinuousMulEquiv_apply
    (x : AdelicPoints (𝓞 F) F (WeilRestriction F E E[T;T⁻¹])) :
    ((multiplicativeGroupAdelicPointsContinuousMulEquiv F E x : IdeleGroup (𝓞 E) E) :
        AdeleRing (𝓞 E) E) =
      adeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (AdeleRing (𝓞 F) F)
          (multiplicativeGroupPoints F E (AdeleRing (𝓞 F) F) x : E ⊗[F] AdeleRing (𝓞 F) F)) := by
  simp [multiplicativeGroupAdelicPointsContinuousMulEquiv]

/-- Applying `pointsMulEquiv` to the inverse of `multiplicativeGroupAdelicPointsContinuousMulEquiv`
converts the idele to the corresponding `𝔾ₘ`-point and post-composes with the inverse of
`adeleBaseChangeAlgEquiv` and the tensor-factor swap. -/
@[simp]
theorem pointsMulEquiv_multiplicativeGroupAdelicPointsContinuousMulEquiv_symm
    (u : IdeleGroup (𝓞 E) E) :
    pointsMulEquiv F E E[T;T⁻¹] (AdeleRing (𝓞 F) F)
        ((multiplicativeGroupAdelicPointsContinuousMulEquiv F E).symm u) =
      AlgHom.mapValue ((adeleBaseChangeAlgEquiv F E).ofCommRight
          (adeleBaseChangeAlgEquiv_one_tmul F E)).symm.toAlgHom
        (toConv (TauCeti.laurentEval (R := E) u)) := by
  simp [multiplicativeGroupAdelicPointsContinuousMulEquiv]

/-- Applying `multiplicativeGroupPoints` to the inverse of
`multiplicativeGroupAdelicPointsContinuousMulEquiv` transports the idele along the inverse of
`adeleBaseChangeAlgEquiv` and the tensor-factor swap. -/
@[simp]
theorem multiplicativeGroupPoints_multiplicativeGroupAdelicPointsContinuousMulEquiv_symm
    (u : IdeleGroup (𝓞 E) E) :
    multiplicativeGroupPoints F E (AdeleRing (𝓞 F) F)
        ((multiplicativeGroupAdelicPointsContinuousMulEquiv F E).symm u) =
      Units.map ((adeleBaseChangeAlgEquiv F E).ofCommRight
        (adeleBaseChangeAlgEquiv_one_tmul F E)).symm.toRingHom.toMonoidHom u := by
  ext
  rw [multiplicativeGroupPoints_apply, ← pointsMulEquiv_apply,
    pointsMulEquiv_multiplicativeGroupAdelicPointsContinuousMulEquiv_symm]
  simp

end MultiplicativeGroup

end TauCeti.Algebra.WeilRestriction
