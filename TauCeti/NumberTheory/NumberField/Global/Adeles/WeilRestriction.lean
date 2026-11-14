/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.BaseChange
public import TauCeti.Topology.Algebra.PointTopology.WeilRestriction
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Topology
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Basic

/-!
# Restriction of scalars on adelic points

Let `E / F` be an extension of number fields and `G = Spec H` an affine monoid or group scheme of
finite presentation over `E`, with Weil restriction `Res_{E/F} G = Spec (WeilRestriction F E H)`
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
  `TauCeti.Algebra.WeilRestriction.infiniteAdelicPointsContinuousMulEquiv`: the finite-adele and
  infinite-adele counterparts `(Res_{E/F} G)(𝔸_F^f) ≃ₜ* G(𝔸_E^f)` and
  `(Res_{E/F} G)(F_∞) ≃ₜ* G(E_∞)`.
* `TauCeti.Algebra.WeilRestriction.adicCompletionPointsContinuousMulEquiv` and
  `TauCeti.Algebra.WeilRestriction.infiniteCompletionPointsContinuousMulEquiv`: the local place
  decompositions `(Res_{E/F} G)(F_v) ≃ₜ* ∏_{w ∣ v} G(E_w)`.
* `TauCeti.Algebra.WeilRestriction.multiplicativeGroupAdelicPointsContinuousMulEquiv`: for
  `G = 𝔾ₘ`, the topological group isomorphism `(Res_{E/F} 𝔾ₘ)(𝔸_F) ≃ₜ* IdeleGroup (𝓞 E) E`.

## Main results

* `TauCeti.Algebra.WeilRestriction.adelicPointsContinuousMulEquiv_mapValue_ofId`: compatibility
  with the rational diagonals `F → 𝔸_F` and `E → 𝔸_E` under `basePointsMulEquiv`.
* `TauCeti.Algebra.WeilRestriction.infiniteAdelicPointsContinuousMulEquiv_mapValue_fst` and
  `TauCeti.Algebra.WeilRestriction.finiteAdelicPointsContinuousMulEquiv_mapValue_snd`:
  compatibility with the projections from `𝔸` to `F_∞` and `𝔸^f`.
* `TauCeti.Algebra.WeilRestriction.adelicPointsContinuousMulEquiv_mapDomain_mapBialgHom`:
  naturality in morphisms `φ : H₁ →ₐc[E] H₂` of coordinate bialgebras.
* `TauCeti.Algebra.WeilRestriction.adelicPointsContinuousMulEquiv_mapDomain_compBialgEquiv`:
  transitivity in a tower `F ⊆ E ⊆ L` of number fields along `WeilRestriction.compBialgEquiv`.
* `TauCeti.Algebra.WeilRestriction.adicCompletionPointsContinuousMulEquiv_mapValue_proj` and
  `TauCeti.Algebra.WeilRestriction.infiniteCompletionPointsContinuousMulEquiv_mapValue_eval`:
  compatibility of the adelic comparisons with projections to completions at single places.

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

section Lemmas

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem adeleBaseChangeEquiv_one_tmul (b : E) :
    adeleBaseChangeEquiv F E (1 ⊗ₜ[F] b) = algebraMap E (AdeleRing (𝓞 E) E) b := by
  simp

private theorem finiteAdeleBaseChangeEquiv_one_tmul (b : E) :
    finiteAdeleBaseChangeEquiv F E (1 ⊗ₜ[F] b) = algebraMap E (FiniteAdeleRing (𝓞 E) E) b := by
  simp

private theorem infiniteAdeleBaseChangeEquiv_one_tmul (b : E) :
    infiniteAdeleBaseChangeEquiv F E (1 ⊗ₜ[F] b) = algebraMap E (InfiniteAdeleRing E) b := by
  simp

private theorem semilocalContinuousEquiv_one_tmul (v : HeightOneSpectrum (𝓞 F)) (b : E) :
    TauCeti.semilocalContinuousEquiv E v (1 ⊗ₜ[F] b) =
      algebraMap E
        ((w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) →
          w.1.adicCompletion E) b := by
  ext w
  simp

private theorem infiniteSemilocalContinuousEquiv_one_tmul (v : InfinitePlace F) (b : E) :
    infiniteSemilocalContinuousEquiv E v (1 ⊗ₜ[F] b) =
      algebraMap E ((w : {w : InfinitePlace E // w.LiesOver v}) → w.1.Completion) b := by
  ext w
  simp

private theorem finiteAdeleBaseChangeEquiv_proj_tmul (v : HeightOneSpectrum (𝓞 F))
    (a : FiniteAdeleRing (𝓞 F) F) (b : E)
    (w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) :
    FiniteAdeleRing.proj E w.1 (finiteAdeleBaseChangeEquiv F E (a ⊗ₜ[F] b)) =
      TauCeti.semilocalContinuousEquiv E v (FiniteAdeleRing.proj F v a ⊗ₜ[F] b) w := by
  have hf : ⇑(finiteAdeleBaseChangeEquiv F E) = ⇑(finiteAdeleBaseChangeHom F E) := by
    rw [← ContinuousAlgEquiv.coe_toAlgEquiv, finiteAdeleBaseChangeEquiv_toAlgEquiv,
      ← AlgEquiv.coe_toAlgHom, finiteAdeleBaseChangeAlgEquiv_toAlgHom]
  have hs : ⇑(TauCeti.semilocalContinuousEquiv E v) = ⇑(TauCeti.semilocalHom E v) := by
    rw [← ContinuousAlgEquiv.coe_toAlgEquiv, TauCeti.semilocalContinuousEquiv_toAlgEquiv,
      TauCeti.coe_semilocalEquiv]
  rw [FiniteAdeleRing.proj_apply, hf, hs, finiteAdeleBaseChangeHom_apply F E _ v w,
    TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply, ContinuousAlgHom.coe_coe]

private theorem infiniteAdeleBaseChangeEquiv_eval_tmul (v : InfinitePlace F)
    (a : InfiniteAdeleRing F) (b : E) (w : {w : InfinitePlace E // w.LiesOver v}) :
    infiniteAdeleBaseChangeEquiv F E (a ⊗ₜ[F] b) w.1 =
      infiniteSemilocalContinuousEquiv E v (a v ⊗ₜ[F] b) w := by
  obtain ⟨w, hw⟩ := w
  obtain rfl : w.comap (algebraMap F E) = v := InfinitePlace.LiesOver.comap_eq w v
  rw [infiniteAdeleBaseChangeEquiv_tmul_apply, infiniteSemilocalContinuousEquiv_tmul,
    AbsoluteValue.Completion.algebraMap_apply_of_liesOver]

end Lemmas

section Adelic

variable (F E H : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [CommRing H] [Bialgebra E H] [Algebra.FinitePresentation E H]

/-- **Restriction of scalars on adelic points.** For an extension `E / F` of number fields and a
finitely presented commutative `E`-bialgebra `H` (a coordinate Hopf algebra when `G = Spec H` is an
affine algebraic group over `E`), the Weil restriction point isomorphism followed by the adelic
scalar-extension equivalence `E ⊗[F] 𝔸_F ≃ 𝔸_F ⊗[F] E ≃ 𝔸_E` is a topological multiplicative
equivalence `(Res_{E/F} G)(𝔸_F) ≃ₜ* G(𝔸_E)` (an isomorphism of topological groups when `H` is a
Hopf algebra). -/
def adelicPointsContinuousMulEquiv :
    WithConv (WeilRestriction F E H →ₐ[F] AdeleRing (𝓞 F) F) ≃ₜ*
      WithConv (H →ₐ[E] AdeleRing (𝓞 E) E) :=
  pointsContinuousMulEquivOfBaseChange F E H (adeleBaseChangeEquiv F E)
    (adeleBaseChangeEquiv_one_tmul F E)

/-- **Restriction of scalars on finite adelic points.** The Weil restriction point isomorphism
followed by `E ⊗[F] 𝔸_F^f ≃ 𝔸_F^f ⊗[F] E ≃ 𝔸_E^f` is a topological multiplicative equivalence
`(Res_{E/F} G)(𝔸_F^f) ≃ₜ* G(𝔸_E^f)`. -/
def finiteAdelicPointsContinuousMulEquiv :
    WithConv (WeilRestriction F E H →ₐ[F] FiniteAdeleRing (𝓞 F) F) ≃ₜ*
      WithConv (H →ₐ[E] FiniteAdeleRing (𝓞 E) E) :=
  pointsContinuousMulEquivOfBaseChange F E H (finiteAdeleBaseChangeEquiv F E)
    (finiteAdeleBaseChangeEquiv_one_tmul F E)

/-- **Restriction of scalars on infinite adelic points.** The Weil restriction point isomorphism
followed by `E ⊗[F] F_∞ ≃ F_∞ ⊗[F] E ≃ E_∞` is a topological multiplicative equivalence
`(Res_{E/F} G)(F_∞) ≃ₜ* G(E_∞)`. -/
def infiniteAdelicPointsContinuousMulEquiv :
    WithConv (WeilRestriction F E H →ₐ[F] InfiniteAdeleRing F) ≃ₜ*
      WithConv (H →ₐ[E] InfiniteAdeleRing E) :=
  pointsContinuousMulEquivOfBaseChange F E H (infiniteAdeleBaseChangeEquiv F E)
    (infiniteAdeleBaseChangeEquiv_one_tmul F E)

variable {F E H}

private theorem adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange
    (x : WithConv (WeilRestriction F E H →ₐ[F] AdeleRing (𝓞 F) F)) :
    adelicPointsContinuousMulEquiv F E H x =
      pointsMulEquivOfBaseChange F E H (adeleBaseChangeEquiv F E).toAlgEquiv
        (adeleBaseChangeEquiv_one_tmul F E) x :=
  DFunLike.congr_fun
    (toMulEquiv_pointsContinuousMulEquivOfBaseChange (adeleBaseChangeEquiv F E)
      (adeleBaseChangeEquiv_one_tmul F E)) x

private theorem finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange
    (x : WithConv (WeilRestriction F E H →ₐ[F] FiniteAdeleRing (𝓞 F) F)) :
    finiteAdelicPointsContinuousMulEquiv F E H x =
      pointsMulEquivOfBaseChange F E H (finiteAdeleBaseChangeEquiv F E).toAlgEquiv
        (finiteAdeleBaseChangeEquiv_one_tmul F E) x :=
  DFunLike.congr_fun
    (toMulEquiv_pointsContinuousMulEquivOfBaseChange (finiteAdeleBaseChangeEquiv F E)
      (finiteAdeleBaseChangeEquiv_one_tmul F E)) x

private theorem infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange
    (x : WithConv (WeilRestriction F E H →ₐ[F] InfiniteAdeleRing F)) :
    infiniteAdelicPointsContinuousMulEquiv F E H x =
      pointsMulEquivOfBaseChange F E H (infiniteAdeleBaseChangeEquiv F E).toAlgEquiv
        (infiniteAdeleBaseChangeEquiv_one_tmul F E) x :=
  DFunLike.congr_fun
    (toMulEquiv_pointsContinuousMulEquivOfBaseChange (infiniteAdeleBaseChangeEquiv F E)
      (infiniteAdeleBaseChangeEquiv_one_tmul F E)) x

/-- `adelicPointsContinuousMulEquiv` acts on coordinate elements by `pointsMulEquiv`, tensor-factor
swap, and `adeleBaseChangeAlgEquiv`. -/
@[simp]
theorem adelicPointsContinuousMulEquiv_apply
    (x : WithConv (WeilRestriction F E H →ₐ[F] AdeleRing (𝓞 F) F)) (h : H) :
    (adelicPointsContinuousMulEquiv F E H x).ofConv h =
      adeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (AdeleRing (𝓞 F) F)
          ((pointsMulEquiv F E H (AdeleRing (𝓞 F) F) x).ofConv h)) := by
  simp [adelicPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- `finiteAdelicPointsContinuousMulEquiv` acts on coordinate elements by `pointsMulEquiv`,
tensor-factor swap, and `finiteAdeleBaseChangeAlgEquiv`. -/
@[simp]
theorem finiteAdelicPointsContinuousMulEquiv_apply
    (x : WithConv (WeilRestriction F E H →ₐ[F] FiniteAdeleRing (𝓞 F) F)) (h : H) :
    (finiteAdelicPointsContinuousMulEquiv F E H x).ofConv h =
      finiteAdeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (FiniteAdeleRing (𝓞 F) F)
          ((pointsMulEquiv F E H (FiniteAdeleRing (𝓞 F) F) x).ofConv h)) := by
  simp [finiteAdelicPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- `infiniteAdelicPointsContinuousMulEquiv` acts on coordinate elements by `pointsMulEquiv`,
tensor-factor swap, and `infiniteAdeleBaseChangeAlgEquiv`. -/
@[simp]
theorem infiniteAdelicPointsContinuousMulEquiv_apply
    (x : WithConv (WeilRestriction F E H →ₐ[F] InfiniteAdeleRing F)) (h : H) :
    (infiniteAdelicPointsContinuousMulEquiv F E H x).ofConv h =
      infiniteAdeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (InfiniteAdeleRing F)
          ((pointsMulEquiv F E H (InfiniteAdeleRing F) x).ofConv h)) := by
  simp [infiniteAdelicPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- **Rational diagonal compatibility on full adeles.** `adelicPointsContinuousMulEquiv` carries
the diagonal image of an `F`-point of `Res_{E/F} G` to the diagonal image of the corresponding
`E`-point of `G`. -/
theorem adelicPointsContinuousMulEquiv_mapValue_ofId
    (x : WithConv (WeilRestriction F E H →ₐ[F] F)) :
    adelicPointsContinuousMulEquiv F E H
        (AlgHom.mapValue (Algebra.ofId F (AdeleRing (𝓞 F) F)) x) =
      AlgHom.mapValue (Algebra.ofId E (AdeleRing (𝓞 E) E)) (basePointsMulEquiv F E H x) :=
  (adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange _).trans
    (pointsMulEquivOfBaseChange_mapValue_ofId _ _ x)

/-- **Rational diagonal compatibility on finite adeles.** -/
theorem finiteAdelicPointsContinuousMulEquiv_mapValue_ofId
    (x : WithConv (WeilRestriction F E H →ₐ[F] F)) :
    finiteAdelicPointsContinuousMulEquiv F E H
        (AlgHom.mapValue (Algebra.ofId F (FiniteAdeleRing (𝓞 F) F)) x) =
      AlgHom.mapValue (Algebra.ofId E (FiniteAdeleRing (𝓞 E) E)) (basePointsMulEquiv F E H x) :=
  (finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange _).trans
    (pointsMulEquivOfBaseChange_mapValue_ofId _ _ x)

/-- **Rational diagonal compatibility on infinite adeles.** -/
theorem infiniteAdelicPointsContinuousMulEquiv_mapValue_ofId
    (x : WithConv (WeilRestriction F E H →ₐ[F] F)) :
    infiniteAdelicPointsContinuousMulEquiv F E H
        (AlgHom.mapValue (Algebra.ofId F (InfiniteAdeleRing F)) x) =
      AlgHom.mapValue (Algebra.ofId E (InfiniteAdeleRing E)) (basePointsMulEquiv F E H x) :=
  (infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange _).trans
    (pointsMulEquivOfBaseChange_mapValue_ofId _ _ x)

/-- **Archimedean component projection.** Projecting from full adeles to infinite adeles intertwines
`adelicPointsContinuousMulEquiv` with `infiniteAdelicPointsContinuousMulEquiv`. -/
theorem infiniteAdelicPointsContinuousMulEquiv_mapValue_fst
    (x : WithConv (WeilRestriction F E H →ₐ[F] AdeleRing (𝓞 F) F)) :
    infiniteAdelicPointsContinuousMulEquiv F E H
        (AlgHom.mapValue (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
          AdeleRing (𝓞 F) F →ₐ[F] InfiniteAdeleRing F) x) =
      AlgHom.mapValue (AlgHom.fst E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) :
          AdeleRing (𝓞 E) E →ₐ[E] InfiniteAdeleRing E)
        (adelicPointsContinuousMulEquiv F E H x) := by
  let pT : AdeleRing (𝓞 F) F →ₐ[F] InfiniteAdeleRing F :=
    AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  let pS : AdeleRing (𝓞 E) E →ₐ[E] InfiniteAdeleRing E :=
    AlgHom.fst E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  rw [infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  refine pointsMulEquivOfBaseChange_mapValue _ _ _ _ pT pS (fun a b ↦ ?_) x
  simp only [ContinuousAlgEquiv.coe_toAlgEquiv, adeleBaseChangeEquiv_tmul,
    infiniteAdeleBaseChangeEquiv_tmul, map_mul, AlgHom.commutes]
  exact congrArg (· * algebraMap E (InfiniteAdeleRing E) b) (adeleExtension_fst a)

/-- **Finite-adele component projection.** Projecting from full adeles to finite adeles intertwines
`adelicPointsContinuousMulEquiv` with `finiteAdelicPointsContinuousMulEquiv`. -/
theorem finiteAdelicPointsContinuousMulEquiv_mapValue_snd
    (x : WithConv (WeilRestriction F E H →ₐ[F] AdeleRing (𝓞 F) F)) :
    finiteAdelicPointsContinuousMulEquiv F E H
        (AlgHom.mapValue (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
          AdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 F) F) x) =
      AlgHom.mapValue (AlgHom.snd E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) :
          AdeleRing (𝓞 E) E →ₐ[E] FiniteAdeleRing (𝓞 E) E)
        (adelicPointsContinuousMulEquiv F E H x) := by
  let pT : AdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 F) F :=
    AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  let pS : AdeleRing (𝓞 E) E →ₐ[E] FiniteAdeleRing (𝓞 E) E :=
    AlgHom.snd E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
  rw [finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  refine pointsMulEquivOfBaseChange_mapValue _ _ _ _ pT pS (fun a b ↦ ?_) x
  simp only [ContinuousAlgEquiv.coe_toAlgEquiv, adeleBaseChangeEquiv_tmul,
    finiteAdeleBaseChangeEquiv_tmul, map_mul, AlgHom.commutes]
  exact congrArg (· * algebraMap E (FiniteAdeleRing (𝓞 E) E) b) (adeleExtension_snd a)

end Adelic

section NaturalityAndTower

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- **Naturality in morphisms of coordinate bialgebras.** `adelicPointsContinuousMulEquiv` commutes
with homomorphisms `φ : H₁ →ₐc[E] H₂` of affine monoid or group schemes over `E`. -/
theorem adelicPointsContinuousMulEquiv_mapDomain_mapBialgHom
    {H₁ H₂ : Type*} [CommRing H₁] [CommRing H₂] [Bialgebra E H₁] [Bialgebra E H₂]
    [Algebra.FinitePresentation E H₁] [Algebra.FinitePresentation E H₂]
    (φ : H₁ →ₐc[E] H₂)
    (x : WithConv (WeilRestriction F E H₂ →ₐ[F] AdeleRing (𝓞 F) F)) :
    adelicPointsContinuousMulEquiv F E H₁ (BialgHom.mapDomain (mapBialgHom F E φ) x) =
      BialgHom.mapDomain φ (adelicPointsContinuousMulEquiv F E H₂ x) := by
  rw [adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  exact pointsMulEquivOfBaseChange_mapDomain_mapBialgHom _ _ φ x

/-- **Naturality of `finiteAdelicPointsContinuousMulEquiv`** in morphisms `φ : H₁ →ₐc[E] H₂`. -/
theorem finiteAdelicPointsContinuousMulEquiv_mapDomain_mapBialgHom
    {H₁ H₂ : Type*} [CommRing H₁] [CommRing H₂] [Bialgebra E H₁] [Bialgebra E H₂]
    [Algebra.FinitePresentation E H₁] [Algebra.FinitePresentation E H₂]
    (φ : H₁ →ₐc[E] H₂)
    (x : WithConv (WeilRestriction F E H₂ →ₐ[F] FiniteAdeleRing (𝓞 F) F)) :
    finiteAdelicPointsContinuousMulEquiv F E H₁ (BialgHom.mapDomain (mapBialgHom F E φ) x) =
      BialgHom.mapDomain φ (finiteAdelicPointsContinuousMulEquiv F E H₂ x) := by
  rw [finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  exact pointsMulEquivOfBaseChange_mapDomain_mapBialgHom _ _ φ x

/-- **Naturality of `infiniteAdelicPointsContinuousMulEquiv`** in morphisms `φ : H₁ →ₐc[E] H₂`. -/
theorem infiniteAdelicPointsContinuousMulEquiv_mapDomain_mapBialgHom
    {H₁ H₂ : Type*} [CommRing H₁] [CommRing H₂] [Bialgebra E H₁] [Bialgebra E H₂]
    [Algebra.FinitePresentation E H₁] [Algebra.FinitePresentation E H₂]
    (φ : H₁ →ₐc[E] H₂)
    (x : WithConv (WeilRestriction F E H₂ →ₐ[F] InfiniteAdeleRing F)) :
    infiniteAdelicPointsContinuousMulEquiv F E H₁ (BialgHom.mapDomain (mapBialgHom F E φ) x) =
      BialgHom.mapDomain φ (infiniteAdelicPointsContinuousMulEquiv F E H₂ x) := by
  rw [infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  exact pointsMulEquivOfBaseChange_mapDomain_mapBialgHom _ _ φ x

/-- **Tower compatibility on full adeles.** In a tower `F ⊆ E ⊆ L` of number fields, precomposing
an `𝔸_F`-point of `Res_{L/F} G` with `WeilRestriction.compBialgEquiv` and applying
`adelicPointsContinuousMulEquiv` in two steps (`E/F` then `L/E`) recovers the direct `L/F`
comparison. -/
theorem adelicPointsContinuousMulEquiv_mapDomain_compBialgEquiv
    {L H : Type*} [Field L] [NumberField L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [CommRing H] [Bialgebra L H] [Algebra.FinitePresentation L H]
    (x : WithConv (WeilRestriction F L H →ₐ[F] AdeleRing (𝓞 F) F)) :
    adelicPointsContinuousMulEquiv E L H
        (adelicPointsContinuousMulEquiv F E (WeilRestriction E L H)
          (BialgHom.mapDomain (compBialgEquiv F E L H :
            WeilRestriction F E (WeilRestriction E L H) →ₐc[F] WeilRestriction F L H) x)) =
      adelicPointsContinuousMulEquiv F L H x := by
  rw [adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    adelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  exact pointsMulEquivOfBaseChange_mapDomain_compBialgEquiv
    (adeleBaseChangeEquiv F E).toAlgEquiv (adeleBaseChangeEquiv_one_tmul F E)
    (adeleBaseChangeEquiv E L).toAlgEquiv (adeleBaseChangeEquiv_one_tmul E L)
    (adeleBaseChangeEquiv F L).toAlgEquiv (adeleBaseChangeEquiv_one_tmul F L)
    (fun a z ↦ adeleBaseChangeEquiv_tower F E L a z) x

/-- **Tower compatibility on finite adeles.** -/
theorem finiteAdelicPointsContinuousMulEquiv_mapDomain_compBialgEquiv
    {L H : Type*} [Field L] [NumberField L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [CommRing H] [Bialgebra L H] [Algebra.FinitePresentation L H]
    (x : WithConv (WeilRestriction F L H →ₐ[F] FiniteAdeleRing (𝓞 F) F)) :
    finiteAdelicPointsContinuousMulEquiv E L H
        (finiteAdelicPointsContinuousMulEquiv F E (WeilRestriction E L H)
          (BialgHom.mapDomain (compBialgEquiv F E L H :
            WeilRestriction F E (WeilRestriction E L H) →ₐc[F] WeilRestriction F L H) x)) =
      finiteAdelicPointsContinuousMulEquiv F L H x := by
  rw [finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  exact pointsMulEquivOfBaseChange_mapDomain_compBialgEquiv
    (finiteAdeleBaseChangeEquiv F E).toAlgEquiv (finiteAdeleBaseChangeEquiv_one_tmul F E)
    (finiteAdeleBaseChangeEquiv E L).toAlgEquiv (finiteAdeleBaseChangeEquiv_one_tmul E L)
    (finiteAdeleBaseChangeEquiv F L).toAlgEquiv (finiteAdeleBaseChangeEquiv_one_tmul F L)
    (fun a z ↦ finiteAdeleBaseChangeEquiv_tower F E L a z) x

/-- **Tower compatibility on infinite adeles.** -/
theorem infiniteAdelicPointsContinuousMulEquiv_mapDomain_compBialgEquiv
    {L H : Type*} [Field L] [NumberField L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    [CommRing H] [Bialgebra L H] [Algebra.FinitePresentation L H]
    (x : WithConv (WeilRestriction F L H →ₐ[F] InfiniteAdeleRing F)) :
    infiniteAdelicPointsContinuousMulEquiv E L H
        (infiniteAdelicPointsContinuousMulEquiv F E (WeilRestriction E L H)
          (BialgHom.mapDomain (compBialgEquiv F E L H :
            WeilRestriction F E (WeilRestriction E L H) →ₐc[F] WeilRestriction F L H) x)) =
      infiniteAdelicPointsContinuousMulEquiv F L H x := by
  rw [infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange,
    infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
  exact pointsMulEquivOfBaseChange_mapDomain_compBialgEquiv
    (infiniteAdeleBaseChangeEquiv F E).toAlgEquiv (infiniteAdeleBaseChangeEquiv_one_tmul F E)
    (infiniteAdeleBaseChangeEquiv E L).toAlgEquiv (infiniteAdeleBaseChangeEquiv_one_tmul E L)
    (infiniteAdeleBaseChangeEquiv F L).toAlgEquiv (infiniteAdeleBaseChangeEquiv_one_tmul F L)
    (fun a z ↦ infiniteAdeleBaseChangeEquiv_tower F E L a z) x

end NaturalityAndTower

section LocalPlaces

variable (F E H : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [CommRing H] [Bialgebra E H] [Algebra.FinitePresentation E H]

/-- **Local decomposition at a finite place.** At a finite place `v` of `F`, the `F_v`-points of
`Res_{E/F} G` decompose as the topological product over the finite places `w ∣ v` of `E` of the
`E_w`-points of `G`, via `TauCeti.semilocalContinuousEquiv`. -/
def adicCompletionPointsContinuousMulEquiv (v : HeightOneSpectrum (𝓞 F)) :
    WithConv (WeilRestriction F E H →ₐ[F] v.adicCompletion F) ≃ₜ*
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal},
        WithConv (H →ₐ[E] w.1.adicCompletion E) :=
  (pointsContinuousMulEquivOfBaseChange F E H (TauCeti.semilocalContinuousEquiv E v)
    (semilocalContinuousEquiv_one_tmul F E v)).trans
    (TauCeti.PointTopology.piPointsContinuousMulEquiv
      fun w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal} ↦
        w.1.adicCompletion E)

/-- **Local decomposition at an infinite place.** At an infinite place `v` of `F`, the
`F_v`-points of `Res_{E/F} G` decompose as the topological product over the infinite places `w ∣ v`
of `E` of the `E_w`-points of `G`, via `infiniteSemilocalContinuousEquiv`. -/
def infiniteCompletionPointsContinuousMulEquiv (v : InfinitePlace F) :
    WithConv (WeilRestriction F E H →ₐ[F] v.Completion) ≃ₜ*
      ∀ w : {w : InfinitePlace E // w.LiesOver v}, WithConv (H →ₐ[E] w.1.Completion) :=
  (pointsContinuousMulEquivOfBaseChange F E H (infiniteSemilocalContinuousEquiv E v)
    (infiniteSemilocalContinuousEquiv_one_tmul F E v)).trans
    (TauCeti.PointTopology.piPointsContinuousMulEquiv
      fun w : {w : InfinitePlace E // w.LiesOver v} ↦ w.1.Completion)

variable {F E H}

/-- The `w`-component of `adicCompletionPointsContinuousMulEquiv` evaluates `pointsMulEquiv`, swaps
the tensor factors, and takes the `w`-coordinate of `TauCeti.semilocalEquiv`. -/
@[simp]
theorem adicCompletionPointsContinuousMulEquiv_apply (v : HeightOneSpectrum (𝓞 F))
    (x : WithConv (WeilRestriction F E H →ₐ[F] v.adicCompletion F))
    (w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) (h : H) :
    (adicCompletionPointsContinuousMulEquiv F E H v x w).ofConv h =
      TauCeti.semilocalEquiv E v
        (Algebra.TensorProduct.comm F E (v.adicCompletion F)
          ((pointsMulEquiv F E H (v.adicCompletion F) x).ofConv h)) w := by
  simp [adicCompletionPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- The `w`-component of `infiniteCompletionPointsContinuousMulEquiv` evaluates `pointsMulEquiv`,
swaps the tensor factors, and takes the `w`-coordinate of `infiniteSemilocalEquiv`. -/
@[simp]
theorem infiniteCompletionPointsContinuousMulEquiv_apply (v : InfinitePlace F)
    (x : WithConv (WeilRestriction F E H →ₐ[F] v.Completion))
    (w : {w : InfinitePlace E // w.LiesOver v}) (h : H) :
    (infiniteCompletionPointsContinuousMulEquiv F E H v x w).ofConv h =
      infiniteSemilocalEquiv E v
        (Algebra.TensorProduct.comm F E v.Completion
          ((pointsMulEquiv F E H v.Completion x).ofConv h)) w := by
  simp [infiniteCompletionPointsContinuousMulEquiv, ← ContinuousAlgEquiv.coe_toAlgEquiv]

/-- **Compatibility with projection to a finite place.** Projecting a finite-adelic point of
`Res_{E/F} G` to `F_v` and decomposing via `adicCompletionPointsContinuousMulEquiv` reads off the
projections to `E_w` (`w ∣ v`) of the corresponding `𝔸_E^f`-point of `G`. -/
theorem adicCompletionPointsContinuousMulEquiv_mapValue_proj (v : HeightOneSpectrum (𝓞 F))
    (x : WithConv (WeilRestriction F E H →ₐ[F] FiniteAdeleRing (𝓞 F) F))
    (w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) :
    adicCompletionPointsContinuousMulEquiv F E H v
        (AlgHom.mapValue (FiniteAdeleRing.proj F v :
          FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F) x) w =
      AlgHom.mapValue (FiniteAdeleRing.proj E w.1 :
        FiniteAdeleRing (𝓞 E) E →ₐ[E] w.1.adicCompletion E)
        (finiteAdelicPointsContinuousMulEquiv F E H x) := by
  let pT : FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F := FiniteAdeleRing.proj F v
  let pS : FiniteAdeleRing (𝓞 E) E →ₐ[E]
      ∀ w' : {w' : HeightOneSpectrum (𝓞 E) // w'.asIdeal.LiesOver v.asIdeal},
        w'.1.adicCompletion E :=
    AlgHom.pi fun w' ↦ (FiniteAdeleRing.proj E w'.1 : _ →ₐ[E] _)
  have hp := pointsMulEquivOfBaseChange_mapValue
    (finiteAdeleBaseChangeEquiv F E).toAlgEquiv (finiteAdeleBaseChangeEquiv_one_tmul F E)
    (TauCeti.semilocalContinuousEquiv E v).toAlgEquiv (semilocalContinuousEquiv_one_tmul F E v)
    pT pS (fun a b ↦ funext fun w' ↦ finiteAdeleBaseChangeEquiv_proj_tmul F E v a b w') x
  have hpi : (Pi.evalAlgHom E
      (fun w' : {w' : HeightOneSpectrum (𝓞 E) // w'.asIdeal.LiesOver v.asIdeal} ↦
        w'.1.adicCompletion E) w).comp pS =
      (FiniteAdeleRing.proj E w.1 : FiniteAdeleRing (𝓞 E) E →ₐ[E] w.1.adicCompletion E) :=
    AlgHom.ext fun _ ↦ rfl
  calc
    adicCompletionPointsContinuousMulEquiv F E H v (AlgHom.mapValue pT x) w
      = AlgHom.mapValue
          (Pi.evalAlgHom E
            (fun w' : {w' : HeightOneSpectrum (𝓞 E) // w'.asIdeal.LiesOver v.asIdeal} ↦
              w'.1.adicCompletion E) w)
          (pointsMulEquivOfBaseChange F E H
            (TauCeti.semilocalContinuousEquiv E v).toAlgEquiv
            (semilocalContinuousEquiv_one_tmul F E v) (AlgHom.mapValue pT x)) := by
        rw [adicCompletionPointsContinuousMulEquiv, ContinuousMulEquiv.trans_apply,
          TauCeti.PointTopology.piPointsContinuousMulEquiv_apply]
        exact congrArg _
          (DFunLike.congr_fun (toMulEquiv_pointsContinuousMulEquivOfBaseChange _ _) _)
    _ = AlgHom.mapValue
          ((Pi.evalAlgHom E
            (fun w' : {w' : HeightOneSpectrum (𝓞 E) // w'.asIdeal.LiesOver v.asIdeal} ↦
              w'.1.adicCompletion E) w).comp pS)
          (finiteAdelicPointsContinuousMulEquiv F E H x) := by
        rw [hp, AlgHom.mapValue_comp, MonoidHom.comp_apply,
          finiteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
    _ = AlgHom.mapValue (FiniteAdeleRing.proj E w.1 :
          FiniteAdeleRing (𝓞 E) E →ₐ[E] w.1.adicCompletion E)
          (finiteAdelicPointsContinuousMulEquiv F E H x) := by
        rw [hpi]

/-- **Compatibility with projection from full adeles to a finite place.** -/
theorem adicCompletionPointsContinuousMulEquiv_mapValue_proj_comp_snd (v : HeightOneSpectrum (𝓞 F))
    (x : WithConv (WeilRestriction F E H →ₐ[F] AdeleRing (𝓞 F) F))
    (w : {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}) :
    adicCompletionPointsContinuousMulEquiv F E H v
        (AlgHom.mapValue ((FiniteAdeleRing.proj F v :
            FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F).comp
          (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
            AdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 F) F)) x) w =
      AlgHom.mapValue ((FiniteAdeleRing.proj E w.1 :
          FiniteAdeleRing (𝓞 E) E →ₐ[E] w.1.adicCompletion E).comp
        (AlgHom.snd E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) :
          AdeleRing (𝓞 E) E →ₐ[E] FiniteAdeleRing (𝓞 E) E))
        (adelicPointsContinuousMulEquiv F E H x) := by
  rw [AlgHom.mapValue_comp, AlgHom.mapValue_comp, MonoidHom.comp_apply, MonoidHom.comp_apply,
    adicCompletionPointsContinuousMulEquiv_mapValue_proj,
    finiteAdelicPointsContinuousMulEquiv_mapValue_snd]

/-- **Compatibility with projection to an infinite place.** Projecting an infinite-adelic point of
`Res_{E/F} G` to `F_v` and decomposing via `infiniteCompletionPointsContinuousMulEquiv` reads off
the projections to `E_w` (`w ∣ v`) of the corresponding `E_∞`-point of `G`. -/
theorem infiniteCompletionPointsContinuousMulEquiv_mapValue_eval (v : InfinitePlace F)
    (x : WithConv (WeilRestriction F E H →ₐ[F] InfiniteAdeleRing F))
    (w : {w : InfinitePlace E // w.LiesOver v}) :
    infiniteCompletionPointsContinuousMulEquiv F E H v
        (AlgHom.mapValue (Pi.evalAlgHom F (fun v' : InfinitePlace F ↦ v'.Completion) v :
          InfiniteAdeleRing F →ₐ[F] v.Completion) x) w =
      AlgHom.mapValue (Pi.evalAlgHom E (fun w' : InfinitePlace E ↦ w'.Completion) w.1 :
        InfiniteAdeleRing E →ₐ[E] w.1.Completion)
        (infiniteAdelicPointsContinuousMulEquiv F E H x) := by
  let pT : InfiniteAdeleRing F →ₐ[F] v.Completion :=
    Pi.evalAlgHom F (fun v' : InfinitePlace F ↦ v'.Completion) v
  let pS : InfiniteAdeleRing E →ₐ[E]
      ∀ w' : {w' : InfinitePlace E // w'.LiesOver v}, w'.1.Completion :=
    AlgHom.pi fun w' ↦ Pi.evalAlgHom E (fun u : InfinitePlace E ↦ u.Completion) w'.1
  have hp := pointsMulEquivOfBaseChange_mapValue
    (infiniteAdeleBaseChangeEquiv F E).toAlgEquiv (infiniteAdeleBaseChangeEquiv_one_tmul F E)
    (infiniteSemilocalContinuousEquiv E v).toAlgEquiv
    (infiniteSemilocalContinuousEquiv_one_tmul F E v)
    pT pS (fun a b ↦ funext fun w' ↦ infiniteAdeleBaseChangeEquiv_eval_tmul F E v a b w') x
  have hpi : (Pi.evalAlgHom E
      (fun w' : {w' : InfinitePlace E // w'.LiesOver v} ↦ w'.1.Completion) w).comp pS =
      Pi.evalAlgHom E (fun u : InfinitePlace E ↦ u.Completion) w.1 :=
    AlgHom.ext fun _ ↦ rfl
  calc
    infiniteCompletionPointsContinuousMulEquiv F E H v (AlgHom.mapValue pT x) w
      = AlgHom.mapValue
          (Pi.evalAlgHom E
            (fun w' : {w' : InfinitePlace E // w'.LiesOver v} ↦ w'.1.Completion) w)
          (pointsMulEquivOfBaseChange F E H
            (infiniteSemilocalContinuousEquiv E v).toAlgEquiv
            (infiniteSemilocalContinuousEquiv_one_tmul F E v) (AlgHom.mapValue pT x)) := by
        rw [infiniteCompletionPointsContinuousMulEquiv, ContinuousMulEquiv.trans_apply,
          TauCeti.PointTopology.piPointsContinuousMulEquiv_apply]
        exact congrArg _
          (DFunLike.congr_fun (toMulEquiv_pointsContinuousMulEquivOfBaseChange _ _) _)
    _ = AlgHom.mapValue
          ((Pi.evalAlgHom E
            (fun w' : {w' : InfinitePlace E // w'.LiesOver v} ↦ w'.1.Completion) w).comp pS)
          (infiniteAdelicPointsContinuousMulEquiv F E H x) := by
        rw [hp, AlgHom.mapValue_comp, MonoidHom.comp_apply,
          infiniteAdelicPointsContinuousMulEquiv_eq_pointsMulEquivOfBaseChange]
    _ = AlgHom.mapValue (Pi.evalAlgHom E (fun w' : InfinitePlace E ↦ w'.Completion) w.1 :
          InfiniteAdeleRing E →ₐ[E] w.1.Completion)
          (infiniteAdelicPointsContinuousMulEquiv F E H x) := by
        rw [hpi]

/-- **Compatibility with projection from full adeles to an infinite place.** -/
theorem infiniteCompletionPointsContinuousMulEquiv_mapValue_eval_comp_fst (v : InfinitePlace F)
    (x : WithConv (WeilRestriction F E H →ₐ[F] AdeleRing (𝓞 F) F))
    (w : {w : InfinitePlace E // w.LiesOver v}) :
    infiniteCompletionPointsContinuousMulEquiv F E H v
        (AlgHom.mapValue ((Pi.evalAlgHom F (fun v' : InfinitePlace F ↦ v'.Completion) v :
            InfiniteAdeleRing F →ₐ[F] v.Completion).comp
          (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
            AdeleRing (𝓞 F) F →ₐ[F] InfiniteAdeleRing F)) x) w =
      AlgHom.mapValue ((Pi.evalAlgHom E (fun w' : InfinitePlace E ↦ w'.Completion) w.1 :
          InfiniteAdeleRing E →ₐ[E] w.1.Completion).comp
        (AlgHom.fst E (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) :
          AdeleRing (𝓞 E) E →ₐ[E] InfiniteAdeleRing E))
        (adelicPointsContinuousMulEquiv F E H x) := by
  rw [AlgHom.mapValue_comp, AlgHom.mapValue_comp, MonoidHom.comp_apply, MonoidHom.comp_apply,
    infiniteCompletionPointsContinuousMulEquiv_mapValue_eval,
    infiniteAdelicPointsContinuousMulEquiv_mapValue_fst]

end LocalPlaces

section MultiplicativeGroup

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- **Adelic points of the Weil restriction of `𝔾ₘ` form the idele group.** Composing
`adelicPointsContinuousMulEquiv` for `H = E[T;T⁻¹]` with
`MultiplicativeGroup.pointsContinuousMulEquiv` identifies `(Res_{E/F} 𝔾ₘ)(𝔸_F)` as a topological
group with the idele group `IdeleGroup (𝓞 E) E = (AdeleRing (𝓞 E) E)ˣ`. -/
def multiplicativeGroupAdelicPointsContinuousMulEquiv :
    WithConv (WeilRestriction F E E[T;T⁻¹] →ₐ[F] AdeleRing (𝓞 F) F) ≃ₜ* IdeleGroup (𝓞 E) E :=
  (adelicPointsContinuousMulEquiv F E E[T;T⁻¹]).trans
    (MultiplicativeGroup.pointsContinuousMulEquiv E (AdeleRing (𝓞 E) E))

variable {F E} in
/-- The idele attached to an `𝔸_F`-point of `Res_{E/F} 𝔾ₘ` has underlying adele obtained by
applying `multiplicativeGroupPoints`, swapping tensor factors, and applying
`adeleBaseChangeAlgEquiv`. -/
@[simp]
theorem val_multiplicativeGroupAdelicPointsContinuousMulEquiv_apply
    (x : WithConv (WeilRestriction F E E[T;T⁻¹] →ₐ[F] AdeleRing (𝓞 F) F)) :
    ((multiplicativeGroupAdelicPointsContinuousMulEquiv F E x : IdeleGroup (𝓞 E) E) :
        AdeleRing (𝓞 E) E) =
      adeleBaseChangeAlgEquiv F E
        (Algebra.TensorProduct.comm F E (AdeleRing (𝓞 F) F)
          (multiplicativeGroupPoints F E (AdeleRing (𝓞 F) F) x : E ⊗[F] AdeleRing (𝓞 F) F)) := by
  simp [multiplicativeGroupAdelicPointsContinuousMulEquiv]

end MultiplicativeGroup

end TauCeti.Algebra.WeilRestriction
