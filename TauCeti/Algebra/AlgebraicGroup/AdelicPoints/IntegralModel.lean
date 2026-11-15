/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdelicPoints.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# Integral models of affine group schemes away from a finite set of places

Let `F` be a number field, `H` a commutative Hopf `F`-algebra representing an affine group scheme
`G = Spec H` over `F`, and `S` a finite set of height-one primes of `𝓞 F`. An *integral model* of
`G` away from `S` (`TauCeti.IntegralModel F H S`) consists of a finitely presented commutative Hopf
algebra `M.coordinate` over the ring of `S`-integers `𝒪_{F,S} = SIntegers F S` together with an
isomorphism of commutative Hopf `F`-algebras identifying `F ⊗[𝒪_{F,S}] M.coordinate` with `H`.

From an integral model `M` away from `S`, this file constructs and characterizes:

* **Local integral points** `M.localPoints v hv ≤ LocalPoints F H v` for `v ∉ S`: the image of the
  `𝒪_v`-points of `M.coordinate` under the generic-fibre identification, characterized by
  integrality on the coordinates of `M.coordinate` (or on any generating family over `𝒪_{F,S}`),
  and proved to be a **compact open** (hence closed) subgroup of `LocalPoints F H v`.
* **Reference level subgroups** `M.level v ≤ LocalPoints F H v`: `⊤` at `v ∈ S` and
  `M.localPoints v hv` at `v ∉ S`, open at every finite place and compact outside `S`.
* **Global `T`-integral points** `M.globalPoints T hST ≤ WithConv (H →ₐ[F] F)` for `S ⊆ T`: the
  `F`-rational points integral on `M.coordinate` away from `T`, proved equal to the rational points
  whose local projections at all `v ∉ T` lie in `M.localPoints v _`.
* **Base change to a larger exceptional set** `M.enlarge hST : IntegralModel F H T`: scalar
  extension of `M.coordinate` from `𝒪_{F,S}` to `𝒪_{F,T}`, preserving local integral subgroups away
  from `T` and global `U`-integral subgroups for `T ⊆ U`.

## Main declarations

* `TauCeti.SIntegers`: the subalgebra `𝒪_{F,S}` of `S`-integers of a number field `F`.
* `TauCeti.IntegralModel`: bundled integral model of `Spec H` over `𝒪_{F,S}`.
* `TauCeti.IntegralModel.integralPointsHom`, `TauCeti.IntegralModel.localIntegralHom`,
  `TauCeti.IntegralModel.globalIntegralHom`: injective group homomorphisms from integral points of
  `M.coordinate` into generic-fibre points.
* `TauCeti.IntegralModel.localPoints`, `TauCeti.IntegralModel.mem_localPoints_iff`,
  `TauCeti.IntegralModel.isOpen_localPoints`, `TauCeti.IntegralModel.isCompact_localPoints`: local
  integral subgroups away from `S` are compact open subgroups.
* `TauCeti.IntegralModel.level`, `TauCeti.IntegralModel.isOpen_level`,
  `TauCeti.IntegralModel.fact_isOpen_level`: the place-by-place reference family for the restricted
  product.
* `TauCeti.IntegralModel.globalPoints`,
  `TauCeti.IntegralModel.mem_globalPoints_iff_forall_localPoints`: global `T`-integral points and
  their local-global characterization.
* `TauCeti.IntegralModel.enlarge`: base change of an integral model from `S` to `T ⊇ S`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Thms. 3.4 and 3.6, Rem. 3.5, pp. 5–6.
* J. S. Milne, *Adelic Algebraic Groups*, §4, pp. 42–43.
-/

public section

open CategoryTheory IsDedekindDomain NumberField TensorProduct Topology WithConv
open TauCeti.AdelicPoints TauCeti.PointTopology

namespace TauCeti

universe u

section SIntegers

variable (F : Type u) [Field F] [NumberField F]

/-- The subalgebra `𝒪_{F,S}` of `S`-integers of `F`, consisting of elements with `v`-adic valuation
at most `1` at every height-one prime `v ∉ S`. -/
noncomputable abbrev SIntegers (S : Finset (HeightOneSpectrum (𝓞 F))) : Subalgebra (𝓞 F) F :=
  (S : Set (HeightOneSpectrum (𝓞 F))).integer F

variable {F}

/-- An element of `F` is an `S`-integer if and only if its image in `F_v` is `v`-integral for every
`v ∉ S`. -/
theorem mem_sIntegers_iff_forall_adicCompletionIntegers
    {S : Finset (HeightOneSpectrum (𝓞 F))} {x : F} :
    x ∈ SIntegers F S ↔
      ∀ v ∉ S, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
  simp only [Set.mem_integer_iff, Finset.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  refine forall_congr' fun v ↦ imp_congr_right fun _ ↦ ?_
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- Enlarging the finite exceptional set `S` enlarges the subalgebra of `S`-integers. -/
theorem sIntegers_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    SIntegers F S ≤ SIntegers F T :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

end SIntegers

/-- An integral model of an affine group scheme `Spec H` over `F` away from a finite set `S` of
finite places: a finitely presented commutative Hopf `𝒪_{F,S}`-algebra `coordinate` together with a
Hopf `F`-algebra isomorphism identifying its base change to `F` with `H`. -/
structure IntegralModel (F : Type u) [Field F] [NumberField F]
    (H : Type u) [CommRing H] [HopfAlgebra F H]
    (S : Finset (HeightOneSpectrum (𝓞 F))) where
  /-- The coordinate Hopf algebra over `𝒪_{F,S}`. -/
  coordinate : CommHopfAlgCat.{u} (SIntegers F S)
  /-- Finite presentation of `coordinate` over `𝒪_{F,S}`. -/
  finitePresentation : Algebra.FinitePresentation (SIntegers F S) coordinate
  /-- Generic-fibre Hopf isomorphism `F ⊗[𝒪_{F,S}] coordinate ≅ H`. -/
  baseChangeIso :
    TauCeti.CommHopfAlgCat.baseChange (K := F) coordinate ≅ CommHopfAlgCat.of F H

attribute [instance] IntegralModel.finitePresentation

namespace IntegralModel

variable {F : Type u} [Field F] [NumberField F] {H : Type u} [CommRing H] [HopfAlgebra F H]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

/-- The generic fibre `H` of an integral model is finitely presented over `F`. -/
theorem finitePresentation_base (M : IntegralModel F H S) :
    Algebra.FinitePresentation F H :=
  Algebra.FinitePresentation.equiv (_root_.CommHopfAlgCat.ofIso M.baseChangeIso).toAlgEquiv

/-- The generic fibre `H` of an integral model is of finite type over `F`. -/
theorem finiteType_base (M : IntegralModel F H S) :
    Algebra.FiniteType F H :=
  let := M.finitePresentation_base
  inferInstance

/-- The canonical `𝒪_{F,S}`-algebra map `M.coordinate →ₐ[𝒪_{F,S}] H` sending `a` to the image of
`1 ⊗ₜ a` under `M.baseChangeIso`. -/
noncomputable def toBase (M : IntegralModel F H S) : M.coordinate →ₐ[SIntegers F S] H :=
  (M.baseChangeIso.hom.hom.toAlgHom.restrictScalars (SIntegers F S)).comp
    Algebra.TensorProduct.includeRight

@[simp]
theorem toBase_apply (M : IntegralModel F H S) (a : M.coordinate) :
    M.toBase a = M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a) := by
  rw [toBase]
  rfl

section GenericFiberPoints

/-- For any commutative `F`-algebra `R` whose `𝒪_{F,S}`-algebra structure factors through `F`, the
generic-fibre isomorphism identifies `R`-points of `M.coordinate` over `𝒪_{F,S}` with `R`-points of
`H` over `F` as groups. -/
noncomputable def pointsMulEquiv (M : IntegralModel F H S) (R : Type*) [CommRing R]
    [Algebra (SIntegers F S) R] [Algebra F R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp) :
    WithConv (M.coordinate →ₐ[SIntegers F S] R) ≃* WithConv (H →ₐ[F] R) :=
  letI : @IsScalarTower (SIntegers F S) F R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  (TauCeti.AlgHom.baseChangePointsMulEquiv
    (k := SIntegers F S) (K := F) (A := M.coordinate) (R := R)).trans
    ((_root_.CommHopfAlgCat.ofIso M.baseChangeIso.symm).mapDomainMulEquiv (A := R))

@[simp]
theorem pointsMulEquiv_symm_ofConv_apply (M : IntegralModel F H S) {R : Type*} [CommRing R]
    [Algebra (SIntegers F S) R] [Algebra F R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp)
    (g : WithConv (H →ₐ[F] R)) (a : M.coordinate) :
    ((M.pointsMulEquiv R hR).symm g).ofConv a =
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) := by
  let _ : @IsScalarTower (SIntegers F S) F R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  rw [pointsMulEquiv, MulEquiv.symm_trans_apply,
    TauCeti.AlgHom.baseChangePointsMulEquiv_symm_apply, BialgEquiv.mapDomainMulEquiv_symm_apply,
    BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
  exact congrArg g.ofConv (_root_.CommHopfAlgCat.ofIso_symm_apply M.baseChangeIso.symm _)

/-- Topological group version of `pointsMulEquiv` when `R` is a topological ring. -/
noncomputable def pointsContinuousMulEquiv (M : IntegralModel F H S) (R : Type*) [CommRing R]
    [Algebra (SIntegers F S) R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp) :
    WithConv (M.coordinate →ₐ[SIntegers F S] R) ≃ₜ* WithConv (H →ₐ[F] R) :=
  letI : @IsScalarTower (SIntegers F S) F R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  (baseChangePointsContinuousMulEquiv (SIntegers F S) F M.coordinate R).trans
    ((_root_.CommHopfAlgCat.ofIso M.baseChangeIso.symm).mapDomainContinuousMulEquiv R)

@[simp]
theorem coe_pointsContinuousMulEquiv (M : IntegralModel F H S) {R : Type*} [CommRing R]
    [Algebra (SIntegers F S) R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp) :
    (M.pointsContinuousMulEquiv R hR :
      WithConv (M.coordinate →ₐ[SIntegers F S] R) ≃* WithConv (H →ₐ[F] R)) =
      M.pointsMulEquiv R hR := by
  let _ : @IsScalarTower (SIntegers F S) F R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  rw [pointsContinuousMulEquiv, pointsMulEquiv]
  exact congrArg₂ MulEquiv.trans
    (coe_baseChangePointsContinuousMulEquiv (SIntegers F S) F M.coordinate R)
    (BialgEquiv.coe_mapDomainContinuousMulEquiv R
      (_root_.CommHopfAlgCat.ofIso M.baseChangeIso.symm))

@[simp]
theorem pointsContinuousMulEquiv_symm_ofConv_apply (M : IntegralModel F H S) {R : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp)
    (g : WithConv (H →ₐ[F] R)) (a : M.coordinate) :
    ((M.pointsContinuousMulEquiv R hR).symm g).ofConv a =
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) := by
  let _ : @IsScalarTower (SIntegers F S) F R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  rw [pointsContinuousMulEquiv, ContinuousMulEquiv.symm_trans_apply,
    BialgEquiv.mapDomainContinuousMulEquiv_symm_apply,
    baseChangePointsContinuousMulEquiv_symm_apply, BialgHom.mapDomain_apply,
    ofConv_toConv, AlgHom.comp_apply]
  exact congrArg g.ofConv (_root_.CommHopfAlgCat.ofIso_symm_apply M.baseChangeIso.symm _)

/-- For a commutative `𝒪_{F,S}`-algebra `R` mapped into a commutative `F`-algebra `K` via
`ι : R →ₐ[𝒪_{F,S}] K`, `integralPointsHom` maps `R`-points of `M.coordinate` into `K`-points of `H`
via `ι` and the generic-fibre isomorphism. -/
noncomputable def integralPointsHom (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [CommRing K] [Algebra (SIntegers F S) K]
    [Algebra F K] (ι : R →ₐ[SIntegers F S] K)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp) :
    WithConv (M.coordinate →ₐ[SIntegers F S] R) →* WithConv (H →ₐ[F] K) :=
  (M.pointsMulEquiv K hK).toMonoidHom.comp (AlgHom.mapValue (H := M.coordinate) ι)

/-- When `ι : R →ₐ[𝒪_{F,S}] K` is injective, the induced homomorphism from `R`-points of
`M.coordinate` to `K`-points of `H` is injective. -/
theorem integralPointsHom_injective (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [CommRing K] [Algebra (SIntegers F S) K]
    [Algebra F K] {ι : R →ₐ[SIntegers F S] K} (hι : Function.Injective ι)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp) :
    Function.Injective (M.integralPointsHom ι hK) :=
  (M.pointsMulEquiv K hK).injective.comp (AlgHom.mapValue_injective hι)

/-- When `ι : R →ₐ[𝒪_{F,S}] K` is injective, the image of `M.integralPointsHom ι hK` consists of
the `K`-points of `H` whose values on the image of `M.coordinate` lie in `Set.range ι`. -/
theorem mem_range_integralPointsHom_iff (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [CommRing K] [Algebra (SIntegers F S) K]
    [Algebra F K] {ι : R →ₐ[SIntegers F S] K} (hι : Function.Injective ι)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp)
    {g : WithConv (H →ₐ[F] K)} :
    g ∈ (M.integralPointsHom ι hK).range ↔
      ∀ a : M.coordinate,
        g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) ∈ Set.range ι := by
  have hrng : g ∈ (M.integralPointsHom ι hK).range ↔
      (M.pointsMulEquiv K hK).symm g ∈
        MonoidHom.mrange (AlgHom.mapValue (H := M.coordinate) ι) := by
    rw [MonoidHom.mem_range, MonoidHom.mem_mrange]
    refine exists_congr fun x ↦ ?_
    rw [integralPointsHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.eq_symm_apply]
  rw [hrng, AlgHom.mem_mrange_mapValue_iff hι]
  refine forall_congr' fun a ↦ ?_
  rw [M.pointsMulEquiv_symm_ofConv_apply hK]
  rfl

/-- When `ι : R →ₐ[𝒪_{F,S}] K` is an open embedding into a topological ring `K`,
`M.integralPointsHom ι hK` is an open embedding. -/
theorem isOpenEmbedding_integralPointsHom (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [TopologicalSpace R]
    [CommRing K] [Algebra (SIntegers F S) K] [Algebra F K]
    [TopologicalSpace K] [IsTopologicalRing K]
    {ι : R →ₐ[SIntegers F S] K} (hι : IsOpenEmbedding ι)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp) :
    IsOpenEmbedding (M.integralPointsHom ι hK) := by
  have h1 := AlgHom.isOpenEmbedding_mapValue (H₁ := M.coordinate) hι
  have h2 := (M.pointsContinuousMulEquiv K hK).toHomeomorph.isOpenEmbedding
  convert h2.comp h1 using 1
  funext x
  rw [integralPointsHom, MonoidHom.comp_apply, ← M.coe_pointsContinuousMulEquiv hK]
  rfl

end GenericFiberPoints

/-! ### Local integral points and level subgroups -/

section LocalPoints

private theorem localCompletionAlgebraMap_comp (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (v.adicCompletion F)).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) (v.adicCompletion F) :=
  RingHom.ext fun _ ↦ rfl

/-- For `v ∉ S`, the valuation ring `𝒪_v` of `F_v` viewed as an `𝒪_{F,S}`-subalgebra of `F_v`. -/
noncomputable def localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    Subalgebra (SIntegers F S) (v.adicCompletion F) :=
  { (v.adicCompletionIntegers F).toSubring with
    algebraMap_mem' r := by
      have hr : algebraMap F (v.adicCompletion F) (r : F) ∈ v.adicCompletionIntegers F :=
        (mem_sIntegers_iff_forall_adicCompletionIntegers.mp r.2) v hv
      simpa [HeightOneSpectrum.algebraMap_adicCompletion] using hr }

/-- The canonical embedding `𝓗(𝒪_v) →* G(F_v)` of `𝒪_v`-points of `M.coordinate` into local points
at `v ∉ S` under the generic-fibre identification. -/
noncomputable def localIntegralHom (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    WithConv (M.coordinate →ₐ[SIntegers F S] localIntegerSubalgebra S v hv) →*
      LocalPoints F H v :=
  M.integralPointsHom (localIntegerSubalgebra S v hv).val (localCompletionAlgebraMap_comp S v)

/-- The canonical map `𝓗(𝒪_v) →* G(F_v)` is injective for every `v ∉ S`. -/
theorem localIntegralHom_injective (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    Function.Injective (M.localIntegralHom v hv) :=
  M.integralPointsHom_injective Subtype.val_injective (localCompletionAlgebraMap_comp S v)

/-- The canonical map `𝓗(𝒪_v) →* G(F_v)` is an open topological embedding for every `v ∉ S`. -/
theorem isOpenEmbedding_localIntegralHom (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    IsOpenEmbedding (M.localIntegralHom v hv) :=
  M.isOpenEmbedding_integralPointsHom
    (Valued.isOpen_valuationSubring _).isOpenEmbedding_subtypeVal
    (localCompletionAlgebraMap_comp S v)

private theorem mem_range_localIntegralHom_iff (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) {g : LocalPoints F H v} :
    g ∈ (M.localIntegralHom v hv).range ↔ ∀ a : M.coordinate,
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) ∈
        v.adicCompletionIntegers F := by
  rw [localIntegralHom,
    M.mem_range_integralPointsHom_iff Subtype.val_injective (localCompletionAlgebraMap_comp S v)]
  exact forall_congr' fun _ ↦ Subtype.range_val.symm ▸ Iff.rfl

/-- The local integral subgroup `𝓗(𝒪_v) ≤ G(F_v)` for `v ∉ S`: the subgroup of local points taking
`v`-integral values on the image of `M.coordinate`, equal to the image of the `𝒪_v`-points of
`M.coordinate`. -/
noncomputable def localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S) : Subgroup (LocalPoints F H v) :=
  Subgroup.copy (M.localIntegralHom v hv).range
    {g | ∀ a : M.coordinate,
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) ∈
        v.adicCompletionIntegers F}
    (Set.ext fun _ ↦ (mem_range_localIntegralHom_iff M v hv).symm)

/-- The range of `M.localIntegralHom v hv` is `M.localPoints v hv`. -/
@[simp]
theorem range_localIntegralHom (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S) :
    (M.localIntegralHom v hv).range = M.localPoints v hv :=
  (Subgroup.copy_eq _ _ _).symm

/-- A local point `g ∈ G(F_v)` (`v ∉ S`) lies in `M.localPoints v hv` if and only if it takes
`v`-integral values on the image of `M.coordinate` in `H`. -/
@[simp]
theorem mem_localPoints_iff (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    {g : LocalPoints F H v} :
    g ∈ M.localPoints v hv ↔ ∀ a : M.coordinate,
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) ∈
        v.adicCompletionIntegers F :=
  Iff.rfl

/-- Membership in `M.localPoints v hv` need only be checked on a generating family of
`M.coordinate` over `𝒪_{F,S}`. -/
theorem mem_localPoints_iff_of_adjoin_eq_top (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) {ι : Type*} {a : ι → M.coordinate}
    (ha : Algebra.adjoin (SIntegers F S) (Set.range a) = ⊤) {g : LocalPoints F H v} :
    g ∈ M.localPoints v hv ↔ ∀ i,
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a i)) ∈
        v.adicCompletionIntegers F := by
  rw [mem_localPoints_iff]
  have hmem : (∀ b : M.coordinate,
      ((M.pointsMulEquiv (v.adicCompletion F)
        (localCompletionAlgebraMap_comp S v)).symm g).ofConv b ∈ v.adicCompletionIntegers F) ↔
      ((M.pointsMulEquiv (v.adicCompletion F)
        (localCompletionAlgebraMap_comp S v)).symm g).ofConv ∈
        Set.range (fun x : M.coordinate →ₐ[SIntegers F S] localIntegerSubalgebra S v hv ↦
          (localIntegerSubalgebra S v hv).val.comp x) := by
    rw [AlgHom.range_comp_left_of_injective _ Subtype.val_injective, Set.mem_ofPred_eq]
    exact forall_congr' fun b ↦ ⟨fun hb ↦ ⟨⟨_, hb⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩
  simp_rw [← M.pointsMulEquiv_symm_ofConv_apply (localCompletionAlgebraMap_comp S v) g]
  rw [hmem, AlgHom.range_comp_left_eq_of_adjoin_eq_top _ Subtype.val_injective ha,
    Set.mem_ofPred_eq]
  exact forall_congr' fun i ↦ ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hi ↦ ⟨⟨_, hi⟩, rfl⟩⟩

/-- For `v ∉ S`, the local integral subgroup `M.localPoints v hv` is open in `G(F_v)`. -/
theorem isOpen_localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    IsOpen (M.localPoints v hv : Set (LocalPoints F H v)) := by
  rw [← M.range_localIntegralHom v hv]
  exact (M.isOpenEmbedding_localIntegralHom v hv).isOpen_range

/-- For `v ∉ S`, the local integral subgroup `M.localPoints v hv` is closed in `G(F_v)`. -/
theorem isClosed_localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    IsClosed (M.localPoints v hv : Set (LocalPoints F H v)) :=
  Subgroup.isClosed_of_isOpen _ (M.isOpen_localPoints v hv)

/-- For `v ∉ S`, the local integral subgroup `M.localPoints v hv` is compact in `G(F_v)`. -/
theorem isCompact_localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S) :
    IsCompact (M.localPoints v hv : Set (LocalPoints F H v)) := by
  rw [← M.range_localIntegralHom v hv]
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    HeightOneSpectrum.isNonarchimedeanLocalField_adicCompletion v
  have : CompactSpace (v.adicCompletionIntegers F) :=
    HeightOneSpectrum.compactSpace_adicCompletionIntegers v
  have : CompactSpace (localIntegerSubalgebra S v hv) :=
    inferInstanceAs <| CompactSpace (v.adicCompletionIntegers F)
  exact isCompact_range (M.isOpenEmbedding_localIntegralHom v hv).continuous

open scoped Classical in
/-- The reference level subgroup at `v`: `⊤` if `v ∈ S`, and `M.localPoints v hv` if `v ∉ S`. -/
noncomputable def level (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (LocalPoints F H v) :=
  if hv : v ∈ S then ⊤ else M.localPoints v hv

@[simp]
theorem level_of_mem (M : IntegralModel F H S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    M.level v = ⊤ := by
  simp [level, hv]

@[simp]
theorem level_of_notMem (M : IntegralModel F H S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    M.level v = M.localPoints v hv := by
  simp [level, hv]

/-- Every reference subgroup `M.level v` is open in `G(F_v)`. -/
theorem isOpen_level (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (M.level v : Set (LocalPoints F H v)) := by
  by_cases hv : v ∈ S
  · rw [M.level_of_mem hv, Subgroup.coe_top]
    exact isOpen_univ
  · rw [M.level_of_notMem hv]
    exact M.isOpen_localPoints v hv

/-- Typeclass wrapper recording that every reference subgroup `M.level v` is open, enabling
restricted-product topology instances on `Πʳ v, [LocalPoints F H v, M.level v]`. -/
instance fact_isOpen_level (M : IntegralModel F H S) :
    Fact (∀ v : HeightOneSpectrum (𝓞 F), IsOpen (M.level v : Set (LocalPoints F H v))) :=
  ⟨M.isOpen_level⟩

/-- Every reference subgroup `M.level v` is closed in `G(F_v)`. -/
theorem isClosed_level (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) :
    IsClosed (M.level v : Set (LocalPoints F H v)) :=
  Subgroup.isClosed_of_isOpen _ (M.isOpen_level v)

/-- Outside `S`, the reference subgroup `M.level v` is compact in `G(F_v)`. -/
theorem isCompact_level_of_notMem (M : IntegralModel F H S) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) :
    IsCompact (M.level v : Set (LocalPoints F H v)) := by
  rw [M.level_of_notMem hv]
  exact M.isCompact_localPoints v hv

end LocalPoints

/-! ### Global `T`-integral points and local-global characterization -/

section GlobalPoints

/-- For `S ⊆ T`, `𝒪_{F,T}` viewed as an `𝒪_{F,S}`-subalgebra of `F`. -/
noncomputable def sIntegersSubalgebra {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) : Subalgebra (SIntegers F S) F :=
  { (SIntegers F T).toSubring with
    algebraMap_mem' r := sIntegers_mono hST r.2 }

/-- The canonical embedding `𝓗(𝒪_{F,T}) →* G(F)` of `𝒪_{F,T}`-points of `M.coordinate` into
`F`-rational points for `S ⊆ T` under the generic-fibre identification. -/
noncomputable def globalIntegralHom (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    WithConv (M.coordinate →ₐ[SIntegers F S] sIntegersSubalgebra hST) →*
      WithConv (H →ₐ[F] F) :=
  M.integralPointsHom (sIntegersSubalgebra hST).val (RingHom.id_comp _)

/-- The canonical map `𝓗(𝒪_{F,T}) →* G(F)` is injective for every `T ⊇ S`. -/
theorem globalIntegralHom_injective (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    Function.Injective (M.globalIntegralHom T hST) :=
  M.integralPointsHom_injective Subtype.val_injective (RingHom.id_comp _)

private theorem mem_range_globalIntegralHom_iff (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ (M.globalIntegralHom T hST).range ↔ ∀ a : M.coordinate,
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) ∈ SIntegers F T := by
  rw [globalIntegralHom,
    M.mem_range_integralPointsHom_iff Subtype.val_injective (RingHom.id_comp _)]
  exact forall_congr' fun _ ↦ Subtype.range_val.symm ▸ Iff.rfl

/-- The subgroup `Γ(M, T) ≤ G(F)` of `T`-integral rational points for `S ⊆ T`: the subgroup of
rational points taking `𝒪_{F,T}`-values on `M.coordinate`, equal to the image of the
`𝒪_{F,T}`-points of `M.coordinate` in `G(F)`. -/
noncomputable def globalPoints (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    Subgroup (WithConv (H →ₐ[F] F)) :=
  Subgroup.copy (M.globalIntegralHom T hST).range
    {g | ∀ a : M.coordinate,
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) ∈ SIntegers F T}
    (Set.ext fun _ ↦ (mem_range_globalIntegralHom_iff M T hST).symm)

/-- The range of `M.globalIntegralHom T hST` is `M.globalPoints T hST`. -/
@[simp]
theorem range_globalIntegralHom (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    (M.globalIntegralHom T hST).range = M.globalPoints T hST :=
  (Subgroup.copy_eq _ _ _).symm

/-- A rational point `g ∈ G(F)` lies in `M.globalPoints T hST` if and only if its values on the
image of `M.coordinate` lie in `𝒪_{F,T}`. -/
@[simp]
theorem mem_globalPoints_iff (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔ ∀ a : M.coordinate,
      g.ofConv (M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a)) ∈ SIntegers F T :=
  Iff.rfl

/-- Enlarging the finite set of places `T` enlarges the subgroup of `T`-integral rational points. -/
theorem globalPoints_mono (M : IntegralModel F H S)
    {T U : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) (hTU : T ⊆ U) :
    M.globalPoints T hST ≤ M.globalPoints U (hST.trans hTU) := by
  intro g hg a
  exact sIntegers_mono hTU (hg a)

/-- **Local-global characterization of `T`-integral rational points**: for `S ⊆ T`, a rational point
`g ∈ G(F)` lies in `M.globalPoints T hST` if and only if its local image at every `v ∉ T` lies in
`M.localPoints v _`. -/
theorem mem_globalPoints_iff_forall_localPoints (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔
      ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T),
        localDiagonal v g ∈ M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_globalPoints_iff, mem_sIntegers_iff_forall_adicCompletionIntegers,
    mem_localPoints_iff, localDiagonal_ofConv_apply]
  exact ⟨fun h v hv a ↦ h a v hv, fun h a v hv ↦ h v hv a⟩

/-- Equivalent adelic form of `mem_globalPoints_iff_forall_localPoints`: `g ∈ M.globalPoints T hST`
if and only if `localProjection v (diagonal g) ∈ M.level v` for every `v ∉ T`. -/
theorem mem_globalPoints_iff_forall_level (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔
      ∀ v ∉ T, localProjection v (diagonal g) ∈ M.level v := by
  rw [M.mem_globalPoints_iff_forall_localPoints hST]
  refine forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_
  rw [localProjection_diagonal, M.level_of_notMem (fun hvS ↦ hv (hST hvS))]

end GlobalPoints

/-! ### Enlarging the exceptional set of places -/

section Enlarge

@[instance_reducible]
private noncomputable def sIntegersAlgebraOfSubset {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) : Algebra (SIntegers F S) (SIntegers F T) :=
  (Subalgebra.inclusion (sIntegers_mono hST)).toAlgebra

private theorem sIntegersTowerOfSubset {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) :
    @IsScalarTower (SIntegers F S) (SIntegers F T) F
      (sIntegersAlgebraOfSubset hST).toSMul Algebra.toSMul Algebra.toSMul :=
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  IsScalarTower.of_algebraMap_eq' rfl

/-- Base change of an integral model `M` away from `S` to an integral model away from `T` for
`S ⊆ T`, obtained by extending scalars of `M.coordinate` along `𝒪_{F,S} → 𝒪_{F,T}`. -/
noncomputable def enlarge (M : IntegralModel F H S) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) : IntegralModel F H T where
  coordinate :=
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    TauCeti.CommHopfAlgCat.baseChange (K := SIntegers F T) M.coordinate
  finitePresentation :=
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    inferInstance
  baseChangeIso :=
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    letI := sIntegersTowerOfSubset hST
    TauCeti.CommHopfAlgCat.baseChangeTowerIso (SIntegers F S) F M.coordinate ≪≫
      M.baseChangeIso

/-- Enlarging the exceptional set from `S` to `T` does not change the local integral subgroup at
any place `v ∉ T`. -/
@[simp]
theorem localPoints_enlarge (M : IntegralModel F H S) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
    (M.enlarge hST).localPoints v hv = M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  ext g
  rw [enlarge]
  simp only [mem_localPoints_iff, Iso.trans_hom, CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
  constructor
  · intro hg a
    have h := hg ((1 : SIntegers F T) ⊗ₜ[SIntegers F S] a)
    rwa [TauCeti.CommHopfAlgCat.baseChangeTowerIso_hom_apply, one_smul] at h
  · intro hg (b : SIntegers F T ⊗[SIntegers F S] M.coordinate)
    induction b using TensorProduct.inductionOn with
    | tmul r a =>
      have hr : algebraMap F (v.adicCompletion F) (r : F) ∈ v.adicCompletionIntegers F :=
        (mem_sIntegers_iff_forall_adicCompletionIntegers.mp r.2) v hv
      have htower :
          (TauCeti.CommHopfAlgCat.baseChangeTowerIso (SIntegers F S) F M.coordinate).hom.hom
            ((1 : F) ⊗ₜ[SIntegers F T] (r ⊗ₜ[SIntegers F S] a)) =
          (r : F) • ((1 : F) ⊗ₜ[SIntegers F S] a) := by
        rw [TauCeti.CommHopfAlgCat.baseChangeTowerIso_hom_apply, TensorProduct.smul_tmul']
        congr 1
      rw [htower, map_smul, map_smul, Algebra.smul_def]
      exact mul_mem hr (hg a)
    | add x y hx hy =>
      simp only [tmul_add, map_add]
      exact add_mem hx hy

theorem level_enlarge_of_notMem (M : IntegralModel F H S) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T) :
    (M.enlarge hST).level v = M.level v := by
  rw [(M.enlarge hST).level_of_notMem hv, M.level_of_notMem (fun hvS ↦ hv (hST hvS)),
    M.localPoints_enlarge hST v hv]

/-- Enlarging `S` to `T` leaves `level v` unchanged at all but finitely many places. -/
theorem eventually_level_enlarge_eq (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    ∀ᶠ v in Filter.cofinite, (M.enlarge hST).level v = M.level v := by
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact M.level_enlarge_of_notMem hST hv

/-- Enlarging the exceptional set from `S` to `T` preserves global `U`-integral points for every
`U ⊇ T`. -/
@[simp]
theorem globalPoints_enlarge (M : IntegralModel F H S) {T U : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (hTU : T ⊆ U) :
    (M.enlarge hST).globalPoints U hTU = M.globalPoints U (hST.trans hTU) := by
  ext g
  simp only [mem_globalPoints_iff_forall_localPoints, M.localPoints_enlarge hST]

end Enlarge

end IntegralModel

end TauCeti
