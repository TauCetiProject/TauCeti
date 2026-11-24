/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.NumberTheory.NumberField.SInteger.Completion
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.Topology.Algebra.PointTopology.BaseChange

/-!
# Integral models of affine group schemes away from a finite set of places

Let `F` be a number field, `H` a commutative Hopf `F`-algebra representing an affine group scheme
`G = Spec H` over `F`, and `S` a finite set of height-one primes of `𝓞 F`. An *integral model* of
`G` away from `S` (`TauCeti.IntegralModel F H S`) consists of a finitely presented commutative Hopf
algebra `M.coordinate` over the ring of `S`-integers `𝒪_{F,S} = SIntegers F S` together with an
isomorphism of commutative Hopf `F`-algebras identifying `F ⊗[𝒪_{F,S}] M.coordinate` with `H`.

Working directly with an integral Hopf model over `𝒪_{F,S}` avoids choosing an auxiliary closed
immersion into `GL_n`: for every finite place `v ∉ S`, the `𝒪_v`-points of `M.coordinate` supply a
canonical compact open subgroup `M.localPoints v hv ≤ LocalPoints (𝓞 F) F H v`, assembling into the
reference level family `M.level` used in
`TauCeti.NumberTheory.NumberField.Global.AdelicPoints.RestrictedProduct` to realize `G(𝔸_{F,f})` as
a restricted product and to define `T`-arithmetic subgroups `M.globalPoints T hST ≤ G(F)`.

From an integral model `M` away from `S`, this file constructs and characterizes:

* **Local integral points** `M.localPoints v hv ≤ LocalPoints (𝓞 F) F H v` for `v ∉ S`: the image
  of the `𝒪_v`-points of `M.coordinate` under the generic-fibre identification, characterized by
  integrality on `M.toBase` (or on any generating family of `M.coordinate` over `𝒪_{F,S}`), and
  proved to be a **compact open** (hence closed) subgroup of `LocalPoints (𝓞 F) F H v`.
* **Reference level subgroups** `M.level v ≤ LocalPoints (𝓞 F) F H v`: `⊤` at `v ∈ S` and
  `M.localPoints v hv` at `v ∉ S`, open at every finite place and compact outside `S`.
* **Global `T`-integral points** `M.globalPoints T hST ≤ WithConv (H →ₐ[F] F)` for `S ⊆ T`: the
  `F`-rational points integral on `M.coordinate` away from `T`, proved equal to the rational points
  whose local projections at all `v ∉ T` lie in `M.localPoints v _`.
* **Base change to a larger exceptional set** `M.enlarge hST : IntegralModel F H T`: scalar
  extension of `M.coordinate` from `𝒪_{F,S}` to `𝒪_{F,T}`, preserving local integral subgroups away
  from `T` and global `U`-integral subgroups for `T ⊆ U`.

## Main declarations

* `TauCeti.IntegralModel`: bundled integral model of `Spec H` over `𝒪_{F,S}`.
* `TauCeti.IntegralModel.integralPointsHom`, `TauCeti.IntegralModel.localIntegralHom`,
  `TauCeti.IntegralModel.globalIntegralHom`: group homomorphisms from points of `M.coordinate` into
  generic-fibre points (injective whenever the coefficient map is injective, in particular for
  `localIntegralHom` and `globalIntegralHom`).
* `TauCeti.IntegralModel.localPoints`, `TauCeti.IntegralModel.mem_localPoints_iff`,
  `TauCeti.IntegralModel.isOpen_localPoints`, `TauCeti.IntegralModel.isCompact_localPoints`: local
  integral subgroups away from `S` are compact open subgroups.
* `TauCeti.IntegralModel.level`, `TauCeti.IntegralModel.isOpen_level`,
  `TauCeti.IntegralModel.fact_isOpen_level`: the place-by-place reference family for the restricted
  product.
* `TauCeti.IntegralModel.globalPoints`,
  `TauCeti.IntegralModel.mem_globalPoints_iff_forall_localPoints`: global `T`-integral points and
  their local-global characterization.
* `TauCeti.IntegralModel.enlarge`, `TauCeti.IntegralModel.enlargeCoordinateIso`,
  `TauCeti.IntegralModel.enlarge_baseChangeIso_hom_tmul`,
  `TauCeti.IntegralModel.enlarge_toBase_tmul`: base change of an integral model from `S` to
  `T ⊇ S` and its coordinate identification.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Thms. 3.4 and 3.6, Rem. 3.5, pp. 5–6.
* J. S. Milne, *Introduction to Shimura varieties*, §4, pp. 42–43.
-/

public section

open CategoryTheory IsDedekindDomain NumberField TensorProduct Topology WithConv
open TauCeti.AdelicPoints TauCeti.AlgHom TauCeti.PointTopology

namespace TauCeti

universe u

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
  (AlgHom.liftEquiv (SIntegers F S) F M.coordinate H).symm M.baseChangeIso.hom.hom.toAlgHom

theorem toBase_apply (M : IntegralModel F H S) (a : M.coordinate) :
    M.toBase a = M.baseChangeIso.hom.hom ((1 : F) ⊗ₜ[SIntegers F S] a) := by
  simp [toBase]

/-- `M.baseChangeIso.hom` maps a pure tensor `c ⊗ₜ a` to `c • M.toBase a`. -/
@[simp]
theorem baseChangeIso_hom_tmul (M : IntegralModel F H S) (c : F) (a : M.coordinate) :
    M.baseChangeIso.hom.hom (c ⊗ₜ[SIntegers F S] a) = c • M.toBase a := by
  have hc : c ⊗ₜ[SIntegers F S] a = c • ((1 : F) ⊗ₜ[SIntegers F S] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hc, map_smul, M.toBase_apply]

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
    ((M.pointsMulEquiv R hR).symm g).ofConv a = g.ofConv (M.toBase a) := by
  let _ : @IsScalarTower (SIntegers F S) F R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  have hbase : (_root_.CommHopfAlgCat.ofIso M.baseChangeIso.symm).symm
      ((1 : F) ⊗ₜ[SIntegers F S] a) = M.toBase a := by
    rw [M.toBase_apply]
    exact _root_.CommHopfAlgCat.ofIso_symm_apply M.baseChangeIso.symm _
  simp [pointsMulEquiv, hbase]

@[simp]
theorem pointsMulEquiv_ofConv_toBase (M : IntegralModel F H S) {R : Type*} [CommRing R]
    [Algebra (SIntegers F S) R] [Algebra F R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp)
    (x : WithConv (M.coordinate →ₐ[SIntegers F S] R)) (a : M.coordinate) :
    (M.pointsMulEquiv R hR x).ofConv (M.toBase a) = x.ofConv a := by
  have hx := M.pointsMulEquiv_symm_ofConv_apply hR (M.pointsMulEquiv R hR x) a
  rwa [MulEquiv.symm_apply_apply, eq_comm] at hx

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

theorem pointsContinuousMulEquiv_apply (M : IntegralModel F H S) {R : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp)
    (x : WithConv (M.coordinate →ₐ[SIntegers F S] R)) :
    M.pointsContinuousMulEquiv R hR x = M.pointsMulEquiv R hR x := by
  let _ : @IsScalarTower (SIntegers F S) F R Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' hR.symm
  apply ofConv_injective
  simp [pointsContinuousMulEquiv, pointsMulEquiv]

@[simp]
theorem pointsContinuousMulEquiv_symm_ofConv_apply (M : IntegralModel F H S) {R : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp)
    (g : WithConv (H →ₐ[F] R)) (a : M.coordinate) :
    ((M.pointsContinuousMulEquiv R hR).symm g).ofConv a = g.ofConv (M.toBase a) := by
  have hsymm : (M.pointsContinuousMulEquiv R hR).symm g = (M.pointsMulEquiv R hR).symm g :=
    (M.pointsContinuousMulEquiv R hR).symm_apply_eq.mpr <| by
      rw [M.pointsContinuousMulEquiv_apply hR, MulEquiv.apply_symm_apply]
  rw [hsymm, M.pointsMulEquiv_symm_ofConv_apply hR]

@[simp]
theorem pointsContinuousMulEquiv_ofConv_toBase (M : IntegralModel F H S) {R : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R]
    (hR : (algebraMap F R).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) R := by ext; simp)
    (x : WithConv (M.coordinate →ₐ[SIntegers F S] R)) (a : M.coordinate) :
    (M.pointsContinuousMulEquiv R hR x).ofConv (M.toBase a) = x.ofConv a := by
  rw [M.pointsContinuousMulEquiv_apply hR, M.pointsMulEquiv_ofConv_toBase hR]

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

theorem integralPointsHom_apply (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [CommRing K] [Algebra (SIntegers F S) K]
    [Algebra F K] (ι : R →ₐ[SIntegers F S] K)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp)
    (x : WithConv (M.coordinate →ₐ[SIntegers F S] R)) :
    M.integralPointsHom ι hK x = M.pointsMulEquiv K hK (AlgHom.mapValue ι x) := by
  rw [integralPointsHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

@[simp]
theorem integralPointsHom_ofConv_toBase (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [CommRing K] [Algebra (SIntegers F S) K]
    [Algebra F K] (ι : R →ₐ[SIntegers F S] K)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp)
    (x : WithConv (M.coordinate →ₐ[SIntegers F S] R)) (a : M.coordinate) :
    (M.integralPointsHom ι hK x).ofConv (M.toBase a) = ι (x.ofConv a) := by
  rw [M.integralPointsHom_apply ι hK, M.pointsMulEquiv_ofConv_toBase hK,
    AlgHom.mapValue_apply, AlgHom.comp_apply]

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
the `K`-points of `H` whose values on `M.toBase` lie in `Set.range ι`. -/
theorem mem_range_integralPointsHom_iff (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [CommRing K] [Algebra (SIntegers F S) K]
    [Algebra F K] {ι : R →ₐ[SIntegers F S] K} (hι : Function.Injective ι)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp)
    {g : WithConv (H →ₐ[F] K)} :
    g ∈ (M.integralPointsHom ι hK).range ↔
      ∀ a : M.coordinate, g.ofConv (M.toBase a) ∈ Set.range ι := by
  have hrng : g ∈ (M.integralPointsHom ι hK).range ↔
      (M.pointsMulEquiv K hK).symm g ∈
        MonoidHom.mrange (AlgHom.mapValue (H := M.coordinate) ι) := by
    rw [MonoidHom.mem_range, MonoidHom.mem_mrange]
    refine exists_congr fun x ↦ ?_
    rw [M.integralPointsHom_apply ι hK, MulEquiv.eq_symm_apply]
  rw [hrng, AlgHom.mem_mrange_mapValue_iff hι]
  exact forall_congr' fun a ↦ by
    rw [M.pointsMulEquiv_symm_ofConv_apply hK, ← SetLike.mem_coe, AlgHom.coe_range]

/-- Membership in `(M.integralPointsHom ι hK).range` for an injective `ι` need only be checked on a
generating family of `M.coordinate` over `𝒪_{F,S}`. -/
theorem mem_range_integralPointsHom_iff_of_adjoin_eq_top (M : IntegralModel F H S) {R K : Type*}
    [CommRing R] [Algebra (SIntegers F S) R] [CommRing K] [Algebra (SIntegers F S) K]
    [Algebra F K] {ι : R →ₐ[SIntegers F S] K} (hι : Function.Injective ι)
    (hK : (algebraMap F K).comp (algebraMap (SIntegers F S) F) =
      algebraMap (SIntegers F S) K := by ext; simp)
    {J : Type*} {a : J → M.coordinate}
    (ha : Algebra.adjoin (SIntegers F S) (Set.range a) = ⊤)
    {g : WithConv (H →ₐ[F] K)} :
    g ∈ (M.integralPointsHom ι hK).range ↔
      ∀ j, g.ofConv (M.toBase (a j)) ∈ Set.range ι := by
  rw [M.mem_range_integralPointsHom_iff hι hK]
  simp_rw [← M.pointsMulEquiv_symm_ofConv_apply hK g]
  have hmem : (∀ b : M.coordinate,
      ((M.pointsMulEquiv K hK).symm g).ofConv b ∈ Set.range ι) ↔
      ((M.pointsMulEquiv K hK).symm g).ofConv ∈
        Set.range (fun x : M.coordinate →ₐ[SIntegers F S] R ↦ ι.comp x) := by
    rw [AlgHom.range_comp_left_of_injective _ hι, Set.mem_ofPred_eq]
  rw [hmem, AlgHom.range_comp_left_eq_of_adjoin_eq_top _ hι ha, Set.mem_ofPred_eq]

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
  have h2 := (Homeomorph.ofClass (M.pointsContinuousMulEquiv K hK)).isOpenEmbedding
  convert h2.comp h1 using 1
  funext x
  rw [Function.comp_apply, Homeomorph.coe_ofClass, M.integralPointsHom_apply ι hK,
    M.pointsContinuousMulEquiv_apply hK]

end GenericFiberPoints

/-! ### Local integral points and level subgroups -/

section LocalPoints

/-- For `v ∉ S`, the valuation ring `𝒪_v` of `F_v` viewed as an `𝒪_{F,S}`-subalgebra of `F_v`. -/
noncomputable def localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    Subalgebra (SIntegers F S) (v.adicCompletion F) :=
  { (v.adicCompletionIntegers F).toSubring with
    algebraMap_mem' r := by
      rw [IsScalarTower.algebraMap_apply (SIntegers F S) F (v.adicCompletion F)]
      exact (mem_sIntegers_iff_forall_adicCompletionIntegers.mp r.property) v hv }

@[simp]
theorem toSubring_localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    (localIntegerSubalgebra S v hv).toSubring = (v.adicCompletionIntegers F).toSubring := by
  rw [localIntegerSubalgebra]

@[simp]
theorem mem_localIntegerSubalgebra_iff (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) {x : v.adicCompletion F} :
    x ∈ localIntegerSubalgebra S v hv ↔ x ∈ v.adicCompletionIntegers F :=
  Iff.rfl

@[simp]
theorem coe_localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    (localIntegerSubalgebra S v hv : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Set.ext fun _ ↦ mem_localIntegerSubalgebra_iff S v hv

/-- For `v ∉ S`, `localIntegerSubalgebra S v hv` is compact in the `v`-adic topology. -/
instance compactSpace_localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    CompactSpace (localIntegerSubalgebra S v hv) := by
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    HeightOneSpectrum.isNonarchimedeanLocalField_adicCompletion v
  have : CompactSpace (v.adicCompletionIntegers F) :=
    HeightOneSpectrum.compactSpace_adicCompletionIntegers v
  exact (Homeomorph.setCongr (coe_localIntegerSubalgebra S v hv).symm).compactSpace

/-- The canonical embedding `𝓗(𝒪_v) →* G(F_v)` of `𝒪_v`-points of `M.coordinate` into local points
at `v ∉ S` under the generic-fibre identification. -/
noncomputable def localIntegralHom (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    WithConv (M.coordinate →ₐ[SIntegers F S] localIntegerSubalgebra S v hv) →*
      LocalPoints (𝓞 F) F H v :=
  M.integralPointsHom (localIntegerSubalgebra S v hv).val
    (IsScalarTower.algebraMap_eq (SIntegers F S) F (v.adicCompletion F)).symm

theorem localIntegralHom_def (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    M.localIntegralHom v hv =
      M.integralPointsHom (localIntegerSubalgebra S v hv).val
        (IsScalarTower.algebraMap_eq (SIntegers F S) F (v.adicCompletion F)).symm := by
  rw [localIntegralHom]

@[simp]
theorem localIntegralHom_ofConv_toBase (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    (x : WithConv (M.coordinate →ₐ[SIntegers F S] localIntegerSubalgebra S v hv))
    (a : M.coordinate) :
    (M.localIntegralHom v hv x).ofConv (M.toBase a) = (x.ofConv a : v.adicCompletion F) := by
  rw [M.localIntegralHom_def, M.integralPointsHom_ofConv_toBase
    (localIntegerSubalgebra S v hv).val
    (IsScalarTower.algebraMap_eq (SIntegers F S) F (v.adicCompletion F)).symm, Subalgebra.coe_val]

/-- The canonical map `𝓗(𝒪_v) →* G(F_v)` is injective for every `v ∉ S`. -/
theorem localIntegralHom_injective (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    Function.Injective (M.localIntegralHom v hv) :=
  M.integralPointsHom_injective Subtype.val_injective
    (IsScalarTower.algebraMap_eq (SIntegers F S) F (v.adicCompletion F)).symm

/-- The canonical map `𝓗(𝒪_v) →* G(F_v)` is an open topological embedding for every `v ∉ S`. -/
theorem isOpenEmbedding_localIntegralHom (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    IsOpenEmbedding (M.localIntegralHom v hv) := by
  have hopen : IsOpen (localIntegerSubalgebra S v hv : Set (v.adicCompletion F)) := by
    rw [coe_localIntegerSubalgebra]
    exact Valued.isOpen_valuationSubring _
  refine M.isOpenEmbedding_integralPointsHom ?_
    (IsScalarTower.algebraMap_eq (SIntegers F S) F (v.adicCompletion F)).symm
  rw [Subalgebra.coe_val]
  exact hopen.isOpenEmbedding_subtypeVal

private theorem mem_range_localIntegralHom_iff (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) {g : LocalPoints (𝓞 F) F H v} :
    g ∈ (M.localIntegralHom v hv).range ↔
      ∀ a : M.coordinate, g.ofConv (M.toBase a) ∈ v.adicCompletionIntegers F := by
  rw [M.localIntegralHom_def, M.mem_range_integralPointsHom_iff Subtype.val_injective
    (IsScalarTower.algebraMap_eq (SIntegers F S) F (v.adicCompletion F)).symm]
  simp [Subalgebra.coe_val]

/-- The local integral subgroup `𝓗(𝒪_v) ≤ G(F_v)` for `v ∉ S`: the subgroup of local points taking
`v`-integral values on `M.toBase`, equal to the image of the `𝒪_v`-points of `M.coordinate`. -/
noncomputable def localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S) : Subgroup (LocalPoints (𝓞 F) F H v) :=
  Subgroup.copy (M.localIntegralHom v hv).range
    {g | ∀ a : M.coordinate, g.ofConv (M.toBase a) ∈ v.adicCompletionIntegers F}
    (Set.ext fun _ ↦ (mem_range_localIntegralHom_iff M v hv).symm)

/-- The range of `M.localIntegralHom v hv` is `M.localPoints v hv`. -/
@[simp]
theorem range_localIntegralHom (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S) :
    (M.localIntegralHom v hv).range = M.localPoints v hv :=
  (Subgroup.copy_eq _ _ _).symm

/-- A local point `g ∈ G(F_v)` (`v ∉ S`) lies in `M.localPoints v hv` if and only if it takes
`v`-integral values on `M.toBase`. -/
@[simp]
theorem mem_localPoints_iff (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
    {g : LocalPoints (𝓞 F) F H v} :
    g ∈ M.localPoints v hv ↔
      ∀ a : M.coordinate, g.ofConv (M.toBase a) ∈ v.adicCompletionIntegers F :=
  Iff.rfl

/-- Membership in `M.localPoints v hv` need only be checked on a generating family of
`M.coordinate` over `𝒪_{F,S}`. -/
theorem mem_localPoints_iff_of_adjoin_eq_top (M : IntegralModel F H S)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) {ι : Type*} {a : ι → M.coordinate}
    (ha : Algebra.adjoin (SIntegers F S) (Set.range a) = ⊤) {g : LocalPoints (𝓞 F) F H v} :
    g ∈ M.localPoints v hv ↔
      ∀ i, g.ofConv (M.toBase (a i)) ∈ v.adicCompletionIntegers F := by
  rw [← M.range_localIntegralHom v hv, M.localIntegralHom_def,
    M.mem_range_integralPointsHom_iff_of_adjoin_eq_top Subtype.val_injective
      (IsScalarTower.algebraMap_eq (SIntegers F S) F (v.adicCompletion F)).symm ha]
  simp [Subalgebra.coe_val]

/-- Since `M.coordinate` is finitely generated over `𝒪_{F,S}`, there is a single finite set `s` of
coordinates testing membership in `M.localPoints v hv` simultaneously for every `v ∉ S`. -/
theorem exists_finset_forall_mem_localPoints_iff (M : IntegralModel F H S) :
    ∃ s : Finset M.coordinate, ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S)
      (g : LocalPoints (𝓞 F) F H v),
      g ∈ M.localPoints v hv ↔
        ∀ a ∈ s, g.ofConv (M.toBase a) ∈ v.adicCompletionIntegers F := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := SIntegers F S) (A := M.coordinate)
  refine ⟨s, fun v hv g ↦ ?_⟩
  rw [M.mem_localPoints_iff_of_adjoin_eq_top v hv (a := ((↑) : s → M.coordinate))
    (by simpa using hs), Subtype.forall]

/-- For `v ∉ S`, the local integral subgroup `M.localPoints v hv` is open in `G(F_v)`. -/
theorem isOpen_localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    IsOpen (M.localPoints v hv : Set (LocalPoints (𝓞 F) F H v)) := by
  rw [← M.range_localIntegralHom v hv]
  exact (M.isOpenEmbedding_localIntegralHom v hv).isOpen_range

/-- For `v ∉ S`, the local integral subgroup `M.localPoints v hv` is closed in `G(F_v)`. -/
theorem isClosed_localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    IsClosed (M.localPoints v hv : Set (LocalPoints (𝓞 F) F H v)) :=
  Subgroup.isClosed_of_isOpen _ (M.isOpen_localPoints v hv)

/-- For `v ∉ S`, the local integral subgroup `M.localPoints v hv` is compact in `G(F_v)`. -/
theorem isCompact_localPoints (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S) :
    IsCompact (M.localPoints v hv : Set (LocalPoints (𝓞 F) F H v)) := by
  rw [← M.range_localIntegralHom v hv]
  exact isCompact_range (M.isOpenEmbedding_localIntegralHom v hv).continuous

open scoped Classical in
/-- The reference level subgroup at `v`: `⊤` if `v ∈ S`, and `M.localPoints v hv` if `v ∉ S`. -/
noncomputable def level (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (LocalPoints (𝓞 F) F H v) :=
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
    IsOpen (M.level v : Set (LocalPoints (𝓞 F) F H v)) := by
  by_cases hv : v ∈ S
  · rw [M.level_of_mem hv, Subgroup.coe_top]
    exact isOpen_univ
  · rw [M.level_of_notMem hv]
    exact M.isOpen_localPoints v hv

/-- Typeclass wrapper recording that every reference subgroup `M.level v` is open, enabling
restricted-product topology instances on `Πʳ v, [LocalPoints (𝓞 F) F H v, M.level v]`. -/
instance fact_isOpen_level (M : IntegralModel F H S) :
    Fact (∀ v : HeightOneSpectrum (𝓞 F), IsOpen (M.level v : Set (LocalPoints (𝓞 F) F H v))) :=
  ⟨M.isOpen_level⟩

/-- Every reference subgroup `M.level v` is closed in `G(F_v)`. -/
theorem isClosed_level (M : IntegralModel F H S) (v : HeightOneSpectrum (𝓞 F)) :
    IsClosed (M.level v : Set (LocalPoints (𝓞 F) F H v)) :=
  Subgroup.isClosed_of_isOpen _ (M.isOpen_level v)

/-- Outside `S`, the reference subgroup `M.level v` is compact in `G(F_v)`. -/
theorem isCompact_level_of_notMem (M : IntegralModel F H S) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) :
    IsCompact (M.level v : Set (LocalPoints (𝓞 F) F H v)) := by
  rw [M.level_of_notMem hv]
  exact M.isCompact_localPoints v hv

end LocalPoints

/-! ### Global `T`-integral points and local-global characterization -/

section GlobalPoints

/-- The canonical embedding `𝓗(𝒪_{F,T}) →* G(F)` of `𝒪_{F,T}`-points of `M.coordinate` into
`F`-rational points for `S ⊆ T` under the generic-fibre identification. -/
noncomputable def globalIntegralHom (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    WithConv (M.coordinate →ₐ[SIntegers F S] SIntegers F T) →*
      WithConv (H →ₐ[F] F) :=
  letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  letI := sIntegersTowerOfSubset hST
  M.integralPointsHom (IsScalarTower.toAlgHom (SIntegers F S) (SIntegers F T) F)
    (IsScalarTower.algebraMap_eq (SIntegers F S) F F).symm

theorem globalIntegralHom_def (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    M.globalIntegralHom T hST =
      (letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
       letI := sIntegersTowerOfSubset hST
       M.integralPointsHom (IsScalarTower.toAlgHom (SIntegers F S) (SIntegers F T) F)
         (IsScalarTower.algebraMap_eq (SIntegers F S) F F).symm) := by
  rw [globalIntegralHom]

@[simp]
theorem globalIntegralHom_ofConv_toBase (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T)
    (x :
      letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
      WithConv (M.coordinate →ₐ[SIntegers F S] SIntegers F T))
    (a : M.coordinate) :
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    (M.globalIntegralHom T hST x).ofConv (M.toBase a) = (x.ofConv a : F) := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  rw [M.globalIntegralHom_def, M.integralPointsHom_ofConv_toBase
    (IsScalarTower.toAlgHom (SIntegers F S) (SIntegers F T) F)
    (IsScalarTower.algebraMap_eq (SIntegers F S) F F).symm]
  simp [IsScalarTower.coe_toAlgHom']

/-- The canonical map `𝓗(𝒪_{F,T}) →* G(F)` is injective for every `T ⊇ S`. -/
theorem globalIntegralHom_injective (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    Function.Injective (M.globalIntegralHom T hST) := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  refine M.integralPointsHom_injective ?_ (IsScalarTower.algebraMap_eq (SIntegers F S) F F).symm
  rw [IsScalarTower.coe_toAlgHom']
  intro x y h
  exact Subtype.ext h

private theorem mem_range_globalIntegralHom_iff (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ (M.globalIntegralHom T hST).range ↔
      ∀ a : M.coordinate, g.ofConv (M.toBase a) ∈ SIntegers F T := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  have hinj : Function.Injective (IsScalarTower.toAlgHom (SIntegers F S) (SIntegers F T) F) := by
    rw [IsScalarTower.coe_toAlgHom']
    intro x y h
    exact Subtype.ext h
  rw [M.globalIntegralHom_def, M.mem_range_integralPointsHom_iff hinj
    (IsScalarTower.algebraMap_eq (SIntegers F S) F F).symm]
  simp [IsScalarTower.coe_toAlgHom']

/-- The subgroup `Γ(M, T) ≤ G(F)` of `T`-integral rational points for `S ⊆ T`: the subgroup of
rational points taking `𝒪_{F,T}`-values on `M.toBase`, equal to the image of the `𝒪_{F,T}`-points
of `M.coordinate` in `G(F)`. -/
noncomputable def globalPoints (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    Subgroup (WithConv (H →ₐ[F] F)) :=
  Subgroup.copy (M.globalIntegralHom T hST).range
    {g | ∀ a : M.coordinate, g.ofConv (M.toBase a) ∈ SIntegers F T}
    (Set.ext fun _ ↦ (mem_range_globalIntegralHom_iff M T hST).symm)

/-- The range of `M.globalIntegralHom T hST` is `M.globalPoints T hST`. -/
@[simp]
theorem range_globalIntegralHom (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) :
    (M.globalIntegralHom T hST).range = M.globalPoints T hST :=
  (Subgroup.copy_eq _ _ _).symm

/-- A rational point `g ∈ G(F)` lies in `M.globalPoints T hST` if and only if its values on
`M.toBase` lie in `𝒪_{F,T}`. -/
@[simp]
theorem mem_globalPoints_iff (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔
      ∀ a : M.coordinate, g.ofConv (M.toBase a) ∈ SIntegers F T :=
  Iff.rfl

/-- Membership in `M.globalPoints T hST` need only be checked on a generating family of
`M.coordinate` over `𝒪_{F,S}`. -/
theorem mem_globalPoints_iff_of_adjoin_eq_top (M : IntegralModel F H S)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hST : S ⊆ T) {ι : Type*} {a : ι → M.coordinate}
    (ha : Algebra.adjoin (SIntegers F S) (Set.range a) = ⊤) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔
      ∀ i, g.ofConv (M.toBase (a i)) ∈ SIntegers F T := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  have hinj : Function.Injective (IsScalarTower.toAlgHom (SIntegers F S) (SIntegers F T) F) := by
    rw [IsScalarTower.coe_toAlgHom']
    intro x y h
    exact Subtype.ext h
  rw [← M.range_globalIntegralHom T hST, M.globalIntegralHom_def,
    M.mem_range_integralPointsHom_iff_of_adjoin_eq_top hinj
      (IsScalarTower.algebraMap_eq (SIntegers F S) F F).symm ha]
  simp [IsScalarTower.coe_toAlgHom']

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
        AlgHom.mapValue (Algebra.ofId F (v.adicCompletion F)) g ∈
          M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  simp only [mem_globalPoints_iff, mem_sIntegers_iff_forall_adicCompletionIntegers,
    mem_localPoints_iff, AlgHom.mapValue_apply, AlgHom.comp_apply, Algebra.ofId_apply]
  exact ⟨fun h v hv a ↦ h a v hv, fun h a v hv ↦ h v hv a⟩

/-- Equivalent adelic form of `mem_globalPoints_iff_forall_localPoints`: `g ∈ M.globalPoints T hST`
if and only if `localProjection (𝓞 F) F H v (diagonal (𝓞 F) F H g) ∈ M.level v` for every
`v ∉ T`. -/
theorem mem_globalPoints_iff_forall_level (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) {g : WithConv (H →ₐ[F] F)} :
    g ∈ M.globalPoints T hST ↔
      ∀ v ∉ T, localProjection (𝓞 F) F H v (diagonal (𝓞 F) F H g) ∈ M.level v := by
  rw [M.mem_globalPoints_iff_forall_localPoints hST]
  refine forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_
  rw [localProjection_diagonal, M.level_of_notMem (fun hvS ↦ hv (hST hvS))]

end GlobalPoints

/-! ### Enlarging the exceptional set of places -/

section Enlarge

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

/-- Canonical Hopf `𝒪_{F,T}`-algebra isomorphism identifying `(M.enlarge hST).coordinate` with the
scalar extension `𝒪_{F,T} ⊗[𝒪_{F,S}] M.coordinate`. -/
noncomputable def enlargeCoordinateIso (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    (M.enlarge hST).coordinate ≅
      TauCeti.CommHopfAlgCat.baseChange (K := SIntegers F T) M.coordinate :=
  Iso.refl _

/-- Compatibility of `(M.enlarge hST).baseChangeIso` with `enlargeCoordinateIso` and
`baseChangeTowerIso`. -/
theorem enlarge_baseChangeIso (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    letI := sIntegersTowerOfSubset hST
    (M.enlarge hST).baseChangeIso =
      (TauCeti.CommHopfAlgCat.baseChangeFunctor (K := F)).mapIso (M.enlargeCoordinateIso hST) ≪≫
        TauCeti.CommHopfAlgCat.baseChangeTowerIso (SIntegers F S) F M.coordinate ≪≫
          M.baseChangeIso := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  dsimp only [enlarge, enlargeCoordinateIso]
  rw [Functor.mapIso_refl, Iso.refl_trans]

/-- Pointwise evaluation of `(M.enlarge hST).baseChangeIso.hom` on a pure tensor in terms of
`enlargeCoordinateIso`, `baseChangeTowerIso`, and `M.baseChangeIso`. -/
theorem enlarge_baseChangeIso_hom_tmul (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (c : F) (x : (M.enlarge hST).coordinate) :
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    letI := sIntegersTowerOfSubset hST
    (M.enlarge hST).baseChangeIso.hom.hom (c ⊗ₜ[SIntegers F T] x) =
      M.baseChangeIso.hom.hom
        ((TauCeti.CommHopfAlgCat.baseChangeTowerIso (SIntegers F S) F M.coordinate).hom.hom
          (c ⊗ₜ[SIntegers F T] (M.enlargeCoordinateIso hST).hom.hom x)) := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  rw [M.enlarge_baseChangeIso hST]
  simp

/-- Under `enlargeCoordinateIso`, `(M.enlarge hST).toBase` sends a pure tensor `r ⊗ₜ a` to
`(r : F) • M.toBase a`. -/
@[simp]
theorem enlarge_toBase_tmul (M : IntegralModel F H S)
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T)
    (r : SIntegers F T) (a : M.coordinate) :
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    (M.enlarge hST).toBase
      ((M.enlargeCoordinateIso hST).inv.hom (r ⊗ₜ[SIntegers F S] a)) =
      (r : F) • M.toBase a := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := sIntegersTowerOfSubset hST
  rw [(M.enlarge hST).toBase_apply, M.enlarge_baseChangeIso_hom_tmul hST,
    (M.enlargeCoordinateIso hST).inv_hom_id_apply,
    TauCeti.CommHopfAlgCat.baseChangeTowerIso_hom_apply, M.baseChangeIso_hom_tmul]
  simp [Algebra.smul_def]

/-- Enlarging the exceptional set from `S` to `T` does not change the local integral subgroup at
any place `v ∉ T`. -/
@[simp]
theorem localPoints_enlarge (M : IntegralModel F H S) {T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
    (M.enlarge hST).localPoints v hv = M.localPoints v (fun hvS ↦ hv (hST hvS)) := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  ext g
  simp only [mem_localPoints_iff]
  constructor
  · intro hg a
    have h := hg ((M.enlargeCoordinateIso hST).inv.hom ((1 : SIntegers F T) ⊗ₜ[SIntegers F S] a))
    simpa only [M.enlarge_toBase_tmul hST, OneMemClass.coe_one, one_smul] using h
  · intro hg c
    have hc : c =
        (M.enlargeCoordinateIso hST).inv.hom ((M.enlargeCoordinateIso hST).hom.hom c) := by
      rw [(M.enlargeCoordinateIso hST).hom_inv_id_apply]
    rw [hc]
    generalize (M.enlargeCoordinateIso hST).hom.hom c = b
    induction (b : SIntegers F T ⊗[SIntegers F S] M.coordinate) using TensorProduct.inductionOn with
    | tmul r a =>
      have hr : algebraMap F (v.adicCompletion F) (r : F) ∈ v.adicCompletionIntegers F :=
        (mem_sIntegers_iff_forall_adicCompletionIntegers.mp r.property) v hv
      rw [M.enlarge_toBase_tmul hST, map_smul, Algebra.smul_def]
      exact mul_mem hr (hg a)
    | add x y hx hy =>
      rw [map_add, map_add, map_add]
      exact add_mem hx hy

/-- Outside `T`, the reference level subgroup of `M.enlarge hST` agrees with that of `M`. -/
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
